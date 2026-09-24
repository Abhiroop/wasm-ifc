{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

{- | The security policy of a module: where the levels that "Validation.Elaborate" checks come
  from. A decoded module says nothing about levels, so without a policy everything is public
  and validation accepts what it always did.

  The design (decided 2026-09-22): everything SecWasm lets a developer annotate is expressible,
  inference is the default where it is sound, and the interface must be declared.

    * /Functions/ and /globals/: a declaration by index, from the module's own @ifc@ custom
      section, or by name for imports and exports, from a policy file. Both may speak about the
      same item only if they agree. Everything else is public.
    * /Stores/: never need a declaration. The validator infers the lowest level the rule allows,
      the join of the pc, the address and the value. A declaration by site overrides it, and is
      meant to be rare.
    * /Loads/: the one thing nothing can infer, since the level is what the site expects to
      read. A site declaration wins; otherwise a region declaration for a constant address;
      otherwise the function's default; otherwise the module's default, which is public unless
      set, so that a secret read without a declaration traps at run time and names the site.

  A memory access site is named by the function's index and the position of the access among
  the memory accesses of that function's body, counted from zero in code order with nested
  blocks included. (A byte offset would also work for a binary; the position is what a tool
  reading either the text or the binary can compute, and it survives changes elsewhere in the
  module.)

  One text format serves both carriers, one statement per line, @;@ starting a comment:

  > func 3 : H L -> H          ; parameters, then results, as levels; the arrow may be -{L}->
  > export check : H -> L
  > import env.read : L L -> H
  > global 0 : H
  > export global key : H
  > load 3 5 : H               ; the sixth memory access of function 3
  > store 3 2 : H
  > region 0x1000 0x1400 : H   ; addresses in [0x1000, 0x1400) hold secrets; overlapping regions must agree
  > load-default : L
  > load-default func 3 : H
  > load-default export check : H
  > stdin : H                  ; the standard streams' levels, for the WASI host
  > stdout : L
  > preopen /data : H          ; a preopened directory (by guest name) and all it contains
  > allow-declassify

  The arrow may carry a level, @-{H}->@: the function's bound, the most secret context it may
  be called from (SecWasm's @→ℓ@; see 'Syntax.TypesIFC.LabelledFuncType'). A plain @->@ is
  @-{L}->@. A function's results must be at least as secret as its bound.
  Annotations can also live in the source program, as calls to an import module named @ifc@
  (the /ghost/ functions): a plain runtime runs them through a shim of identities and plain
  accesses, and this stage rewrites every call to one into the instruction it stands for, so
  the interpreter never pays the call and a source language needs no new syntax:

  > (import "ifc" "secret_i32"      (func (param i32) (result i32)))  ;; relabel to secret
  > (import "ifc" "declassify_i32"  (func (param i32) (result i32)))  ;; trusted, needs allow-declassify
  > (import "ifc" "load_secret_i32" (func (param i32) (result i32)))  ;; a load declared secret
  > (import "ifc" "store_secret_i32" (func (param i32 i32)))          ;; a store declared secret

  with @i64@, @f32@ and @f64@ likewise, and @public@ in place of @secret@ for the accesses. A
  ghost keeps its place in the function index space, so nothing else moves; it may not be
  exported, started, or put in a table, since it exists to be rewritten, not entered.
  TODO(ifc P2): inference of the levels of undeclared internal functions; today they are
  public throughout, so a helper that receives a secret must be declared by index. Two ways to
  build it, and the choice is Daniel's: (a) re-run elaboration with the levels raised whenever
  it fails on a level at a call or a result, which reuses the typed rules unchanged and is sound
  by construction, but re-elaborates the whole module once per raised level and needs the
  error to name the function and position; (b) a separate level-flow analysis over the raw
  instructions, one pass with a fixpoint, which is fast but a second copy of the rules that
  can drift from the typed ones. The arrow label should come first either way, since an
  inferred function is only useful if it can also be called from a secret context.
-}
module Validation.Policy (
    Policy (..),
    FunctionLevels (..),
    PolicyError (..),
    emptyPolicy,
    parsePolicy,
    mergePolicies,
    sectionPolicy,
    modulePolicy,
    Assembled (..),
    assemble,
    labelFuncType,
    ghostModuleName,
) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, unless, when)
import Data.ByteString qualified as BS
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, mapMaybe, maybeToList)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8')
import Data.Word (Word32)
import Numeric (readHex)

import Data.Singletons (withSomeSing)
import Syntax.Functions (RawFunction (..))
import Syntax.Globals (RawGlobal (..))
import Syntax.Immediates (MemArg (..))
import Syntax.Indices (FunctionIdx (..), GlobalIdx (..))
import Syntax.Instructions (RawInstr (..))
import Syntax.Module
import Syntax.Types (FuncType, FuncTypeOf (..), GlobalTypeOf (..), SValType (..), ValType (..))
import Syntax.TypesIFC (LabelledFuncType (..), LabelledGlobalType, LabelledValType (..), SecLevel (..), join)

-- | The levels of a function's parameters and results, in declared order, and its bound.
data FunctionLevels = FunctionLevels
    { params :: [SecLevel]
    , results :: [SecLevel]
    , bound :: SecLevel
    }
    deriving stock (Eq, Show)

-- | A policy as written: every declaration is optional, and each kind lives in its own map.
data Policy = Policy
    { functionsByIndex :: Map Word32 FunctionLevels
    , exportedFunctions :: Map Text FunctionLevels
    , importedFunctions :: Map (Text, Text) FunctionLevels
    , globalsByIndex :: Map Word32 SecLevel
    , exportedGlobals :: Map Text SecLevel
    , loads :: Map (Word32, Word32) SecLevel
    -- ^ by function index and memory-access position
    , stores :: Map (Word32, Word32) SecLevel
    , regions :: [(Word32, Word32, SecLevel)]
    -- ^ half-open address ranges
    , loadDefault :: Maybe SecLevel
    , loadDefaultsByIndex :: Map Word32 SecLevel
    , loadDefaultsByExport :: Map Text SecLevel
    , declassifyAllowed :: Bool
    , streamLevels :: Map Text SecLevel
    -- ^ by @stdin@, @stdout@, @stderr@
    , preopenLevels :: Map Text SecLevel
    -- ^ by the directory's guest name
    }
    deriving stock (Eq, Show)

emptyPolicy :: Policy
emptyPolicy = Policy Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty [] Nothing Map.empty Map.empty False Map.empty Map.empty

data PolicyError
    = -- | a line that is not a statement: its number and text
      PolicySyntax Int Text
    | -- | two declarations of the same item disagree
      PolicyConflict Text
    | -- | a declaration names something the module does not have
      PolicyUnknown Text
    | -- | a function declaration with the wrong number of levels
      PolicyArity Text
    | -- | a custom section that is not UTF-8 text
      PolicySectionNotText
    | -- | a function whose results are below its bound
      PolicyResultsBelowBound Text
    | -- | an @ifc@ import with a name this stage does not know, or the wrong type for it
      PolicyGhostType Text
    | -- | an @ifc@ import that is exported, started or placed in a table
      PolicyGhostReferenced Text
    deriving stock (Eq, Show)

-- *** Parsing ***

-- | Parse the text format described in the module header.
parsePolicy :: Text -> Either PolicyError Policy
parsePolicy source = foldM statement emptyPolicy (zip [1 ..] (T.lines source))
  where
    statement policy (lineNo, raw) = case T.words (T.takeWhile (/= ';') raw) of
        [] -> Right policy
        ["allow-declassify"] -> Right policy {declassifyAllowed = True}
        ws -> case break (== ":") ws of
            (headWords, ":" : body) -> declaration policy lineNo headWords body
            _ -> Left (PolicySyntax lineNo raw)
    declaration policy lineNo headWords body = case headWords of
        ["func", ix] -> do
            i <- number lineNo ix
            fl <- functionLevels lineNo body
            Right policy {functionsByIndex = Map.insert i fl policy.functionsByIndex}
        ["export", name] -> do
            fl <- functionLevels lineNo body
            Right policy {exportedFunctions = Map.insert name fl policy.exportedFunctions}
        ["import", qualified] -> case T.breakOn "." qualified of
            (modName, field) | not (T.null field) -> do
                fl <- functionLevels lineNo body
                Right policy {importedFunctions = Map.insert (modName, T.drop 1 field) fl policy.importedFunctions}
            _ -> Left (PolicySyntax lineNo qualified)
        ["global", ix] -> do
            i <- number lineNo ix
            l <- oneLevel lineNo body
            Right policy {globalsByIndex = Map.insert i l policy.globalsByIndex}
        ["export", "global", name] -> do
            l <- oneLevel lineNo body
            Right policy {exportedGlobals = Map.insert name l policy.exportedGlobals}
        ["load", fn, pos] -> do
            key <- (,) <$> number lineNo fn <*> number lineNo pos
            l <- oneLevel lineNo body
            Right policy {loads = Map.insert key l policy.loads}
        ["store", fn, pos] -> do
            key <- (,) <$> number lineNo fn <*> number lineNo pos
            l <- oneLevel lineNo body
            Right policy {stores = Map.insert key l policy.stores}
        ["region", lo, hi] -> do
            range <- (,) <$> number lineNo lo <*> number lineNo hi
            l <- oneLevel lineNo body
            Right policy {regions = policy.regions ++ [(fst range, snd range, l)]}
        ["load-default"] -> do
            l <- oneLevel lineNo body
            Right policy {loadDefault = Just l}
        ["load-default", "func", ix] -> do
            i <- number lineNo ix
            l <- oneLevel lineNo body
            Right policy {loadDefaultsByIndex = Map.insert i l policy.loadDefaultsByIndex}
        ["load-default", "export", name] -> do
            l <- oneLevel lineNo body
            Right policy {loadDefaultsByExport = Map.insert name l policy.loadDefaultsByExport}
        [stream] | stream `elem` ["stdin", "stdout", "stderr"] -> do
            l <- oneLevel lineNo body
            Right policy {streamLevels = Map.insert stream l policy.streamLevels}
        ["preopen", guest] -> do
            l <- oneLevel lineNo body
            Right policy {preopenLevels = Map.insert guest l policy.preopenLevels}
        _ -> Left (PolicySyntax lineNo (T.unwords headWords))
    functionLevels lineNo body = case break isArrow body of
        (ps, arrow : rs) -> do
            arrowLevel <- case arrow of
                "->" -> Right Low
                _ -> level lineNo (T.drop 2 (T.dropEnd 3 arrow))
            FunctionLevels <$> traverse (level lineNo) ps <*> traverse (level lineNo) rs <*> pure arrowLevel
        _ -> Left (PolicySyntax lineNo (T.unwords body))
    isArrow w = w == "->" || (T.isPrefixOf "-{" w && T.isSuffixOf "}->" w)
    oneLevel lineNo body = case body of
        [w] -> level lineNo w
        _ -> Left (PolicySyntax lineNo (T.unwords body))
    level _ "L" = Right Low
    level _ "H" = Right High
    level lineNo w = Left (PolicySyntax lineNo w)
    number lineNo w = case T.stripPrefix "0x" w of
        Just hex | [(n, "")] <- readHex (T.unpack hex) -> Right n
        Nothing | T.all (`elem` ['0' .. '9']) w, not (T.null w) -> Right (read (T.unpack w))
        _ -> Left (PolicySyntax lineNo w)

-- *** Merging ***

-- | Combine two policies, which may declare the same item only if they agree.
mergePolicies :: Policy -> Policy -> Either PolicyError Policy
mergePolicies a b = do
    functionsByIndex <- agreeing "func" a.functionsByIndex b.functionsByIndex
    exportedFunctions <- agreeing "export" a.exportedFunctions b.exportedFunctions
    importedFunctions <- agreeing "import" a.importedFunctions b.importedFunctions
    globalsByIndex <- agreeing "global" a.globalsByIndex b.globalsByIndex
    exportedGlobals <- agreeing "export global" a.exportedGlobals b.exportedGlobals
    loads <- agreeing "load" a.loads b.loads
    stores <- agreeing "store" a.stores b.stores
    loadDefaultsByIndex <- agreeing "load-default func" a.loadDefaultsByIndex b.loadDefaultsByIndex
    loadDefaultsByExport <- agreeing "load-default export" a.loadDefaultsByExport b.loadDefaultsByExport
    streamLevels <- agreeing "stream" a.streamLevels b.streamLevels
    preopenLevels <- agreeing "preopen" a.preopenLevels b.preopenLevels
    loadDefault <- case (a.loadDefault, b.loadDefault) of
        (Just x, Just y) | x /= y -> Left (PolicyConflict "load-default")
        (x, y) -> Right (x <|> y)
    Right
        Policy
            { functionsByIndex
            , exportedFunctions
            , importedFunctions
            , globalsByIndex
            , exportedGlobals
            , loads
            , stores
            , regions = a.regions ++ b.regions
            , loadDefault
            , loadDefaultsByIndex
            , loadDefaultsByExport
            , declassifyAllowed = a.declassifyAllowed || b.declassifyAllowed
            , streamLevels
            , preopenLevels
            }
  where
    agreeing :: (Ord k, Show k, Eq v) => Text -> Map k v -> Map k v -> Either PolicyError (Map k v)
    agreeing what x y = case [k | (k, v) <- Map.toList x, Just v' <- [Map.lookup k y], v /= v'] of
        [] -> Right (Map.union x y)
        k : _ -> Left (PolicyConflict (what <> " " <> T.pack (show k)))

-- | The policy a module carries in its own @ifc@ custom sections (merged, in order).
sectionPolicy :: RawModule -> Either PolicyError Policy
sectionPolicy m = foldM step emptyPolicy [bytes | (name, bytes) <- m.customSections, name == "ifc"]
  where
    step acc bytes = do
        text <- either (const (Left PolicySectionNotText)) Right (decodeUtf8' (BS.toStrict bytes))
        parsePolicy text >>= mergePolicies acc

-- | The policy in force for a module: the given one merged with the module's own section.
modulePolicy :: Policy -> RawModule -> Either PolicyError Policy
modulePolicy given m = sectionPolicy m >>= mergePolicies given

-- *** Assembly ***

{- | A policy resolved against a module: one level for everything, and the module with the
  site declarations written into its bodies as 'Annotated' instructions. Validation reads only
  this; nothing at run time consults a policy.
-}
data Assembled = Assembled
    { functionTypes :: [LabelledFuncType]
    -- ^ one per entry of the function index space, in declared order
    , globalTypes :: [LabelledGlobalType]
    , loadDefaults :: [SecLevel]
    -- ^ one per entry of the function index space
    , declassify :: Bool
    , annotated :: RawModule
    }

-- | The import module whose functions are annotations in disguise.
ghostModuleName :: Text
ghostModuleName = "ifc"

-- | What a ghost function stands for.
data Ghost
    = GhostLoad SecLevel ValType
    | GhostStore SecLevel ValType
    | GhostRelabel SecLevel ValType
    | GhostDeclassify SecLevel ValType

-- | The ghost an import name denotes, if any (see the module header for the names).
ghostByName :: Text -> Maybe Ghost
ghostByName name = case T.splitOn "_" name of
    ["secret", t] -> GhostRelabel High <$> valueType t
    ["declassify", t] -> GhostDeclassify Low <$> valueType t
    ["load", l, t] -> GhostLoad <$> level l <*> valueType t
    ["store", l, t] -> GhostStore <$> level l <*> valueType t
    _ -> Nothing
  where
    level "secret" = Just High
    level "public" = Just Low
    level _ = Nothing
    valueType "i32" = Just I32
    valueType "i64" = Just I64
    valueType "f32" = Just F32
    valueType "f64" = Just F64
    valueType _ = Nothing

-- | The type a ghost must be imported at.
ghostType :: Ghost -> FuncType
ghostType ghost = case ghost of
    GhostLoad _ t -> FuncType [I32] [t]
    GhostStore _ t -> FuncType [I32, t] []
    GhostRelabel _ t -> FuncType [t] [t]
    GhostDeclassify _ t -> FuncType [t] [t]

-- | The instruction a call to a ghost stands for.
ghostInstruction :: Ghost -> RawInstr
ghostInstruction ghost = case ghost of
    GhostLoad l t -> Annotated l (withSomeSing t (\st -> Load st (MemArg 0 0)))
    GhostStore l t -> Annotated l (withSomeSing t (\st -> Store st (MemArg 0 0)))
    GhostRelabel l _ -> Relabel l
    GhostDeclassify l _ -> Declassify l

-- | Resolve a policy against a module (see the module header for the order of precedence).
assemble :: Policy -> RawModule -> Either PolicyError Assembled
assemble policy m = do
    unless (null [() | (lo, hi, l) <- policy.regions, (lo', hi', l') <- policy.regions, l /= l', lo < hi', lo' < hi]) (Left (PolicyConflict "region"))
    ghosts <- Map.fromList <$> sequence [(i,) <$> ghostOf imp | (i, imp) <- zip [0 ..] m.imports, imp.moduleName == ghostModuleName]
    mapM_ (notAGhost ghosts) ([(e.name, i) | e <- m.exports, ExportFunc (FunctionIdx i) <- [e.desc]] ++ [("start", i) | Just (FunctionIdx i) <- [m.start]] ++ [("elem", i) | seg <- m.elementSegments, FunctionIdx i <- seg.functions])
    mapM_ (knownFunction . fst) (Map.toList policy.functionsByIndex)
    mapM_ (knownFunction . fst) (Map.toList policy.loadDefaultsByIndex)
    mapM_ (knownExport . fst) (Map.toList policy.exportedFunctions)
    mapM_ (knownExport . fst) (Map.toList policy.loadDefaultsByExport)
    mapM_ knownImport (Map.keys policy.importedFunctions)
    mapM_ (knownGlobal . fst) (Map.toList policy.globalsByIndex)
    mapM_ knownExportedGlobal (Map.keys policy.exportedGlobals)
    functionTypes <- traverse functionType (zip [0 ..] signatures)
    globalTypes <- traverse globalType (zip [0 ..] [gt | RawGlobal gt _ <- m.globals])
    loadDefaults <- traverse functionLoadDefault (zipWith const [0 ..] signatures)
    Right
        Assembled
            { functionTypes
            , globalTypes
            , loadDefaults
            , declassify = policy.declassifyAllowed
            , annotated = withFunctions (zipWith (annotateFunction ghosts) [fromIntegral (length m.imports) ..] m.functions)
            }
  where
    ghostOf (RawImport _ name (ImportFunc declared)) = case ghostByName name of
        Just ghost | declared == ghostType ghost -> Right ghost
        _ -> Left (PolicyGhostType name)
    notAGhost :: Map Word32 Ghost -> (Text, Word32) -> Either PolicyError ()
    notAGhost ghosts (what, i) = when (Map.member i ghosts) (Left (PolicyGhostReferenced what))
    -- The module with its bodies replaced (a construction, since the field name is shared).
    withFunctions fs =
        RawModule
            { types = m.types
            , imports = m.imports
            , functions = fs
            , globals = m.globals
            , memories = m.memories
            , tables = m.tables
            , elementSegments = m.elementSegments
            , dataSegments = m.dataSegments
            , exports = m.exports
            , start = m.start
            , customSections = m.customSections
            }
    -- The function index space: imports first, then the module's own functions.
    signatures = [ft | RawImport _ _ (ImportFunc ft) <- m.imports] ++ map (\(RawFunction sig _ _) -> sig) m.functions
    exportNamesOf i = [e.name | e <- m.exports, ExportFunc (FunctionIdx j) <- [e.desc], j == i]
    importOf i = case drop (fromIntegral i) m.imports of
        (RawImport modName field _ : _) | fromIntegral i < length m.imports -> Just (modName, field)
        _ -> Nothing
    knownFunction i = when (fromIntegral i >= length signatures) (Left (PolicyUnknown ("func " <> T.pack (show i))))
    knownExport name = when (null [() | e <- m.exports, e.name == name, ExportFunc _ <- [e.desc]]) (Left (PolicyUnknown ("export " <> name)))
    knownImport (modName, field) = when (null [() | RawImport mn f _ <- m.imports, mn == modName, f == field]) (Left (PolicyUnknown ("import " <> modName <> "." <> field)))
    knownGlobal i = when (fromIntegral i >= length m.globals) (Left (PolicyUnknown ("global " <> T.pack (show i))))
    knownExportedGlobal name = when (null [() | e <- m.exports, e.name == name, ExportGlobal _ <- [e.desc]]) (Left (PolicyUnknown ("export global " <> name)))

    -- Every declaration that names function @i@: by index, by each export name, by import.
    declarationsFor :: Word32 -> [(Text, FunctionLevels)]
    declarationsFor i =
        [("func " <> T.pack (show i), fl) | Just fl <- [Map.lookup i policy.functionsByIndex]]
            ++ [("export " <> name, fl) | name <- exportNamesOf i, Just fl <- [Map.lookup name policy.exportedFunctions]]
            ++ [("import", fl) | Just key <- [importOf i], Just fl <- [Map.lookup key policy.importedFunctions]]
    functionType (i, ft@(FuncType ps rs)) = case declarationsFor i of
        [] -> Right (labelFuncType (FunctionLevels (map (const Low) ps) (map (const Low) rs) Low) ft)
        (what, fl) : others -> do
            unless (all ((== fl) . snd) others) (Left (PolicyConflict what))
            unless (length fl.params == length ps && length fl.results == length rs) (Left (PolicyArity what))
            unless (all (\l -> join fl.bound l == l) fl.results) (Left (PolicyResultsBelowBound what))
            Right (labelFuncType fl ft)
    globalType (i, GlobalType mutability t) = case maybeToList (Map.lookup i policy.globalsByIndex) ++ mapMaybe (`Map.lookup` policy.exportedGlobals) (globalExportNames i) of
        [] -> Right (GlobalType mutability (t :~ Low))
        l : others
            | all (== l) others -> Right (GlobalType mutability (t :~ l))
            | otherwise -> Left (PolicyConflict ("global " <> T.pack (show i)))
    globalExportNames i = [e.name | e <- m.exports, ExportGlobal (GlobalIdx j) <- [e.desc], j == i]
    functionLoadDefault i = case maybeToList (Map.lookup i policy.loadDefaultsByIndex) ++ mapMaybe (`Map.lookup` policy.loadDefaultsByExport) (exportNamesOf i) of
        [] -> Right (fromMaybe Low policy.loadDefault)
        l : others
            | all (== l) others -> Right l
            | otherwise -> Left (PolicyConflict ("load-default " <> T.pack (show i)))

    -- Write the site declarations into a body: each memory access, in code order, takes the
    -- level declared for its position, else the level of the region a constant address
    -- falls in.
    annotateFunction ghosts i (RawFunction sig locals body) = RawFunction sig locals (lowerGhosts ghosts (fst (annotateSeq i 0 body)))
    -- Rewrite every call to a ghost into the instruction it stands for; after the site
    -- annotation, so the accesses it introduces do not shift the positions a tool computed
    -- from the module as written.
    lowerGhosts :: Map Word32 Ghost -> [RawInstr] -> [RawInstr]
    lowerGhosts ghosts = map lower
      where
        lower instr = case instr of
            Call (FunctionIdx f) | Just ghost <- Map.lookup f ghosts -> ghostInstruction ghost
            Block bt b -> Block bt (map lower b)
            Loop bt b -> Loop bt (map lower b)
            If bt t e -> If bt (map lower t) (map lower e)
            other -> other
    annotateSeq :: Word32 -> Word32 -> [RawInstr] -> ([RawInstr], Word32)
    annotateSeq _ n [] = ([], n)
    -- A load whose address is a constant: @i32.const k; load@.
    annotateSeq i n (Const SI32 k : access : rest)
        | isLoad access =
            let (rest', n') = annotateSeq i (n + 1) rest
             in (Const SI32 k : atSite i n (Just k) access : rest', n')
    -- A store whose address is a constant and whose value is one instruction that only
    -- pushes: @i32.const k; <value>; store@. (A value computed by several instructions hides the
    -- address from this peephole, and the store then gets no region level.)
    annotateSeq i n (Const SI32 k : value : access : rest)
        | isStore access && pushesOne value =
            let (rest', n') = annotateSeq i (n + 1) rest
             in (Const SI32 k : value : atSite i n (Just k) access : rest', n')
    annotateSeq i n (instr : rest)
        | isMemoryAccess instr =
            let (rest', n') = annotateSeq i (n + 1) rest
             in (atSite i n Nothing instr : rest', n')
        | otherwise =
            let (instr', n') = case instr of
                    Block bt b -> let (b', k) = annotateSeq i n b in (Block bt b', k)
                    Loop bt b -> let (b', k) = annotateSeq i n b in (Loop bt b', k)
                    If bt t e -> let (t', k) = annotateSeq i n t; (e', k') = annotateSeq i k e in (If bt t' e', k')
                    other -> (other, n)
                (rest', n'') = annotateSeq i n' rest
             in (instr' : rest', n'')
    -- The level a memory access declares: the site's, else the region's when the address
    -- is the constant given, else nothing (the validator then applies the defaults).
    atSite i n constantAddress access = case Map.lookup (i, n) (siteMap access) of
        Just l -> Annotated l access
        Nothing -> case constantAddress >>= \k -> regionLevel (fromIntegral k + offsetOf access) of
            Just l -> Annotated l access
            Nothing -> access
    isLoad instr = case instr of
        Load {} -> True
        LoadN {} -> True
        _ -> False
    isStore instr = case instr of
        Store {} -> True
        StoreN {} -> True
        _ -> False
    isMemoryAccess instr = isLoad instr || isStore instr
    pushesOne instr = case instr of
        Const {} -> True
        LocalGet _ -> True
        GlobalGet _ -> True
        MemorySize -> True
        _ -> False
    siteMap instr = case instr of
        Load {} -> policy.loads
        LoadN {} -> policy.loads
        _ -> policy.stores
    offsetOf instr = case instr of
        Load _ (MemArg _ off) -> fromIntegral off
        LoadN _ _ _ (MemArg _ off) -> fromIntegral off
        Store _ (MemArg _ off) -> fromIntegral off
        StoreN _ _ (MemArg _ off) -> fromIntegral off
        _ -> 0 :: Integer
    regionLevel :: Integer -> Maybe SecLevel
    regionLevel addr = case [l | (lo, hi, l) <- policy.regions, toInteger lo <= addr, addr < toInteger hi] of
        [] -> Nothing
        ls -> Just (if High `elem` ls then High else Low)

-- | Attach levels to a decoded function type, in declared order.
labelFuncType :: FunctionLevels -> FuncType -> LabelledFuncType
labelFuncType fl (FuncType ps rs) = LabelledFuncType fl.bound (zipWith (:~) ps fl.params) (zipWith (:~) rs fl.results)
