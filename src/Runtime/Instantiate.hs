{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

{- | Instantiation: from a validated 'Module' to a running 'ModuleInst'. Imports are linked to
  the host's functions, memories and tables are allocated from the shape, the active data and
  element segments are placed, and the start function runs. Each step can fail the way the
  spec says instantiation may (a segment that does not fit, a start function that traps).
-}
module Runtime.Instantiate (
    InstantiationError (..),
    instantiate,
    Embedder (..),
    providesNothing,
    providesFunctions,
    newMemory,
    newTable,
    instantiateWith,
    instantiateUntilStart,
    StateImports (..),
    stateImportsOf,
    moduleInterface,
) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, forM, when)
import Data.Bifunctor (first)
import Data.Bits (shiftL, (.|.))
import Data.ByteString qualified as BS
import Data.IntMap.Strict qualified as IntMap
import Data.Maybe (fromMaybe)
import Data.Singletons (Sing, fromSing)
import Data.Singletons.Base.TH (SList (SCons, SNil))
import Data.Text (Text)
import Data.Word (Word32, Word64)

import Runtime.Host (SomeWasiFunc (..), resolveWasiImport, wasiFuncType, wasiModuleName)
import Runtime.Interpreter (ForeignTarget (..), FuncInst (..), FuncSpaceInst (..), ModuleInst (..), Outcome (..), getFunc, runFunction)
import Runtime.MemInst (MemInst, allocMemory, labelRange, retypeMemory, writeBytes)
import Runtime.Module (GivenMemory (..), GivenTable (..), SomeModuleInst (..), Value, fromValue)
import Runtime.Stack (DataSpaceInst (..), ElemSpaceInst (..), GlobalSpaceInst (..), MemSpaceInst (..), TableInsts (..), TableSpaceInst (..), ValueStack (..), getMem, getTable, setMem, setTable)
import Runtime.TableInst (allocTable, fillEntries, functionDirectory, tableSize, writeEntries)
import Runtime.Trap (Trap)
import Syntax.Functions (FunctionSpace (..))
import Syntax.Globals (ConstExpr (..), ConstOp (..), Global (..), GlobalSpace (..))
import Syntax.Immediates (HostType, Reference, functionReferenceIn, withReference)
import Syntax.Module (DataPlacement (..), DataSegment (..), ElementMode (..), ElementSegment (..), ElementSpace (..), Export, Interface, Module (..), SomeModule (..), TableInitialiser (..))
import Syntax.Types
import Syntax.TypesIFC (LabelledFuncType (..), SLabelledFuncType (..), SLabelledValType (..), SSecLevel (..), SecLevel (..), decideAllPublic, decideSameValueTypes, decideSegmentFlows, unlabelled)
import Validation.Policy (ghostModuleName)
import Validation.Reflect (NonEmptyMems (..), allFuncRefs, memsNonEmpty)
import Validation.Shape

data InstantiationError
    = -- | an import (module, name) this host does not provide
      UnsupportedImport Text Text
    | -- | the import's declared type is not the host function's
      ImportTypeMismatch Text
    | -- | a global or a table is imported at another level than the one it has where it is defined
      ImportLevelMismatch Text
    | {- | the policy declares an import callable from a secret context or with secret arguments,
      which the host, whose effects are observable, cannot be
      -}
      ImportNotPublic Text
    | {- | the module imports one memory, one table or one global that can be written under two
      of its indices. An instance holds each of its indices' objects by itself, so two of them
      cannot be one object inside it ("Runtime.Link").
      -}
      ImportedTwice Text Text
    | -- | a WASI import requires the module to have a memory
      WasiNeedsMemory
    | -- | a memory or a table declares a minimum size beyond what this machine holds
      MinimumTooLarge
    | -- | a data segment does not fit in its memory
      DataSegmentOutOfBounds Int
    | -- | a secret region of the policy does not fit in memory 0 as instantiated
      RegionOutOfBounds Word32 Word32
    | -- | an element segment does not fit in table 0 (or there is no table)
      ElementSegmentOutOfBounds Int
    | -- | the start function trapped
      StartFunctionTrapped Trap
    | -- | the start function called into the host, which instantiation cannot serve
      StartFunctionNeedsHost
    deriving stock (Eq, Show)

instantiate :: SomeModule -> Either InstantiationError SomeModuleInst
instantiate = instantiateWith providesNothing

{- | What an embedder provides besides WASI, each by the module name and the field name a module
  imports it under.

    * A function: its type, parameters and results in declared order. The embedder answers
      the calls to it ('Runtime.Module.answerForeign').
    * A global: whether it may be written, its level, and its value now.
    * A memory or a table: its type and the memory or table itself, as it is now.

  The module starts with what it is given. Whether it then /shares/ it is the embedder's
  doing: an embedder that links instances hands a memory, a table or a mutable global back and
  forth whenever control passes between them ("Runtime.Link"); one that does not has given a
  copy. The number is the instance's among those the embedder links, which the references to
  its functions carry.

  A level is part of what is given, and instantiation compares it with the level the importing
  module's policy declares: a global that cannot be written may be imported at its level or
  above, and one that can, like a table, at exactly its level, since both sides read and write
  it. A memory has no level of its own; its bytes carry theirs.
-}
data Embedder = Embedder
    { instanceNumber :: Word32
    , functions :: Text -> Text -> Maybe FuncType
    , globals :: Text -> Text -> Maybe (Mutability, SecLevel, Value)
    , memories :: Text -> Text -> Maybe GivenMemory
    , tables :: Text -> Text -> Maybe GivenTable
    , tags :: Text -> Text -> Maybe (Word64, [ValType])
    -- ^ an exception tag: its name among the instances, and the types of what an exception of it carries
    }

providesNothing :: Embedder
providesNothing = Embedder 0 none none none none none
  where
    none _ _ = Nothing

-- | An embedder that provides functions only.
providesFunctions :: (Text -> Text -> Maybe FuncType) -> Embedder
providesFunctions answered = Embedder 0 answered none none none none
  where
    none _ _ = Nothing

-- | A new, empty memory of a type, to give to a module that imports one.
newMemory :: MemType -> Maybe GivenMemory
newMemory (MemType addresses limits) = GivenMemory addresses limits <$> (allocMemory addresses limits :: Maybe (MemInst ('MemShape 'AddrI32 0 'Nothing)))

-- | A new public table of a type, every entry null.
newTable :: ValType -> AddrType -> Limits -> Maybe GivenTable
newTable entries indices limits = GivenTable entries indices Low limits <$> allocTable limits

-- | 'instantiate' for a module that imports from its embedder.
instantiateWith :: Embedder -> SomeModule -> Either InstantiationError SomeModuleInst
instantiateWith embedder m = do
    Prepared shapeS inst exports failed start <- prepare embedder m
    maybe (Right ()) Left failed
    started <- runStart inst start
    Right (SomeModuleInst shapeS started exports)

{- | Instantiate a module up to its start function, for an embedder that runs the start function
  itself (it may call functions of other instances). An error on the left is one before
  anything was written: an import that is missing or does not match. Otherwise the instance
  comes back with the error of the active segment that did not fit, if one did not: the
  segments before it are written, in the instance's own and in the imported memories and
  tables, and stay so, as the specification has it. Last is the index of the start function.
-}
instantiateUntilStart :: Embedder -> SomeModule -> Either InstantiationError (SomeModuleInst, Maybe InstantiationError, Maybe Word32)
instantiateUntilStart embedder m = do
    Prepared shapeS inst exports failed start <- prepare embedder m
    Right (SomeModuleInst shapeS inst exports, failed, fmap position start)
  where
    position :: Elem a xs -> Word32
    position Here = 0
    position (There rest) = 1 + position rest

-- | An instance with its active segments placed as far as they fit, and its start function not yet run.
data Prepared where
    Prepared ::
        Sing (shape :: ModuleShape) ->
        ModuleInst shape ->
        [Export] ->
        Maybe InstantiationError ->
        Maybe (Elem ('LabelledFuncType 'Low '[] '[]) (ModuleFuncs shape)) ->
        Prepared

prepare :: Embedder -> SomeModule -> Either InstantiationError Prepared
prepare embedder (SomeModule shapeS m) = case shapeS of
    SModuleShape ftsS gsS msS tsS dsS _ tagsS -> do
        funcs <- link embedder.functions (memsNonEmpty msS) ftsS m.functions
        -- A tag the module imports has the name of the tag it imports, which must carry the same types; its own tags are named after the instance.
        importedTags <- forM (zip m.tagImports (fromSing tagsS)) $ \((moduleName, fieldName), declared) -> do
            (name, carried) <- note (UnsupportedImport moduleName fieldName) (embedder.tags moduleName fieldName)
            when (carried /= reverse (map unlabelled declared)) (Left (ImportTypeMismatch fieldName))
            Right name
        let tagNames = importedTags ++ [(fromIntegral embedder.instanceNumber `shiftL` 33) .|. (index + 1) | index <- [fromIntegral (length importedTags) .. fromIntegral (length (fromSing tagsS)) - 1]]
        globals <- instantiateGlobals embedder gsS m.globals
        allocated <- allocateMemories embedder (map Just m.memoryImports ++ repeat Nothing) msS
        allocatedTables <- allocateTables embedder (map Just m.tableImports ++ repeat Nothing) tsS
        emptyTables <- foldM (startAt embedder) allocatedTables m.tableInitialisers
        kept <- keptElements embedder m.elementSegments
        -- The active segments are placed in the specification's order, the element segments
        -- first, and placing stops at the first that does not fit.
        let (tables, elementsFailed) = placeElements embedder 0 m.elementSegments (TableSpaceInst (functionDirectory embedder.instanceNumber (allFuncRefs ftsS)) emptyTables kept IntMap.empty tagNames)
            (placed, dataFailed) = maybe (placeData embedder m.dataSegments allocated) (const (allocated, Nothing)) elementsFailed
            (mems, regionsFailed) = case elementsFailed <|> dataFailed of
                Just _ -> (placed, Nothing)
                Nothing -> case labelRegions m.secretRegions placed of
                    Left failure -> (placed, Just failure)
                    Right labelled -> (labelled, Nothing)
            inst = ModuleInst {functions = funcs, globals, memories = mems, tables, dataSegments = remainingData dsS m.dataSegments}
        Right (Prepared shapeS inst m.exports (elementsFailed <|> dataFailed <|> regionsFailed) m.start)

-- | The types of a module's functions, globals and tables as it wrote them, if it was decoded from a binary.
moduleInterface :: SomeModule -> Maybe Interface
moduleInterface (SomeModule _ m) = m.interface

-- | The globals, memories, tables and functions a module imports, each list in the order of its index space.
data StateImports = StateImports
    { globals :: [(Text, Text)]
    , memories :: [(Text, Text)]
    , tables :: [(Text, Text)]
    , functions :: [(Text, Text)]
    , tags :: [(Text, Text)]
    }

stateImportsOf :: SomeModule -> StateImports
stateImportsOf (SomeModule _ m) = StateImports (provided m.globals) m.memoryImports m.tableImports (imported m.functions) m.tagImports
  where
    imported :: FunctionSpace shape fts -> [(Text, Text)]
    imported NoFunctions = []
    imported (Defined _ rest) = imported rest
    imported (Imported moduleName fieldName rest) = (moduleName, fieldName) : imported rest
    provided :: GlobalSpace gs -> [(Text, Text)]
    provided NoGlobals = []
    provided (Declared global rest) = case global of
        ProvidedGlobal moduleName fieldName _ _ -> (moduleName, fieldName) : provided rest
        Global _ -> provided rest

-- | The value of a constant expression, with the imported globals as the embedder provides them.
evalConst :: Embedder -> ConstExpr t -> Either InstantiationError (HostType t)
evalConst embedder expr = case expr of
    ConstValue value -> Right value
    ConstFunction index -> Right (functionReferenceIn embedder.instanceNumber index)
    ConstImported moduleName fieldName st -> do
        (_, _, value) <- note (UnsupportedImport moduleName fieldName) (embedder.globals moduleName fieldName)
        note (ImportTypeMismatch fieldName) (fromValue st value)
    ConstBinary isInt op a b -> apply isInt op <$> evalConst embedder a <*> evalConst embedder b
  where
    apply :: IsInt t -> ConstOp -> HostType t -> HostType t -> HostType t
    apply I32IsInt op = arithmetic op
    apply I64IsInt op = arithmetic op
    arithmetic :: Num a => ConstOp -> a -> a -> a
    arithmetic ConstAdd = (+)
    arithmetic ConstSub = (-)
    arithmetic ConstMul = (*)

{- | The globals as a module starts: a defined one at the value of its initialiser, an imported
  one at the value its embedder provides, which must be a global of the declared type that may
  be written exactly if the import says so.
-}
instantiateGlobals :: Embedder -> Sing gs -> GlobalSpace gs -> Either InstantiationError (GlobalSpaceInst gs)
instantiateGlobals _ SNil NoGlobals = Right GNil
instantiateGlobals embedder (SCons (SGlobalType _ (_ :%~ declaredLevel)) more) (Declared global rest) = case global of
    Global initialiser -> GCons <$> evalConst embedder initialiser <*> instantiateGlobals embedder more rest
    ProvidedGlobal moduleName fieldName smut st -> do
        (mutability, level, provided) <- note (UnsupportedImport moduleName fieldName) (embedder.globals moduleName fieldName)
        -- (A preserved global is a mutable one that the policy marks.)
        when ((mutability == Immutable) /= (fromSing smut == Immutable)) (Left (ImportTypeMismatch fieldName))
        -- Both sides write a global that can be written, so its level is one; a global that
        -- cannot is only read here, at its level or above.
        when (if mutability == Immutable then level == High && fromSing declaredLevel == Low else level /= fromSing declaredLevel) (Left (ImportLevelMismatch fieldName))
        value <- note (ImportTypeMismatch fieldName) (fromValue st provided)
        GCons value <$> instantiateGlobals embedder more rest

{- | Link the functions: a defined one is its own instance; an import must come from the WASI
  module, name a function the host provides, be declared at exactly that function's type, and
  the module must have a memory (WASI requires one, and 'HostFunc' cannot be built without it).
-}
link :: (Text -> Text -> Maybe FuncType) -> Maybe (NonEmptyMems (ModuleMems shape)) -> Sing fts -> FunctionSpace shape fts -> Either InstantiationError (FuncSpaceInst shape fts)
link _ _ SNil NoFunctions = Right FsNil
link provided mems (SCons _ rest) (Defined f more) = FsCons (WasmFunc f) <$> link provided mems rest more
link provided mems (SCons (SLabelledFuncType boundS psS rsS) rest) (Imported moduleName fieldName more)
    | moduleName == ghostModuleName = FsCons GhostFunc <$> link provided mems rest more
    -- An embedder's function: at the type the embedder gives it, from a public context,
    -- with public arguments.
    | Just (FuncType params results) <- provided moduleName fieldName = do
        when (params /= reverse (map unlabelled (fromSing psS)) || results /= reverse (map unlabelled (fromSing rsS))) (Left (ImportTypeMismatch fieldName))
        public <- note (ImportNotPublic fieldName) (decideAllPublic psS)
        case boundS of
            SLow -> FsCons (ForeignFunc (ImportedAs moduleName fieldName) psS rsS public) <$> link provided mems rest more
            SHigh -> Left (ImportNotPublic fieldName)
    | moduleName /= wasiModuleName = Left (UnsupportedImport moduleName fieldName)
    | otherwise = case resolveWasiImport fieldName of
        Nothing -> Left (UnsupportedImport moduleName fieldName)
        Just (SomeWasiFunc wasiFunc) -> case wasiFuncType wasiFunc of
            -- Every host function is bound at public (its type is 'PublicFunc'); the match on the
            -- bound is what tells the type checker so, since 'SomeWasiFunc' hides the type.
            SLabelledFuncType SLow hostPsS hostRsS -> do
                _ <- note (ImportTypeMismatch fieldName) (decideSameValueTypes psS hostPsS)
                resultsAgree <- note (ImportTypeMismatch fieldName) (decideSameValueTypes hostRsS rsS)
                argsPublic <- note (ImportNotPublic fieldName) (decideSegmentFlows psS hostPsS)
                NonEmptyMems <- note WasiNeedsMemory mems
                case boundS of
                    SLow -> FsCons (HostFunc wasiFunc argsPublic resultsAgree) <$> link provided mems rest more
                    SHigh -> Left (ImportNotPublic fieldName)
            SLabelledFuncType SHigh _ _ -> Left (ImportTypeMismatch fieldName)

{- | Every memory, from the shape: a defined one at its declared minimum size, an imported one
  (the first ones, by the names given) at the size its embedder provides. A minimum beyond what
  this machine holds is refused; only 64-bit memories and tables can declare one.
-}
allocateMemories :: Embedder -> [Maybe (Text, Text)] -> Sing (ms :: [MemShape]) -> Either InstantiationError (MemSpaceInst ms)
allocateMemories _ _ SNil = Right MNil
allocateMemories embedder origins (SCons shape rest) = case fromSing shape of
    MemShape addresses lo hi -> do
        let declared = Limits (fromIntegral lo) (fmap fromIntegral hi)
        memory <- case take 1 origins of
            [Just (moduleName, fieldName)] -> do
                GivenMemory providedAddresses provided given <- note (UnsupportedImport moduleName fieldName) (embedder.memories moduleName fieldName)
                when (providedAddresses /= addresses || not (provided `fitsImport` declared)) (Left (ImportTypeMismatch fieldName))
                Right (retypeMemory given)
            _ -> note MinimumTooLarge (allocMemory addresses declared)
        MCons memory <$> allocateMemories embedder (drop 1 origins) rest

-- | Every table, its entries null, from the shape: as 'allocateMemories'.
allocateTables :: Embedder -> [Maybe (Text, Text)] -> Sing (ts :: [TableShape]) -> Either InstantiationError (TableInsts ts)
allocateTables _ _ SNil = Right TNil
allocateTables embedder origins (SCons shape rest) = case fromSing shape of
    TableShape entries declaredLevel indices lo hi -> do
        let declared = Limits (fromIntegral lo) (fmap fromIntegral hi)
        table <- case take 1 origins of
            [Just (moduleName, fieldName)] -> do
                given <- note (UnsupportedImport moduleName fieldName) (embedder.tables moduleName fieldName)
                when (given.entries /= entries || given.indices /= indices || not (given.limits `fitsImport` declared)) (Left (ImportTypeMismatch fieldName))
                -- (Both sides read and write the table, so its level is one.)
                when (given.level /= declaredLevel) (Left (ImportLevelMismatch fieldName))
                Right given.table
            _ -> note MinimumTooLarge (allocTable declared)
        TCons table <$> allocateTables embedder (drop 1 origins) rest

-- | Give every entry of a table the value the module declares for it.
startAt :: Embedder -> TableInsts ts -> TableInitialiser -> Either InstantiationError (TableInsts ts)
startAt embedder tables (TableInitialiser index isRef expr) = do
    reference <- withReference isRef (evalConst embedder expr)
    Right (at index reference tables)
  where
    at :: Int -> Reference -> TableInsts ts' -> TableInsts ts'
    at _ _ TNil = TNil
    at n reference (TCons table rest)
        | n == 0 = TCons (fromMaybe table (fillEntries 0 (tableSize table) reference table)) rest
        | otherwise = TCons table (at (n - 1) reference rest)

{- | Whether what is provided has the limits an import declares (the spec's matching of
  limits): at least the minimum, and, if the import declares a maximum, one within it.
-}
fitsImport :: Limits -> Limits -> Bool
fitsImport provided declared = provided.min >= declared.min && maybe True (\most -> maybe False (<= most) provided.max) declared.max

{- | Copy the active data segments into their memories, in order, up to the first that does not
  fit: the memories as they then are, and that segment's error.
-}
placeData :: Embedder -> [DataSegment ms] -> MemSpaceInst ms -> (MemSpaceInst ms, Maybe InstantiationError)
placeData embedder segments mems = go mems (zip [0 ..] segments)
  where
    go current [] = (current, Nothing)
    go current (indexed : rest) = case place current indexed of
        Left failure -> (current, Just failure)
        Right written -> go written rest
    place current (i, segment) = case segment.placement of
        Nothing -> Right current
        Just (PlacedAt at ix offsetExpr) -> do
            offset <- offsetOf at <$> evalConst embedder offsetExpr
            -- (An offset past what an 'Int' holds is past the end of every memory.)
            written <- note (DataSegmentOutOfBounds i) (if offset > 2 ^ (60 :: Int) then Nothing else writeBytes (getMem ix current) (fromIntegral offset) (BS.unpack segment.bytes))
            Right (setMem ix written current)

-- | An offset of an address type, as wide as the widest.
offsetOf :: Sing (at :: AddrType) -> HostType (AddrVal at) -> Word64
offsetOf SAddrI32 offset = fromIntegral offset
offsetOf SAddrI64 offset = offset

{- | Label the bytes of the policy's secret regions secret, once the data segments are placed
  (their bytes are public, the region's are secret, whatever a segment wrote there).
-}
labelRegions :: [(Word32, Word32)] -> MemSpaceInst ms -> Either InstantiationError (MemSpaceInst ms)
labelRegions [] mems = Right mems
labelRegions regions (MCons mem rest) = do
    mem' <- foldM (\current (lo, hi) -> note (RegionOutOfBounds lo hi) (labelRange High current (fromIntegral lo) (fromIntegral (hi - lo)))) mem regions
    Right (MCons mem' rest)
labelRegions ((lo, hi) : _) MNil = Left (RegionOutOfBounds lo hi)

{- | Write the active element segments into their tables, in order, up to the first that does
  not fit: the tables as they then are, and that segment's error.
-}
placeElements :: Embedder -> Int -> ElementSpace shape es -> TableSpaceInst fts (ModuleTables shape) kept tags -> (TableSpaceInst fts (ModuleTables shape) kept tags, Maybe InstantiationError)
placeElements _ _ NoElements tables = (tables, Nothing)
placeElements embedder index (Elements segment rest) tables = case written of
    Left failure -> (tables, Just failure)
    Right placed -> placeElements embedder (index + 1) rest placed
  where
    written = case segment.mode of
        WrittenTo at tableIx offsetExpr -> do
            offset <- offsetOf at <$> evalConst embedder offsetExpr
            references <- segmentReferences embedder segment
            -- (An offset past what a table holds is past the end of this one.)
            table <- note (ElementSegmentOutOfBounds index) (if offset > 0xFFFFFFFF then Nothing else writeEntries (fromIntegral offset) references (getTable tableIx tables))
            Right (setTable tableIx table tables)
        KeptForInit -> Right tables
        DeclaredOnly -> Right tables

-- | The references of an element segment, each the value of its constant expression.
segmentReferences :: Embedder -> ElementSegment shape t -> Either InstantiationError [Reference]
segmentReferences embedder segment = withReference segment.entryType (traverse (evalConst embedder) segment.items)

{- | The element segments as @table.init@ will find them: passive ones keep their references,
active and declarative ones are already dropped.
-}
keptElements :: Embedder -> ElementSpace shape es -> Either InstantiationError (ElemSpaceInst es)
keptElements _ NoElements = Right ENil
keptElements embedder (Elements segment rest) = ECons <$> kept <*> keptElements embedder rest
  where
    kept = case segment.mode of
        KeptForInit -> segmentReferences embedder segment
        _ -> Right []

{- | The data segments as @memory.init@ will find them: passive ones keep their bytes, active
ones are already dropped (instantiation copied them).
-}
remainingData :: Sing (ds :: [DataShape]) -> [DataSegment ms] -> DataSpaceInst ds
remainingData SNil _ = DNil
remainingData (SCons SDataShape rest) (segment : more) = DCons (maybe (Just segment.bytes) (const Nothing) segment.placement) (remainingData rest more)
remainingData (SCons SDataShape rest) [] = DCons Nothing (remainingData rest [])

-- | Run the start function, if there is one, as the last step of instantiation.
runStart :: ModuleInst shape -> Maybe (Elem ('LabelledFuncType 'Low '[] '[]) (ModuleFuncs shape)) -> Either InstantiationError (ModuleInst shape)
runStart inst Nothing = Right inst
runStart inst (Just funcIx) = do
    outcome <- first StartFunctionTrapped (runFunction SNil inst (getFunc funcIx inst.functions) VNil)
    case outcome of
        Completed started _ -> Right started
        NeedsHost _ -> Left StartFunctionNeedsHost

note :: e -> Maybe a -> Either e a
note e = maybe (Left e) Right
