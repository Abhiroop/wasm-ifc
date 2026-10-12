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
    instantiateWith,
) where

import Control.Monad (foldM, when)
import Data.Bifunctor (first)
import Data.ByteString qualified as BS
import Data.IntMap.Strict qualified as IntMap
import Data.Singletons (Sing, fromSing)
import Data.Singletons.Base.TH (SList (SCons, SNil))
import Data.Text (Text)
import Data.Word (Word32, Word64)

import Runtime.Host (SomeWasiFunc (..), resolveWasiImport, wasiFuncType, wasiModuleName)
import Runtime.Interpreter (FuncInst (..), FuncSpaceInst (..), ModuleInst (..), Outcome (..), getFunc, runFunction)
import Runtime.MemInst (allocMemory, labelRange, writeBytes)
import Runtime.Module (SomeModuleInst (..), Value, fromValue)
import Runtime.Stack (DataSpaceInst (..), ElemSpaceInst (..), GlobalSpaceInst (..), MemSpaceInst (..), TableInsts (..), TableSpaceInst (..), ValueStack (..), getMem, getTable, setMem, setTable)
import Runtime.TableInst (allocTable, functionDirectory, writeEntries)
import Runtime.Trap (Trap)
import Syntax.Functions (FunctionSpace (..))
import Syntax.Globals (ConstExpr (..), ConstOp (..), Global (..), GlobalSpace (..))
import Syntax.Immediates (HostType, Reference, withReference)
import Syntax.Module (DataPlacement (..), DataSegment (..), ElementMode (..), ElementSegment (..), ElementSpace (..), Module (..), SomeModule (..))
import Syntax.Types
import Syntax.TypesIFC (LabelledFuncType (..), SLabelledFuncType (..), SSecLevel (..), SecLevel (..), decideAllPublic, decideSameValueTypes, decideSegmentFlows, unlabelled)
import Validation.Policy (ghostModuleName)
import Validation.Reflect (NonEmptyMems (..), allFuncRefs, memsNonEmpty)
import Validation.Shape

data InstantiationError
    = -- | an import (module, name) this host does not provide
      UnsupportedImport Text Text
    | -- | the import's declared type is not the host function's
      ImportTypeMismatch Text
    | {- | the policy declares an import callable from a secret context or with secret arguments,
      which the host, whose effects are observable, cannot be
      -}
      ImportNotPublic Text
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
    * A global: whether it may be written, and its value. The module gets the value, not the
      global: nothing the module writes to it reaches the embedder, so an embedder that shares
      a mutable global with others must not provide it here.
    * A memory or a table: its type. The module gets a new, empty one of that type, of which
      the same holds.

  So no state is shared with what a module imports: an import is a way to give a module its
  starting state, and calls are the only way out.
-}
data Embedder = Embedder
    { functions :: Text -> Text -> Maybe FuncType
    , globals :: Text -> Text -> Maybe (Mutability, Value)
    , memories :: Text -> Text -> Maybe MemType
    , tables :: Text -> Text -> Maybe (ValType, AddrType, Limits)
    }

providesNothing :: Embedder
providesNothing = Embedder none none none none
  where
    none _ _ = Nothing

-- | An embedder that provides functions only.
providesFunctions :: (Text -> Text -> Maybe FuncType) -> Embedder
providesFunctions answered = Embedder answered none none none
  where
    none _ _ = Nothing

-- | 'instantiate' for a module that imports from its embedder.
instantiateWith :: Embedder -> SomeModule -> Either InstantiationError SomeModuleInst
instantiateWith embedder (SomeModule shapeS m) = case shapeS of
    SModuleShape ftsS _ msS tsS dsS _ _ -> do
        funcs <- link embedder.functions (memsNonEmpty msS) ftsS m.functions
        globals <- instantiateGlobals embedder m.globals
        placed <- placeData embedder m.dataSegments =<< allocateMemories embedder (map Just m.memoryImports ++ repeat Nothing) msS
        mems <- labelRegions m.secretRegions placed
        emptyTables <- allocateTables embedder (map Just m.tableImports ++ repeat Nothing) tsS
        kept <- keptElements embedder m.elementSegments
        tables <- placeElements embedder 0 m.elementSegments (TableSpaceInst (functionDirectory (allFuncRefs ftsS)) emptyTables kept IntMap.empty)
        let inst = ModuleInst {functions = funcs, globals, memories = mems, tables, dataSegments = remainingData dsS m.dataSegments}
        started <- runStart inst m.start
        Right (SomeModuleInst shapeS started m.exports)

-- | The value of a constant expression, with the imported globals as the embedder provides them.
evalConst :: Embedder -> ConstExpr t -> Either InstantiationError (HostType t)
evalConst embedder expr = case expr of
    ConstValue value -> Right value
    ConstImported moduleName fieldName st -> do
        (_, value) <- note (UnsupportedImport moduleName fieldName) (embedder.globals moduleName fieldName)
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
instantiateGlobals :: Embedder -> GlobalSpace gs -> Either InstantiationError (GlobalSpaceInst gs)
instantiateGlobals _ NoGlobals = Right GNil
instantiateGlobals embedder (Declared global rest) = case global of
    Global initialiser -> GCons <$> evalConst embedder initialiser <*> instantiateGlobals embedder rest
    ProvidedGlobal moduleName fieldName smut st -> do
        (mutability, provided) <- note (UnsupportedImport moduleName fieldName) (embedder.globals moduleName fieldName)
        -- (A preserved global is a mutable one that the policy marks.)
        when ((mutability == Immutable) /= (fromSing smut == Immutable)) (Left (ImportTypeMismatch fieldName))
        value <- note (ImportTypeMismatch fieldName) (fromValue st provided)
        GCons value <$> instantiateGlobals embedder rest

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
            SLow -> FsCons (ForeignFunc moduleName fieldName psS rsS public) <$> link provided mems rest more
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
        limits <- case take 1 origins of
            [Just (moduleName, fieldName)] -> do
                MemType providedAddresses provided <- note (UnsupportedImport moduleName fieldName) (embedder.memories moduleName fieldName)
                when (providedAddresses /= addresses || not (provided `fitsImport` declared)) (Left (ImportTypeMismatch fieldName))
                Right provided
            _ -> Right declared
        MCons <$> note MinimumTooLarge (allocMemory addresses limits) <*> allocateMemories embedder (drop 1 origins) rest

-- | Every table, its entries null, from the shape: as 'allocateMemories'.
allocateTables :: Embedder -> [Maybe (Text, Text)] -> Sing (ts :: [TableShape]) -> Either InstantiationError (TableInsts ts)
allocateTables _ _ SNil = Right TNil
allocateTables embedder origins (SCons shape rest) = case fromSing shape of
    TableShape entries _ indices lo hi -> do
        let declared = Limits (fromIntegral lo) (fmap fromIntegral hi)
        limits <- case take 1 origins of
            [Just (moduleName, fieldName)] -> do
                (providedEntries, providedIndices, provided) <- note (UnsupportedImport moduleName fieldName) (embedder.tables moduleName fieldName)
                when (providedEntries /= entries || providedIndices /= indices || not (provided `fitsImport` declared)) (Left (ImportTypeMismatch fieldName))
                Right provided
            _ -> Right declared
        TCons <$> note MinimumTooLarge (allocTable limits) <*> allocateTables embedder (drop 1 origins) rest

{- | Whether what is provided has the limits an import declares (the spec's matching of
  limits): at least the minimum, and, if the import declares a maximum, one within it.
-}
fitsImport :: Limits -> Limits -> Bool
fitsImport provided declared = provided.min >= declared.min && maybe True (\most -> maybe False (<= most) provided.max) declared.max

-- | Copy the active data segments into their memories, in order.
placeData :: Embedder -> [DataSegment ms] -> MemSpaceInst ms -> Either InstantiationError (MemSpaceInst ms)
placeData embedder segments mems = foldM place mems (zip [0 ..] segments)
  where
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

-- | Write the active element segments into their tables, in order.
placeElements :: Embedder -> Int -> ElementSpace shape es -> TableSpaceInst fts (ModuleTables shape) kept tags -> Either InstantiationError (TableSpaceInst fts (ModuleTables shape) kept tags)
placeElements _ _ NoElements tables = Right tables
placeElements embedder index (Elements segment rest) tables = do
    written <- case segment.mode of
        WrittenTo at tableIx offsetExpr -> do
            offset <- offsetOf at <$> evalConst embedder offsetExpr
            references <- segmentReferences embedder segment
            -- (An offset past what a table holds is past the end of this one.)
            table <- note (ElementSegmentOutOfBounds index) (if offset > 0xFFFFFFFF then Nothing else writeEntries (fromIntegral offset) references (getTable tableIx tables))
            Right (setTable tableIx table tables)
        KeptForInit -> Right tables
        DeclaredOnly -> Right tables
    placeElements embedder (index + 1) rest written

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
