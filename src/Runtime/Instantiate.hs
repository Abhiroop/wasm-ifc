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
) where

import Control.Monad (foldM)
import Data.Bifunctor (first)
import Data.ByteString qualified as BS
import Data.Singletons (Sing, fromSing)
import Data.Singletons.Base.TH (SList (SCons, SNil))
import Data.Text (Text)
import Data.Word (Word32)

import Runtime.Host (SomeWasiFunc (..), resolveWasiImport, wasiFuncType, wasiModuleName)
import Runtime.Interpreter (FuncInst (..), FuncSpaceInst (..), ModuleInst (..), Outcome (..), getFunc, runFunction)
import Runtime.MemInst (allocMemory, labelRange, writeBytes)
import Runtime.Module (SomeModuleInst (..))
import Runtime.Stack (DataSpaceInst (..), ElemSpaceInst (..), MemSpaceInst (..), TableInsts (..), TableSpaceInst (..), ValueStack (..), getTable, initialGlobals, setTable)
import Runtime.TableInst (allocTable, functionDirectory, writeEntries)
import Runtime.Trap (Trap)
import Syntax.Functions (FunctionSpace (..))
import Syntax.Module (DataSegment (..), ElementMode (..), ElementSegment (..), ElementSpace (..), Module (..), SomeModule (..), constReference)
import Syntax.Types
import Syntax.TypesIFC (LabelledFuncType (..), SLabelledFuncType (..), SSecLevel (..), SecLevel (..), decideSameValueTypes, decideSegmentFlows)
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
    | -- | a data segment does not fit in memory 0 (or there is no memory)
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
instantiate (SomeModule shapeS m) = case shapeS of
    SModuleShape ftsS _ msS tsS dsS _ -> do
        funcs <- link (memsNonEmpty msS) ftsS m.functions
        placed <- placeData m.dataSegments (allocateMemories msS)
        mems <- labelRegions m.secretRegions placed
        tables <- placeElements 0 m.elementSegments (TableSpaceInst (functionDirectory (allFuncRefs ftsS)) (allocateTables tsS) (keptElements m.elementSegments))
        let inst = ModuleInst {functions = funcs, globals = initialGlobals m.globals, memories = mems, tables, dataSegments = remainingData dsS m.dataSegments}
        started <- runStart inst m.start
        Right (SomeModuleInst shapeS started m.exports)

{- | Link the functions: a defined one is its own instance; an import must come from the WASI
  module, name a function the host provides, be declared at exactly that function's type, and
  the module must have a memory (WASI requires one, and 'HostFunc' cannot be built without it).
-}
link :: Maybe (NonEmptyMems (ModuleMems shape)) -> Sing fts -> FunctionSpace shape fts -> Either InstantiationError (FuncSpaceInst shape fts)
link _ SNil NoFunctions = Right FsNil
link mems (SCons _ rest) (Defined f more) = FsCons (WasmFunc f) <$> link mems rest more
link mems (SCons (SLabelledFuncType boundS psS rsS) rest) (Imported moduleName fieldName more)
    | moduleName == ghostModuleName = FsCons GhostFunc <$> link mems rest more
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
                    SLow -> FsCons (HostFunc wasiFunc argsPublic resultsAgree) <$> link mems rest more
                    SHigh -> Left (ImportNotPublic fieldName)
            SLabelledFuncType SHigh _ _ -> Left (ImportTypeMismatch fieldName)

-- | Every memory at its declared minimum size, from the shape.
allocateMemories :: Sing (ms :: [MemShape]) -> MemSpaceInst ms
allocateMemories SNil = MNil
allocateMemories (SCons shape rest) = MCons (allocMemory (limitsOf (fromSing shape))) (allocateMemories rest)
  where
    limitsOf (MemShape _ lo hi) = Limits (fromIntegral lo) (fmap fromIntegral hi)

-- | Every table at its declared minimum size, its entries null, from the shape.
allocateTables :: Sing (ts :: [TableShape]) -> TableInsts ts
allocateTables SNil = TNil
allocateTables (SCons shape rest) = TCons (allocTable (limitsOf (fromSing shape))) (allocateTables rest)
  where
    limitsOf (TableShape _ _ lo hi) = Limits (fromIntegral lo) (fmap fromIntegral hi)

-- | Copy the active data segments into memory 0, in order.
placeData :: [DataSegment] -> MemSpaceInst ms -> Either InstantiationError (MemSpaceInst ms)
placeData segments mems = case (mems, [(i, off, s.bytes) | (i, s) <- zip [0 ..] segments, Just off <- [s.placement]]) of
    (_, []) -> Right mems
    (MCons mem rest, active) -> do
        mem' <- foldl (\acc (i, off, payload) -> acc >>= \current -> note (DataSegmentOutOfBounds i) (writeBytes current (fromIntegral off) (BS.unpack payload))) (Right mem) active
        Right (MCons mem' rest)
    (MNil, (i, _, _) : _) -> Left (DataSegmentOutOfBounds i)

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
placeElements :: Int -> ElementSpace shape es -> TableSpaceInst fts (ModuleTables shape) kept -> Either InstantiationError (TableSpaceInst fts (ModuleTables shape) kept)
placeElements _ NoElements tables = Right tables
placeElements index (Elements segment rest) tables = do
    written <- case segment.mode of
        WrittenTo tableIx offset -> do
            table <- note (ElementSegmentOutOfBounds index) (writeEntries offset (map constReference segment.items) (getTable tableIx tables))
            Right (setTable tableIx table tables)
        KeptForInit -> Right tables
        DeclaredOnly -> Right tables
    placeElements (index + 1) rest written

{- | The element segments as @table.init@ will find them: passive ones keep their references,
active and declarative ones are already dropped.
-}
keptElements :: ElementSpace shape es -> ElemSpaceInst es
keptElements NoElements = ENil
keptElements (Elements segment rest) = ECons kept (keptElements rest)
  where
    kept = case segment.mode of
        KeptForInit -> map constReference segment.items
        _ -> []

{- | The data segments as @memory.init@ will find them: passive ones keep their bytes, active
ones are already dropped (instantiation copied them).
-}
remainingData :: Sing (ds :: [DataShape]) -> [DataSegment] -> DataSpaceInst ds
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
