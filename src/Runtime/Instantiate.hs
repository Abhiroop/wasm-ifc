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

import Data.Bifunctor (first)
import Data.ByteString qualified as BS
import Data.Singletons (Sing, fromSing)
import Data.Singletons.Base.TH (SList (SCons, SNil))
import Data.Singletons.Decide (decideEquality)
import Data.Text (Text)
import Data.Type.Equality ((:~:) (Refl))

import Runtime.Host (SomeWasiFunc (..), resolveWasiImport, wasiFuncType, wasiModuleName)
import Runtime.Interpreter (FuncInst (..), FuncInsts (..), ModuleInst (..), Outcome (..), getFunc, runFunction)
import Runtime.MemInst (allocMemory, writeBytes)
import Runtime.Module (SomeModuleInst (..))
import Runtime.Stack (DataInsts (..), MemInsts (..), TableInsts (..), ValueStack (..), initialGlobals)
import Runtime.TableInst (allocTable, setTableEntries)
import Runtime.Trap (Trap)
import Syntax.Functions (Functions (..))
import Syntax.Module (DataSegment (..), ElementSegment (..), Module (..), SomeModule (..))
import Syntax.Types
import Validation.Reflect (NonEmptyMems (..), memsNonEmpty)
import Validation.Shape

data InstantiationError
    = -- | an import (module, name) this host does not provide
      UnsupportedImport Text Text
    | -- | the import's declared type is not the host function's
      ImportTypeMismatch Text
    | -- | a WASI import requires the module to have a memory
      WasiNeedsMemory
    | -- | a data segment does not fit in memory 0 (or there is no memory)
      DataSegmentOutOfBounds Int
    | -- | an element segment does not fit in table 0 (or there is no table)
      ElementSegmentOutOfBounds Int
    | -- | the start function trapped
      StartFunctionTrapped Trap
    | -- | the start function called into the host, which instantiation cannot serve
      StartFunctionNeedsHost
    deriving stock (Eq, Show)

instantiate :: SomeModule -> Either InstantiationError SomeModuleInst
instantiate (SomeModule shapeS m) = case shapeS of
    SModuleShape ftsS _ msS tsS dsS -> do
        funcs <- link (memsNonEmpty msS) ftsS m.functions
        mems <- placeData m.dataSegments (allocateMemories msS)
        tables <- placeElements m.elements (allocateTables tsS)
        let inst = ModuleInst {funcs, globals = initialGlobals m.globals, mems, tables, dataSegments = remainingData dsS m.dataSegments}
        started <- runStart inst m.start
        Right (SomeModuleInst shapeS started m.exports)

{- | Link the functions: a defined one is its own instance; an import must come from the WASI
  module, name a function the host provides, be declared at exactly that function's type, and
  the module must have a memory (WASI requires one, and 'HostFunc' cannot be built without it).
-}
link :: Maybe (NonEmptyMems (ModuleMems shape)) -> Sing fts -> Functions shape fts -> Either InstantiationError (FuncInsts shape fts)
link _ SNil FunctionsNil = Right FsNil
link mems (SCons _ rest) (Defined f more) = FsCons (WasmFunc f) <$> link mems rest more
link mems (SCons (SFuncType psS rsS) rest) (Imported moduleName fieldName more)
    | moduleName /= wasiModuleName = Left (UnsupportedImport moduleName fieldName)
    | otherwise = case resolveWasiImport fieldName of
        Nothing -> Left (UnsupportedImport moduleName fieldName)
        Just (SomeWasiFunc wasiFunc) -> case wasiFuncType wasiFunc of
            SFuncType hostPsS hostRsS -> do
                Refl <- note (ImportTypeMismatch fieldName) (decideEquality psS hostPsS)
                Refl <- note (ImportTypeMismatch fieldName) (decideEquality rsS hostRsS)
                NonEmptyMems <- note WasiNeedsMemory mems
                FsCons (HostFunc wasiFunc) <$> link mems rest more

-- | Every memory at its declared minimum size, from the shape.
allocateMemories :: Sing (ms :: [MemShape]) -> MemInsts ms
allocateMemories SNil = MNil
allocateMemories (SCons shape rest) = MCons (allocMemory (limitsOf (fromSing shape))) (allocateMemories rest)
  where
    limitsOf (MemShape _ lo hi) = Limits (fromIntegral lo) (fmap fromIntegral hi)

-- | Every table at its declared minimum size, uninitialised, from the shape.
allocateTables :: Sing (ts :: [TableShape]) -> TableInsts fts ts
allocateTables SNil = TNil
allocateTables (SCons shape rest) = TCons (allocTable (limitsOf (fromSing shape))) (allocateTables rest)
  where
    limitsOf (TableShape lo hi) = Limits (fromIntegral lo) (fmap fromIntegral hi)

-- | Copy the active data segments into memory 0, in order.
placeData :: [DataSegment] -> MemInsts ms -> Either InstantiationError (MemInsts ms)
placeData segments mems = case (mems, [(i, off, s.bytes) | (i, s) <- zip [0 ..] segments, Just off <- [s.placement]]) of
    (_, []) -> Right mems
    (MCons mem rest, active) -> do
        mem' <- foldl (\acc (i, off, payload) -> acc >>= \current -> note (DataSegmentOutOfBounds i) (writeBytes current (fromIntegral off) (BS.unpack payload))) (Right mem) active
        Right (MCons mem' rest)
    (MNil, (i, _, _) : _) -> Left (DataSegmentOutOfBounds i)

-- | Place the element segments' functions into table 0, in order.
placeElements :: [ElementSegment fts] -> TableInsts fts ts -> Either InstantiationError (TableInsts fts ts)
placeElements [] tables = Right tables
placeElements segments (TCons table rest) = do
    table' <- foldl (\acc (i, segment) -> acc >>= \current -> note (ElementSegmentOutOfBounds i) (setTableEntries segment.offset segment.functions current)) (Right table) (zip [0 ..] segments)
    Right (TCons table' rest)
placeElements (_ : _) TNil = Left (ElementSegmentOutOfBounds 0)

{- | The data segments as @memory.init@ will find them: passive ones keep their bytes, active
ones are already dropped (instantiation copied them).
-}
remainingData :: Sing (ds :: [DataShape]) -> [DataSegment] -> DataInsts ds
remainingData SNil _ = DNil
remainingData (SCons SDataShape rest) (segment : more) = DCons (maybe (Just segment.bytes) (const Nothing) segment.placement) (remainingData rest more)
remainingData (SCons SDataShape rest) [] = DCons Nothing (remainingData rest [])

-- | Run the start function, if there is one, as the last step of instantiation.
runStart :: ModuleInst shape -> Maybe (Elem ('FuncType '[] '[]) (ModuleFuncs shape)) -> Either InstantiationError (ModuleInst shape)
runStart inst Nothing = Right inst
runStart inst (Just funcIx) = do
    outcome <- first StartFunctionTrapped (runFunction inst (getFunc funcIx inst.funcs) VNil)
    case outcome of
        Completed started _ -> Right started
        NeedsHost _ -> Left StartFunctionNeedsHost

note :: e -> Maybe a -> Either e a
note e = maybe (Left e) Right
