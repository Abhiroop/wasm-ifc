{-
TODO Summary:
1. Line 106: ignore alignment for now
2. Line 143: Maybe we still need to not the limits here to check whether the memory can grow or whether we have a maximum size!
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module WasmModule where

import Data.Word (Word32, Word64, Word8)
import Types 
import Utils
import GHC.TypeError (ErrorMessage (Text))
import GHC.TypeLits (TypeError)

-- https://webassembly.github.io/spec/core/syntax/modules.html#syntax-global
-- WebAssembly programs are organized into modules,
-- which are the unit of deployment, loading, and compilation.
-- A module collects definitions for types, functions, tables, memories, and globals.
-- In addition, it can declare imports and exports and provide initialization
-- in the form of data and element segments, or a start function.
-- Each of the vectors – and thus the entire module – may be empty.

data Mutability = Const | Var

type family IsVarMutability (m :: Mutability) :: Bool where
    IsVarMutability 'Const = 'False
    IsVarMutability 'Var = 'True

data KnownMutability (m :: Mutability) where
    SConst :: KnownMutability 'Const
    SVar :: KnownMutability 'Var

-- Global types classify global variables, which hold a value and can either be mutable or immutable.
data GlobalType = GlobalTypeMW Mutability SecWasmType

type family GetMutability (g :: GlobalType) :: Mutability where
    GetMutability (GlobalTypeMW m w) = m

-- The global component of a module defines a vector of global variables (or globals for short):
-- Each global stores a single value of the given global type.
-- Its also specifies whether a global is immutable or mutable.
-- Moreover, each global is initialized with an value given by a constant initializer expression.
-- global ::= {type globaltype, init expr}

-- technically we do global.get x
-- where a = globaladdr[x]
-- where val = globals[a]
-- this is in execution in validation it doesn't go throught the globaladdr

-- type GlobalsShape = [GlobalType]
type GlobalsShape = [GlobalType]

type family GetGlobalsShape (m :: WasmModuleShape) :: Nat where
    GetGlobalsShape ('WasmModuleShapeR globalsShape _) = globalsShape

type family GetMemoriesShape (m :: WasmModuleShape) :: Nat where
    GetMemoriesShape ('WasmModuleShapeR _ memoriesShape) = memoriesShape

data WasmModuleShape = WasmModuleShapeR
    { globalsShape :: Nat
    , memoriesShape :: Nat
    }

-- module ::== {
-- types vec(functype),
-- funcs vec(func),
-- tables vec(table),
-- mems vec(global),
-- elems vec(elem),
-- datas vec(data),
-- start start?,
-- import vec(import),
-- exports vec(export)
--    }
data WasmModule (shape :: WasmModuleShape) = WasmModuleR
    { globals :: GlobalsShape
    , mems :: MemoriesShape
    -- , x :: String
    -- types :: XYZ,
    }

type family GetGlobals (m :: WasmModule shape) :: [GlobalType] where
    GetGlobals ('WasmModuleR globals _) = globals

-- Type family to extract WasmType from GlobalType
-- ABHI: We need something here that discards the mutability information
--      Define a type family called GlobalTypeToWasmType here.
type family GlobalTypeToWasmType (g :: GlobalType) :: SecWasmType where
    GlobalTypeToWasmType (GlobalTypeMW _ w) = w

type family CombineGlobalSecLevel (g :: GlobalType) (secPC :: SecLevel) :: SecWasmType where
    CombineGlobalSecLevel (GlobalTypeMW _ (w :~ l)) secPC = w :~ (l :/\ secPC)

type GlobalSlot = Nat

type family SetSecLevelsGlobalModule (i :: Nat) (newSecLevel :: SecLevel) (wasmModule :: WasmModule shape) :: WasmModule shape where
    SetSecLevelsGlobalModule i newSecLevel ('WasmModuleR globals mems) =
        'WasmModuleR (SetSecLevelGlobals i newSecLevel globals) mems

type family SetSecLevelGlobals (i :: Nat) (newSecLevel :: SecLevel) (globalsShape :: GlobalsShape) :: GlobalsShape where
    SetSecLevelGlobals 'Z newSecLevel (GlobalTypeMW mut (v :~ oldSecLevel) ': rest) =
        GlobalTypeMW mut (v :~ newSecLevel) ': rest
    SetSecLevelGlobals ('S i) newSecLevel (g ': rest) =
        g ': SetSecLevelGlobals i newSecLevel rest

type family CombineSecTypesGlobalModule (wasmModule1 :: WasmModule shape) (wasmModule2 :: WasmModule shape) :: WasmModule shape where
    CombineSecTypesGlobalModule ('WasmModuleR globals1 mems) ('WasmModuleR globals2 mems) =
        'WasmModuleR (CombineSecTypesGlobals globals1 globals2) mems -- mems unchanged

type family CombineSecTypesGlobals (globals1 :: GlobalsShape) (globals2 :: GlobalsShape) :: GlobalsShape where
    CombineSecTypesGlobals '[] '[] = '[]
    CombineSecTypesGlobals (GlobalTypeMW mut (w :~ sec1) ': rest1) (GlobalTypeMW mut (w :~ sec2) ': rest2) =
        GlobalTypeMW mut (w :~ sec1 :/\ sec2) ': CombineSecTypesGlobals rest1 rest2
    CombineSecTypesGlobals g1 g2 =
        TypeError ('Text "CombineSecTypesGlobals: GlobalsShapes have different GlobalTypes")

-- TODO depending on what we do with memory
-- type family CheckWasmTypesInModuleUnchanged (wasmModule1 :: WasmModule shape) (wasmModule2 :: WasmModule shape) :: Bool where
--     CheckWasmTypesInModuleUnchanged ('WasmModuleR globals1 mems1) ('WasmModuleR globals2 mems2) =
--         CheckGlobalsTypesUnchanged globals1 globals2 -- && CheckMemoriesTypesUnchanged mems1 mems2

type family CheckGlobalsTypesUnchanged (globals1 :: GlobalsShape) (globals2 :: GlobalsShape) :: Bool where
    CheckGlobalsTypesUnchanged '[] '[] = 'True
    CheckGlobalsTypesUnchanged g g = 'True
    CheckGlobalsTypesUnchanged (GlobalTypeMW mut (w :~ l1) ': rest1) (GlobalTypeMW mut (w :~ l2) ': rest2) = 
        CheckGlobalsTypesUnchanged rest1 rest2
    CheckGlobalsTypesUnchanged g1 g2 = 'False


-----------------
-- MEMORY
-----------------
-- mem ::== {type memtype}
-- memtype ::== limits
-- limits constrain the minimum and optionally the maximum size of a memory.
-- The limits are given in units of page size -> always a multiple of the WebAssembly page size = 65536
-- Approach 1: Define based on the limits a vector with a size and then with offset access that vector?
-- Based on spec one entry in memory vector is 1 Byte or 8 bits.
-- Hence we reserve 4 entries for a 32 bit integer e.g.
-- ignore alignment for now, TODO

-- technically also addr type that defines whether the address is i32 or i64
-- https://webassembly.github.io/spec/core/syntax/types.html#syntax-memtype
-- data MemoryArray where
--     MemoryArrayR :: SNat n -> (Vec n WasmType) -> MemoryArray

-- data SomeWasmType where
--     SomeWasmType :: RuntimeWasmTypes t -> SomeWasmType
type MemoryArray = [Word8]
data Limits = LimitsR Word64 (Maybe Word64)

-- data MemoryType (n::Nat) where
--      MemoryTypeR :: SNat n -> Limits -> MemoryArray n -> MemoryType n

-- data SWord64 (n :: Word64) where
--     ZWord64 :: SWord64 (fromIntegral 0)
--     SWord64 :: Word64 -> SWord64 n

{-
data ValStackShape where
    EmptyValStack :: ValStackShape
    (:>) :: WasmType -> ValStackShape -> ValStackShape
-}
-- Is a vector with memory type which defines the limits of the memory space.
-- the first to arguments are the min and max limits
-- data MemoriesShapeStack where
--     EmptyMemShape :: MemoriesShapeStack
--     ConsMemShape :: (SWord64 n,Maybe (SWord64 m)) -> MemoriesShapeStack -> MemoriesShapeStack

-- TODO: Maybe we still need to not the limits here to check whether the memory can grow or whether we have a maximum size!
type MemoriesShape = [MemoryArray]

data SMemArray (memArray :: MemoryArray) where
    SMemArray :: MemoryArray -> SMemArray memArray

type family
    InsertMemory (idx :: Nat) (memArray :: MemoryArray) (memsShape :: MemoriesShape) ::
        MemoriesShape
    where
    InsertMemory Z memArray memsShape = memArray : memsShape
    InsertMemory (S idx) memArray (mem ': memsShape) =
        mem : InsertMemory idx memArray memsShape

data MemArg (alignment :: Word32) (offset :: Word64) where -- Memory Offset Alignment
    SMemArg :: Word32 -> Word64 -> MemArg alignment offset

-- Is this ok? or do we need to have an "incremental" constructor?
-- because we have it simply defined like this we have it as unsigned integers like in the
-- spec https://webassembly.github.io/spec/core/syntax/instructions.html#memory-instructions

type family GetMems (m :: WasmModule shape) :: [MemoryArray] where
    GetMems ('WasmModuleR _ mems) = mems

-- type family GetMemArrayFromMemoryType (memType :: MemoryType) :: List WasmType where
--     GetMemArrayFromMemoryType (_ arr) = arr

-- data RuntimeTypeOfMemory (memType :: MemoryType) where
--     RuntimeTypeOfMemory :: MemoryType -> RuntimeTypeOfMemory memType
