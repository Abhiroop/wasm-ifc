{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module WasmModule where 
import GHC.TypeLits (Nat)  
import Types (WasmType(..))    
import Utils  
import Data.Int (Int32)
import Data.Word (Word32, Word64)
-- https://webassembly.github.io/spec/core/syntax/modules.html#syntax-global
-- WebAssembly programs are organized into modules, 
-- which are the unit of deployment, loading, and compilation.
-- A module collects definitions for types, functions, tables, memories, and globals.
-- In addition, it can declare imports and exports and provide initialization
-- in the form of data and element segments, or a start function.
-- Each of the vectors – and thus the entire module – may be empty.

data Mutability = Const | Var

data KnownMutability (m :: Mutability) where
    SConst :: KnownMutability 'Const
    SVar   :: KnownMutability 'Var

-- Global types classify global variables, which hold a value and can either be mutable or immutable.
data GlobalType = GlobalTypeMW Mutability WasmType

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
type GlobalsShape n = Vec n GlobalType

type family GetGlobalsShape (m :: WasmModuleShape) :: SNat where
    GetGlobalsShape ('WasmModuleShape globalsShape _) = globalsShape

type family GetMemoriesShape (m :: WasmModuleShape) :: SNat where
    GetMemoriesShape ('WasmModuleShape _ memoriesShape) = memoriesShape

data WasmModuleShape = WasmModuleShape {
    globalsShape :: SNat,
    memoriesShape :: SNat
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
data WasmModule (shape :: WasmModuleShape) = WasmModule {
    globals :: GlobalsShape (GetGlobalsShape shape),
    mems :: MemoriesShape (GetMemoriesShape shape)
    -- , x :: String
    -- types :: XYZ,
    }

type family GetGlobals (m :: WasmModule shape) :: Vec (GetGlobalsShape shape) GlobalType where
    GetGlobals ('WasmModule globals _) = globals

-- Type family to extract WasmType from GlobalType
-- ABHI: We need something here that discards the mutability information
--      Define a type family called GlobalTypeToWasmType here.
type family GlobalTypeToWasmType (g :: GlobalType) :: WasmType where
    GlobalTypeToWasmType (GlobalTypeMW _ w) = w



type GlobalSlot = Nat


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

data Limits = Limits Word32 (Maybe Word32)
newtype MemoryType = MemoryType Limits

-- Is a vector with memory type which defines the limits of the memory space.
type MemoriesShape n = Vec n MemoryType

data MemArg (alignment :: Word32) (offset :: Word64)where-- Memory Offset Alignment
    SMemArg :: MemArg alignment offset-- Is this ok? or do we need to have an "incremental" constructor?
    -- because we have it simply defined like this we have it as unsigned integers like in the 
    -- spec https://webassembly.github.io/spec/core/syntax/instructions.html#memory-instructions


type family GetMems (m :: WasmModule shape) :: Vec (GetMemoriesShape shape) MemoryType where
    GetMems ('WasmModule _ mems) = mems
