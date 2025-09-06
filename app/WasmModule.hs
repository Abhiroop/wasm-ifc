{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}

module WasmModule where 
import GHC.TypeLits (Nat, type (-))  
import Types (WasmType(..)) 
import GHC.TypeError (TypeError, ErrorMessage(..))    
import Utils  
import Data.Kind (Type)
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
data GlobalType = GlobalType Mutability WasmType
 

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
data WasmModule (n::SNat) = WasmModule {
    globals :: GlobalsShape n
    -- , x :: String
    -- types :: XYZ,
    }

type GlobalSlot = Nat




