{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Types where

import GHC.TypeLits (Nat, CmpNat, TypeError)
import Data.Type.Equality (type (==))
import Data.Kind (Type)
import Data.Int (Int32, Int64)
import Data.String ()
import Utils(SNat(S, Z), (:-))
import GHC.TypeError (ErrorMessage(Text))

{-
=============================================================================
FUNCTION TYPES
=============================================================================
-}
type FuncName = [Char]

data FuncTypeAnn (inputStack :: StackShape) (outputStack :: StackShape) where
    FFuncTypeAnn :: StackShape -> StackShape -> FuncTypeAnn inputStack outputStack


{-
=============================================================================
BLOCK TYPE
=============================================================================
-}
-- BlockType has parameters and results of WasmType
data BlockType (params :: StackShape) (res :: StackShape) where
    -- BTParamsResultsBothEmpty :: BlockType 'Empty 'Empty
    -- BTParamsEmptyResults :: SStackShape s -> BlockType 'Empty s
    -- BTParamsResultEmpty :: SStackShape s -> BlockType s 'Empty
    BTParamsResults :: SStackShape s -> SStackShape t -> BlockType s t
               -- | BT_TypeIdx SNat TODO also some sort of typeidx but not sure what to do about that yet


{-
=============================================================================
STACK REPRESENTATION
=============================================================================
-}

data SStackShape (s :: StackShape) where
    SEmpty :: SStackShape 'Empty
    (::>) :: KnownWasmType t -> SStackShape ts -> SStackShape (t :> ts)



-- data WasmOrLabelType = IsWasmType WasmType | Label | StackType StackShape-- if we go for the stack
    -- for the labels so we can put a stackshape on a stack
    -- therefore we can put the type of the label on the stack


-- | Type-level representation of the WebAssembly stack.
-- The stack grows to the right: (I32 :> I32 :> Empty) means two I32s on stack.
infixr 5 :>  -- Right-associative operator with precedence 5
-- data StackShape = Empty | (:>) WasmOrLabelType StackShape
data StackShape = Empty | (:>) WasmType StackShape

-- | Stack concatenation at the type level.
-- This combines two stack shapes: upper sits on top of lower.
-- Example: (I32 :> Empty) +>+ (I32 :> I32 :> Empty) = (I32 :> I32 :> I32 :> Empty)
type family (upper :: StackShape) +>+ (lower :: StackShape) :: StackShape where
    upper +>+ Empty = upper
    Empty +>+ lower = lower
    (top :> upper) +>+ lower = top :> (upper +>+ lower)

-- | Singleton type for stack shapes that we expect to return from blocks.
-- This lets us specify at the type level what shape a block should produce.
data KnownStackShape (stackShape :: StackShape) where
    NoReturn  :: KnownStackShape Empty                    -- Block returns nothing
    ReturnsOneWasmType :: KnownWasmType t -> KnownStackShape (t :> Empty)  -- Block returns one value

data LabelStack (l :: SNat) where
    EmptyLabels :: LabelStack 'Z
    (:>:) :: StackShape -> LabelStack l -> LabelStack ('S l)

type family RemoveLabels (i :: SNat) (labels :: LabelStack ('S l)) :: LabelStack (l :- i) where
    RemoveLabels 'Z (l :>: ls) = ls
    RemoveLabels ('S i) (t :>: ts) = RemoveLabels i ts

    
type family StackLength (s :: StackShape) :: SNat where
    StackLength Empty       = 'Z
    StackLength (t :> ts)  = 'S (StackLength ts)

-- type family GetLabelStackLength (ls :: LabelStack l) :: SNat where

data StackIndex (i :: SNat) (n :: SNat) where
    StackIndexZ :: StackIndex 'Z ('S n)
    StackIndexS :: StackIndex i n -> StackIndex ('S i) ('S n)

--------------------------------------
---- Labels on input Stack old try
---------------------------------------
type family CheckTopEqual (top :: StackShape) (stack :: StackShape) :: Bool where
    CheckTopEqual Empty _ = 'True
    CheckTopEqual (t :> ts) (t :> ss) = CheckTopEqual ts ss
    CheckTopEqual top stack = TypeError ('Text "Top of stack does not match expected type.")

-- Pop the labels out of the stack but make sure to add the other entries back
-- when the type family is first called the top parameter should be Empty
-- We return only everything on the stack without the label until the label we want
-- type family PopTopUntilLabelFromStack (nestedness :: SNat) (arity :: SNat) (top::StackShape) (stack :: StackShape) :: StackShape where
--     PopTopUntilLabelFromStack 'Z a t (Label :> ss) = ReturnTopWithCorrectArity a t Empty
--     PopTopUntilLabelFromStack ('S nestedness) a t (Label :> ss) = PopTopUntilLabelFromStack nestedness a t ss
--     PopTopUntilLabelFromStack nestedness a t (s :> ss) = PopTopUntilLabelFromStack nestedness a (s :> t) ss
--     PopTopUntilLabelFromStack 'Z _ t Empty = TypeError ('Text "Cannot pop more labels than present on stack.")

-- now we want a function the with the labeltype computes the arity and therefore only pushes the right number
-- of stack entries back onto the stack
-- then we can compare whether this is actually the correct label type
-- type family ReturnTopWithCorrectArity (arity :: SNat) (popped :: StackShape) (top :: StackShape) :: StackShape where
--     ReturnTopWithCorrectArity 'Z popped top = top -- if it is zero we don't put anything on the stack
--     ReturnTopWithCorrectArity ('S arity) (p :> ps) top = ReturnTopWithCorrectArity arity ps (p :> top)

{-
=============================================================================
SCALAR VALUES AND TYPES
=============================================================================
-}

-- | WebAssembly value types.
-- Currently only supports 32-bit integers, but could be extended with:
-- I64, F32, F64, etc.
data WasmType = I32
    | I64
-- | Singleton type for WasmType.
-- This is a "witness" type that lets us bring type-level information
-- (the WasmType kind) into term-level code. This is a common pattern
-- in dependently-typed Haskell programming.
data KnownWasmType (wasmType :: WasmType) where
    ForI32 :: KnownWasmType I32
    ForI64 :: KnownWasmType I64

-- data KnownWasmTypeOrLabel (wasmTypeOrLabel :: WasmOrLabelType) where
--     KnownWasmType :: KnownWasmType t -> KnownWasmTypeOrLabel ('IsWasmType t)
--     KnownLabel    :: KnownStackShape s -> KnownWasmTypeOrLabel 'Label

type family GetLabelType (n :: SNat) (labels :: LabelStack l) :: StackShape where
    GetLabelType 'Z (t :>: ts)       = t
    GetLabelType ('S n) (t :>: ts)   = GetLabelType n ts


-- data KnownLabelType (l :: StackShape)

-- | Type family that maps WebAssembly types to their Haskell representations.
-- This is how we connect the type-level WebAssembly types to actual runtime values.
type family RuntimeTypeOf (wasmType :: WasmType) :: Type where
    RuntimeTypeOf I32 = Int32
    RuntimeTypeOf I64 = Int64


-- type family RuntimeStackTypeOf (wasmType :: WasmOrLabelType) :: Type where
--     RuntimeStackTypeOf ('IsWasmType I32) = Int32
--     RuntimeStackTypeOf ('IsWasmType I64) = Int64
--     RuntimeStackTypeOf 'Label = () -- ??? not sure should be a stack shape I think

    
-- | Type-level comparison: is n less than m?
type family (n :: Nat) <? (m :: Nat) :: Bool where
    n <? m = CmpNat n m == 'LT