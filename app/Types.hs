{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Types where

import GHC.TypeLits (TypeError)
import Data.Kind (Type)
import Data.Int (Int32, Int64)
import Data.String ()
import Utils(Nat(S, Z), (:-), (:+), SNat(..))
import GHC.TypeError (ErrorMessage(Text))

{-
=============================================================================
FUNCTION TYPES
=============================================================================
-}
type FuncName = [Char]

data FuncTypeAnn (inputStack :: ValStackShape) (outputStack :: ValStackShape) where
    FFuncTypeAnn :: ValStackShape -> ValStackShape -> FuncTypeAnn inputStack outputStack


{-
=============================================================================
BLOCK TYPE
=============================================================================
-}
-- BlockType has parameters and results of WasmType
-- simplification of what actually happens in WASM Spec
data BlockType (params :: ValStackShape) (res :: ValStackShape) where
    BTParamsResults :: SValStackShape s -> SValStackShape t -> BlockType s t


{-
=============================================================================
(VALUE AND LABEL) STACK REPRESENTATION
=============================================================================
-}

data SValStackShape (s :: ValStackShape) where
    SEmpty :: SValStackShape 'EmptyValStack
    (::>) :: KnownWasmType t -> SValStackShape ts -> SValStackShape (t :> ts)


type family LenStackShape (s :: ValStackShape) :: Nat where
  LenStackShape 'EmptyValStack      = 'Z
  LenStackShape (t :> ts)   = 'S (LenStackShape ts)


stackShapeLen :: SValStackShape s -> SNat (LenStackShape s)
stackShapeLen SEmpty         = SZ
stackShapeLen (_kw ::> rest) = SS (stackShapeLen rest)

-- | Type-level representation of the WebAssembly stack.
-- The stack grows to the right: (I32 :> I32 :> Empty) means two I32s on stack.
infixr 5 :>  -- Right-associative operator with precedence 5
data ValStackShape where
    EmptyValStack :: ValStackShape
    (:>) :: WasmType -> ValStackShape -> ValStackShape

-- | Type family that reverses a ValStackShape.
type family Reverse (s :: ValStackShape) :: ValStackShape where
  Reverse EmptyValStack    = EmptyValStack
  Reverse (t :> s) = Reverse s +>+ (t :> EmptyValStack)

-- | Type family that takes the top n elements from a ValStackShape.
type family Take (n :: Nat) (s :: ValStackShape) :: ValStackShape where
  Take 'Z       s         = 'EmptyValStack
  Take ('S n)   (t :> s)  = t :> Take n s
  Take ('S n)   'EmptyValStack    = TypeError ('Text "take: stack too small")

-- | Type family that drops the top n elements from a ValStackShape.
type family Drop (n :: Nat) (s :: ValStackShape) :: ValStackShape where
  Drop 'Z       s         = s
  Drop ('S n)   (t :> s)  = Drop n s
  Drop ('S n)   'EmptyValStack    = TypeError ('Text "drop: stack too small")


-- | Stack concatenation at the type level.
-- This combines two stack shapes: upper sits on top of lower.
-- Example: (I32 :> Empty) +>+ (I32 :> I32 :> Empty) = (I32 :> I32 :> I32 :> Empty)
type family (upper :: ValStackShape) +>+ (lower :: ValStackShape) :: ValStackShape where
    EmptyValStack +>+ lower = lower
    (top :> upper) +>+ lower = top :> (upper +>+ lower)
infixl 5 +>+


-- Save the stack length of the current value stack along with the label type on the label stack
data LabelStackShape (l :: Nat) where
    EmptyLabels :: LabelStackShape 'Z
    (:>:) :: (ValStackShape, Nat) -> LabelStackShape l -> LabelStackShape ('S l)


-- | Type family to remove top n labels from a LabelStackShape.
type family RemoveLabels (i :: Nat) (labels :: LabelStackShape l) :: LabelStackShape (l :- 'S i) where
    RemoveLabels 'Z ('(l, _) :>: ls) = ls
    RemoveLabels ('S i) ('(t, _) :>: ts) = RemoveLabels i ts

-- | Type family to concatenate two LabelStackShapes.
type family ConcatLabelStacks (ls1 :: LabelStackShape l1) (ls2 :: LabelStackShape l2) :: LabelStackShape (l1 :+ l2) where
    ConcatLabelStacks EmptyLabels ls2 = ls2
    ConcatLabelStacks (t :>: ts) ls2 = t :>: ConcatLabelStacks ts ls2

-- | Type family to check if a LabelStackShape includes a specific ValStackShape.
type family IncludesLabelType (labelType :: ValStackShape) (labels :: LabelStackShape l) :: Bool where
    IncludesLabelType labelType EmptyLabels = 'False
    IncludesLabelType labelType ('(labelType, _) :>: ls) = 'True
    IncludesLabelType labelType ('(t, _) :>: ls) = IncludesLabelType labelType ls


type family GetNthLabelType (n :: Nat) (labels :: LabelStackShape l) :: (ValStackShape, Nat) where
    GetNthLabelType 'Z ('(t, lenInput) :>: ts)       = '(t, lenInput)
    GetNthLabelType ('S n) ('(t, _) :>: ts)   = GetNthLabelType n ts


type family StackLength (s :: ValStackShape) :: Nat where
    StackLength EmptyValStack       = 'Z
    StackLength (t :> ts)  = 'S (StackLength ts)


--------------------------------------
---- EQUALITY CHECKS ON STACKS
---------------------------------------
type family CheckTopEqual (top :: ValStackShape) (stack :: ValStackShape) :: Bool where
    CheckTopEqual EmptyValStack stack = 'True
    CheckTopEqual (t :> ts) (t :> ss) = CheckTopEqual ts ss
    CheckTopEqual top stack = TypeError ('Text "Top of stack does not match expected type.")

type family CheckEqualStacks (s1 :: ValStackShape) (s2 :: ValStackShape) :: Bool where
    CheckEqualStacks EmptyValStack EmptyValStack = 'True
    CheckEqualStacks (t :> ts) (t :> ss) = CheckEqualStacks ts ss
    CheckEqualStacks s1 s2 = 'False


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


type family GetLabelType (n :: Nat) (labels :: LabelStackShape l) :: ValStackShape where
    GetLabelType 'Z ('(t, _) :>: ts)       = t
    GetLabelType ('S n) ('(t, _) :>: ts)   = GetLabelType n ts

type family GetLabelCreationStackLength (n :: Nat) (labels :: LabelStackShape l) :: Nat where
    GetLabelCreationStackLength 'Z ('(t, lenInput) :>: ts)       = lenInput
    GetLabelCreationStackLength ('S n) ('(t, _) :>: ts)   = GetLabelCreationStackLength n ts



-- | Type family that maps WebAssembly types to their Haskell representations.
-- This is how we connect the type-level WebAssembly types to actual runtime values.
type family RuntimeTypeOf (wasmType :: WasmType) :: Type where
    RuntimeTypeOf I32 = Int32
    RuntimeTypeOf I64 = Int64
