{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Refactor.Types where

import Data.Int (Int32, Int64)
import Data.Kind (Type)
import Data.String ()
import GHC.TypeError (ErrorMessage (Text))
import GHC.TypeLits (TypeError)
import Utils (Nat (S, Z), SNat (..), Vec (..), (:-), (:==), type (+:), type (:+))

type family CheckSameVecType (xs :: [a]) (ys :: [a]) :: Bool where
    CheckSameVecType (xs :: [a]) (ys :: [a]) =
        Length xs :== Length ys

-- CheckSameVecType _ _ = 'False

type family CheckTopVecEqual (top :: ValStackShape) (stack :: ValStackShape) :: Bool where
    CheckTopVecEqual '[] s2 = 'True
    CheckTopVecEqual (t ': ts) (t ': ss) = CheckTopVecEqual ts ss
    CheckTopVecEqual s1 s2 = 'False

{-
=============================================================================
FUNCTION TYPES
=============================================================================
-}
type FuncName = [Char]

data FuncTypeAnn (inputStack :: ValStackShape) (outputStack :: ValStackShape) where
    FFuncTypeAnn ::
        ValStackShape -> ValStackShape -> FuncTypeAnn inputStack outputStack

{-
=============================================================================
BLOCK TYPE
=============================================================================
-}
-- BlockType has parameters and results of WasmType
-- simplification of what actually happens in WASM Spec
data BlockType (params :: ValStackShape) (res :: ValStackShape) where
    BTParamsResults ::
        KnownValStackShape params -> KnownValStackShape res -> BlockType params res

{-
=============================================================================
LABEL THINGS
=============================================================================
-}

--- TODO move
type family Length (list :: [a]) :: Nat where
    Length '[] = Z
    Length (x ': xs) = S (Length xs)

data LabelShape = LabelShape
    { types :: [WasmType]
    , height :: Nat
    }

-- HACK: no automatic way of projecting at type level?
type family Types (shape :: LabelShape) :: [WasmType] where
    Types ('LabelShape types height) = types

type family Arity (shape :: LabelShape) :: Nat where
    Arity ('LabelShape types height) = Length types

type family Height (shape :: LabelShape) :: Nat where
    Height ('LabelShape types height) = height

type family GetLabelType (label :: LabelShape) :: ValStackShape where
    GetLabelType ('LabelShape types height) = types

type LabelStackShape = [LabelShape]

type family GetLabelCreationValStackLength (label :: LabelShape) :: Nat where
    GetLabelCreationValStackLength ('LabelShape types height) =
        height

-- | Type family to remove top n labels from a LabelStackShape.GetLabelCreationValStackLength
type family RemoveLabels (i :: Nat) (labels :: LabelStackShape) :: LabelStackShape where
    RemoveLabels 'Z (_ ': ls) = ls
    RemoveLabels ('S i) (_ ': ts) = RemoveLabels i ts

{- type family IncludesLabelType (labelType :: [WasmType]) (labels :: LabelStackShape) :: Bool where
    IncludesLabelType labelType '[] = 'False
    IncludesLabelType labelType (LabelShape labelType height ': ls) = 'True
    IncludesLabelType labelType ('(t, _) ': ls) = IncludesLabelType labelType ls -}

knownStackShapeLen :: KnownValStackShape (v :: [WasmType]) -> SNat (Length v)
knownStackShapeLen KnownValVNil = SZ
knownStackShapeLen (KnownValCons _kw rest) = SS (knownStackShapeLen rest)

{- | Type-level representation of the WebAssembly stack.
The stack grows to the right: (I32 ': I32 ': []) means two I32s on stack.
-}
type ValStackShape = [WasmType]

data KnownValStackShape (s :: ValStackShape) where
    KnownValVNil :: KnownValStackShape '[]
    KnownValCons ::
        KnownWasmType t -> KnownValStackShape ts -> KnownValStackShape (t ': ts)

type family AddComm (a :: Nat) (b :: Nat) :: Bool where
    AddComm a b = (a :+ b) :== (b :+ a)

-- | Type family that reverses a ValStackShape.
type family Reverse (s :: [a]) :: [a] where
    Reverse '[] = '[]
    Reverse (t ': (s :: [a])) = Reverse s +>+: (t ': '[])

type family Take (n :: Nat) (s :: [a]) :: [a] where
    Take 'Z s = '[]
    Take ('S n) (t ': s) = t ': Take n s
    Take ('S n) '[] = TypeError ('Text "take: stack too small")

-- | Type family that drops the top n elements from a ValStackShape.
type family Drop (n :: Nat) (s :: [a]) :: [a] where
    Drop 'Z s = s
    Drop ('S n) (t ': s) = Drop n s
    Drop ('S n) '[] = TypeError ('Text "drop: stack too small")

{- | Stack concatenation at the type level.
This combines two stack shapes: upper sits on top of lower.
Once from the left and once from the right since we need it both directions.
-}
type family (lower :: [a]) :+>+ (upper :: [a]) :: [a] where
    lower :+>+ '[] = lower
    lower :+>+ (top ': upper) = top ': (lower :+>+ upper)

infixr 5 :+>+

type family (upper :: [a]) +>+: (lower :: [a]) :: [a] where
    '[] +>+: lower = lower
    (top ': upper) +>+: lower = top ': (upper +>+: lower)
infixl 5 +>+:

type family (upper :: [a]) +<+: (lower :: [a]) :: [a] where

{-
=============================================================================
SCALAR VALUES AND TYPES
=============================================================================
-}

{- | WebAssembly value types.
Currently only supports 32-bit integers, but could be extended with:
I64, F32, F64, etc.
-}
data WasmType
    = I32
    | I64

type family (==) (a :: WasmType) (b :: WasmType) :: Bool where
    I32 == I32 = 'True
    I64 == I64 = 'True
    _ == _ = 'False

{- | Singleton type for WasmType.
This is a "witness" type that lets us bring type-level information
(the WasmType kind) into term-level code. This is a common pattern
in dependently-typed Haskell programming.
-}
data KnownWasmType (wasmType :: WasmType) where
    ForI32 :: KnownWasmType I32
    ForI64 :: KnownWasmType I64

-- Runtime representation of WASM values, with types encoded in the GADT
-- data RuntimeWasmTypes (t :: WasmType) where
--     RInt32 :: RuntimeTypeOf 'I32 -> RuntimeWasmTypes 'I32
--     RInt64 :: RuntimeTypeOf 'I64 -> RuntimeWasmTypes 'I64

type RuntimeWasmTypes = Int32

{- | Type family that maps WebAssembly types to their Haskell representations.
This is how we connect the type-level WebAssembly types to actual runtime values.
-}
type family RuntimeTypeOf (wasmType :: WasmType) :: Type where
    RuntimeTypeOf I32 = Int32
    RuntimeTypeOf I64 = Int64
