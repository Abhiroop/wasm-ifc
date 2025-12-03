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
import Utils(Nat(S, Z), (:-), type (:+), type (+:), (:==), SNat(..), Vec(..))
import GHC.TypeError (ErrorMessage(Text))


type family CheckSameVecType (xs :: Vec n a) (ys :: Vec m a) :: Bool where
    CheckSameVecType (xs :: Vec n a) (ys :: Vec m a)
        = (n :== m)
    -- CheckSameVecType _ _ = 'False

type family CheckTopVecEqual (top :: SomeValStackShape) (stack :: SomeValStackShape) :: Bool where
    CheckTopVecEqual ('SomeValStackShape VNil) s2 = 'True
    CheckTopVecEqual ('SomeValStackShape (t :<| ts)) ('SomeValStackShape (t :<| ss)) = CheckTopVecEqual ('SomeValStackShape ts) ('SomeValStackShape ss)
    CheckTopVecEqual s1 s2 = 'False

type family GetSpecificValVec (s :: SomeValStackShape) :: ValStackShape n where
    GetSpecificValVec ('SomeValStackShape v) = v

{-
=============================================================================
FUNCTION TYPES
=============================================================================
-}
type FuncName = [Char]

data FuncTypeAnn (inputStack :: ValStackShape n) (outputStack :: ValStackShape m) where
    FFuncTypeAnn :: ValStackShape n -> ValStackShape m -> FuncTypeAnn inputStack outputStack


{-
=============================================================================
BLOCK TYPE
=============================================================================
-}
-- BlockType has parameters and results of WasmType
-- simplification of what actually happens in WASM Spec
data BlockType (params :: ValStackShape s) (res :: ValStackShape t) where
    BTParamsResults :: KnownValStackShape params -> KnownValStackShape res -> BlockType params res


{-
=============================================================================
LABEL THINGS
=============================================================================
-}

type family GetLabelType (label :: (SomeValStackShape, Nat)) :: SomeValStackShape where
    GetLabelType '( t, _) = t

type LabelStackShape (l :: Nat) = Vec l (SomeValStackShape, Nat)
    

type family GetLabelCreationValStackLength (label :: (SomeValStackShape, Nat)) :: Nat where
    GetLabelCreationValStackLength '(t, lenInput)  
         = lenInput
-- | Type family to remove top n labels from a LabelStackShape.
type family RemoveLabels (i :: Nat) (labels :: LabelStackShape l) :: LabelStackShape (l :- 'S i) where
    RemoveLabels 'Z ('(l, _) :<| ls) = ls
    RemoveLabels ('S i) ('(t, _) :<| ts) = RemoveLabels i ts

type family IncludesLabelType (labelType :: ValStackShape lts) (labels :: LabelStackShape l) :: Bool where
    IncludesLabelType labelType VNil = 'False
    IncludesLabelType labelType ('( 'SomeValStackShape labelType, _) :<| ls) = 'True
    IncludesLabelType labelType ('(t, _) :<| ls) = IncludesLabelType labelType ls


knownStackShapeLen :: KnownValStackShape (v :: Vec n WasmType) -> SNat n
knownStackShapeLen KnownValVNil         = SZ
knownStackShapeLen (KnownValCons _kw rest) = SS (knownStackShapeLen rest)

-- | Type-level representation of the WebAssembly stack.
-- The stack grows to the right: (I32 :<| I32 :<| VNil) means two I32s on stack.
type ValStackShape n = Vec n WasmType

-- existential valstackshape type
data SomeValStackShape where
    SomeValStackShape :: ValStackShape n -> SomeValStackShape

data KnownValStackShape (s :: ValStackShape n) where
    KnownValVNil :: KnownValStackShape 'VNil
    KnownValCons :: KnownWasmType t -> KnownValStackShape ts -> KnownValStackShape (t :<| ts)

type family AddComm (a :: Nat) (b :: Nat) :: Bool where
  AddComm a b = (a :+ b) :== (b :+ a)


-- | Type family that reverses a ValStackShape.
type family Reverse (s :: Vec n a) :: Vec n a where
  Reverse VNil    = VNil
  Reverse (t :<| (s :: Vec n a)) = Reverse s :+>+ (t :<| VNil)


type family Take (n :: Nat) (s :: Vec m a) :: Vec n a where
  Take 'Z       s         = 'VNil
  Take ('S n)   (t :<| s)  = t :<| Take n s
  Take ('S n)   'VNil    = TypeError ('Text "take: stack too small")

-- | Type family that drops the top n elements from a ValStackShape.
type family Drop (n :: Nat) (s :: Vec m a) :: Vec (m :- n) a where
  Drop 'Z       s         = s
  Drop ('S n)   (t :<| s)  = Drop n s
  Drop ('S n)   'VNil    = TypeError ('Text "drop: stack too small")


-- | Stack concatenation at the type level.
-- This combines two stack shapes: upper sits on top of lower.
-- Once from the left and once from the right since we need it both directions.
type family (lower :: Vec n a) :+>+ (upper :: Vec m a) :: Vec (n :+ m) a where
    lower :+>+ VNil = lower
    lower :+>+ (top :<| upper) = top :<| (lower :+>+ upper)
infixr 5 :+>+

type family (upper :: Vec n a) +>+: (lower :: Vec m a) :: Vec (n +: m) a where
    VNil +>+: lower = lower
    (top :<| upper) +>+: lower = top :<| (upper +>+: lower)
infixl 5 +>+:

type family (upper :: Vec n a) +<+: (lower :: Vec m a) :: Vec (n +: m) a where



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

type family (==) (a :: WasmType) (b :: WasmType) :: Bool
    where
    I32 == I32 = 'True
    I64 == I64 = 'True
    _ == _ = 'False

-- | Singleton type for WasmType.
-- This is a "witness" type that lets us bring type-level information
-- (the WasmType kind) into term-level code. This is a common pattern
-- in dependently-typed Haskell programming.
data KnownWasmType (wasmType :: WasmType) where
    ForI32 :: KnownWasmType I32
    ForI64 :: KnownWasmType I64

-- Runtime representation of WASM values, with types encoded in the GADT
-- data RuntimeWasmTypes (t :: WasmType) where
--     RInt32 :: RuntimeTypeOf 'I32 -> RuntimeWasmTypes 'I32
--     RInt64 :: RuntimeTypeOf 'I64 -> RuntimeWasmTypes 'I64

type RuntimeWasmTypes = Int32



-- | Type family that maps WebAssembly types to their Haskell representations.
-- This is how we connect the type-level WebAssembly types to actual runtime values.
type family RuntimeTypeOf (wasmType :: WasmType) :: Type where
    RuntimeTypeOf I32 = Int32
    RuntimeTypeOf I64 = Int64
