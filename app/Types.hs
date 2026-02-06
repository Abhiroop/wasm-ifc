{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}


module Types where

import Data.Int (Int32, Int64)
import Data.Kind (Type)
import Data.String ()
import GHC.TypeError (ErrorMessage (Text))
import GHC.TypeLits (TypeError)
import Utils
type family CheckTopVecEqual (top :: ValStackShape) (stack :: ValStackShape) :: Bool where
    CheckTopVecEqual '[] s2 = 'True
    CheckTopVecEqual s s = 'True
    CheckTopVecEqual (t :~ l1 ': ts) (t :~ l2 ': ss) = CheckTopVecEqual ts ss
    CheckTopVecEqual (t1 :~ _ ': _) (t2 :~ _ ': _) = False

    
type LocalsShape = [SecWasmType]

type family CombineLocalSecLevel (local :: SecWasmType) (secPC :: SecLevel) :: SecWasmType where
    CombineLocalSecLevel (t :~ l1) l2 = (t :~ (l1 :/\ l2))

type family SetSecLevelLocals (i :: Nat) (l :: SecLevel) (locals :: LocalsShape) :: LocalsShape where
    SetSecLevelLocals 'Z l ((w :~ oldL) ': locals) = ((w :~ l) ': locals)
    SetSecLevelLocals ('S i) l (currLocal ': rest) =
        currLocal ': SetSecLevelLocals i l rest

-- type family to combine two LocalsShapes sec type => needed for if instructions
-- this is overly careful but works
type family CombineSecTypes (l1 :: LocalsShape) (l2 :: LocalsShape) :: LocalsShape where
    CombineSecTypes '[] '[] = '[]
    CombineSecTypes ((t :~ l1) ': rest1) ((t :~ l2) ': rest2) =
        (t :~ (l1 :/\ l2)) ': CombineSecTypes rest1 rest2
    CombineSecTypes l1 l2 =
        TypeError ('Text "CombineSecTypes: LocalsShapes have different WasmTypes")

type family CheckWasmTypesInLocalsEqual (l1 :: LocalsShape) (l2 :: LocalsShape) :: Bool where
    CheckWasmTypesInLocalsEqual '[] '[] = 'True
    CheckWasmTypesInLocalsEqual l l = 'True
    CheckWasmTypesInLocalsEqual ((t :~ l1) ': rest1) ((t :~ l2) ': rest2) =
        CheckWasmTypesInLocalsEqual rest1 rest2
    CheckWasmTypesInLocalsEqual (sect ': rest1) (sect ': rest2) =
        CheckWasmTypesInLocalsEqual rest1 rest2
    CheckWasmTypesInLocalsEqual ((t1 :~ l1) ': rest1) ((t2 :~ l2) ': rest1) =
        False
        

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
    { types :: [SecWasmType]
    , height :: Nat
    }

-- HACK: no automatic way of projecting at type level?
type family Types (shape :: LabelShape) :: [SecWasmType] where
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

knownStackShapeLen :: KnownValStackShape (v :: [SecWasmType]) -> SNat (Length v)
knownStackShapeLen KnownValVNil = SZ
knownStackShapeLen (KnownValCons (_sec, _kw) rest) = SS (knownStackShapeLen rest)

{- | Type-level representation of the WebAssembly stack.
The stack grows to the right: (I32 ': I32 ': []) means two I32s on stack.
-}
type ValStackShape = [SecWasmType]

data KnownValStackShape (s :: ValStackShape) where
    KnownValVNil :: KnownValStackShape '[]
    KnownValCons ::
        (KnownSecLevel l,KnownWasmType t) -> KnownValStackShape ts -> KnownValStackShape ((t :~ l) ': ts)

type family CombineValSecTypes (vs1 :: ValStackShape) (vs2 :: ValStackShape) :: ValStackShape where
    CombineValSecTypes '[] '[] = '[]
    CombineValSecTypes ((t :~ l1) ': rest1) ((t :~ l2) ': rest2) =
        (t :~ (l1 :/\ l2)) ': CombineValSecTypes rest1 rest2
    CombineValSecTypes v1 v2 =
        TypeError ('Text "CombineValSecTypes: ValStackShapes have different WasmTypes")

type family CheckValStackShapesEqual (vs1 :: ValStackShape) (vs2 :: ValStackShape) :: Bool where
    CheckValStackShapesEqual '[] '[] = 'True
    CheckValStackShapesEqual ((t :~ l1) ': rest1) ((t :~ l2) ': rest2) =
        CheckValStackShapesEqual rest1 rest2
    CheckValStackShapesEqual (t1 :~ _ ': _) (t2 :~ _ ': _) = 'False
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

{-
=============================================================================
IFC
=============================================================================
-}

data SecLevel = Low | High

infix 6 :~
data SecWasmType = (:~) WasmType SecLevel

data KnownSecLevel (l :: SecLevel) where
    IsLow  :: KnownSecLevel Low
    IsHigh :: KnownSecLevel High


type family CanFlow (l :: SecLevel) (l' :: SecLevel) :: Bool where
    CanFlow 'Low 'Low = 'True
    CanFlow 'Low 'High = 'True
    CanFlow 'High 'High = 'True
    CanFlow 'High 'Low = 'False

infixl 7 :/\
type family (:/\) (l :: SecLevel) (l' :: SecLevel) :: SecLevel where
    Low :/\ Low = Low
    _ :/\ _ = High

type family GetWasmType (swt :: SecWasmType) :: WasmType where
    GetWasmType (t :~ l) = t

type family GetSecLevel (swt :: SecWasmType) :: SecLevel where
    GetSecLevel (t :~ l) = l

type family CombineSecLevel (swt :: SecWasmType) (secPC :: SecLevel) :: SecWasmType where
    CombineSecLevel (t :~ l1) l2 = (t :~ (l1 :/\ l2))

type family RuntimeSecTypeOf (swt :: SecWasmType) :: Type where
    RuntimeSecTypeOf (t :~ _) =  RuntimeTypeOf t

