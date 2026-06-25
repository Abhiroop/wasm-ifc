{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}

-- | Reflection between the term level and the type level, and reconstruction of the typed
--   AST's indices ('Elem') and witnesses ('Append') from runtime data — what lets
--   elaboration recover a decoded module's hidden type indices.
--
--   The @singletons-th@ we depend on does not ship list singletons (those live in
--   @singletons-base@), so we hand-roll small singletons for stack shapes (@StackS@ for
--   @[ValType]@) and label contexts (@LabelS@ for @[[ValType]]@) over the generated
--   'SValType'/'SNumType'.
module Validation.Reflect
    ( StackS (..)
    , LabelS (..)
    , SomeStack (..)
    , SomeElem (..)
    , SomeLabel (..)
    , SomeSplit (..)
    , reflectStack
    , decideNumType
    , decideValType
    , decideStack
    , mkLocalElem
    , mkLabelElem
    , matchPrefix
    , sAppendS
      -- module-signature witnesses
    , SMut (..)
    , FuncTypeS (..)
    , FuncTypesS (..)
    , GlobalTypeS (..)
    , GlobalsS (..)
    , MemsS (..)
    , ModuleShapeS (..)
    , SomeModuleShapeS (..)
    , SomeFuncRef (..)
    , SomeGlobalRef (..)
    , NonEmptyMems (..)
    , reflectCtx
    , lookupFuncRef
    , lookupGlobalRef
    , memsNonEmpty
    ) where

import Data.Kind          (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Word          (Word32)
import GHC.TypeNats       (SNat, withSomeSNat)
import Numeric.Natural    (Natural)

import Syntax.Types  (AddrType (..), FuncType (..), GlobalType (..), Limits (..),
                      MemType (..), Mutability (..), NumType (..), SNumType (..), SValType (..),
                      ValType (..))
import Validation.Shape (Append (..), Elem (..), MemShape (..), ModuleShape (..), type (++))

{- *** Hand-rolled stack-shape singletons *** -}

-- | A singleton for a stack shape @[ValType]@.
type StackS :: [ValType] -> Type
data StackS s where
    SSNil  :: StackS '[]
    SSCons :: SValType v -> StackS vs -> StackS (v ': vs)

-- | A singleton for a label context @[[ValType]]@ (each label carries a stack shape).
type LabelS :: [[ValType]] -> Type
data LabelS ls where
    LSNil  :: LabelS '[]
    LSCons :: StackS rs -> LabelS rest -> LabelS (rs ': rest)

data SomeStack where
    SomeStack :: StackS s -> SomeStack

data SomeNumType where
    SomeNumType :: SNumType n -> SomeNumType

data SomeValType where
    SomeValType :: SValType v -> SomeValType

reflectNumType :: NumType -> SomeNumType
reflectNumType I32 = SomeNumType SI32
reflectNumType I64 = SomeNumType SI64
reflectNumType F32 = SomeNumType SF32
reflectNumType F64 = SomeNumType SF64

reflectValType :: ValType -> SomeValType
reflectValType (Num n) = case reflectNumType n of SomeNumType sn -> SomeValType (SNum sn)

-- | Reflect a term-level stack shape to its singleton, hidden existentially.
reflectStack :: [ValType] -> SomeStack
reflectStack []       = SomeStack SSNil
reflectStack (v : vs) = case (reflectValType v, reflectStack vs) of
    (SomeValType sv, SomeStack svs) -> SomeStack (SSCons sv svs)

{- *** Decidable equality *** -}

decideNumType :: SNumType a -> SNumType b -> Maybe (a :~: b)
decideNumType SI32 SI32 = Just Refl
decideNumType SI64 SI64 = Just Refl
decideNumType SF32 SF32 = Just Refl
decideNumType SF64 SF64 = Just Refl
decideNumType _    _    = Nothing

decideValType :: SValType a -> SValType b -> Maybe (a :~: b)
decideValType (SNum a) (SNum b) = (\Refl -> Refl) <$> decideNumType a b

decideStack :: StackS a -> StackS b -> Maybe (a :~: b)
decideStack SSNil         SSNil         = Just Refl
decideStack (SSCons x xs) (SSCons y ys) = do
    Refl <- decideValType x y
    Refl <- decideStack xs ys
    Just Refl
decideStack _ _ = Nothing

{- *** Index and witness construction *** -}

-- | @∃x. (SValType x, Elem x xs)@ — a bounds-checked index into a stack shape.
type SomeElem :: [ValType] -> Type
data SomeElem xs where
    SomeElem :: SValType x -> Elem x xs -> SomeElem xs

mkLocalElem :: StackS xs -> Word32 -> Maybe (SomeElem xs)
mkLocalElem (SSCons x _)  0 = Just (SomeElem x Here)
mkLocalElem (SSCons _ xs) n = (\(SomeElem y ix) -> SomeElem y (There ix)) <$> mkLocalElem xs (n - 1)
mkLocalElem SSNil         _ = Nothing

-- | @∃rs. (StackS rs, Elem rs ls)@ — a bounds-checked index into a label context.
type SomeLabel :: [[ValType]] -> Type
data SomeLabel ls where
    SomeLabel :: StackS rs -> Elem rs ls -> SomeLabel ls

mkLabelElem :: LabelS ls -> Word32 -> Maybe (SomeLabel ls)
mkLabelElem (LSCons rs _)   0 = Just (SomeLabel rs Here)
mkLabelElem (LSCons _ rest) n = (\(SomeLabel rs ix) -> SomeLabel rs (There ix)) <$> mkLabelElem rest (n - 1)
mkLabelElem LSNil           _ = Nothing

-- | @∃s. (StackS s, Append ps s full)@ — proof that @ps@ is a prefix of @full@, with the
--   suffix singleton and the 'Append' witness used to split/recombine stacks.
type SomeSplit :: [ValType] -> [ValType] -> Type
data SomeSplit ps full where
    SomeSplit :: StackS s -> Append ps s full -> SomeSplit ps full

matchPrefix :: StackS ps -> StackS full -> Maybe (SomeSplit ps full)
matchPrefix SSNil         sfull         = Just (SomeSplit sfull ANil)
matchPrefix (SSCons p ps) (SSCons f fs) = do
    Refl          <- decideValType p f
    SomeSplit s w <- matchPrefix ps fs
    Just (SomeSplit s (ACons w))
matchPrefix (SSCons _ _) SSNil = Nothing

-- | Compute the singleton for a concatenated stack shape.
sAppendS :: StackS a -> StackS b -> StackS (a ++ b)
sAppendS SSNil         sb = sb
sAppendS (SSCons x xs) sb = SSCons x (sAppendS xs sb)

{- *** Module-signature singletons ***

   To elaborate @call@/global/memory we need a runtime witness of the module signature so
   their indices can be turned into the typed AST's 'Elem's and constraints. -}

-- | A singleton for 'Mutability' (which is not itself singletonised).
type SMut :: Mutability -> Type
data SMut m where
    SImmutable :: SMut 'Immutable
    SMutable   :: SMut 'Mutable

type FuncTypeS :: FuncType -> Type
data FuncTypeS ft where
    FuncTypeS :: StackS ps -> StackS rs -> FuncTypeS ('FuncType ps rs)

type FuncTypesS :: [FuncType] -> Type
data FuncTypesS fts where
    FtSNil  :: FuncTypesS '[]
    FtSCons :: FuncTypeS ft -> FuncTypesS fts -> FuncTypesS (ft ': fts)

type GlobalTypeS :: GlobalType -> Type
data GlobalTypeS g where
    GlobalTypeS :: SMut m -> SValType t -> GlobalTypeS ('GlobalType m t)

type GlobalsS :: [GlobalType] -> Type
data GlobalsS gs where
    GsSNil  :: GlobalsS '[]
    GsSCons :: GlobalTypeS g -> GlobalsS gs -> GlobalsS (g ': gs)

-- | Singleton for an address type.
data SAddrType (a :: AddrType) where
    SAddrI32 :: SAddrType 'AddrI32
    SAddrI64 :: SAddrType 'AddrI64

-- | Singleton for an optional type-level limit.
data SMaybeNat (m :: Maybe Natural) where
    SNothingN :: SMaybeNat 'Nothing
    SJustN    :: SNat n -> SMaybeNat ('Just n)

-- | Singleton for a memory shape: its address type and (type-level 'Natural') limits.
data MemShapeS (m :: MemShape) where
    MemShapeS :: SAddrType at -> SNat lo -> SMaybeNat hi -> MemShapeS ('MemShape at lo hi)

type MemsS :: [MemShape] -> Type
data MemsS ms where
    MsSNil  :: MemsS '[]
    MsSCons :: MemShapeS m -> MemsS ms -> MemsS (m ': ms)

-- | A runtime witness of a whole module signature.
type ModuleShapeS :: ModuleShape -> Type
data ModuleShapeS shape where
    ModuleShapeS :: FuncTypesS fts -> GlobalsS gs -> MemsS ms -> ModuleShapeS ('ModuleShape fts gs ms)

data SomeModuleShapeS where
    SomeModuleShapeS :: ModuleShapeS shape -> SomeModuleShapeS

data SomeMut where
    SomeMut :: SMut m -> SomeMut

reflectMut :: Mutability -> SomeMut
reflectMut Immutable = SomeMut SImmutable
reflectMut Mutable   = SomeMut SMutable

data SomeFuncTypeS where
    SomeFuncTypeS :: FuncTypeS ft -> SomeFuncTypeS

reflectFuncType :: FuncType -> SomeFuncTypeS
reflectFuncType (FuncType psT rsT) = case (reflectStack psT, reflectStack rsT) of
    (SomeStack ps, SomeStack rs) -> SomeFuncTypeS (FuncTypeS ps rs)

data SomeFuncTypesS where
    SomeFuncTypesS :: FuncTypesS fts -> SomeFuncTypesS

reflectFuncTypes :: [FuncType] -> SomeFuncTypesS
reflectFuncTypes []       = SomeFuncTypesS FtSNil
reflectFuncTypes (f : fs) = case (reflectFuncType f, reflectFuncTypes fs) of
    (SomeFuncTypeS ft, SomeFuncTypesS fts) -> SomeFuncTypesS (FtSCons ft fts)

data SomeGlobalTypeS where
    SomeGlobalTypeS :: GlobalTypeS g -> SomeGlobalTypeS

reflectGlobalType :: GlobalType -> SomeGlobalTypeS
reflectGlobalType (GlobalType mut (Num n)) = case (reflectMut mut, reflectNumType n) of
    (SomeMut sm, SomeNumType sn) -> SomeGlobalTypeS (GlobalTypeS sm (SNum sn))

data SomeGlobalsS where
    SomeGlobalsS :: GlobalsS gs -> SomeGlobalsS

reflectGlobals :: [GlobalType] -> SomeGlobalsS
reflectGlobals []       = SomeGlobalsS GsSNil
reflectGlobals (g : gs) = case (reflectGlobalType g, reflectGlobals gs) of
    (SomeGlobalTypeS gt, SomeGlobalsS gts) -> SomeGlobalsS (GsSCons gt gts)

data SomeMemsS where
    SomeMemsS :: MemsS ms -> SomeMemsS

data SomeAddrType where
    SomeAddrType :: SAddrType a -> SomeAddrType

reflectAddrType :: AddrType -> SomeAddrType
reflectAddrType AddrI32 = SomeAddrType SAddrI32
reflectAddrType AddrI64 = SomeAddrType SAddrI64

data SomeMemShapeS where
    SomeMemShapeS :: MemShapeS m -> SomeMemShapeS

-- | Reflect a decoded memory type to its shape singleton, lifting the @Word32@ limits to
--   type-level 'Natural's via 'withSomeSNat'.
reflectMemShape :: MemType -> SomeMemShapeS
reflectMemShape (MemType at (Limits lo hi)) = case reflectAddrType at of
    SomeAddrType sAt -> withSomeSNat (fromIntegral lo) $ \sLo -> case hi of
        Nothing -> SomeMemShapeS (MemShapeS sAt sLo SNothingN)
        Just h  -> withSomeSNat (fromIntegral h) $ \sHi ->
                       SomeMemShapeS (MemShapeS sAt sLo (SJustN sHi))

reflectMems :: [MemType] -> SomeMemsS
reflectMems []         = SomeMemsS MsSNil
reflectMems (mt : mts) = case (reflectMemShape mt, reflectMems mts) of
    (SomeMemShapeS m, SomeMemsS ms) -> SomeMemsS (MsSCons m ms)

-- | Reflect a module's signature (function types, global types, memory types) to a runtime
--   witness with the type-level signature hidden existentially.
reflectCtx :: [FuncType] -> [GlobalType] -> [MemType] -> SomeModuleShapeS
reflectCtx funcTypes globalTypes memTypes =
    case (reflectFuncTypes funcTypes, reflectGlobals globalTypes, reflectMems memTypes) of
        (SomeFuncTypesS fts, SomeGlobalsS gs, SomeMemsS ms) -> SomeModuleShapeS (ModuleShapeS fts gs ms)

-- | @∃ps rs. (StackS ps, StackS rs, Elem ('FuncType ps rs) fts)@ — a function reference
--   resolved against the signature, carrying its parameter and result shapes.
type SomeFuncRef :: [FuncType] -> Type
data SomeFuncRef fts where
    SomeFuncRef :: StackS ps -> StackS rs -> Elem ('FuncType ps rs) fts -> SomeFuncRef fts

lookupFuncRef :: FuncTypesS fts -> Word32 -> Maybe (SomeFuncRef fts)
lookupFuncRef (FtSCons (FuncTypeS ps rs) _) 0 = Just (SomeFuncRef ps rs Here)
lookupFuncRef (FtSCons _ rest) n =
    (\(SomeFuncRef ps rs ix) -> SomeFuncRef ps rs (There ix)) <$> lookupFuncRef rest (n - 1)
lookupFuncRef FtSNil _ = Nothing

-- | @∃m t. (SMut m, SValType t, Elem ('GlobalType m t) gs)@ — a global resolved against
--   the signature, carrying its mutability and type.
type SomeGlobalRef :: [GlobalType] -> Type
data SomeGlobalRef gs where
    SomeGlobalRef :: SMut m -> SValType t -> Elem ('GlobalType m t) gs -> SomeGlobalRef gs

lookupGlobalRef :: GlobalsS gs -> Word32 -> Maybe (SomeGlobalRef gs)
lookupGlobalRef (GsSCons (GlobalTypeS sm st) _) 0 = Just (SomeGlobalRef sm st Here)
lookupGlobalRef (GsSCons _ rest) n =
    (\(SomeGlobalRef sm st ix) -> SomeGlobalRef sm st (There ix)) <$> lookupGlobalRef rest (n - 1)
lookupGlobalRef GsSNil _ = Nothing

-- | Proof that a memory index space is non-empty, licensing @load@/@store@.
type NonEmptyMems :: [MemShape] -> Type
data NonEmptyMems ms where
    NonEmptyMems :: NonEmptyMems (m ': ms)

memsNonEmpty :: MemsS ms -> Maybe (NonEmptyMems ms)
memsNonEmpty (MsSCons _ _) = Just NonEmptyMems
memsNonEmpty MsSNil        = Nothing
