{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{- | Reflection between the term level and the type level, and reconstruction of the typed
  AST's indices ('Elem') and witnesses ('Append') from runtime data — what lets
  elaboration recover a decoded module's hidden type indices.

  With @singletons-base@ providing the @Sing@ instances for our types (and for lists,
  @Maybe@ and @Natural@), the term→type direction is just the library's 'withSomeSing'.
  This module adds the WASM-specific pieces the library does not give us: small decidable
  equalities used during elaboration, and the bounds-checked construction of 'Elem' indices
  and 'Append' split witnesses from decoded indices.
-}
module Validation.Reflect (
    SomeStack (..),
    SomeElem (..),
    SomeLabel (..),
    SomeSplit (..),
    reflectStack,
    stackOrder,
    declaredOrder,
    sReverseOnto,
    mkLocalElem,
    mkLabelElem,
    matchPrefix,
    -- module-signature witnesses
    SomeModuleShape (..),
    SomeFuncRef (..),
    SomeGlobalRef (..),
    NonEmptyMems (..),
    reflectCtx,
    funcTypesSing,
    globalTypesSing,
    memShapesSing,
    lookupFuncRef,
    lookupGlobalRef,
    memsNonEmpty,
) where

import Data.Type.Equality ((:~:) (Refl))
import Data.Word (Word32)

import Data.Singletons.Base.TH (SList (SCons, SNil), Sing, withSomeSing)
import Data.Singletons.Decide (decideEquality)
import Syntax.Types

-- Open import: the generated single-constructor 'SModuleShape' shares its name with its type.
import Validation.Shape

{- *** Reflecting term-level shapes to singletons ***

   Each is a one-liner over the library's 'withSomeSing': the @Sing@ and @SingKind@ instances
   for our types come from @singletons-base@.
-}

-- | A term-level stack shape reflected to its singleton, hidden existentially.
data SomeStack where
    SomeStack :: Sing (s :: [ValType]) -> SomeStack

reflectStack :: [ValType] -> SomeStack
reflectStack vs = withSomeSing vs SomeStack

{- | Convert between the decoded (declared) order of a parameter or result list and the stack
  order the shapes use (top of stack first; see "Validation.Shape"). Both are a reversal; the
  two names say which way a call site is going.
-}
stackOrder :: [a] -> [a]
stackOrder = reverse

declaredOrder :: [a] -> [a]
declaredOrder = reverse

-- | A decoded function type with its parameter and result lists in stack order.
stackOrderFuncType :: FuncType -> FuncType
stackOrderFuncType (FuncType params results) = FuncType (stackOrder params) (stackOrder results)

-- | The singleton of 'ReverseOnto', built the same structural way.
sReverseOnto :: Sing (xs :: [ValType]) -> Sing (acc :: [ValType]) -> Sing (ReverseOnto xs acc)
sReverseOnto SNil acc = acc
sReverseOnto (SCons x xs) acc = sReverseOnto xs (SCons x acc)

{- *** Index and witness construction ***

   Decidable equality on stack/type singletons comes from the library's 'decideEquality'
   (over the 'SDecide' instances generated in "Syntax.Types"); the pieces below build the
   typed AST's index and split witnesses, which the library does not provide.
-}

-- | @∃x. (Sing (x :: ValType), Elem x xs)@ — a bounds-checked index into a stack shape.
data SomeElem (xs :: [ValType]) where
    SomeElem :: Sing (x :: ValType) -> Elem x xs -> SomeElem xs

mkLocalElem :: Sing (xs :: [ValType]) -> Word32 -> Maybe (SomeElem xs)
mkLocalElem (SCons x _) 0 = Just (SomeElem x Here)
mkLocalElem (SCons _ xs) n = (\(SomeElem y ix) -> SomeElem y (There ix)) <$> mkLocalElem xs (n - 1)
mkLocalElem SNil _ = Nothing

-- | @∃rs. (Sing (rs :: ResultType), Elem rs ls)@ — a bounds-checked index into a label context.
data SomeLabel (ls :: [ResultType]) where
    SomeLabel :: Sing (rs :: ResultType) -> Elem rs ls -> SomeLabel ls

mkLabelElem :: Sing (ls :: [ResultType]) -> Word32 -> Maybe (SomeLabel ls)
mkLabelElem (SCons rs _) 0 = Just (SomeLabel rs Here)
mkLabelElem (SCons _ rest) n = (\(SomeLabel rs ix) -> SomeLabel rs (There ix)) <$> mkLabelElem rest (n - 1)
mkLabelElem SNil _ = Nothing

{- | @∃s. (Sing (s :: [ValType]), Append ps s full)@ — proof that @ps@ is a prefix of @full@,
  with the suffix singleton and the 'Append' witness used to split/recombine stacks.
-}
data SomeSplit (ps :: [ValType]) (full :: [ValType]) where
    SomeSplit :: Sing (s :: [ValType]) -> Append ps s full -> SomeSplit ps full

matchPrefix :: Sing (ps :: [ValType]) -> Sing (full :: [ValType]) -> Maybe (SomeSplit ps full)
matchPrefix SNil sfull = Just (SomeSplit sfull ANil)
matchPrefix (SCons p ps) (SCons f fs) = do
    Refl <- decideEquality p f
    SomeSplit s w <- matchPrefix ps fs
    Just (SomeSplit s (ACons w))
matchPrefix (SCons _ _) SNil = Nothing

{- *** Module-signature reflection ***

   To elaborate @call@/global/memory we need a runtime witness of the module signature so
   their indices can be turned into the typed AST's 'Elem's and constraints. The whole
   signature reflects in one 'withSomeSing'; the lookups then walk the resulting singleton.
-}

data SomeModuleShape where
    SomeModuleShape :: Sing (shape :: ModuleShape) -> SomeModuleShape

-- | The type-level mirror of a decoded 'MemType': lift its @Word32@ limits to 'Natural's.
memShapeOf :: MemType -> MemShape
memShapeOf (MemType at (Limits lo hi)) = MemShape at (fromIntegral lo) (fmap fromIntegral hi)

{- | Reflect a module's signature (function types, global types, memory types) to a runtime
  witness with the type-level signature hidden existentially. The function types are given in
  declared order (as decoded) and stored in stack order.
-}
reflectCtx :: [FuncType] -> [GlobalType] -> [MemType] -> SomeModuleShape
reflectCtx funcTypes globalTypes memTypes =
    withSomeSing
        (ModuleShape (map stackOrderFuncType funcTypes) globalTypes (map memShapeOf memTypes))
        SomeModuleShape

-- | The three index spaces of a module-shape singleton.
funcTypesSing :: SModuleShape shape -> Sing (ModuleFuncs shape)
funcTypesSing (SModuleShape fts _ _) = fts

globalTypesSing :: SModuleShape shape -> Sing (ModuleGlobals shape)
globalTypesSing (SModuleShape _ gs _) = gs

memShapesSing :: SModuleShape shape -> Sing (ModuleMems shape)
memShapesSing (SModuleShape _ _ ms) = ms

{- | @∃ps rs. (Sing ps, Sing rs, Elem ('FuncType ps rs) fts)@ — a function reference resolved
  against the signature, carrying its parameter and result shapes.
-}
data SomeFuncRef (fts :: [FuncType]) where
    SomeFuncRef :: Sing (ps :: [ValType]) -> Sing (rs :: [ValType]) -> Elem ('FuncType ps rs) fts -> SomeFuncRef fts

lookupFuncRef :: Sing (fts :: [FuncType]) -> Word32 -> Maybe (SomeFuncRef fts)
lookupFuncRef (SCons (SFuncType ps rs) _) 0 = Just (SomeFuncRef ps rs Here)
lookupFuncRef (SCons _ rest) n =
    (\(SomeFuncRef ps rs ix) -> SomeFuncRef ps rs (There ix)) <$> lookupFuncRef rest (n - 1)
lookupFuncRef SNil _ = Nothing

{- | @∃m t. (Sing m, Sing (t :: ValType), Elem ('GlobalType m t) gs)@ — a global resolved
  against the signature, carrying its mutability and type.
-}
data SomeGlobalRef (gs :: [GlobalType]) where
    SomeGlobalRef :: Sing (m :: Mutability) -> Sing (t :: ValType) -> Elem ('GlobalType m t) gs -> SomeGlobalRef gs

lookupGlobalRef :: Sing (gs :: [GlobalType]) -> Word32 -> Maybe (SomeGlobalRef gs)
lookupGlobalRef (SCons (SGlobalType sm st) _) 0 = Just (SomeGlobalRef sm st Here)
lookupGlobalRef (SCons _ rest) n =
    (\(SomeGlobalRef sm st ix) -> SomeGlobalRef sm st (There ix)) <$> lookupGlobalRef rest (n - 1)
lookupGlobalRef SNil _ = Nothing

-- | Proof that a memory index space is non-empty, licensing @load@/@store@.
data NonEmptyMems (ms :: [MemShape]) where
    NonEmptyMems :: NonEmptyMems (m ': ms)

memsNonEmpty :: Sing (ms :: [MemShape]) -> Maybe (NonEmptyMems ms)
memsNonEmpty (SCons _ _) = Just NonEmptyMems
memsNonEmpty SNil = Nothing
