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
    stackOrderFuncType,
    sReverseOnto,
    appendNil,
    mkLocalElem,
    mkLabelElem,
    matchPrefix,
    SomeCoercion (..),
    matchPrefixFlows,
    SomePrefix (..),
    takePrefix,
    reflectStackAt,
    SameLength (..),
    sameLengthAs,
    thenSameLength,
    raiseAllSameLength,
    joinEachSameLength,
    SomeBranchTarget (..),
    mkBranchTarget,
    -- module-signature witnesses
    SomeModuleShape (..),
    SomeGlobalRef (..),
    NonEmptyMems (..),
    NonEmptyTables (..),
    tablesNonEmpty,
    reflectCtx,
    funcTypesSing,
    globalTypesSing,
    memShapesSing,
    tableShapesSing,
    dataShapesSing,
    mkDataElem,
    lookupFuncRef,
    lookupGlobalRef,
    memsNonEmpty,
) where

import Data.Type.Equality ((:~:) (Refl))
import Data.Word (Word32)

import Data.Singletons.Base.TH (SList (SCons, SNil), Sing, withSomeSing)
import Data.Singletons.Decide (decideEquality)
import Syntax.Types
import Syntax.TypesIFC

-- Open import: the generated single-constructor 'SModuleShape' shares its name with its type.
import Validation.Shape

{- *** Reflecting term-level shapes to singletons ***

   Each is a one-liner over the library's 'withSomeSing': the @Sing@ and @SingKind@ instances
   for our types come from @singletons-base@.
-}

-- | A term-level stack shape reflected to its singleton, hidden existentially.
data SomeStack where
    SomeStack :: Sing (s :: [LabelledValType]) -> SomeStack

{- | Reflect a function's declared locals, labelling each one public. (Function types and
  globals get their levels from the policy, see "Validation.Policy"; a declared local has no
  declaration and is public.)
-}
reflectStack :: [ValType] -> SomeStack
reflectStack vs = withSomeSing (publicAll vs) SomeStack

{- | Convert between the decoded (declared) order of a parameter or result list and the stack
  order the shapes use (top of stack first; see "Validation.Shape"). Both are a reversal; the
  two names say which way a call site is going.
-}
stackOrder :: [a] -> [a]
stackOrder = reverse

declaredOrder :: [a] -> [a]
declaredOrder = reverse

-- | A decoded function type with its parameter and result lists in stack order.
stackOrderFuncType :: FuncTypeOf v -> FuncTypeOf v
stackOrderFuncType (FuncType params results) = FuncType (stackOrder params) (stackOrder results)

-- | The witness that appending nothing changes nothing, for a stack whose singleton we hold.
appendNil :: Sing (xs :: [LabelledValType]) -> Append xs '[] xs
appendNil SNil = ANil
appendNil (SCons _ rest) = ACons (appendNil rest)

-- | The singleton of 'ReverseOnto', built the same structural way.
sReverseOnto :: Sing (xs :: [LabelledValType]) -> Sing (acc :: [LabelledValType]) -> Sing (ReverseOnto xs acc)
sReverseOnto SNil acc = acc
sReverseOnto (SCons x xs) acc = sReverseOnto xs (SCons x acc)

{- *** Index and witness construction ***

   Decidable equality on stack/type singletons comes from the library's 'decideEquality'
   (over the 'SDecide' instances generated in "Syntax.Types"); the pieces below build the
   typed AST's index and split witnesses, which the library does not provide.
-}

-- | @∃x. (Sing (x :: ValType), Elem x xs)@ — a bounds-checked index into a stack shape.
data SomeElem (xs :: [LabelledValType]) where
    SomeElem :: Sing (x :: LabelledValType) -> Elem x xs -> SomeElem xs

mkLocalElem :: Sing (xs :: [LabelledValType]) -> Word32 -> Maybe (SomeElem xs)
mkLocalElem (SCons x _) 0 = Just (SomeElem x Here)
mkLocalElem (SCons _ xs) n = (\(SomeElem y ix) -> SomeElem y (There ix)) <$> mkLocalElem xs (n - 1)
mkLocalElem SNil _ = Nothing

-- | @∃rs. (Sing (rs :: ResultType), Elem rs ls)@ — a bounds-checked index into a label context.
data SomeLabel (ls :: [LabelledResultType]) where
    SomeLabel :: Sing (rs :: LabelledResultType) -> Elem rs ls -> SomeLabel ls

mkLabelElem :: Sing (ls :: [LabelledResultType]) -> Word32 -> Maybe (SomeLabel ls)
mkLabelElem (SCons rs _) 0 = Just (SomeLabel rs Here)
mkLabelElem (SCons _ rest) n = (\(SomeLabel rs ix) -> SomeLabel rs (There ix)) <$> mkLabelElem rest (n - 1)
mkLabelElem SNil _ = Nothing

{- | @∃s. (Sing (s :: [ValType]), Append ps s full)@ — proof that @ps@ is a prefix of @full@,
  with the suffix singleton and the 'Append' witness used to split/recombine stacks.
-}
data SomeSplit (ps :: [LabelledValType]) (full :: [LabelledValType]) where
    SomeSplit :: Sing (s :: [LabelledValType]) -> Append ps s full -> SomeSplit ps full

matchPrefix :: Sing (ps :: [LabelledValType]) -> Sing (full :: [LabelledValType]) -> Maybe (SomeSplit ps full)
matchPrefix SNil sfull = Just (SomeSplit sfull ANil)
matchPrefix (SCons p ps) (SCons f fs) = do
    Refl <- decideEquality p f
    SomeSplit s w <- matchPrefix ps fs
    Just (SomeSplit s (ACons w))
matchPrefix (SCons _ _) SNil = Nothing

{- | @∃args s. (Sing s, SegmentFlows args ps, Append args s full)@: the top of @full@ is a
  segment whose values may flow into @ps@ (SecWasm's subtyping on stacks), with the suffix and
  the split witness. What a call, a branch or a return needs of the stack.
-}
data SomeCoercion (ps :: [LabelledValType]) (full :: [LabelledValType]) where
    SomeCoercion :: Sing (s :: [LabelledValType]) -> SegmentFlows args ps -> Append args s full -> SomeCoercion ps full

matchPrefixFlows :: Sing (ps :: [LabelledValType]) -> Sing (full :: [LabelledValType]) -> Maybe (SomeCoercion ps full)
matchPrefixFlows SNil sfull = Just (SomeCoercion sfull NoValuesFlow ANil)
matchPrefixFlows (SCons (p :%~ lp) ps) (SCons (f :%~ lf) fs) = do
    Refl <- decideEquality p f
    flow <- decideFlow lf lp
    SomeCoercion s flows w <- matchPrefixFlows ps fs
    Just (SomeCoercion s (ValueFlows flow flows) (ACons w))
matchPrefixFlows (SCons _ _) SNil = Nothing

-- | The top @n@ entries of a stack, whatever they are, with the suffix and the split witness.
data SomePrefix (full :: [LabelledValType]) where
    SomePrefix :: Sing (ps :: [LabelledValType]) -> Sing (s :: [LabelledValType]) -> Append ps s full -> SomePrefix full

takePrefix :: Int -> Sing (full :: [LabelledValType]) -> Maybe (SomePrefix full)
takePrefix 0 sfull = Just (SomePrefix SNil sfull ANil)
takePrefix n (SCons x xs) = (\(SomePrefix ps s w) -> SomePrefix (SCons x ps) s (ACons w)) <$> takePrefix (n - 1) xs
takePrefix _ SNil = Nothing

-- | Reflect value types with every level the given one.
reflectStackAt :: SecLevel -> [ValType] -> SomeStack
reflectStackAt level vs = withSomeSing (map (:~ level) vs) SomeStack

{- *** The pc stack ***

   Validation threads the pc stack ("Syntax.TypesIFC") through a function body. Every rule
   keeps its length, and validation needs to know that: the stack has one entry per enclosing
   block plus one for the function, so it is never empty where an instruction reads the pc, and
   a block's body leaves at least the entries that were below it. 'SameLength' is that
   knowledge as a witness, so none of it is an assumption.
-}

-- | Two lists have the same length.
data SameLength (xs :: [k]) (ys :: [k]) where
    BothEmpty :: SameLength '[] '[]
    BothLonger :: SameLength xs ys -> SameLength (x ': xs) (y ': ys)

sameLengthAs :: Sing (xs :: [k]) -> SameLength xs xs
sameLengthAs SNil = BothEmpty
sameLengthAs (SCons _ rest) = BothLonger (sameLengthAs rest)

thenSameLength :: SameLength xs ys -> SameLength ys zs -> SameLength xs zs
thenSameLength BothEmpty BothEmpty = BothEmpty
thenSameLength (BothLonger a) (BothLonger b) = BothLonger (thenSameLength a b)

raiseAllSameLength :: Sing (l :: SecLevel) -> Sing (pcs :: [SecLevel]) -> SameLength pcs (RaiseAll l pcs)
raiseAllSameLength _ SNil = BothEmpty
raiseAllSameLength l (SCons _ rest) = BothLonger (raiseAllSameLength l rest)

joinEachSameLength :: SameLength (pcs :: [SecLevel]) as -> SameLength pcs bs -> SameLength pcs (JoinEach as bs)
joinEachSameLength BothEmpty BothEmpty = BothEmpty
joinEachSameLength (BothLonger a) (BothLonger b) = BothLonger (joinEachSameLength a b)

{- | A branch target resolved against the label context and the pc stack: the label's result
  type, the pc stack after the branch, and the witness that ties them together.
-}
data SomeBranchTarget (l :: SecLevel) (labels :: [LabelledResultType]) (pcs :: [SecLevel]) where
    SomeBranchTarget ::
        Sing (rs :: LabelledResultType) ->
        Sing (pcs' :: [SecLevel]) ->
        SameLength pcs pcs' ->
        BranchTarget l rs labels pcs pcs' ->
        SomeBranchTarget l labels pcs

mkBranchTarget :: Sing (l :: SecLevel) -> Sing (labels :: [LabelledResultType]) -> Sing (pcs :: [SecLevel]) -> Word32 -> Maybe (SomeBranchTarget l labels pcs)
mkBranchTarget l (SCons rs _) (SCons p ps) 0 = Just (SomeBranchTarget rs (SCons (sJoin l p) ps) (BothLonger (sameLengthAs ps)) TargetHere)
mkBranchTarget l (SCons _ labels) (SCons p ps) n =
    (\(SomeBranchTarget rs ps' same target) -> SomeBranchTarget rs (SCons (sJoin l p) ps') (BothLonger same) (TargetThere target))
        <$> mkBranchTarget l labels ps (n - 1)
mkBranchTarget _ _ _ _ = Nothing

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

-- | The type-level mirror of a table's limits.
tableShapeOf :: Limits -> TableShape
tableShapeOf (Limits lo hi) = TableShape (fromIntegral lo) (fmap fromIntegral hi)

{- | Reflect a module's signature (function types, global types, memory types, table limits)
  to a runtime witness with the type-level signature hidden existentially. The function types
  are given in declared order (as decoded) and stored in stack order.
-}
reflectCtx :: [LabelledFuncType] -> [LabelledGlobalType] -> [MemType] -> [Limits] -> Int -> SomeModuleShape
reflectCtx funcTypes globalTypes memTypes tableLimits dataCount =
    withSomeSing
        ( ModuleShape
            (map stackOrderFuncType funcTypes)
            globalTypes
            (map memShapeOf memTypes)
            (map tableShapeOf tableLimits)
            (replicate dataCount DataShape)
        )
        SomeModuleShape

-- | The five index spaces of a module-shape singleton.
funcTypesSing :: SModuleShape shape -> Sing (ModuleFuncs shape)
funcTypesSing (SModuleShape fts _ _ _ _) = fts

globalTypesSing :: SModuleShape shape -> Sing (ModuleGlobals shape)
globalTypesSing (SModuleShape _ gs _ _ _) = gs

memShapesSing :: SModuleShape shape -> Sing (ModuleMems shape)
memShapesSing (SModuleShape _ _ ms _ _) = ms

tableShapesSing :: SModuleShape shape -> Sing (ModuleTables shape)
tableShapesSing (SModuleShape _ _ _ ts _) = ts

dataShapesSing :: SModuleShape shape -> Sing (ModuleData shape)
dataShapesSing (SModuleShape _ _ _ _ ds) = ds

-- | A bounds-checked index into the data index space.
mkDataElem :: Sing (ds :: [DataShape]) -> Word32 -> Maybe (Elem 'DataShape ds)
mkDataElem (SCons SDataShape _) 0 = Just Here
mkDataElem (SCons _ rest) n = There <$> mkDataElem rest (n - 1)
mkDataElem SNil _ = Nothing

lookupFuncRef :: Sing (fts :: [LabelledFuncType]) -> Word32 -> Maybe (SomeFuncRef fts)
lookupFuncRef (SCons (SFuncType ps rs) _) 0 = Just (SomeFuncRef ps rs Here)
lookupFuncRef (SCons _ rest) n =
    (\(SomeFuncRef ps rs ix) -> SomeFuncRef ps rs (There ix)) <$> lookupFuncRef rest (n - 1)
lookupFuncRef SNil _ = Nothing

{- | @∃m t. (Sing m, Sing (t :: ValType), Elem ('GlobalType m t) gs)@ — a global resolved
  against the signature, carrying its mutability and type.
-}
data SomeGlobalRef (gs :: [LabelledGlobalType]) where
    SomeGlobalRef :: Sing (m :: Mutability) -> Sing (t :: LabelledValType) -> Elem ('GlobalType m t) gs -> SomeGlobalRef gs

lookupGlobalRef :: Sing (gs :: [LabelledGlobalType]) -> Word32 -> Maybe (SomeGlobalRef gs)
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

-- | Proof that a table index space is non-empty, licensing @call_indirect@.
data NonEmptyTables (ts :: [TableShape]) where
    NonEmptyTables :: NonEmptyTables (t ': ts)

tablesNonEmpty :: Sing (ts :: [TableShape]) -> Maybe (NonEmptyTables ts)
tablesNonEmpty (SCons _ _) = Just NonEmptyTables
tablesNonEmpty SNil = Nothing
