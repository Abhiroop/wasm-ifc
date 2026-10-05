{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- | The information-flow vocabulary of the typed layer: security levels, value types labelled
  with one, the join, and the flow relation. Every stack, local, global and function type the
  typed AST is indexed by is over 'LabelledValType', so the one instruction type of
  "Syntax.Instructions" tracks information flow as well as value types. The model we follow is
  SecWasm (Bastys, Algehed, Sjösten, Sabelfeld, SAS 2022; linked from TODO.md §F).

  Exports openly, like "Syntax.Types", so the generated singletons are visible.
-}
module Syntax.TypesIFC where

import Data.List.Singletons (MapSym0, sMap)
import Data.Singletons.Base.TH

import Data.Singletons.Decide (decideEquality)
import Syntax.Types

$( singletons
    [d|
        -- The two-point security lattice: public and secret.
        data SecLevel = Low | High

        -- The join (least upper bound): the level of a value computed from two others.
        join :: SecLevel -> SecLevel -> SecLevel
        join Low l = l
        join High _ = High
        |]
 )

deriving stock instance Eq SecLevel
deriving stock instance Show SecLevel

infix 6 :~

{- | A value type together with the security level of the values it classifies: SecWasm's
  labelled type @τ ::= t⟨ℓ⟩@.
-}
data LabelledValType = ValType :~ SecLevel
    deriving stock (Eq, Show)

$(genSingletons [''LabelledValType])
$(singDecideInstances [''SecLevel])

-- Written by hand: the generated instance carries constraints GHC reports as redundant.
instance SDecide LabelledValType where
    (t :%~ l) %~ (t' :%~ l') = case t %~ t' of
        Disproved differ -> Disproved (\Refl -> differ Refl)
        Proved Refl -> case l %~ l' of
            Disproved differ -> Disproved (\Refl -> differ Refl)
            Proved Refl -> Proved Refl

$( singletons
    [d|
        -- A value type at the public level: how every type of a decoded module is labelled
        -- until a policy says otherwise.
        public :: ValType -> LabelledValType
        public t = t :~ Low

        publicAll :: [ValType] -> [LabelledValType]
        publicAll ts = map public ts

        -- A labelled type without its label.
        unlabelled :: LabelledValType -> ValType
        unlabelled (t :~ _) = t
        |]
 )

$( singletons
    [d|
        -- Raise every entry of a pc stack by a level (see 'PcStack').
        raiseAll :: SecLevel -> [SecLevel] -> [SecLevel]
        raiseAll l ps = map (join l) ps

        -- Join two pc stacks entry by entry: what is known after an @if@, whichever arm ran.
        joinEach :: [SecLevel] -> [SecLevel] -> [SecLevel]
        joinEach [] _ = []
        joinEach (_ : _) [] = []
        joinEach (p : ps) (q : qs) = join p q : joinEach ps qs
        |]
 )

{- | The program counter label, @pc@ for short: the security level of the decisions that led
  control to the current instruction. Inside @(if (secret) …)@ it is 'High, and whatever the
  code there does reveals the secret to anyone who can see the effect.

  The typed AST keeps a /stack/ of them, one entry per enclosing block with the innermost
  first, and every instruction has one such stack before it and one after it (the design of the
  @ifc@ branch, which is SecWasm's). The top entry is the pc in force. A conditional branch out
  of several blocks raises the entries of all the blocks it may leave, because the rest of each
  of them now runs only if the branch was not taken. When a block ends, its own entry is dropped
  and the entries below it stay as they were left, which is how a raise ends exactly where the
  branch's target ends.
-}
type PcStack = [SecLevel]

-- | A labelled result type: the stack segment a block, loop, if or function yields.
type LabelledResultType = [LabelledValType]

{- | A function type as the shapes hold it: SecWasm's @τ* →ℓ τ*@. Besides labelled parameters
  and results it carries a /bound/ @ℓ@, the most secret context the function may be called
  from: the body is checked with @ℓ@ as its starting pc, and a call needs the caller's pc to
  flow into @ℓ@. So a function bound at 'Low may only be called where nothing secret has been
  decided, and one bound at 'High may be called from anywhere but can then write only to
  secret places. Its results must be at least as secret as the bound (a well-formedness
  condition the policy stage checks), so that what a call pushes respects the caller's pc.
-}
data LabelledFuncType = LabelledFuncType SecLevel [LabelledValType] [LabelledValType]
    deriving stock (Eq, Show)

$(genSingletons [''LabelledFuncType])

-- | A global's type over labelled value types, as the shapes hold it.
type LabelledGlobalType = GlobalTypeOf LabelledValType

-- | A decoded function type labelled public throughout, bound included.
publicFuncType :: FuncType -> LabelledFuncType
publicFuncType (FuncType params results) = LabelledFuncType Low (publicAll params) (publicAll results)

-- | A decoded global type labelled public.
publicGlobalType :: GlobalType -> LabelledGlobalType
publicGlobalType (GlobalType mutability t) = GlobalType mutability (public t)

{- | The type of a function all of whose parameters and results are public, from plain value
  types. The host functions of "Runtime.Host" are declared with it.
-}
type PublicFunc ps rs = 'LabelledFuncType 'Low (PublicAll ps) (PublicAll rs)

{- | The premise of an instruction's rule that only the machine can decide, when it runs the
  instruction: SecWasm's two run-time checks. It is an index of the typed instruction
  ('Syntax.Instructions.Instr'), so an instruction says which check its rule depends on, and
  the machine's step for it has to present evidence that the check passed
  ("Runtime.Obligation") before it may continue. Leaving a check out of the interpreter is
  then a type error.

    * 'BytesBelow' @ℓ@: the bytes a load reads are labelled at most @ℓ@, the level the load
      declares (E-LOAD);
    * 'CalleeWithin' @ℓ@: the function an indirect call finds in the table has the expected
      labelled type and a bound that @ℓ@, the expected bound, flows into (E-CALL-INDIRECT).
-}
data DynamicCheck = NoDynamicCheck | BytesBelow SecLevel | CalleeWithin SecLevel

{- | Evidence that level @l@ may flow into level @l'@: the lattice order. A witness rather than
  a class because validation of a decoded module has to construct it at run time, from
  singletons, with 'decideFlow'.
-}
data FlowsInto (l :: SecLevel) (l' :: SecLevel) where
    LowFlowsAnywhere :: FlowsInto 'Low l
    HighFlowsToHigh :: FlowsInto 'High 'High

{- | Evidence that every value in a stack segment is at least as secret as @l@. A branch
  carries the values of its target's type out of the block, and which values arrive depends on
  whether the branch was taken, so they must be at least as secret as that decision.
-}
data AllAtLeast (l :: SecLevel) (rs :: [LabelledValType]) where
    NothingCarried :: AllAtLeast l '[]
    CarriedAtLeast :: FlowsInto l lv -> AllAtLeast l rs -> AllAtLeast l ((t ':~ lv) ': rs)

{- | Whether a call's arguments must be at least as secret as the pc at the call. SecWasm's
  rule for calls demands exactly the parameters' labels, and its lift may have raised an
  argument pushed before a secret branch up to the pc, so a program is typable in SecWasm only
  if every argument can be at that level. Without the lift the requirement is not needed for
  security ('Syntax.Instructions.IBlock' gives the argument); with the SecWasm restrictions of
  the policy it is imposed, and this is its witness.
-}
data ArgumentsAtCallPc (pc :: SecLevel) (ps :: [LabelledValType]) where
    -- | the lift-free rule: the arguments may be below the pc
    ArgumentsAtAnyLevel :: ArgumentsAtCallPc pc ps
    -- | the SecWasm restriction: every parameter is at least the pc
    ArgumentsAtLeastPc :: AllAtLeast pc ps -> ArgumentsAtCallPc pc ps

{- | Whether the results of a block or conditional must be at least as secret as the pc its
  body ends with. They are always at least the pc the body starts with (the 'AllAtLeast' of
  'Syntax.Instructions.IBlock'). A branch out of the body to an enclosing block, taken under a
  secret condition, raises the pc the body ends with and leaves the results alone; SecWasm's
  lift raises them as well, so a proof by inclusion into SecWasm needs them raised here too.
  This is the third of the SecWasm restrictions of the policy, beside 'ArgumentsAtCallPc' and
  'Syntax.Instructions.FallThrough'.
-}
data ResultsAtEndPc (pcEnd :: SecLevel) (rs :: [LabelledValType]) where
    -- | the lift-free rule: nothing is asked of the pc the body ends with
    ResultsAtAnyLevel :: ResultsAtEndPc pcEnd rs
    -- | the SecWasm restriction: every result is at least the pc the body ends with
    ResultsAtLeastEndPc :: AllAtLeast pcEnd rs -> ResultsAtEndPc pcEnd rs

decideAllAtLeast :: Sing (l :: SecLevel) -> Sing (rs :: [LabelledValType]) -> Maybe (AllAtLeast l rs)
decideAllAtLeast _ SNil = Just NothingCarried
decideAllAtLeast l (SCons (_ :%~ lv) rest) = CarriedAtLeast <$> decideFlow l lv <*> decideAllAtLeast l rest

-- | Every level flows into itself: the witness an inferred store level satisfies by construction.
flowsSelf :: Sing (l :: SecLevel) -> FlowsInto l l
flowsSelf SLow = LowFlowsAnywhere
flowsSelf SHigh = HighFlowsToHigh

decideFlow :: Sing (l :: SecLevel) -> Sing (l' :: SecLevel) -> Maybe (FlowsInto l l')
decideFlow SLow _ = Just LowFlowsAnywhere
decideFlow SHigh SHigh = Just HighFlowsToHigh
decideFlow SHigh SLow = Nothing

{- | Evidence that a stack segment may be used where another is expected: the same value
  types, each level flowing into its counterpart. This is SecWasm's subtyping on type stacks
  (@st ⊑ st'@, used at calls, branches, returns and block results) as a witness the instruction
  carries; at run time the words are unchanged and only the type changes.
-}
data SegmentFlows (from :: [LabelledValType]) (to :: [LabelledValType]) where
    NoValuesFlow :: SegmentFlows '[] '[]
    ValueFlows :: FlowsInto l l' -> SegmentFlows from to -> SegmentFlows ((t ':~ l) ': from) ((t ':~ l') ': to)

decideSegmentFlows :: Sing (from :: [LabelledValType]) -> Sing (to :: [LabelledValType]) -> Maybe (SegmentFlows from to)
decideSegmentFlows SNil SNil = Just NoValuesFlow
decideSegmentFlows (SCons (t :%~ l) rest) (SCons (t' :%~ l') rest') = do
    Refl <- decideEquality t t'
    ValueFlows <$> decideFlow l l' <*> decideSegmentFlows rest rest'
decideSegmentFlows _ _ = Nothing

-- | A segment flows into itself: what a hand-written program with matching levels supplies.
segmentSelf :: Sing (s :: [LabelledValType]) -> SegmentFlows s s
segmentSelf SNil = NoValuesFlow
segmentSelf (SCons (_ :%~ l) rest) = ValueFlows (flowsSelf l) (segmentSelf rest)

{- | Evidence that two stack segments have the same value types, whatever their levels: what a
  host function's own type (public throughout, since a host implementation knows nothing of
  levels) shares with the type the module's policy declares for the import. At the host
  boundary the words cross under the declared levels on the module's side and under public
  ones on the host's; nothing about them changes.
-}
data SameValueTypes (a :: [LabelledValType]) (b :: [LabelledValType]) where
    NoValues :: SameValueTypes '[] '[]
    SameValue :: SameValueTypes as bs -> SameValueTypes ((t ':~ l) ': as) ((t ':~ l') ': bs)

decideSameValueTypes :: Sing (a :: [LabelledValType]) -> Sing (b :: [LabelledValType]) -> Maybe (SameValueTypes a b)
decideSameValueTypes SNil SNil = Just NoValues
decideSameValueTypes (SCons (t :%~ _) rest) (SCons (t' :%~ _) rest') = do
    Refl <- decideEquality t t'
    SameValue <$> decideSameValueTypes rest rest'
decideSameValueTypes _ _ = Nothing
