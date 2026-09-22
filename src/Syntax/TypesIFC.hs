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
  typed AST is indexed by is over 'LValType', so the one instruction type of
  "Syntax.Instructions" tracks information flow as well as value types. The model we follow is
  SecWasm (Bastys, Algehed, Sjösten, Sabelfeld, SAS 2022; linked from TODO.md §F).

  Exports openly, like "Syntax.Types", so the generated singletons are visible.
-}
module Syntax.TypesIFC where

import Data.List.Singletons (MapSym0, sMap)
import Data.Singletons.Base.TH

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

  TODO(ifc P3): naming. @LValType@ reads as "l-value type"; @LabelledValType@ would read as
  prose, which is the repo's rule.
-}
data LValType = ValType :~ SecLevel
    deriving stock (Eq, Show)

$(genSingletons [''LValType])
$(singDecideInstances [''SecLevel])

-- Written by hand: the generated instance carries constraints GHC reports as redundant.
instance SDecide LValType where
    (t :%~ l) %~ (t' :%~ l') = case t %~ t' of
        Disproved differ -> Disproved (\Refl -> differ Refl)
        Proved Refl -> case l %~ l' of
            Disproved differ -> Disproved (\Refl -> differ Refl)
            Proved Refl -> Proved Refl

$( singletons
    [d|
        -- A value type at the public level: how every type of a decoded module is labelled
        -- until a policy says otherwise.
        public :: ValType -> LValType
        public t = t :~ Low

        publicAll :: [ValType] -> [LValType]
        publicAll ts = map public ts

        -- A labelled type without its label.
        unlabelled :: LValType -> ValType
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
type LResultType = [LValType]

-- | A function type over labelled value types, as the shapes hold it.
type LFuncType = FuncTypeOf LValType

-- | A global's type over labelled value types, as the shapes hold it.
type LGlobalType = GlobalTypeOf LValType

-- | A decoded function type labelled public throughout.
publicFuncType :: FuncType -> LFuncType
publicFuncType (FuncType params results) = FuncType (publicAll params) (publicAll results)

-- | A decoded global type labelled public.
publicGlobalType :: GlobalType -> LGlobalType
publicGlobalType (GlobalType mutability t) = GlobalType mutability (public t)

{- | The type of a function all of whose parameters and results are public, from plain value
  types. The host functions of "Runtime.Host" are declared with it.
-}
type PublicFunc ps rs = 'FuncType (PublicAll ps) (PublicAll rs)

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
data AllAtLeast (l :: SecLevel) (rs :: [LValType]) where
    NothingCarried :: AllAtLeast l '[]
    CarriedAtLeast :: FlowsInto l lv -> AllAtLeast l rs -> AllAtLeast l ((t ':~ lv) ': rs)

decideAllAtLeast :: Sing (l :: SecLevel) -> Sing (rs :: [LValType]) -> Maybe (AllAtLeast l rs)
decideAllAtLeast _ SNil = Just NothingCarried
decideAllAtLeast l (SCons (_ :%~ lv) rest) = CarriedAtLeast <$> decideFlow l lv <*> decideAllAtLeast l rest

decideFlow :: Sing (l :: SecLevel) -> Sing (l' :: SecLevel) -> Maybe (FlowsInto l l')
decideFlow SLow _ = Just LowFlowsAnywhere
decideFlow SHigh SHigh = Just HighFlowsToHigh
decideFlow SHigh SLow = Nothing
