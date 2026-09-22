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

{- | The dynamic premises a rule may have. Every instruction names one; most name none.

  Most of SecWasm's premises are decided once, by the validator, and leave no trace in the
  instruction beyond its type. A few cannot be, because they are about run-time state: the
  labels of the bytes a load reads, or the callee a table lookup produces. An instruction
  whose rule has such a premise names it in its type, so that the machine has to show
  evidence for it before it may step (see "Runtime.Obligation"). 'CalleeWithin' is declared
  for @call_indirect@ but nothing uses it yet.
-}
data DynamicCheck = NoDynamicCheck | BytesBelow SecLevel | CalleeWithin SecLevel

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

  TODO(ifc P1): only the loads carry this so far, and they carry it at run time (see
  'Runtime.Obligation.CheckPassed'). It is the premise of every SecWasm rule with a @⊑@ in
  it: @local.set@, @global.set@, the stores, the branches and the calls.
-}
data FlowsInto (l :: SecLevel) (l' :: SecLevel) where
    LowFlowsAnywhere :: FlowsInto 'Low l
    HighFlowsToHigh :: FlowsInto 'High 'High

decideFlow :: Sing (l :: SecLevel) -> Sing (l' :: SecLevel) -> Maybe (FlowsInto l l')
decideFlow SLow _ = Just LowFlowsAnywhere
decideFlow SHigh SHigh = Just HighFlowsToHigh
decideFlow SHigh SLow = Nothing
