{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{- | The information-flow vocabulary the IFC layer adds to the core types: security levels,
  value types labelled with one, the flow relation and the join. Abhiroop's first cut
  (2026-09); the labelled instruction GADT in "Syntax.InstructionsIFC" is indexed by these.
-}
module Syntax.TypesIFC (
    SecLevel (..),
    LValType (..),
    KnownSecLevel (..),
    CanFlowInto,
    type (:/\),
) where

import Syntax.Types (ValType)

{- | The two-point security lattice.
  TODO(ifc P3): two points are enough for the theorem and for every example in sight; an
  arbitrary lattice (a class with ⊑ and ⊔, or a product for principals) is a later
  generalisation. Do it after the system works for two, and only if a case study asks for it.
-}
data SecLevel = Low | High
    deriving stock (Eq, Ord, Show)

infix 6 :~

{- | A value type together with the security level of the values it classifies.
  TODO(ifc P3): naming. @LValType@ reads as "l-value type"; the repo's rule is names that read
  as prose (CLAUDE.md), so @LabelledValType@ would fit. Also where the label sits: on the type
  (as here, SecWasm style, the stack being one @[LValType]@) or as a parallel index (@[ValType]@
  plus @[SecLevel]@, which keeps the existing 'Validation.Shape.Append' witnesses and singletons
  untouched at the price of two lists that must stay in step). The single list is the simpler
  encoding (STYLE.md §2's spirit); keep it unless the P0 structure decision prefers the split.
-}
data LValType = ValType :~ SecLevel
    deriving stock (Eq, Show)

{- | The term-level witness of a security level (a hand-rolled singleton).
  TODO(ifc P2): replace by @genSingletons [''SecLevel, ''LValType]@ (singletons-base, as
  "Syntax.Types" does for 'ValType'), which gives @SSecLevel@ (@SLow@, @SHigh@),
  @Sing (l :: SecLevel)@, 'Data.Singletons.SingI' and the list singletons for @[LValType]@ for
  free. The elaborator needs those to reflect decoded labels to the type level and to build
  'Validation.Shape.Append' witnesses over labelled stacks; this GADT then goes.
-}
data KnownSecLevel (l :: SecLevel) where
    IsLow :: KnownSecLevel 'Low
    IsHigh :: KnownSecLevel 'High

{- | @l@ may flow into @l'@: the lattice order, as a constraint.
  TODO(ifc P1): unused so far; it is meant to guard @local.set@, @global.set@, the stores and
  the host sinks (see the TODOs in "Syntax.InstructionsIFC"). Before using it, change its
  form: a class is resolved by GHC on hand-written programs, but validating a /decoded/ module
  must produce the evidence at run time from singletons, and a class constraint cannot be
  constructed dynamically. Make it a GADT witness, as 'Syntax.Types.IsNum' is:
  @data FlowsInto l l' where LowFlowsAnywhere :: FlowsInto 'Low l; HighFlowsToHigh :: FlowsInto 'High 'High@
  with @decideFlow :: Sing l -> Sing l' -> Maybe (FlowsInto l l')@ for the elaborator; the
  instruction then carries the witness as a field, like every other refinement in 'Instr'.
-}
class CanFlowInto (l :: SecLevel) (l' :: SecLevel)

instance CanFlowInto 'Low 'Low
instance CanFlowInto 'Low 'High
instance CanFlowInto 'High 'High

infixl 7 :/\

{- | The join (least upper bound) of two levels: the label of a value computed from both.
  TODO(ifc P3): naming. @/\@ is the meet in lattice notation; the join is @\/@ (⊔). Rename
  before it spreads.
  TODO(ifc P2): the elaborator also needs the join on singletons,
  @sJoin :: Sing l -> Sing l' -> Sing (l :/\ l')@, one pattern match once the singletons exist
  (with singletons-th a term-level @join@ generates the family and @sJoin@ together).
-}
type family (:/\) (l :: SecLevel) (l' :: SecLevel) :: SecLevel where
    'Low :/\ 'Low = 'Low
    _ :/\ _ = 'High
