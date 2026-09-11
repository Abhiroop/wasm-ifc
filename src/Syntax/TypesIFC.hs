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
  TODO(ifc P3): two points are enough for the theorem and for every example in sight (SecWasm
  itself is stated over any join semi-lattice, §3.1, but its examples use L/M/H). Keep two:
  the pc pre-pass in "Syntax.InstructionsIFC" converges trivially over two points, and a
  finite lattice can be a later generalisation if a case study asks for it.
-}
data SecLevel = Low | High
    deriving stock (Eq, Ord, Show)

infix 6 :~

{- | A value type together with the security level of the values it classifies: SecWasm's
  labelled type @τ ::= t⟨ℓ⟩@ (Fig. 8), which is also what its type stack @st@ holds, so the
  single-list encoding is the paper's.
  TODO(ifc P3): naming. @LValType@ reads as "l-value type"; the repo's rule is names that read
  as prose (CLAUDE.md), so @LabelledValType@ would fit. Keep the label on the type rather than
  as a parallel @[SecLevel]@ index: one list is the simpler encoding (STYLE.md §2's spirit)
  and matches the paper's @st@.
-}
data LValType = ValType :~ SecLevel
    deriving stock (Eq, Show)

{- | The term-level witness of a security level (a hand-rolled singleton).
  TODO(ifc P2): replace by @genSingletons [''SecLevel, ''LValType]@ (singletons-base, as
  "Syntax.Types" does for 'ValType'), which gives @SSecLevel@ (@SLow@, @SHigh@),
  @Sing (l :: SecLevel)@, 'Data.Singletons.SingI' and the list singletons for @[LValType]@ for
  free. Needed in three places: the elaborator reflects the policy's labels and the load/store
  immediates to the type level; 'Validation.Shape.Append' witnesses over labelled stacks; and
  the interpreter reads the load's @Sing ℓ@ at run time for SecWasm's dynamic check. This GADT
  then goes.
-}
data KnownSecLevel (l :: SecLevel) where
    IsLow :: KnownSecLevel 'Low
    IsHigh :: KnownSecLevel 'High

{- | @l@ may flow into @l'@: the lattice order, as a constraint.
  TODO(ifc P1): unused so far; it is meant for every @⊑@ premise of SecWasm's rules (T-STORE's
  @pc ⊔ ℓa ⊔ ℓv ⊑ ℓ@, T-CALL's @pc ⊑ ℓ@, T-BR-IF's @pc ⊔ ℓ ⊑ C.labels[i]@, the sets) and for
  the explicit relabelling that replaces the paper's subtyping (see the header of
  "Syntax.InstructionsIFC"). Before using it, change its form: a class is resolved by GHC on
  hand-written programs, but validating a /decoded/ module must produce the evidence at run
  time from singletons, and a class constraint cannot be constructed dynamically. Make it a
  GADT witness, as 'Syntax.Types.IsNum' is:
  @data FlowsInto l l' where LowFlowsAnywhere :: FlowsInto 'Low l; HighFlowsToHigh :: FlowsInto 'High 'High@
  with @decideFlow :: Sing l -> Sing l' -> Maybe (FlowsInto l l')@ for the elaborator, and a
  second witness @StackAtLeast pc rs@ (structured like 'Validation.Shape.Append') for "every
  label in @rs@ is @⊒ pc@", which block results and branch targets need. Instructions carry
  these as fields, like every other refinement in 'Instr'.
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
  TODO(ifc P1): a design constraint on every rule that uses this family: GHC reduces it only
  on concrete levels; it knows nothing of commutativity, associativity or idempotence, so a
  rule that needs @l :/\ l' ~ l' :/\ l@ or @l :/\ l ~ l@ to unify will not type-check on
  variables. Write the rules so the join only ever appears in a /result/ position built from
  the operands' labels (as every rule in "Syntax.InstructionsIFC" does), and let the elaborator
  instantiate everything concretely; never require GHC to prove two joins equal. If a rule
  ever needs a lattice law, add it as a witness the elaborator produces, not as an axiom.
-}
type family (:/\) (l :: SecLevel) (l' :: SecLevel) :: SecLevel where
    'Low :/\ 'Low = 'Low
    _ :/\ _ = 'High
