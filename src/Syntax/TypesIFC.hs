{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- | The information-flow vocabulary the IFC layer adds to the core types: security levels,
  value types labelled with one, the flow relation and the join, the shape of a label context
  entry, and the labelled layout of linear memory. Abhiroop's first cut (2026-09); the labelled
  instruction GADT in "Syntax.InstructionsIFC" is indexed by these.

  Every side condition of SecWasm's typing rules is a __witness GADT__ here ('FlowsInto',
  'StackAtLeast', 'SpanAt'), carried as a field of the instruction it guards, exactly as
  'Syntax.Types.IsNum' and 'Validation.Shape.Append' are. Two reasons, both from
  "Syntax.InstructionsIFC"'s header: a hand-written program then states its own proof
  obligations and GHC discharges them, and a /decoded/ module can have the same evidence
  produced at run time by the elaborator from singletons ('decideFlow'), which a class
  constraint could never be.
-}
module Syntax.TypesIFC (
    -- * Security levels
    SecLevel (..),
    SSecLevel (..),
    {- | @LowSym0@ and @HighSym0@ are @singletons@' defunctionalisation symbols for the two
    constructors; they are part of the generated API and are exported so that generated
    code elsewhere can name them (and so @-Wunused-top-binds@ stays quiet).
    -}
    LowSym0,
    HighSym0,
    type (:/\),

    -- * Labelled value types
    LValType (..),

    -- * Flow witnesses
    FlowsInto (..),
    decideFlow,
    StackAtLeast (..),

    -- * Label (block) contexts
    LabelShape (..),
    LabelPc,
    LabelResults,

    -- * The labelled layout of linear memory
    SpanShape (..),
    MemPolicy,
    SpanAt (..),
    spanBounds,
) where

import Data.Kind (Type)
import Data.Singletons.Base.TH (Sing, fromSing, genSingletons)
import GHC.TypeNats (type (+))
import Numeric.Natural (Natural)

import Syntax.Types (ValType)

{- | The two-point security lattice.
  TODO(ifc P3): two points are enough for the theorem and for every example in sight (SecWasm
  itself is stated over any join semi-lattice, §3.1, but its examples use L/M/H). Keep two:
  the pc pre-pass in "Syntax.InstructionsIFC" converges trivially over two points, and a
  finite lattice can be a later generalisation if a case study asks for it.
-}
data SecLevel = Low | High
    deriving stock (Eq, Ord, Show)

-- Singletons for the security level: the load/store label immediates, the elaborator's
-- 'decideFlow', and (later) the labels it reflects out of the policy all need the level at
-- both levels at once. This replaces the hand-rolled @KnownSecLevel@ of the first cut, per
-- STYLE.md §11 ("the library's singletons over hand-rolled ones").
$(genSingletons [''SecLevel])

infixl 7 :/\

{- | The join (least upper bound) of two levels: the label of a value computed from both.
  TODO(ifc P3): naming. @/\@ is the meet in lattice notation; the join is @\/@ (⊔). Rename
  before it spreads further.
  TODO(ifc P2): the elaborator also needs the join on singletons,
  @sJoin :: Sing l -> Sing l' -> Sing (l :/\ l')@, one pattern match (with singletons-th a
  term-level @join@ generates the family and @sJoin@ together).
  A design constraint on every rule that uses this family: GHC reduces it only on concrete
  levels; it knows nothing of commutativity, associativity or idempotence, so a rule that
  needs @l :/\ l' ~ l' :/\ l@ or @l :/\ l ~ l@ to unify will not type-check on variables.
  Every rule in "Syntax.InstructionsIFC" therefore writes the join only in a /result/ position
  built from the operands' labels, or inside a witness the elaborator constructs concretely;
  GHC is never asked to prove two joins equal.
-}
type family (:/\) (l :: SecLevel) (l' :: SecLevel) :: SecLevel where
    'Low :/\ 'Low = 'Low
    _ :/\ _ = 'High

infix 6 :~

{- | A value type together with the security level of the values it classifies: SecWasm's
  labelled type @τ ::= t⟨ℓ⟩@ (Fig. 8), which is also what its type stack @st@ holds, so the
  single-list encoding is the paper's.
  TODO(ifc P3): naming. @LValType@ reads as "l-value type"; the repo's rule is names that read
  as prose (CLAUDE.md), so @LabelledValType@ would fit.
-}
data LValType = ValType :~ SecLevel
    deriving stock (Eq, Show)

{- | Evidence that @l@ may flow into @l'@ — the lattice order @l ⊑ l'@, as a term.

  This is the witness every @⊑@ premise of SecWasm's rules is discharged by: T-STORE's
  @pc ⊔ ℓa ⊔ ℓv ⊑ ℓ@, T-BR-IF's @pc ⊔ ℓ ⊑ C.labels[i]@, T-IF's raised pc, and the explicit
  relabelling that replaces the paper's subtyping (see 'Syntax.InstructionsIFC.IRelabel').
  Being a GADT rather than a class is what lets the elaborator build it at run time
  ('decideFlow') for a module it has just decoded.
-}
type FlowsInto :: SecLevel -> SecLevel -> Type
data FlowsInto l l' where
    -- | @Low ⊑ anything@ — public data may be used anywhere.
    LowFlowsAnywhere :: FlowsInto 'Low l
    -- | @High ⊑ High@ — secret data may only reach secret sinks.
    HighFlowsToHigh :: FlowsInto 'High 'High

-- | Decide the flow relation on singletons: the elaborator's way to build a 'FlowsInto'.
decideFlow :: Sing (l :: SecLevel) -> Sing (l' :: SecLevel) -> Maybe (FlowsInto l l')
decideFlow SLow _ = Just LowFlowsAnywhere
decideFlow SHigh SHigh = Just HighFlowsToHigh
decideFlow SHigh SLow = Nothing

{- | Evidence that every label in a labelled stack segment is at or above @pc@ — SecWasm's
  "the results are @⊒ pc@" premise on blocks, branch targets and @return@ (T-BLOCK, T-BR,
  T-RETURN).

  It is what makes the flat, flow-insensitive pc scheme sound: a block entered under @pc@ can
  only leave behind values a @pc@-observer was already allowed to learn, so the raise ends
  exactly where the block does. Structured like 'Validation.Shape.Append' — a spine the length
  of the segment.
  TODO(ifc P2): the elaborator needs @decideStackAtLeast :: Sing pc -> Sing ts -> Maybe (StackAtLeast pc ts)@,
  which needs singletons for @[LValType]@ (one more @genSingletons@ call, once the labelled
  shapes it would reflect from exist).
-}
type StackAtLeast :: SecLevel -> [LValType] -> Type
data StackAtLeast pc ts where
    AtLeastNil :: StackAtLeast pc '[]
    AtLeastCons :: FlowsInto pc l -> StackAtLeast pc ts -> StackAtLeast pc ((t ':~ l) ': ts)

{- | One entry of the label (block) context: the pc a block's body is typed under, and the
  labelled types it leaves on the stack when a branch to it is taken.

  The pc travels with the label because that is what a branch has to be checked against: a
  @br@ out of a secret context into a block typed public would leak the fact that the branch
  was taken (SecWasm's Example 8). A prose name rather than a bare pair, like
  'Validation.Shape.FrameShape'; used only promoted.
-}
data LabelShape = LabelShape
    { pc :: SecLevel
    , results :: [LValType]
    }
    deriving stock (Eq, Show)

type LabelPc :: LabelShape -> SecLevel
type family LabelPc lbl where
    LabelPc ('LabelShape p _) = p

type LabelResults :: LabelShape -> [LValType]
type family LabelResults lbl where
    LabelResults ('LabelShape _ rs) = rs

{- | One span of linear memory: a run of @bytes@ bytes, every one of which carries @label@ for
  the lifetime of the module.
-}
data SpanShape = SpanShape
    { bytes :: Natural
    , label :: SecLevel
    }
    deriving stock (Eq, Show)

{- | The labelled layout of a module's linear memory: consecutive spans, laid end to end from
  address 0. A span's base address is therefore not declared but /derived/ — the sum of the
  lengths before it — which is why overlapping spans with disagreeing labels are not
  representable (STYLE.md §2) and why 'SpanAt' can compute a base address at all.

  __Why this, and not SecWasm's memory.__ SecWasm labels memory /per byte/ and
  /flow-sensitively/ (§3.2): the label of a byte is run-time state that a store overwrites, so
  the label of the bytes a @load@ reaches is not known statically and its check
  (@⨆ labels read ⊑ ℓ@) has to be dynamic — the one dynamic check in an otherwise static
  system, and a trap. Declaring the layout up front instead makes a byte's label /immutable/,
  which is exactly the property that turns that check static: the label of what a load reads
  is determined by which span it lands in, and no store can change it. It is the same
  flow-insensitive treatment SecWasm already gives locals and globals (§5), applied to memory.

  What it costs: SecWasm's relabelling store (a public store over secret bytes makes them
  public again) is gone — a store must respect the span's declared label instead — and the
  layout must be known, which is a policy the producer writes, not something inferred. What it
  buys: no label state at run time, no label join per byte read, and no trap from the label
  check. The paper's objection to a single label for the whole memory (compiled code keeps
  secret and public data in one linear memory) is answered by spans being per-object rather
  than per-memory: an array or a struct is a span.

  What stays dynamic is only what plain WebAssembly already checks dynamically — that the
  effective address really is inside the span the proof names. That is a bounds check against
  the span instead of against the memory, and it traps like any other out-of-bounds access
  (accepted under SecWasm's termination-insensitive noninterference, Cor. 1).
-}
type MemPolicy = [SpanShape]

{- | Evidence that a span of @bytes@ bytes labelled @l@ begins at address @base@ in @policy@ —
  a typed de Bruijn index into the policy that /computes the base address as it walks/, by
  summing the lengths it steps over.

  This is the proof a load or a store carries ("Syntax.InstructionsIFC"): the programmer (or
  the elaborator) says which span the access targets, and the witness hands back both the
  static label @l@ the type system reasons with and, through 'spanBounds', the two numbers the
  run-time bounds check needs. Each step carries the length it skips as a singleton so those
  numbers survive to the term level.
-}
type SpanAt :: MemPolicy -> Natural -> Natural -> SecLevel -> Type
data SpanAt policy base bytes l where
    SpanHere :: Sing bytes -> SpanAt ('SpanShape bytes l ': rest) 0 bytes l
    SpanThere ::
        Sing skip ->
        SpanAt rest base bytes l ->
        SpanAt ('SpanShape skip skipped ': rest) (skip + base) bytes l

-- | The first byte of the span a witness names, and its length: what the bounds check needs.
spanBounds :: SpanAt policy base bytes l -> (Natural, Natural)
spanBounds (SpanHere len) = (0, fromSing len)
spanBounds (SpanThere skip rest) =
    let (base, len) = spanBounds rest
     in (fromSing skip + base, len)
