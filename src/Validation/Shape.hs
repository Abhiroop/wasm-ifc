{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- | The type-level validation vocabulary: the shapes the typed AST is indexed by. List
  concatenation and its 'Append' witness, typed de Bruijn indices ('Elem'), the module
  shape ('ModuleShape') against which @call@, globals and memory operations are checked,
  and the memory shape ('MemShape'). These are the "types" the syntax carries as indices,
  so the typed AST in "Syntax.Instructions" depends on this module.

  Library singletons (from @singletons-base@) are generated for 'ModuleShape', 'FrameShape'
  and 'MemShape'; the module exports openly so those generated @Sing@ constructors are
  visible to "Validation.Reflect" and "Validation.Elaborate".
-}
module Validation.Shape where

import Data.Kind (Type)
import Data.List.Singletons (type (++))
import Data.Singletons.Base.TH (SList (SCons, SNil), Sing, genSingletons)
import Numeric.Natural (Natural)

import Data.Type.Equality ((:~:) (Refl))
import Data.Word (Word64)
import Syntax.Types (AddrType, GlobalTypeOf (..), Mutability (..), SValType, ValType)
import Syntax.TypesIFC (FlowsInto, Join, LabelledFuncType (..), LabelledValType (..), SecLevel (..))

{- *** Stack order ***

   Every type-level @[LabelledValType]@ that describes a stack segment lists the /top/ of the stack
   first — the operand stack indices of 'Syntax.Instructions.Instr', the label result types,
   and the parameter and result lists of a 'FuncType' or block type once it is inside a shape
   (they are exactly the segment a call or block consumes and produces). Declared order, the
   order the text and binary formats write, survives only in the decoded "Syntax" and in a
   function's locals; "Validation.Reflect" converts at that boundary.
-}

-- We reuse @singletons-base@'s promoted list concatenation '(++)' (it is exactly the family we
-- would otherwise hand-roll). Stack shapes compose by appending the part a scope produces on
-- top of the part it leaves untouched. @++@ is not injective, so splitting a @ps ++ s@ stack
-- back into @ps@ and @s@ is driven by the 'Append' witness below rather than by inverting it.
-- (We do NOT import the library's @Elem@ — that is @Foldable@'s @Bool@-valued @elem@, unrelated
-- to our de Bruijn-index 'Elem'.)

{- | Evidence that @c@ is @a ++ b@. Its spine is the length of @a@; because @a@, @b@ and
  @c@ are independent indices, consuming it (in @splitStack@) never requires inverting
  @++@. Carried by the framed/branching instructions so the interpreter can peel operands.
  Poly-kinded, although every use is at labelled value types; the kind is an inferred binder
  (@forall {k}.@) so no use site has to pass it.
-}
type Append :: forall {k}. [k] -> [k] -> [k] -> Type
data Append a b c where
    ANil :: Append '[] b b
    ACons :: Append a b c -> Append (x ': a) b (x ': c)

-- | What an 'Append' witness is evidence of, as an equation.
appendIs :: Append a b c -> (a ++ b) :~: c
appendIs ANil = Refl
appendIs (ACons rest) = case appendIs rest of Refl -> Refl

{- | Build the 'Append' witness for a prefix from its singleton. The witness is just the spine
  of the prefix, so the suffix @b@ is whatever the use site fixes. The smart constructors in
  "Syntax.Instructions" use this with 'sing', so call sites with static stack shapes need not
  write witnesses by hand; the elaborator builds the same witness from decoded data with
  'Validation.Reflect.matchPrefix'.
-}
appendFromSing :: forall {k} (a :: [k]) (b :: [k]). Sing a -> Append a b (a ++ b)
appendFromSing SNil = ANil
appendFromSing (SCons _ rest) = ACons (appendFromSing rest)

{- | @ReverseOnto xs acc@ is @reverse xs ++ acc@, defined with the structural accumulator so it
  reduces one constructor at a time and never needs a lemma. It bridges the two orders in play:
  a call's argument segment lists the last argument first (top of stack), while locals number
  the first parameter 0 — so a function body's locals are @ReverseOnto params declared@.
-}
type ReverseOnto :: [k] -> [k] -> [k]
type family ReverseOnto xs acc where
    ReverseOnto '[] acc = acc
    ReverseOnto (x ': xs) acc = ReverseOnto xs (x ': acc)

{- | A typed de Bruijn index: a proof that @x@ is the element of @xs@ at this position,
  carrying both the position (its term-level structure) and the element (in its type).
  One workhorse for every index space: locals (@Elem t locals@), labels
  (@Elem rs labels@), functions (@Elem ft (ModuleFuncs shape)@) and globals.
-}
type Elem :: k -> [k] -> Type
data Elem x xs where
    Here :: Elem x (x ': xs)
    There :: Elem x xs -> Elem x (y ': xs)

{- | A branch target: like an 'Elem' into the label context, it names the label at a position
  and proves its result type is @rs@. It also says what the branch does to the pc stack
  ("Syntax.TypesIFC"): the entries of the blocks the branch may leave, the target's included,
  are raised by @l@, the level of the decision to branch, and the entries below are untouched.
  One witness for both facts, so the position and the raise cannot disagree.
-}
type BranchTarget :: SecLevel -> [LabelledValType] -> [[LabelledValType]] -> [SecLevel] -> [SecLevel] -> Type
data BranchTarget l rs labels pcs pcs' where
    TargetHere :: BranchTarget l rs (rs ': labels) (p ': pcs) (Join l p ': pcs)
    TargetThere :: BranchTarget l rs labels pcs pcs' -> BranchTarget l rs (other ': labels) (p ': pcs) (Join l p ': pcs')

{- | How far a @br_table@ reaches into the label context: the labels its targets may name,
  @reach@, which are the innermost ones down to its deepest target, and what it does to the pc
  stack. As for a single branch ('BranchTarget'), the entries of the blocks the table may leave
  are raised by @l@, here those of every label in @reach@, and the entries below are untouched.
  The targets are 'Elem's into @reach@, so no target can lie deeper than the raise.
-}
type TableReach :: SecLevel -> [[LabelledValType]] -> [SecLevel] -> [SecLevel] -> [[LabelledValType]] -> Type
data TableReach l labels pcs pcs' reach where
    ReachesHere :: TableReach l (label ': labels) (p ': pcs) (Join l p ': pcs) '[label]
    ReachesThere :: TableReach l labels pcs pcs' reach -> TableReach l (label ': labels) (p ': pcs) (Join l p ': pcs') (label ': reach)

-- | A target within a table's reach, as the label in the whole context it names.
withinReach :: TableReach l labels pcs pcs' reach -> Elem rs reach -> Elem rs labels
withinReach ReachesHere Here = Here
withinReach ReachesHere (There beyond) = case beyond of {}
withinReach (ReachesThere _) Here = Here
withinReach (ReachesThere reach) (There ix) = There (withinReach reach ix)

{- *** Preserved globals ***

   A region of code in which the pc is secret must leave public state as it found it. For most
   state the typing rules guarantee that by forbidding the write. A /preserved/ global
   ('Syntax.Types.Preserved') may be written there, and the machine guarantees the same by
   comparing: where a block, loop, conditional or call in which the pc may end up secret
   begins, it records the preserved globals, and where control comes out of it, they must hold
   the recorded values, or the run traps. The witnesses below say where that has to happen
   ('Restores', 'ReturnsWith') and which globals it concerns ('PreservedGlobals').
-}

-- | Why a global needs no comparison: it is not preserved, or it is secret, and then code under a secret pc may write it anyway.
data NoRestoreNeeded (mut :: Mutability) (l :: SecLevel) where
    ImmutableNeedsNone :: NoRestoreNeeded 'Immutable l
    MutableNeedsNone :: NoRestoreNeeded 'Mutable l
    SecretNeedsNone :: NoRestoreNeeded 'Preserved 'High

{- | The preserved globals of a module's global space, every one of them: each global is either
  one that needs no comparison or a preserved public one, which carries a @payload@ at its
  value type. With the type's singleton as payload this says which globals to record
  ('PreservedOf'); with a recorded word, what they must hold ('RecordedGlobals').
-}
type PreservedGlobals :: (ValType -> Type) -> [GlobalTypeOf LabelledValType] -> Type
data PreservedGlobals payload gs where
    NoGlobalsLeft :: PreservedGlobals payload '[]
    NotPreserved :: NoRestoreNeeded mut l -> PreservedGlobals payload gs -> PreservedGlobals payload ('GlobalType mut (t ':~ l) ': gs)
    PreservedHere :: payload t -> PreservedGlobals payload gs -> PreservedGlobals payload ('GlobalType 'Preserved (t ':~ 'Low) ': gs)

-- | Which globals of a global space are preserved.
type PreservedOf = PreservedGlobals SValType

-- | The value a preserved global had when it was recorded, as its machine word.
data Recorded (t :: ValType) = Recorded !(SValType t) !Word64

-- | The values the preserved globals of a global space had at some point.
type RecordedGlobals = PreservedGlobals Recorded

{- | Whether control coming out of a block, loop or conditional has to find the preserved
  globals as they were at its start. It has to if the pc drops there: @pcEnd@ is the most
  secret pc of the construct's own entry and the first of @pcsAfter@ the pc in force after it.
  A proof that the first flows into the second says the pc does not drop.
-}
data Restores (pcEnd :: SecLevel) (pcsAfter :: [SecLevel]) (gs :: [GlobalTypeOf LabelledValType]) where
    PcDoesNotDrop :: FlowsInto pcEnd pcAfter -> Restores pcEnd (pcAfter ': pcs) gs
    PreservedRestored :: PreservedOf gs -> Restores pcEnd pcsAfter gs

{- | The same for a function, whose body ends with the pc stack @pcOut@: if its pc is public
  when it returns, whichever way it returns, nothing has to be compared; otherwise the
  preserved globals must hold at the return what they held at the call.
-}
data ReturnsWith (pcOut :: [SecLevel]) (gs :: [GlobalTypeOf LabelledValType]) where
    ReturnsUnderPublicPc :: ReturnsWith ('Low ': pcs) gs
    RestoresOnReturn :: PreservedOf gs -> ReturnsWith pcOut gs

{- | @∃bound ps rs. (Sing bound, Sing ps, Sing rs, Elem ('LabelledFuncType bound ps rs) fts)@ — a
  function reference resolved against the signature, carrying its bound and its parameter and
  result shapes: what a table entry, an element segment and the runtime's export lookup hold.
-}
data SomeFuncRef (fts :: [LabelledFuncType]) where
    SomeFuncRef :: Sing (bound :: SecLevel) -> Sing (ps :: [LabelledValType]) -> Sing (rs :: [LabelledValType]) -> Elem ('LabelledFuncType bound ps rs) fts -> SomeFuncRef fts

{- | The compile-time shape of a module: the types of its function, global, memory, table and
  data-segment index spaces. Used as a single kind index on the instruction GADT so it stays compact. Memories
  are identified by their 'MemShape' (so a memory carries its declared type, like every other
  instance). A record only for the field names' documentation value — 'ModuleShape' is used
  promoted, and the projection type families below ('ModuleFuncs' etc.) are what read the
  fields at the type level.

  The function and global types here are labelled: a function has a bound on the context it
  may be called from besides labelled parameters and results ('LabelledFuncType'), and a global
  has a security level.
-}
data ModuleShape = ModuleShape
    { funcTypes :: [LabelledFuncType]
    , globalTypes :: [GlobalTypeOf LabelledValType]
    , memShapes :: [MemShape]
    , tableShapes :: [TableShape]
    , dataShapes :: [DataShape]
    -- ^ one entry per data segment: the data index space, which only has a size
    , elemShapes :: [ElemShape]
    -- ^ one entry per element segment, with the type of its references
    }

type ModuleFuncs :: ModuleShape -> [LabelledFuncType]
type family ModuleFuncs s where
    ModuleFuncs ('ModuleShape fs _ _ _ _ _) = fs

type ModuleGlobals :: ModuleShape -> [GlobalTypeOf LabelledValType]
type family ModuleGlobals s where
    ModuleGlobals ('ModuleShape _ gs _ _ _ _) = gs

type ModuleMems :: ModuleShape -> [MemShape]
type family ModuleMems s where
    ModuleMems ('ModuleShape _ _ ms _ _ _) = ms

type ModuleTables :: ModuleShape -> [TableShape]
type family ModuleTables s where
    ModuleTables ('ModuleShape _ _ _ ts _ _) = ts

type ModuleData :: ModuleShape -> [DataShape]
type family ModuleData s where
    ModuleData ('ModuleShape _ _ _ _ ds _) = ds

type ModuleElems :: ModuleShape -> [ElemShape]
type family ModuleElems s where
    ModuleElems ('ModuleShape _ _ _ _ _ es) = es

{- | The per-activation (function-scoped) part of an instruction's context: the local
  variable types and the function's result type. These two always share a scope — both
  are fixed within a function and both change exactly on a @call@ — so they travel
  together as one index on the typed AST.

  The locals are labelled: a local's security level is declared once and fixed for the function.
  (The function's bound is not here: it is the pc the body's pc stack starts at, see
  'Syntax.Functions.FunctionBody'.)
-}
data FrameShape = FrameShape
    { locals :: [LabelledValType]
    , results :: [LabelledValType]
    }

type FrameLocals :: FrameShape -> [LabelledValType]
type family FrameLocals f where
    FrameLocals ('FrameShape ls _) = ls

type FrameReturn :: FrameShape -> [LabelledValType]
type family FrameReturn f where
    FrameReturn ('FrameShape _ rs) = rs

{- | The type-level counterpart of 'Syntax.Types.MemType', used as the shape index of a
  'Runtime.MemInst.MemInst' and the memory slots of a 'ModuleShape'. 'MemType'\'s @Word32@
  limits do not promote to a kind, so this mirror uses type-level 'Natural's (reflected
  from the decoded limits during elaboration). The limits are carried for faithfulness,
  not used for static checking — WebAssembly bounds are runtime traps. (Used only
  promoted; the term-level selectors document the fields.)

  IFC note: nothing to add here. SecWasm labels every /byte/ at run time, flow-sensitively, and
  puts the static labels on the load and store instructions as immediates (its §3.2 rejects a
  single label per memory as too rigid); so the memory's shape stays as it is and the labels
  live in 'Runtime.MemInst.MemInst'. See the memory TODO on 'Syntax.Instructions.IMemSize'.
-}
data MemShape = MemShape
    { addrType :: AddrType
    , minPages :: Natural
    , maxPages :: Maybe Natural
    }
    deriving stock (Eq, Show)

{- | The type-level counterpart of a table's type: the type of its entries (a reference type,
  which the instructions on tables ask for as an 'Syntax.Types.IsRef'), its security level and
  its size limits (as 'Natural's, like 'MemShape').

  IFC note: unlike a memory, a table has one level for good, declared by the policy like a
  global's ("Validation.Policy"). SecWasm covers WebAssembly 1.0, where no instruction writes a
  table; with the table instructions a table is state like any other, and its level bounds what
  may be written to it and labels what is read from it, its size included.
-}
data TableShape = TableShape
    { entryType :: ValType
    , tableLevel :: SecLevel
    , minEntries :: Natural
    , maxEntries :: Maybe Natural
    }
    deriving stock (Eq, Show)

{- | An element segment's type: that of the references it holds. The element index space is a
  list of these, so @table.init@ and @elem.drop@ name a segment with an 'Elem' proof.
-}
newtype ElemShape = ElemShape ValType
    deriving stock (Eq, Show)

{- | A data segment has no type beyond existing: the data index space is a list of these, so
  @memory.init@ and @data.drop@ can name a segment with an 'Elem' proof like every other index.
-}
data DataShape = DataShape
    deriving stock (Eq, Show)

-- Library singletons for the shape kinds. The list/'Maybe'/'Natural' fields draw their 'Sing'
-- instances from @singletons-base@; the element types from "Syntax.Types".
$(genSingletons [''MemShape, ''TableShape, ''DataShape, ''ElemShape, ''ModuleShape, ''FrameShape])
