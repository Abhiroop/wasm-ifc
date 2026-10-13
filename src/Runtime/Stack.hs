{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- | Type-indexed runtime structures for the intrinsically-typed interpreter: the value
  stack, locals, and globals, each indexed by the (type-level) list of value types it
  holds. A value-stack or global slot of type @t ':~ l@ stores a bare @HostType t@ — there is no
  per-value tag, because the index already says how to read it, and no trace of the security
  level @l@, which exists only in the types. Locals are stored flat
  instead, one packed word each, for the reason given at 'LocalSpaceInst'.

  Splitting a concatenated stack @c = a ++ b@ back into its parts is driven by an
  'Append' witness, not by inverting the (non-injective) @++@ family. The witness's
  three indices are independent, so @splitStack@ never asks GHC to invert anything.
-}
module Runtime.Stack (
    ValueStack (..),
    LocalSpaceInst,
    noLocals,
    GlobalSpaceInst (..),
    MemSpaceInst (..),
    TableSpaceInst (..),
    TableInsts (..),
    ElemSpaceInst (..),
    noTables,
    getTable,
    setTable,
    getElements,
    ExceptionInst (..),
    tagName,
    keepException,
    keptException,
    dropElements,
    DataSpaceInst (..),
    getSegment,
    dropSegment,
    appendStack,
    relabelStack,
    retagStack,
    appendWith,
    splitStack,
    seedLocals,
    defaultLocals,
    getLocal,
    setLocal,
    getGlobal,
    setGlobal,
    recordPreserved,
    stillRestored,
    getMem,
    setMem,
    firstMem,
    setFirstMem,
) where

import Control.Monad.ST (ST)
import Data.ByteString (ByteString)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Kind (Type)
import Data.Vector.Unboxed qualified as UV
import Data.Vector.Unboxed.Mutable qualified as MV
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64, castFloatToWord32, castWord32ToFloat, castWord64ToDouble)

import Data.List.Singletons (type (++))
import Data.Singletons.Base.TH (SList (SCons, SNil), Sing)
import Runtime.MemInst (MemInst)
import Runtime.TableInst (FunctionDirectory, TableInst, functionDirectory)
import Syntax.Immediates (HostType, Reference (..), Vector128 (..), referenceTo, referent)
import Syntax.Types
import Syntax.TypesIFC
import Validation.Ref (LocalRef, localPosition, localType, wordsOf)
import Validation.Shape (Append (..), DataShape (..), Elem (..), ElemShape (..), MemShape, PreservedGlobals (..), PreservedOf, Recorded (..), RecordedGlobals, ReverseOnto, TableShape)

{- | The operand stack (head = top of stack), indexed by the types it holds.

  Every field here and in the other runtime containers is strict, and deliberately so: a
  WebAssembly value is a machine word that is always defined, so forcing one can never change
  a result, whereas /not/ forcing it does. With lazy fields, @i32.add@ pushes an unevaluated
  thunk, the next @i32.add@ builds a thunk on top of that, and a program whose working set is
  a handful of words retains a heap proportional to the number of instructions it has run.
  Measured before this became strict: @fib 30@ spent 48 % of its time in the collector and
  peaked at 163 MB of residency — the specific, stated suspicion STYLE.md §0 asks for before
  performance is allowed to motivate anything. See @bench/@ for how that was measured.
-}
type ValueStack :: [LabelledValType] -> Type
data ValueStack s where
    VNil :: ValueStack '[]
    (:#) :: !(HostType t) -> !(ValueStack ts) -> ValueStack ((t ':~ l) ': ts)

infixr 5 :#

{- | The instance of a function activation's local index space: its locals' current values,
  indexed by their types.

  Stored flat in an unboxed vector of machine words, one per local and two for a 128-bit
  vector, and reached through a 'Validation.Ref.LocalRef' that elaboration resolved from the
  local's witness: its place, and its type, which says how to read the words back. Every other
  WebAssembly value fits in 64 bits, so the word /is/ the value, bit for bit (a float's NaN
  payload survives the round trip). A cons list indexed by the witness itself, the obvious
  typed encoding, makes every access walk to its local and every @local.set@ rebuild the cells
  in front of it (TODO.md §I, E2, E2b).

  The type is abstract, with one invariant: the vector holds exactly the words the types of
  @ls@ take ('wordsIn'). 'defaultLocals' and 'seedLocals' establish it and 'setLocal' preserves
  it, being the only ways to make or change a frame; and a reference's place, with the words
  of its type, is below that length because its witness proves the local exists and
  'Validation.Ref.resolveLocal' counts the words before it the same way. The two together
  license the unchecked read and write.
-}
type LocalSpaceInst :: [LabelledValType] -> Type
newtype LocalSpaceInst ls = LocalSpaceInst (UV.Vector Word64)

-- | The instance of a module's global index space: the globals' current values, by type.
type GlobalSpaceInst :: [LabelledGlobalType] -> Type
data GlobalSpaceInst gs where
    GNil :: GlobalSpaceInst '[]
    GCons :: !(HostType t) -> !(GlobalSpaceInst gs) -> GlobalSpaceInst ('GlobalType mut (t ':~ l) ': gs)

{- | Give a stack the levels a 'SegmentFlows' witness allows: the same words, rebuilt under
  the new index. Linear in the segment, like every operation on the value stack.
-}

-- Inlined, so that the usual witness, of a segment at its own levels, costs a comparison where
-- the stack is used and no call.
{-# INLINE relabelStack #-}
relabelStack :: SegmentFlows from to -> ValueStack from -> ValueStack to
relabelStack flows vs = case flows of
    SegmentAsItIs -> vs
    _ -> relabelByValue flows vs

relabelByValue :: SegmentFlows from to -> ValueStack from -> ValueStack to
relabelByValue NoValuesFlow VNil = VNil
relabelByValue (ValueFlows _ rest) (v :# vs) = v :# relabelByValue rest vs
relabelByValue SegmentAsItIs vs = vs

-- | Re-index a stack under other levels for the same value types: the host boundary's retagging.
retagStack :: SameValueTypes from to -> ValueStack from -> ValueStack to
retagStack NoValues VNil = VNil
retagStack (SameValue rest) (v :# vs) = v :# retagStack rest vs

-- | Concatenate two stacks; the upper one ends up on top. Purely structural.
appendStack :: ValueStack a -> ValueStack b -> ValueStack (a ++ b)
appendStack VNil ys = ys
appendStack (x :# xs) ys = x :# appendStack xs ys

-- | Concatenate two stacks, guided by an 'Append' witness (so the result type is the witness's).
appendWith :: Append a b c -> ValueStack a -> ValueStack b -> ValueStack c
appendWith ANil VNil ys = ys
appendWith (ACons w) (x :# xs) ys = x :# appendWith w xs ys

-- | Split a concatenated stack into its parts, guided by an 'Append' witness.
splitStack :: Append a b c -> ValueStack c -> (ValueStack a, ValueStack b)
splitStack ANil vs = (VNil, vs)
splitStack (ACons w) (x :# vs) = let (upper, lower) = splitStack w vs in (x :# upper, lower)

{- | Seed a callee's locals from its argument segment: the parameters, then the declared locals
  at zero. The segment lists the last argument first (top of stack) while local 0 is the first
  parameter, so the arguments are written from the last slot of the parameters downwards —
  which is 'ReverseOnto', done in place. One allocation per call: calls are the hottest path
  there is, and building the frame through intermediate lists cost @fib@ a third more heap.
-}
seedLocals :: SegmentFlows args ps -> Sing ps -> Sing declared -> ValueStack args -> LocalSpaceInst (ReverseOnto ps declared)
seedLocals flows paramTypes declaredTypes args =
    LocalSpaceInst (UV.create frame)
  where
    arity = wordsIn paramTypes
    frame :: ST s (MV.MVector s Word64)
    frame = do
        slots <- MV.replicate (arity + wordsIn declaredTypes) 0
        writeArguments slots arity flows paramTypes args
        pure slots

{- | Write a stack's values into consecutive slots, the top one ending just below @end@ and
  each deeper one just below it; a vector takes two slots, its low word first. The arguments
  arrive at the levels the caller had ('SegmentFlows' says they may flow into the
  parameters'); a level is nothing at run time, so the words go in as they are.
-}
writeArguments :: MV.MVector s Word64 -> Int -> SegmentFlows args ps -> Sing (ps :: [LabelledValType]) -> ValueStack args -> ST s ()
writeArguments _ _ NoValuesFlow SNil VNil = pure ()
writeArguments _ _ SegmentAsItIs SNil VNil = pure ()
writeArguments slots end flows@(ValueFlows _ _) types@(SCons _ _) stack@(_ :# _) = writeArgument slots end (flowsOfRest flows) types stack
writeArguments slots end SegmentAsItIs types@(SCons _ _) stack@(_ :# _) = writeArgument slots end SegmentAsItIs types stack

-- | 'writeArguments' for a segment that has a first value: that value, then the rest.
writeArgument :: MV.MVector s Word64 -> Int -> SegmentFlows args ps -> Sing ((t ':~ lp) ': ps) -> ValueStack ((t ':~ la) ': args) -> ST s ()
writeArgument slots end flows (SCons (st :%~ _) rest) (x :# xs) = case st of
    SV128 -> case x of
        Vector128 low high -> do
            MV.unsafeWrite slots (end - 2) low
            MV.unsafeWrite slots (end - 1) high
            writeArguments slots (end - 2) flows rest xs
    _ -> do
        MV.unsafeWrite slots (end - 1) (packValue st x)
        writeArguments slots (end - 1) flows rest xs

{- | A locals frame of the given shape, every slot zero (how declared locals start a call).
  Zero is the all-zero word at every value type, the floats' @+0.0@ included.
-}
defaultLocals :: Sing (ls :: [LabelledValType]) -> LocalSpaceInst ls
defaultLocals types = LocalSpaceInst (UV.replicate (wordsIn types) 0)

-- | The frame of a function with neither parameters nor declared locals.
noLocals :: LocalSpaceInst '[]
noLocals = defaultLocals SNil

-- | Read a local: its reference says where it is and how to read the word (or two) found there.
getLocal :: LocalRef (t ':~ l) ls -> LocalSpaceInst ls -> HostType t
getLocal ref (LocalSpaceInst values) = case localType ref of
    SV128 -> Vector128 (UV.unsafeIndex values at) (UV.unsafeIndex values (at + 1))
    ty -> unpackValue ty (UV.unsafeIndex values at)
  where
    at = localPosition ref

-- | Write a local: a copy of the frame with its word (or two) replaced, so of the same length.
setLocal :: LocalRef (t ':~ l) ls -> HostType t -> LocalSpaceInst ls -> LocalSpaceInst ls
setLocal ref v (LocalSpaceInst values) = case localType ref of
    SV128 -> case v of
        Vector128 low high -> LocalSpaceInst (UV.modify (\slots -> MV.unsafeWrite slots at low >> MV.unsafeWrite slots (at + 1) high) values)
    ty -> LocalSpaceInst (UV.modify (\slots -> MV.unsafeWrite slots at (packValue ty v)) values)
  where
    at = localPosition ref

{- | Pack a value into a machine word, bit for bit. Every WebAssembly value but a vector fits in
  one; of a vector this is the low word, and 'highWord' the other.
-}
packValue :: Sing (t :: ValType) -> HostType t -> Word64
packValue SI32 v = fromIntegral v
packValue SI64 v = v
packValue SF32 v = fromIntegral (castFloatToWord32 v)
packValue SF64 v = castDoubleToWord64 v
packValue SV128 (Vector128 low _) = low
packValue SFuncRef (Reference w) = w
packValue SExternRef (Reference w) = w
packValue SExnRef (Reference w) = w

-- | The second word of a value: a vector's high word, and zero for every other type.
highWord :: Sing (t :: ValType) -> HostType t -> Word64
highWord SV128 (Vector128 _ high) = high
highWord _ _ = 0

{- | Read a packed word back at its type: the inverse of 'packValue'. (Of a vector it gives the
  low word alone; the frame reads both words itself.)
-}
unpackValue :: Sing (t :: ValType) -> Word64 -> HostType t
unpackValue SI32 w = fromIntegral w
unpackValue SI64 w = w
unpackValue SF32 w = castWord32ToFloat (fromIntegral w)
unpackValue SF64 w = castWord64ToDouble w
unpackValue SV128 w = Vector128 w 0
unpackValue SFuncRef w = Reference w
unpackValue SExternRef w = Reference w
unpackValue SExnRef w = Reference w

-- | The words a frame of these locals takes: one each, two for a vector.
wordsIn :: Sing (ls :: [LabelledValType]) -> Int
wordsIn SNil = 0
wordsIn (SCons (ty :%~ _) rest) = wordsOf ty + wordsIn rest

getGlobal :: Elem ('GlobalType mut (t ':~ l)) gs -> GlobalSpaceInst gs -> HostType t
getGlobal Here (GCons x _) = x
getGlobal (There ix) (GCons _ rest) = getGlobal ix rest

setGlobal :: Elem ('GlobalType mut (t ':~ l)) gs -> HostType t -> GlobalSpaceInst gs -> GlobalSpaceInst gs
setGlobal Here v (GCons _ rest) = GCons v rest
setGlobal (There ix) v (GCons x rest) = GCons x (setGlobal ix v rest)

{- | The values of the preserved globals, or 'Nothing' if the module has none (the usual case,
  and then nothing is recorded and nothing compared).
-}
recordPreserved :: PreservedOf gs -> GlobalSpaceInst gs -> Maybe (RecordedGlobals gs)
recordPreserved which globals
    | anyPreserved which = Just (record which globals)
    | otherwise = Nothing
  where
    anyPreserved :: PreservedOf gs' -> Bool
    anyPreserved NoGlobalsLeft = False
    anyPreserved (NotPreserved _ rest) = anyPreserved rest
    anyPreserved (PreservedHere _ _) = True
    record :: PreservedOf gs' -> GlobalSpaceInst gs' -> RecordedGlobals gs'
    record NoGlobalsLeft GNil = NoGlobalsLeft
    record (NotPreserved why rest) (GCons _ values) = NotPreserved why (record rest values)
    record (PreservedHere t rest) (GCons value values) = PreservedHere (Recorded t (packValue t value) (highWord t value)) (record rest values)

-- | Whether every preserved global holds the value recorded for it, bit for bit.
stillRestored :: RecordedGlobals gs -> GlobalSpaceInst gs -> Bool
stillRestored NoGlobalsLeft GNil = True
stillRestored (NotPreserved _ rest) (GCons _ values) = stillRestored rest values
stillRestored (PreservedHere (Recorded t word high) rest) (GCons value values) = packValue t value == word && highWord t value == high && stillRestored rest values

{- | A module's linear memories, indexed by their declared shapes. Being a non-empty 'MemSpaceInst'
  (@m ': ms@) is the runtime counterpart of the @ModuleMems shape ~ (m ': ms)@ constraint the
  memory instructions carry, so 'firstMem' is total — the interpreter never has to ask
  whether a memory it is already typed to use actually exists.
-}
type MemSpaceInst :: [MemShape] -> Type
data MemSpaceInst ms where
    MNil :: MemSpaceInst '[]
    MCons :: !(MemInst m) -> !(MemSpaceInst ms) -> MemSpaceInst (m ': ms)

getMem :: Elem m ms -> MemSpaceInst ms -> MemInst m
getMem Here (MCons mem _) = mem
getMem (There ix) (MCons _ rest) = getMem ix rest

setMem :: Elem m ms -> MemInst m -> MemSpaceInst ms -> MemSpaceInst ms
setMem Here mem (MCons _ rest) = MCons mem rest
setMem (There ix) mem (MCons other rest) = MCons other (setMem ix mem rest)

firstMem :: MemSpaceInst (m ': ms) -> MemInst m
firstMem (MCons mem _) = mem

setFirstMem :: MemInst m -> MemSpaceInst (m ': ms) -> MemSpaceInst (m ': ms)
setFirstMem mem (MCons _ rest) = MCons mem rest

{- | A module's tables, indexed by their declared shapes, together with what they are filled
  from and resolved against: the element segments as they stand (a dropped segment is empty;
  active and declarative segments are dropped as soon as the module is instantiated, as the
  spec prescribes), and the directory of the module's functions, which an indirect call
  resolves an entry in. They are one field of the machine's store because none of them is
  touched by ordinary code.
-}
type TableSpaceInst :: [LabelledFuncType] -> [TableShape] -> [ElemShape] -> [[LabelledValType]] -> Type
data TableSpaceInst fts ts es tags = TableSpaceInst
    { directory :: !(FunctionDirectory fts)
    , instances :: !(TableInsts ts)
    , segments :: !(ElemSpaceInst es)
    , caught :: !(IntMap (ExceptionInst tags))
    -- ^ the exceptions an @exnref@ refers to, by its index: those that a clause caught by reference
    , tagNames :: ![Word64]
    {- ^ for each tag of the module, in order, the name it has among all the instances its
    embedder links: a tag the module imports has the name of the tag it imports, so an
    exception that crosses from one module to another is of the same tag in both
    -}
    }

{- | An exception: its tag, by the name the tag has among all instances ('tagNames'), and the
  values it carries, at their types. A clause for a tag catches an exception of that name whose
  values have the tag's types, whichever module threw it; two tags of a module that import the
  same tag have one name, and are one tag.
-}
type ExceptionInst :: [[LabelledValType]] -> Type
data ExceptionInst tags where
    ExceptionInst :: !Word64 -> Sing ps -> ValueStack ps -> ExceptionInst tags

-- | The name of a tag of the module, by its witness (which is its position).
tagName :: Elem ps tags -> TableSpaceInst fts ts es tags -> Word64
tagName tag tables = at tag tables.tagNames
  where
    at :: Elem a as -> [Word64] -> Word64
    at Here (name : _) = name
    at (There rest) (_ : names) = at rest names
    at _ [] = 0

-- | Keep an exception for a reference to it, which is returned.
keepException :: ExceptionInst tags -> TableSpaceInst fts ts es tags -> (Reference, TableSpaceInst fts ts es tags)
keepException exception tables =
    let index = IntMap.size tables.caught
     in (referenceTo (fromIntegral index), tables {caught = IntMap.insert index exception tables.caught})

-- | The exception a reference refers to, or 'Nothing' for null.
keptException :: Reference -> TableSpaceInst fts ts es tags -> Maybe (ExceptionInst tags)
keptException reference tables = referent reference >>= \index -> IntMap.lookup (fromIntegral index) tables.caught

type TableInsts :: [TableShape] -> Type
data TableInsts ts where
    TNil :: TableInsts '[]
    TCons :: !TableInst -> !(TableInsts ts) -> TableInsts (t ': ts)

-- | The table space of a module with no table and no element segment.
noTables :: TableSpaceInst fts '[] '[] tags
noTables = TableSpaceInst (functionDirectory 0 []) TNil ENil IntMap.empty []

getTable :: Elem t ts -> TableSpaceInst fts ts es tags -> TableInst
getTable ix tables = go ix tables.instances
  where
    go :: Elem t ts -> TableInsts ts -> TableInst
    go Here (TCons table _) = table
    go (There rest) (TCons _ others) = go rest others

setTable :: Elem t ts -> TableInst -> TableSpaceInst fts ts es tags -> TableSpaceInst fts ts es tags
setTable ix table tables = tables {instances = go ix tables.instances}
  where
    go :: Elem t ts -> TableInsts ts -> TableInsts ts
    go Here (TCons _ others) = TCons table others
    go (There rest) (TCons other others) = TCons other (go rest others)

type ElemSpaceInst :: [ElemShape] -> Type
data ElemSpaceInst es where
    ENil :: ElemSpaceInst '[]
    ECons :: ![Reference] -> !(ElemSpaceInst es) -> ElemSpaceInst ('ElemShape t ': es)

getElements :: Elem ('ElemShape t) es -> TableSpaceInst fts ts es tags -> [Reference]
getElements ix tables = go ix tables.segments
  where
    go :: Elem e es -> ElemSpaceInst es -> [Reference]
    go Here (ECons references _) = references
    go (There rest) (ECons _ others) = go rest others

dropElements :: Elem ('ElemShape t) es -> TableSpaceInst fts ts es tags -> TableSpaceInst fts ts es tags
dropElements ix tables = tables {segments = go ix tables.segments}
  where
    go :: Elem e es -> ElemSpaceInst es -> ElemSpaceInst es
    go Here (ECons _ others) = ECons [] others
    go (There rest) (ECons references others) = ECons references (go rest others)

{- | A module's data segments as they stand at run time, one slot per segment of the data index
  space: the bytes still available to @memory.init@, or nothing once dropped (active segments
  are dropped as soon as instantiation has copied them, as the spec prescribes).
-}
type DataSpaceInst :: [DataShape] -> Type
data DataSpaceInst ds where
    DNil :: DataSpaceInst '[]
    DCons :: !(Maybe ByteString) -> !(DataSpaceInst ds) -> DataSpaceInst ('DataShape ': ds)

getSegment :: Elem 'DataShape ds -> DataSpaceInst ds -> Maybe ByteString
getSegment Here (DCons segment _) = segment
getSegment (There ix) (DCons _ rest) = getSegment ix rest

dropSegment :: Elem 'DataShape ds -> DataSpaceInst ds -> DataSpaceInst ds
dropSegment Here (DCons _ rest) = DCons Nothing rest
dropSegment (There ix) (DCons segment rest) = DCons segment (dropSegment ix rest)
