{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
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

    -- * A frame's words, for the benchmarks' erased copy of the machine
    Frame,
    zeroFrame,
    frameSlot,
    withFrameSlot,
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

import Control.Monad.ST (runST)
import Data.Bits (shiftL, shiftR, (.&.))
import Data.ByteString (ByteString)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Kind (Type)
import Data.Word (Word64)
import GHC.Exts (ByteArray#, Int (I#), SmallArray#, andI#, copyByteArray#, indexSmallArray#, indexWord64Array#, newByteArray#, newSmallArray#, setByteArray#, thawSmallArray#, uncheckedIShiftRL#, unsafeFreezeByteArray#, unsafeFreezeSmallArray#, writeSmallArray#, writeWord64Array#)
import GHC.Float (castDoubleToWord64, castFloatToWord32, castWord32ToFloat, castWord64ToDouble)
import GHC.ST (ST (ST))
import GHC.Word (Word64 (W64#))

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

  Stored as machine words, one per local and two for a 128-bit vector, and reached through a
  'Validation.Ref.LocalRef' that elaboration resolved from the local's witness: its place, and
  its type, which says how to read the words back. Every other WebAssembly value fits in 64
  bits, so the word /is/ the value, bit for bit (a float's NaN payload survives the round
  trip). A cons list indexed by the witness itself, the obvious typed encoding, makes every
  access walk to its local and every @local.set@ rebuild the cells in front of it (TODO.md §I,
  E2, E2b).

  The words are kept eight to a group ('Frame'), and a write copies the group it writes into
  and nothing else. Kept in one vector, the whole frame was copied by every @local.set@ and
  @local.tee@, which was most of the 220 machine instructions that either cost.

  The type is abstract, with one invariant: the frame has room for the words the types of
  @ls@ take ('wordsIn'). 'defaultLocals' and 'seedLocals' establish it and 'setLocal' preserves
  it, being the only ways to make or change a frame; and a reference's place, with the words
  of its type, is below that number because its witness proves the local exists and
  'Validation.Ref.resolveLocal' counts the words before it the same way.
-}
type LocalSpaceInst :: [LabelledValType] -> Type
newtype LocalSpaceInst ls = LocalSpaceInst Frame

{- | Eight words of a frame, in 64 bytes. The size is a constant, so GHC allocates a group
  where it is made, by moving the heap pointer, and copies one with eight moves; an array of
  a size known only at run time is allocated and copied by calls into the runtime system.

  The primitive reads and writes below check no index. They take the low three bits of the
  place they are given, so they stay inside the 64 bytes whatever the place is.
-}
data Slots = Slots ByteArray#

-- | Eight words of zero: how every local that is not a parameter starts, and shared by all frames.
{-# NOINLINE zeroSlots #-}
zeroSlots :: Slots
zeroSlots =
    runST
        ( ST
            ( \s0 -> case newByteArray# 64# s0 of
                (# s1, new #) -> case setByteArray# new 0# 64# 0# s1 of
                    s2 -> case unsafeFreezeByteArray# new s2 of
                        (# s3, frozen #) -> (# s3, Slots frozen #)
            )
        )

-- | The word at a place, which is counted within the frame: its low three bits say which of the eight.
{-# INLINE slotAt #-}
slotAt :: Slots -> Int -> Word64
slotAt (Slots held) (I# place) = W64# (indexWord64Array# held (place `andI#` 7#))

-- | A copy of the eight words with one replaced.
{-# INLINE withSlotAt #-}
withSlotAt :: Int -> Word64 -> Slots -> Slots
withSlotAt (I# place) (W64# word) (Slots old) =
    runST
        ( ST
            ( \s0 -> case newByteArray# 64# s0 of
                (# s1, new #) -> case copyByteArray# old 0# new 0# 64# s1 of
                    s2 -> case writeWord64Array# new (place `andI#` 7#) word s2 of
                        s3 -> case unsafeFreezeByteArray# new s3 of
                            (# s4, frozen #) -> (# s4, Slots frozen #)
            )
        )

{- | The words of a frame, in groups of eight. A frame of at most 8 words is one group, and
  one of at most 64 is an array of eight groups: a read finds its group by an index, and a
  write copies that group and the eight pointers. A larger frame is eight frames of an eighth
  of its size, and so on: a write copies one group and eight pointers for each level. The
  parts that were never written are one shared group of zeros.
-}
data Frame
    = OneGroup {-# UNPACK #-} !Slots
    | -- | an array of exactly eight groups
      EightGroups (SmallArray# ByteArray#)
    | -- | eight frames of @2 ^ shift@ words each
      EightFrames !Int !Frame !Frame !Frame !Frame !Frame !Frame !Frame !Frame

-- | A frame of so many words, all zero.
zeroFrame :: Int -> Frame
zeroFrame size
    | size <= 8 = OneGroup zeroSlots
    | otherwise = eightOf 3 (OneGroup zeroSlots)
  where
    -- Eight of a part that has @2 ^ shift@ words, and eight of that, until the size is reached.
    eightOf :: Int -> Frame -> Frame
    eightOf shift part
        | size <= 8 `shiftL` shift = whole
        | otherwise = eightOf (shift + 3) whole
      where
        whole = case part of
            OneGroup _ -> eightZeroGroups
            _ -> EightFrames shift part part part part part part part part

-- | Eight groups of zeros, which are one group eight times.
{-# NOINLINE eightZeroGroups #-}
eightZeroGroups :: Frame
eightZeroGroups = case zeroSlots of
    Slots zeros ->
        runST
            ( ST
                ( \s0 -> case newSmallArray# 8# zeros s0 of
                    (# s1, new #) -> case unsafeFreezeSmallArray# new s1 of
                        (# s2, frozen #) -> (# s2, EightGroups frozen #)
                )
            )

{- | The group of a place among eight. As in a group, the index is three bits of the place (the
  next three), so it is inside the array of eight whatever the place is.
-}
{-# INLINE groupAt #-}
groupAt :: SmallArray# ByteArray# -> Int -> Slots
groupAt groups (I# place) = case indexSmallArray# groups ((place `uncheckedIShiftRL#` 3#) `andI#` 7#) of
    (# group #) -> Slots group

-- | A copy of the eight groups with the one of a place replaced.
{-# INLINE withGroupAt #-}
withGroupAt :: Int -> Slots -> SmallArray# ByteArray# -> Frame
withGroupAt (I# place) (Slots group) groups =
    runST
        ( ST
            ( \s0 -> case thawSmallArray# groups 0# 8# s0 of
                (# s1, new #) -> case writeSmallArray# new ((place `uncheckedIShiftRL#` 3#) `andI#` 7#) group s1 of
                    s2 -> case unsafeFreezeSmallArray# new s2 of
                        (# s3, frozen #) -> (# s3, EightGroups frozen #)
            )
        )

-- | The word at a place of a frame that has it.
{-# INLINE frameSlot #-}
frameSlot :: Frame -> Int -> Word64
frameSlot frame place = case frame of
    OneGroup only -> slotAt only place
    EightGroups groups -> slotAt (groupAt groups place) place
    EightFrames {} -> slotOfLargeFrame frame place

-- | 'frameSlot' for a frame of more than 64 words.
slotOfLargeFrame :: Frame -> Int -> Word64
slotOfLargeFrame frame place = case frame of
    EightFrames shift f0 f1 f2 f3 f4 f5 f6 f7 -> case (place `shiftR` shift) .&. 7 of
        0 -> slotOfLargeFrame f0 place
        1 -> slotOfLargeFrame f1 place
        2 -> slotOfLargeFrame f2 place
        3 -> slotOfLargeFrame f3 place
        4 -> slotOfLargeFrame f4 place
        5 -> slotOfLargeFrame f5 place
        6 -> slotOfLargeFrame f6 place
        _ -> slotOfLargeFrame f7 place
    _ -> frameSlot frame place

-- | A frame with the word at one of its places replaced.
withFrameSlot :: Int -> Word64 -> Frame -> Frame
withFrameSlot !place !word !frame = case frame of
    OneGroup only -> OneGroup (withSlotAt place word only)
    EightGroups groups -> withGroupAt place (withSlotAt place word (groupAt groups place)) groups
    EightFrames shift f0 f1 f2 f3 f4 f5 f6 f7 -> case (place `shiftR` shift) .&. 7 of
        0 -> EightFrames shift (withFrameSlot place word f0) f1 f2 f3 f4 f5 f6 f7
        1 -> EightFrames shift f0 (withFrameSlot place word f1) f2 f3 f4 f5 f6 f7
        2 -> EightFrames shift f0 f1 (withFrameSlot place word f2) f3 f4 f5 f6 f7
        3 -> EightFrames shift f0 f1 f2 (withFrameSlot place word f3) f4 f5 f6 f7
        4 -> EightFrames shift f0 f1 f2 f3 (withFrameSlot place word f4) f5 f6 f7
        5 -> EightFrames shift f0 f1 f2 f3 f4 (withFrameSlot place word f5) f6 f7
        6 -> EightFrames shift f0 f1 f2 f3 f4 f5 (withFrameSlot place word f6) f7
        _ -> EightFrames shift f0 f1 f2 f3 f4 f5 f6 (withFrameSlot place word f7)

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

{- | Concatenate two stacks; the upper one ends up on top. Purely structural.
The stack with nothing to put on it is found where the append is asked for, without a
call: that is the end of every block that has no result.
-}
{-# INLINE appendStack #-}
appendStack :: ValueStack a -> ValueStack b -> ValueStack (a ++ b)
appendStack VNil ys = ys
appendStack (x :# xs) ys = x :# appendValues xs ys

appendValues :: ValueStack a -> ValueStack b -> ValueStack (a ++ b)
appendValues VNil ys = ys
appendValues (x :# xs) ys = x :# appendValues xs ys

-- | Concatenate two stacks, guided by an 'Append' witness (so the result type is the witness's).
appendWith :: Append a b c -> ValueStack a -> ValueStack b -> ValueStack c
appendWith ANil VNil ys = ys
appendWith (ACons w) (x :# xs) ys = x :# appendWith w xs ys

{- | Split a concatenated stack into its parts, guided by an 'Append' witness.
As for 'appendStack': a split that takes nothing off, which is the entry of every block
without parameters, costs no call and no pair.
-}
{-# INLINE splitStack #-}
splitStack :: Append a b c -> ValueStack c -> (ValueStack a, ValueStack b)
splitStack ANil vs = (VNil, vs)
splitStack (ACons w) (x :# vs) = case splitValues w vs of (upper, lower) -> (x :# upper, lower)

splitValues :: Append a b c -> ValueStack c -> (ValueStack a, ValueStack b)
splitValues ANil vs = (VNil, vs)
splitValues (ACons w) (x :# vs) = case splitValues w vs of (upper, lower) -> (x :# upper, lower)

{- | Seed a callee's locals from its argument segment: the parameters, then the declared locals
  at zero. The segment lists the last argument first (top of stack) while local 0 is the first
  parameter, so the arguments are written from the last slot of the parameters downwards —
  which is 'ReverseOnto', done in place. One allocation per call: calls are the hottest path
  there is, and building the frame through intermediate lists cost @fib@ a third more heap.
-}
seedLocals :: SegmentFlows args ps -> Sing ps -> Sing declared -> ValueStack args -> LocalSpaceInst (ReverseOnto ps declared)
seedLocals flows paramTypes declaredTypes args =
    LocalSpaceInst (withArguments arity flows paramTypes args (zeroFrame (arity + wordsIn declaredTypes)))
  where
    arity = wordsIn paramTypes

{- | A frame with a stack's values written into consecutive places, the top one ending just
  below @end@ and each deeper one just below it; a vector takes two places, its low word first.
  The arguments arrive at the levels the caller had ('SegmentFlows' says they may flow into the
  parameters'); a level is nothing at run time, so the words go in as they are.
-}
withArguments :: Int -> SegmentFlows args ps -> Sing (ps :: [LabelledValType]) -> ValueStack args -> Frame -> Frame
withArguments _ NoValuesFlow SNil VNil frame = frame
withArguments _ SegmentAsItIs SNil VNil frame = frame
withArguments end flows@(ValueFlows _ _) types@(SCons _ _) stack@(_ :# _) frame = withArgument end (flowsOfRest flows) types stack frame
withArguments end SegmentAsItIs types@(SCons _ _) stack@(_ :# _) frame = withArgument end SegmentAsItIs types stack frame

-- | 'withArguments' for a segment that has a first value: that value, then the rest.
withArgument :: Int -> SegmentFlows args ps -> Sing ((t ':~ lp) ': ps) -> ValueStack ((t ':~ la) ': args) -> Frame -> Frame
withArgument end flows (SCons (st :%~ _) rest) (x :# xs) !frame = case st of
    SV128 -> case x of
        Vector128 low high -> withArguments (end - 2) flows rest xs (withFrameSlot (end - 1) high (withFrameSlot (end - 2) low frame))
    _ -> withArguments (end - 1) flows rest xs (withFrameSlot (end - 1) (packValue st x) frame)

{- | A locals frame of the given shape, every slot zero (how declared locals start a call).
  Zero is the all-zero word at every value type, the floats' @+0.0@ included.
-}
defaultLocals :: Sing (ls :: [LabelledValType]) -> LocalSpaceInst ls
defaultLocals types = LocalSpaceInst (zeroFrame (wordsIn types))

-- | The frame of a function with neither parameters nor declared locals.
noLocals :: LocalSpaceInst '[]
noLocals = defaultLocals SNil

-- | Read a local: its reference says where it is and how to read the word (or two) found there.
{-# INLINE getLocal #-}
getLocal :: LocalRef (t ':~ l) ls -> LocalSpaceInst ls -> HostType t
getLocal ref (LocalSpaceInst frame) = case localType ref of
    SV128 -> Vector128 (frameSlot frame at) (frameSlot frame (at + 1))
    ty -> unpackValue ty (frameSlot frame at)
  where
    at = localPosition ref

-- | Write a local: the frame with its word (or two) replaced.
setLocal :: LocalRef (t ':~ l) ls -> HostType t -> LocalSpaceInst ls -> LocalSpaceInst ls
setLocal ref v (LocalSpaceInst frame) = case localType ref of
    SV128 -> case v of
        Vector128 low high -> LocalSpaceInst (withFrameSlot (at + 1) high (withFrameSlot at low frame))
    ty -> LocalSpaceInst (withFrameSlot at (packValue ty v) frame)
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

-- The first memory, which is the one almost every load and store names, is found where it is
-- asked for, without a call.
{-# INLINE getMem #-}
getMem :: Elem m ms -> MemSpaceInst ms -> MemInst m
getMem Here (MCons mem _) = mem
getMem (There ix) (MCons _ rest) = getLaterMem ix rest

getLaterMem :: Elem m ms -> MemSpaceInst ms -> MemInst m
getLaterMem Here (MCons mem _) = mem
getLaterMem (There ix) (MCons _ rest) = getLaterMem ix rest

{-# INLINE setMem #-}
setMem :: Elem m ms -> MemInst m -> MemSpaceInst ms -> MemSpaceInst ms
setMem Here mem (MCons _ rest) = MCons mem rest
setMem (There ix) mem (MCons other rest) = MCons other (setLaterMem ix mem rest)

setLaterMem :: Elem m ms -> MemInst m -> MemSpaceInst ms -> MemSpaceInst ms
setLaterMem Here mem (MCons _ rest) = MCons mem rest
setLaterMem (There ix) mem (MCons other rest) = MCons other (setLaterMem ix mem rest)

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
