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
  holds. A value-stack or global slot of type @t@ stores a bare @HostType t@ — there is no
  per-value tag, because the index already says how to read it. Locals are stored flat
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
    initialGlobals,
    MemSpaceInst (..),
    TableSpaceInst (..),
    firstTable,
    DataSpaceInst (..),
    getSegment,
    dropSegment,
    appendStack,
    appendWith,
    splitStack,
    seedLocals,
    defaultLocals,
    getLocal,
    setLocal,
    getGlobal,
    setGlobal,
    firstMem,
    setFirstMem,
) where

import Control.Monad.ST (ST)
import Data.ByteString (ByteString)
import Data.Kind (Type)
import Data.Vector.Unboxed qualified as UV
import Data.Vector.Unboxed.Mutable qualified as MV
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64, castFloatToWord32, castWord32ToFloat, castWord64ToDouble)

import Data.List.Singletons (type (++))
import Data.Singletons.Base.TH (SList (SCons, SNil), Sing)
import Runtime.MemInst (MemInst)
import Runtime.TableInst (TableInst)
import Syntax.Globals (Global (..), GlobalSpace (..))
import Syntax.Immediates (HostType)
import Syntax.Types
import Validation.Ref (LocalRef, localPosition, localType)
import Validation.Shape (Append (..), DataShape (..), Elem (..), MemShape, ReverseOnto, TableShape)

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
type ValueStack :: [ValType] -> Type
data ValueStack s where
    VNil :: ValueStack '[]
    (:#) :: !(HostType t) -> !(ValueStack ts) -> ValueStack (t ': ts)

infixr 5 :#

{- | The instance of a function activation's local index space: its locals' current values,
  indexed by their types.

  Stored flat, one machine word per local in an unboxed vector, and reached through a
  'Validation.Ref.LocalRef' that elaboration resolved from the local's witness: its position,
  and its type, which says how to read the word back. Every WebAssembly value fits in 64 bits,
  so the word /is/ the value, bit for bit (a float's NaN payload survives the round trip). A
  cons list indexed by the witness itself, the obvious typed encoding, makes every access walk
  to its local and every @local.set@ rebuild the cells in front of it (TODO.md §I, E2, E2b).

  The type is abstract, with one invariant: the vector holds exactly as many words as @ls@ has
  types. 'defaultLocals' and 'seedLocals' establish it and 'setLocal' preserves it, being the
  only ways to make or change a frame; and a reference's position is below that length because
  its witness proves the local exists. The two together license the unchecked read and write.
-}
type LocalSpaceInst :: [ValType] -> Type
newtype LocalSpaceInst ls = LocalSpaceInst (UV.Vector Word64)

-- | The instance of a module's global index space: the globals' current values, by type.
type GlobalSpaceInst :: [GlobalType] -> Type
data GlobalSpaceInst gs where
    GNil :: GlobalSpaceInst '[]
    GCons :: !(HostType t) -> !(GlobalSpaceInst gs) -> GlobalSpaceInst ('GlobalType mut t ': gs)

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
seedLocals :: Sing ps -> Sing declared -> ValueStack ps -> LocalSpaceInst (ReverseOnto ps declared)
seedLocals paramTypes declaredTypes args =
    LocalSpaceInst (UV.create frame)
  where
    arity = lengthOf paramTypes
    frame :: ST s (MV.MVector s Word64)
    frame = do
        slots <- MV.replicate (arity + lengthOf declaredTypes) 0
        writeArguments slots (arity - 1) paramTypes args
        pure slots

{- | Write a stack's values into consecutive slots, the top one at @slot@ and each deeper one
  just below it.
-}
writeArguments :: MV.MVector s Word64 -> Int -> Sing (xs :: [ValType]) -> ValueStack xs -> ST s ()
writeArguments _ _ SNil VNil = pure ()
writeArguments slots slot (SCons st rest) (x :# xs) = do
    MV.unsafeWrite slots slot (packValue st x)
    writeArguments slots (slot - 1) rest xs

{- | A locals frame of the given shape, every slot zero (how declared locals start a call).
  Zero is the all-zero word at every value type, the floats' @+0.0@ included.
-}
defaultLocals :: Sing (ls :: [ValType]) -> LocalSpaceInst ls
defaultLocals types = LocalSpaceInst (UV.replicate (lengthOf types) 0)

-- | The frame of a function with neither parameters nor declared locals.
noLocals :: LocalSpaceInst '[]
noLocals = defaultLocals SNil

-- | Read a local: its reference says where it is and how to read the word found there.
getLocal :: LocalRef t ls -> LocalSpaceInst ls -> HostType t
getLocal ref (LocalSpaceInst values) = unpackValue (localType ref) (UV.unsafeIndex values (localPosition ref))

-- | Write a local: a copy of the frame with one word replaced, so of the same length.
setLocal :: LocalRef t ls -> HostType t -> LocalSpaceInst ls -> LocalSpaceInst ls
setLocal ref v (LocalSpaceInst values) =
    LocalSpaceInst (UV.modify (\slots -> MV.unsafeWrite slots (localPosition ref) (packValue (localType ref) v)) values)

-- | Pack a value into the one machine word every WebAssembly value fits in, bit for bit.
packValue :: Sing (t :: ValType) -> HostType t -> Word64
packValue SI32 v = fromIntegral v
packValue SI64 v = v
packValue SF32 v = fromIntegral (castFloatToWord32 v)
packValue SF64 v = castDoubleToWord64 v

-- | Read a packed word back at its type: the inverse of 'packValue'.
unpackValue :: Sing (t :: ValType) -> Word64 -> HostType t
unpackValue SI32 w = fromIntegral w
unpackValue SI64 w = w
unpackValue SF32 w = castWord32ToFloat (fromIntegral w)
unpackValue SF64 w = castWord64ToDouble w

lengthOf :: Sing (ls :: [ValType]) -> Int
lengthOf SNil = 0
lengthOf (SCons _ rest) = 1 + lengthOf rest

-- | The globals as a module starts: each at its validated initial value.
initialGlobals :: GlobalSpace gs -> GlobalSpaceInst gs
initialGlobals NoGlobals = GNil
initialGlobals (Declared (Global value) rest) = GCons value (initialGlobals rest)

getGlobal :: Elem ('GlobalType mut t) gs -> GlobalSpaceInst gs -> HostType t
getGlobal Here (GCons x _) = x
getGlobal (There ix) (GCons _ rest) = getGlobal ix rest

setGlobal :: Elem ('GlobalType mut t) gs -> HostType t -> GlobalSpaceInst gs -> GlobalSpaceInst gs
setGlobal Here v (GCons _ rest) = GCons v rest
setGlobal (There ix) v (GCons x rest) = GCons x (setGlobal ix v rest)

{- | A module's linear memories, indexed by their declared shapes. Being a non-empty 'MemSpaceInst'
  (@m ': ms@) is the runtime counterpart of the @ModuleMems shape ~ (m ': ms)@ constraint the
  memory instructions carry, so 'firstMem' is total — the interpreter never has to ask
  whether a memory it is already typed to use actually exists.
-}
type MemSpaceInst :: [MemShape] -> Type
data MemSpaceInst ms where
    MNil :: MemSpaceInst '[]
    MCons :: !(MemInst m) -> !(MemSpaceInst ms) -> MemSpaceInst (m ': ms)

firstMem :: MemSpaceInst (m ': ms) -> MemInst m
firstMem (MCons mem _) = mem

setFirstMem :: MemInst m -> MemSpaceInst (m ': ms) -> MemSpaceInst (m ': ms)
setFirstMem mem (MCons _ rest) = MCons mem rest

{- | A module's tables, indexed by their declared shapes and by the module's function types
  (which every entry is a reference into). Non-emptiness is the runtime counterpart of the
  @ModuleTables shape ~ (t ': ts)@ constraint @call_indirect@ carries, so 'firstTable' is total.
-}
type TableSpaceInst :: [FuncType] -> [TableShape] -> Type
data TableSpaceInst fts ts where
    TNil :: TableSpaceInst fts '[]
    TCons :: !(TableInst fts) -> !(TableSpaceInst fts ts) -> TableSpaceInst fts (t ': ts)

firstTable :: TableSpaceInst fts (t ': ts) -> TableInst fts
firstTable (TCons table _) = table

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
