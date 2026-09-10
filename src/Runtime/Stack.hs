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
  holds. A slot of type @t@ stores a bare @HostType t@ — there is no per-value
  tag, because the index already says how to read it.

  Splitting a concatenated stack @c = a ++ b@ back into its parts is driven by an
  'Append' witness, not by inverting the (non-injective) @++@ family. The witness's
  three indices are independent, so @splitStack@ never asks GHC to invert anything.
-}
module Runtime.Stack (
    ValueStack (..),
    LocalSpaceInst (..),
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
    reverseOnto,
    defaultLocals,
    getLocal,
    setLocal,
    getGlobal,
    setGlobal,
    firstMem,
    setFirstMem,
) where

import Data.ByteString (ByteString)
import Data.Kind (Type)

import Data.List.Singletons (type (++))
import Data.Singletons.Base.TH (SList (SCons, SNil), Sing)
import Runtime.MemInst (MemInst)
import Runtime.TableInst (TableInst)
import Syntax.Globals (Global (..), GlobalSpace (..))
import Syntax.Immediates (HostType)
import Syntax.Types
import Validation.Shape (Append (..), DataShape (..), Elem (..), MemShape, ReverseOnto, TableShape)

-- | The operand stack (head = top of stack), indexed by the types it holds.
type ValueStack :: [ValType] -> Type
data ValueStack s where
    VNil :: ValueStack '[]
    (:#) :: HostType t -> ValueStack ts -> ValueStack (t ': ts)

infixr 5 :#

{- | The instance of a function activation's local index space: its locals' current values,
  indexed by their types. (As for every @…SpaceInst@, the static description is the type
  index itself; the name says which index space the vector instantiates.)
-}
type LocalSpaceInst :: [ValType] -> Type
data LocalSpaceInst ls where
    LNil :: LocalSpaceInst '[]
    (:&) :: HostType t -> LocalSpaceInst ls -> LocalSpaceInst (t ': ls)

infixr 5 :&

-- | The instance of a module's global index space: the globals' current values, by type.
type GlobalSpaceInst :: [GlobalType] -> Type
data GlobalSpaceInst gs where
    GNil :: GlobalSpaceInst '[]
    GCons :: HostType t -> GlobalSpaceInst gs -> GlobalSpaceInst ('GlobalType mut t ': gs)

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

{- | Seed a callee's locals from its argument segment: the arguments go in front of @acc@ (the
  zero-initialised declared locals), reversed on the way, because the segment lists the last
  argument first (top of stack) while local 0 is the first parameter. Structural, mirroring
  'ReverseOnto'.
-}
reverseOnto :: ValueStack xs -> LocalSpaceInst acc -> LocalSpaceInst (ReverseOnto xs acc)
reverseOnto VNil acc = acc
-- The slot's type @t@ is bound explicitly: 'HostType' is not injective, so it cannot be
-- recovered from the value @x@ alone when it is pushed onto the locals.
reverseOnto ((:#) @t x xs) acc = reverseOnto xs ((:&) @t x acc)

-- | A locals frame of the given shape, every slot zero (how declared locals start a call).
defaultLocals :: Sing (ls :: [ValType]) -> LocalSpaceInst ls
defaultLocals SNil = LNil
defaultLocals (SCons st rest) = zeroOf st :& defaultLocals rest
  where
    zeroOf :: Sing (t :: ValType) -> HostType t
    zeroOf SI32 = 0
    zeroOf SI64 = 0
    zeroOf SF32 = 0
    zeroOf SF64 = 0

getLocal :: Elem t ls -> LocalSpaceInst ls -> HostType t
getLocal Here (x :& _) = x
getLocal (There ix) (_ :& rest) = getLocal ix rest

setLocal :: Elem t ls -> HostType t -> LocalSpaceInst ls -> LocalSpaceInst ls
setLocal Here v (_ :& rest) = v :& rest
setLocal (There ix) v (x :& rest) = x :& setLocal ix v rest

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
    MCons :: MemInst m -> MemSpaceInst ms -> MemSpaceInst (m ': ms)

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
    TCons :: TableInst fts -> TableSpaceInst fts ts -> TableSpaceInst fts (t ': ts)

firstTable :: TableSpaceInst fts (t ': ts) -> TableInst fts
firstTable (TCons table _) = table

{- | A module's data segments as they stand at run time, one slot per segment of the data index
  space: the bytes still available to @memory.init@, or nothing once dropped (active segments
  are dropped as soon as instantiation has copied them, as the spec prescribes).
-}
type DataSpaceInst :: [DataShape] -> Type
data DataSpaceInst ds where
    DNil :: DataSpaceInst '[]
    DCons :: Maybe ByteString -> DataSpaceInst ds -> DataSpaceInst ('DataShape ': ds)

getSegment :: Elem 'DataShape ds -> DataSpaceInst ds -> Maybe ByteString
getSegment Here (DCons segment _) = segment
getSegment (There ix) (DCons _ rest) = getSegment ix rest

dropSegment :: Elem 'DataShape ds -> DataSpaceInst ds -> DataSpaceInst ds
dropSegment Here (DCons _ rest) = DCons Nothing rest
dropSegment (There ix) (DCons segment rest) = DCons segment (dropSegment ix rest)
