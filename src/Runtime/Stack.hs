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
    LocalInsts (..),
    GlobalInsts (..),
    MemInsts (..),
    TableInsts (..),
    firstTable,
    appendStack,
    appendWith,
    splitStack,
    reverseOnto,
    getLocal,
    setLocal,
    getGlobal,
    setGlobal,
    firstMem,
    setFirstMem,
) where

import Data.Kind (Type)

import Data.List.Singletons (type (++))
import Runtime.MemInst (MemInst)
import Runtime.TableInst (TableInst)
import Syntax.Immediates (HostType)
import Syntax.Types (FuncType, GlobalType (..), ValType)
import Validation.Shape (Append (..), Elem (..), MemShape, ReverseOnto, TableShape)

-- | The operand stack (head = top of stack), indexed by the types it holds.
type ValueStack :: [ValType] -> Type
data ValueStack s where
    VNil :: ValueStack '[]
    (:#) :: HostType t -> ValueStack ts -> ValueStack (t ': ts)

infixr 5 :#

{- | A function activation's local variable instances, indexed by their types. (The @Inst@
  suffix marks the runtime values; the static description is just the type index.)
-}
type LocalInsts :: [ValType] -> Type
data LocalInsts ls where
    LNil :: LocalInsts '[]
    (:&) :: HostType t -> LocalInsts ls -> LocalInsts (t ': ls)

infixr 5 :&

-- | A module's global variable instances, indexed by their declared global types.
type GlobalInsts :: [GlobalType] -> Type
data GlobalInsts gs where
    GNil :: GlobalInsts '[]
    GCons :: HostType t -> GlobalInsts gs -> GlobalInsts ('GlobalType mut t ': gs)

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
reverseOnto :: ValueStack xs -> LocalInsts acc -> LocalInsts (ReverseOnto xs acc)
reverseOnto VNil acc = acc
-- The slot's type @t@ is bound explicitly: 'HostType' is not injective, so it cannot be
-- recovered from the value @x@ alone when it is pushed onto the locals.
reverseOnto ((:#) @t x xs) acc = reverseOnto xs ((:&) @t x acc)

getLocal :: Elem t ls -> LocalInsts ls -> HostType t
getLocal Here (x :& _) = x
getLocal (There ix) (_ :& rest) = getLocal ix rest

setLocal :: Elem t ls -> HostType t -> LocalInsts ls -> LocalInsts ls
setLocal Here v (_ :& rest) = v :& rest
setLocal (There ix) v (x :& rest) = x :& setLocal ix v rest

getGlobal :: Elem ('GlobalType mut t) gs -> GlobalInsts gs -> HostType t
getGlobal Here (GCons x _) = x
getGlobal (There ix) (GCons _ rest) = getGlobal ix rest

setGlobal :: Elem ('GlobalType mut t) gs -> HostType t -> GlobalInsts gs -> GlobalInsts gs
setGlobal Here v (GCons _ rest) = GCons v rest
setGlobal (There ix) v (GCons x rest) = GCons x (setGlobal ix v rest)

{- | A module's linear memories, indexed by their declared shapes. Being a non-empty 'MemInsts'
  (@m ': ms@) is the runtime counterpart of the @ModuleMems shape ~ (m ': ms)@ constraint the
  memory instructions carry, so 'firstMem' is total — the interpreter never has to ask
  whether a memory it is already typed to use actually exists.
-}
type MemInsts :: [MemShape] -> Type
data MemInsts ms where
    MNil :: MemInsts '[]
    MCons :: MemInst m -> MemInsts ms -> MemInsts (m ': ms)

firstMem :: MemInsts (m ': ms) -> MemInst m
firstMem (MCons mem _) = mem

setFirstMem :: MemInst m -> MemInsts (m ': ms) -> MemInsts (m ': ms)
setFirstMem mem (MCons _ rest) = MCons mem rest

{- | A module's tables, indexed by their declared shapes and by the module's function types
  (which every entry is a reference into). Non-emptiness is the runtime counterpart of the
  @ModuleTables shape ~ (t ': ts)@ constraint @call_indirect@ carries, so 'firstTable' is total.
-}
type TableInsts :: [FuncType] -> [TableShape] -> Type
data TableInsts fts ts where
    TNil :: TableInsts fts '[]
    TCons :: TableInst fts -> TableInsts fts ts -> TableInsts fts (t ': ts)

firstTable :: TableInsts fts (t ': ts) -> TableInst fts
firstTable (TCons table _) = table
