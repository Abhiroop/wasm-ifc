{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Type-indexed runtime structures for the intrinsically-typed interpreter: the value
--   stack, locals, and globals, each indexed by the (type-level) list of value types it
--   holds. A slot of type @t@ stores a bare @RuntimeHostType t@ — there is no per-value
--   tag, because the index already says how to read it.
--
--   Splitting a concatenated stack @c = a ++ b@ back into its parts is driven by an
--   'Append' witness, not by inverting the (non-injective) @++@ family. The witness's
--   three indices are independent, so @splitStack@ never asks GHC to invert anything.
module Runtime.Stack
    ( ValueStack (..)
    , LocalInsts (..)
    , GlobalInsts (..)
    , MemInsts (..)
    , appendStack
    , splitStack
    , stackToLocals
    , appendLocals
    , getLocal
    , setLocal
    , getGlobal
    , setGlobal
    , firstMem
    , setFirstMem
    ) where

import Data.Kind (Type)

import Runtime.MemInst  (MemInst)
import Runtime.Values (RuntimeHostType)
import Syntax.Types   (GlobalType (..), ValType)
import Validation.Shape  (Append (..), Elem (..), MemShape, type (++))

-- | The operand stack (head = top of stack), indexed by the types it holds.
type ValueStack :: [ValType] -> Type
data ValueStack s where
    VNil :: ValueStack '[]
    (:#) :: RuntimeHostType t -> ValueStack ts -> ValueStack (t ': ts)

infixr 5 :#

-- | A function activation's local variable instances, indexed by their types. (The @Inst@
--   suffix marks the runtime values; the static description is just the type index.)
type LocalInsts :: [ValType] -> Type
data LocalInsts ls where
    LNil :: LocalInsts '[]
    (:&) :: RuntimeHostType t -> LocalInsts ls -> LocalInsts (t ': ls)

infixr 5 :&

-- | A module's global variable instances, indexed by their declared global types.
type GlobalInsts :: [GlobalType] -> Type
data GlobalInsts gs where
    GNil  :: GlobalInsts '[]
    GCons :: RuntimeHostType t -> GlobalInsts gs -> GlobalInsts ('GlobalType mut t ': gs)

-- | Concatenate two stacks; the upper one ends up on top. Purely structural.
appendStack :: ValueStack a -> ValueStack b -> ValueStack (a ++ b)
appendStack VNil      ys = ys
appendStack (x :# xs) ys = x :# appendStack xs ys

-- | Split a concatenated stack into its parts, guided by an 'Append' witness.
splitStack :: Append a b c -> ValueStack c -> (ValueStack a, ValueStack b)
splitStack ANil       vs        = (VNil, vs)
splitStack (ACons w)  (x :# vs) = let (upper, lower) = splitStack w vs in (x :# upper, lower)

-- | Reinterpret a value stack as locals (used to seed a callee's parameters).
stackToLocals :: ValueStack s -> LocalInsts s
stackToLocals VNil      = LNil
stackToLocals (x :# xs) = x :& stackToLocals xs

-- | Append two locals frames (parameters followed by declared locals).
appendLocals :: LocalInsts a -> LocalInsts b -> LocalInsts (a ++ b)
appendLocals LNil      ys = ys
appendLocals (x :& xs) ys = x :& appendLocals xs ys

getLocal :: Elem t ls -> LocalInsts ls -> RuntimeHostType t
getLocal Here       (x :& _)    = x
getLocal (There ix) (_ :& rest) = getLocal ix rest

setLocal :: Elem t ls -> RuntimeHostType t -> LocalInsts ls -> LocalInsts ls
setLocal Here       v (_ :& rest) = v :& rest
setLocal (There ix) v (x :& rest) = x :& setLocal ix v rest

getGlobal :: Elem ('GlobalType mut t) gs -> GlobalInsts gs -> RuntimeHostType t
getGlobal Here       (GCons x _)    = x
getGlobal (There ix) (GCons _ rest) = getGlobal ix rest

setGlobal :: Elem ('GlobalType mut t) gs -> RuntimeHostType t -> GlobalInsts gs -> GlobalInsts gs
setGlobal Here       v (GCons _ rest) = GCons v rest
setGlobal (There ix) v (GCons x rest) = GCons x (setGlobal ix v rest)

-- | A module's linear memories, indexed by their declared shapes. Being a non-empty 'MemInsts'
--   (@m ': ms@) is the runtime counterpart of the @ModuleMems shape ~ (m ': ms)@ constraint the
--   memory instructions carry, so 'firstMem' is total — the interpreter never has to ask
--   whether a memory it is already typed to use actually exists.
type MemInsts :: [MemShape] -> Type
data MemInsts ms where
    MNil  :: MemInsts '[]
    MCons :: MemInst m -> MemInsts ms -> MemInsts (m ': ms)

firstMem :: MemInsts (m ': ms) -> MemInst m
firstMem (MCons mem _) = mem

setFirstMem :: MemInst m -> MemInsts (m ': ms) -> MemInsts (m ': ms)
setFirstMem mem (MCons _ rest) = MCons mem rest
