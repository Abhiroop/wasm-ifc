{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The type-level validation vocabulary: the shapes the typed AST is indexed by. List
--   concatenation and its 'Append' witness, typed de Bruijn indices ('Elem'), the module
--   shape ('ModuleShape') against which @call@, globals and memory operations are checked,
--   and the memory shape ('MemShape'). These are the "types" the syntax carries as indices,
--   so the typed AST in "Syntax.Instructions" depends on this module.
module Validation.Shape
    ( type (++)
    , Append (..)
    , KnownAppend (..)
    , Elem (..)
    , ModuleShape (..)
    , ModuleFuncs
    , ModuleGlobals
    , ModuleMems
    , MemShape (..)
    ) where

import Data.Kind       (Constraint, Type)
import Numeric.Natural (Natural)

import Syntax.Types (AddrType, FuncType, GlobalType)

-- | Type-level list concatenation. Stack shapes compose by appending the part a scope
--   produces on top of the part it leaves untouched. There is no list @++@ at the type level
--   in @base@ (it lives in @singletons-base@, which we do not depend on), so it is a small
--   hand-rolled family. It is not injective, so splitting a @ps ++ s@ stack back into @ps@
--   and @s@ is driven by an 'Append' witness rather than by inverting this family.
type (++) :: [k] -> [k] -> [k]
type family xs ++ ys where
    '[]       ++ ys = ys
    (x ': xs) ++ ys = x ': (xs ++ ys)

infixr 5 ++

-- | Evidence that @c@ is @a ++ b@. Its spine is the length of @a@; because @a@, @b@ and
--   @c@ are independent indices, consuming it (in @splitStack@) never requires inverting
--   @++@. Carried by the framed/branching instructions so the interpreter can peel operands.
-- The 'k' here is deliberately an inferred binder ('forall {k}.'), not a specified one — a
-- specified 'k' would insert itself ahead of 'a'/'b' in the 'TypeApplications' order and
-- break every existing @appendWitness \@ps \@s@ call site (this used to be monomorphic in
-- 'ValType', so none of those call sites expect a leading kind argument).
type Append :: forall {k}. [k] -> [k] -> [k] -> Type
data Append a b c where
    ANil  :: Append '[] b b
    ACons :: Append a b c -> Append (x ': a) b (x ': c)

-- | Build the 'Append' witness for a statically known prefix @a@ (the suffix @b@ is
--   whatever the use site fixes). Instruction smart constructors use this so call sites
--   need not write witnesses by hand.
type KnownAppend :: forall {k}. [k] -> [k] -> Constraint
class KnownAppend a b where
    appendWitness :: Append a b (a ++ b)

instance KnownAppend '[] b where
    appendWitness = ANil

instance KnownAppend a b => KnownAppend (x ': a) b where
    appendWitness = ACons appendWitness

-- | A typed de Bruijn index: a proof that @x@ is the element of @xs@ at this position,
--   carrying both the position (its term-level structure) and the element (in its type).
--   One workhorse for every index space: locals (@Elem t locals@), labels
--   (@Elem rs labels@), functions (@Elem ft (ModuleFuncs shape)@) and globals.
type Elem :: k -> [k] -> Type
data Elem x xs where
    Here  :: Elem x (x ': xs)
    There :: Elem x xs -> Elem x (y ': xs)

-- | The compile-time shape of a module: the function, global and memory index spaces. Used
--   as a single kind index on the instruction GADT so it stays compact. Memories are
--   identified by their 'MemShape' (so a memory carries its declared type, like every other
--   instance).
data ModuleShape = ModuleShape [FuncType] [GlobalType] [MemShape]

type ModuleFuncs :: ModuleShape -> [FuncType]
type family ModuleFuncs s where
    ModuleFuncs ('ModuleShape fs _ _) = fs

type ModuleGlobals :: ModuleShape -> [GlobalType]
type family ModuleGlobals s where
    ModuleGlobals ('ModuleShape _ gs _) = gs

type ModuleMems :: ModuleShape -> [MemShape]
type family ModuleMems s where
    ModuleMems ('ModuleShape _ _ ms) = ms

-- | The type-level counterpart of 'Syntax.Types.MemType', used as the shape index of a
--   'Runtime.MemInst.MemInst' and the memory slots of a 'ModuleShape'. 'MemType'\'s @Word32@
--   limits do not promote to a kind, so this mirror uses type-level 'Natural's (reflected
--   from the decoded limits during elaboration). The limits are carried for faithfulness,
--   not used for static checking — WebAssembly bounds are runtime traps. (Used only
--   promoted; the term-level selectors document the fields.)
data MemShape = MemShape
    { msAddrType :: AddrType
    , msMin      :: Natural
    , msMax      :: Maybe Natural
    } deriving (Eq, Show)
