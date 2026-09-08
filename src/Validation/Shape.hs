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

import Syntax.Types (AddrType, FuncType, GlobalType, ResultType, ValType)

-- We reuse @singletons-base@'s promoted list concatenation '(++)' (it is exactly the family we
-- would otherwise hand-roll). Stack shapes compose by appending the part a scope produces on
-- top of the part it leaves untouched. @++@ is not injective, so splitting a @ps ++ s@ stack
-- back into @ps@ and @s@ is driven by the 'Append' witness below rather than by inverting it.
-- (We do NOT import the library's @Elem@ — that is @Foldable@'s @Bool@-valued @elem@, unrelated
-- to our de Bruijn-index 'Elem'.)

{- | Evidence that @c@ is @a ++ b@. Its spine is the length of @a@; because @a@, @b@ and
  @c@ are independent indices, consuming it (in @splitStack@) never requires inverting
  @++@. Carried by the framed/branching instructions so the interpreter can peel operands.
-}
type Append :: [ValType] -> [ValType] -> [ValType] -> Type
data Append a b c where
    ANil :: Append '[] b b
    ACons :: Append a b c -> Append (x ': a) b (x ': c)

{- | Build the 'Append' witness for a prefix from its singleton. The witness is just the spine
  of the prefix, so the suffix @b@ is whatever the use site fixes. The smart constructors in
  "Syntax.Instructions" use this with 'sing', so call sites with static stack shapes need not
  write witnesses by hand; the elaborator builds the same witness from decoded data with
  'Validation.Reflect.matchPrefix'.
-}
appendFromSing :: forall a b. Sing (a :: [ValType]) -> Append a b (a ++ b)
appendFromSing SNil = ANil
appendFromSing (SCons _ rest) = ACons (appendFromSing rest)

{- | A typed de Bruijn index: a proof that @x@ is the element of @xs@ at this position,
  carrying both the position (its term-level structure) and the element (in its type).
  One workhorse for every index space: locals (@Elem t locals@), labels
  (@Elem rs labels@), functions (@Elem ft (ModuleFuncs shape)@) and globals.
-}
type Elem :: k -> [k] -> Type
data Elem x xs where
    Here :: Elem x (x ': xs)
    There :: Elem x xs -> Elem x (y ': xs)

{- | The compile-time shape of a module: the types of its function, global and memory index
  spaces. Used as a single kind index on the instruction GADT so it stays compact. Memories
  are identified by their 'MemShape' (so a memory carries its declared type, like every other
  instance). A record only for the field names' documentation value — 'ModuleShape' is used
  promoted, and the projection type families below ('ModuleFuncs' etc.) are what read the
  fields at the type level.
-}
data ModuleShape = ModuleShape
    { moduleFuncTypes :: [FuncType]
    , moduleGlobalTypes :: [GlobalType]
    , moduleMemShapes :: [MemShape]
    }

type ModuleFuncs :: ModuleShape -> [FuncType]
type family ModuleFuncs s where
    ModuleFuncs ('ModuleShape fs _ _) = fs

type ModuleGlobals :: ModuleShape -> [GlobalType]
type family ModuleGlobals s where
    ModuleGlobals ('ModuleShape _ gs _) = gs

type ModuleMems :: ModuleShape -> [MemShape]
type family ModuleMems s where
    ModuleMems ('ModuleShape _ _ ms) = ms

{- | The per-activation (function-scoped) part of an instruction's context: the local
  variable types and the function's result type. These two always share a scope — both
  are fixed within a function and both change exactly on a @call@ — so they travel
  together as one index on the typed AST.
-}
data FrameShape = FrameShape
    { frLocals :: [ValType]
    , frReturn :: ResultType
    }

type FrameLocals :: FrameShape -> [ValType]
type family FrameLocals f where
    FrameLocals ('FrameShape ls _) = ls

type FrameReturn :: FrameShape -> ResultType
type family FrameReturn f where
    FrameReturn ('FrameShape _ rs) = rs

{- | The type-level counterpart of 'Syntax.Types.MemType', used as the shape index of a
  'Runtime.MemInst.MemInst' and the memory slots of a 'ModuleShape'. 'MemType'\'s @Word32@
  limits do not promote to a kind, so this mirror uses type-level 'Natural's (reflected
  from the decoded limits during elaboration). The limits are carried for faithfulness,
  not used for static checking — WebAssembly bounds are runtime traps. (Used only
  promoted; the term-level selectors document the fields.)
-}
data MemShape = MemShape
    { msAddrType :: AddrType
    , msMin :: Natural
    , msMax :: Maybe Natural
    }
    deriving stock (Eq, Show)

-- Library singletons for the shape kinds. The list/'Maybe'/'Natural' fields draw their 'Sing'
-- instances from @singletons-base@; the element types from "Syntax.Types".
$(genSingletons [''MemShape, ''ModuleShape, ''FrameShape])
