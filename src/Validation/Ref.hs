{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RoleAnnotations #-}

{- | Local variables resolved for the machine (TODO.md §I, E2b).

  An instruction that reads or writes a local used to carry the local's 'Elem' witness, and the
  machine walked the witness, one step per position, on every access. A 'LocalRef' is that
  witness resolved once, at elaboration: the local's position in its frame and its value type,
  so an access indexes a flat frame directly and knows how to read the word it finds there.

  This is the one place where a property the types used to carry is kept by an interface
  instead, a trade approved on 2026-09-15. The types still guarantee everything about @t@ and
  @ls@: a @LocalRef t ls@ names a local of type @t@ in a frame of shape @ls@, and fits no other
  frame. The interface guarantees that the position is the one the witness denotes: the
  constructor is not exported, and 'resolveLocal', the only way to build a reference, computes
  the position from the witness. The type needs no such care, since a @Sing t@ is the unique
  singleton of @t@.
-}
module Validation.Ref (
    LocalRef,
    resolveLocal,
    wordsOf,
    localPosition,
    localType,
    FunctionRef,
    resolveFunction,
    functionReference,
    MemoryRef (..),
    TableRef (..),
) where

import Data.Kind (Type)
import Data.Singletons.Base.TH (SList (SCons, SNil), Sing)
import Data.Word (Word32)

import Syntax.Immediates (Reference, referenceTo)
import Syntax.Types (AddrType, SValType (..), ValType)
import Syntax.TypesIFC (LabelledFuncType, LabelledValType (..), SLabelledValType (..), SecLevel)
import Validation.Shape (Elem (..), MemShape (..), TableShape (..))

type LocalRef :: LabelledValType -> [LabelledValType] -> Type
data LocalRef t ls where
    LocalRef :: !Int -> !(Sing (vt :: ValType)) -> LocalRef (vt ':~ l) ls

{- | Resolve a local's witness into its place in the frame and its value type. A local takes
  one word of the frame, or two if it is a vector, so its place is the number of words the
  locals before it take: the frame's types say that.
-}
resolveLocal :: Sing (ls :: [LabelledValType]) -> Elem t ls -> LocalRef t ls
resolveLocal = go 0
  where
    go :: Int -> Sing (ls' :: [LabelledValType]) -> Elem t ls' -> LocalRef t ls'
    go !at (SCons (ty :%~ _) _) Here = LocalRef at ty
    go !at (SCons (ty :%~ _) rest) (There ix) = case go (at + wordsOf ty) rest ix of LocalRef found foundType -> LocalRef found foundType
    go _ SNil ix = case ix of {}

-- | The words of a frame that a local of a type takes.
wordsOf :: Sing (t :: ValType) -> Int
wordsOf ty = case ty of
    SV128 -> 2
    _ -> 1

-- | Where the local sits in its frame: below the frame's length, since the witness proves it.
localPosition :: LocalRef t ls -> Int
localPosition (LocalRef position _) = position

{- | The local's value type, which says how to read its word back. (Its security level is
  static only: nothing at run time depends on it.)
-}
localType :: LocalRef (vt ':~ l) ls -> Sing vt
localType (LocalRef _ ty) = ty

{- | A function of the module as a @funcref@ value: the reference whose index is the position
  of a function that a witness proved to exist. The constructor stays in this module, so every
  reference a typed instruction or an element segment holds names a function of its module.
-}
type FunctionRef :: [LabelledFuncType] -> Type

type role FunctionRef nominal
newtype FunctionRef fts = FunctionRef Reference

-- | Resolve a function's witness into the reference to it.
resolveFunction :: Elem ft fts -> FunctionRef fts
resolveFunction ix = FunctionRef (referenceTo (positionOf 0 ix))
  where
    positionOf :: Word32 -> Elem x xs -> Word32
    positionOf !n Here = n
    positionOf !n (There rest) = positionOf (n + 1) rest

functionReference :: FunctionRef fts -> Reference
functionReference (FunctionRef reference) = reference

{- | A memory of the module as an instruction names it: its witness, and the address type the
  witness's shape has, as a singleton, since the machine reads an address off the stack by it.
-}
type MemoryRef :: AddrType -> [MemShape] -> Type
data MemoryRef at ms where
    MemoryRef :: !(Sing at) -> Elem ('MemShape at lo hi) ms -> MemoryRef at ms

{- | A table of the module as an instruction names it: its witness, and the type of its
  indices as a singleton, by which the machine reads an index off the stack.
-}
type TableRef :: ValType -> SecLevel -> AddrType -> [TableShape] -> Type
data TableRef t lt at ts where
    TableRef :: !(Sing at) -> Elem ('TableShape t lt at lo hi) ts -> TableRef t lt at ts
