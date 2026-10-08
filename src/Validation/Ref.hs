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
    localPosition,
    localType,
    FunctionRef,
    resolveFunction,
    functionReference,
) where

import Data.Kind (Type)
import Data.Singletons.Base.TH (Sing)
import Data.Word (Word32)

import Syntax.Immediates (Reference, referenceTo)
import Syntax.Types (ValType)
import Syntax.TypesIFC (LabelledFuncType, LabelledValType (..), SLabelledValType (..))
import Validation.Shape (Elem (..))

type LocalRef :: LabelledValType -> [LabelledValType] -> Type
data LocalRef t ls where
    LocalRef :: !Int -> !(Sing (vt :: ValType)) -> LocalRef (vt ':~ l) ls

-- | Resolve a local's witness into its position, counted from zero, and its value type.
resolveLocal :: Sing (t :: LabelledValType) -> Elem t ls -> LocalRef t ls
resolveLocal (ty :%~ _) ix = LocalRef (positionOf 0 ix) ty
  where
    positionOf :: Int -> Elem x xs -> Int
    positionOf !n Here = n
    positionOf !n (There rest) = positionOf (n + 1) rest

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
