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
) where

import Data.Kind (Type)
import Data.Singletons.Base.TH (Sing)

import Syntax.Types (ValType)
import Validation.Shape (Elem (..))

type LocalRef :: ValType -> [ValType] -> Type
data LocalRef t ls = LocalRef !Int !(Sing t)

-- | Resolve a local's witness into its position, counted from zero, and its value type.
resolveLocal :: Sing t -> Elem t ls -> LocalRef t ls
resolveLocal ty ix = LocalRef (positionOf 0 ix) ty
  where
    positionOf :: Int -> Elem x xs -> Int
    positionOf !n Here = n
    positionOf !n (There rest) = positionOf (n + 1) rest

-- | Where the local sits in its frame: below the frame's length, since the witness proves it.
localPosition :: LocalRef t ls -> Int
localPosition (LocalRef position _) = position

-- | The local's value type, which says how to read its word back.
localType :: LocalRef t ls -> Sing t
localType (LocalRef _ ty) = ty
