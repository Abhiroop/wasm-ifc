{- | The module's index spaces, as typed @newtype@s over the @u32@ indices that instructions
  and sections use to refer to labels, locals, globals, functions and memories.
-}
module Syntax.Indices (
    LabelIdx (..),
    GlobalIdx (..),
    LocalIdx (..),
    FunctionIdx (..),
    MemoryIdx (..),
    TypeIdx (..),
    TableIdx (..),
    DataIdx (..),
) where

import Data.Word (Word32)

newtype LabelIdx = LabelIdx Word32 deriving stock (Eq, Ord, Show)

newtype GlobalIdx = GlobalIdx Word32 deriving stock (Eq, Ord, Show)
newtype LocalIdx = LocalIdx Word32 deriving stock (Eq, Ord, Show)

newtype FunctionIdx = FunctionIdx Word32 deriving stock (Eq, Ord, Show)
newtype MemoryIdx = MemoryIdx Word32 deriving stock (Eq, Ord, Show)

newtype TypeIdx = TypeIdx Word32 deriving stock (Eq, Ord, Show)
newtype TableIdx = TableIdx Word32 deriving stock (Eq, Ord, Show)
newtype DataIdx = DataIdx Word32 deriving stock (Eq, Ord, Show)

{- newtype TagIdx    = TagIdx    Word32 deriving stock (Eq, Ord, Show) -}
{- newtype DataIdx   = DataIdx   Word32 deriving stock (Eq, Ord, Show) -}
{- newtype ElemIdx   = ElemIdx   Word32 deriving stock (Eq, Ord, Show) -}
