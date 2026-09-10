{- | The module's index spaces, as typed @newtype@s over the @u32@ indices that instructions
  and sections use to refer to types, functions, tables, memories, globals, data segments,
  locals and labels.
-}
module Syntax.Indices (
    TypeIdx (..),
    FunctionIdx (..),
    TableIdx (..),
    MemoryIdx (..),
    GlobalIdx (..),
    DataIdx (..),
    LocalIdx (..),
    LabelIdx (..),
) where

import Data.Word (Word32)

newtype TypeIdx = TypeIdx Word32 deriving stock (Eq, Ord, Show)
newtype FunctionIdx = FunctionIdx Word32 deriving stock (Eq, Ord, Show)
newtype TableIdx = TableIdx Word32 deriving stock (Eq, Ord, Show)
newtype MemoryIdx = MemoryIdx Word32 deriving stock (Eq, Ord, Show)
newtype GlobalIdx = GlobalIdx Word32 deriving stock (Eq, Ord, Show)
newtype DataIdx = DataIdx Word32 deriving stock (Eq, Ord, Show)
newtype LocalIdx = LocalIdx Word32 deriving stock (Eq, Ord, Show)
newtype LabelIdx = LabelIdx Word32 deriving stock (Eq, Ord, Show)
