{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | The module's index spaces, as typed @newtype@s over the @u32@ indices that instructions
--   and sections use to refer to labels, locals, globals, functions and memories.
module Syntax.Indices where

import Data.Word (Word32)

newtype LabelIdx    = LabelIdx    Word32 deriving (Eq, Ord, Show, Enum)

newtype GlobalIdx   = GlobalIdx   Word32 deriving (Eq, Ord, Show, Enum)
newtype LocalIdx    = LocalIdx    Word32 deriving (Eq, Ord, Show, Enum)

newtype FunctionIdx = FunctionIdx Word32 deriving (Eq, Ord, Show, Enum)
newtype MemoryIdx   = MemoryIdx   Word32 deriving (Eq, Ord, Show, Enum)

{- newtype TypeIdx   = TypeIdx   Word32 deriving (Eq, Ord, Show, Enum) -}
{- newtype TableIdx  = TableIdx  Word32 deriving (Eq, Ord, Show, Enum) -}
{- newtype TagIdx    = TagIdx    Word32 deriving (Eq, Ord, Show, Enum) -}
{- newtype DataIdx   = DataIdx   Word32 deriving (Eq, Ord, Show, Enum) -}
{- newtype ElemIdx   = ElemIdx   Word32 deriving (Eq, Ord, Show, Enum) -}
