-- | A memory as decoded: just its type (the address width and page limits).
module Syntax.Memories (
    RawMemory (..),
) where

import Syntax.Types

newtype RawMemory = RawMemory
    { memType :: MemType
    }
    deriving stock (Eq, Show)
