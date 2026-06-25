-- | A memory as decoded: just its type (the address width and page limits).
module Syntax.Memories where

import Syntax.Types

newtype RawMemory = RawMemory
    { wasmType :: MemType
    } deriving (Eq, Show)
