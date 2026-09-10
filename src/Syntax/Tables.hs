-- | A table as decoded: its size limits. Only @funcref@ tables exist here, so that is all of it.
module Syntax.Tables (
    RawTable (..),
) where

import Syntax.Types (Limits)

newtype RawTable = RawTable
    { limits :: Limits
    }
    deriving stock (Eq, Show)
