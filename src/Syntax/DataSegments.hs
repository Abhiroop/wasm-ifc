-- | An active data segment as decoded: the bytes to copy into memory 0 at a constant offset.
module Syntax.DataSegments (
    RawData (..),
) where

import Data.ByteString (ByteString)

import Syntax.Expressions

data RawData = RawData
    { offset :: RawExpr
    , bytes :: ByteString
    }
