{- | A data segment as decoded: bytes that are either copied into memory 0 at a constant offset
  when the module is instantiated (active), or kept for @memory.init@ to copy later (passive).
-}
module Syntax.DataSegments (
    RawData (..),
    DataMode (..),
) where

import Data.ByteString (ByteString)

import Syntax.Expressions

data RawData = RawData
    { mode :: DataMode
    , bytes :: ByteString
    }

data DataMode
    = Active RawExpr
    | Passive
