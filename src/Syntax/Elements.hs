-- | An active element segment as decoded: functions to place in table 0 from a constant offset.
module Syntax.Elements (
    RawElem (..),
) where

import Syntax.Expressions
import Syntax.Indices (FunctionIdx)

data RawElem = RawElem
    { offset :: RawExpr
    , functions :: [FunctionIdx]
    }
