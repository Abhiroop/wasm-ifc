{- | A function as decoded: its signature, the locals it declares (beyond its parameters),
  and its instruction body. The decoder merges the binary's separate function and code
  sections into this single record.
-}
module Syntax.Functions (
    RawFunction (..),
) where

import Syntax.Instructions (RawExpr)
import Syntax.Types

data RawFunction = RawFunction
    { signature :: FuncType
    , locals :: [ValType]
    , body :: RawExpr
    }
