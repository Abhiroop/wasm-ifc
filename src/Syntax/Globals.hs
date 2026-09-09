-- | A global as decoded: its declared type plus the constant expression that initializes it.
module Syntax.Globals (
    RawGlobal (..),
) where

import Syntax.Expressions
import Syntax.Types

data RawGlobal = RawGlobal
    { globalType :: GlobalType
    , initializer :: RawExpr
    }
