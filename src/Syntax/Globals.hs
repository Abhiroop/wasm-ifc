-- | A global as decoded: its declared type plus the constant expression that initializes it.
module Syntax.Globals where

import Syntax.Expressions
import Syntax.Types

data RawGlobal = RawGlobal
    { wasmType :: GlobalType
    , initializer :: RawExpr
    }
