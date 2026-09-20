{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

{- | Globals, in their two forms: 'RawGlobal' as decoded (a type and an initializer
  expression), and 'Global' as validated — the constant the initializer denotes, at the
  global's type.
-}
module Syntax.Globals (
    RawGlobal (..),
    Global (..),
    GlobalSpace (..),
) where

import Syntax.Immediates (HostType)
import Syntax.Instructions (RawExpr)
import Syntax.Types
import Syntax.TypesIFC (LGlobalType, LValType (..))

-- *** As decoded ***

data RawGlobal = RawGlobal
    { globalType :: GlobalType
    , initializer :: RawExpr
    }

-- *** As validated ***

-- | A global's initial value, typed by its declared type.
data Global (gt :: LGlobalType) where
    Global :: HostType t -> Global ('GlobalType mut (t ':~ l))

-- | A module's global index space: one entry per global type in the shape.
data GlobalSpace (gs :: [LGlobalType]) where
    NoGlobals :: GlobalSpace '[]
    Declared :: Global gt -> GlobalSpace gs -> GlobalSpace (gt ': gs)
