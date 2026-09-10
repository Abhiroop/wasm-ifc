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
    Globals (..),
) where

import Syntax.Immediates (HostType)
import Syntax.Instructions (RawExpr)
import Syntax.Types

-- *** As decoded ***

data RawGlobal = RawGlobal
    { globalType :: GlobalType
    , initializer :: RawExpr
    }

-- *** As validated ***

-- | A global's initial value, typed by its declared type.
data Global (gt :: GlobalType) where
    Global :: HostType t -> Global ('GlobalType mut t)

-- | A module's globals, one per entry of its global index space.
data Globals (gs :: [GlobalType]) where
    GlobalsNil :: Globals '[]
    GlobalsCons :: Global gt -> Globals gs -> Globals (gt ': gs)
