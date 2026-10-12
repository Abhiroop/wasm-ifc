{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

{- | Globals, in their two forms: 'RawGlobal' as decoded (a type and an initializer
  expression), and 'Global' as validated — the constant the initializer denotes, at the
  global's type.
-}
module Syntax.Globals (
    RawGlobal (..),
    ConstExpr (..),
    ConstOp (..),
    Global (..),
    GlobalSpace (..),
) where

import Data.Singletons (Sing)
import Data.Text (Text)
import Syntax.Immediates (HostType)
import Syntax.Instructions (RawExpr)
import Syntax.Types
import Syntax.TypesIFC (LabelledGlobalType, LabelledValType (..))

-- *** As decoded ***

data RawGlobal = RawGlobal
    { globalType :: GlobalType
    , initializer :: RawExpr
    }

-- *** As validated ***

{- | A constant expression of a value type, as validation leaves it: a constant, the value of
  an imported global (by the names it is imported under, since only instantiation knows it),
  or integer arithmetic on two of them (WebAssembly 3.0's extended constant expressions). A
  reference to a function is a constant: validation has resolved it.
-}
data ConstExpr (t :: ValType) where
    ConstValue :: HostType t -> ConstExpr t
    ConstImported :: Text -> Text -> Sing t -> ConstExpr t
    ConstBinary :: IsInt t -> ConstOp -> ConstExpr t -> ConstExpr t -> ConstExpr t

data ConstOp = ConstAdd | ConstSub | ConstMul

{- | A global as validated: a defined one has its initial value, a constant expression of its
  type; an imported one has the names its embedder provides it under, and what it must be.
-}
data Global (gt :: LabelledGlobalType) where
    Global :: ConstExpr t -> Global ('GlobalType mut (t ':~ l))
    ProvidedGlobal :: Text -> Text -> Sing mut -> Sing t -> Global ('GlobalType mut (t ':~ l))

-- | A module's global index space: one entry per global type in the shape.
data GlobalSpace (gs :: [LabelledGlobalType]) where
    NoGlobals :: GlobalSpace '[]
    Declared :: Global gt -> GlobalSpace gs -> GlobalSpace (gt ': gs)
