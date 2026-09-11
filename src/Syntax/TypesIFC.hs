{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{- | The information-flow vocabulary the IFC layer adds to the core types: security levels,
  value types labelled with one, the flow relation and the join. Abhiroop's first cut
  (2026-09); the labelled instruction GADT in "Syntax.InstructionsIFC" is indexed by these.
-}
module Syntax.TypesIFC (
    SecLevel (..),
    LValType (..),
    KnownSecLevel (..),
    CanFlowInto,
    type (:/\),
) where

import Syntax.Types (ValType)

-- | The two-point security lattice.
data SecLevel = Low | High
    deriving stock (Eq, Ord, Show)

infix 6 :~

-- | A value type together with the security level of the values it classifies.
data LValType = ValType :~ SecLevel
    deriving stock (Eq, Show)

-- | The term-level witness of a security level (a hand-rolled singleton).
data KnownSecLevel (l :: SecLevel) where
    IsLow :: KnownSecLevel 'Low
    IsHigh :: KnownSecLevel 'High

-- | @l@ may flow into @l'@: the lattice order, as a constraint.
class CanFlowInto (l :: SecLevel) (l' :: SecLevel)

instance CanFlowInto 'Low 'Low
instance CanFlowInto 'Low 'High
instance CanFlowInto 'High 'High

infixl 7 :/\

-- | The join (least upper bound) of two levels: the label of a value computed from both.
type family (:/\) (l :: SecLevel) (l' :: SecLevel) :: SecLevel where
    'Low :/\ 'Low = 'Low
    _ :/\ _ = 'High
