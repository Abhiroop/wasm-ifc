{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | The core WASM types — number and value types, function/global/memory types, and the
--   small operand tags (signedness, memory immediates). Singletons are generated for the
--   number and value types so the intrinsically-typed layer can reflect them between the
--   term and type levels.
module Syntax.TypesIFC where

import Syntax.Types




-- | IFC Types

data SecLevel = Low | High

infix 6 :~
data LValType = (:~) ValType SecLevel

data KnownSecLevel (l :: SecLevel) where
    IsLow  :: KnownSecLevel Low
    IsHigh :: KnownSecLevel High

class CanFlowInto (l :: SecLevel) (l' :: SecLevel)
instance CanFlowInto 'Low 'Low
instance CanFlowInto 'Low 'High
instance CanFlowInto 'High 'High

infixl 7 :/\
type family (:/\) (l :: SecLevel) (l' :: SecLevel) :: SecLevel where
    Low :/\ Low = Low
    _ :/\ _ = High