{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

{- | The host (Haskell) type that represents each WASM value type — used both for a constant's
  immediate literal and for the values held on the operand stack, locals and globals. (This
  is one family now that 'Syntax.Types.ValType' is flat; it used to be split into a
  @NumType@-keyed @Immediate@ and a @ValType@-keyed @RuntimeHostType@.)
-}
module Syntax.Immediates (
    HostType,
) where

import Data.Kind (Type)
import Data.Word (Word32, Word64)

import Syntax.Types

type family HostType (t :: ValType) :: Type where
    HostType 'I32 = Word32
    HostType 'I64 = Word64
    HostType 'F32 = Float
    HostType 'F64 = Double
