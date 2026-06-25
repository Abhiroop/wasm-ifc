{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

-- | The host (Haskell) type that represents each WASM number type. The intrinsically-typed
--   layer uses this to give a constant literal exactly the value type its 'NumType' demands.
module Syntax.Immediates where

import Data.Word (Word32, Word64)
import Data.Kind (Type)

import Syntax.Types

type family ImmediateHostType (wasmType :: NumType) :: Type where
    ImmediateHostType 'I32 = Word32
    ImmediateHostType 'I64 = Word64
    ImmediateHostType 'F32 = Float
    ImmediateHostType 'F64 = Double
