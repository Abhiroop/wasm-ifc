{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Runtime.Values where

import Data.Int       (Int32, Int64)
import Data.Kind      (Type)
import Data.Word      (Word32, Word64)
import GHC.Float      (castDoubleToWord64, castFloatToWord32, castWord32ToFloat, castWord64ToDouble)

import Syntax.Immediates (ImmediateHostType)
import Syntax.Types

-- | Maps a value type to its Haskell host representation at the type level.
--
-- In the typed interpreter a value-stack slot of type @t@ literally /is/ a
-- @RuntimeHostType t@: the type, not the value, says how to read the bits. The untyped
-- 'Val' below is the type-erased counterpart used by the decoder and the conversion
-- bridge, with the @from*@/@to*@ helpers shadowing this family at the term level.
type family RuntimeHostType (t :: ValType) :: Type where
    RuntimeHostType ('Num n) = ImmediateHostType n

-- | A runtime value: just 64 bits, with no record of its type.
--
-- 'Val' is the type-erased slot used by the conversion bridge ('Runtime.Convert'): the
-- typed interpreter marshals a host value into it, applies a bit-level conversion, and
-- reads it back. 32-bit values occupy the low half; floats are stored as their IEEE-754
-- bit pattern.
--- TODO: should probably define Val (t :: ValType), representing a val that satifies a given type
newtype Val = Val Word64
    deriving (Eq, Show)

-- Move host values in and out of the untyped slot.

fromI32 :: Word32 -> Val
fromI32 = Val . fromIntegral

toI32 :: Val -> Word32
toI32 (Val bits) = fromIntegral bits

fromI64 :: Word64 -> Val
fromI64 = Val

toI64 :: Val -> Word64
toI64 (Val bits) = bits

fromF32 :: Float -> Val
fromF32 = fromI32 . castFloatToWord32

toF32 :: Val -> Float
toF32 = castWord32ToFloat . toI32

fromF64 :: Double -> Val
fromF64 = fromI64 . castDoubleToWord64

toF64 :: Val -> Double
toF64 = castWord64ToDouble . toI64

-- Reinterpret an unsigned word as a signed integer of the same width, and back.
toSigned32 :: Word32 -> Int32
toSigned32 = fromIntegral

toSigned64 :: Word64 -> Int64
toSigned64 = fromIntegral

fromSigned32 :: Int32 -> Word32
fromSigned32 = fromIntegral

fromSigned64 :: Int64 -> Word64
fromSigned64 = fromIntegral
