{-# LANGUAGE DataKinds #-}

module Runtime.Values (
    Val,
    fromI32,
    toI32,
    fromI64,
    toI64,
    fromF32,
    toF32,
    fromF64,
    toF64,
    toSigned32,
    toSigned64,
    fromSigned32,
    fromSigned64,
) where

import Data.Int (Int32, Int64)
import Data.Word (Word32, Word64)
import GHC.Float (castDoubleToWord64, castFloatToWord32, castWord32ToFloat, castWord64ToDouble)

-- In the typed interpreter a value-stack slot of type @t@ literally /is/ a
-- @'Syntax.Immediates.HostType' t@: the type, not the value, says how to read the bits. The
-- untyped 'Val' below is the type-erased counterpart used by the decoder and the conversion
-- bridge, with the @from*@/@to*@ helpers shadowing 'HostType' at the term level.

{- | A runtime value: just 64 bits, with no record of its type.

'Val' is the type-erased slot used by the conversion bridge ('Runtime.Convert'): the
typed interpreter marshals a host value into it, applies a bit-level conversion, and
reads it back. 32-bit values occupy the low half; floats are stored as their IEEE-754
bit pattern.

It is deliberately untyped. A @Val (t :: ValType)@ would let the marshalling be checked,
but it would force 'Syntax.Instructions.ConvertOp' to be indexed by its source and target
types and threaded through the interpreter, for little gain: a conversion is exactly a
change of type, so a single flat bit-bag is the natural home for it, and this slot never
escapes into the typed operand stack (the interpreter converts back to 'HostType' at the
source/target types it already knows).
-}
newtype Val = Val Word64
    deriving stock (Eq, Show)

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
