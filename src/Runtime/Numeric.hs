{- | Integer arithmetic with WebAssembly's signedness and trapping behaviour, plus the float
  min/max/copysign corner cases. Stored integers are raw bit patterns ('Word32'/'Word64', see
  'Syntax.Immediates.HostType'); a signed operation reinterprets them through
  'toSigned32'/'toSigned64' and converts back. Returning @Either Trap@ keeps these independent
  of the interpreter's plumbing.
-}
module Runtime.Numeric (
    toSigned32,
    toSigned64,
    fromSigned32,
    fromSigned64,
    intDiv32,
    intDiv64,
    intRem32,
    intRem64,
    wasmMin,
    wasmMax,
    copysign32,
    copysign64,
) where

import Data.Bits ((.&.), (.|.))
import Data.Int (Int32, Int64)
import Data.Word (Word32, Word64)
import GHC.Float (castDoubleToWord64, castFloatToWord32, castWord32ToFloat, castWord64ToDouble)

import Runtime.Trap (Trap (..))
import Syntax.Immediates (Signedness (..))

-- *** Signed views of the raw integer bits ***

toSigned32 :: Word32 -> Int32
toSigned32 = fromIntegral

toSigned64 :: Word64 -> Int64
toSigned64 = fromIntegral

fromSigned32 :: Int32 -> Word32
fromSigned32 = fromIntegral

fromSigned64 :: Int64 -> Word64
fromSigned64 = fromIntegral

-- *** Division and remainder ***

intDiv32 :: Signedness -> Word32 -> Word32 -> Either Trap Word32
intDiv32 _ _ 0 = Left IntegerDivideByZero
intDiv32 Unsigned x y = Right (x `div` y)
intDiv32 Signed x y
    | sx == minBound && sy == -1 = Left IntegerOverflow
    | otherwise = Right (fromSigned32 (sx `quot` sy))
  where
    sx = toSigned32 x
    sy = toSigned32 y

intDiv64 :: Signedness -> Word64 -> Word64 -> Either Trap Word64
intDiv64 _ _ 0 = Left IntegerDivideByZero
intDiv64 Unsigned x y = Right (x `div` y)
intDiv64 Signed x y
    | sx == minBound && sy == -1 = Left IntegerOverflow
    | otherwise = Right (fromSigned64 (sx `quot` sy))
  where
    sx = toSigned64 x
    sy = toSigned64 y

intRem32 :: Signedness -> Word32 -> Word32 -> Either Trap Word32
intRem32 _ _ 0 = Left IntegerDivideByZero
intRem32 Unsigned x y = Right (x `rem` y)
intRem32 Signed x y
    | sx == minBound && sy == -1 = Right 0 -- the only signed-overflow case; remainder is 0
    | otherwise = Right (fromSigned32 (sx `rem` sy))
  where
    sx = toSigned32 x
    sy = toSigned32 y

intRem64 :: Signedness -> Word64 -> Word64 -> Either Trap Word64
intRem64 _ _ 0 = Left IntegerDivideByZero
intRem64 Unsigned x y = Right (x `rem` y)
intRem64 Signed x y
    | sx == minBound && sy == -1 = Right 0
    | otherwise = Right (fromSigned64 (sx `rem` sy))
  where
    sx = toSigned64 x
    sy = toSigned64 y

-- *** Float corner cases ***

{- | WebAssembly @min@/@max@. NaN propagates (the spec permits an arithmetic NaN; we keep the
  offending operand). Signed zero is handled explicitly, which Haskell's 'min'/'max' do not:
  @min +0 -0 = -0@ and @max +0 -0 = +0@, regardless of argument order.
-}
wasmMin, wasmMax :: RealFloat a => a -> a -> a
wasmMin x y
    | isNaN x = x
    | isNaN y = y
    | x == 0 && y == 0 = if isNegativeZero x || isNegativeZero y then -0 else 0
    | otherwise = min x y
wasmMax x y
    | isNaN x = x
    | isNaN y = y
    | x == 0 && y == 0 = if isNegativeZero x && isNegativeZero y then -0 else 0
    | otherwise = max x y

{- | The magnitude of @x@ with the sign bit of @y@ — on the bits, because the sign of a NaN
  is not observable through comparisons, and a NaN's payload must survive.
-}
copysign32 :: Float -> Float -> Float
copysign32 x y =
    castWord32ToFloat ((castFloatToWord32 x .&. 0x7FFFFFFF) .|. (castFloatToWord32 y .&. 0x80000000))

copysign64 :: Double -> Double -> Double
copysign64 x y =
    castWord64ToDouble ((castDoubleToWord64 x .&. 0x7FFFFFFFFFFFFFFF) .|. (castDoubleToWord64 y .&. 0x8000000000000000))
