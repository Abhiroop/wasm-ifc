-- | Integer division and remainder with WebAssembly's trapping behaviour, shared by both
--   interpreters. Returning @Either Trap@ keeps these independent of either interpreter's
--   monad. Operands are raw bit patterns; signedness selects the interpretation.
module Runtime.Numeric
    ( intDiv32
    , intDiv64
    , intRem32
    , intRem64
    , wasmMin
    , wasmMax
    , copysign
    ) where

import Data.Int  (Int32, Int64)
import Data.Word (Word32, Word64)

import Runtime.Trap  (Trap (..))
import Syntax.Types  (Signedness (..))

intDiv32 :: Signedness -> Word32 -> Word32 -> Either Trap Word32
intDiv32 _        _ 0 = Left IntegerDivideByZero
intDiv32 Unsigned x y = Right (x `div` y)
intDiv32 Signed   x y
    | sx == minBound && sy == -1 = Left IntegerOverflow
    | otherwise                  = Right (fromIntegral (sx `quot` sy))
  where
    sx = fromIntegral x :: Int32
    sy = fromIntegral y :: Int32

intDiv64 :: Signedness -> Word64 -> Word64 -> Either Trap Word64
intDiv64 _        _ 0 = Left IntegerDivideByZero
intDiv64 Unsigned x y = Right (x `div` y)
intDiv64 Signed   x y
    | sx == minBound && sy == -1 = Left IntegerOverflow
    | otherwise                  = Right (fromIntegral (sx `quot` sy))
  where
    sx = fromIntegral x :: Int64
    sy = fromIntegral y :: Int64

intRem32 :: Signedness -> Word32 -> Word32 -> Either Trap Word32
intRem32 _        _ 0 = Left IntegerDivideByZero
intRem32 Unsigned x y = Right (x `rem` y)
intRem32 Signed   x y
    | sx == minBound && sy == -1 = Right 0   -- the only signed-overflow case; remainder is 0
    | otherwise                  = Right (fromIntegral (sx `rem` sy))
  where
    sx = fromIntegral x :: Int32
    sy = fromIntegral y :: Int32

intRem64 :: Signedness -> Word64 -> Word64 -> Either Trap Word64
intRem64 _        _ 0 = Left IntegerDivideByZero
intRem64 Unsigned x y = Right (x `rem` y)
intRem64 Signed   x y
    | sx == minBound && sy == -1 = Right 0
    | otherwise                  = Right (fromIntegral (sx `rem` sy))
  where
    sx = fromIntegral x :: Int64
    sy = fromIntegral y :: Int64

-- | WebAssembly @min@/@max@: NaN propagates; otherwise the host operation.
wasmMin, wasmMax :: RealFloat a => a -> a -> a
wasmMin x y | isNaN x = x | isNaN y = y | otherwise = min x y
wasmMax x y | isNaN x = x | isNaN y = y | otherwise = max x y

-- | The magnitude of @x@ with the sign of @y@.
copysign :: RealFloat a => a -> a -> a
copysign x y
    | y < 0 || isNegativeZero y = negate (abs x)
    | otherwise                 = abs x
