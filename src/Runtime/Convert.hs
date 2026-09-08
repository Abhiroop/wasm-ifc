{- | Numeric type conversions, typed by the 'ConvertOp' they implement. The opcode's indices
  fix the source and target value types, so each case converts a concrete @HostType from@
  into a concrete @HostType to@ with no untyped slot in between; only the float-to-integer
  truncations can trap.
-}
module Runtime.Convert (
    convertVal,
) where

import Data.Int (Int16, Int32, Int8)
import Data.Word (Word32, Word64)
import GHC.Float (
    castDoubleToWord64,
    castFloatToWord32,
    castWord32ToFloat,
    castWord64ToDouble,
    double2Float,
    float2Double,
 )

import Runtime.Numeric (fromSigned32, fromSigned64, toSigned32, toSigned64)
import Runtime.Trap (Trap (..))
import Syntax.Immediates (HostType)
import Syntax.Instructions (ConvertOp (..))
import Syntax.Types (Signedness (..))

{- | Apply a conversion. Matching the opcode refines @from@ and @to@, so within each case the
  operand and result are ordinary host types. Integers are raw bit patterns: a signed
  conversion first reinterprets them through 'toSigned32'/'toSigned64'.
-}
convertVal :: ConvertOp from to -> HostType from -> Either Trap (HostType to)
convertVal op a = case op of
    I32WrapI64 -> Right (fromIntegral a)
    I64ExtendI32 Signed -> Right (fromIntegral (toSigned32 a))
    I64ExtendI32 Unsigned -> Right (fromIntegral a)
    I32TruncF32 sign -> truncToI32 sign a
    I32TruncF64 sign -> truncToI32 sign a
    I64TruncF32 sign -> truncToI64 sign a
    I64TruncF64 sign -> truncToI64 sign a
    F32ConvertI32 Signed -> Right (fromIntegral (toSigned32 a))
    F32ConvertI32 Unsigned -> Right (fromIntegral a)
    F32ConvertI64 Signed -> Right (fromIntegral (toSigned64 a))
    F32ConvertI64 Unsigned -> Right (fromIntegral a)
    F64ConvertI32 Signed -> Right (fromIntegral (toSigned32 a))
    F64ConvertI32 Unsigned -> Right (fromIntegral a)
    F64ConvertI64 Signed -> Right (fromIntegral (toSigned64 a))
    F64ConvertI64 Unsigned -> Right (fromIntegral a)
    -- The dedicated casts are exact for NaN and the infinities; 'realToFrac' is only
    -- guaranteed to be when GHC's rewrite rules happen to fire.
    F32DemoteF64 -> Right (double2Float a)
    F64PromoteF32 -> Right (float2Double a)
    I32ReinterpretF32 -> Right (castFloatToWord32 a)
    F32ReinterpretI32 -> Right (castWord32ToFloat a)
    I64ReinterpretF64 -> Right (castDoubleToWord64 a)
    F64ReinterpretI64 -> Right (castWord64ToDouble a)
    I32Extend8S -> Right (fromSigned32 (fromIntegral (fromIntegral a :: Int8)))
    I32Extend16S -> Right (fromSigned32 (fromIntegral (fromIntegral a :: Int16)))
    I64Extend8S -> Right (fromSigned64 (fromIntegral (fromIntegral a :: Int8)))
    I64Extend16S -> Right (fromSigned64 (fromIntegral (fromIntegral a :: Int16)))
    I64Extend32S -> Right (fromSigned64 (fromIntegral (fromIntegral a :: Int32)))

-- WebAssembly traps when a truncation's argument is NaN/infinite or out of range.
truncToI32 :: RealFloat a => Signedness -> a -> Either Trap Word32
truncToI32 sign x
    | isNaN x || isInfinite x = Left InvalidConversionToInteger
    | otherwise = case sign of
        Signed | t >= -(2 ^ (31 :: Int)) && t <= 2 ^ (31 :: Int) - 1 -> Right (fromIntegral t)
        Unsigned | t >= 0 && t <= 2 ^ (32 :: Int) - 1 -> Right (fromIntegral t)
        _ -> Left IntegerOverflow
  where
    t = truncate x :: Integer

truncToI64 :: RealFloat a => Signedness -> a -> Either Trap Word64
truncToI64 sign x
    | isNaN x || isInfinite x = Left InvalidConversionToInteger
    | otherwise = case sign of
        Signed | t >= -(2 ^ (63 :: Int)) && t <= 2 ^ (63 :: Int) - 1 -> Right (fromIntegral t)
        Unsigned | t >= 0 && t <= 2 ^ (64 :: Int) - 1 -> Right (fromIntegral t)
        _ -> Left IntegerOverflow
  where
    t = truncate x :: Integer
