-- | Numeric type conversions. Operates on the untyped 'Val' slot (raw bits) and returns
--   @Either Trap@. The typed interpreter wraps its host values into 'Val' and back around
--   this, keeping all the conversion cases in one place.
module Runtime.Convert
    ( convertVal
    ) where

import Data.Int (Int8, Int16, Int32)

import Runtime.Trap        (Trap (..))
import Runtime.Values
import Syntax.Instructions (ConvertOp (..))
import Syntax.Types        (Signedness (..))

convertVal :: ConvertOp -> Val -> Either Trap Val
convertVal op a = case op of
    I32WrapI64             -> Right (fromI32 (fromIntegral (toI64 a)))
    I64ExtendI32 Signed    -> Right (fromI64 (fromIntegral (toSigned32 (toI32 a))))
    I64ExtendI32 Unsigned  -> Right (fromI64 (fromIntegral (toI32 a)))
    I32TruncF32 sign       -> truncToI32 sign (toF32 a)
    I32TruncF64 sign       -> truncToI32 sign (toF64 a)
    I64TruncF32 sign       -> truncToI64 sign (toF32 a)
    I64TruncF64 sign       -> truncToI64 sign (toF64 a)
    F32ConvertI32 Signed   -> Right (fromF32 (fromIntegral (toSigned32 (toI32 a))))
    F32ConvertI32 Unsigned -> Right (fromF32 (fromIntegral (toI32 a)))
    F32ConvertI64 Signed   -> Right (fromF32 (fromIntegral (toSigned64 (toI64 a))))
    F32ConvertI64 Unsigned -> Right (fromF32 (fromIntegral (toI64 a)))
    F64ConvertI32 Signed   -> Right (fromF64 (fromIntegral (toSigned32 (toI32 a))))
    F64ConvertI32 Unsigned -> Right (fromF64 (fromIntegral (toI32 a)))
    F64ConvertI64 Signed   -> Right (fromF64 (fromIntegral (toSigned64 (toI64 a))))
    F64ConvertI64 Unsigned -> Right (fromF64 (fromIntegral (toI64 a)))
    F32DemoteF64           -> Right (fromF32 (realToFrac (toF64 a)))
    F64PromoteF32          -> Right (fromF64 (realToFrac (toF32 a)))
    I32ReinterpretF32      -> Right a   -- the untyped slot already holds the raw bits
    F32ReinterpretI32      -> Right a
    I64ReinterpretF64      -> Right a
    F64ReinterpretI64      -> Right a
    I32Extend8S            -> Right (fromI32 (fromSigned32 (fromIntegral (fromIntegral (toI32 a) :: Int8))))
    I32Extend16S           -> Right (fromI32 (fromSigned32 (fromIntegral (fromIntegral (toI32 a) :: Int16))))
    I64Extend8S            -> Right (fromI64 (fromSigned64 (fromIntegral (fromIntegral (toI64 a) :: Int8))))
    I64Extend16S           -> Right (fromI64 (fromSigned64 (fromIntegral (fromIntegral (toI64 a) :: Int16))))
    I64Extend32S           -> Right (fromI64 (fromSigned64 (fromIntegral (fromIntegral (toI64 a) :: Int32))))

-- WebAssembly traps when a truncation's argument is NaN/infinite or out of range.
truncToI32 :: RealFloat a => Signedness -> a -> Either Trap Val
truncToI32 sign x
    | isNaN x || isInfinite x = Left InvalidConversionToInteger
    | otherwise = case sign of
        Signed   | t >= -(2 ^ (31 :: Int)) && t <= 2 ^ (31 :: Int) - 1 -> Right (fromI32 (fromIntegral t))
        Unsigned | t >= 0 && t <= 2 ^ (32 :: Int) - 1                  -> Right (fromI32 (fromIntegral t))
        _ -> Left IntegerOverflow
  where
    t = truncate x :: Integer

truncToI64 :: RealFloat a => Signedness -> a -> Either Trap Val
truncToI64 sign x
    | isNaN x || isInfinite x = Left InvalidConversionToInteger
    | otherwise = case sign of
        Signed   | t >= -(2 ^ (63 :: Int)) && t <= 2 ^ (63 :: Int) - 1 -> Right (fromI64 (fromIntegral t))
        Unsigned | t >= 0 && t <= 2 ^ (64 :: Int) - 1                  -> Right (fromI64 (fromIntegral t))
        _ -> Left IntegerOverflow
  where
    t = truncate x :: Integer
