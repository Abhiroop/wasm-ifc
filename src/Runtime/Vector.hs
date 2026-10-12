{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

{- | What the vector instructions compute ("Syntax.Vector"). A vector is taken apart into its
  lanes, each a 'Word64' holding the lane's bits, the operation is done lane by lane, and the
  lanes are put back together. That is slower than working on the two words of a vector at
  once, and it keeps two hundred operations to a page each of integer and of floating-point
  arithmetic: the scalar operations of "Runtime.Numeric" and "Runtime.Convert" do the lanes.
-}
module Runtime.Vector (
    vector1,
    vector2,
    vector3,
    loadedVector,
    replaceLaneBits,
    laneBitsAt,
    lanes,
    fromLanes,
) where

import Data.Bits (complement, popCount, shiftL, shiftR, testBit, xor, (.&.), (.|.))
import Data.Word (Word32, Word64, Word8)
import GHC.Float (castDoubleToWord64, castFloatToWord32, castWord32ToFloat, castWord64ToDouble, double2Float, float2Double)

import Runtime.Convert (truncSatToI32)
import Runtime.Numeric (wasmMax, wasmMin)
import Syntax.Immediates (HostType, Signedness (..), Vector128 (..))
import Syntax.Vector

-- *** Lanes ***

shapeBits :: Shape -> Int
shapeBits shape = case shape of
    I8x16 -> 8
    I16x8 -> 16
    I32x4 -> 32
    I64x2 -> 64

floatBits :: FloatShape -> Int
floatBits shape = case shape of
    F32x4 -> 32
    F64x2 -> 64

-- | The shape whose lanes are half as wide (of @i8x16@, itself: it has none).
narrower :: Shape -> Shape
narrower shape = case shape of
    I64x2 -> I32x4
    I32x4 -> I16x8
    _ -> I8x16

-- | The shape whose lanes are twice as wide (of @i64x2@, itself).
wider :: Shape -> Shape
wider shape = case shape of
    I8x16 -> I16x8
    I16x8 -> I32x4
    _ -> I64x2

maskOf :: Int -> Word64
maskOf bits = if bits >= 64 then maxBound else (1 `shiftL` bits) - 1

-- | The lanes of a vector at a width in bits, lane 0 first, each in the low bits of a word.
lanes :: Int -> Vector128 -> [Word64]
lanes bits (Vector128 low high) = [lane (i * bits) | i <- [0 .. 128 `div` bits - 1]]
  where
    lane at = ((if at < 64 then low else high) `shiftR` (at `mod` 64)) .&. maskOf bits

-- | A vector from its lanes at a width in bits; a lane's bits past the width are dropped.
fromLanes :: Int -> [Word64] -> Vector128
fromLanes bits values = Vector128 (half 0) (half 64)
  where
    half base = foldr (.|.) 0 [(value .&. maskOf bits) `shiftL` (at - base) | (i, value) <- zip [0 ..] values, let at = i * bits, at >= base, at < base + 64]

-- | A lane's bits as a signed or an unsigned number.
signedLane, unsignedLane :: Int -> Word64 -> Integer
signedLane bits value = if testBit value (bits - 1) then toInteger value - 2 ^ bits else toInteger value
unsignedLane _ = toInteger

numberOf :: Signedness -> Int -> Word64 -> Integer
numberOf Signed = signedLane
numberOf Unsigned = unsignedLane

-- | A number as a lane's bits, wrapped to the width.
wrapLane :: Int -> Integer -> Word64
wrapLane bits number = fromInteger (number `mod` 2 ^ bits)

-- | A number as a lane's bits, clamped to what the width holds at that signedness.
saturateLane :: Signedness -> Int -> Integer -> Word64
saturateLane sign bits number = wrapLane bits (max lowest (min highest number))
  where
    (lowest, highest) = case sign of
        Signed -> (-(2 ^ (bits - 1)), 2 ^ (bits - 1) - 1)
        Unsigned -> (0, 2 ^ bits - 1)

-- | A comparison's lane: all ones if it holds, zero otherwise.
truthLane :: Int -> Bool -> Word64
truthLane bits holds = if holds then maskOf bits else 0

-- | A floating-point operation on a lane's bits, at either width.
onFloat :: FloatShape -> (Float -> Float) -> (Double -> Double) -> Word64 -> Word64
onFloat F32x4 single _ value = fromIntegral (castFloatToWord32 (single (castWord32ToFloat (fromIntegral value))))
onFloat F64x2 _ double value = castDoubleToWord64 (double (castWord64ToDouble value))

onFloats :: FloatShape -> (Float -> Float -> Float) -> (Double -> Double -> Double) -> Word64 -> Word64 -> Word64
onFloats F32x4 single _ a b = fromIntegral (castFloatToWord32 (single (castWord32ToFloat (fromIntegral a)) (castWord32ToFloat (fromIntegral b))))
onFloats F64x2 _ double a b = castDoubleToWord64 (double (castWord64ToDouble a) (castWord64ToDouble b))

comparingFloats :: FloatShape -> (Float -> Float -> Bool) -> (Double -> Double -> Bool) -> Word64 -> Word64 -> Bool
comparingFloats F32x4 single _ a b = single (castWord32ToFloat (fromIntegral a)) (castWord32ToFloat (fromIntegral b))
comparingFloats F64x2 _ double a b = double (castWord64ToDouble a) (castWord64ToDouble b)

{- | Round to an integral value the WebAssembly way: NaN and the infinities pass through, and a
  zero result keeps the sign of its argument.
-}
roundLane :: RealFloat a => (a -> Integer) -> a -> a
roundLane toInteger' x
    | isNaN x || isInfinite x = x
    | rounded == 0 && (x < 0 || isNegativeZero x) = -0.0
    | otherwise = rounded
  where
    rounded = fromInteger (toInteger' x)

-- *** Operations, by their number of operands (the top of the stack first) ***

vector1 :: VectorOp '[a] result -> HostType a -> HostType result
vector1 op operand = case op of
    VUnary unary -> vectorUnary unary operand
    VTest test -> vectorTest test operand
    VSplat lane -> splatLane lane operand
    VExtract lane index sign -> extractLane lane index sign operand

vector2 :: VectorOp '[a, b] result -> HostType a -> HostType b -> HostType result
vector2 op top below = case op of
    VBinary binary -> vectorBinary binary below top
    VShift shift -> vectorShift shift below top
    VReplace lane index -> replaceLane lane index below top

vector3 :: VectorOp '[a, b, c] result -> HostType a -> HostType b -> HostType c -> HostType result
vector3 VBitselect mask second first = vectorBitselect first second mask

vectorUnary :: VectorUnary -> Vector128 -> Vector128
vectorUnary op vector@(Vector128 low high) = case op of
    VNot -> Vector128 (complement low) (complement high)
    VIntUnary shape intOp ->
        let bits = shapeBits shape
            apply value = case intOp of
                IAbs -> wrapLane bits (abs (signedLane bits value))
                INeg -> wrapLane bits (negate (signedLane bits value))
                IPopcnt -> fromIntegral (popCount value)
         in fromLanes bits (map apply (lanes bits vector))
    VFloatUnary shape floatOp ->
        let bits = floatBits shape
            signBit = 1 `shiftL` (bits - 1) :: Word64
            apply value = case floatOp of
                -- (On the bits: the sign of a NaN changes too, and its payload stays.)
                FAbsLanes -> value .&. complement signBit
                FNegLanes -> value `xor` signBit
                FSqrtLanes -> onFloat shape sqrt sqrt value
                FCeilLanes -> onFloat shape (roundLane ceiling) (roundLane ceiling) value
                FFloorLanes -> onFloat shape (roundLane floor) (roundLane floor) value
                FTruncLanes -> onFloat shape (roundLane truncate) (roundLane truncate) value
                FNearestLanes -> onFloat shape (roundLane round) (roundLane round) value
         in fromLanes bits (map apply (lanes bits vector))
    VExtend shape half sign ->
        let from = shapeBits (narrower shape)
            sources = pick half (lanes from vector)
         in fromLanes (shapeBits shape) [wrapLane (shapeBits shape) (numberOf sign from value) | value <- sources]
    VExtAddPairwise shape sign ->
        let from = shapeBits (narrower shape)
         in fromLanes (shapeBits shape) [wrapLane (shapeBits shape) (numberOf sign from a + numberOf sign from b) | (a, b) <- pairs (lanes from vector)]
    VTruncSatF32x4 sign -> fromLanes 32 [fromIntegral (truncSatToI32 sign (castWord32ToFloat (fromIntegral value))) | value <- lanes 32 vector]
    VTruncSatF64x2Zero sign -> fromLanes 32 ([fromIntegral (truncSatToI32 sign (castWord64ToDouble value)) | value <- lanes 64 vector] ++ [0, 0])
    VConvertI32x4 sign -> fromLanes 32 [fromIntegral (castFloatToWord32 (fromInteger (numberOf sign 32 value))) | value <- lanes 32 vector]
    VConvertLowI32x4 sign -> fromLanes 64 [castDoubleToWord64 (fromInteger (numberOf sign 32 value)) | value <- take 2 (lanes 32 vector)]
    VDemoteF64x2Zero -> fromLanes 32 ([fromIntegral (castFloatToWord32 (double2Float (castWord64ToDouble value))) | value <- lanes 64 vector] ++ [0, 0])
    VPromoteLowF32x4 -> fromLanes 64 [castDoubleToWord64 (float2Double (castWord32ToFloat (fromIntegral value))) | value <- take 2 (lanes 32 vector)]

-- | The low or the high half of a list of lanes.
pick :: Half -> [a] -> [a]
pick half values = case half of
    LowHalf -> take (length values `div` 2) values
    HighHalf -> drop (length values `div` 2) values

pairs :: [a] -> [(a, a)]
pairs (a : b : rest) = (a, b) : pairs rest
pairs _ = []

-- | A binary operation; the first argument is the first operand (the one deeper on the stack).
vectorBinary :: VectorBinary -> Vector128 -> Vector128 -> Vector128
vectorBinary op first@(Vector128 firstLow firstHigh) second@(Vector128 secondLow secondHigh) = case op of
    VAnd -> Vector128 (firstLow .&. secondLow) (firstHigh .&. secondHigh)
    VAndNot -> Vector128 (firstLow .&. complement secondLow) (firstHigh .&. complement secondHigh)
    VOr -> Vector128 (firstLow .|. secondLow) (firstHigh .|. secondHigh)
    VXor -> Vector128 (firstLow `xor` secondLow) (firstHigh `xor` secondHigh)
    VSwizzle ->
        let bytes = lanes 8 first
         in fromLanes 8 [if index < 16 then bytes !! fromIntegral index else 0 | index <- lanes 8 second]
    VShuffle indices ->
        let bytes = lanes 8 first ++ lanes 8 second
         in fromLanes 8 [bytes !! (fromIntegral index `mod` 32) | index <- indices]
    VIntBinary shape intOp ->
        let bits = shapeBits shape
            apply a b = case intOp of
                IAddLanes -> wrapLane bits (toInteger a + toInteger b)
                ISubLanes -> wrapLane bits (toInteger a - toInteger b)
                IMulLanes -> wrapLane bits (toInteger a * toInteger b)
                IAddSat sign -> saturateLane sign bits (numberOf sign bits a + numberOf sign bits b)
                ISubSat sign -> saturateLane sign bits (numberOf sign bits a - numberOf sign bits b)
                IMinLanes sign -> wrapLane bits (min (numberOf sign bits a) (numberOf sign bits b))
                IMaxLanes sign -> wrapLane bits (max (numberOf sign bits a) (numberOf sign bits b))
                IAvgr -> wrapLane bits ((toInteger a + toInteger b + 1) `div` 2)
         in fromLanes bits (zipWith apply (lanes bits first) (lanes bits second))
    VIntCompare shape comparison ->
        let bits = shapeBits shape
            apply a b = truthLane bits $ case comparison of
                IEqLanes -> a == b
                INeLanes -> a /= b
                ILtLanes sign -> numberOf sign bits a < numberOf sign bits b
                IGtLanes sign -> numberOf sign bits a > numberOf sign bits b
                ILeLanes sign -> numberOf sign bits a <= numberOf sign bits b
                IGeLanes sign -> numberOf sign bits a >= numberOf sign bits b
         in fromLanes bits (zipWith apply (lanes bits first) (lanes bits second))
    VFloatBinary shape floatOp ->
        let bits = floatBits shape
            apply = case floatOp of
                FAddLanes -> onFloats shape (+) (+)
                FSubLanes -> onFloats shape (-) (-)
                FMulLanes -> onFloats shape (*) (*)
                FDivLanes -> onFloats shape (/) (/)
                FMinLanes -> onFloats shape wasmMin wasmMin
                FMaxLanes -> onFloats shape wasmMax wasmMax
                -- The "pseudo" minimum and maximum: the second operand if it is smaller
                -- (larger) by the comparison, otherwise the first, NaNs and zeros included.
                FPMin -> \a b -> if comparingFloats shape (<) (<) b a then b else a
                FPMax -> \a b -> if comparingFloats shape (<) (<) a b then b else a
         in fromLanes bits (zipWith apply (lanes bits first) (lanes bits second))
    VFloatCompare shape comparison ->
        let bits = floatBits shape
            holds = case comparison of
                FEqLanes -> comparingFloats shape (==) (==)
                FNeLanes -> comparingFloats shape (/=) (/=)
                FLtLanes -> comparingFloats shape (<) (<)
                FGtLanes -> comparingFloats shape (>) (>)
                FLeLanes -> comparingFloats shape (<=) (<=)
                FGeLanes -> comparingFloats shape (>=) (>=)
         in fromLanes bits (zipWith (\a b -> truthLane bits (holds a b)) (lanes bits first) (lanes bits second))
    VNarrow shape sign ->
        let from = shapeBits (wider shape)
            bits = shapeBits shape
         in fromLanes bits [saturateLane sign bits (signedLane from value) | value <- lanes from first ++ lanes from second]
    VExtMul shape half sign ->
        let from = shapeBits (narrower shape)
            bits = shapeBits shape
         in fromLanes bits [wrapLane bits (numberOf sign from a * numberOf sign from b) | (a, b) <- zip (pick half (lanes from first)) (pick half (lanes from second))]
    VDot ->
        let products = [signedLane 16 a * signedLane 16 b | (a, b) <- zip (lanes 16 first) (lanes 16 second)]
         in fromLanes 32 [wrapLane 32 (a + b) | (a, b) <- pairs products]
    VQ15MulrSat ->
        fromLanes 16 [saturateLane Signed 16 ((signedLane 16 a * signedLane 16 b + 0x4000) `div` 0x8000) | (a, b) <- zip (lanes 16 first) (lanes 16 second)]

-- | @v128.bitselect@: each bit from the first vector where the mask has a one, from the second elsewhere.
vectorBitselect :: Vector128 -> Vector128 -> Vector128 -> Vector128
vectorBitselect (Vector128 firstLow firstHigh) (Vector128 secondLow secondHigh) (Vector128 maskLow maskHigh) =
    Vector128 ((firstLow .&. maskLow) .|. (secondLow .&. complement maskLow)) ((firstHigh .&. maskHigh) .|. (secondHigh .&. complement maskHigh))

vectorTest :: VectorTest -> Vector128 -> Word32
vectorTest test vector@(Vector128 low high) = case test of
    VAnyTrue -> if low /= 0 || high /= 0 then 1 else 0
    VAllTrue shape -> if 0 `notElem` lanes (shapeBits shape) vector then 1 else 0
    VBitmask shape ->
        let bits = shapeBits shape
         in foldr (.|.) 0 [1 `shiftL` i | (i, value) <- zip [0 ..] (lanes bits vector), testBit value (bits - 1)]

-- | A shift of every lane by a count taken modulo the lane's width.
vectorShift :: VectorShift -> Vector128 -> Word32 -> Vector128
vectorShift shift vector count = case shift of
    VShl shape -> shifted shape (\bits by value -> wrapLane bits (toInteger value * 2 ^ by))
    VShr shape sign -> shifted shape (\bits by value -> wrapLane bits (numberOf sign bits value `div` 2 ^ by))
  where
    shifted shape apply =
        let bits = shapeBits shape
            by = fromIntegral count `mod` bits
         in fromLanes bits (map (apply bits by) (lanes bits vector))

-- *** Lanes and scalars ***

-- | The width in bits of a lane of a type.
laneBits :: LaneType t -> Int
laneBits lane = case lane of
    LaneI8 -> 8
    LaneI16 -> 16
    LaneI32 -> 32
    LaneI64 -> 64
    LaneF32 -> 32
    LaneF64 -> 64

-- | A scalar as the bits of a lane, and a lane's bits as a scalar (extended as the sign says).
scalarBits :: LaneType t -> HostType t -> Word64
scalarBits lane value = case lane of
    LaneI8 -> fromIntegral value .&. 0xFF
    LaneI16 -> fromIntegral value .&. 0xFFFF
    LaneI32 -> fromIntegral value
    LaneI64 -> value
    LaneF32 -> fromIntegral (castFloatToWord32 value)
    LaneF64 -> castDoubleToWord64 value

bitsScalar :: LaneType t -> Signedness -> Word64 -> HostType t
bitsScalar lane sign value = case lane of
    LaneI8 -> fromInteger (numberOf sign 8 value `mod` 2 ^ (32 :: Int))
    LaneI16 -> fromInteger (numberOf sign 16 value `mod` 2 ^ (32 :: Int))
    LaneI32 -> fromIntegral value
    LaneI64 -> value
    LaneF32 -> castWord32ToFloat (fromIntegral value)
    LaneF64 -> castWord64ToDouble value

splatLane :: LaneType t -> HostType t -> Vector128
splatLane lane value = fromLanes (laneBits lane) (replicate (128 `div` laneBits lane) (scalarBits lane value))

extractLane :: LaneType t -> Word8 -> Signedness -> Vector128 -> HostType t
extractLane lane index sign vector = bitsScalar lane sign (lanes (laneBits lane) vector !! fromIntegral index)

replaceLane :: LaneType t -> Word8 -> Vector128 -> HostType t -> Vector128
replaceLane lane index vector value = replaceLaneBits (laneBits lane) index vector (scalarBits lane value)

-- | A vector with one lane, at a width in bits, replaced by the given bits.
replaceLaneBits :: Int -> Word8 -> Vector128 -> Word64 -> Vector128
replaceLaneBits bits index vector value =
    fromLanes bits [if i == index then value else old | (i, old) <- zip [0 ..] (lanes bits vector)]

-- *** Memory ***

{- | The vector a load makes of the bytes it read, given as the little-endian words of the
  first eight bytes and, for a whole vector, of the next eight.
-}
loadedVector :: VectorLoadKind -> Word64 -> Word64 -> Vector128
loadedVector kind low high = case kind of
    LoadWhole -> Vector128 low high
    LoadExtend shape sign ->
        let from = shapeBits (narrower shape)
         in fromLanes (shapeBits shape) [wrapLane (shapeBits shape) (numberOf sign from value) | value <- take (64 `div` from) (lanes from (Vector128 low 0))]
    LoadSplat width -> fromLanes (8 * laneBytes width) (replicate (16 `div` laneBytes width) low)
    LoadZero width -> Vector128 (low .&. maskOf (8 * laneBytes width)) 0

-- | The bits of one lane of a vector, at a width in bits.
laneBitsAt :: Int -> Word8 -> Vector128 -> Word64
laneBitsAt bits index vector = lanes bits vector !! fromIntegral index
