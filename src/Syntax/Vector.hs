{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

{- | The vector instructions of WebAssembly 2.0 (fixed-width SIMD), other than those that touch
  memory: about two hundred opcodes over one value type, @v128@. They are kept out of the
  instruction type as one family, 'VectorOp', indexed by the types of its operands and of its
  result, so that the typed AST needs one constructor per number of operands
  ('Syntax.Instructions.IVector1' and its siblings) and the rule for all of them is the rule of
  a numeric operation: the result is as secret as the operands and the pc.

  An operation says what it does lane by lane: a vector is read as lanes of a 'Shape', and
  the operations on a shape are enumerations ('IntBinary', 'FloatBinary', …). Not every
  combination is an opcode (there is no @i64x2.min_s@); the decoder builds only those that
  are, and "Runtime.Vector" gives every combination its lane-wise meaning.
-}
module Syntax.Vector (
    Shape (..),
    FloatShape (..),
    Half (..),
    LaneType (..),
    laneSing,
    laneCount,
    VectorOp (..),
    SomeVectorOp (..),
    VectorUnary (..),
    VectorBinary (..),
    VectorTernary (..),
    VectorTest (..),
    VectorShift (..),
    IntUnary (..),
    IntBinary (..),
    IntCompare (..),
    FloatUnary (..),
    FloatBinary (..),
    FloatCompare (..),
    VectorLoadKind (..),
    loadedBytes,
    LaneWidth (..),
    laneBytes,
) where

import Data.Singletons (Sing)
import Data.Word (Word8)

import Syntax.Immediates (Signedness, Vector128)
import Syntax.Types (SValType (..), ValType (..))

-- | How a vector is read as integer lanes: 16 of 8 bits, 8 of 16, 4 of 32 or 2 of 64.
data Shape = I8x16 | I16x8 | I32x4 | I64x2 deriving stock (Eq, Show)

-- | How a vector is read as floating-point lanes.
data FloatShape = F32x4 | F64x2 deriving stock (Eq, Show)

-- | The low or the high half of a vector's lanes, for the operations that widen them.
data Half = LowHalf | HighHalf deriving stock (Eq, Show)

{- | A kind of lane together with the scalar type it is exchanged with on the stack (@splat@,
  @extract_lane@, @replace_lane@): 8- and 16-bit lanes travel as @i32@.
-}
data LaneType (t :: ValType) where
    LaneI8 :: LaneType 'I32
    LaneI16 :: LaneType 'I32
    LaneI32 :: LaneType 'I32
    LaneI64 :: LaneType 'I64
    LaneF32 :: LaneType 'F32
    LaneF64 :: LaneType 'F64

-- | The scalar type a lane is exchanged at, as a singleton.
laneSing :: LaneType t -> Sing t
laneSing lane = case lane of
    LaneI8 -> SI32
    LaneI16 -> SI32
    LaneI32 -> SI32
    LaneI64 -> SI64
    LaneF32 -> SF32
    LaneF64 -> SF64

-- | How many lanes of this type a vector has.
laneCount :: LaneType t -> Word8
laneCount lane = case lane of
    LaneI8 -> 16
    LaneI16 -> 8
    LaneI32 -> 4
    LaneI64 -> 2
    LaneF32 -> 4
    LaneF64 -> 2

{- | A vector instruction that does not touch memory, by the value types of its operands (the
  top of the stack first) and of its result.
-}
data VectorOp (operands :: [ValType]) (result :: ValType) where
    VConst :: Vector128 -> VectorOp '[] 'V128
    VUnary :: VectorUnary -> VectorOp '[ 'V128] 'V128
    VBinary :: VectorBinary -> VectorOp '[ 'V128, 'V128] 'V128
    -- | @v128.bitselect@: operands, top first, are the mask, then the two vectors
    VBitselect :: VectorOp '[ 'V128, 'V128, 'V128] 'V128
    VTernary :: VectorTernary -> VectorOp '[ 'V128, 'V128, 'V128] 'V128
    VTest :: VectorTest -> VectorOp '[ 'V128] 'I32
    -- | a shift: the count is on top of the vector
    VShift :: VectorShift -> VectorOp '[ 'I32, 'V128] 'V128
    VSplat :: LaneType t -> VectorOp '[t] 'V128
    -- | the lane index, and how a lane narrower than its scalar type is extended
    VExtract :: LaneType t -> Word8 -> Signedness -> VectorOp '[ 'V128] t
    VReplace :: LaneType t -> Word8 -> VectorOp '[t, 'V128] 'V128

-- | A vector operation with its operand and result types as singletons: what the decoder produces.
data SomeVectorOp where
    SomeVectorOp :: Sing operands -> Sing result -> VectorOp operands result -> SomeVectorOp

data VectorUnary
    = VNot
    | VIntUnary Shape IntUnary
    | VFloatUnary FloatShape FloatUnary
    | -- | widen the low or high half of the lanes of the next narrower shape to this one
      VExtend Shape Half Signedness
    | -- | add adjacent pairs of lanes of the next narrower shape into lanes of this one
      VExtAddPairwise Shape Signedness
    | -- | @i32x4.trunc_sat_f32x4@
      VTruncSatF32x4 Signedness
    | -- | @i32x4.trunc_sat_f64x2_zero@: two lanes converted, two zero
      VTruncSatF64x2Zero Signedness
    | -- | @f32x4.convert_i32x4@
      VConvertI32x4 Signedness
    | -- | @f64x2.convert_low_i32x4@
      VConvertLowI32x4 Signedness
    | VDemoteF64x2Zero
    | VPromoteLowF32x4
    deriving stock (Eq, Show)

data VectorBinary
    = VAnd
    | VAndNot
    | VOr
    | VXor
    | -- | @i8x16.swizzle@: the second operand selects bytes of the first
      VSwizzle
    | -- | @i8x16.shuffle@ with its sixteen lane indices into the two operands
      VShuffle [Word8]
    | VIntBinary Shape IntBinary
    | VIntCompare Shape IntCompare
    | VFloatBinary FloatShape FloatBinary
    | VFloatCompare FloatShape FloatCompare
    | -- | narrow the lanes of the next wider shape into this one, saturating
      VNarrow Shape Signedness
    | -- | multiply the low or high halves of the next narrower shape into lanes of this one
      VExtMul Shape Half Signedness
    | -- | @i32x4.dot_i16x8_s@
      VDot
    | -- | @i16x8.q15mulr_sat_s@
      VQ15MulrSat
    | -- | @i16x8.relaxed_dot_i8x16_i7x16_s@: the products of adjacent pairs of bytes, added
      VDotBytes
    deriving stock (Eq, Show)

{- | The relaxed vector instructions of WebAssembly 3.0 with three operands, written here for
  operands @a@, @b@, @c@ with @c@ on top. The specification lets an implementation choose among
  a few results for a relaxed instruction, the same choice every time; ours are the ones named
  here. The other relaxed instructions are decoded as the instructions of 2.0 that give one of
  their permitted results (@relaxed_swizzle@ as @swizzle@, and so on; see "Codec.Wasm").
-}
data VectorTernary
    = -- | @relaxed_madd@: @a * b + c@, the product rounded before the sum
      VMulAdd FloatShape
    | -- | @relaxed_nmadd@: @-(a * b) + c@
      VNegMulAdd FloatShape
    | -- | @i32x4.relaxed_dot_i8x16_i7x16_add_s@: the products of the bytes of @a@ and @b@, added in fours, plus @c@
      VDotBytesAdd
    deriving stock (Eq, Show)

data VectorTest
    = VAnyTrue
    | VAllTrue Shape
    | VBitmask Shape
    deriving stock (Eq, Show)

data VectorShift = VShl Shape | VShr Shape Signedness deriving stock (Eq, Show)

data IntUnary = IAbs | INeg | IPopcnt deriving stock (Eq, Show)

data IntBinary
    = IAddLanes
    | ISubLanes
    | IMulLanes
    | IAddSat Signedness
    | ISubSat Signedness
    | IMinLanes Signedness
    | IMaxLanes Signedness
    | IAvgr
    deriving stock (Eq, Show)

data IntCompare = IEqLanes | INeLanes | ILtLanes Signedness | IGtLanes Signedness | ILeLanes Signedness | IGeLanes Signedness
    deriving stock (Eq, Show)

data FloatUnary = FAbsLanes | FNegLanes | FSqrtLanes | FCeilLanes | FFloorLanes | FTruncLanes | FNearestLanes
    deriving stock (Eq, Show)

data FloatBinary = FAddLanes | FSubLanes | FMulLanes | FDivLanes | FMinLanes | FMaxLanes | FPMin | FPMax
    deriving stock (Eq, Show)

data FloatCompare = FEqLanes | FNeLanes | FLtLanes | FGtLanes | FLeLanes | FGeLanes
    deriving stock (Eq, Show)

{- | What a vector load reads and how it becomes a vector: all sixteen bytes; eight bytes whose
  lanes are each widened to twice their width; one lane copied to every lane; or one lane in
  the low bits and zero elsewhere.
-}
data VectorLoadKind
    = LoadWhole
    | -- | the shape of the result, whose lanes come from lanes half as wide
      LoadExtend Shape Signedness
    | LoadSplat LaneWidth
    | LoadZero LaneWidth
    deriving stock (Eq, Show)

-- | How many bytes a vector load reads.
loadedBytes :: VectorLoadKind -> Int
loadedBytes kind = case kind of
    LoadWhole -> 16
    LoadExtend _ _ -> 8
    LoadSplat width -> laneBytes width
    LoadZero width -> laneBytes width

-- | The width of one lane in memory, for the loads and stores of a single lane.
data LaneWidth = Lane8 | Lane16 | Lane32 | Lane64 deriving stock (Eq, Show)

laneBytes :: LaneWidth -> Int
laneBytes width = case width of
    Lane8 -> 1
    Lane16 -> 2
    Lane32 -> 4
    Lane64 -> 8
