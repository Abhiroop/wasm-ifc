{-# LANGUAGE DataKinds #-}

{- | A decoder from the WebAssembly binary format into the raw AST.

Only the instruction subset declared in "Syntax.Instructions" is recognised; any other
opcode, and any feature outside the subset (imported tables, memories and globals;
reference and vector types; element segments in the forms that need them), fails the decode
with a message starting @unsupported@. Everything the format itself requires is checked:
integer encodings, section order and uniqueness, section and code-entry sizes, UTF-8 names.
-}
module Codec.Wasm (
    decodeModule,
) where

import Control.Monad (replicateM, unless, when)
import Data.Binary.Get (
    Get,
    getByteString,
    getRemainingLazyByteString,
    getWord32le,
    getWord64le,
    getWord8,
    isEmpty,
    isolate,
    runGetOrFail,
 )
import Data.Bits (shiftL, shiftR, testBit, (.&.), (.|.))
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BL
import Data.Int (Int32, Int64)
import Data.List (elemIndex)
import Data.Maybe (isJust)
import Data.Singletons.Base.TH (SList (SCons, SNil), Sing)
import Data.Text (Text)
import Data.Text.Encoding (decodeUtf8')
import Data.Word (Word32, Word64, Word8)
import GHC.Float (castWord32ToFloat, castWord64ToDouble)
import Numeric (showHex)

import Syntax.Functions (RawFunction (RawFunction))
import Syntax.Globals (RawGlobal (RawGlobal))
import Syntax.Immediates
import Syntax.Indices
import Syntax.Instructions
import Syntax.Module
import Syntax.Types
import Syntax.Vector

-- | Decode a complete module from its binary representation.
decodeModule :: BL.ByteString -> Either String RawModule
decodeModule bytes = case runGetOrFail getModule bytes of
    Left (_, _, err) -> Left err
    Right (_, _, decoded) -> Right decoded

-- *** LEB128 ***

{- | Unsigned LEB128 for an integer of @bits@ bits: at most @ceil(bits/7)@ bytes ("integer
  representation too long" beyond that), and the unused high bits of the last byte must be
  zero ("integer too large"), as the binary format requires.
-}
getUnsignedLeb :: Int -> Get Word64
getUnsignedLeb bits = go 0 0
  where
    maxBytes = (bits + 6) `div` 7
    go shift acc = do
        when (shift `div` 7 >= maxBytes) (fail "integer representation too long")
        byte <- getWord8
        let payload = byte .&. 0x7F
            remainingBits = bits - shift
        when (remainingBits < 7 && payload `shiftR` remainingBits /= 0) (fail "integer too large")
        let acc' = acc .|. (fromIntegral payload `shiftL` shift)
        if testBit byte 7 then go (shift + 7) acc' else pure acc'

{- | Signed LEB128 for an integer of @bits@ bits, sign-extended: the same length bound, and
  the unused bits of the last byte must all equal the value's sign bit.
-}
getSignedLeb :: Int -> Get Int64
getSignedLeb bits = go 0 0
  where
    maxBytes = (bits + 6) `div` 7
    go shift acc = do
        when (shift `div` 7 >= maxBytes) (fail "integer representation too long")
        byte <- getWord8
        let payload = byte .&. 0x7F
            acc' = acc .|. (fromIntegral payload `shiftL` shift)
            shift' = shift + 7
            remainingBits = bits - shift
        if testBit byte 7
            then go shift' acc'
            else do
                when (remainingBits < 7) $ do
                    let unusedMask = (0x7F `shiftL` remainingBits) .&. 0x7F
                        signExtension = if testBit payload (remainingBits - 1) then unusedMask else 0
                    when (payload .&. unusedMask /= signExtension) (fail "integer too large")
                pure (if shift' < 64 && testBit byte 6 then acc' .|. ((-1) `shiftL` shift') else acc')

-- | The @u32@ used for every count, size and index.
getULEB128 :: Get Word32
getULEB128 = fromIntegral <$> getUnsignedLeb 32

getS32 :: Get Int32
getS32 = fromIntegral <$> getSignedLeb 32

-- | Block types are encoded as @s33@ (negative for the short forms, a type index otherwise).
getS33 :: Get Int64
getS33 = getSignedLeb 33

getS64 :: Get Int64
getS64 = getSignedLeb 64

-- | A length-prefixed vector.
getVec :: Get a -> Get [a]
getVec getItem = do
    count <- getULEB128
    replicateM (fromIntegral count) getItem

-- | A length-prefixed UTF-8 name (rejected, not thrown, when the bytes are not UTF-8).
getName :: Get Text
getName = do
    count <- getULEB128
    bytes <- getByteString (fromIntegral count)
    either (const (fail "malformed UTF-8 encoding")) pure (decodeUtf8' bytes)

-- *** Types ***

-- | A value type as the module writes it.
getWrittenType :: Get WrittenType
getWrittenType = do
    byte <- getWord8
    case byte of
        0x7F -> pure (Plain I32)
        0x7E -> pure (Plain I64)
        0x7D -> pure (Plain F32)
        0x7C -> pure (Plain F64)
        0x7B -> pure (Plain V128)
        -- A reference to a heap type, not null or possibly null (the typed function references of 3.0).
        0x64 -> RefTo False <$> getHeapType
        0x63 -> RefTo True <$> getHeapType
        -- (An abstract heap type alone is the reference to it that may be null.)
        _ -> maybe (fail ("unknown valtype byte 0x" ++ showHex byte "")) (fmap (RefTo True) . abstractHeapType) (lookup (fromIntegral byte - 0x80) abstractHeapTypes)

-- | A heap type: one of the module's function types, by its index, or an abstract one.
getHeapType :: Get HeapType
getHeapType = do
    code <- getS33
    if code >= 0 then pure (OfType (fromIntegral code)) else maybe (fail ("unknown heap type " ++ show code)) abstractHeapType (lookup code abstractHeapTypes)

-- | The abstract heap types, by their code as a signed number; none for those of garbage collection.
abstractHeapTypes :: [(Int64, Maybe HeapType)]
abstractHeapTypes =
    [ (-16, Just AnyFunction)
    , (-13, Just NoFunction)
    , (-17, Just AnyExtern)
    , (-14, Just NoExtern)
    , (-23, Just AnyException)
    , (-12, Just NoException)
    , (-15, Nothing)
    , (-18, Nothing)
    , (-19, Nothing)
    , (-20, Nothing)
    , (-21, Nothing)
    , (-22, Nothing)
    ]

abstractHeapType :: Maybe HeapType -> Get HeapType
abstractHeapType = maybe (fail "unsupported: a heap type of garbage collection") pure

getFuncType :: Get (FuncTypeOf WrittenType)
getFuncType = do
    form <- getWord8
    when (form /= 0x60) (fail ("expected functype (0x60), got 0x" ++ showHex form ""))
    FuncType <$> getVec getWrittenType <*> getVec getWrittenType

{- | The limits of a memory or a table, with its address type: bit 0 of the flag says that a
  maximum follows, bit 2 that the addresses and the limits are 64 bits wide. (Bit 1 is the
  threads proposal's shared memory.)
-}
getLimits :: Get (AddrType, Limits)
getLimits = do
    flag <- getWord8
    case flag of
        0x00 -> (,) AddrI32 <$> (Limits . fromIntegral <$> getULEB128 <*> pure Nothing)
        0x01 -> (,) AddrI32 <$> (Limits . fromIntegral <$> getULEB128 <*> (Just . fromIntegral <$> getULEB128))
        0x04 -> (,) AddrI64 <$> (Limits <$> getUnsignedLeb 64 <*> pure Nothing)
        0x05 -> (,) AddrI64 <$> (Limits <$> getUnsignedLeb 64 <*> (Just <$> getUnsignedLeb 64))
        _ -> fail ("unknown limits flag 0x" ++ showHex flag "")

-- | A global's type, and the type of its value as the module writes it.
getWrittenGlobalType :: Get (GlobalType, WrittenType)
getWrittenGlobalType = do
    valType <- getWrittenType
    mutability <- getWord8
    case mutability of
        0x00 -> pure (GlobalType Immutable (erasedType valType), valType)
        0x01 -> pure (GlobalType Mutable (erasedType valType), valType)
        _ -> fail ("unknown mutability 0x" ++ showHex mutability "")

{- | A block type is either empty, a single result type, or a reference to a function
  type in the type section. The three cases are distinguished by a signed encoding.
-}
getBlockType :: [FuncType] -> Get (BlockType, Maybe WrittenNote)
getBlockType types = do
    code <- getS33
    case code of
        -64 -> pure (FuncType [] [], Nothing)
        -1 -> pure (FuncType [] [I32], Nothing)
        -2 -> pure (FuncType [] [I64], Nothing)
        -3 -> pure (FuncType [] [F32], Nothing)
        -4 -> pure (FuncType [] [F64], Nothing)
        -5 -> pure (FuncType [] [V128], Nothing)
        -28 -> oneResult . RefTo False <$> getHeapType
        -29 -> oneResult . RefTo True <$> getHeapType
        n | Just known <- lookup n abstractHeapTypes -> oneResult . RefTo True <$> abstractHeapType known
        n -> case nth types (fromIntegral n) of
            Just ft -> pure (ft, Just (BlockOfType (fromIntegral n)))
            Nothing -> fail ("block type index out of range: " ++ show n)
  where
    oneResult result = (FuncType [] [erasedType result], Just (BlockResult result))

-- | An instruction with the note of what the module wrote, if it wrote more than the instruction keeps.
noted :: Maybe WrittenNote -> RawInstr -> RawInstr
noted = maybe id Precisely

{- | Total list indexing (@Nothing@ if out of range), so a malformed index in the binary
  becomes a decode error rather than a crash.
-}
nth :: [a] -> Int -> Maybe a
nth xs i
    | i < 0 = Nothing
    | otherwise = case drop i xs of x : _ -> Just x; [] -> Nothing

{- | A memory access's alignment, memory and offset. Bit 6 of the alignment field says that a
  memory index follows (otherwise the memory is 0), and a field of 128 or more is malformed.
  The offset is a @u64@, which validation bounds by the address type of the memory.
-}
getMemArg :: Get MemArg
getMemArg = do
    flags <- getULEB128
    when (flags >= 128) (fail "malformed memop flags")
    memory <- if flags >= 64 then getULEB128 else pure 0
    offset <- getUnsignedLeb 64
    pure (MemArg (if flags >= 64 then flags - 64 else flags) offset memory)

-- *** Instructions ***

{- | Read instructions up to (and consuming) a terminator byte — @end@ (0x0B) or
  @else@ (0x05) — returning the instructions and which terminator was seen.
-}
getBlockBody :: Bool -> [FuncType] -> Get ([RawInstr], Word8)
getBlockBody hasDataCount types = go []
  where
    go acc = do
        opcode <- getWord8
        if opcode == 0x0B || opcode == 0x05
            then pure (reverse acc, opcode)
            else do
                instr <- getInstr hasDataCount types opcode
                go (instr : acc)

-- | An expression: instructions up to a terminating @end@.
getExpr :: Bool -> [FuncType] -> Get [RawInstr]
getExpr hasDataCount types = fst <$> getBlockBody hasDataCount types

-- | Decode one (non-terminator) instruction whose opcode byte has already been read.
getInstr :: Bool -> [FuncType] -> Word8 -> Get RawInstr
getInstr hasDataCount types opcode = case opcode of
    {- Control -}
    0x00 -> pure Unreachable
    0x01 -> pure Nop
    0x02 -> (\(blockType, note) body -> noted note (Block blockType body)) <$> getBlockType types <*> getExpr hasDataCount types
    0x03 -> (\(blockType, note) body -> noted note (Loop blockType body)) <$> getBlockType types <*> getExpr hasDataCount types
    0x04 -> do
        (blockType, note) <- getBlockType types
        (thenArm, term) <- getBlockBody hasDataCount types
        elseArm <- if term == 0x05 then getExpr hasDataCount types else pure []
        pure (noted note (If blockType thenArm elseArm))
    0x08 -> Throw . TagIdx <$> getULEB128
    0x0A -> pure ThrowRef
    0x1F -> (\(blockType, note) clauses body -> noted note (TryTable blockType clauses body)) <$> getBlockType types <*> getVec getCatch <*> getExpr hasDataCount types
    0x0C -> Br . LabelIdx <$> getULEB128
    0x0D -> BrIf . LabelIdx <$> getULEB128
    0x0E -> BrTable <$> getVec (LabelIdx <$> getULEB128) <*> (LabelIdx <$> getULEB128)
    0x0F -> pure Return
    0x10 -> Call . FunctionIdx <$> getULEB128
    0x11 -> do
        typeIdx <- getULEB128
        tableIdx <- getULEB128
        pure (CallIndirect (TableIdx tableIdx) (TypeIdx typeIdx))
    0x12 -> ReturnCall . FunctionIdx <$> getULEB128
    0x14 -> CallRef . TypeIdx <$> getULEB128
    0x15 -> ReturnCallRef . TypeIdx <$> getULEB128
    0x13 -> do
        typeIdx <- getULEB128
        tableIdx <- getULEB128
        pure (ReturnCallIndirect (TableIdx tableIdx) (TypeIdx typeIdx))
    {- Locals & globals -}
    0x20 -> LocalGet . LocalIdx <$> getULEB128
    0x21 -> LocalSet . LocalIdx <$> getULEB128
    0x22 -> LocalTee . LocalIdx <$> getULEB128
    0x23 -> GlobalGet . GlobalIdx <$> getULEB128
    0x24 -> GlobalSet . GlobalIdx <$> getULEB128
    {- Memory loads & stores -}
    0x28 -> Load SI32 <$> getMemArg
    0x29 -> Load SI64 <$> getMemArg
    0x2A -> Load SF32 <$> getMemArg
    0x2B -> Load SF64 <$> getMemArg
    0x2C -> LoadN SI32 1 Signed <$> getMemArg
    0x2D -> LoadN SI32 1 Unsigned <$> getMemArg
    0x2E -> LoadN SI32 2 Signed <$> getMemArg
    0x2F -> LoadN SI32 2 Unsigned <$> getMemArg
    0x30 -> LoadN SI64 1 Signed <$> getMemArg
    0x31 -> LoadN SI64 1 Unsigned <$> getMemArg
    0x32 -> LoadN SI64 2 Signed <$> getMemArg
    0x33 -> LoadN SI64 2 Unsigned <$> getMemArg
    0x34 -> LoadN SI64 4 Signed <$> getMemArg
    0x35 -> LoadN SI64 4 Unsigned <$> getMemArg
    0x36 -> Store SI32 <$> getMemArg
    0x37 -> Store SI64 <$> getMemArg
    0x38 -> Store SF32 <$> getMemArg
    0x39 -> Store SF64 <$> getMemArg
    0x3A -> StoreN SI32 1 <$> getMemArg
    0x3B -> StoreN SI32 2 <$> getMemArg
    0x3C -> StoreN SI64 1 <$> getMemArg
    0x3D -> StoreN SI64 2 <$> getMemArg
    0x3E -> StoreN SI64 4 <$> getMemArg
    0x3F -> MemorySize . MemoryIdx <$> getULEB128
    0x40 -> MemoryGrow . MemoryIdx <$> getULEB128
    {- Constants -}
    0x41 -> Const SI32 . fromIntegral <$> getS32
    0x42 -> Const SI64 . fromIntegral <$> getS64
    0x43 -> Const SF32 . castWord32ToFloat <$> getWord32le
    0x44 -> Const SF64 . castWord64ToDouble <$> getWord64le
    {- Comparison: i32 -}
    0x45 -> pure (Eqz SI32)
    0x46 -> pure (Eq SI32)
    0x47 -> pure (Ne SI32)
    0x48 -> pure (Lt SI32 Signed)
    0x49 -> pure (Lt SI32 Unsigned)
    0x4A -> pure (Gt SI32 Signed)
    0x4B -> pure (Gt SI32 Unsigned)
    0x4C -> pure (Le SI32 Signed)
    0x4D -> pure (Le SI32 Unsigned)
    0x4E -> pure (Ge SI32 Signed)
    0x4F -> pure (Ge SI32 Unsigned)
    {- Comparison: i64 -}
    0x50 -> pure (Eqz SI64)
    0x51 -> pure (Eq SI64)
    0x52 -> pure (Ne SI64)
    0x53 -> pure (Lt SI64 Signed)
    0x54 -> pure (Lt SI64 Unsigned)
    0x55 -> pure (Gt SI64 Signed)
    0x56 -> pure (Gt SI64 Unsigned)
    0x57 -> pure (Le SI64 Signed)
    0x58 -> pure (Le SI64 Unsigned)
    0x59 -> pure (Ge SI64 Signed)
    0x5A -> pure (Ge SI64 Unsigned)
    {- Comparison: f32 / f64 (signedness is irrelevant for floats) -}
    0x5B -> pure (Eq SF32)
    0x5C -> pure (Ne SF32)
    0x5D -> pure (Lt SF32 Signed)
    0x5E -> pure (Gt SF32 Signed)
    0x5F -> pure (Le SF32 Signed)
    0x60 -> pure (Ge SF32 Signed)
    0x61 -> pure (Eq SF64)
    0x62 -> pure (Ne SF64)
    0x63 -> pure (Lt SF64 Signed)
    0x64 -> pure (Gt SF64 Signed)
    0x65 -> pure (Le SF64 Signed)
    0x66 -> pure (Ge SF64 Signed)
    {- Numeric: i32 -}
    0x67 -> pure (Clz SI32)
    0x68 -> pure (Ctz SI32)
    0x69 -> pure (Popcnt SI32)
    0x6A -> pure (Add SI32)
    0x6B -> pure (Sub SI32)
    0x6C -> pure (Mul SI32)
    0x6D -> pure (Div SI32 Signed)
    0x6E -> pure (Div SI32 Unsigned)
    0x6F -> pure (Rem SI32 Signed)
    0x70 -> pure (Rem SI32 Unsigned)
    0x71 -> pure (And SI32)
    0x72 -> pure (Or SI32)
    0x73 -> pure (Xor SI32)
    0x74 -> pure (Shl SI32)
    0x75 -> pure (Shr SI32 Signed)
    0x76 -> pure (Shr SI32 Unsigned)
    0x77 -> pure (Rotl SI32)
    0x78 -> pure (Rotr SI32)
    {- Numeric: i64 -}
    0x79 -> pure (Clz SI64)
    0x7A -> pure (Ctz SI64)
    0x7B -> pure (Popcnt SI64)
    0x7C -> pure (Add SI64)
    0x7D -> pure (Sub SI64)
    0x7E -> pure (Mul SI64)
    0x7F -> pure (Div SI64 Signed)
    0x80 -> pure (Div SI64 Unsigned)
    0x81 -> pure (Rem SI64 Signed)
    0x82 -> pure (Rem SI64 Unsigned)
    0x83 -> pure (And SI64)
    0x84 -> pure (Or SI64)
    0x85 -> pure (Xor SI64)
    0x86 -> pure (Shl SI64)
    0x87 -> pure (Shr SI64 Signed)
    0x88 -> pure (Shr SI64 Unsigned)
    0x89 -> pure (Rotl SI64)
    0x8A -> pure (Rotr SI64)
    {- Numeric: f32 -}
    0x8B -> pure (Abs SF32)
    0x8C -> pure (Neg SF32)
    0x8D -> pure (Ceil SF32)
    0x8E -> pure (Floor SF32)
    0x8F -> pure (FloatTrunc SF32)
    0x90 -> pure (Nearest SF32)
    0x91 -> pure (Sqrt SF32)
    0x92 -> pure (Add SF32)
    0x93 -> pure (Sub SF32)
    0x94 -> pure (Mul SF32)
    0x95 -> pure (Div SF32 Signed)
    0x96 -> pure (Min SF32)
    0x97 -> pure (Max SF32)
    0x98 -> pure (Copysign SF32)
    {- Numeric: f64 -}
    0x99 -> pure (Abs SF64)
    0x9A -> pure (Neg SF64)
    0x9B -> pure (Ceil SF64)
    0x9C -> pure (Floor SF64)
    0x9D -> pure (FloatTrunc SF64)
    0x9E -> pure (Nearest SF64)
    0x9F -> pure (Sqrt SF64)
    0xA0 -> pure (Add SF64)
    0xA1 -> pure (Sub SF64)
    0xA2 -> pure (Mul SF64)
    0xA3 -> pure (Div SF64 Signed)
    0xA4 -> pure (Min SF64)
    0xA5 -> pure (Max SF64)
    0xA6 -> pure (Copysign SF64)
    {- Conversions -}
    0xA7 -> pure (Convert I32WrapI64)
    0xA8 -> pure (Convert (I32TruncF32 Signed))
    0xA9 -> pure (Convert (I32TruncF32 Unsigned))
    0xAA -> pure (Convert (I32TruncF64 Signed))
    0xAB -> pure (Convert (I32TruncF64 Unsigned))
    0xAC -> pure (Convert (I64ExtendI32 Signed))
    0xAD -> pure (Convert (I64ExtendI32 Unsigned))
    0xAE -> pure (Convert (I64TruncF32 Signed))
    0xAF -> pure (Convert (I64TruncF32 Unsigned))
    0xB0 -> pure (Convert (I64TruncF64 Signed))
    0xB1 -> pure (Convert (I64TruncF64 Unsigned))
    0xB2 -> pure (Convert (F32ConvertI32 Signed))
    0xB3 -> pure (Convert (F32ConvertI32 Unsigned))
    0xB4 -> pure (Convert (F32ConvertI64 Signed))
    0xB5 -> pure (Convert (F32ConvertI64 Unsigned))
    0xB6 -> pure (Convert F32DemoteF64)
    0xB7 -> pure (Convert (F64ConvertI32 Signed))
    0xB8 -> pure (Convert (F64ConvertI32 Unsigned))
    0xB9 -> pure (Convert (F64ConvertI64 Signed))
    0xBA -> pure (Convert (F64ConvertI64 Unsigned))
    0xBB -> pure (Convert F64PromoteF32)
    0xBC -> pure (Convert I32ReinterpretF32)
    0xBD -> pure (Convert I64ReinterpretF64)
    0xBE -> pure (Convert F32ReinterpretI32)
    0xBF -> pure (Convert F64ReinterpretI64)
    0xC0 -> pure (Convert I32Extend8S)
    0xC1 -> pure (Convert I32Extend16S)
    0xC2 -> pure (Convert I64Extend8S)
    0xC3 -> pure (Convert I64Extend16S)
    0xC4 -> pure (Convert I64Extend32S)
    {- Stack management -}
    0x1A -> pure Drop
    0x1B -> pure Select
    0x1C -> (\types' -> Precisely (SelectOf types') (SelectTyped (map erasedType types'))) <$> getVec getWrittenType
    {- References and tables -}
    0xD0 -> (\heap -> Precisely (NullOf heap) (RefNull (erasedType (RefTo True heap)))) <$> getHeapType
    0xD1 -> pure RefIsNull
    0xD2 -> RefFunc . FunctionIdx <$> getULEB128
    0xD4 -> pure RefAsNonNull
    0xD5 -> BrOnNull . LabelIdx <$> getULEB128
    0xD6 -> BrOnNonNull . LabelIdx <$> getULEB128
    0x25 -> TableGet . TableIdx <$> getULEB128
    0x26 -> TableSet . TableIdx <$> getULEB128
    {- The 0xFC prefix: saturating truncations (0–7); the rest is bulk memory -}
    0xFC -> do
        sub <- getULEB128
        case sub of
            0 -> pure (Convert (I32TruncSatF32 Signed))
            1 -> pure (Convert (I32TruncSatF32 Unsigned))
            2 -> pure (Convert (I32TruncSatF64 Signed))
            3 -> pure (Convert (I32TruncSatF64 Unsigned))
            4 -> pure (Convert (I64TruncSatF32 Signed))
            5 -> pure (Convert (I64TruncSatF32 Unsigned))
            6 -> pure (Convert (I64TruncSatF64 Signed))
            7 -> pure (Convert (I64TruncSatF64 Unsigned))
            8 -> do
                unless hasDataCount (fail "data count section required")
                MemoryInit . DataIdx <$> getULEB128 <*> (MemoryIdx <$> getULEB128)
            9 -> do
                unless hasDataCount (fail "data count section required")
                DataDrop . DataIdx <$> getULEB128
            10 -> MemoryCopy . MemoryIdx <$> getULEB128 <*> (MemoryIdx <$> getULEB128)
            11 -> MemoryFill . MemoryIdx <$> getULEB128
            12 -> TableInit . ElemIdx <$> getULEB128 <*> (TableIdx <$> getULEB128)
            13 -> ElemDrop . ElemIdx <$> getULEB128
            14 -> TableCopy . TableIdx <$> getULEB128 <*> (TableIdx <$> getULEB128)
            15 -> TableGrow . TableIdx <$> getULEB128
            16 -> TableSize . TableIdx <$> getULEB128
            17 -> TableFill . TableIdx <$> getULEB128
            _ -> fail ("unsupported: 0xFC opcode " ++ show sub)
    0xFD -> getVectorInstr
    _ -> fail ("unsupported opcode 0x" ++ showHex opcode "")

-- | A clause of a @try_table@.
getCatch :: Get Catch
getCatch = do
    kind <- getWord8
    case kind of
        0x00 -> CatchTag . TagIdx <$> getULEB128 <*> (LabelIdx <$> getULEB128)
        0x01 -> CatchTagRef . TagIdx <$> getULEB128 <*> (LabelIdx <$> getULEB128)
        0x02 -> CatchAll . LabelIdx <$> getULEB128
        0x03 -> CatchAllRef . LabelIdx <$> getULEB128
        _ -> fail ("unknown catch clause " ++ show kind)

{- | A vector instruction: the prefix @0xFD@ has been read, its own opcode follows as a @u32@.
  The table is the binary format's, in its order; the gaps are opcodes it reserves.
-}
getVectorInstr :: Get RawInstr
getVectorInstr = do
    opcode <- getULEB128
    case opcode of
        0x00 -> VectorLoad LoadWhole <$> getMemArg
        0x01 -> VectorLoad (LoadExtend I16x8 Signed) <$> getMemArg
        0x02 -> VectorLoad (LoadExtend I16x8 Unsigned) <$> getMemArg
        0x03 -> VectorLoad (LoadExtend I32x4 Signed) <$> getMemArg
        0x04 -> VectorLoad (LoadExtend I32x4 Unsigned) <$> getMemArg
        0x05 -> VectorLoad (LoadExtend I64x2 Signed) <$> getMemArg
        0x06 -> VectorLoad (LoadExtend I64x2 Unsigned) <$> getMemArg
        0x07 -> VectorLoad (LoadSplat Lane8) <$> getMemArg
        0x08 -> VectorLoad (LoadSplat Lane16) <$> getMemArg
        0x09 -> VectorLoad (LoadSplat Lane32) <$> getMemArg
        0x0A -> VectorLoad (LoadSplat Lane64) <$> getMemArg
        0x0B -> VectorStore <$> getMemArg
        0x0C -> (\low high -> operation SNil SV128 (VConst (Vector128 low high))) <$> getWord64le <*> getWord64le
        0x0D -> binary . VShuffle <$> replicateM 16 getWord8
        0x0E -> pure (binary VSwizzle)
        0x0F -> pure (splat LaneI8)
        0x10 -> pure (splat LaneI16)
        0x11 -> pure (splat LaneI32)
        0x12 -> pure (splat LaneI64)
        0x13 -> pure (splat LaneF32)
        0x14 -> pure (splat LaneF64)
        0x15 -> extract LaneI8 Signed
        0x16 -> extract LaneI8 Unsigned
        0x17 -> replace LaneI8
        0x18 -> extract LaneI16 Signed
        0x19 -> extract LaneI16 Unsigned
        0x1A -> replace LaneI16
        0x1B -> extract LaneI32 Unsigned
        0x1C -> replace LaneI32
        0x1D -> extract LaneI64 Unsigned
        0x1E -> replace LaneI64
        0x1F -> extract LaneF32 Unsigned
        0x20 -> replace LaneF32
        0x21 -> extract LaneF64 Unsigned
        0x22 -> replace LaneF64
        _ | opcode >= 0x23 && opcode <= 0x2C -> pure (binary (VIntCompare I8x16 (comparison (opcode - 0x23))))
        _ | opcode >= 0x2D && opcode <= 0x36 -> pure (binary (VIntCompare I16x8 (comparison (opcode - 0x2D))))
        _ | opcode >= 0x37 && opcode <= 0x40 -> pure (binary (VIntCompare I32x4 (comparison (opcode - 0x37))))
        _ | opcode >= 0x41 && opcode <= 0x46 -> pure (binary (VFloatCompare F32x4 (floatComparison (opcode - 0x41))))
        _ | opcode >= 0x47 && opcode <= 0x4C -> pure (binary (VFloatCompare F64x2 (floatComparison (opcode - 0x47))))
        0x4D -> pure (unary VNot)
        0x4E -> pure (binary VAnd)
        0x4F -> pure (binary VAndNot)
        0x50 -> pure (binary VOr)
        0x51 -> pure (binary VXor)
        0x52 -> pure (ternary VBitselect)
        0x53 -> pure (test VAnyTrue)
        0x54 -> laneAccess VectorLoadLane Lane8
        0x55 -> laneAccess VectorLoadLane Lane16
        0x56 -> laneAccess VectorLoadLane Lane32
        0x57 -> laneAccess VectorLoadLane Lane64
        0x58 -> laneAccess VectorStoreLane Lane8
        0x59 -> laneAccess VectorStoreLane Lane16
        0x5A -> laneAccess VectorStoreLane Lane32
        0x5B -> laneAccess VectorStoreLane Lane64
        0x5C -> VectorLoad (LoadZero Lane32) <$> getMemArg
        0x5D -> VectorLoad (LoadZero Lane64) <$> getMemArg
        0x5E -> pure (unary VDemoteF64x2Zero)
        0x5F -> pure (unary VPromoteLowF32x4)
        0x60 -> pure (unary (VIntUnary I8x16 IAbs))
        0x61 -> pure (unary (VIntUnary I8x16 INeg))
        0x62 -> pure (unary (VIntUnary I8x16 IPopcnt))
        0x63 -> pure (test (VAllTrue I8x16))
        0x64 -> pure (test (VBitmask I8x16))
        0x65 -> pure (binary (VNarrow I8x16 Signed))
        0x66 -> pure (binary (VNarrow I8x16 Unsigned))
        0x67 -> pure (unary (VFloatUnary F32x4 FCeilLanes))
        0x68 -> pure (unary (VFloatUnary F32x4 FFloorLanes))
        0x69 -> pure (unary (VFloatUnary F32x4 FTruncLanes))
        0x6A -> pure (unary (VFloatUnary F32x4 FNearestLanes))
        0x6B -> pure (shift (VShl I8x16))
        0x6C -> pure (shift (VShr I8x16 Signed))
        0x6D -> pure (shift (VShr I8x16 Unsigned))
        0x6E -> pure (intBinary I8x16 IAddLanes)
        0x6F -> pure (intBinary I8x16 (IAddSat Signed))
        0x70 -> pure (intBinary I8x16 (IAddSat Unsigned))
        0x71 -> pure (intBinary I8x16 ISubLanes)
        0x72 -> pure (intBinary I8x16 (ISubSat Signed))
        0x73 -> pure (intBinary I8x16 (ISubSat Unsigned))
        0x74 -> pure (unary (VFloatUnary F64x2 FCeilLanes))
        0x75 -> pure (unary (VFloatUnary F64x2 FFloorLanes))
        0x76 -> pure (intBinary I8x16 (IMinLanes Signed))
        0x77 -> pure (intBinary I8x16 (IMinLanes Unsigned))
        0x78 -> pure (intBinary I8x16 (IMaxLanes Signed))
        0x79 -> pure (intBinary I8x16 (IMaxLanes Unsigned))
        0x7A -> pure (unary (VFloatUnary F64x2 FTruncLanes))
        0x7B -> pure (intBinary I8x16 IAvgr)
        0x7C -> pure (unary (VExtAddPairwise I16x8 Signed))
        0x7D -> pure (unary (VExtAddPairwise I16x8 Unsigned))
        0x7E -> pure (unary (VExtAddPairwise I32x4 Signed))
        0x7F -> pure (unary (VExtAddPairwise I32x4 Unsigned))
        0x80 -> pure (unary (VIntUnary I16x8 IAbs))
        0x81 -> pure (unary (VIntUnary I16x8 INeg))
        0x82 -> pure (binary VQ15MulrSat)
        0x83 -> pure (test (VAllTrue I16x8))
        0x84 -> pure (test (VBitmask I16x8))
        0x85 -> pure (binary (VNarrow I16x8 Signed))
        0x86 -> pure (binary (VNarrow I16x8 Unsigned))
        0x87 -> pure (unary (VExtend I16x8 LowHalf Signed))
        0x88 -> pure (unary (VExtend I16x8 HighHalf Signed))
        0x89 -> pure (unary (VExtend I16x8 LowHalf Unsigned))
        0x8A -> pure (unary (VExtend I16x8 HighHalf Unsigned))
        0x8B -> pure (shift (VShl I16x8))
        0x8C -> pure (shift (VShr I16x8 Signed))
        0x8D -> pure (shift (VShr I16x8 Unsigned))
        0x8E -> pure (intBinary I16x8 IAddLanes)
        0x8F -> pure (intBinary I16x8 (IAddSat Signed))
        0x90 -> pure (intBinary I16x8 (IAddSat Unsigned))
        0x91 -> pure (intBinary I16x8 ISubLanes)
        0x92 -> pure (intBinary I16x8 (ISubSat Signed))
        0x93 -> pure (intBinary I16x8 (ISubSat Unsigned))
        0x94 -> pure (unary (VFloatUnary F64x2 FNearestLanes))
        0x95 -> pure (intBinary I16x8 IMulLanes)
        0x96 -> pure (intBinary I16x8 (IMinLanes Signed))
        0x97 -> pure (intBinary I16x8 (IMinLanes Unsigned))
        0x98 -> pure (intBinary I16x8 (IMaxLanes Signed))
        0x99 -> pure (intBinary I16x8 (IMaxLanes Unsigned))
        0x9B -> pure (intBinary I16x8 IAvgr)
        0x9C -> pure (binary (VExtMul I16x8 LowHalf Signed))
        0x9D -> pure (binary (VExtMul I16x8 HighHalf Signed))
        0x9E -> pure (binary (VExtMul I16x8 LowHalf Unsigned))
        0x9F -> pure (binary (VExtMul I16x8 HighHalf Unsigned))
        0xA0 -> pure (unary (VIntUnary I32x4 IAbs))
        0xA1 -> pure (unary (VIntUnary I32x4 INeg))
        0xA3 -> pure (test (VAllTrue I32x4))
        0xA4 -> pure (test (VBitmask I32x4))
        0xA7 -> pure (unary (VExtend I32x4 LowHalf Signed))
        0xA8 -> pure (unary (VExtend I32x4 HighHalf Signed))
        0xA9 -> pure (unary (VExtend I32x4 LowHalf Unsigned))
        0xAA -> pure (unary (VExtend I32x4 HighHalf Unsigned))
        0xAB -> pure (shift (VShl I32x4))
        0xAC -> pure (shift (VShr I32x4 Signed))
        0xAD -> pure (shift (VShr I32x4 Unsigned))
        0xAE -> pure (intBinary I32x4 IAddLanes)
        0xB1 -> pure (intBinary I32x4 ISubLanes)
        0xB5 -> pure (intBinary I32x4 IMulLanes)
        0xB6 -> pure (intBinary I32x4 (IMinLanes Signed))
        0xB7 -> pure (intBinary I32x4 (IMinLanes Unsigned))
        0xB8 -> pure (intBinary I32x4 (IMaxLanes Signed))
        0xB9 -> pure (intBinary I32x4 (IMaxLanes Unsigned))
        0xBA -> pure (binary VDot)
        0xBC -> pure (binary (VExtMul I32x4 LowHalf Signed))
        0xBD -> pure (binary (VExtMul I32x4 HighHalf Signed))
        0xBE -> pure (binary (VExtMul I32x4 LowHalf Unsigned))
        0xBF -> pure (binary (VExtMul I32x4 HighHalf Unsigned))
        0xC0 -> pure (unary (VIntUnary I64x2 IAbs))
        0xC1 -> pure (unary (VIntUnary I64x2 INeg))
        0xC3 -> pure (test (VAllTrue I64x2))
        0xC4 -> pure (test (VBitmask I64x2))
        0xC7 -> pure (unary (VExtend I64x2 LowHalf Signed))
        0xC8 -> pure (unary (VExtend I64x2 HighHalf Signed))
        0xC9 -> pure (unary (VExtend I64x2 LowHalf Unsigned))
        0xCA -> pure (unary (VExtend I64x2 HighHalf Unsigned))
        0xCB -> pure (shift (VShl I64x2))
        0xCC -> pure (shift (VShr I64x2 Signed))
        0xCD -> pure (shift (VShr I64x2 Unsigned))
        0xCE -> pure (intBinary I64x2 IAddLanes)
        0xD1 -> pure (intBinary I64x2 ISubLanes)
        0xD5 -> pure (intBinary I64x2 IMulLanes)
        0xD6 -> pure (binary (VIntCompare I64x2 IEqLanes))
        0xD7 -> pure (binary (VIntCompare I64x2 INeLanes))
        0xD8 -> pure (binary (VIntCompare I64x2 (ILtLanes Signed)))
        0xD9 -> pure (binary (VIntCompare I64x2 (IGtLanes Signed)))
        0xDA -> pure (binary (VIntCompare I64x2 (ILeLanes Signed)))
        0xDB -> pure (binary (VIntCompare I64x2 (IGeLanes Signed)))
        0xDC -> pure (binary (VExtMul I64x2 LowHalf Signed))
        0xDD -> pure (binary (VExtMul I64x2 HighHalf Signed))
        0xDE -> pure (binary (VExtMul I64x2 LowHalf Unsigned))
        0xDF -> pure (binary (VExtMul I64x2 HighHalf Unsigned))
        0xE0 -> pure (unary (VFloatUnary F32x4 FAbsLanes))
        0xE1 -> pure (unary (VFloatUnary F32x4 FNegLanes))
        0xE3 -> pure (unary (VFloatUnary F32x4 FSqrtLanes))
        _ | opcode >= 0xE4 && opcode <= 0xEB -> pure (binary (VFloatBinary F32x4 (floatArithmetic (opcode - 0xE4))))
        0xEC -> pure (unary (VFloatUnary F64x2 FAbsLanes))
        0xED -> pure (unary (VFloatUnary F64x2 FNegLanes))
        0xEF -> pure (unary (VFloatUnary F64x2 FSqrtLanes))
        _ | opcode >= 0xF0 && opcode <= 0xF7 -> pure (binary (VFloatBinary F64x2 (floatArithmetic (opcode - 0xF0))))
        0xF8 -> pure (unary (VTruncSatF32x4 Signed))
        0xF9 -> pure (unary (VTruncSatF32x4 Unsigned))
        0xFA -> pure (unary (VConvertI32x4 Signed))
        0xFB -> pure (unary (VConvertI32x4 Unsigned))
        0xFC -> pure (unary (VTruncSatF64x2Zero Signed))
        0xFD -> pure (unary (VTruncSatF64x2Zero Unsigned))
        -- The relaxed instructions of 3.0: each is the instruction of 2.0 that gives one of the
        -- results it permits, or one of the three in 'VectorTernary'.
        0x100 -> pure (binary VSwizzle)
        0x101 -> pure (unary (VTruncSatF32x4 Signed))
        0x102 -> pure (unary (VTruncSatF32x4 Unsigned))
        0x103 -> pure (unary (VTruncSatF64x2Zero Signed))
        0x104 -> pure (unary (VTruncSatF64x2Zero Unsigned))
        0x105 -> pure (ternary (VTernary (VMulAdd F32x4)))
        0x106 -> pure (ternary (VTernary (VNegMulAdd F32x4)))
        0x107 -> pure (ternary (VTernary (VMulAdd F64x2)))
        0x108 -> pure (ternary (VTernary (VNegMulAdd F64x2)))
        _ | opcode >= 0x109 && opcode <= 0x10C -> pure (ternary VBitselect)
        0x10D -> pure (binary (VFloatBinary F32x4 FMinLanes))
        0x10E -> pure (binary (VFloatBinary F32x4 FMaxLanes))
        0x10F -> pure (binary (VFloatBinary F64x2 FMinLanes))
        0x110 -> pure (binary (VFloatBinary F64x2 FMaxLanes))
        0x111 -> pure (binary VQ15MulrSat)
        0x112 -> pure (binary VDotBytes)
        0x113 -> pure (ternary (VTernary VDotBytesAdd))
        0xFE -> pure (unary (VConvertLowI32x4 Signed))
        0xFF -> pure (unary (VConvertLowI32x4 Unsigned))
        _ -> fail ("unsupported: vector opcode " ++ show opcode)
  where
    operation :: Sing operands -> Sing result -> VectorOp operands result -> RawInstr
    operation operands result op = Vector (SomeVectorOp operands result op)
    unary = operation (SCons SV128 SNil) SV128 . VUnary
    ternary = operation (SCons SV128 (SCons SV128 (SCons SV128 SNil))) SV128
    binary = operation (SCons SV128 (SCons SV128 SNil)) SV128 . VBinary
    intBinary shape = binary . VIntBinary shape
    test = operation (SCons SV128 SNil) SI32 . VTest
    shift = operation (SCons SI32 (SCons SV128 SNil)) SV128 . VShift
    splat :: LaneType t -> RawInstr
    splat lane = operation (SCons (laneSing lane) SNil) SV128 (VSplat lane)
    extract :: LaneType t -> Signedness -> Get RawInstr
    extract lane sign = (\index -> operation (SCons SV128 SNil) (laneSing lane) (VExtract lane index sign)) <$> getWord8
    replace :: LaneType t -> Get RawInstr
    replace lane = operation (SCons (laneSing lane) (SCons SV128 SNil)) SV128 . VReplace lane <$> getWord8
    laneAccess access width = flip (access width) <$> getMemArg <*> getWord8
    -- The order of the comparisons within a shape's block of opcodes.
    comparison offset = [IEqLanes, INeLanes, ILtLanes Signed, ILtLanes Unsigned, IGtLanes Signed, IGtLanes Unsigned, ILeLanes Signed, ILeLanes Unsigned, IGeLanes Signed, IGeLanes Unsigned] !! fromIntegral offset
    floatComparison offset = [FEqLanes, FNeLanes, FLtLanes, FGtLanes, FLeLanes, FGeLanes] !! fromIntegral offset
    floatArithmetic offset = [FAddLanes, FSubLanes, FMulLanes, FDivLanes, FMinLanes, FMaxLanes, FPMin, FPMax] !! fromIntegral offset

-- *** Sections ***

{- | Accumulator gathering sections as they are read. The function and code sections are
  stored separately and merged into 'RawFunction's at the end.
-}
data Sections = Sections
    { typeSection :: [FuncType]
    , importSection :: [Import]
    , functionSection :: [Word32]
    -- ^ function section: type index per function
    , codeSection :: [([WrittenType], [RawInstr])]
    -- ^ code section: locals and body per function
    , globalSection :: [(RawGlobal, WrittenType)]
    , memorySection :: [RawMemory]
    , tableSection :: [(RawTable, WrittenType)]
    , elementSection :: [RawElementSegment]
    , exportSection :: [Export]
    , startSection :: Maybe FunctionIdx
    , dataSection :: [RawDataSegment]
    , dataCountSection :: Maybe Word32
    -- ^ the data count section, which must agree with the data section
    , customs :: [(Text, BL.ByteString)]
    , tagSection :: [(FuncType, Word32)]
    -- ^ each tag's type, and its index
    , writtenTypes :: [FuncTypeOf WrittenType]
    -- ^ the type section as written; 'typeSection' is its erasure
    }

emptySections :: Sections
emptySections = Sections [] [] [] [] [] [] [] [] [] Nothing [] Nothing [] [] []

getModule :: Get RawModule
getModule = do
    magic <- getByteString 4
    when (magic /= wasmMagic) (fail "not a WebAssembly module (bad magic)")
    version <- getWord32le
    when (version /= 1) (fail ("unsupported binary version " ++ show version))
    readSections emptySections >>= either fail pure . assemble

wasmMagic :: BS.ByteString
wasmMagic = BS.pack [0x00, 0x61, 0x73, 0x6D]

{- | Read the sections in order. Non-custom sections must appear in the spec's fixed order,
  each at most once; custom sections may appear anywhere. Each section is parsed in isolation
  so it must consume exactly its declared size.
-}
readSections :: Sections -> Get Sections
readSections = go 0
  where
    go lastRank acc = do
        done <- isEmpty
        if done
            then pure acc
            else do
                sectionId <- getWord8
                size <- getULEB128
                rank <- maybe (fail ("malformed section id " ++ show sectionId)) pure (sectionRank sectionId)
                when (sectionId /= 0 && rank <= lastRank) (fail ("section " ++ show sectionId ++ " out of order or repeated"))
                acc' <- isolate (fromIntegral size) (parseSection sectionId acc)
                go (if sectionId == 0 then lastRank else rank) acc'

-- | The position of a section id in the required order: tags (13) follow memories, and the data count (12) precedes code (10).
sectionRank :: Word8 -> Maybe Int
sectionRank 0 = Just 0
sectionRank sectionId = (+ 1) <$> elemIndex sectionId [1, 2, 3, 4, 5, 13, 6, 7, 8, 9, 12, 10, 11]

parseSection :: Word8 -> Sections -> Get Sections
parseSection sectionId acc = case sectionId of
    0 -> (\name bytes -> acc {customs = acc.customs ++ [(name, bytes)]}) <$> getName <*> getRemainingLazyByteString
    1 -> (\ts -> acc {typeSection = map erasedFuncType ts, writtenTypes = ts}) <$> getVec getFuncType
    2 -> (\is -> acc {importSection = is}) <$> getVec (getImport (acc.typeSection))
    3 -> (\is -> acc {functionSection = is}) <$> getVec getULEB128
    4 -> (\ts -> acc {tableSection = ts}) <$> getVec getWrittenTable
    5 -> (\ms -> acc {memorySection = ms}) <$> getVec getMemory
    6 -> (\gs -> acc {globalSection = gs}) <$> getVec getGlobal
    7 -> (\es -> acc {exportSection = es}) <$> getVec getExport
    8 -> (\i -> acc {startSection = Just (FunctionIdx i)}) <$> getULEB128
    9 -> (\es -> acc {elementSection = es}) <$> getVec (getElem (length acc.typeSection))
    10 -> (\cs -> acc {codeSection = cs}) <$> getVec (getCode (isJust acc.dataCountSection) (acc.typeSection))
    11 -> (\ds -> acc {dataSection = ds}) <$> getVec getData
    12 -> (\n -> acc {dataCountSection = Just n}) <$> getULEB128
    13 -> (\ts -> acc {tagSection = ts}) <$> getVec (getTag acc.typeSection)
    _ -> fail ("malformed section id " ++ show sectionId)

-- | A data segment: active for memory 0 (mode 0) or for a memory it names (mode 2), or passive (mode 1).
getData :: Get RawDataSegment
getData = do
    mode <- getULEB128
    case mode of
        0 -> RawDataSegment . Active (MemoryIdx 0) <$> getExpr False [] <*> payload
        1 -> RawDataSegment Passive <$> payload
        2 -> do
            memIdx <- getULEB128
            RawDataSegment . Active (MemoryIdx memIdx) <$> getExpr False [] <*> payload
        _ -> fail ("unknown data segment mode " ++ show mode)
  where
    payload = getULEB128 >>= getByteString . fromIntegral

{- | An import as the binary lists it: its two names, and the type of what is imported.
(A function with its type's index, and a table and a global with the type as written.)
-}
data Import
    = FunctionImport Word32 RawImport
    | TableImport Text Text WrittenType RawTable
    | MemoryImport Text Text RawMemory
    | GlobalImport Text Text WrittenType GlobalType

getImport :: [FuncType] -> Get Import
getImport types = do
    moduleName <- getName
    fieldName <- getName
    kind <- getWord8
    case kind of
        0x00 -> do
            typeIdx <- getULEB128
            case nth types (fromIntegral typeIdx) of
                Just ft -> pure (FunctionImport typeIdx (RawImport moduleName fieldName (ImportFunc ft)))
                Nothing -> fail ("import type index out of range: " ++ show typeIdx)
        0x01 -> (\(table, entries) -> TableImport moduleName fieldName entries table) <$> getWrittenTable
        0x02 -> MemoryImport moduleName fieldName <$> getMemory
        0x03 -> (\(globalType, valType) -> GlobalImport moduleName fieldName valType globalType) <$> getWrittenGlobalType
        0x04 -> fail "unsupported: tag import"
        _ -> fail ("unknown import kind 0x" ++ showHex kind "")

-- | A tag: an attribute byte, which is zero (an exception), and the type of what it carries.
getTag :: [FuncType] -> Get (FuncType, Word32)
getTag types = do
    attribute <- getWord8
    when (attribute /= 0) (fail "malformed tag attribute")
    typeIdx <- getULEB128
    maybe (fail ("tag type index out of range: " ++ show typeIdx)) (\ft -> pure (ft, typeIdx)) (nth types (fromIntegral typeIdx))

{- | A table type: the reference type of its entries, then its limits.
| A table type, and the type of its entries as the module writes it.
-}
getWrittenTable :: Get (RawTable, WrittenType)
getWrittenTable = do
    entries <- getWrittenType
    unless (erasedType entries `elem` [FuncRef, ExternRef, ExnRef]) (fail "malformed reference type")
    (addrType, limits) <- getLimits
    pure (RawTable (erasedType entries) addrType limits, entries)

{- | An element segment. Bit 0 of its flags says that it is not active, bit 1 that an active
  one names its table (or that an inactive one is declarative), and bit 2 that its items are
  expressions and not function indices. A function index is kept as the expression it
  abbreviates, @ref.func@ of it.
-}
getElem :: Int -> Get RawElementSegment
getElem typeCount = do
    flags <- getULEB128 :: Get Word32
    let indices = map (\f -> [RefFunc f]) <$> getVec (FunctionIdx <$> getULEB128)
        expressions = getVec (getExpr False [])
        kindThenIndices = do
            elemKind <- getWord8
            when (elemKind /= 0) (fail ("unknown element kind " ++ show elemKind))
            RawElementSegment ElemPassive FuncRef <$> indices
        typeThenExpressions = RawElementSegment ElemPassive <$> entriesType <*> expressions
        -- (The type as written may name a function type, which must be one of the module's.)
        entriesType = do
            entries <- getWrittenType
            case entries of
                RefTo _ (OfType i) | fromIntegral i >= typeCount -> fail "unknown type"
                RefTo _ _ -> pure (erasedType entries)
                Plain _ -> fail "malformed reference type"
        activeIn table segment = (\offset (RawElementSegment _ entryType items) -> RawElementSegment (ElemActive table offset) entryType items) <$> getExpr False [] <*> segment
        named segment = getULEB128 >>= \table -> activeIn (TableIdx table) segment
        declarative segment = (\(RawElementSegment _ entryType items) -> RawElementSegment ElemDeclarative entryType items) <$> segment
    case flags of
        0 -> activeIn (TableIdx 0) (RawElementSegment ElemPassive FuncRef <$> indices)
        1 -> kindThenIndices
        2 -> named kindThenIndices
        3 -> declarative kindThenIndices
        4 -> activeIn (TableIdx 0) (RawElementSegment ElemPassive FuncRef <$> expressions)
        5 -> typeThenExpressions
        6 -> named typeThenExpressions
        7 -> declarative typeThenExpressions
        _ -> fail ("unknown element segment flags " ++ show flags)

getMemory :: Get RawMemory
getMemory = RawMemory . uncurry MemType <$> getLimits

getGlobal :: Get (RawGlobal, WrittenType)
getGlobal = (\(globalType, valType) initialiser -> (RawGlobal globalType initialiser, valType)) <$> getWrittenGlobalType <*> getExpr False []

getExport :: Get Export
getExport = do
    name <- getName
    kind <- getWord8
    idx <- getULEB128
    desc <- case kind of
        0x00 -> pure (ExportFunc (FunctionIdx idx))
        0x01 -> pure (ExportTable (TableIdx idx))
        0x02 -> pure (ExportMem (MemoryIdx idx))
        0x03 -> pure (ExportGlobal (GlobalIdx idx))
        0x04 -> pure (ExportTag (TagIdx idx))
        _ -> fail ("unsupported export kind 0x" ++ showHex kind "")
    pure (Export name desc)

{- | A code-section entry: a redundant byte size, the (run-length encoded) locals, and
  the body expression.
-}
getCode :: Bool -> [FuncType] -> Get ([WrittenType], [RawInstr])
getCode hasDataCount types = do
    entrySize <- getULEB128
    isolate (fromIntegral entrySize) $ do
        localGroups <- getVec getLocalGroup
        when (sum [toInteger count | (count, _) <- localGroups] > toInteger maxLocals) (fail "too many locals")
        body <- getExpr hasDataCount types
        pure (concatMap expand localGroups, body)
  where
    expand (count, valType) = replicate (fromIntegral count) valType

{- | An implementation limit on the locals of one function. The spec only caps them at 2^32,
  but locals are materialised as a list here, so a six-byte input must not be able to demand
  four billion of them.
-}
maxLocals :: Int
maxLocals = 50000

getLocalGroup :: Get (Word32, WrittenType)
getLocalGroup = (,) <$> getULEB128 <*> getWrittenType

assemble :: Sections -> Either String RawModule
assemble secs = do
    when
        (length secs.functionSection /= length secs.codeSection)
        (Left "function and code sections have different lengths")
    when
        (maybe False (\n -> fromIntegral n /= length secs.dataSection) secs.dataCountSection)
        (Left "data count and data section have inconsistent lengths")
    funcs <- traverse toFunction (zip secs.functionSection secs.codeSection)
    pure
        RawModule
            { types = secs.typeSection
            , imports = [imported | FunctionImport _ imported <- secs.importSection]
            , functions = funcs
            , globals = [RawGlobal globalType [] | (_, _, globalType) <- importedGlobals] ++ map fst secs.globalSection
            , memories = [memory | (_, _, memory) <- importedMemories] ++ secs.memorySection
            , tables = [table | (_, _, table) <- importedTables] ++ map fst secs.tableSection
            , elementSegments = secs.elementSection
            , dataSegments = secs.dataSection
            , exports = secs.exportSection
            , start = secs.startSection
            , customSections = secs.customs
            , stateImports = StateImports (map names importedGlobals) (map names importedMemories) (map names importedTables)
            , tags = map fst secs.tagSection
            , written =
                Just
                    Written
                        { types = secs.writtenTypes
                        , functions = [typeIdx | FunctionImport typeIdx _ <- secs.importSection] ++ secs.functionSection
                        , locals = map fst secs.codeSection
                        , globals = [valType | GlobalImport _ _ valType _ <- secs.importSection] ++ map snd secs.globalSection
                        , tables = [entries | TableImport _ _ entries _ <- secs.importSection] ++ map snd secs.tableSection
                        , tags = map snd secs.tagSection
                        }
            }
  where
    importedGlobals = [(moduleName, fieldName, globalType) | GlobalImport moduleName fieldName _ globalType <- secs.importSection]
    importedMemories = [(moduleName, fieldName, memory) | MemoryImport moduleName fieldName memory <- secs.importSection]
    importedTables = [(moduleName, fieldName, table) | TableImport moduleName fieldName _ table <- secs.importSection]
    names (moduleName, fieldName, _) = (moduleName, fieldName)
    toFunction (typeIdx, (locals, body)) =
        case nth secs.typeSection (fromIntegral typeIdx) of
            Just sig -> Right (RawFunction sig (map erasedType locals) body)
            Nothing -> Left ("function type index out of range: " ++ show typeIdx)
