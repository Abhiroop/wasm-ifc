{-# LANGUAGE DataKinds #-}

{- | A decoder from the WebAssembly binary format into the raw AST.

Only the instruction subset declared in "Syntax.Instructions" is recognised; any other
opcode, and any feature outside the subset (imports, tables, elements), fails the decode
with a message starting @unsupported@. Everything the format itself requires is checked:
integer encodings, section order and uniqueness, section and code-entry sizes, UTF-8 names.
-}
module Codec.Wasm (
    decodeModule,
) where

import Control.Monad (replicateM, when)
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
import Data.Text (Text)
import Data.Text.Encoding (decodeUtf8')
import Data.Word (Word32, Word64, Word8)
import GHC.Float (castWord32ToFloat, castWord64ToDouble)
import Numeric (showHex)

import Syntax.DataSegments (RawData (RawData))
import Syntax.Functions (RawFunction (RawFunction))
import Syntax.Globals (RawGlobal (RawGlobal))
import Syntax.Indices
import Syntax.Instructions
import Syntax.Memories (RawMemory (RawMemory))
import Syntax.Module
import Syntax.Types

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

getValType :: Get ValType
getValType = do
    byte <- getWord8
    case byte of
        0x7F -> pure I32
        0x7E -> pure I64
        0x7D -> pure F32
        0x7C -> pure F64
        _ -> fail ("unknown valtype byte 0x" ++ showHex byte "")

getFuncType :: Get FuncType
getFuncType = do
    form <- getWord8
    when (form /= 0x60) (fail ("expected functype (0x60), got 0x" ++ showHex form ""))
    FuncType <$> getVec getValType <*> getVec getValType

getLimits :: Get Limits
getLimits = do
    flag <- getWord8
    case flag of
        0x00 -> Limits <$> getULEB128 <*> pure Nothing
        0x01 -> Limits <$> getULEB128 <*> (Just <$> getULEB128)
        _ -> fail ("unknown limits flag 0x" ++ showHex flag "")

getGlobalType :: Get GlobalType
getGlobalType = do
    valType <- getValType
    mutability <- getWord8
    case mutability of
        0x00 -> pure (GlobalType Immutable valType)
        0x01 -> pure (GlobalType Mutable valType)
        _ -> fail ("unknown mutability 0x" ++ showHex mutability "")

{- | A block type is either empty, a single result type, or a reference to a function
  type in the type section. The three cases are distinguished by a signed encoding.
-}
getBlockType :: [FuncType] -> Get BlockType
getBlockType types = do
    code <- getS33
    case code of
        -64 -> pure (FuncType [] [])
        -1 -> pure (FuncType [] [I32])
        -2 -> pure (FuncType [] [I64])
        -3 -> pure (FuncType [] [F32])
        -4 -> pure (FuncType [] [F64])
        n -> case nth types (fromIntegral n) of
            Just ft -> pure ft
            Nothing -> fail ("block type index out of range: " ++ show n)

{- | Total list indexing (@Nothing@ if out of range), so a malformed index in the binary
  becomes a decode error rather than a crash.
-}
nth :: [a] -> Int -> Maybe a
nth xs i
    | i < 0 = Nothing
    | otherwise = case drop i xs of x : _ -> Just x; [] -> Nothing

getMemArg :: Get MemArg
getMemArg = MemArg <$> getULEB128 <*> getULEB128

-- *** Instructions ***

{- | Read instructions up to (and consuming) a terminator byte — @end@ (0x0B) or
  @else@ (0x05) — returning the instructions and which terminator was seen.
-}
getBlockBody :: [FuncType] -> Get ([RawInstr], Word8)
getBlockBody types = go []
  where
    go acc = do
        opcode <- getWord8
        if opcode == 0x0B || opcode == 0x05
            then pure (reverse acc, opcode)
            else do
                instr <- getInstr types opcode
                go (instr : acc)

-- | An expression: instructions up to a terminating @end@.
getExpr :: [FuncType] -> Get [RawInstr]
getExpr types = fst <$> getBlockBody types

-- | Decode one (non-terminator) instruction whose opcode byte has already been read.
getInstr :: [FuncType] -> Word8 -> Get RawInstr
getInstr types opcode = case opcode of
    {- Control -}
    0x00 -> pure Unreachable
    0x01 -> pure Nop
    0x02 -> Block <$> getBlockType types <*> getExpr types
    0x03 -> Loop <$> getBlockType types <*> getExpr types
    0x04 -> do
        blockType <- getBlockType types
        (thenArm, term) <- getBlockBody types
        elseArm <- if term == 0x05 then getExpr types else pure []
        pure (If blockType thenArm elseArm)
    0x0C -> Br . LabelIdx <$> getULEB128
    0x0D -> BrIf . LabelIdx <$> getULEB128
    0x0E -> BrTable <$> getVec (LabelIdx <$> getULEB128) <*> (LabelIdx <$> getULEB128)
    0x0F -> pure Return
    0x10 -> Call . FunctionIdx <$> getULEB128
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
    0x3F -> reservedZero >> pure MemorySize
    0x40 -> reservedZero >> pure MemoryGrow
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
    _ -> fail ("unsupported opcode 0x" ++ showHex opcode "")

-- | The memory-index byte of @memory.size@/@memory.grow@, which must be @0x00@.
reservedZero :: Get ()
reservedZero = do
    byte <- getWord8
    when (byte /= 0) (fail "zero byte expected")

-- *** Sections ***

{- | Accumulator gathering sections as they are read. The function and code sections are
  stored separately and merged into 'RawFunction's at the end.
-}
data Sections = Sections
    { secTypes :: [FuncType]
    , secFuncTypes :: [Word32]
    -- ^ function section: type index per function
    , secCodes :: [([ValType], [RawInstr])]
    -- ^ code section: locals and body per function
    , secGlobals :: [RawGlobal]
    , secMems :: [RawMemory]
    , secExports :: [Export]
    , secStart :: Maybe FunctionIdx
    , secData :: [RawData]
    , secDataCount :: Maybe Word32
    -- ^ the data count section, which must agree with the data section
    }

emptySections :: Sections
emptySections = Sections [] [] [] [] [] [] Nothing [] Nothing

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

-- | The position of a section id in the required order; the data count (12) precedes code (10).
sectionRank :: Word8 -> Maybe Int
sectionRank 0 = Just 0
sectionRank sectionId = (+ 1) <$> elemIndex sectionId [1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 10, 11]

parseSection :: Word8 -> Sections -> Get Sections
parseSection sectionId acc = case sectionId of
    0 -> getName >> getRemainingLazyByteString >> pure acc -- a custom section: a name, then anything
    1 -> (\ts -> acc {secTypes = ts}) <$> getVec getFuncType
    2 -> do
        importCount <- getULEB128
        when (importCount /= 0) (fail "imports are not supported")
        pure acc
    3 -> (\is -> acc {secFuncTypes = is}) <$> getVec getULEB128
    4 -> fail "unsupported: table section"
    5 -> (\ms -> acc {secMems = ms}) <$> getVec getMemory
    6 -> (\gs -> acc {secGlobals = gs}) <$> getVec getGlobal
    7 -> (\es -> acc {secExports = es}) <$> getVec getExport
    8 -> (\i -> acc {secStart = Just (FunctionIdx i)}) <$> getULEB128
    9 -> fail "unsupported: element section"
    10 -> (\cs -> acc {secCodes = cs}) <$> getVec (getCode (acc.secTypes))
    11 -> (\ds -> acc {secData = ds}) <$> getVec getData
    12 -> (\n -> acc {secDataCount = Just n}) <$> getULEB128
    _ -> fail ("malformed section id " ++ show sectionId)

{- | A data segment. Only the active form for memory 0 (@0x00 offset-expr bytes@) is
  supported; passive segments and explicit memory indices are bulk-memory features.
-}
getData :: Get RawData
getData = do
    mode <- getULEB128
    case mode of
        0 -> RawData <$> getExpr [] <*> (getULEB128 >>= getByteString . fromIntegral)
        1 -> fail "unsupported: passive data segment"
        2 -> fail "unsupported: data segment with an explicit memory index"
        _ -> fail ("unknown data segment mode " ++ show mode)

getMemory :: Get RawMemory
getMemory = RawMemory . MemType AddrI32 <$> getLimits

getGlobal :: Get RawGlobal
getGlobal = RawGlobal <$> getGlobalType <*> getExpr []

getExport :: Get Export
getExport = do
    name <- getName
    kind <- getWord8
    idx <- getULEB128
    desc <- case kind of
        0x00 -> pure (ExportFunc (FunctionIdx idx))
        0x02 -> pure (ExportMem (MemoryIdx idx))
        0x03 -> pure (ExportGlobal (GlobalIdx idx))
        _ -> fail ("unsupported export kind 0x" ++ showHex kind "")
    pure (Export name desc)

{- | A code-section entry: a redundant byte size, the (run-length encoded) locals, and
  the body expression.
-}
getCode :: [FuncType] -> Get ([ValType], [RawInstr])
getCode types = do
    entrySize <- getULEB128
    isolate (fromIntegral entrySize) $ do
        localGroups <- getVec getLocalGroup
        when (sum [toInteger count | (count, _) <- localGroups] > toInteger maxLocals) (fail "too many locals")
        body <- getExpr types
        pure (concatMap expand localGroups, body)
  where
    expand (count, valType) = replicate (fromIntegral count) valType

{- | An implementation limit on the locals of one function. The spec only caps them at 2^32,
  but locals are materialised as a list here, so a six-byte input must not be able to demand
  four billion of them.
-}
maxLocals :: Int
maxLocals = 50000

getLocalGroup :: Get (Word32, ValType)
getLocalGroup = (,) <$> getULEB128 <*> getValType

assemble :: Sections -> Either String RawModule
assemble secs = do
    when
        (length secs.secFuncTypes /= length secs.secCodes)
        (Left "function and code sections have different lengths")
    when
        (maybe False (\n -> fromIntegral n /= length secs.secData) secs.secDataCount)
        (Left "data count and data section have inconsistent lengths")
    funcs <- traverse toFunction (zip secs.secFuncTypes secs.secCodes)
    pure
        RawModule
            { moduleTypes = secs.secTypes
            , moduleFuncs = funcs
            , moduleGlobals = secs.secGlobals
            , moduleMemories = secs.secMems
            , moduleData = secs.secData
            , moduleExports = secs.secExports
            , moduleStart = secs.secStart
            }
  where
    toFunction (typeIdx, (locals, body)) =
        case nth secs.secTypes (fromIntegral typeIdx) of
            Just sig -> Right (RawFunction sig locals body)
            Nothing -> Left ("function type index out of range: " ++ show typeIdx)
