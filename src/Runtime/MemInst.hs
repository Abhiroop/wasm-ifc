{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE StandaloneKindSignatures #-}

{- | Linear memory: the one piece of mutable runtime state the interpreter still keeps
  outside the type-indexed value stack and locals. (GlobalSpaceInst are tracked by the typed
  'Runtime.Stack.GlobalSpaceInst'; functions by 'Runtime.Interpreter.FuncSpaceInst'.)

  A 'MemInst' is indexed by its declared 'MemShape', so — like every other instance — it
  carries its type. The index is a phantom (the contents do not depend on it); the operations
  below thread it through unchanged. The declared limits are also kept at the term level,
  because @memory.grow@ has to consult the maximum at run time.

  The bytes are stored sparsely, in chunks of 'chunkSize' bytes, and a chunk exists only once
  something has been written into it: a chunk never touched reads as zeros without existing. So
  declaring or growing to a large memory costs nothing until it is used, which is what lets a
  module ask for the full 4 GiB the spec allows. Storage is copy-on-write per chunk, so a store
  copies one chunk rather than the whole memory. The chunk is a unit of storage only (the memory
  still grows by 64 KiB pages), and it is small because its copy is the price of every store: at
  the page size that was 64 KiB for a 4-byte write, which the @memory-stream@ kernel in @bench/@
  measured as nearly all of its time (TODO.md §I, E6).

  Loads and stores of a whole value go through 'loadChecked' and 'storeWord', a little-endian
  word at a time; the byte-list functions serve the bulk operations, data segments and the WASI
  host.

  'loadChecked' is the one way the interpreter reads a value from memory, and half of the
  trusted code behind SecWasm's run-time checks (the other half is
  'Runtime.TableInst.lookupChecked'): it hands out the word only as a 'CheckedRead' at the
  level it compared the bytes' labels with, and that value is the evidence a load's step has to
  present ("Runtime.Obligation").
-}
module Runtime.MemInst (
    MemInst,
    allocMemory,
    retypeMemory,
    growMemory,
    memoryPages,
    maxMemoryPages,
    CheckedRead,
    checkedWord,
    LoadFailure (..),
    loadChecked,
    loadWordUnchecked,
    storeWord,
    readBytes,
    writeBytes,
    copyWithin,
    fillBytes,
    levelOfRange,
    labelRange,
    storeWordAt,
    writeBytesAt,
    copyWithinAt,
    copyBetweenAt,
    fillBytesAt,
) where

import Control.Monad (forM_)
import Data.Bits (complement, shiftL, shiftR, (.&.), (.|.))
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.Vector.Unboxed qualified as UV
import Data.Vector.Unboxed.Mutable qualified as MV
import Data.Word (Word32, Word64, Word8)
import GHC.Word (Word64 (W64#))

import Data.Singletons (Sing)
import Syntax.Types (AddrType (..), Limits (..))
import Syntax.TypesIFC (SSecLevel (..), SecLevel (..))
import Validation.Shape (MemShape)

-- *** Linear memory ***

{- | A linear memory: its declared limits, its current size in pages, the written chunks, and
  the security level of every byte.

  The levels follow SecWasm: memory is labelled per byte, at run time, and a store relabels the
  bytes it writes. They are kept in a second chunk map with the same chunks as the bytes, one
  bit per memory byte (set for secret), and an absent chunk means "all public", just as an
  absent byte chunk means "all zero". So a memory that never holds a secret has an empty level
  map, @memory.grow@ labels new pages public for free, and a public store into a chunk without
  levels costs nothing. A store whose bytes have its level already writes no levels, and one
  that changes them copies the chunk's bits, an eighth of what it copies of the bytes. A load reports the join of the levels it read ('levelOfRange'); the
  interpreter compares it with the level the instruction declares and traps when it is higher.
-}
type MemInst :: MemShape -> Type
data MemInst m = MemInst
    { maxPages :: !Word32
    -- ^ how far the memory may grow: its declared maximum, or what its addresses reach if less
    , pageCount :: !Word32
    , chunks :: !(IntMap (UV.Vector Word8))
    -- ^ by chunk index; an absent chunk is all zeros, a present one is 'chunkSize' bytes long
    , levels :: !(IntMap (UV.Vector Word64))
    {- ^ by chunk index, one bit per byte in 'levelWords' words, set where the byte is secret;
    an absent chunk is all public
    -}
    }

-- | Bytes per WebAssembly page.
pageSize :: Int
pageSize = 65536

{- | Bytes per stored chunk: the unit of storage and of copy-on-write (see the module header).
  1 KiB was measured against 4 KiB on the real programs in @bench/@: 1.26× faster, and 1.04× on
  the kernels; 256 bytes bought nothing more (TODO.md §I, "E6 next"). A label store kept beside
  the bytes for IFC can share this granularity.
-}
chunkSize :: Int
chunkSize = 1024

-- | A chunk that has never been written.
zeroChunk :: UV.Vector Word8
zeroChunk = UV.replicate chunkSize 0

-- | Words of level bits per chunk: byte @i@ of a chunk has bit @i mod 64@ of word @i div 64@.
levelWords :: Int
levelWords = chunkSize `div` 64

-- | The levels of a chunk that holds no secret.
publicChunk :: UV.Vector Word64
publicChunk = UV.replicate levelWords 0

{- | The bits of word @w@ of a chunk's levels that belong to the bytes from @from@ up to, not
  including, @to@ of the chunk; the word is one the range reaches.
-}
{-# INLINE wordMask #-}
wordMask :: Int -> Int -> Int -> Word64
wordMask from to w = upTo .&. complement below
  where
    firstBit = max from (w * 64) - w * 64
    endBit = min to (w * 64 + 64) - w * 64
    below = (1 `shiftL` firstBit) - 1
    upTo = if endBit >= 64 then maxBound else (1 `shiftL` endBit) - 1

{- | The most pages a memory may have (the spec's bound for validation): 4 GiB of them with
  32-bit addresses, 2^48 pages with 64-bit ones.
-}
maxMemoryPages :: AddrType -> Word64
maxMemoryPages AddrI32 = 65536
maxMemoryPages AddrI64 = 2 ^ (48 :: Int)

{- | The most pages a memory of this machine holds: the spec's bound with 32-bit addresses,
  and with 64-bit ones as many as a 32-bit count of pages (256 TiB), far past what a host has.
-}
pagesHeld :: AddrType -> Word32
pagesHeld AddrI32 = 65536
pagesHeld AddrI64 = maxBound

{- | Allocate a memory at its declared minimum size, zero-initialised; 'Nothing' if the minimum
  is more than this machine holds, which only a 64-bit memory can declare.
-}
allocMemory :: AddrType -> Limits -> Maybe (MemInst m)
allocMemory addresses declared
    | declared.min > held = Nothing
    | otherwise = Just (MemInst (fromIntegral (maybe held (min held) declared.max)) (fromIntegral declared.min) IntMap.empty IntMap.empty)
  where
    held = fromIntegral (pagesHeld addresses)

{- | The same memory at another shape. The shape is a phantom: the contents do not depend on it,
  and what limits growth is kept in the memory itself. A module that imports a memory holds it
  at the shape its import declares, which need not be the shape it was defined at.
-}
retypeMemory :: MemInst m -> MemInst m'
retypeMemory (MemInst most pages chunks levels) = MemInst most pages chunks levels

-- | Size of a memory in whole pages.
memoryPages :: MemInst m -> Word32
memoryPages mem = mem.pageCount

{- | Grow a memory by @delta@ pages (zero-filled), or refuse if the result would exceed the
  declared maximum or what the memory's addresses reach. Refusal is the spec's @memory.grow@ failure, which
  the instruction reports as @-1@ rather than trapping.
-}
growMemory :: Word32 -> MemInst m -> Maybe (MemInst m)
growMemory delta mem
    | requested > toInteger allowed = Nothing
    | otherwise = Just mem {pageCount = fromInteger requested}
  where
    requested = toInteger mem.pageCount + toInteger delta
    allowed = mem.maxPages

{- | Whether @count@ bytes from @addr@ lie inside the memory. Computed in 'Int', which is 64 bits
  wide on the platforms GHC builds this for (the effective address already relies on it): the
  largest memory is 2^32 bytes and an address is a 32-bit base plus a 32-bit offset, so nothing
  here can overflow. It used to be 'Integer', an allocation on every load and store for nothing.
-}
inBounds :: MemInst m -> Int -> Int -> Bool
inBounds mem addr count = addr >= 0 && count >= 0 && addr + count <= fromIntegral mem.pageCount * pageSize

{- | A word read from memory whose bytes are labelled at most @level@. The constructor stays in
  this module and 'loadChecked' is its only use, so a value of this type exists only if those
  bytes were read and their labels compared with @level@: it is both the word a load pushes and
  the evidence that the load's check passed.
-}
type CheckedRead :: SecLevel -> Type
newtype CheckedRead level = CheckedRead Word64

-- | The word of a checked read.
checkedWord :: CheckedRead level -> Word64
checkedWord (CheckedRead word) = word

-- | Why a load yields no word.
data LoadFailure
    = -- | the range falls outside the memory
      LoadOutOfBounds
    | -- | a byte in the range is more secret than the level the load declares
      LoadAboveLevel

{- | A load with SecWasm's run-time check (E-LOAD): read a little-endian word of @count@ bytes
  (1 to 8) at effective address @addr@, and compare the join of its bytes' labels with @level@,
  the level the load declares. The comparison is skipped when the load declares 'High, since
  nothing exceeds it. The caller says what to do with a failure and with the word.

  The word goes to its use in one place and as a machine word. Returned in an 'Either'
  instead, it reaches the code after the load from several branches (one per way of reading
  it), and GHC shares that code and passes the word boxed: 16 bytes allocated on every load.
-}
{-# INLINE loadChecked #-}
loadChecked :: MemInst m -> Sing (level :: SecLevel) -> Int -> Int -> (LoadFailure -> result) -> (CheckedRead level -> result) -> result
loadChecked mem level addr count failed loaded
    | not (inBounds mem addr count) = failed LoadOutOfBounds
    | aboveLevel = failed LoadAboveLevel
    | otherwise = case wordInBounds mem addr count of W64# bits -> loaded (CheckedRead (W64# bits))
  where
    aboveLevel = case level of
        SHigh -> False
        SLow -> case levelOfRange mem addr count of
            Low -> False
            High -> True

{- | Read a little-endian word of @count@ bytes (1 to 8) at effective address @addr@,
  zero-extended, whatever its bytes' labels; 'Nothing' if the range falls outside the memory. A
  word inside one chunk — every word but those straddling a chunk boundary — costs one chunk
  lookup and no list. Not for the interpreter, which reads through 'loadChecked': this is for
  code outside the labelled machine (the benchmarks' erased copy).
-}

-- Inlined into each load of the interpreter: as a call it returns its word in a 'Just',
-- which is allocated on every load (32 bytes), and GHC stopped inlining it of its own accord
-- once the interpreter had a clause per address type.
{-# INLINE loadWordUnchecked #-}
loadWordUnchecked :: MemInst m -> Int -> Int -> Maybe Word64
loadWordUnchecked mem addr count
    | inBounds mem addr count = Just (wordInBounds mem addr count)
    | otherwise = Nothing

-- | The word of @count@ bytes at @addr@, a range that is inside the memory.
{-# INLINE wordInBounds #-}
wordInBounds :: MemInst m -> Int -> Int -> Word64
wordInBounds mem addr count
    | offset + count <= chunkSize = maybe 0 assemble (IntMap.lookup chunkIx mem.chunks)
    | otherwise = foldr (.|.) 0 [fromIntegral b `shiftL` (8 * i) | (i, b) <- zip [0 ..] (bytesAt mem addr count)]
  where
    (chunkIx, offset) = addr `quotRem` chunkSize
    assemble stored = go 0 0
      where
        go :: Int -> Word64 -> Word64
        go !i !acc
            | i == count = acc
            | otherwise = go (i + 1) (acc .|. (fromIntegral (fromMaybe 0 (stored UV.!? (offset + i))) `shiftL` (8 * i)))

{- | Write the low @count@ bytes (1 to 8) of @word@, little-endian, at @addr@; 'Nothing' if the
  range falls outside the memory. A word inside one chunk copies that chunk once; a word
  straddling a boundary goes byte by byte through 'writeBytes'.
-}
storeWord :: MemInst m -> Int -> Int -> Word64 -> Maybe (MemInst m)
storeWord = storeWordAt Low

-- | 'storeWord' at a security level: the bytes written take that level (SecWasm's E-STORE).
{-# INLINE storeWordAt #-}
storeWordAt :: SecLevel -> MemInst m -> Int -> Int -> Word64 -> Maybe (MemInst m)
storeWordAt level mem addr count word
    | not (inBounds mem addr count) = Nothing
    | offset + count <= chunkSize = Just (setLevels level addr count mem {chunks = IntMap.insert chunkIx written mem.chunks})
    | otherwise = writeBytesAt level mem addr [fromIntegral (word `shiftR` (8 * i)) | i <- [0 .. count - 1]]
  where
    (chunkIx, offset) = addr `quotRem` chunkSize
    current = IntMap.findWithDefault zeroChunk chunkIx mem.chunks
    written = UV.modify (\slots -> forM_ [0 .. count - 1] (\i -> MV.write slots (offset + i) (fromIntegral (word `shiftR` (8 * i))))) current

{- | Read @count@ bytes starting at effective byte address @addr@, in ascending order.
  'Nothing' if the range falls outside the memory. The address is an 'Int' (the caller
  forms it as @base + offset@ without 32-bit wraparound), so an out-of-range access is
  reported here rather than silently aliasing a wrapped-around address.
-}
readBytes :: MemInst m -> Int -> Int -> Maybe [Word8]
readBytes mem addr count
    | inBounds mem addr count = Just (bytesAt mem addr count)
    | otherwise = Nothing

-- | The bytes of an in-bounds range, one chunk lookup each.
bytesAt :: MemInst m -> Int -> Int -> [Word8]
bytesAt mem addr count = [byteAt a | a <- [addr .. addr + count - 1]]
  where
    byteAt a =
        let (chunkIx, offset) = a `quotRem` chunkSize
         in maybe 0 (\stored -> fromMaybe 0 (stored UV.!? offset)) (IntMap.lookup chunkIx mem.chunks)

{- | Write bytes starting at effective byte address @addr@, in ascending order.
  'Nothing' if the range falls outside the memory. Each chunk touched is copied once.
-}
writeBytes :: MemInst m -> Int -> [Word8] -> Maybe (MemInst m)
writeBytes = writeBytesAt Low

-- | 'writeBytes' at a security level.
writeBytesAt :: SecLevel -> MemInst m -> Int -> [Word8] -> Maybe (MemInst m)
writeBytesAt level mem addr payload
    | inBounds mem addr (length payload) = Just (setLevels level addr (length payload) mem {chunks = foldl' writeRun mem.chunks (runsByChunk addr payload)})
    | otherwise = Nothing
  where
    writeRun stored (chunkIx, offset, run) =
        let current = IntMap.findWithDefault zeroChunk chunkIx stored
         in IntMap.insert chunkIx (current UV.// zip [offset ..] run) stored

-- | Split a write into runs that each stay within one chunk: (chunk, offset in chunk, bytes).
runsByChunk :: Int -> [Word8] -> [(Int, Int, [Word8])]
runsByChunk _ [] = []
runsByChunk addr payload =
    let (chunkIx, offset) = addr `quotRem` chunkSize
        (run, rest) = splitAt (chunkSize - offset) payload
     in (chunkIx, offset, run) : runsByChunk (addr + length run) rest

{- | @memory.copy@: move @count@ bytes from @src@ to @dst@ within the memory, overlap-safe (the
  bytes are read before any is written). 'Nothing' if either range falls outside the memory —
  and then nothing is written.
-}
copyWithin :: Int -> Int -> Int -> MemInst m -> Maybe (MemInst m)
copyWithin = copyWithinAt Low

{- | 'copyWithin' under a context level: each copied byte keeps its own level, joined with the
  given one (the pc and the operands' levels, which decide whether and where bytes move).
-}
copyWithinAt :: SecLevel -> Int -> Int -> Int -> MemInst m -> Maybe (MemInst m)
copyWithinAt context dst src count mem = copyBetweenAt context dst src count mem mem

{- | @memory.copy@ from one memory to another (or the same): the bytes and their levels are read
  from the first and written to the second, as 'copyWithinAt' does within one.
-}
copyBetweenAt :: SecLevel -> Int -> Int -> Int -> MemInst from -> MemInst to -> Maybe (MemInst to)
copyBetweenAt context dst src count from to = do
    payload <- readBytes from src count
    let sourceLevels = [levelOfRange from a 1 | a <- [src .. src + count - 1]]
    written <- writeBytes to dst payload
    Just (foldl' (\acc (i, level) -> setLevels (joinLevel context level) (dst + i) 1 acc) written (zip [0 ..] sourceLevels))

{- | @memory.fill@: write @count@ copies of a byte from @dst@. 'Nothing' if the range is outside —
  decided before the bytes are materialised, since a count may be in the billions.
-}
fillBytes :: Int -> Word8 -> Int -> MemInst m -> Maybe (MemInst m)
fillBytes = fillBytesAt Low

-- | 'fillBytes' at a security level (the fill value's, joined with the context's).
fillBytesAt :: SecLevel -> Int -> Word8 -> Int -> MemInst m -> Maybe (MemInst m)
fillBytesAt level dst value count mem
    | inBounds mem dst count = writeBytesAt level mem dst (replicate count value)
    | otherwise = Nothing

-- *** Levels ***

joinLevel :: SecLevel -> SecLevel -> SecLevel
joinLevel Low l = l
joinLevel High _ = High

{- | The join of the levels of @count@ bytes from @addr@: what a load must compare with the
  level it declares. A memory that never held a secret answers without a lookup, and a range
  inside one chunk costs one lookup.
-}
{-# INLINE levelOfRange #-}
levelOfRange :: MemInst m -> Int -> Int -> SecLevel
levelOfRange mem addr count
    | IntMap.null mem.levels = Low
    | offset + count <= chunkSize = maybe Low chunkLevel (IntMap.lookup chunkIx mem.levels)
    | otherwise = foldl' joinLevel Low [levelOfRange mem a 1 | a <- [addr .. addr + count - 1]]
  where
    (chunkIx, offset) = addr `quotRem` chunkSize
    chunkLevel stored = if anySecret stored (offset `shiftR` 6) then High else Low
    lastWord = (offset + count - 1) `shiftR` 6
    anySecret :: UV.Vector Word64 -> Int -> Bool
    anySecret stored !w
        | w > lastWord = False
        | fromMaybe 0 (stored UV.!? w) .&. wordMask offset (offset + count) w /= 0 = True
        | otherwise = anySecret stored (w + 1)

{- | Give @count@ bytes from @addr@ one level without changing them, or 'Nothing' if they are
  out of bounds: how instantiation labels the policy's secret regions.
-}
labelRange :: SecLevel -> MemInst m -> Int -> Int -> Maybe (MemInst m)
labelRange level mem addr count
    | inBounds mem addr count = Just (setLevels level addr count mem)
    | otherwise = Nothing

{- | Give @count@ bytes from @addr@ (already checked to be in bounds) one level. Marking bytes
  public in a chunk that has no levels changes nothing, so it costs nothing; that is the common
  case, and the one every unlabelled program stays in.
-}
{-# INLINE setLevels #-}
setLevels :: SecLevel -> Int -> Int -> MemInst m -> MemInst m
setLevels level addr count mem
    | Low <- level, IntMap.null mem.levels = mem
    | count <= 0 = mem
    | otherwise = setLevelsFrom level addr count mem

-- | 'setLevels' where there is something to do: chunk by chunk.
setLevelsFrom :: SecLevel -> Int -> Int -> MemInst m -> MemInst m
setLevelsFrom level addr count mem
    | count <= 0 = mem
    | offset + count <= chunkSize = inChunk count
    | otherwise = setLevelsFrom level (addr + here) (count - here) (inChunk here)
  where
    (chunkIx, offset) = addr `quotRem` chunkSize
    here = chunkSize - offset
    -- The first @n@ bytes of the range, which are inside this chunk.
    inChunk n = case IntMap.lookup chunkIx mem.levels of
        Nothing -> case level of
            Low -> mem
            High -> mem {levels = IntMap.insert chunkIx (marked n publicChunk) mem.levels}
        Just current
            -- The bytes are at this level already: nothing to write. Once a region holds
            -- secrets this is most stores into it, and such a store copies no levels.
            | unchanged n current (offset `shiftR` 6) -> mem
            | otherwise -> mem {levels = IntMap.insert chunkIx (marked n current) mem.levels}
    lastWordOf n = (offset + n - 1) `shiftR` 6
    unchanged :: Int -> UV.Vector Word64 -> Int -> Bool
    unchanged n current !w
        | w > lastWordOf n = True
        | otherwise =
            let mask = wordMask offset (offset + n) w
                bits = fromMaybe 0 (current UV.!? w) .&. mask
             in (case level of High -> bits == mask; Low -> bits == 0) && unchanged n current (w + 1)
    marked n = UV.modify $ \slots ->
        forM_ [offset `shiftR` 6 .. lastWordOf n] $ \w ->
            let mask = wordMask offset (offset + n) w
             in MV.modify slots (\bits -> case level of High -> bits .|. mask; Low -> bits .&. complement mask) w
