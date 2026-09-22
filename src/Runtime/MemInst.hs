{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
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

  Loads and stores of a whole value go through 'loadWord' and 'storeWord', a little-endian word
  at a time; the byte-list functions serve the bulk operations, data segments and the WASI host.
-}
module Runtime.MemInst (
    MemInst,
    allocMemory,
    growMemory,
    memoryPages,
    maxMemoryPages,
    loadWord,
    storeWord,
    readBytes,
    writeBytes,
    copyWithin,
    fillBytes,
) where

import Control.Monad (forM_)
import Data.Bits (shiftL, shiftR, (.|.))
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.Vector.Unboxed qualified as UV
import Data.Vector.Unboxed.Mutable qualified as MV
import Data.Word (Word32, Word64, Word8)

import Syntax.Types (Limits (..))
import Validation.Shape (MemShape)

-- *** Linear memory ***

{- | A linear memory: its declared limits, its current size in pages, and the written chunks.
  TODO(ifc P1): __this record does not grow a label store.__ SecWasm labels memory per byte,
  flow-sensitively, at run time (§3.2: each location is a pair @(byte, ℓ)@), which would mean a
  second sparse chunk map here and a label join on every read. The IFC layer takes the other
  road: a module /declares/ the labelled layout of its memory as a
  'Syntax.TypesIFC.MemPolicy' of consecutive spans, and each load and store carries a
  'Syntax.TypesIFC.SpanAt' proof of the span it targets (see the memory section of
  "Syntax.InstructionsIFC"). Because a span's label is then fixed for the module's lifetime,
  every label check is static and nothing about labels survives to run time: this record stays
  exactly as it is, and the only new run-time obligation is to bounds-check an access against
  the span its proof names ('Syntax.TypesIFC.spanBounds' gives the two numbers) instead of
  against the whole memory. If the declared layout ever proves too rigid for a case study — the
  paper's worry about compiled code mixing secret and public data — the per-byte store
  described above is the fallback, and it is additive to what is here.
-}
type MemInst :: MemShape -> Type
data MemInst m = MemInst
    { limits :: !Limits
    , pageCount :: !Word32
    , chunks :: !(IntMap (UV.Vector Word8))
    -- ^ by chunk index; an absent chunk is all zeros, a present one is 'chunkSize' bytes long
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

-- | The hard ceiling of a 32-bit memory, in pages (4 GiB).
maxMemoryPages :: Word32
maxMemoryPages = 65536

-- | Allocate a memory at its declared minimum size, zero-initialised.
allocMemory :: Limits -> MemInst m
allocMemory declared = MemInst declared declared.min IntMap.empty

-- | Size of a memory in whole pages.
memoryPages :: MemInst m -> Word32
memoryPages mem = mem.pageCount

{- | Grow a memory by @delta@ pages (zero-filled), or refuse if the result would exceed the
  declared maximum or the 4 GiB ceiling. Refusal is the spec's @memory.grow@ failure, which
  the instruction reports as @-1@ rather than trapping.
-}
growMemory :: Word32 -> MemInst m -> Maybe (MemInst m)
growMemory delta mem
    | requested > toInteger allowed = Nothing
    | otherwise = Just mem {pageCount = fromInteger requested}
  where
    requested = toInteger mem.pageCount + toInteger delta
    allowed = maybe maxMemoryPages (min maxMemoryPages) mem.limits.max

{- | Whether @count@ bytes from @addr@ lie inside the memory. Computed in 'Int', which is 64 bits
  wide on the platforms GHC builds this for (the effective address already relies on it): the
  largest memory is 2^32 bytes and an address is a 32-bit base plus a 32-bit offset, so nothing
  here can overflow. It used to be 'Integer', an allocation on every load and store for nothing.
-}
inBounds :: MemInst m -> Int -> Int -> Bool
inBounds mem addr count = addr >= 0 && count >= 0 && addr + count <= fromIntegral mem.pageCount * pageSize

{- | Read a little-endian word of @count@ bytes (1 to 8) at effective address @addr@,
  zero-extended; 'Nothing' if the range falls outside the memory. A word inside one chunk —
  every word but those straddling a chunk boundary — costs one chunk lookup and no list.
-}
loadWord :: MemInst m -> Int -> Int -> Maybe Word64
loadWord mem addr count
    | not (inBounds mem addr count) = Nothing
    | offset + count <= chunkSize = Just (maybe 0 assemble (IntMap.lookup chunkIx mem.chunks))
    | otherwise = Just (foldr (.|.) 0 [fromIntegral b `shiftL` (8 * i) | (i, b) <- zip [0 ..] (bytesAt mem addr count)])
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
storeWord mem addr count word
    | not (inBounds mem addr count) = Nothing
    | offset + count <= chunkSize = Just mem {chunks = IntMap.insert chunkIx written mem.chunks}
    | otherwise = writeBytes mem addr [fromIntegral (word `shiftR` (8 * i)) | i <- [0 .. count - 1]]
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
writeBytes mem addr payload
    | inBounds mem addr (length payload) = Just mem {chunks = foldl' writeRun mem.chunks (runsByChunk addr payload)}
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
copyWithin dst src count mem = do
    payload <- readBytes mem src count
    writeBytes mem dst payload

{- | @memory.fill@: write @count@ copies of a byte from @dst@. 'Nothing' if the range is outside —
  decided before the bytes are materialised, since a count may be in the billions.
-}
fillBytes :: Int -> Word8 -> Int -> MemInst m -> Maybe (MemInst m)
fillBytes dst value count mem
    | inBounds mem dst count = writeBytes mem dst (replicate count value)
    | otherwise = Nothing
