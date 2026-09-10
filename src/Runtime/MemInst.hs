{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}

{- | Linear memory: the one piece of mutable runtime state the interpreter still keeps
  outside the type-indexed value stack and locals. (GlobalInsts are tracked by the typed
  'Runtime.Stack.GlobalInsts'; functions by 'Runtime.Interpreter.FuncInsts'.)

  A 'MemInst' is indexed by its declared 'MemShape', so — like every other instance — it
  carries its type. The index is a phantom (the contents do not depend on it); the operations
  below thread it through unchanged. The declared limits are also kept at the term level,
  because @memory.grow@ has to consult the maximum at run time.

  The bytes are stored sparsely, one 64 KiB page at a time and only once a page has been
  written: a page that was never touched reads as zeros without existing. So declaring or
  growing to a large memory costs nothing until it is used, which is what lets a module ask
  for the full 4 GiB the spec allows, and a store copies one page rather than the whole memory.
-}
module Runtime.MemInst (
    MemInst,
    allocMemory,
    growMemory,
    memoryPages,
    maxMemoryPages,
    readBytes,
    writeBytes,
    copyWithin,
    fillBytes,
) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.Vector.Unboxed qualified as UV
import Data.Word (Word32, Word8)

import Syntax.Types (Limits (..))
import Validation.Shape (MemShape)

-- *** Linear memory ***

-- | A linear memory: its declared limits, its current size in pages, and the written pages.
type MemInst :: MemShape -> Type
data MemInst m = MemInst
    { limits :: Limits
    , pageCount :: Word32
    , pages :: IntMap (UV.Vector Word8)
    -- ^ by page index; an absent page is all zeros
    }

-- | Bytes per WebAssembly page.
pageSize :: Int
pageSize = 65536

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

byteSize :: MemInst m -> Integer
byteSize mem = toInteger mem.pageCount * toInteger pageSize

inBounds :: MemInst m -> Int -> Int -> Bool
inBounds mem addr count = addr >= 0 && toInteger addr + toInteger count <= byteSize mem

{- | Read @count@ bytes starting at effective byte address @addr@, in ascending order.
  'Nothing' if the range falls outside the memory. The address is an 'Int' (the caller
  forms it as @base + offset@ without 32-bit wraparound), so an out-of-range access is
  reported here rather than silently aliasing a wrapped-around address.
-}
readBytes :: MemInst m -> Int -> Int -> Maybe [Word8]
readBytes mem addr count
    | inBounds mem addr count = Just [byteAt a | a <- [addr .. addr + count - 1]]
    | otherwise = Nothing
  where
    byteAt a =
        let (page, offset) = a `divMod` pageSize
         in maybe 0 (\stored -> fromMaybe 0 (stored UV.!? offset)) (IntMap.lookup page mem.pages)

{- | Write bytes starting at effective byte address @addr@, in ascending order.
  'Nothing' if the range falls outside the memory. Each page touched is copied once.
-}
writeBytes :: MemInst m -> Int -> [Word8] -> Maybe (MemInst m)
writeBytes mem addr payload
    | inBounds mem addr (length payload) = Just mem {pages = foldl' writeRun mem.pages (runsByPage addr payload)}
    | otherwise = Nothing
  where
    writeRun stored (page, offset, chunk) =
        let current = IntMap.findWithDefault (UV.replicate pageSize 0) page stored
         in IntMap.insert page (current UV.// zip [offset ..] chunk) stored

-- | Split a write into runs that each stay within one page: (page, offset in page, bytes).
runsByPage :: Int -> [Word8] -> [(Int, Int, [Word8])]
runsByPage _ [] = []
runsByPage addr payload =
    let (page, offset) = addr `divMod` pageSize
        (chunk, rest) = splitAt (pageSize - offset) payload
     in (page, offset, chunk) : runsByPage (addr + length chunk) rest

{- | @memory.copy@: move @count@ bytes from @src@ to @dst@ within the memory, overlap-safe (the
  bytes are read before any is written). 'Nothing' if either range falls outside the memory —
  and then nothing is written.
-}
copyWithin :: Int -> Int -> Int -> MemInst m -> Maybe (MemInst m)
copyWithin dst src count mem = do
    payload <- readBytes mem src count
    writeBytes mem dst payload

-- | @memory.fill@: write @count@ copies of a byte from @dst@. 'Nothing' if the range is outside.
fillBytes :: Int -> Word8 -> Int -> MemInst m -> Maybe (MemInst m)
fillBytes dst value count mem = writeBytes mem dst (replicate count value)
