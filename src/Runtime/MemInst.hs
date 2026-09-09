{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}

{- | Linear memory: the one piece of mutable runtime state the interpreter still keeps
  outside the type-indexed value stack and locals. (GlobalInsts are tracked by the typed
  'Runtime.Stack.GlobalInsts'; functions by 'Runtime.Interpreter.FuncInsts'.)

  A 'MemInst' is indexed by its declared 'MemShape', so — like every other instance — it
  carries its type. The index is a phantom (the byte array does not depend on it); the
  operations below thread it through unchanged. The declared limits are also kept at the term
  level, because @memory.grow@ has to consult the maximum at run time.
-}
module Runtime.MemInst (
    MemInst,
    allocMemory,
    growMemory,
    memoryPages,
    readBytes,
    writeBytes,
) where

import Data.Kind (Type)
import Data.Vector.Unboxed qualified as UV
import Data.Word (Word32, Word8)

import Syntax.Types (Limits (..))
import Validation.Shape (MemShape)

-- *** Linear memory ***

{- | A linear memory: a flat, zero-initialised byte array plus its declared limits, indexed by
  its shape.

Updates are functional (copy-on-write). This is O(n) per store, which is fine for the
programs we run; a mutable representation can come later.
-}
type MemInst :: MemShape -> Type
data MemInst m = MemInst
    { limits :: Limits
    , bytes :: UV.Vector Word8
    }

-- | Bytes per WebAssembly page.
pageSize :: Int
pageSize = 65536

-- | The hard ceiling of a 32-bit memory, in pages (4 GiB).
maxPages :: Word32
maxPages = 65536

-- | Allocate a memory at its declared minimum size, zero-initialised.
allocMemory :: Limits -> MemInst m
allocMemory declared = MemInst declared (UV.replicate (fromIntegral declared.min * pageSize) 0)

-- | Size of a memory in whole pages.
memoryPages :: MemInst m -> Word32
memoryPages mem = fromIntegral (UV.length mem.bytes `div` pageSize)

{- | Grow a memory by @delta@ pages (zero-filled), or refuse if the result would exceed the
  declared maximum or the 4 GiB ceiling. Refusal is the spec's @memory.grow@ failure, which
  the instruction reports as @-1@ rather than trapping.
-}
growMemory :: Word32 -> MemInst m -> Maybe (MemInst m)
growMemory delta mem
    | requested > fromIntegral allowed = Nothing
    | otherwise = Just mem {bytes = mem.bytes UV.++ UV.replicate (fromIntegral delta * pageSize) 0}
  where
    requested = fromIntegral (memoryPages mem) + fromIntegral delta :: Integer
    allowed = maybe maxPages (min maxPages) mem.limits.max

{- | Read @count@ bytes starting at effective byte address @addr@, in ascending order.
  'Nothing' if the range falls outside the memory. The address is an 'Int' (the caller
  forms it as @base + offset@ without 32-bit wraparound), so an out-of-range access is
  reported here rather than silently aliasing a wrapped-around address.
-}
readBytes :: MemInst m -> Int -> Int -> Maybe [Word8]
readBytes mem addr count
    | addr >= 0 && addr + count <= UV.length mem.bytes = Just (UV.toList (UV.slice addr count mem.bytes))
    | otherwise = Nothing

{- | Write bytes starting at effective byte address @addr@, in ascending order.
  'Nothing' if the range falls outside the memory.
-}
writeBytes :: MemInst m -> Int -> [Word8] -> Maybe (MemInst m)
writeBytes mem addr payload
    | addr >= 0 && addr + length payload <= UV.length mem.bytes =
        Just mem {bytes = mem.bytes UV.// zip [addr ..] payload}
    | otherwise = Nothing
