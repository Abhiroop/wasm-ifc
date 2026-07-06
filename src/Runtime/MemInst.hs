{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}

{- | Linear memory: the one piece of mutable runtime state the interpreter still keeps
  outside the type-indexed value stack and locals. (GlobalInsts are tracked by the typed
  'Runtime.Stack.GlobalInsts'; functions by 'Runtime.Interpreter.FuncInsts'.)

  A 'MemInst' is indexed by its declared 'MemShape', so — like every other instance — it
  carries its type. The index is a phantom (the byte array does not depend on it); the
  operations below thread it through unchanged.
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

import Validation.Shape (MemShape)

-- *** Linear memory ***

{- | A linear memory: a flat, zero-initialised byte array, indexed by its declared shape.

Updates are functional (copy-on-write). This is O(n) per store, which is fine for the
programs we run; a mutable representation can come later.
-}
type MemInst :: MemShape -> Type
newtype MemInst m = MemInst (UV.Vector Word8)

-- | Bytes per WebAssembly page.
pageSize :: Int
pageSize = 65536

-- | Allocate @pages@ pages of zero-initialised memory.
allocMemory :: Word32 -> MemInst m
allocMemory pages = MemInst (UV.replicate (fromIntegral pages * pageSize) 0)

-- | Size of a memory in whole pages.
memoryPages :: MemInst m -> Word32
memoryPages (MemInst bytes) = fromIntegral (UV.length bytes `div` pageSize)

-- | Grow a memory by @delta@ pages (zero-filled). No maximum is enforced.
growMemory :: Word32 -> MemInst m -> MemInst m
growMemory delta (MemInst bytes) =
    MemInst (bytes UV.++ UV.replicate (fromIntegral delta * pageSize) 0)

{- | Read @count@ bytes starting at effective byte address @addr@, in ascending order.
  'Nothing' if the range falls outside the memory. The address is an 'Int' (the caller
  forms it as @base + offset@ without 32-bit wraparound), so an out-of-range access is
  reported here rather than silently aliasing a wrapped-around address.
-}
readBytes :: MemInst m -> Int -> Int -> Maybe [Word8]
readBytes (MemInst bytes) addr count
    | addr >= 0 && addr + count <= UV.length bytes = Just (UV.toList (UV.slice addr count bytes))
    | otherwise = Nothing

{- | Write bytes starting at effective byte address @addr@, in ascending order.
  'Nothing' if the range falls outside the memory.
-}
writeBytes :: MemInst m -> Int -> [Word8] -> Maybe (MemInst m)
writeBytes (MemInst bytes) addr payload
    | addr >= 0 && addr + length payload <= UV.length bytes =
        Just (MemInst (bytes UV.// zip [addr ..] payload))
    | otherwise = Nothing
