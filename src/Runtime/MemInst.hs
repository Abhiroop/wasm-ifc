{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}

-- | Linear memory: the one piece of mutable runtime state the interpreter still keeps
--   outside the type-indexed value stack and locals. (GlobalInsts are tracked by the typed
--   'Runtime.Stack.GlobalInsts'; functions by 'Runtime.Interpreter.FuncInsts'.)
--
--   A 'MemInst' is indexed by its declared 'MemShape', so — like every other instance — it
--   carries its type. The index is a phantom (the byte array does not depend on it); the
--   operations below thread it through unchanged.
module Runtime.MemInst where

import Data.Kind (Type)
import qualified Data.Vector.Unboxed as UV
import Data.Word (Word8, Word32)

import Validation.Shape (MemShape)

{- *** Linear memory *** -}

-- | A linear memory: a flat, zero-initialised byte array, indexed by its declared shape.
--
-- Updates are functional (copy-on-write). This is O(n) per store, which is fine for the
-- programs we run; a mutable representation can come later.
type MemInst :: MemShape -> Type
newtype MemInst m = MemInst (UV.Vector Word8)

-- | Bytes per WebAssembly page.
pageSize :: Int
pageSize = 65536

-- | Allocate @pages@ pages of zero-initialised memory.
allocMemory :: Word32 -> MemInst m
allocMemory pages = MemInst (UV.replicate (fromIntegral pages * pageSize) 0)

-- | Total size of a memory in bytes.
memoryBytes :: MemInst m -> Int
memoryBytes (MemInst bytes) = UV.length bytes

-- | Size of a memory in whole pages.
memoryPages :: MemInst m -> Word32
memoryPages (MemInst bytes) = fromIntegral (UV.length bytes `div` pageSize)

-- | Grow a memory by @delta@ pages (zero-filled). No maximum is enforced.
growMemory :: Word32 -> MemInst m -> MemInst m
growMemory delta (MemInst bytes) =
    MemInst (bytes UV.++ UV.replicate (fromIntegral delta * pageSize) 0)

-- | Read @count@ bytes starting at @addr@, in ascending address order.
--   'Nothing' if the range falls outside the memory.
readBytes :: MemInst m -> Word32 -> Int -> Maybe [Word8]
readBytes (MemInst bytes) addr count
    | start + count <= UV.length bytes = Just [bytes UV.! (start + i) | i <- [0 .. count - 1]]
    | otherwise                        = Nothing
  where
    start = fromIntegral addr

-- | Write bytes starting at @addr@, in ascending address order.
--   'Nothing' if the range falls outside the memory.
writeBytes :: MemInst m -> Word32 -> [Word8] -> Maybe (MemInst m)
writeBytes (MemInst bytes) addr payload
    | start + length payload <= UV.length bytes =
        Just (MemInst (bytes UV.// zip [start ..] payload))
    | otherwise = Nothing
  where
    start = fromIntegral addr
