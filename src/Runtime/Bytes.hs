-- | Little-endian marshalling between fixed-width words and byte lists, used by the
--   interpreter's memory load/store.
module Runtime.Bytes
    ( bytesOfWord32
    , bytesOfWord64
    , word32OfBytes
    , word64OfBytes
    ) where

import Data.Bits (shiftL, shiftR, (.|.))
import Data.Word (Word8, Word32, Word64)

bytesOfWord32 :: Word32 -> [Word8]
bytesOfWord32 w = [fromIntegral (w `shiftR` (8 * i)) | i <- [0 .. 3]]

bytesOfWord64 :: Word64 -> [Word8]
bytesOfWord64 w = [fromIntegral (w `shiftR` (8 * i)) | i <- [0 .. 7]]

word32OfBytes :: [Word8] -> Word32
word32OfBytes bytes = foldr (.|.) 0 [fromIntegral b `shiftL` (8 * i) | (i, b) <- zip [0 ..] bytes]

word64OfBytes :: [Word8] -> Word64
word64OfBytes bytes = foldr (.|.) 0 [fromIntegral b `shiftL` (8 * i) | (i, b) <- zip [0 ..] bytes]
