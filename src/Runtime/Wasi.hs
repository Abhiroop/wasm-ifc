{- | A minimal WASI (WebAssembly System Interface) host layer — the "Preview 1"
  (@wasi_snapshot_preview1@) subset needed to run a program that prints and exits.

  This module is deliberately self-contained and does /not/ touch the pure interpreter. It
  is the outer, effectful half of the planned effect-request boundary (see @TODO.md §H@):

    * the pure, total 'Runtime.Interpreter.step' stays pure — when a @call@ resolves to an
      imported (host) function it will yield a request rather than doing IO itself;
    * an IO driver hands that request here via 'runWasiCall', which performs the effect and
      hands back a 'WasiOutcome' (an @errno@ to push, the possibly-updated memory, or a
      program exit) for the driver to resume the machine with.

  So all IO is quarantined to this module and the future driver; the soundness core is
  untouched. Only 'FdWrite' and 'ProcExit' are implemented so far.
-}
module Runtime.Wasi (
    wasiModuleName,
    WasiFunc (..),
    resolveWasiImport,
    wasiSignature,
    Errno (..),
    errnoWord,
    WasiOutcome (..),
    runWasiCall,
) where

import Data.ByteString qualified as BS
import Data.Text (Text)
import Data.Word (Word32, Word8)
import System.IO (Handle, hFlush, stderr, stdout)

import Runtime.Bytes (bytesOfWord32, word32OfBytes)
import Runtime.MemInst (MemInst, readBytes, writeBytes)
import Syntax.Types (FuncType (..), ValType (..))

-- | The import module name WASI functions are resolved against.
wasiModuleName :: Text
wasiModuleName = "wasi_snapshot_preview1"

-- | The supported WASI Preview 1 functions.
data WasiFunc
    = -- | @fd_write(fd, iovs, iovs_len, nwritten) -> errno@
      FdWrite
    | -- | @proc_exit(code) -> !@
      ProcExit
    deriving stock (Eq, Show)

-- | Resolve an import's field name to a supported function (@Nothing@ if unsupported).
resolveWasiImport :: Text -> Maybe WasiFunc
resolveWasiImport name = case name of
    "fd_write" -> Just FdWrite
    "proc_exit" -> Just ProcExit
    _ -> Nothing

{- | The WebAssembly type each function must be imported at, so elaboration can check the
  import's declared type against the one WASI expects.
-}
wasiSignature :: WasiFunc -> FuncType
wasiSignature FdWrite = FuncType [I32, I32, I32, I32] [I32]
wasiSignature ProcExit = FuncType [I32] []

-- *** Error numbers (the subset we return) ***

-- | The WASI @errno@ values this layer can return.
data Errno
    = Success
    | -- | bad file descriptor
      Badf
    | -- | a pointer/range fell outside linear memory
      Fault
    | -- | malformed call
      Inval
    deriving stock (Eq, Show)

errnoWord :: Errno -> Word32
errnoWord Success = 0
errnoWord Badf = 8
errnoWord Fault = 21
errnoWord Inval = 28

-- *** Executing a call ***

-- | The result of a WASI call, for the driver to resume the machine with.
data WasiOutcome m
    = -- | push this @errno@; store this (possibly-updated) memory back
      WasiReturn Word32 (MemInst m)
    | -- | @proc_exit@: terminate the program with this code
      WasiExit Int

{- | Perform a WASI call: given its integer arguments and the current linear memory, do its
  effect in IO and report the outcome. Memory reads/writes go through the bounds-checked
  'readBytes'/'writeBytes', so an out-of-range pointer yields 'Fault' rather than a crash.
-}
runWasiCall :: WasiFunc -> [Word32] -> MemInst m -> IO (WasiOutcome m)
runWasiCall FdWrite [fd, iovs, iovsLen, nwritten] mem =
    case gatherIovecs mem iovs (fromIntegral iovsLen) of
        Nothing -> pure (WasiReturn (errnoWord Fault) mem)
        Just chunks -> do
            written <- writeToFd fd (concat chunks)
            pure $ case written of
                Nothing -> WasiReturn (errnoWord Badf) mem
                Just count ->
                    case writeBytes mem (fromIntegral nwritten) (bytesOfWord32 (fromIntegral count)) of
                        Just mem' -> WasiReturn (errnoWord Success) mem'
                        Nothing -> WasiReturn (errnoWord Fault) mem
runWasiCall ProcExit [code] _ = pure (WasiExit (fromIntegral code))
runWasiCall _ _ mem = pure (WasiReturn (errnoWord Inval) mem)

{- | Read @count@ iovec structures (each an 8-byte @(ptr, len)@ pair) starting at @base@,
  then the bytes each one points at. 'Nothing' if any pointer/length is out of range.
-}
gatherIovecs :: MemInst m -> Word32 -> Int -> Maybe [[Word8]]
gatherIovecs mem base count = traverse readIovec [0 .. count - 1]
  where
    readIovec i = do
        header <- readBytes mem (fromIntegral base + i * 8) 8
        let (ptrBytes, lenBytes) = splitAt 4 header
        readBytes mem (fromIntegral (word32OfBytes ptrBytes)) (fromIntegral (word32OfBytes lenBytes))

{- | Write bytes to a standard file descriptor (1 = stdout, 2 = stderr). 'Nothing' for any
  other descriptor (no real filesystem yet), which the caller reports as 'Badf'.
-}
writeToFd :: Word32 -> [Word8] -> IO (Maybe Int)
writeToFd fd payload = case standardHandle fd of
    Nothing -> pure Nothing
    Just handle -> do
        BS.hPut handle (BS.pack payload)
        hFlush handle
        pure (Just (length payload))

standardHandle :: Word32 -> Maybe Handle
standardHandle 1 = Just stdout
standardHandle 2 = Just stderr
standardHandle _ = Nothing
