{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

{- | The WASI (WebAssembly System Interface) Preview 1 host, and the IO driver that runs a
  module against it. This is the effectful half of the effect-request boundary: the pure,
  total 'Runtime.Interpreter.step' never performs IO — when a call resolves to an imported
  host function it hands out a 'Runtime.Interpreter.HostRequest' — and 'runWithWasi' is the
  loop that performs each request here and resumes the module. All IO lives in this module.

  Only @fd_write@ (to the standard streams) and @proc_exit@ are provided.
-}
module Runtime.Wasi (
    Errno (..),
    errnoWord,
    WasiOutcome (..),
    runWasiCall,
    Completion (..),
    runWithWasi,
) where

import Data.ByteString qualified as BS
import Data.Text (Text)
import Data.Word (Word32, Word8)
import System.IO (Handle, hFlush, stderr, stdout)

import Runtime.Bytes (bytesOfWord32, word32OfBytes)
import Runtime.Host (WasiFunc (..))
import Runtime.Interpreter (HostRequest (..), currentMem, resumeWith, storeMem)
import Runtime.MemInst (MemInst, readBytes, writeBytes)
import Runtime.Module (Invocation (..), RunError, SomeHostRequest (..), SomeModule, Value, continueWith, invokeExport)
import Runtime.Stack (ValueStack (..))
import Syntax.Types (FuncType (..), ValType)
import Validation.Shape (MemShape)

-- *** Error numbers (the subset we return) ***

-- | The WASI @errno@ values this host can return.
data Errno
    = Success
    | -- | bad file descriptor
      Badf
    | -- | a pointer or range fell outside linear memory
      Fault
    deriving stock (Eq, Show)

errnoWord :: Errno -> Word32
errnoWord Success = 0
errnoWord Badf = 8
errnoWord Fault = 21

-- *** Performing one call ***

-- | What a host call produced: results to push and the memory as it left it, or an exit.
data WasiOutcome (rs :: [ValType]) (m :: MemShape) where
    WasiReturn :: ValueStack rs -> MemInst m -> WasiOutcome rs m
    WasiExit :: Int -> WasiOutcome rs m

{- | Perform a WASI call. The arguments arrive as a stack of exactly the function's parameter
  shape (last argument on top), so each case has precisely the operands it needs. Memory is
  read and written through the bounds-checked 'readBytes'/'writeBytes', so a pointer outside
  linear memory yields 'Fault' rather than a crash.
-}
runWasiCall :: WasiFunc ('FuncType ps rs) -> ValueStack ps -> MemInst m -> IO (WasiOutcome rs m)
runWasiCall FdWrite (nwrittenPtr :# iovsLen :# iovsPtr :# fd :# VNil) mem =
    case gatherIovecs mem iovsPtr (fromIntegral iovsLen) of
        Nothing -> pure (returning Fault mem)
        Just chunks -> do
            written <- writeToFd fd (concat chunks)
            pure $ case written of
                Nothing -> returning Badf mem
                Just count -> case writeBytes mem (fromIntegral nwrittenPtr) (bytesOfWord32 (fromIntegral count)) of
                    Just mem' -> returning Success mem'
                    Nothing -> returning Fault mem
  where
    returning errno = WasiReturn (errnoWord errno :# VNil)
runWasiCall ProcExit (code :# VNil) _ = pure (WasiExit (fromIntegral code))

{- | Read @count@ iovec structures (each an 8-byte @(ptr, len)@ pair) starting at @base@,
  then the bytes each one points at. 'Nothing' if any pointer or length is out of range.
-}
gatherIovecs :: MemInst m -> Word32 -> Int -> Maybe [[Word8]]
gatherIovecs mem base count = traverse readIovec [0 .. count - 1]
  where
    readIovec i = do
        header <- readBytes mem (fromIntegral base + i * 8) 8
        let (ptrBytes, lenBytes) = splitAt 4 header
        readBytes mem (fromIntegral (word32OfBytes ptrBytes)) (fromIntegral (word32OfBytes lenBytes))

{- | Write bytes to a standard file descriptor (1 = stdout, 2 = stderr). 'Nothing' for any
  other descriptor (there is no file system), which the caller reports as 'Badf'.
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

-- *** The driver ***

-- | How a run under the WASI host ends: normally, with results, or through @proc_exit@.
data Completion
    = Ran SomeModule [Value]
    | Exited Int

{- | Invoke an export and serve every host call it makes until it returns or exits. Each
  request is performed against the module's memory, the memory is stored back, and the
  module resumes where it left off.
-}
runWithWasi :: SomeModule -> Text -> [Value] -> IO (Either RunError Completion)
runWithWasi wasmModule name args = serve (invokeExport wasmModule name args)
  where
    serve :: Either RunError Invocation -> IO (Either RunError Completion)
    serve (Left err) = pure (Left err)
    serve (Right (Returned finished results)) = pure (Right (Ran finished results))
    serve (Right (CalledHost (SomeHostRequest shapeS funcs exports rsS (HostRequest wasiFunc callArgs store suspended)))) = do
        outcome <- runWasiCall wasiFunc callArgs (currentMem store)
        case outcome of
            WasiExit code -> pure (Right (Exited code))
            WasiReturn results mem' ->
                serve (continueWith shapeS funcs exports rsS (resumeWith (storeMem mem' store) results suspended))
