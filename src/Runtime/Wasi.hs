{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

{- | The WASI (WebAssembly System Interface) Preview 1 host, and the IO driver that runs a
  module against it. This is the effectful half of the effect-request boundary: the pure,
  total 'Runtime.Interpreter.step' never performs IO — when a call resolves to an imported
  host function it hands out a 'Runtime.Interpreter.HostRequest' — and 'runWithWasi' is the
  loop that performs each request here and resumes the module. All IO lives in this module.

  The host keeps a descriptor table (the standard streams, the preopened directories, and
  whatever the module opens), resolves guest paths inside their preopened directory (a path
  may not climb above it), and speaks the interface's binary layouts. Sockets are not
  provided, nor hard links.
-}
module Runtime.Wasi (
    WasiConfig (..),
    Preopen (..),
    Errno (..),
    errnoWord,
    WasiHost,
    newHost,
    WasiOutcome (..),
    runWasiCall,
    Completion (..),
    runWithWasi,
) where

import Control.Concurrent (threadDelay, yield)
import Control.Exception (IOException, try)
import Control.Monad (foldM, forM, unless, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Except (ExceptT (..), except, runExceptT, throwE)
import Data.Bits (testBit, xor)
import Data.ByteString qualified as BS
import Data.Either (fromRight)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import Data.List (sort)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8', encodeUtf8)
import Data.Time.Clock (UTCTime)
import Data.Time.Clock.POSIX (getPOSIXTime, posixSecondsToUTCTime, utcTimeToPOSIXSeconds)
import Data.Word (Word16, Word32, Word64, Word8)
import GHC.Clock (getMonotonicTimeNSec)
import GHC.IO.Exception (IOErrorType (..))
import System.CPUTime (getCPUTime)
import System.Directory (
    createDirectory,
    createFileLink,
    doesDirectoryExist,
    doesFileExist,
    getAccessTime,
    getFileSize,
    getModificationTime,
    getSymbolicLinkTarget,
    listDirectory,
    pathIsSymbolicLink,
    removeDirectory,
    removeFile,
    renamePath,
    setAccessTime,
    setModificationTime,
 )
import System.FilePath ((</>))
import System.IO (
    BufferMode (NoBuffering),
    Handle,
    IOMode (..),
    SeekMode (..),
    hClose,
    hFlush,
    hSeek,
    hSetBuffering,
    hSetFileSize,
    hTell,
    openFile,
    stderr,
    stdin,
    stdout,
    withBinaryFile,
 )
import System.IO.Error (ioeGetErrorType)

import Runtime.Bytes (bytesOfWord32, bytesOfWord64, word32OfBytes, word64OfBytes)
import Runtime.Host (WasiFunc (..))
import Runtime.Interpreter (HostRequest (..), currentMem, resumeWith, storeMem)
import Runtime.MemInst (MemInst, readBytes, writeBytes)
import Runtime.Module (Invocation (..), RunError, SomeHostRequest (..), SomeModule, Value, continueWith, invokeExport)
import Runtime.Numeric (toSigned64)
import Runtime.Stack (ValueStack (..))
import Syntax.Types (FuncType (..), ValType (..))
import Validation.Shape (MemShape)

-- *** Configuration and the descriptor table ***

-- | What a run is given: its argument vector (including @argv[0]@), environment, and preopens.
data WasiConfig = WasiConfig
    { arguments :: [Text]
    , environment :: [(Text, Text)]
    , preopens :: [Preopen]
    -- ^ become descriptors 3, 4, … in order
    }

-- | A host directory the module may reach, under the name the guest sees.
data Preopen = Preopen
    { guestPath :: Text
    , hostPath :: FilePath
    }

data Descriptor
    = StandardStream Handle
    | -- | a directory on the host, with its guest name if it is a preopen
      Directory FilePath (Maybe Text)
    | -- | an open file: host path, handle, append mode
      File FilePath Handle Bool

data WasiHost = WasiHost
    { config :: WasiConfig
    , descriptors :: IORef (Map Word32 Descriptor)
    }

-- | A host with the standard streams at 0–2 and the preopens from 3 on.
newHost :: WasiConfig -> IO WasiHost
newHost cfg = do
    let streams = [(0, StandardStream stdin), (1, StandardStream stdout), (2, StandardStream stderr)]
        dirs = [(fd, Directory p.hostPath (Just p.guestPath)) | (fd, p) <- zip [3 ..] cfg.preopens]
    table <- newIORef (Map.fromList (streams ++ dirs))
    pure (WasiHost cfg table)

-- *** Error numbers ***

-- | The interface's @errno@ values, in its numbering (so 'fromEnum' is the number).
data Errno
    = Success
    | TooBig
    | Acces
    | Addrinuse
    | Addrnotavail
    | Afnosupport
    | Again
    | Already
    | Badf
    | Badmsg
    | Busy
    | Canceled
    | Child
    | Connaborted
    | Connrefused
    | Connreset
    | Deadlk
    | Destaddrreq
    | Dom
    | Dquot
    | Exist
    | Fault
    | Fbig
    | Hostunreach
    | Idrm
    | Ilseq
    | Inprogress
    | Intr
    | Inval
    | Io
    | Isconn
    | Isdir
    | Loop
    | Mfile
    | Mlink
    | Msgsize
    | Multihop
    | Nametoolong
    | Netdown
    | Netreset
    | Netunreach
    | Nfile
    | Nobufs
    | Nodev
    | Noent
    | Noexec
    | Nolck
    | Nolink
    | Nomem
    | Nomsg
    | Noprotoopt
    | Nospc
    | Nosys
    | Notconn
    | Notdir
    | Notempty
    | Notrecoverable
    | Notsock
    | Notsup
    | Notty
    | Nxio
    | Overflow
    | Ownerdead
    | Perm
    | Pipe
    | Proto
    | Protonosupport
    | Prototype
    | Range
    | Rofs
    | Spipe
    | Srch
    | Stale
    | Timedout
    | Txtbsy
    | Xdev
    | Notcapable
    deriving stock (Eq, Show, Enum, Bounded)

errnoWord :: Errno -> Word32
errnoWord = fromIntegral . fromEnum

-- | The errno a host IO failure maps to.
errnoOf :: IOException -> Errno
errnoOf e = case ioeGetErrorType e of
    NoSuchThing -> Noent
    AlreadyExists -> Exist
    PermissionDenied -> Acces
    InappropriateType -> Notdir
    UnsatisfiedConstraints -> Notempty
    ResourceBusy -> Busy
    InvalidArgument -> Inval
    _ -> Io

-- *** The call monad and memory access ***

-- | A host call: IO that may fail with an errno. The memory is threaded through explicitly.
type Host = ExceptT Errno IO

hostIO :: IO a -> Host a
hostIO action = ExceptT (either (Left . errnoOf) Right <$> try action)

peekBytes :: MemInst m -> Word32 -> Int -> Host [Word8]
peekBytes mem addr count = except (maybe (Left Fault) Right (readBytes mem (fromIntegral addr) count))

pokeBytes :: MemInst m -> Word32 -> [Word8] -> Host (MemInst m)
pokeBytes mem addr payload = except (maybe (Left Fault) Right (writeBytes mem (fromIntegral addr) payload))

peekWord32 :: MemInst m -> Word32 -> Host Word32
peekWord32 mem addr = word32OfBytes <$> peekBytes mem addr 4

peekWord64 :: MemInst m -> Word32 -> Host Word64
peekWord64 mem addr = word64OfBytes <$> peekBytes mem addr 8

pokeWord32 :: MemInst m -> Word32 -> Word32 -> Host (MemInst m)
pokeWord32 mem addr = pokeBytes mem addr . bytesOfWord32

pokeWord64 :: MemInst m -> Word32 -> Word64 -> Host (MemInst m)
pokeWord64 mem addr = pokeBytes mem addr . bytesOfWord64

-- | A guest path or name: @len@ bytes of UTF-8 at @ptr@.
peekString :: MemInst m -> Word32 -> Word32 -> Host Text
peekString mem ptr len = do
    bytes <- peekBytes mem ptr (fromIntegral len)
    except (either (const (Left Ilseq)) Right (decodeUtf8' (BS.pack bytes)))

-- | The @(ptr, len)@ pairs of an iovec array.
peekIovecs :: MemInst m -> Word32 -> Word32 -> Host [(Word32, Word32)]
peekIovecs mem base count = forM [0 .. count - 1] $ \i -> do
    ptr <- peekWord32 mem (base + i * 8)
    len <- peekWord32 mem (base + i * 8 + 4)
    pure (ptr, len)

-- *** Descriptors and paths ***

lookupFd :: WasiHost -> Word32 -> Host Descriptor
lookupFd host fd = do
    table <- liftIO (readIORef host.descriptors)
    maybe (throwE Badf) pure (Map.lookup fd table)

-- | Install a descriptor at the smallest free number from 3 on.
insertFd :: WasiHost -> Descriptor -> IO Word32
insertFd host descriptor = atomicModifyIORef' host.descriptors $ \table ->
    let fd = head' [n | n <- [3 ..], not (Map.member n table)]
     in (Map.insert fd descriptor table, fd)
  where
    head' (x : _) = x
    head' [] = 3 -- unreachable: the candidate list is infinite

removeFd :: WasiHost -> Word32 -> IO ()
removeFd host fd = atomicModifyIORef' host.descriptors (\table -> (Map.delete fd table, ()))

replaceFd :: WasiHost -> Word32 -> Descriptor -> IO ()
replaceFd host fd descriptor = atomicModifyIORef' host.descriptors (\table -> (Map.insert fd descriptor table, ()))

closeDescriptor :: Descriptor -> IO ()
closeDescriptor (File _ handle _) = hClose handle
closeDescriptor _ = pure ()

directoryOf :: Descriptor -> Host FilePath
directoryOf (Directory path _) = pure path
directoryOf _ = throwE Notdir

{- | A guest path resolved inside a directory. Components are normalised and a path may not
  climb above the directory it is resolved in (the interface's capability rule).
-}
resolvePath :: FilePath -> Text -> Host FilePath
resolvePath base guest = do
    parts <- walk [] [p | p <- T.splitOn "/" guest, not (T.null p), p /= "."]
    pure (foldl (</>) base (map T.unpack parts))
  where
    walk acc [] = pure (reverse acc)
    walk acc (p : rest)
        | p == ".." = case acc of
            [] -> throwE Notcapable
            _ : up -> walk up rest
        | otherwise = walk (p : acc) rest

-- | Resolve a guest path against a directory descriptor.
resolveIn :: WasiHost -> Word32 -> MemInst m -> Word32 -> Word32 -> Host FilePath
resolveIn host fd mem ptr len = do
    base <- lookupFd host fd >>= directoryOf
    guest <- peekString mem ptr len
    resolvePath base guest

-- *** File status ***

data Stat = Stat
    { filetype :: Word8
    , size :: Word64
    , atim :: Word64
    , mtim :: Word64
    , ino :: Word64
    }

fileTypeCharacterDevice, fileTypeDirectory, fileTypeRegular, fileTypeSymlink :: Word8
fileTypeCharacterDevice = 2
fileTypeDirectory = 3
fileTypeRegular = 4
fileTypeSymlink = 7

isSymbolicLink :: FilePath -> Host Bool
isSymbolicLink path = liftIO (fromRight False <$> (try (pathIsSymbolicLink path) :: IO (Either IOException Bool)))

-- | The status of a host path; a symbolic link is described itself unless @follow@.
statPath :: Bool -> FilePath -> Host Stat
statPath follow path = do
    link <- isSymbolicLink path
    if link && not follow
        then do
            target <- hostIO (getSymbolicLinkTarget path)
            pure (Stat fileTypeSymlink (fromIntegral (length target)) 0 0 (inodeOf path))
        else do
            isDir <- hostIO (doesDirectoryExist path)
            isFile <- hostIO (doesFileExist path)
            unless (isDir || isFile) (throwE Noent)
            fileSize <- if isDir then pure 0 else fromIntegral <$> hostIO (getFileSize path)
            modified <- hostIO (getModificationTime path)
            accessed <- hostIO (getAccessTime path)
            pure (Stat (if isDir then fileTypeDirectory else fileTypeRegular) fileSize (nanosOf accessed) (nanosOf modified) (inodeOf path))

nanosOf :: UTCTime -> Word64
nanosOf t = floor (utcTimeToPOSIXSeconds t * 1000000000)

timeOfNanos :: Word64 -> UTCTime
timeOfNanos ns = posixSecondsToUTCTime (fromIntegral ns / 1000000000)

-- | A stable inode number for a path (FNV-1a over its bytes): equal paths, equal inodes.
inodeOf :: FilePath -> Word64
inodeOf = foldl step 14695981039346656037 . BS.unpack . encodeUtf8 . T.pack
  where
    step h b = (h `xor` fromIntegral b) * 1099511628211

-- | The 64-byte @filestat@ layout.
pokeStat :: MemInst m -> Word32 -> Stat -> Host (MemInst m)
pokeStat mem addr st =
    pokeBytes mem addr $
        concat
            [ bytesOfWord64 0 -- dev
            , bytesOfWord64 st.ino
            , st.filetype : replicate 7 0
            , bytesOfWord64 1 -- nlink
            , bytesOfWord64 st.size
            , bytesOfWord64 st.atim
            , bytesOfWord64 st.mtim
            , bytesOfWord64 st.mtim -- ctim
            ]

-- | The 24-byte @fdstat@ layout: file type, flags, and every right.
pokeFdstat :: MemInst m -> Word32 -> Word8 -> Word16 -> Host (MemInst m)
pokeFdstat mem addr filetype flags =
    pokeBytes mem addr (filetype : 0 : take 2 (bytesOfWord32 (fromIntegral flags)) ++ replicate 4 0 ++ bytesOfWord64 allRights ++ bytesOfWord64 allRights)
  where
    allRights = 0x1FFFFFFF

descriptorStat :: Descriptor -> Host Stat
descriptorStat (StandardStream _) = pure (Stat fileTypeCharacterDevice 0 0 0 0)
descriptorStat (Directory path _) = statPath True path
descriptorStat (File path handle _) = do
    hostIO (hFlush handle)
    statPath True path

-- | The @fstflags@ of the set-times calls, checked and turned into the two updates to make.
timesToSet :: Word64 -> Word64 -> Word32 -> Host (Maybe UTCTime, Maybe UTCTime)
timesToSet atim mtim flags = do
    when ((setAtim && atimNow) || (setMtim && mtimNow)) (throwE Inval)
    now <- liftIO (posixSecondsToUTCTime <$> getPOSIXTime)
    let access
            | atimNow = Just now
            | setAtim = Just (timeOfNanos atim)
            | otherwise = Nothing
        modification
            | mtimNow = Just now
            | setMtim = Just (timeOfNanos mtim)
            | otherwise = Nothing
    pure (access, modification)
  where
    setAtim = testBit flags 0
    atimNow = testBit flags 1
    setMtim = testBit flags 2
    mtimNow = testBit flags 3

applyTimes :: FilePath -> (Maybe UTCTime, Maybe UTCTime) -> Host ()
applyTimes path (access, modification) = do
    mapM_ (hostIO . setAccessTime path) access
    mapM_ (hostIO . setModificationTime path) modification

-- *** Performing one call ***

-- | What a host call produced: results to push and the memory as it left it, or an exit.
data WasiOutcome (rs :: [ValType]) (m :: MemShape) where
    WasiReturn :: ValueStack rs -> MemInst m -> WasiOutcome rs m
    WasiExit :: Int -> WasiOutcome rs m

-- | Run an errno-returning call: on failure the memory is as it was.
completing :: MemInst m -> Host (MemInst m) -> IO (WasiOutcome '[ 'I32] m)
completing mem action = do
    result <- runExceptT action
    pure $ case result of
        Left err -> WasiReturn (errnoWord err :# VNil) mem
        Right mem' -> WasiReturn (errnoWord Success :# VNil) mem'

{- | Perform a WASI call. The arguments arrive as a stack of exactly the function's parameter
  shape — last argument on top — so each case has precisely the operands it needs. Every
  memory access goes through the bounds-checked 'MemInst' operations, so a pointer outside
  linear memory yields 'Fault' rather than a crash.
-}
runWasiCall :: WasiHost -> WasiFunc ('FuncType ps rs) -> ValueStack ps -> MemInst m -> IO (WasiOutcome rs m)
runWasiCall host func args mem = case (func, args) of
    (ProcExit, code :# VNil) -> pure (WasiExit (fromIntegral code))
    (ArgsGet, bufPtr :# argvPtr :# VNil) -> completing mem (pokeStrings mem argvPtr bufPtr host.config.arguments)
    (ArgsSizesGet, sizePtr :# countPtr :# VNil) -> completing mem (pokeSizes mem countPtr sizePtr host.config.arguments)
    (EnvironGet, bufPtr :# envPtr :# VNil) -> completing mem (pokeStrings mem envPtr bufPtr environmentStrings)
    (EnvironSizesGet, sizePtr :# countPtr :# VNil) -> completing mem (pokeSizes mem countPtr sizePtr environmentStrings)
    (ClockResGet, outPtr :# clockId :# VNil) -> completing mem $ do
        resolution <- case clockId of
            0 -> pure 1000
            1 -> pure 1
            2 -> pure 1000
            3 -> pure 1000
            _ -> throwE Inval
        pokeWord64 mem outPtr resolution
    (ClockTimeGet, outPtr :# _precision :# clockId :# VNil) -> completing mem (clockNow clockId >>= pokeWord64 mem outPtr)
    (FdAdvise, advice :# _len :# _offset :# fd :# VNil) -> completing mem $ do
        _ <- lookupFd host fd
        when (advice > 5) (throwE Inval)
        pure mem
    (FdAllocate, _len :# _offset :# fd :# VNil) -> completing mem $ do
        _ <- lookupFd host fd
        throwE Notsup
    (FdClose, fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd
        liftIO (closeDescriptor descriptor >> removeFd host fd)
        pure mem
    (FdDatasync, fd :# VNil) -> completing mem (lookupFd host fd >>= flushDescriptor >> pure mem)
    (FdSync, fd :# VNil) -> completing mem (lookupFd host fd >>= flushDescriptor >> pure mem)
    (FdFdstatGet, outPtr :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd
        let (filetype, flags) = case descriptor of
                StandardStream _ -> (fileTypeCharacterDevice, 0)
                Directory _ _ -> (fileTypeDirectory, 0)
                File _ _ appendMode -> (fileTypeRegular, if appendMode then 1 else 0)
        pokeFdstat mem outPtr filetype flags
    (FdFdstatSetFlags, flags :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd
        case descriptor of
            File path handle _ -> liftIO (replaceFd host fd (File path handle (testBit flags 0)))
            _ -> pure ()
        pure mem
    (FdFdstatSetRights, _inheriting :# _base :# fd :# VNil) -> completing mem (lookupFd host fd >> pure mem)
    (FdFilestatGet, outPtr :# fd :# VNil) -> completing mem (lookupFd host fd >>= descriptorStat >>= pokeStat mem outPtr)
    (FdFilestatSetSize, newSize :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd
        case descriptor of
            File _ handle _ -> hostIO (hSetFileSize handle (fromIntegral newSize))
            Directory _ _ -> throwE Isdir
            StandardStream _ -> throwE Badf
        pure mem
    (FdFilestatSetTimes, flags :# mtim :# atim :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd
        times <- timesToSet atim mtim flags
        case descriptor of
            File path _ _ -> applyTimes path times
            Directory path _ -> applyTimes path times
            StandardStream _ -> throwE Badf
        pure mem
    (FdPread, nreadPtr :# offset :# iovsLen :# iovsPtr :# fd :# VNil) -> completing mem $ do
        handle <- lookupFd host fd >>= fileHandle
        iovecs <- peekIovecs mem iovsPtr iovsLen
        position <- hostIO (hTell handle)
        hostIO (hSeek handle AbsoluteSeek (fromIntegral offset))
        (mem', count) <- readInto mem handle iovecs
        hostIO (hSeek handle AbsoluteSeek position)
        pokeWord32 mem' nreadPtr count
    (FdPrestatGet, outPtr :# fd :# VNil) -> completing mem $ do
        name <- lookupFd host fd >>= preopenName
        pokeBytes mem outPtr (0 : replicate 3 0 ++ bytesOfWord32 (fromIntegral (BS.length (encodeUtf8 name))))
    (FdPrestatDirName, pathLen :# pathPtr :# fd :# VNil) -> completing mem $ do
        name <- lookupFd host fd >>= preopenName
        let bytes = BS.unpack (encodeUtf8 name)
        when (length bytes > fromIntegral pathLen) (throwE Nametoolong)
        pokeBytes mem pathPtr bytes
    (FdPwrite, nwrittenPtr :# offset :# iovsLen :# iovsPtr :# fd :# VNil) -> completing mem $ do
        handle <- lookupFd host fd >>= fileHandle
        iovecs <- peekIovecs mem iovsPtr iovsLen
        payload <- gather mem iovecs
        position <- hostIO (hTell handle)
        hostIO (hSeek handle AbsoluteSeek (fromIntegral offset) >> BS.hPut handle (BS.pack payload) >> hFlush handle)
        hostIO (hSeek handle AbsoluteSeek position)
        pokeWord32 mem nwrittenPtr (fromIntegral (length payload))
    (FdRead, nreadPtr :# iovsLen :# iovsPtr :# fd :# VNil) -> completing mem $ do
        handle <- lookupFd host fd >>= readableHandle
        iovecs <- peekIovecs mem iovsPtr iovsLen
        (mem', count) <- readInto mem handle iovecs
        pokeWord32 mem' nreadPtr count
    (FdReaddir, bufusedPtr :# cookie :# bufLen :# bufPtr :# fd :# VNil) -> completing mem $ do
        path <- lookupFd host fd >>= directoryOf
        names <- hostIO (sort <$> listDirectory path)
        entries <- forM (zip [1 ..] ("." : ".." : names)) $ \(next, name) -> do
            st <- statPath False (if name `elem` [".", ".."] then path else path </> name)
            pure (dirent next st.ino st.filetype name)
        let payload = take (fromIntegral bufLen) (concat (drop (fromIntegral cookie) entries))
        mem' <- pokeBytes mem bufPtr payload
        pokeWord32 mem' bufusedPtr (fromIntegral (length payload))
    (FdRenumber, to :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd
        previous <- liftIO (Map.lookup to <$> readIORef host.descriptors)
        liftIO (mapM_ closeDescriptor previous >> replaceFd host to descriptor >> removeFd host fd)
        pure mem
    (FdSeek, newPtr :# whence :# offset :# fd :# VNil) -> completing mem $ do
        handle <- lookupFd host fd >>= seekableHandle
        mode <- case whence of
            0 -> pure AbsoluteSeek
            1 -> pure RelativeSeek
            2 -> pure SeekFromEnd
            _ -> throwE Inval
        hostIO (hSeek handle mode (fromIntegral (toSigned64 offset)))
        position <- hostIO (hTell handle)
        pokeWord64 mem newPtr (fromIntegral position)
    (FdTell, outPtr :# fd :# VNil) -> completing mem $ do
        handle <- lookupFd host fd >>= seekableHandle
        position <- hostIO (hTell handle)
        pokeWord64 mem outPtr (fromIntegral position)
    (FdWrite, nwrittenPtr :# iovsLen :# iovsPtr :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd
        iovecs <- peekIovecs mem iovsPtr iovsLen
        payload <- gather mem iovecs
        case descriptor of
            StandardStream handle -> hostIO (BS.hPut handle (BS.pack payload) >> hFlush handle)
            File _ handle appendMode -> hostIO $ do
                when appendMode (hSeek handle SeekFromEnd 0)
                BS.hPut handle (BS.pack payload)
                hFlush handle
            Directory _ _ -> throwE Isdir
        pokeWord32 mem nwrittenPtr (fromIntegral (length payload))
    (PathCreateDirectory, pathLen :# pathPtr :# fd :# VNil) -> completing mem $ do
        target <- resolveIn host fd mem pathPtr pathLen
        hostIO (createDirectory target)
        pure mem
    (PathFilestatGet, outPtr :# pathLen :# pathPtr :# flags :# fd :# VNil) -> completing mem $ do
        target <- resolveIn host fd mem pathPtr pathLen
        st <- statPath (testBit flags 0) target
        pokeStat mem outPtr st
    (PathFilestatSetTimes, fstFlags :# mtim :# atim :# pathLen :# pathPtr :# _flags :# fd :# VNil) -> completing mem $ do
        target <- resolveIn host fd mem pathPtr pathLen
        times <- timesToSet atim mtim fstFlags
        _ <- statPath True target
        applyTimes target times
        pure mem
    (PathLink, _ :# _ :# _ :# _ :# _ :# _ :# _ :# VNil) -> completing mem (throwE Notsup)
    (PathOpen, outPtr :# fdflags :# _inheriting :# rightsBase :# oflags :# pathLen :# pathPtr :# dirflags :# fd :# VNil) ->
        completing mem $ do
            target <- resolveIn host fd mem pathPtr pathLen
            opened <- openPath host target (testBit dirflags 0) oflags rightsBase fdflags
            pokeWord32 mem outPtr opened
    (PathReadlink, usedPtr :# bufLen :# bufPtr :# pathLen :# pathPtr :# fd :# VNil) -> completing mem $ do
        target <- resolveIn host fd mem pathPtr pathLen
        link <- isSymbolicLink target
        unless link (throwE Inval)
        destination <- hostIO (getSymbolicLinkTarget target)
        let payload = take (fromIntegral bufLen) (BS.unpack (encodeUtf8 (T.pack destination)))
        mem' <- pokeBytes mem bufPtr payload
        pokeWord32 mem' usedPtr (fromIntegral (length payload))
    (PathRemoveDirectory, pathLen :# pathPtr :# fd :# VNil) -> completing mem $ do
        target <- resolveIn host fd mem pathPtr pathLen
        isFile <- hostIO (doesFileExist target)
        when isFile (throwE Notdir)
        hostIO (removeDirectory target)
        pure mem
    (PathRename, newLen :# newPtr :# newFd :# oldLen :# oldPtr :# fd :# VNil) -> completing mem $ do
        source <- resolveIn host fd mem oldPtr oldLen
        destination <- resolveIn host newFd mem newPtr newLen
        hostIO (renamePath source destination)
        pure mem
    (PathSymlink, newLen :# newPtr :# fd :# oldLen :# oldPtr :# VNil) -> completing mem $ do
        contents <- peekString mem oldPtr oldLen
        link <- resolveIn host fd mem newPtr newLen
        hostIO (createFileLink (T.unpack contents) link)
        pure mem
    (PathUnlinkFile, pathLen :# pathPtr :# fd :# VNil) -> completing mem $ do
        target <- resolveIn host fd mem pathPtr pathLen
        isDir <- hostIO (doesDirectoryExist target)
        when isDir (throwE Isdir)
        hostIO (removeFile target)
        pure mem
    (PollOneoff, neventsPtr :# count :# outPtr :# inPtr :# VNil) -> completing mem (pollOneoff host mem inPtr outPtr count neventsPtr)
    (ProcRaise, _signal :# VNil) -> completing mem (throwE Nosys)
    (SchedYield, VNil) -> completing mem (liftIO yield >> pure mem)
    (RandomGet, len :# bufPtr :# VNil) -> completing mem $ do
        bytes <- hostIO (withBinaryFile "/dev/urandom" ReadMode (\h -> BS.hGet h (fromIntegral len)))
        pokeBytes mem bufPtr (BS.unpack bytes)
    (SockAccept, _ :# _ :# _ :# VNil) -> completing mem (throwE Notsup)
    (SockRecv, _ :# _ :# _ :# _ :# _ :# _ :# VNil) -> completing mem (throwE Notsup)
    (SockSend, _ :# _ :# _ :# _ :# _ :# VNil) -> completing mem (throwE Notsup)
    (SockShutdown, _ :# _ :# VNil) -> completing mem (throwE Notsup)
  where
    environmentStrings = [k <> "=" <> v | (k, v) <- host.config.environment]

-- | The argument/environment vectors: pointers into a buffer of NUL-terminated strings.
pokeStrings :: MemInst m -> Word32 -> Word32 -> [Text] -> Host (MemInst m)
pokeStrings mem ptrsPtr bufPtr strings = do
    let encoded = [BS.unpack (encodeUtf8 s) ++ [0] | s <- strings]
        offsets = scanl (+) bufPtr (map (fromIntegral . length) encoded)
    mem' <- foldM (\m (i, off) -> pokeWord32 m (ptrsPtr + 4 * i) off) mem (zip [0 ..] (zipWith const offsets encoded))
    pokeBytes mem' bufPtr (concat encoded)

pokeSizes :: MemInst m -> Word32 -> Word32 -> [Text] -> Host (MemInst m)
pokeSizes mem countPtr sizePtr strings = do
    mem' <- pokeWord32 mem countPtr (fromIntegral (length strings))
    pokeWord32 mem' sizePtr (fromIntegral (sum [BS.length (encodeUtf8 s) + 1 | s <- strings]))

clockNow :: Word32 -> Host Word64
clockNow clockId = case clockId of
    0 -> liftIO (floor . (* 1000000000) <$> getPOSIXTime)
    1 -> liftIO getMonotonicTimeNSec
    2 -> cpu
    3 -> cpu
    _ -> throwE Inval
  where
    cpu = liftIO (fromIntegral . (`div` 1000) <$> getCPUTime)

flushDescriptor :: Descriptor -> Host ()
flushDescriptor (File _ handle _) = hostIO (hFlush handle)
flushDescriptor (StandardStream handle) = hostIO (hFlush handle)
flushDescriptor (Directory _ _) = pure ()

fileHandle :: Descriptor -> Host Handle
fileHandle (File _ handle _) = pure handle
fileHandle (Directory _ _) = throwE Isdir
fileHandle (StandardStream _) = throwE Spipe

readableHandle :: Descriptor -> Host Handle
readableHandle (File _ handle _) = pure handle
readableHandle (StandardStream handle) = pure handle
readableHandle (Directory _ _) = throwE Isdir

seekableHandle :: Descriptor -> Host Handle
seekableHandle (File _ handle _) = pure handle
seekableHandle (Directory _ _) = throwE Badf
seekableHandle (StandardStream _) = throwE Spipe

preopenName :: Descriptor -> Host Text
preopenName (Directory _ (Just name)) = pure name
preopenName _ = throwE Badf

-- | Read into each iovec in turn until one comes back short (end of input).
readInto :: MemInst m -> Handle -> [(Word32, Word32)] -> Host (MemInst m, Word32)
readInto mem handle = go mem 0
  where
    go m total [] = pure (m, total)
    go m total ((ptr, len) : rest) = do
        chunk <- hostIO (BS.hGetSome handle (fromIntegral len))
        m' <- pokeBytes m ptr (BS.unpack chunk)
        let got = fromIntegral (BS.length chunk)
        if got < len then pure (m', total + got) else go m' (total + got) rest

-- | The bytes the iovecs point at, in order.
gather :: MemInst m -> [(Word32, Word32)] -> Host [Word8]
gather mem iovecs = concat <$> forM iovecs (\(ptr, len) -> peekBytes mem ptr (fromIntegral len))

-- | A @dirent@ (24-byte header, then the name) with the cookie of the entry after it.
dirent :: Word64 -> Word64 -> Word8 -> FilePath -> [Word8]
dirent next inode filetype name =
    bytesOfWord64 next ++ bytesOfWord64 inode ++ bytesOfWord32 (fromIntegral (length nameBytes)) ++ filetype : replicate 3 0 ++ nameBytes
  where
    nameBytes = BS.unpack (encodeUtf8 (T.pack name))

{- | @path_open@: the open flags decide creation, exclusivity, truncation and whether the
  target must be a directory; the rights decide the access mode; a symbolic link is followed
  only if asked. A directory becomes a 'Directory' descriptor, a file an unbuffered 'File'.
-}
openPath :: WasiHost -> FilePath -> Bool -> Word32 -> Word64 -> Word32 -> Host Word32
openPath host target follow oflags rightsBase fdflags = do
    link <- isSymbolicLink target
    when (link && not follow) (throwE Loop)
    isDir <- hostIO (doesDirectoryExist target)
    isFile <- hostIO (doesFileExist target)
    when (creat && excl && (isDir || isFile)) (throwE Exist)
    if isDir
        then do
            when (wantsWrite && not mustBeDirectory) (throwE Isdir)
            liftIO (insertFd host (Directory target Nothing))
        else do
            when mustBeDirectory (throwE (if isFile then Notdir else Noent))
            unless (isFile || creat) (throwE Noent)
            handle <- hostIO (openFile target mode)
            hostIO (hSetBuffering handle NoBuffering)
            when trunc (hostIO (hSetFileSize handle 0))
            liftIO (insertFd host (File target handle appendMode))
  where
    creat = testBit oflags 0
    mustBeDirectory = testBit oflags 1
    excl = testBit oflags 2
    trunc = testBit oflags 3
    appendMode = testBit fdflags 0
    wantsRead = testBit rightsBase 1
    wantsWrite = testBit rightsBase 6 || appendMode || trunc
    mode
        | appendMode = AppendMode
        | wantsWrite || creat = ReadWriteMode
        | wantsRead = ReadMode
        | otherwise = ReadMode

{- | @poll_oneoff@. File-descriptor subscriptions are ready at once (a bad descriptor reports
  its error in the event). Clock subscriptions wait for the earliest deadline when nothing
  else is ready; each subscription due by then produces an event.
-}
pollOneoff :: WasiHost -> MemInst m -> Word32 -> Word32 -> Word32 -> Word32 -> Host (MemInst m)
pollOneoff host mem inPtr outPtr count neventsPtr = do
    subscriptions <- forM [0 .. count - 1] (peekSubscription . (inPtr +) . (* 48))
    fdEvents <- fmap concat . forM subscriptions $ \(userdata, kind) -> case kind of
        FdSubscription fd eventType -> do
            known <- liftIO (Map.member fd <$> readIORef host.descriptors)
            pure [event userdata (if known then Success else Badf) eventType]
        ClockSubscription {} -> pure []
    clockEvents <-
        if null fdEvents
            then do
                deadlines <- forM [(u, c) | (u, ClockSubscription c) <- subscriptions] $ \(userdata, clock) -> do
                    remaining <- nanosUntil clock
                    pure (remaining, userdata)
                case deadlines of
                    [] -> pure []
                    _ -> do
                        let earliest = minimum (map fst deadlines)
                        liftIO (threadDelay (fromIntegral (earliest `div` 1000)))
                        pure [event u Success 0 | (r, u) <- deadlines, r == earliest]
            else pure []
    let events = fdEvents ++ clockEvents
    mem' <- pokeBytes mem outPtr (concat events)
    pokeWord32 mem' neventsPtr (fromIntegral (length events))
  where
    peekSubscription addr = do
        userdata <- peekWord64 mem addr
        tag <- peekBytes mem (addr + 8) 1
        case tag of
            [0] -> do
                clockId <- peekWord32 mem (addr + 16)
                timeout <- peekWord64 mem (addr + 24)
                flags <- peekBytes mem (addr + 40) 2
                pure (userdata, ClockSubscription (Clock clockId timeout (take 1 flags == [1])))
            [t] -> do
                fd <- peekWord32 mem (addr + 16)
                pure (userdata, FdSubscription fd t)
            _ -> throwE Inval
    nanosUntil (Clock clockId timeout absolute) = do
        now <- clockNow clockId
        pure (if absolute then (if timeout > now then timeout - now else 0) else timeout)
    event userdata err eventType =
        bytesOfWord64 userdata ++ take 2 (bytesOfWord32 (errnoWord err)) ++ eventType : replicate 5 0 ++ bytesOfWord64 0 ++ replicate 8 0

data Clock = Clock Word32 Word64 Bool

data Subscription = ClockSubscription Clock | FdSubscription Word32 Word8

-- *** The driver ***

-- | How a run under the WASI host ends: normally, with results, or through @proc_exit@.
data Completion
    = Ran SomeModule [Value]
    | Exited Int

{- | Invoke an export and serve every host call it makes until it returns or exits. Each
  request is performed against the module's memory, the memory is stored back, and the
  module resumes where it left off.
-}
runWithWasi :: WasiConfig -> SomeModule -> Text -> [Value] -> IO (Either RunError Completion)
runWithWasi cfg wasmModule name args = do
    host <- newHost cfg
    let serve :: Either RunError Invocation -> IO (Either RunError Completion)
        serve (Left err) = pure (Left err)
        serve (Right (Returned finished results)) = pure (Right (Ran finished results))
        serve (Right (CalledHost (SomeHostRequest shapeS funcs exports rsS (HostRequest wasiFunc callArgs store suspended)))) = do
            outcome <- runWasiCall host wasiFunc callArgs (currentMem store)
            case outcome of
                WasiExit code -> pure (Right (Exited code))
                WasiReturn results mem' ->
                    serve (continueWith shapeS funcs exports rsS (resumeWith (storeMem mem' store) results suspended))
    serve (invokeExport wasmModule name args)
