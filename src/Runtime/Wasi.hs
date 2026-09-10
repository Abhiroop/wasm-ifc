{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

{- | The WASI (WebAssembly System Interface) Preview 1 host, and the IO driver that runs a
  module against it. This is the effectful half of the effect-request boundary: the pure,
  total 'Runtime.Interpreter.step' never performs IO — when a call resolves to an imported
  host function it hands out a 'Runtime.Interpreter.HostRequest' — and 'runWithWasi' is the
  loop that performs each request here and resumes the module. All IO lives in this module.

  The host keeps a descriptor table (the standard streams, the preopened directories, and
  whatever the module opens), each descriptor with the rights and flags the interface
  attaches to it; resolves guest paths inside their preopened directory (a path may not climb
  above it, nor be absolute); speaks the interface's binary layouts; and reaches the file
  system through POSIX calls so that errnos, inodes, links and times are the real ones.
  Sockets are not provided.
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
import Control.Monad (foldM, forM, void, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Except (ExceptT (..), except, runExceptT, throwE)
import Data.Bits (complement, shiftL, testBit, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Internal (createAndTrim)
import Data.ByteString.Unsafe (unsafeUseAsCStringLen)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import Data.List (sort)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8', encodeUtf8)
import Data.Time.Clock.POSIX (POSIXTime, getPOSIXTime)
import Data.Word (Word16, Word32, Word64, Word8)
import Foreign.C.Error qualified as C
import Foreign.Ptr (castPtr)
import GHC.Clock (getMonotonicTimeNSec)
import GHC.IO.Exception (IOErrorType (..), IOException (..))
import System.CPUTime (getCPUTime)
import System.Directory (listDirectory)
import System.FilePath (takeDirectory, (</>))
import System.IO (Handle, IOMode (ReadMode), SeekMode (..), hFlush, stderr, stdin, stdout, withBinaryFile)
import System.IO.Error (ioeGetErrorType)
import System.Posix.Directory (createDirectory, removeDirectory)
import System.Posix.Files (
    FileStatus,
    accessTimeHiRes,
    createLink,
    createSymbolicLink,
    deviceID,
    fileID,
    fileSize,
    getFdStatus,
    getFileStatus,
    getSymbolicLinkStatus,
    isBlockDevice,
    isCharacterDevice,
    isDirectory,
    isRegularFile,
    isSocket,
    isSymbolicLink,
    linkCount,
    modificationTimeHiRes,
    readSymbolicLink,
    removeLink,
    rename,
    setFdSize,
    setFdTimesHiRes,
    setFileTimesHiRes,
    setSymbolicLinkTimesHiRes,
    statusChangeTimeHiRes,
 )
import System.Posix.IO (
    OpenFileFlags (..),
    OpenMode (..),
    closeFd,
    defaultFileFlags,
    fdReadBuf,
    fdSeek,
    fdWriteBuf,
    openFd,
 )
import System.Posix.Types (Fd)
import System.Posix.Unistd (fileSynchronise)

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

-- | An open descriptor: what it is, and the rights and flags the interface attaches to it.
data Descriptor = Descriptor
    { resource :: Resource
    , rightsBase :: Word64
    , rightsInheriting :: Word64
    , fdflags :: Word16
    }

data Resource
    = StandardStream Handle
    | -- | a directory on the host, with its guest name if it is a preopen
      Directory FilePath (Maybe Text)
    | -- | an open regular file: host path and POSIX descriptor
      RegularFile FilePath Fd

data WasiHost = WasiHost
    { config :: WasiConfig
    , descriptors :: IORef (Map Word32 Descriptor)
    }

-- | A host with the standard streams at 0–2 and the preopens from 3 on.
newHost :: WasiConfig -> IO WasiHost
newHost cfg = do
    let stream h = Descriptor (StandardStream h) streamRights 0 0
        streams = [(0, stream stdin), (1, stream stdout), (2, stream stderr)]
        dirs = [(fd, Descriptor (Directory p.hostPath (Just p.guestPath)) directoryRights (directoryRights .|. fileRights) 0) | (fd, p) <- zip [3 ..] cfg.preopens]
    table <- newIORef (Map.fromList (streams ++ dirs))
    pure (WasiHost cfg table)

-- *** Rights ***

{- The interface's rights, by bit. A file and a directory each get the set that applies to
  them (as wasmtime grants), and @path_open@ narrows a new descriptor's rights to what was
  asked for; @fd_fdstat_set_rights@ can only narrow further.
-}
rightFdRead, rightFdSeek, rightFdWrite, rightFdTell :: Int
rightFdRead = 1
rightFdSeek = 2
rightFdTell = 5
rightFdWrite = 6

rightsOf :: [Int] -> Word64
rightsOf = foldr (\bit acc -> acc .|. (1 `shiftL` bit)) 0

fileRights, directoryRights, streamRights :: Word64
fileRights = rightsOf [0, rightFdRead, rightFdSeek, 3, 4, rightFdTell, rightFdWrite, 7, 8, 21, 22, 23, 27]
directoryRights = rightsOf [3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27]
streamRights = rightsOf [0, rightFdRead, 3, 4, rightFdWrite, 7, 21, 27]

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

-- | The errno a host IO failure maps to: the POSIX errno when the call carried one.
errnoOf :: IOException -> Errno
errnoOf e = case e.ioe_errno of
    Just code -> fromMaybe Io (lookup (C.Errno code) posixErrnos)
    Nothing -> case ioeGetErrorType e of
        NoSuchThing -> Noent
        AlreadyExists -> Exist
        PermissionDenied -> Acces
        InappropriateType -> Notdir
        UnsatisfiedConstraints -> Notempty
        ResourceBusy -> Busy
        InvalidArgument -> Inval
        _ -> Io

posixErrnos :: [(C.Errno, Errno)]
posixErrnos =
    [ (C.eNOENT, Noent)
    , (C.eEXIST, Exist)
    , (C.eNOTDIR, Notdir)
    , (C.eISDIR, Isdir)
    , (C.eNOTEMPTY, Notempty)
    , (C.eACCES, Acces)
    , (C.ePERM, Perm)
    , (C.eBADF, Badf)
    , (C.eINVAL, Inval)
    , (C.eLOOP, Loop)
    , (C.eNAMETOOLONG, Nametoolong)
    , (C.eXDEV, Xdev)
    , (C.eBUSY, Busy)
    , (C.eMLINK, Mlink)
    , (C.eNOSPC, Nospc)
    , (C.eROFS, Rofs)
    , (C.eSPIPE, Spipe)
    , (C.eIO, Io)
    , (C.eNOTSUP, Notsup)
    , (C.eOPNOTSUPP, Notsup)
    , (C.eTXTBSY, Txtbsy)
    , (C.eFBIG, Fbig)
    , (C.eMFILE, Mfile)
    , (C.eNFILE, Nfile)
    , (C.eNXIO, Nxio)
    , (C.eAGAIN, Again)
    , (C.eINTR, Intr)
    , (C.ePIPE, Pipe)
    , (C.eDQUOT, Dquot)
    , (C.eNOTSOCK, Notsock)
    , (C.eNOSYS, Nosys)
    , (C.eNODEV, Nodev)
    ]

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

-- *** Descriptors ***

lookupFd :: WasiHost -> Word32 -> Host Descriptor
lookupFd host fd = do
    table <- liftIO (readIORef host.descriptors)
    maybe (throwE Badf) pure (Map.lookup fd table)

-- | Install a descriptor at the smallest free number from 3 on.
insertFd :: WasiHost -> Descriptor -> IO Word32
insertFd host descriptor = atomicModifyIORef' host.descriptors $ \table ->
    let fd = case [n | n <- [3 ..], not (Map.member n table)] of
            n : _ -> n
            [] -> 3 -- unreachable: the candidates are unbounded
     in (Map.insert fd descriptor table, fd)

removeFd :: WasiHost -> Word32 -> IO ()
removeFd host fd = atomicModifyIORef' host.descriptors (\table -> (Map.delete fd table, ()))

replaceFd :: WasiHost -> Word32 -> Descriptor -> IO ()
replaceFd host fd descriptor = atomicModifyIORef' host.descriptors (\table -> (Map.insert fd descriptor table, ()))

closeResource :: Resource -> IO ()
closeResource (RegularFile _ fd) = closeFd fd
closeResource _ = pure ()

-- | The operation needs this right on the descriptor (the interface's capability check).
requireRight :: Int -> Descriptor -> Host Descriptor
requireRight bit descriptor
    | testBit descriptor.rightsBase bit = pure descriptor
    | otherwise = throwE Notcapable

directoryOf :: Descriptor -> Host FilePath
directoryOf descriptor = case descriptor.resource of
    Directory path _ -> pure path
    _ -> throwE Notdir

fileOf :: Descriptor -> Host Fd
fileOf descriptor = case descriptor.resource of
    RegularFile _ fd -> pure fd
    Directory _ _ -> throwE Isdir
    StandardStream _ -> throwE Spipe

-- *** Paths ***

-- | A guest path resolved on the host; a trailing slash means it must name a directory.
data GuestPath = GuestPath
    { host :: FilePath
    , mustBeDirectory :: Bool
    }

{- | A guest path resolved inside a directory. Components are normalised; a path may not climb
  above the directory it is resolved in, nor be absolute (the interface's capability rule);
  and it may not contain a NUL.
-}
resolvePath :: FilePath -> Text -> Host GuestPath
resolvePath base guest
    | T.any (== '\0') guest = throwE Ilseq
    | "/" `T.isPrefixOf` guest = throwE Notcapable
    | T.null guest = throwE Noent
    | otherwise = do
        parts <- walk [] [p | p <- T.splitOn "/" guest, not (T.null p), p /= "."]
        pure (GuestPath (foldl (</>) base (map T.unpack parts)) ("/" `T.isSuffixOf` guest))
  where
    walk acc [] = pure (reverse acc)
    walk acc (p : rest)
        | p == ".." = case acc of
            [] -> throwE Notcapable
            _ : up -> walk up rest
        | otherwise = walk (p : acc) rest

-- | Resolve a guest path against a directory descriptor that must hold the given right.
resolveIn :: WasiHost -> Word32 -> Int -> MemInst m -> Word32 -> Word32 -> Host GuestPath
resolveIn host fd right mem ptr len = do
    base <- lookupFd host fd >>= requireRight right >>= directoryOf
    guest <- peekString mem ptr len
    resolvePath base guest

-- *** File status ***

-- | The interface's file types.
fileTypeOf :: FileStatus -> Word8
fileTypeOf st
    | isBlockDevice st = 1
    | isCharacterDevice st = 2
    | isDirectory st = 3
    | isRegularFile st = 4
    | isSocket st = 6
    | isSymbolicLink st = 7
    | otherwise = 0

nanosOf :: POSIXTime -> Word64
nanosOf t = floor (t * 1000000000)

timeOfNanos :: Word64 -> POSIXTime
timeOfNanos ns = fromIntegral ns / 1000000000

-- | The status of a path (following symbolic links or not), as an errno on failure.
statPath :: Bool -> FilePath -> Host FileStatus
statPath follow path = hostIO (if follow then getFileStatus path else getSymbolicLinkStatus path)

-- | The status of a path if it exists at all (a symbolic link counts, dangling or not).
statIfExists :: Bool -> FilePath -> Host (Maybe FileStatus)
statIfExists follow path = do
    result <- liftIO (try (if follow then getFileStatus path else getSymbolicLinkStatus path))
    case result of
        Right st -> pure (Just st)
        Left e | errnoOf e `elem` [Noent, Notdir] -> pure Nothing
        Left e -> throwE (errnoOf e)

-- | The 64-byte @filestat@ layout.
pokeStat :: MemInst m -> Word32 -> FileStatus -> Host (MemInst m)
pokeStat mem addr st =
    pokeBytes mem addr $
        concat
            [ bytesOfWord64 (fromIntegral (deviceID st))
            , bytesOfWord64 (fromIntegral (fileID st))
            , fileTypeOf st : replicate 7 0
            , bytesOfWord64 (fromIntegral (linkCount st))
            , bytesOfWord64 (fromIntegral (fileSize st))
            , bytesOfWord64 (nanosOf (accessTimeHiRes st))
            , bytesOfWord64 (nanosOf (modificationTimeHiRes st))
            , bytesOfWord64 (nanosOf (statusChangeTimeHiRes st))
            ]

-- | The 24-byte @fdstat@ layout.
pokeFdstat :: MemInst m -> Word32 -> Word8 -> Descriptor -> Host (MemInst m)
pokeFdstat mem addr filetype descriptor =
    pokeBytes mem addr $
        concat
            [ [filetype, 0]
            , take 2 (bytesOfWord32 (fromIntegral descriptor.fdflags))
            , replicate 4 0
            , bytesOfWord64 descriptor.rightsBase
            , bytesOfWord64 descriptor.rightsInheriting
            ]

descriptorStatus :: Descriptor -> Host FileStatus
descriptorStatus descriptor = case descriptor.resource of
    StandardStream _ -> hostIO (getFdStatus 1)
    Directory path _ -> statPath True path
    RegularFile _ fd -> hostIO (getFdStatus fd)

{- | The @fstflags@ of the set-times calls, checked and turned into the access and
modification times to set (each 'Nothing' when it is to be left alone).
-}
timesToSet :: Word64 -> Word64 -> Word32 -> Host (Maybe POSIXTime, Maybe POSIXTime)
timesToSet atim mtim flags = do
    when ((setAtim && atimNow) || (setMtim && mtimNow)) (throwE Inval)
    now <- liftIO getPOSIXTime
    let pick set useNow value
            | useNow = Just now
            | set = Just (timeOfNanos value)
            | otherwise = Nothing
    pure (pick setAtim atimNow atim, pick setMtim mtimNow mtim)
  where
    setAtim = testBit flags 0
    atimNow = testBit flags 1
    setMtim = testBit flags 2
    mtimNow = testBit flags 3

-- | Apply a times update to a path (following links or not), keeping the other time.
applyTimes :: Bool -> FilePath -> (Maybe POSIXTime, Maybe POSIXTime) -> Host ()
applyTimes follow path (access, modification) = do
    st <- statPath follow path
    let atime = fromMaybe (accessTimeHiRes st) access
        mtime = fromMaybe (modificationTimeHiRes st) modification
    hostIO ((if follow then setFileTimesHiRes else setSymbolicLinkTimesHiRes) path atime mtime)

-- *** Reading and writing ***

readSome :: Resource -> Int -> Host ByteString
readSome (StandardStream handle) count = hostIO (BS.hGetSome handle count)
readSome (RegularFile _ fd) count = hostIO (createAndTrim count (\ptr -> fromIntegral <$> fdReadBuf fd ptr (fromIntegral count)))
readSome (Directory _ _) _ = throwE Isdir

writeAll :: Descriptor -> ByteString -> Host Int
writeAll descriptor payload = case descriptor.resource of
    StandardStream handle -> hostIO (BS.hPut handle payload >> hFlush handle >> pure (BS.length payload))
    RegularFile _ fd -> do
        when (testBit descriptor.fdflags 0) (void (hostIO (fdSeek fd SeekFromEnd 0)))
        hostIO (fdWriteAll fd payload)
    Directory _ _ -> throwE Isdir

-- | Write the whole buffer to a POSIX descriptor (retrying short writes).
fdWriteAll :: Fd -> ByteString -> IO Int
fdWriteAll fd payload
    | BS.null payload = pure 0
    | otherwise = do
        written <- unsafeUseAsCStringLen payload (\(ptr, len) -> fromIntegral <$> fdWriteBuf fd (castPtr ptr) (fromIntegral len))
        (written +) <$> fdWriteAll fd (BS.drop written payload)

-- | Read into each iovec in turn until one comes back short (end of input).
readInto :: MemInst m -> Resource -> [(Word32, Word32)] -> Host (MemInst m, Word32)
readInto mem resource = go mem 0
  where
    go m total [] = pure (m, total)
    go m total ((ptr, len) : rest) = do
        chunk <- readSome resource (fromIntegral len)
        m' <- pokeBytes m ptr (BS.unpack chunk)
        let got = fromIntegral (BS.length chunk)
        if got < len then pure (m', total + got) else go m' (total + got) rest

-- | The bytes the iovecs point at, in order.
gather :: MemInst m -> [(Word32, Word32)] -> Host ByteString
gather mem iovecs = BS.pack . concat <$> forM iovecs (\(ptr, len) -> peekBytes mem ptr (fromIntegral len))

-- | Run an action at a file offset, then put the position back.
atOffset :: Fd -> Word64 -> Host a -> Host a
atOffset fd offset action = do
    position <- hostIO (fdSeek fd RelativeSeek 0)
    _ <- hostIO (fdSeek fd AbsoluteSeek (fromIntegral offset))
    result <- action
    _ <- hostIO (fdSeek fd AbsoluteSeek position)
    pure result

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
        descriptor <- lookupFd host fd >>= requireRight 7
        _ <- fileOf descriptor
        when (advice > 5) (throwE Inval)
        pure mem
    (FdAllocate, _len :# _offset :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd >>= requireRight 8
        _ <- fileOf descriptor
        throwE Notsup
    (FdClose, fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd
        liftIO (closeResource descriptor.resource >> removeFd host fd)
        pure mem
    (FdDatasync, fd :# VNil) -> completing mem (lookupFd host fd >>= requireRight 0 >>= syncDescriptor >> pure mem)
    (FdSync, fd :# VNil) -> completing mem (lookupFd host fd >>= requireRight 4 >>= syncDescriptor >> pure mem)
    (FdFdstatGet, outPtr :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd
        let filetype = case descriptor.resource of
                StandardStream _ -> 2
                Directory _ _ -> 3
                RegularFile _ _ -> 4
        pokeFdstat mem outPtr filetype descriptor
    (FdFdstatSetFlags, flags :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd >>= requireRight 3
        liftIO (replaceFd host fd descriptor {fdflags = fromIntegral flags})
        pure mem
    (FdFdstatSetRights, inheriting :# base :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd
        when (base .&. complement descriptor.rightsBase /= 0 || inheriting .&. complement descriptor.rightsInheriting /= 0) (throwE Notcapable)
        liftIO (replaceFd host fd descriptor {rightsBase = base, rightsInheriting = inheriting})
        pure mem
    (FdFilestatGet, outPtr :# fd :# VNil) -> completing mem (lookupFd host fd >>= requireRight 21 >>= descriptorStatus >>= pokeStat mem outPtr)
    (FdFilestatSetSize, newSize :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd >>= requireRight 22
        fd' <- fileOf descriptor
        hostIO (setFdSize fd' (fromIntegral newSize))
        pure mem
    (FdFilestatSetTimes, flags :# mtim :# atim :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd >>= requireRight 23
        (access, modification) <- timesToSet atim mtim flags
        case descriptor.resource of
            RegularFile _ fd' -> do
                st <- hostIO (getFdStatus fd')
                hostIO (setFdTimesHiRes fd' (fromMaybe (accessTimeHiRes st) access) (fromMaybe (modificationTimeHiRes st) modification))
            Directory path _ -> applyTimes True path (access, modification)
            StandardStream _ -> throwE Badf
        pure mem
    (FdPread, nreadPtr :# offset :# iovsLen :# iovsPtr :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd >>= requireRight rightFdRead >>= requireRight rightFdSeek
        fd' <- fileOf descriptor
        iovecs <- peekIovecs mem iovsPtr iovsLen
        (mem', count) <- atOffset fd' offset (readInto mem descriptor.resource iovecs)
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
        descriptor <- lookupFd host fd >>= requireRight rightFdWrite >>= requireRight rightFdSeek
        fd' <- fileOf descriptor
        iovecs <- peekIovecs mem iovsPtr iovsLen
        payload <- gather mem iovecs
        -- The position is left where it was. With the append flag the offset is ignored and
        -- the data goes to the end, as Linux does.
        written <- atOffset fd' offset (writeAll descriptor payload)
        pokeWord32 mem nwrittenPtr (fromIntegral written)
    (FdRead, nreadPtr :# iovsLen :# iovsPtr :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd >>= requireRight rightFdRead
        iovecs <- peekIovecs mem iovsPtr iovsLen
        (mem', count) <- readInto mem descriptor.resource iovecs
        pokeWord32 mem' nreadPtr count
    (FdReaddir, bufusedPtr :# cookie :# bufLen :# bufPtr :# fd :# VNil) -> completing mem $ do
        path <- lookupFd host fd >>= requireRight 14 >>= directoryOf
        names <- hostIO (sort <$> listDirectory path)
        entries <- forM (zip [1 ..] ("." : ".." : names)) $ \(next, name) -> do
            st <- statPath False (path </> name)
            pure (dirent next (fromIntegral (fileID st)) (fileTypeOf st) name)
        let payload = take (fromIntegral bufLen) (concat (drop (fromIntegral cookie) entries))
        mem' <- pokeBytes mem bufPtr payload
        pokeWord32 mem' bufusedPtr (fromIntegral (length payload))
    (FdRenumber, to :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd
        previous <- lookupFd host to
        when (fd /= to) $ liftIO (closeResource previous.resource >> replaceFd host to descriptor >> removeFd host fd)
        pure mem
    (FdSeek, newPtr :# whence :# offset :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd >>= requireRight rightFdSeek
        fd' <- seekableFile descriptor
        mode <- case whence of
            0 -> pure AbsoluteSeek
            1 -> pure RelativeSeek
            2 -> pure SeekFromEnd
            _ -> throwE Inval
        position <- hostIO (fdSeek fd' mode (fromIntegral (toSigned64 offset)))
        pokeWord64 mem newPtr (fromIntegral position)
    (FdTell, outPtr :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd >>= requireRight rightFdTell
        fd' <- seekableFile descriptor
        position <- hostIO (fdSeek fd' RelativeSeek 0)
        pokeWord64 mem outPtr (fromIntegral position)
    (FdWrite, nwrittenPtr :# iovsLen :# iovsPtr :# fd :# VNil) -> completing mem $ do
        descriptor <- lookupFd host fd >>= requireRight rightFdWrite
        iovecs <- peekIovecs mem iovsPtr iovsLen
        payload <- gather mem iovecs
        written <- writeAll descriptor payload
        pokeWord32 mem nwrittenPtr (fromIntegral written)
    (PathCreateDirectory, pathLen :# pathPtr :# fd :# VNil) -> completing mem $ do
        target <- resolveIn host fd 9 mem pathPtr pathLen
        hostIO (createDirectory target.host 0o755)
        pure mem
    (PathFilestatGet, outPtr :# pathLen :# pathPtr :# flags :# fd :# VNil) -> completing mem $ do
        target <- resolveIn host fd 18 mem pathPtr pathLen
        st <- statPath (testBit flags 0) target.host
        when (target.mustBeDirectory && not (isDirectory st)) (throwE Notdir)
        pokeStat mem outPtr st
    (PathFilestatSetTimes, fstFlags :# mtim :# atim :# pathLen :# pathPtr :# flags :# fd :# VNil) -> completing mem $ do
        target <- resolveIn host fd 20 mem pathPtr pathLen
        times <- timesToSet atim mtim fstFlags
        applyTimes (testBit flags 0) target.host times
        pure mem
    (PathLink, newLen :# newPtr :# newFd :# oldLen :# oldPtr :# oldFlags :# oldFd :# VNil) -> completing mem $ do
        source <- resolveIn host oldFd 11 mem oldPtr oldLen
        link <- resolveIn host newFd 12 mem newPtr newLen
        st <- statPath False source.host
        when (isDirectory st) (throwE Perm)
        when (source.mustBeDirectory || link.mustBeDirectory) (throwE Noent)
        origin <-
            if isSymbolicLink st && testBit oldFlags 0
                then hostIO (relativeTo (takeDirectory source.host) <$> readSymbolicLink source.host)
                else pure source.host
        hostIO (createLink origin link.host)
        pure mem
    (PathOpen, outPtr :# fdflags :# inheriting :# rightsBase :# oflags :# pathLen :# pathPtr :# dirflags :# fd :# VNil) ->
        completing mem $ do
            parent <- lookupFd host fd >>= requireRight 13
            when (testBit oflags 0) (void (requireRight 10 parent))
            when (testBit oflags 3) (void (requireRight 19 parent))
            base <- directoryOf parent
            guest <- peekString mem pathPtr pathLen
            target <- resolvePath base guest
            opened <- openPath host parent target (testBit dirflags 0) oflags rightsBase inheriting (fromIntegral fdflags)
            pokeWord32 mem outPtr opened
    (PathReadlink, usedPtr :# bufLen :# bufPtr :# pathLen :# pathPtr :# fd :# VNil) -> completing mem $ do
        target <- resolveIn host fd 15 mem pathPtr pathLen
        destination <- hostIO (readSymbolicLink target.host)
        let payload = take (fromIntegral bufLen) (BS.unpack (encodeUtf8 (T.pack destination)))
        mem' <- pokeBytes mem bufPtr payload
        pokeWord32 mem' usedPtr (fromIntegral (length payload))
    (PathRemoveDirectory, pathLen :# pathPtr :# fd :# VNil) -> completing mem $ do
        target <- resolveIn host fd 25 mem pathPtr pathLen
        hostIO (removeDirectory target.host)
        pure mem
    (PathRename, newLen :# newPtr :# newFd :# oldLen :# oldPtr :# fd :# VNil) -> completing mem $ do
        source <- resolveIn host fd 16 mem oldPtr oldLen
        destination <- resolveIn host newFd 17 mem newPtr newLen
        hostIO (rename source.host destination.host)
        pure mem
    (PathSymlink, newLen :# newPtr :# fd :# oldLen :# oldPtr :# VNil) -> completing mem $ do
        contents <- peekString mem oldPtr oldLen
        link <- resolveIn host fd 24 mem newPtr newLen
        when (link.mustBeDirectory || T.null contents) (throwE Noent)
        when ("/" `T.isPrefixOf` contents) (throwE Perm)
        hostIO (createSymbolicLink (T.unpack contents) link.host)
        pure mem
    (PathUnlinkFile, pathLen :# pathPtr :# fd :# VNil) -> completing mem $ do
        target <- resolveIn host fd 26 mem pathPtr pathLen
        st <- statPath False target.host
        when (isDirectory st) (throwE Isdir)
        when target.mustBeDirectory (throwE Notdir)
        hostIO (removeLink target.host)
        pure mem
    (PollOneoff, neventsPtr :# count :# outPtr :# inPtr :# VNil) -> completing mem (pollOneoff host mem inPtr outPtr count neventsPtr)
    (ProcRaise, _signal :# VNil) -> completing mem (throwE Nosys)
    (SchedYield, VNil) -> completing mem (liftIO yield >> pure mem)
    (RandomGet, len :# bufPtr :# VNil) -> completing mem $ do
        bytes <- hostIO (withBinaryFile "/dev/urandom" ReadMode (\h -> BS.hGet h (fromIntegral len)))
        pokeBytes mem bufPtr (BS.unpack bytes)
    (SockAccept, _ :# _ :# fd :# VNil) -> completing mem (notASocket fd)
    (SockRecv, _ :# _ :# _ :# _ :# _ :# fd :# VNil) -> completing mem (notASocket fd)
    (SockSend, _ :# _ :# _ :# _ :# fd :# VNil) -> completing mem (notASocket fd)
    (SockShutdown, _ :# fd :# VNil) -> completing mem (notASocket fd)
  where
    environmentStrings = [k <> "=" <> v | (k, v) <- host.config.environment]
    -- There are no sockets: an unknown descriptor is bad, a known one is not a socket.
    notASocket fd = lookupFd host fd >> throwE Notsock

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
    0 -> liftIO (nanosOf <$> getPOSIXTime)
    1 -> liftIO getMonotonicTimeNSec
    2 -> cpu
    3 -> cpu
    _ -> throwE Inval
  where
    cpu = liftIO (fromIntegral . (`div` 1000) <$> getCPUTime)

syncDescriptor :: Descriptor -> Host ()
syncDescriptor descriptor = case descriptor.resource of
    RegularFile _ fd -> hostIO (fileSynchronise fd)
    StandardStream handle -> hostIO (hFlush handle)
    Directory _ _ -> pure ()

seekableFile :: Descriptor -> Host Fd
seekableFile descriptor = case descriptor.resource of
    RegularFile _ fd -> pure fd
    Directory _ _ -> throwE Badf
    StandardStream _ -> throwE Spipe

preopenName :: Descriptor -> Host Text
preopenName descriptor = case descriptor.resource of
    Directory _ (Just name) -> pure name
    _ -> throwE Badf

-- | A relative link target, read from a link in @dir@, as a host path.
relativeTo :: FilePath -> FilePath -> FilePath
relativeTo dir target
    | "/" `T.isPrefixOf` T.pack target = target
    | otherwise = dir </> target

-- | A @dirent@ (24-byte header, then the name) with the cookie of the entry after it.
dirent :: Word64 -> Word64 -> Word8 -> FilePath -> [Word8]
dirent next inode filetype name =
    bytesOfWord64 next ++ bytesOfWord64 inode ++ bytesOfWord32 (fromIntegral (length nameBytes)) ++ filetype : replicate 3 0 ++ nameBytes
  where
    nameBytes = BS.unpack (encodeUtf8 (T.pack name))

{- | @path_open@. The open flags decide creation, exclusivity, truncation and whether the target
  must be a directory; the requested rights (narrowed to the parent's inheritable ones and to
  what applies to a file or a directory) decide the access mode and become the new
  descriptor's rights; a symbolic link in the last component is followed only if asked.
-}
openPath :: WasiHost -> Descriptor -> GuestPath -> Bool -> Word32 -> Word64 -> Word64 -> Word16 -> Host Word32
openPath host parent target follow oflags requestedBase requestedInheriting flags = do
    let base = requestedBase .&. parent.rightsInheriting
        inheriting = requestedInheriting .&. parent.rightsInheriting
        wantsWrite = testBit base rightFdWrite || trunc || append
    unlinked <- statIfExists False target.host
    when (maybe False isSymbolicLink unlinked && not follow) (throwE Loop)
    existing <- statIfExists True target.host
    when (creat && excl && isJust existing) (throwE Exist)
    case existing of
        Just st | isDirectory st -> do
            when wantsWrite (throwE Isdir)
            liftIO (insertFd host (Descriptor (Directory target.host Nothing) (base .&. directoryRights) inheriting flags))
        Just _ | mustBeDirectory -> throwE Notdir
        Nothing | mustBeDirectory -> throwE Noent
        Nothing | not creat -> throwE Noent
        _ -> do
            let mode
                    | testBit base rightFdRead && wantsWrite = ReadWrite
                    | wantsWrite = WriteOnly
                    | otherwise = ReadOnly
                openFlags =
                    defaultFileFlags
                        { creat = if creat then Just 0o644 else Nothing
                        , exclusive = excl
                        , trunc = trunc
                        , nofollow = not follow
                        , sync = testBit flags 4
                        }
            fd <- hostIO (openFd target.host mode openFlags)
            liftIO (insertFd host (Descriptor (RegularFile target.host fd) (base .&. fileRights) inheriting flags))
  where
    creat = testBit oflags 0
    mustBeDirectory = testBit oflags 1 || target.mustBeDirectory
    excl = testBit oflags 2
    trunc = testBit oflags 3
    append = testBit flags 0

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
                flagBytes <- peekBytes mem (addr + 40) 2
                pure (userdata, ClockSubscription (Clock clockId timeout (take 1 flagBytes == [1])))
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
