{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

{- | The host functions a module may import: the complete WASI Preview 1 interface
  (@wasi_snapshot_preview1@), each at the exact function type the interface fixes. This is
  the pure vocabulary; performing a call is "Runtime.Wasi"'s job.

  A 'WasiFunc' is indexed by its type, so a host function can only ever be installed in a
  module at the type it really has, and the interpreter receives its arguments as a stack of
  exactly that shape. The parameter lists are written in stack order — the last parameter
  first — like every type in a shape (see "Validation.Shape"); the Haddock on each constructor
  gives the declared order.
-}
module Runtime.Host (
    WasiFunc (..),
    SomeWasiFunc (..),
    wasiModuleName,
    resolveWasiImport,
    wasiFuncType,
    wasiFuncName,
) where

import Data.Singletons (Sing, sing)
import Data.Text (Text)

import Syntax.Types (FuncType (..), ValType (..))

-- | The import module name WASI functions are resolved against.
wasiModuleName :: Text
wasiModuleName = "wasi_snapshot_preview1"

{- TODO(ifc P1): each WASI function needs a labelled signature, the most concrete part of the
   policy, and this is our extension of SecWasm (host imports are a stated non-goal there).
   Sources: @fd_read@ and @fd_pread@ results take the descriptor's label (a secret file yields
   secret bytes, written into memory /with that label/ per byte, which the hybrid memory model
   supports directly); @args_get@, @environ_get@, @clock_time_get@ are public; @random_get@ is
   public entropy unless it seeds a key. Sinks: @fd_write@ and @fd_pwrite@ need the labels of
   the bytes they read from memory ⊑ the descriptor's label and the pc ⊑ it (a write under a
   secret pc leaks by happening); @proc_exit@'s code and @path_open@'s path are public outputs.
   The descriptor is a run-time value, so its label is dynamic: a label per preopen in
   'Runtime.Wasi.WasiConfig', inherited through @path_open@, checked by the driver at the
   boundary against the per-byte labels of the buffer, the same kind of dynamic check as
   SecWasm's load. Statically each host function then only needs a pc bound and labels for its
   scalar arguments and results, encoded as a second index here or as a function from the
   constructor to a labelled type; the check happens at 'Runtime.Interpreter.HostRequest'. -}
data WasiFunc (ft :: FuncType) where
    -- | @args_get(argv, argv_buf)@
    ArgsGet :: WasiFunc ('FuncType '[ 'I32, 'I32] '[ 'I32])
    -- | @args_sizes_get(argc, argv_buf_size)@
    ArgsSizesGet :: WasiFunc ('FuncType '[ 'I32, 'I32] '[ 'I32])
    -- | @environ_get(environ, environ_buf)@
    EnvironGet :: WasiFunc ('FuncType '[ 'I32, 'I32] '[ 'I32])
    -- | @environ_sizes_get(count, buf_size)@
    EnvironSizesGet :: WasiFunc ('FuncType '[ 'I32, 'I32] '[ 'I32])
    -- | @clock_res_get(id, resolution)@
    ClockResGet :: WasiFunc ('FuncType '[ 'I32, 'I32] '[ 'I32])
    -- | @clock_time_get(id, precision, time)@
    ClockTimeGet :: WasiFunc ('FuncType '[ 'I32, 'I64, 'I32] '[ 'I32])
    -- | @fd_advise(fd, offset, len, advice)@
    FdAdvise :: WasiFunc ('FuncType '[ 'I32, 'I64, 'I64, 'I32] '[ 'I32])
    -- | @fd_allocate(fd, offset, len)@
    FdAllocate :: WasiFunc ('FuncType '[ 'I64, 'I64, 'I32] '[ 'I32])
    -- | @fd_close(fd)@
    FdClose :: WasiFunc ('FuncType '[ 'I32] '[ 'I32])
    -- | @fd_datasync(fd)@
    FdDatasync :: WasiFunc ('FuncType '[ 'I32] '[ 'I32])
    -- | @fd_fdstat_get(fd, stat)@
    FdFdstatGet :: WasiFunc ('FuncType '[ 'I32, 'I32] '[ 'I32])
    -- | @fd_fdstat_set_flags(fd, flags)@
    FdFdstatSetFlags :: WasiFunc ('FuncType '[ 'I32, 'I32] '[ 'I32])
    -- | @fd_fdstat_set_rights(fd, base, inheriting)@
    FdFdstatSetRights :: WasiFunc ('FuncType '[ 'I64, 'I64, 'I32] '[ 'I32])
    -- | @fd_filestat_get(fd, stat)@
    FdFilestatGet :: WasiFunc ('FuncType '[ 'I32, 'I32] '[ 'I32])
    -- | @fd_filestat_set_size(fd, size)@
    FdFilestatSetSize :: WasiFunc ('FuncType '[ 'I64, 'I32] '[ 'I32])
    -- | @fd_filestat_set_times(fd, atim, mtim, flags)@
    FdFilestatSetTimes :: WasiFunc ('FuncType '[ 'I32, 'I64, 'I64, 'I32] '[ 'I32])
    -- | @fd_pread(fd, iovs, iovs_len, offset, nread)@
    FdPread :: WasiFunc ('FuncType '[ 'I32, 'I64, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @fd_prestat_get(fd, prestat)@
    FdPrestatGet :: WasiFunc ('FuncType '[ 'I32, 'I32] '[ 'I32])
    -- | @fd_prestat_dir_name(fd, path, path_len)@
    FdPrestatDirName :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32] '[ 'I32])
    -- | @fd_pwrite(fd, iovs, iovs_len, offset, nwritten)@
    FdPwrite :: WasiFunc ('FuncType '[ 'I32, 'I64, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @fd_read(fd, iovs, iovs_len, nread)@
    FdRead :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @fd_readdir(fd, buf, buf_len, cookie, bufused)@
    FdReaddir :: WasiFunc ('FuncType '[ 'I32, 'I64, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @fd_renumber(fd, to)@
    FdRenumber :: WasiFunc ('FuncType '[ 'I32, 'I32] '[ 'I32])
    -- | @fd_seek(fd, offset, whence, newoffset)@
    FdSeek :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I64, 'I32] '[ 'I32])
    -- | @fd_sync(fd)@
    FdSync :: WasiFunc ('FuncType '[ 'I32] '[ 'I32])
    -- | @fd_tell(fd, offset)@
    FdTell :: WasiFunc ('FuncType '[ 'I32, 'I32] '[ 'I32])
    -- | @fd_write(fd, iovs, iovs_len, nwritten)@
    FdWrite :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @path_create_directory(fd, path, path_len)@
    PathCreateDirectory :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32] '[ 'I32])
    -- | @path_filestat_get(fd, flags, path, path_len, stat)@
    PathFilestatGet :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @path_filestat_set_times(fd, flags, path, path_len, atim, mtim, fst_flags)@
    PathFilestatSetTimes :: WasiFunc ('FuncType '[ 'I32, 'I64, 'I64, 'I32, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @path_link(old_fd, old_flags, old_path, old_path_len, new_fd, new_path, new_path_len)@
    PathLink :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32, 'I32, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @path_open(fd, dirflags, path, path_len, oflags, rights_base, rights_inheriting, fdflags, opened_fd)@
    PathOpen :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I64, 'I64, 'I32, 'I32, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @path_readlink(fd, path, path_len, buf, buf_len, bufused)@
    PathReadlink :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @path_remove_directory(fd, path, path_len)@
    PathRemoveDirectory :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32] '[ 'I32])
    -- | @path_rename(fd, old_path, old_path_len, new_fd, new_path, new_path_len)@
    PathRename :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @path_symlink(old_path, old_path_len, fd, new_path, new_path_len)@
    PathSymlink :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @path_unlink_file(fd, path, path_len)@
    PathUnlinkFile :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32] '[ 'I32])
    -- | @poll_oneoff(in, out, nsubscriptions, nevents)@
    PollOneoff :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @proc_exit(rval)@ — never returns
    ProcExit :: WasiFunc ('FuncType '[ 'I32] '[])
    -- | @proc_raise(sig)@
    ProcRaise :: WasiFunc ('FuncType '[ 'I32] '[ 'I32])
    -- | @sched_yield()@
    SchedYield :: WasiFunc ('FuncType '[] '[ 'I32])
    -- | @random_get(buf, buf_len)@
    RandomGet :: WasiFunc ('FuncType '[ 'I32, 'I32] '[ 'I32])
    -- | @sock_accept(fd, flags, fd_out)@
    SockAccept :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32] '[ 'I32])
    -- | @sock_recv(fd, ri_data, ri_data_len, ri_flags, ro_datalen, ro_flags)@
    SockRecv :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @sock_send(fd, si_data, si_data_len, si_flags, so_datalen)@
    SockSend :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @sock_shutdown(fd, how)@
    SockShutdown :: WasiFunc ('FuncType '[ 'I32, 'I32] '[ 'I32])

data SomeWasiFunc where
    SomeWasiFunc :: WasiFunc ft -> SomeWasiFunc

-- | Resolve an import's field name to a function of the interface (@Nothing@ if it has none).
resolveWasiImport :: Text -> Maybe SomeWasiFunc
resolveWasiImport name = case name of
    "args_get" -> Just (SomeWasiFunc ArgsGet)
    "args_sizes_get" -> Just (SomeWasiFunc ArgsSizesGet)
    "environ_get" -> Just (SomeWasiFunc EnvironGet)
    "environ_sizes_get" -> Just (SomeWasiFunc EnvironSizesGet)
    "clock_res_get" -> Just (SomeWasiFunc ClockResGet)
    "clock_time_get" -> Just (SomeWasiFunc ClockTimeGet)
    "fd_advise" -> Just (SomeWasiFunc FdAdvise)
    "fd_allocate" -> Just (SomeWasiFunc FdAllocate)
    "fd_close" -> Just (SomeWasiFunc FdClose)
    "fd_datasync" -> Just (SomeWasiFunc FdDatasync)
    "fd_fdstat_get" -> Just (SomeWasiFunc FdFdstatGet)
    "fd_fdstat_set_flags" -> Just (SomeWasiFunc FdFdstatSetFlags)
    "fd_fdstat_set_rights" -> Just (SomeWasiFunc FdFdstatSetRights)
    "fd_filestat_get" -> Just (SomeWasiFunc FdFilestatGet)
    "fd_filestat_set_size" -> Just (SomeWasiFunc FdFilestatSetSize)
    "fd_filestat_set_times" -> Just (SomeWasiFunc FdFilestatSetTimes)
    "fd_pread" -> Just (SomeWasiFunc FdPread)
    "fd_prestat_get" -> Just (SomeWasiFunc FdPrestatGet)
    "fd_prestat_dir_name" -> Just (SomeWasiFunc FdPrestatDirName)
    "fd_pwrite" -> Just (SomeWasiFunc FdPwrite)
    "fd_read" -> Just (SomeWasiFunc FdRead)
    "fd_readdir" -> Just (SomeWasiFunc FdReaddir)
    "fd_renumber" -> Just (SomeWasiFunc FdRenumber)
    "fd_seek" -> Just (SomeWasiFunc FdSeek)
    "fd_sync" -> Just (SomeWasiFunc FdSync)
    "fd_tell" -> Just (SomeWasiFunc FdTell)
    "fd_write" -> Just (SomeWasiFunc FdWrite)
    "path_create_directory" -> Just (SomeWasiFunc PathCreateDirectory)
    "path_filestat_get" -> Just (SomeWasiFunc PathFilestatGet)
    "path_filestat_set_times" -> Just (SomeWasiFunc PathFilestatSetTimes)
    "path_link" -> Just (SomeWasiFunc PathLink)
    "path_open" -> Just (SomeWasiFunc PathOpen)
    "path_readlink" -> Just (SomeWasiFunc PathReadlink)
    "path_remove_directory" -> Just (SomeWasiFunc PathRemoveDirectory)
    "path_rename" -> Just (SomeWasiFunc PathRename)
    "path_symlink" -> Just (SomeWasiFunc PathSymlink)
    "path_unlink_file" -> Just (SomeWasiFunc PathUnlinkFile)
    "poll_oneoff" -> Just (SomeWasiFunc PollOneoff)
    "proc_exit" -> Just (SomeWasiFunc ProcExit)
    "proc_raise" -> Just (SomeWasiFunc ProcRaise)
    "sched_yield" -> Just (SomeWasiFunc SchedYield)
    "random_get" -> Just (SomeWasiFunc RandomGet)
    "sock_accept" -> Just (SomeWasiFunc SockAccept)
    "sock_recv" -> Just (SomeWasiFunc SockRecv)
    "sock_send" -> Just (SomeWasiFunc SockSend)
    "sock_shutdown" -> Just (SomeWasiFunc SockShutdown)
    _ -> Nothing

-- | The singleton of a host function's type, for checking an import's declared type against it.
wasiFuncType :: WasiFunc ft -> Sing ft
wasiFuncType ArgsGet = sing
wasiFuncType ArgsSizesGet = sing
wasiFuncType EnvironGet = sing
wasiFuncType EnvironSizesGet = sing
wasiFuncType ClockResGet = sing
wasiFuncType ClockTimeGet = sing
wasiFuncType FdAdvise = sing
wasiFuncType FdAllocate = sing
wasiFuncType FdClose = sing
wasiFuncType FdDatasync = sing
wasiFuncType FdFdstatGet = sing
wasiFuncType FdFdstatSetFlags = sing
wasiFuncType FdFdstatSetRights = sing
wasiFuncType FdFilestatGet = sing
wasiFuncType FdFilestatSetSize = sing
wasiFuncType FdFilestatSetTimes = sing
wasiFuncType FdPread = sing
wasiFuncType FdPrestatGet = sing
wasiFuncType FdPrestatDirName = sing
wasiFuncType FdPwrite = sing
wasiFuncType FdRead = sing
wasiFuncType FdReaddir = sing
wasiFuncType FdRenumber = sing
wasiFuncType FdSeek = sing
wasiFuncType FdSync = sing
wasiFuncType FdTell = sing
wasiFuncType FdWrite = sing
wasiFuncType PathCreateDirectory = sing
wasiFuncType PathFilestatGet = sing
wasiFuncType PathFilestatSetTimes = sing
wasiFuncType PathLink = sing
wasiFuncType PathOpen = sing
wasiFuncType PathReadlink = sing
wasiFuncType PathRemoveDirectory = sing
wasiFuncType PathRename = sing
wasiFuncType PathSymlink = sing
wasiFuncType PathUnlinkFile = sing
wasiFuncType PollOneoff = sing
wasiFuncType ProcExit = sing
wasiFuncType ProcRaise = sing
wasiFuncType SchedYield = sing
wasiFuncType RandomGet = sing
wasiFuncType SockAccept = sing
wasiFuncType SockRecv = sing
wasiFuncType SockSend = sing
wasiFuncType SockShutdown = sing

-- | The interface's name for a function.
wasiFuncName :: WasiFunc ft -> Text
wasiFuncName ArgsGet = "args_get"
wasiFuncName ArgsSizesGet = "args_sizes_get"
wasiFuncName EnvironGet = "environ_get"
wasiFuncName EnvironSizesGet = "environ_sizes_get"
wasiFuncName ClockResGet = "clock_res_get"
wasiFuncName ClockTimeGet = "clock_time_get"
wasiFuncName FdAdvise = "fd_advise"
wasiFuncName FdAllocate = "fd_allocate"
wasiFuncName FdClose = "fd_close"
wasiFuncName FdDatasync = "fd_datasync"
wasiFuncName FdFdstatGet = "fd_fdstat_get"
wasiFuncName FdFdstatSetFlags = "fd_fdstat_set_flags"
wasiFuncName FdFdstatSetRights = "fd_fdstat_set_rights"
wasiFuncName FdFilestatGet = "fd_filestat_get"
wasiFuncName FdFilestatSetSize = "fd_filestat_set_size"
wasiFuncName FdFilestatSetTimes = "fd_filestat_set_times"
wasiFuncName FdPread = "fd_pread"
wasiFuncName FdPrestatGet = "fd_prestat_get"
wasiFuncName FdPrestatDirName = "fd_prestat_dir_name"
wasiFuncName FdPwrite = "fd_pwrite"
wasiFuncName FdRead = "fd_read"
wasiFuncName FdReaddir = "fd_readdir"
wasiFuncName FdRenumber = "fd_renumber"
wasiFuncName FdSeek = "fd_seek"
wasiFuncName FdSync = "fd_sync"
wasiFuncName FdTell = "fd_tell"
wasiFuncName FdWrite = "fd_write"
wasiFuncName PathCreateDirectory = "path_create_directory"
wasiFuncName PathFilestatGet = "path_filestat_get"
wasiFuncName PathFilestatSetTimes = "path_filestat_set_times"
wasiFuncName PathLink = "path_link"
wasiFuncName PathOpen = "path_open"
wasiFuncName PathReadlink = "path_readlink"
wasiFuncName PathRemoveDirectory = "path_remove_directory"
wasiFuncName PathRename = "path_rename"
wasiFuncName PathSymlink = "path_symlink"
wasiFuncName PathUnlinkFile = "path_unlink_file"
wasiFuncName PollOneoff = "poll_oneoff"
wasiFuncName ProcExit = "proc_exit"
wasiFuncName ProcRaise = "proc_raise"
wasiFuncName SchedYield = "sched_yield"
wasiFuncName RandomGet = "random_get"
wasiFuncName SockAccept = "sock_accept"
wasiFuncName SockRecv = "sock_recv"
wasiFuncName SockSend = "sock_send"
wasiFuncName SockShutdown = "sock_shutdown"
