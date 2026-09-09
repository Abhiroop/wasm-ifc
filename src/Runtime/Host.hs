{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

{- | The host functions a module may import: the WASI Preview 1 subset we provide, each at
  the exact function type the interface fixes. This is the pure vocabulary; performing a
  call is "Runtime.Wasi"'s job.

  A 'WasiFunc' is indexed by its type, so a host function can only ever be installed in a
  module at the type it really has, and the interpreter receives its arguments as a stack of
  exactly that shape (last argument on top, like every stack segment).
-}
module Runtime.Host (
    WasiFunc (..),
    SomeWasiFunc (..),
    wasiModuleName,
    resolveWasiImport,
    wasiFuncType,
) where

import Data.Singletons (Sing, sing)
import Data.Text (Text)

import Syntax.Types (FuncType (..), ValType (..))

-- | The import module name WASI functions are resolved against.
wasiModuleName :: Text
wasiModuleName = "wasi_snapshot_preview1"

data WasiFunc (ft :: FuncType) where
    -- | @fd_write(fd, iovs, iovs_len, nwritten) -> errno@
    FdWrite :: WasiFunc ('FuncType '[ 'I32, 'I32, 'I32, 'I32] '[ 'I32])
    -- | @proc_exit(code)@ — never returns
    ProcExit :: WasiFunc ('FuncType '[ 'I32] '[])

data SomeWasiFunc where
    SomeWasiFunc :: WasiFunc ft -> SomeWasiFunc

-- | Resolve an import's field name to a supported function (@Nothing@ if unsupported).
resolveWasiImport :: Text -> Maybe SomeWasiFunc
resolveWasiImport name = case name of
    "fd_write" -> Just (SomeWasiFunc FdWrite)
    "proc_exit" -> Just (SomeWasiFunc ProcExit)
    _ -> Nothing

-- | The singleton of a host function's type, for checking an import's declared type against it.
wasiFuncType :: WasiFunc ft -> Sing ft
wasiFuncType FdWrite = sing
wasiFuncType ProcExit = sing
