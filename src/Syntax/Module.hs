{- | A decoded module and its components, before any validation: what the binary format's
  sections say, as plain records. Component vectors are lists — an index is a position — because
  the typed phase reflects them as type-level lists. (Functions and globals, which also have a
  typed form, are in "Syntax.Functions" and "Syntax.Globals".)
-}
module Syntax.Module (
    RawModule (..),
    RawImport (..),
    ImportDesc (..),
    RawMemory (..),
    RawTable (..),
    RawData (..),
    DataMode (..),
    RawElem (..),
    Export (..),
    ExportDesc (..),
) where

import Data.ByteString (ByteString)
import Data.Text (Text)

import Syntax.Functions (RawFunction)
import Syntax.Globals (RawGlobal)
import Syntax.Indices (FunctionIdx, GlobalIdx, MemoryIdx, TableIdx)
import Syntax.Instructions (RawExpr)
import Syntax.Types (FuncType, Limits, MemType)

data RawModule = RawModule
    { types :: [FuncType]
    -- ^ the type section
    , imports :: [RawImport]
    -- ^ imported functions; they come first in the function index space
    , funcs :: [RawFunction]
    -- ^ function + code sections, merged by the decoder
    , globals :: [RawGlobal]
    , memories :: [RawMemory]
    , tables :: [RawTable]
    , elements :: [RawElem]
    -- ^ active element segments, applied in order at instantiation
    , dataSegments :: [RawData]
    , exports :: [Export]
    , start :: Maybe FunctionIdx
    }

-- | An import: where it comes from and what it must be.
data RawImport = RawImport
    { moduleName :: Text
    , name :: Text
    , desc :: ImportDesc
    }
    deriving stock (Eq, Show)

-- | What is imported. Only functions so far; their type index is resolved by the decoder.
newtype ImportDesc = ImportFunc FuncType
    deriving stock (Eq, Show)

-- | A memory: just its type (the address width and page limits).
newtype RawMemory = RawMemory
    { memType :: MemType
    }
    deriving stock (Eq, Show)

-- | A table: its size limits. Only @funcref@ tables exist here, so that is all of it.
newtype RawTable = RawTable
    { limits :: Limits
    }
    deriving stock (Eq, Show)

{- | A data segment: bytes that are either copied into memory 0 at a constant offset when the
  module is instantiated (active), or kept for @memory.init@ to copy later (passive).
-}
data RawData = RawData
    { mode :: DataMode
    , bytes :: ByteString
    }

data DataMode
    = Active RawExpr
    | Passive

-- | An active element segment: functions to place in table 0 from a constant offset.
data RawElem = RawElem
    { offset :: RawExpr
    , functions :: [FunctionIdx]
    }

-- | A named entry point exposed by the module.
data Export = Export
    { name :: Text
    , desc :: ExportDesc
    }
    deriving stock (Eq, Show)

-- | What an export refers to.
data ExportDesc
    = ExportFunc FunctionIdx
    | ExportGlobal GlobalIdx
    | ExportMem MemoryIdx
    | ExportTable TableIdx
    deriving stock (Eq, Show)
