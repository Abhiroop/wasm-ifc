module Syntax.Module (
    ExportDesc (..),
    Export (..),
    RawModule (..),
) where

import Data.Text (Text)

import Syntax.DataSegments (RawData)
import Syntax.Elements (RawElem)
import Syntax.Functions (RawFunction)
import Syntax.Globals (RawGlobal)
import Syntax.Imports (RawImport)
import Syntax.Indices (FunctionIdx, GlobalIdx, MemoryIdx, TableIdx)
import Syntax.Memories (RawMemory)
import Syntax.Tables (RawTable)
import Syntax.Types (FuncType)

-- | What an export refers to.
data ExportDesc
    = ExportFunc FunctionIdx
    | ExportGlobal GlobalIdx
    | ExportMem MemoryIdx
    | ExportTable TableIdx
    deriving stock (Eq, Show)

-- | A named entry point exposed by the module.
data Export = Export
    { name :: Text
    , desc :: ExportDesc
    }
    deriving stock (Eq, Show)

{- | A decoded module, before any validation.

Component vectors are plain lists: an index is a position in the list. Lists
(rather than 'Data.Array.Array') are intentional — the typed phase will reflect
these as type-level lists, which is far more tractable than type-level arrays.
-}
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
    -- ^ active data segments, applied in order at instantiation
    , exports :: [Export]
    , start :: Maybe FunctionIdx
    }
