module Syntax.Module where

import Data.Text (Text)

import Syntax.Functions (RawFunction)
import Syntax.Globals   (RawGlobal)
import Syntax.Indices   (FunctionIdx, GlobalIdx, MemoryIdx)
import Syntax.Memories  (RawMemory)
import Syntax.Types     (FuncType)

-- | What an export refers to.
data ExportDesc
    = ExportFunc   FunctionIdx
    | ExportGlobal GlobalIdx
    | ExportMem    MemoryIdx
    deriving (Eq, Show)

-- | A named entry point exposed by the module.
data Export = Export
    { exportName :: Text
    , exportDesc :: ExportDesc
    } deriving (Eq, Show)

-- | A decoded module, before any validation.
--
-- Component vectors are plain lists: an index is a position in the list. Lists
-- (rather than 'Data.Array.Array') are intentional — the typed phase will reflect
-- these as type-level lists, which is far more tractable than type-level arrays.
data RawModule = RawModule
    { moduleTypes    :: [FuncType]      -- ^ the type section
    , moduleFuncs    :: [RawFunction]   -- ^ function + code sections, merged by the decoder
    , moduleGlobals  :: [RawGlobal]
    , moduleMemories :: [RawMemory]
    , moduleExports  :: [Export]
    , moduleStart    :: Maybe FunctionIdx
    }
