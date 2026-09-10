{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

{- | A module, in its two forms: 'RawModule' as decoded — what the binary format's sections
  say, as plain records, with lists for the index spaces — and 'Module' as validated, typed by
  its 'ModuleShape': every function body type-checked, every index resolved to a proof, every
  constant evaluated. A 'Module' is what instantiation turns into a running instance.
-}
module Syntax.Module (
    -- * As decoded
    RawModule (..),
    RawImport (..),
    ImportDesc (..),
    RawMemory (..),
    RawTable (..),
    RawDataSegment (..),
    DataMode (..),
    RawElementSegment (..),
    Export (..),
    ExportDesc (..),

    -- * As validated
    Module (..),
    DataSegment (..),
    ElementSegment (..),
    SomeModule (..),
) where

import Data.ByteString (ByteString)
import Data.Singletons (Sing)
import Data.Text (Text)
import Data.Word (Word32)

import Syntax.Functions (FunctionSpace, RawFunction)
import Syntax.Globals (GlobalSpace, RawGlobal)
import Syntax.Indices (FunctionIdx, GlobalIdx, MemoryIdx, TableIdx)
import Syntax.Instructions (RawExpr)
import Syntax.Types (FuncType (..), Limits, MemType)
import Validation.Shape (Elem, ModuleFuncs, ModuleGlobals, ModuleShape, SomeFuncRef)

data RawModule = RawModule
    { types :: [FuncType]
    -- ^ the type section
    , imports :: [RawImport]
    -- ^ imported functions; they come first in the function index space
    , functions :: [RawFunction]
    -- ^ function + code sections, merged by the decoder
    , globals :: [RawGlobal]
    , memories :: [RawMemory]
    , tables :: [RawTable]
    , elementSegments :: [RawElementSegment]
    -- ^ active element segments, applied in order at instantiation
    , dataSegments :: [RawDataSegment]
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
data RawDataSegment = RawDataSegment
    { mode :: DataMode
    , bytes :: ByteString
    }

data DataMode
    = Active RawExpr
    | Passive

-- | An active element segment: functions to place in table 0 from a constant offset.
data RawElementSegment = RawElementSegment
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

-- *** As validated ***

{- | A validated module. Its memories, tables and data-segment count need no fields: the shape
  index says exactly what they are, and instantiation allocates them from it.
-}
data Module (shape :: ModuleShape) = Module
    { functions :: FunctionSpace shape (ModuleFuncs shape)
    , globals :: GlobalSpace (ModuleGlobals shape)
    , dataSegments :: [DataSegment]
    , elementSegments :: [ElementSegment (ModuleFuncs shape)]
    , exports :: [Export]
    , start :: Maybe (Elem ('FuncType '[] '[]) (ModuleFuncs shape))
    -- ^ the start function, known to take and return nothing
    }

-- | A data segment as validated: an active segment's constant offset, and the bytes.
data DataSegment = DataSegment
    { placement :: Maybe Word32
    , bytes :: ByteString
    }

-- | An element segment as validated: its constant offset, and its functions, each resolved.
data ElementSegment (fts :: [FuncType]) = ElementSegment
    { offset :: Word32
    , functions :: [SomeFuncRef fts]
    }

-- | A validated module with its shape hidden, together with the shape's singleton.
data SomeModule where
    SomeModule :: Sing (shape :: ModuleShape) -> Module shape -> SomeModule
