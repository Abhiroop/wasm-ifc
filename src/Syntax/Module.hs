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
    StateImports (..),
    importsNoState,
    referencedFunctions,
    RawImport (..),
    ImportDesc (..),
    RawMemory (..),
    RawTable (..),
    RawDataSegment (..),
    DataMode (..),
    RawElementSegment (..),
    ElemMode (..),
    Export (..),
    ExportDesc (..),

    -- * As validated
    Module (..),
    DataSegment (..),
    DataPlacement (..),
    ElementSpace (..),
    ElementSegment (..),
    ElementMode (..),
    SomeModule (..),
) where

import Data.ByteString (ByteString)
import Data.ByteString.Lazy qualified as BL
import Data.Singletons (Sing)
import Data.Text (Text)
import Data.Word (Word32)

import Syntax.Functions (FunctionSpace, RawFunction)
import Syntax.Globals (ConstExpr, GlobalSpace, RawGlobal (..))
import Syntax.Indices (FunctionIdx, GlobalIdx, MemoryIdx, TableIdx, TagIdx)
import Syntax.Instructions (RawExpr, RawInstr (RefFunc))
import Syntax.Types (AddrType, AddrVal, FuncType, IsRef, Limits, MemType, ValType (..))
import Syntax.TypesIFC (LabelledFuncType (..), SecLevel (..))
import Validation.Shape (Elem, ElemShape (..), MemShape (..), ModuleElems, ModuleFuncs, ModuleGlobals, ModuleMems, ModuleShape, ModuleTables, TableShape (..))

data RawModule = RawModule
    { types :: [FuncType]
    -- ^ the type section
    , imports :: [RawImport]
    -- ^ imported functions; they come first in the function index space
    , functions :: [RawFunction]
    -- ^ function + code sections, merged by the decoder
    , globals :: [RawGlobal]
    -- ^ the global index space: the imported globals ('stateImports'), then the defined ones
    , memories :: [RawMemory]
    , tables :: [RawTable]
    , elementSegments :: [RawElementSegment]
    , dataSegments :: [RawDataSegment]
    , exports :: [Export]
    , start :: Maybe FunctionIdx
    , customSections :: [(Text, BL.ByteString)]
    {- ^ every custom section, by name, in order; the @ifc@ ones carry the module's security
    policy ("Validation.Policy") and the rest are ignored
    -}
    , stateImports :: StateImports
    -- ^ which globals, memories and tables are imported
    , tags :: [FuncType]
    -- ^ the exception tags, each with the type of what an exception of it carries (as parameters)
    }

{- | The imports that are not functions. An imported global, memory or table comes first in its
  index space, before those the module defines, and is listed there with its type like them
  (an imported global with an empty initialiser); here are the module and field names each is
  imported under, in order. So the first @length globals@ entries of a module's globals are the
  imported ones, and likewise for the other two.
-}
data StateImports = StateImports
    { globals :: [(Text, Text)]
    , memories :: [(Text, Text)]
    , tables :: [(Text, Text)]
    }
    deriving stock (Eq, Show)

importsNoState :: StateImports
importsNoState = StateImports [] [] []

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

-- | A table: the reference type of its entries, the type of its indices, and its size limits.
data RawTable = RawTable
    { entryType :: ValType
    , addrType :: AddrType
    , limits :: Limits
    }
    deriving stock (Eq, Show)

{- | A data segment: bytes that are either copied into a memory at a constant offset when the
  module is instantiated (active), or kept for @memory.init@ to copy later (passive).
-}
data RawDataSegment = RawDataSegment
    { mode :: DataMode
    , bytes :: ByteString
    }

data DataMode
    = Active MemoryIdx RawExpr
    | Passive

{- | An element segment: references of one type, each given by a constant expression (a
  function index in the binary is the expression @ref.func@ of it). An active segment is
  written into a table at a constant offset when the module is instantiated; a passive one is
  kept for @table.init@; a declarative one only declares its functions for @ref.func@.
-}
data RawElementSegment = RawElementSegment
    { mode :: ElemMode
    , entryType :: ValType
    , items :: [RawExpr]
    }

data ElemMode
    = ElemActive TableIdx RawExpr
    | ElemPassive
    | ElemDeclarative

{- | The functions a module names outside its code, in element segments and in the initial
  values of globals: those a reference may come to refer to, and (with the exported ones) the
  only ones @ref.func@ may name in a function body.
-}
referencedFunctions :: RawModule -> [FunctionIdx]
referencedFunctions m = [f | expr <- concatMap (.items) m.elementSegments ++ map (.initializer) m.globals, RefFunc f <- expr]

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
    | ExportTag TagIdx
    deriving stock (Eq, Show)

-- *** As validated ***

{- | A validated module. Its memories, tables and data-segment count need no fields: the shape
  index says exactly what they are, and instantiation allocates them from it.
-}
data Module (shape :: ModuleShape) = Module
    { functions :: FunctionSpace shape (ModuleFuncs shape)
    , globals :: GlobalSpace (ModuleGlobals shape)
    , dataSegments :: [DataSegment (ModuleMems shape)]
    , secretRegions :: [(Word32, Word32)]
    -- ^ the half-open address ranges of memory 0 whose bytes the policy declares secret
    , elementSegments :: ElementSpace shape (ModuleElems shape)
    , memoryImports :: [(Text, Text)]
    -- ^ the names the first memories of the shape are imported under
    , tableImports :: [(Text, Text)]
    -- ^ likewise for its first tables
    , exports :: [Export]
    , start :: Maybe (Elem ('LabelledFuncType 'Low '[] '[]) (ModuleFuncs shape))
    -- ^ the start function, known to take and return nothing
    }

-- | A data segment as validated: where an active segment goes, and the bytes.
data DataSegment (ms :: [MemShape]) = DataSegment
    { placement :: Maybe (DataPlacement ms)
    , bytes :: ByteString
    }

-- | An active data segment's memory, and its constant offset there.
data DataPlacement (ms :: [MemShape]) where
    PlacedAt :: Sing at -> Elem ('MemShape at lo hi) ms -> ConstExpr (AddrVal at) -> DataPlacement ms

{- | A module's element index space: one segment per element type in the shape, so that
  @table.init@ and @elem.drop@ find a segment of the type their witness names.
-}
data ElementSpace (shape :: ModuleShape) (es :: [ElemShape]) where
    NoElements :: ElementSpace shape '[]
    Elements :: ElementSegment shape t -> ElementSpace shape es -> ElementSpace shape ('ElemShape t ': es)

-- | An element segment as validated: where it goes, and its references, each a constant of its type.
data ElementSegment (shape :: ModuleShape) (t :: ValType) = ElementSegment
    { mode :: ElementMode shape t
    , entryType :: IsRef t
    , items :: [ConstExpr t]
    }

{- | What becomes of an element segment at instantiation: it is written into a table of its
  type at a constant offset, kept for @table.init@, or neither (a declarative segment, whose
  only use is to declare its functions for @ref.func@).
-}
data ElementMode (shape :: ModuleShape) (t :: ValType) where
    WrittenTo :: Sing at -> Elem ('TableShape t lt at lo hi) (ModuleTables shape) -> ConstExpr (AddrVal at) -> ElementMode shape t
    KeptForInit :: ElementMode shape t
    DeclaredOnly :: ElementMode shape t

-- | A validated module with its shape hidden, together with the shape's singleton.
data SomeModule where
    SomeModule :: Sing (shape :: ModuleShape) -> Module shape -> SomeModule
