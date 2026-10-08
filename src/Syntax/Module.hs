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
    ElementSpace (..),
    ElementSegment (..),
    ElementMode (..),
    ConstRef (..),
    constReference,
    SomeModule (..),
) where

import Data.ByteString (ByteString)
import Data.ByteString.Lazy qualified as BL
import Data.Singletons (Sing)
import Data.Text (Text)
import Data.Word (Word32)

import Syntax.Functions (FunctionSpace, RawFunction)
import Syntax.Globals (GlobalSpace, RawGlobal (..))
import Syntax.Immediates (Reference, nullReference)
import Syntax.Indices (FunctionIdx, GlobalIdx, MemoryIdx, TableIdx)
import Syntax.Instructions (RawExpr, RawInstr (RefFunc))
import Syntax.Types (FuncType, Limits, MemType, ValType (..))
import Syntax.TypesIFC (LabelledFuncType (..), SecLevel (..))
import Validation.Ref (FunctionRef, functionReference)
import Validation.Shape (Elem, ElemShape (..), ModuleElems, ModuleFuncs, ModuleGlobals, ModuleShape, ModuleTables, TableShape (..))

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
    , dataSegments :: [RawDataSegment]
    , exports :: [Export]
    , start :: Maybe FunctionIdx
    , customSections :: [(Text, BL.ByteString)]
    {- ^ every custom section, by name, in order; the @ifc@ ones carry the module's security
    policy ("Validation.Policy") and the rest are ignored
    -}
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

-- | A table: the reference type of its entries, and its size limits.
data RawTable = RawTable
    { entryType :: ValType
    , limits :: Limits
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
    deriving stock (Eq, Show)

-- *** As validated ***

{- | A validated module. Its memories, tables and data-segment count need no fields: the shape
  index says exactly what they are, and instantiation allocates them from it.
-}
data Module (shape :: ModuleShape) = Module
    { functions :: FunctionSpace shape (ModuleFuncs shape)
    , globals :: GlobalSpace (ModuleGlobals shape)
    , dataSegments :: [DataSegment]
    , secretRegions :: [(Word32, Word32)]
    -- ^ the half-open address ranges of memory 0 whose bytes the policy declares secret
    , elementSegments :: ElementSpace shape (ModuleElems shape)
    , exports :: [Export]
    , start :: Maybe (Elem ('LabelledFuncType 'Low '[] '[]) (ModuleFuncs shape))
    -- ^ the start function, known to take and return nothing
    }

-- | A data segment as validated: an active segment's constant offset, and the bytes.
data DataSegment = DataSegment
    { placement :: Maybe Word32
    , bytes :: ByteString
    }

{- | A module's element index space: one segment per element type in the shape, so that
  @table.init@ and @elem.drop@ find a segment of the type their witness names.
-}
data ElementSpace (shape :: ModuleShape) (es :: [ElemShape]) where
    NoElements :: ElementSpace shape '[]
    Elements :: ElementSegment shape t -> ElementSpace shape es -> ElementSpace shape ('ElemShape t ': es)

-- | An element segment as validated: where it goes, and its references, each resolved.
data ElementSegment (shape :: ModuleShape) (t :: ValType) = ElementSegment
    { mode :: ElementMode shape t
    , items :: [ConstRef (ModuleFuncs shape) t]
    }

{- | What becomes of an element segment at instantiation: it is written into a table of its
  type at a constant offset, kept for @table.init@, or neither (a declarative segment, whose
  only use is to declare its functions for @ref.func@).
-}
data ElementMode (shape :: ModuleShape) (t :: ValType) where
    WrittenTo :: Elem ('TableShape t lt lo hi) (ModuleTables shape) -> Word32 -> ElementMode shape t
    KeptForInit :: ElementMode shape t
    DeclaredOnly :: ElementMode shape t

-- | A constant of a reference type: null, or a function of the module.
data ConstRef (fts :: [LabelledFuncType]) (t :: ValType) where
    NullConst :: ConstRef fts t
    FunctionConst :: FunctionRef fts -> ConstRef fts 'FuncRef

constReference :: ConstRef fts t -> Reference
constReference NullConst = nullReference
constReference (FunctionConst function) = functionReference function

-- | A validated module with its shape hidden, together with the shape's singleton.
data SomeModule where
    SomeModule :: Sing (shape :: ModuleShape) -> Module shape -> SomeModule
