{- | The indices of a decoded module's globals, memories and tables, wherever the module uses
  them: in instructions, constant expressions, segments and exports.

  A module may import one object twice, under two indices (the same memory of another module,
  say). Inside one instance each index holds its own object ("Runtime.Link"), so the two would
  not stay one. They need not: a use of the second index is a use of the first, and can be
  written as one. 'renamed' does that, and records the second index in 'RawModule.aliases' as
  one that nothing uses any more; the elaborator checks that claim with 'used' before it
  believes it, and the linker then leaves such an index alone.
-}
module Validation.Aliases (
    Kind (..),
    renamed,
    used,
) where

import Data.Functor.Const qualified as Functor
import Data.Functor.Identity (Identity (..))
import Data.Word (Word32)

import Syntax.Functions (RawFunction (..))
import Syntax.Globals (RawGlobal (..))
import Syntax.Immediates (MemArg (..))
import Syntax.Indices
import Syntax.Instructions
import Syntax.Module (DataMode (..), ElemMode (..), Export (..), ExportDesc (..), RawDataSegment (..), RawElementSegment (..), RawModule (..))

-- | An index space whose entries may be imported.
data Kind = OfGlobals | OfMemories | OfTables
    deriving stock (Eq, Show)

-- | The module with every use of an index replaced by what the function gives for it.
renamed :: (Kind -> Word32 -> Word32) -> RawModule -> RawModule
renamed rename = runIdentity . overModule (\kind index -> Identity (rename kind index))

-- | Every index the module uses, with its kind.
used :: RawModule -> [(Kind, Word32)]
used = Functor.getConst . overModule (\kind index -> Functor.Const [(kind, index)])

overModule :: Applicative f => (Kind -> Word32 -> f Word32) -> RawModule -> f RawModule
overModule at m =
    rebuilt
        <$> traverse (\function -> (\body -> function {body}) <$> overExpr at function.body) m.functions
        <*> traverse (\global -> RawGlobal global.globalType <$> overExpr at global.initializer) m.globals
        <*> traverse element m.elementSegments
        <*> traverse segment m.dataSegments
        <*> traverse export m.exports
        <*> traverse (\(TableIdx t, expr) -> (,) . TableIdx <$> at OfTables t <*> overExpr at expr) m.tableInitialisers
  where
    rebuilt functions globals elementSegments dataSegments exports tableInitialisers =
        m {functions, globals, elementSegments, dataSegments, exports, tableInitialisers}
    element (RawElementSegment mode entryType items) = RawElementSegment <$> elementMode mode <*> pure entryType <*> traverse (overExpr at) items
    elementMode mode = case mode of
        ElemActive (TableIdx t) offset -> ElemActive . TableIdx <$> at OfTables t <*> overExpr at offset
        ElemPassive -> pure ElemPassive
        ElemDeclarative -> pure ElemDeclarative
    segment (RawDataSegment mode bytes) = RawDataSegment <$> dataMode mode <*> pure bytes
    dataMode mode = case mode of
        Active (MemoryIdx i) offset -> Active . MemoryIdx <$> at OfMemories i <*> overExpr at offset
        Passive -> pure Passive
    export (Export name desc) =
        Export name <$> case desc of
            ExportGlobal (GlobalIdx g) -> ExportGlobal . GlobalIdx <$> at OfGlobals g
            ExportMem (MemoryIdx i) -> ExportMem . MemoryIdx <$> at OfMemories i
            ExportTable (TableIdx t) -> ExportTable . TableIdx <$> at OfTables t
            ExportFunc _ -> pure desc
            ExportTag _ -> pure desc

overExpr :: Applicative f => (Kind -> Word32 -> f Word32) -> [RawInstr] -> f [RawInstr]
overExpr at = traverse (overInstr at)

-- | An instruction with its indices of globals, memories and tables visited, and those of the instructions inside it.
overInstr :: Applicative f => (Kind -> Word32 -> f Word32) -> RawInstr -> f RawInstr
overInstr at instr = case instr of
    Block blockType body -> Block blockType <$> overExpr at body
    Loop blockType body -> Loop blockType <$> overExpr at body
    If blockType thenArm elseArm -> If blockType <$> overExpr at thenArm <*> overExpr at elseArm
    TryTable blockType clauses body -> TryTable blockType clauses <$> overExpr at body
    Annotated level inner -> Annotated level <$> overInstr at inner
    AtSite site inner -> AtSite site <$> overInstr at inner
    Precisely note inner -> Precisely note <$> overInstr at inner
    GlobalGet (GlobalIdx g) -> GlobalGet . GlobalIdx <$> at OfGlobals g
    GlobalSet (GlobalIdx g) -> GlobalSet . GlobalIdx <$> at OfGlobals g
    Load t memArg -> Load t <$> memory memArg
    Store t memArg -> Store t <$> memory memArg
    LoadN t width sign memArg -> LoadN t width sign <$> memory memArg
    StoreN t width memArg -> StoreN t width <$> memory memArg
    VectorLoad kind memArg -> VectorLoad kind <$> memory memArg
    VectorStore memArg -> VectorStore <$> memory memArg
    VectorLoadLane width lane memArg -> VectorLoadLane width lane <$> memory memArg
    VectorStoreLane width lane memArg -> VectorStoreLane width lane <$> memory memArg
    MemorySize (MemoryIdx i) -> MemorySize . MemoryIdx <$> at OfMemories i
    MemoryGrow (MemoryIdx i) -> MemoryGrow . MemoryIdx <$> at OfMemories i
    MemoryFill (MemoryIdx i) -> MemoryFill . MemoryIdx <$> at OfMemories i
    MemoryCopy (MemoryIdx to) (MemoryIdx from) -> (\to' from' -> MemoryCopy (MemoryIdx to') (MemoryIdx from')) <$> at OfMemories to <*> at OfMemories from
    MemoryInit segment (MemoryIdx i) -> MemoryInit segment . MemoryIdx <$> at OfMemories i
    TableGet (TableIdx t) -> TableGet . TableIdx <$> at OfTables t
    TableSet (TableIdx t) -> TableSet . TableIdx <$> at OfTables t
    TableSize (TableIdx t) -> TableSize . TableIdx <$> at OfTables t
    TableGrow (TableIdx t) -> TableGrow . TableIdx <$> at OfTables t
    TableFill (TableIdx t) -> TableFill . TableIdx <$> at OfTables t
    TableCopy (TableIdx to) (TableIdx from) -> (\to' from' -> TableCopy (TableIdx to') (TableIdx from')) <$> at OfTables to <*> at OfTables from
    TableInit segment (TableIdx t) -> TableInit segment . TableIdx <$> at OfTables t
    CallIndirect (TableIdx t) expected -> (\t' -> CallIndirect (TableIdx t') expected) <$> at OfTables t
    ReturnCallIndirect (TableIdx t) expected -> (\t' -> ReturnCallIndirect (TableIdx t') expected) <$> at OfTables t
    -- The rest name no global, memory or table. Each is listed, so that an instruction added
    -- later is not passed over here without anyone deciding that it should be.
    Unreachable -> pure instr
    Nop -> pure instr
    Br _ -> pure instr
    BrIf _ -> pure instr
    BrTable _ _ -> pure instr
    Return -> pure instr
    Call _ -> pure instr
    Throw _ -> pure instr
    ThrowRef -> pure instr
    ReturnCall _ -> pure instr
    LocalGet _ -> pure instr
    LocalSet _ -> pure instr
    LocalTee _ -> pure instr
    Relabel _ -> pure instr
    Declassify _ -> pure instr
    DataDrop _ -> pure instr
    Vector _ -> pure instr
    RefNull _ -> pure instr
    RefIsNull -> pure instr
    RefFunc _ -> pure instr
    CallRef _ -> pure instr
    ReturnCallRef _ -> pure instr
    RefAsNonNull -> pure instr
    BrOnNull _ -> pure instr
    BrOnNonNull _ -> pure instr
    Duplicate -> pure instr
    ElemDrop _ -> pure instr
    Const _ _ -> pure instr
    Add _ -> pure instr
    Sub _ -> pure instr
    Mul _ -> pure instr
    Div _ _ -> pure instr
    Rem _ _ -> pure instr
    And _ -> pure instr
    Or _ -> pure instr
    Xor _ -> pure instr
    Shl _ -> pure instr
    Shr _ _ -> pure instr
    Rotl _ -> pure instr
    Rotr _ -> pure instr
    Clz _ -> pure instr
    Ctz _ -> pure instr
    Popcnt _ -> pure instr
    Abs _ -> pure instr
    Neg _ -> pure instr
    Sqrt _ -> pure instr
    Ceil _ -> pure instr
    Floor _ -> pure instr
    FloatTrunc _ -> pure instr
    Nearest _ -> pure instr
    Min _ -> pure instr
    Max _ -> pure instr
    Copysign _ -> pure instr
    Convert _ -> pure instr
    Eqz _ -> pure instr
    Eq _ -> pure instr
    Ne _ -> pure instr
    Lt _ _ -> pure instr
    Gt _ _ -> pure instr
    Le _ _ -> pure instr
    Ge _ _ -> pure instr
    Drop -> pure instr
    Select -> pure instr
    SelectTyped _ -> pure instr
  where
    memory memArg = (\i -> memArg {memory = i}) <$> at OfMemories memArg.memory
