{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{- | WebAssembly instructions, in their two forms, side by side:

  * 'RawInstr' — the untyped, unvalidated tree the decoder produces (elaboration's input).
  * 'Instr' — the intrinsically-typed form, indexed by the value-stack shapes, locals,
    labels and module shape it runs within, so only well-typed programs are representable.
    'Expr' is a sequence of them.

The @Raw@ prefix is the only thing distinguishing the two.
-}
module Syntax.Instructions (
    -- * Untyped (decoded) AST
    RawInstr (..),
    RawExpr,
    ConvertOp (..),
    convertEnds,
    BitwiseOp (..),
    CountOp (..),
    FloatUnOp (..),
    FloatBinOp (..),

    -- * Intrinsically-typed AST
    Instr (..),
    Expr (..),

    -- * Smart constructors (empty-result label variants)
    call,
    block_,
    loop_,
    br_,
    brIf_,
) where

import Data.List.Singletons (type (++))
import Data.Singletons.TH (Sing, SingI (sing))
import Syntax.Immediates
import Syntax.Indices
import Syntax.Types
import Syntax.TypesIFC
import Validation.Ref (LocalRef)
import Validation.Shape (
    Append (..),
    BranchTarget,
    DataShape (..),
    Elem,
    FrameLocals,
    FrameReturn,
    FrameShape,
    ModuleData,
    ModuleFuncs,
    ModuleGlobals,
    ModuleMems,
    ModuleShape,
    ModuleTables,
    appendFromSing,
 )

{- | The untyped WebAssembly instruction AST: the raw, unvalidated representation produced by
  the decoder. Numeric instructions carry a @Sing (t :: ValType)@ recording the type they operate
  on; integer operations whose meaning depends on signedness carry a 'Signedness'.
-}
data RawInstr where
    -- \*** Control ***
    Unreachable :: RawInstr
    Nop :: RawInstr
    Block :: BlockType -> [RawInstr] -> RawInstr
    Loop :: BlockType -> [RawInstr] -> RawInstr
    If :: BlockType -> [RawInstr] -> [RawInstr] -> RawInstr
    Br :: LabelIdx -> RawInstr
    BrIf :: LabelIdx -> RawInstr
    BrTable :: [LabelIdx] -> LabelIdx -> RawInstr
    Return :: RawInstr
    Call :: FunctionIdx -> RawInstr
    CallIndirect :: TypeIdx -> RawInstr
    -- \*** Locals & globals ***
    LocalGet :: LocalIdx -> RawInstr
    LocalSet :: LocalIdx -> RawInstr
    LocalTee :: LocalIdx -> RawInstr
    GlobalGet :: GlobalIdx -> RawInstr
    GlobalSet :: GlobalIdx -> RawInstr
    -- \*** Memory ***
    Load :: Sing (t :: ValType) -> MemArg -> RawInstr
    Store :: Sing (t :: ValType) -> MemArg -> RawInstr
    -- narrow load/store: @width@ is the storage width in bytes (1, 2 or 4); loads also
    -- carry a 'Signedness' for sign/zero extension.
    LoadN :: Sing (t :: ValType) -> Int -> Signedness -> MemArg -> RawInstr
    StoreN :: Sing (t :: ValType) -> Int -> MemArg -> RawInstr
    MemorySize :: RawInstr
    MemoryGrow :: RawInstr
    -- \*** Information flow (never decoded: the policy stage produces them, see
    --       "Validation.Policy") ***

    -- | a load or store with the security level it declares
    Annotated :: SecLevel -> RawInstr -> RawInstr
    -- | raise the level of the value on top of the stack to this one
    Relabel :: SecLevel -> RawInstr
    {- | lower the level of the value on top of the stack to this one: trusted, and only
    allowed when the policy says so
    -}
    Declassify :: SecLevel -> RawInstr
    -- bulk memory: @memory.copy@, @memory.fill@, @memory.init@ from a data segment, @data.drop@
    MemoryCopy :: RawInstr
    MemoryFill :: RawInstr
    MemoryInit :: DataIdx -> RawInstr
    DataDrop :: DataIdx -> RawInstr
    -- \*** Constants ***
    Const :: Sing (t :: ValType) -> HostType t -> RawInstr
    -- \*** Numeric ***
    Add :: Sing (t :: ValType) -> RawInstr
    Sub :: Sing (t :: ValType) -> RawInstr
    Mul :: Sing (t :: ValType) -> RawInstr
    Div :: Sing (t :: ValType) -> Signedness -> RawInstr
    Rem :: Sing (t :: ValType) -> Signedness -> RawInstr
    -- \*** Integer bitwise / shift / count ***
    And :: Sing (t :: ValType) -> RawInstr
    Or :: Sing (t :: ValType) -> RawInstr
    Xor :: Sing (t :: ValType) -> RawInstr
    Shl :: Sing (t :: ValType) -> RawInstr
    Shr :: Sing (t :: ValType) -> Signedness -> RawInstr
    Rotl :: Sing (t :: ValType) -> RawInstr
    Rotr :: Sing (t :: ValType) -> RawInstr
    Clz :: Sing (t :: ValType) -> RawInstr
    Ctz :: Sing (t :: ValType) -> RawInstr
    Popcnt :: Sing (t :: ValType) -> RawInstr
    -- \*** Floating-point unary / binary ***
    Abs :: Sing (t :: ValType) -> RawInstr
    Neg :: Sing (t :: ValType) -> RawInstr
    Sqrt :: Sing (t :: ValType) -> RawInstr
    Ceil :: Sing (t :: ValType) -> RawInstr
    Floor :: Sing (t :: ValType) -> RawInstr
    FloatTrunc :: Sing (t :: ValType) -> RawInstr
    Nearest :: Sing (t :: ValType) -> RawInstr
    Min :: Sing (t :: ValType) -> RawInstr
    Max :: Sing (t :: ValType) -> RawInstr
    Copysign :: Sing (t :: ValType) -> RawInstr
    -- \*** Conversions ***
    Convert :: ConvertOp from to -> RawInstr
    -- \*** Comparison ***
    Eqz :: Sing (t :: ValType) -> RawInstr
    Eq :: Sing (t :: ValType) -> RawInstr
    Ne :: Sing (t :: ValType) -> RawInstr
    Lt :: Sing (t :: ValType) -> Signedness -> RawInstr
    Gt :: Sing (t :: ValType) -> Signedness -> RawInstr
    Le :: Sing (t :: ValType) -> Signedness -> RawInstr
    Ge :: Sing (t :: ValType) -> Signedness -> RawInstr
    -- \*** Stack management ***
    Drop :: RawInstr
    Select :: RawInstr
    -- | @select t*@ as encoded: the annotation is a vector, which validation requires to hold one type
    SelectTyped :: [ValType] -> RawInstr

-- | An expression: a flat list of (tree-structured) instructions — a function body or an initializer.
type RawExpr = [RawInstr]

{- | The fixed-opcode numeric conversions, each indexed by its concrete source and target
  value types — so the op /is/ the evidence of what it converts, and a conversion cannot be
  typed at anything other than the types its opcode names. @Signedness@ selects the signed or
  unsigned form where the opcode has both.
-}
data ConvertOp (from :: ValType) (to :: ValType) where
    I32WrapI64 :: ConvertOp 'I64 'I32
    I64ExtendI32 :: Signedness -> ConvertOp 'I32 'I64
    I32TruncF32 :: Signedness -> ConvertOp 'F32 'I32
    I32TruncF64 :: Signedness -> ConvertOp 'F64 'I32
    I64TruncF32 :: Signedness -> ConvertOp 'F32 'I64
    I64TruncF64 :: Signedness -> ConvertOp 'F64 'I64
    -- the saturating forms (0xFC prefix): out of range clamps, NaN gives zero, never a trap
    I32TruncSatF32 :: Signedness -> ConvertOp 'F32 'I32
    I32TruncSatF64 :: Signedness -> ConvertOp 'F64 'I32
    I64TruncSatF32 :: Signedness -> ConvertOp 'F32 'I64
    I64TruncSatF64 :: Signedness -> ConvertOp 'F64 'I64
    F32ConvertI32 :: Signedness -> ConvertOp 'I32 'F32
    F32ConvertI64 :: Signedness -> ConvertOp 'I64 'F32
    F64ConvertI32 :: Signedness -> ConvertOp 'I32 'F64
    F64ConvertI64 :: Signedness -> ConvertOp 'I64 'F64
    F32DemoteF64 :: ConvertOp 'F64 'F32
    F64PromoteF32 :: ConvertOp 'F32 'F64
    I32ReinterpretF32 :: ConvertOp 'F32 'I32
    F32ReinterpretI32 :: ConvertOp 'I32 'F32
    I64ReinterpretF64 :: ConvertOp 'F64 'I64
    F64ReinterpretI64 :: ConvertOp 'I64 'F64
    I32Extend8S :: ConvertOp 'I32 'I32
    I32Extend16S :: ConvertOp 'I32 'I32
    I64Extend8S :: ConvertOp 'I64 'I64
    I64Extend16S :: ConvertOp 'I64 'I64
    I64Extend32S :: ConvertOp 'I64 'I64

{- | The numeric source/target witnesses of a conversion — the value-level companion to its
  type indices, used to reflect the types (elaboration) and marshal operands (interpreter).
-}
convertEnds :: ConvertOp from to -> (IsNum from, IsNum to)
convertEnds I32WrapI64 = (I64IsNum, I32IsNum)
convertEnds (I64ExtendI32 _) = (I32IsNum, I64IsNum)
convertEnds (I32TruncF32 _) = (F32IsNum, I32IsNum)
convertEnds (I32TruncF64 _) = (F64IsNum, I32IsNum)
convertEnds (I64TruncF32 _) = (F32IsNum, I64IsNum)
convertEnds (I64TruncF64 _) = (F64IsNum, I64IsNum)
convertEnds (I32TruncSatF32 _) = (F32IsNum, I32IsNum)
convertEnds (I32TruncSatF64 _) = (F64IsNum, I32IsNum)
convertEnds (I64TruncSatF32 _) = (F32IsNum, I64IsNum)
convertEnds (I64TruncSatF64 _) = (F64IsNum, I64IsNum)
convertEnds (F32ConvertI32 _) = (I32IsNum, F32IsNum)
convertEnds (F32ConvertI64 _) = (I64IsNum, F32IsNum)
convertEnds (F64ConvertI32 _) = (I32IsNum, F64IsNum)
convertEnds (F64ConvertI64 _) = (I64IsNum, F64IsNum)
convertEnds F32DemoteF64 = (F64IsNum, F32IsNum)
convertEnds F64PromoteF32 = (F32IsNum, F64IsNum)
convertEnds I32ReinterpretF32 = (F32IsNum, I32IsNum)
convertEnds F32ReinterpretI32 = (I32IsNum, F32IsNum)
convertEnds I64ReinterpretF64 = (F64IsNum, I64IsNum)
convertEnds F64ReinterpretI64 = (I64IsNum, F64IsNum)
convertEnds I32Extend8S = (I32IsNum, I32IsNum)
convertEnds I32Extend16S = (I32IsNum, I32IsNum)
convertEnds I64Extend8S = (I64IsNum, I64IsNum)
convertEnds I64Extend16S = (I64IsNum, I64IsNum)
convertEnds I64Extend32S = (I64IsNum, I64IsNum)

-- | Same-type operation groups, so the GADT (and interpreter) stay compact.
data BitwiseOp = BwAnd | BwOr | BwXor | BwShl | BwShr Signedness | BwRotl | BwRotr
    deriving stock (Eq, Show)

data CountOp = OpClz | OpCtz | OpPopcnt deriving stock (Eq, Show)
data FloatUnOp = FAbs | FNeg | FSqrt | FCeil | FFloor | FTrunc | FNearest deriving stock (Eq, Show)
data FloatBinOp = FMin | FMax | FCopysign deriving stock (Eq, Show)

{- | The intrinsically-typed instruction. Its last two indices, @stackIn@/@stackOut@, are
  the instruction's actual type — the operand stack before and after. The first three are
  its typing context, organised by scope:

    * @mod@    — module-scoped: the module's functions, globals and memories.
    * @frame@  — function-scoped: the current function's locals and result type.
    * @labels@ — block-scoped: the result types of the enclosing branch targets.

  Every type on the stack, in the frame and in a label is a /labelled/ value type
  (@t ':~ l@, from "Syntax.TypesIFC"): a value type together with a security level, 'Low for
  public data and 'High for secret data. So this one type tracks information flow as well as
  value types. The rule for computed values is that a result is as secret as the most secret
  operand it was computed from, which the signatures below write as @Join l l'@. The levels
  exist only in the types. At run time a value is a bare machine word, exactly as before.

  Two more indices, @pcIn@ and @pcOut@, are the stack of program counter labels before and
  after the instruction ('PcStack' in "Syntax.TypesIFC" explains it). The top entry, written
  @pc@ below, is the level of the decisions that led control here. Three rules use it, all taken
  from the @ifc@ branch, which follows SecWasm:

    * a value pushed under @pc@ is at least as secret as @pc@, so every result is joined with it;
    * a write to a variable needs both the value and @pc@ to flow into the variable's level,
      because a write inside a secret branch reveals the branch condition even when the value
      written is public;
    * a branch raises the pc entries of the blocks it may leave ('BranchTarget'), and the
      values it carries must be at least as secret as the decision to branch ('AllAtLeast').

  Each side condition is a witness the instruction carries ('FlowsInto', 'AllAtLeast'), which
  the validator builds with a decision procedure and a hand-written program states directly.

  What is still unfinished has a @TODO(ifc …)@ beside it (@grep -rn 'TODO(ifc' src test@ lists
  them; P0 is a decision to take first, P1 is needed for a sound system, P2 for real modules,
  P3 is polish). The large one is function types, which have no bound on the pc they may be
  called from, so calls are only allowed at a public pc for now.
-}

-- TODO: organize instructions into groups: data, mem, ctrl and admin
-- TODO: [ValType] into ValStackType and remove ResultType
data
    Instr
        (mod :: ModuleShape)
        (frame :: FrameShape)
        (labels :: [LResultType])
        (pcIn :: PcStack)
        (pcOut :: PcStack)
        (stackIn :: [LValType])
        (stackOut :: [LValType])
    where
    {- Constants. The level @lv@ is free: whoever builds the instruction says how secret the
       literal is, and the validator says 'Low. -}
    IConst :: forall lv t m f l pc pcs s. IsNum t -> HostType t -> Instr m f l (pc ': pcs) (pc ': pcs) s ((t ':~ Join pc lv) ': s)
    {- Numeric: both operands and the result share the value type, and the result is as secret
       as the more secret operand (and the pc). -}
    IAdd :: IsNum t -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join pc (Join lv lv')) ': s)
    ISub :: IsNum t -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join pc (Join lv lv')) ': s)
    IMul :: IsNum t -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join pc (Join lv lv')) ': s)
    IDiv :: NumWithSign t -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join pc (Join lv lv')) ': s)
    IRem :: IsInt t -> Signedness -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join pc (Join lv lv')) ': s)
    {- Comparison (consume two @t@, produce an i32 boolean as secret as the operands). @eqz@ is
       integer-only; @eq@/@ne@ have no signedness; the ordered comparisons carry a 'NumWithSign'
       (signed on ints only). -}
    IEqz :: IsInt t -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': s) (('I32 ':~ Join pc lv) ': s)
    IEq :: IsNum t -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ Join pc (Join lv lv')) ': s)
    INe :: IsNum t -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ Join pc (Join lv lv')) ': s)
    ILt :: NumWithSign t -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ Join pc (Join lv lv')) ': s)
    IGt :: NumWithSign t -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ Join pc (Join lv lv')) ': s)
    ILe :: NumWithSign t -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ Join pc (Join lv lv')) ': s)
    IGe :: NumWithSign t -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ Join pc (Join lv lv')) ': s)
    {- Integer bitwise / shift / count, and floating-point unary / binary (all same-type). -}
    IBitwise :: IsInt t -> BitwiseOp -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join pc (Join lv lv')) ': s)
    ICount :: IsInt t -> CountOp -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': s) ((t ':~ Join pc lv) ': s)
    IFloatUn :: IsFloat t -> FloatUnOp -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': s) ((t ':~ Join pc lv) ': s)
    IFloatBin :: IsFloat t -> FloatBinOp -> Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join pc (Join lv lv')) ': s)
    {- Conversions: pop one @from@, push one @to@ at the same level. The 'ConvertOp' is indexed
       by exactly those types, so the operand/result and the opcode cannot disagree. -}
    IConvert :: ConvertOp from to -> Instr m f l (pc ': pcs) (pc ': pcs) ((from ':~ lv) ': s) ((to ':~ Join pc lv) ': s)
    {- Memory size / grow and narrow load/store, SecWasm's rules. Every byte of memory has a
       level at run time ("Runtime.MemInst"). A load declares a level @ℓ@, the most secret bytes
       it expects to read: its result is as secret as the address, the pc and @ℓ@, and at run
       time it traps if a byte it reads is more secret than @ℓ@. A store declares the level its
       bytes get; the pc, the address and the value must all flow into it, and that is checked
       here, not at run time. @memory.grow@ is allowed only in a public context with a public
       argument, since the memory's size is public (new bytes are public), and @memory.size@
       yields a public value. -}
    IMemSize :: (ModuleMems m ~ (mem ': mems)) => Instr m f l (pc ': pcs) (pc ': pcs) s (('I32 ':~ pc) ': s)
    IMemGrow ::
        (ModuleMems m ~ (mem ': mems)) =>
        FlowsInto (Join pc lv) 'Low ->
        Instr m f l (pc ': pcs) (pc ': pcs) (('I32 ':~ lv) ': s) (('I32 ':~ pc) ': s)
    ILoadN ::
        (ModuleMems m ~ (mem ': mems)) =>
        Sing (level :: SecLevel) ->
        NarrowWidth t ->
        Signedness ->
        MemArg ->
        Instr m f l (pc ': pcs) (pc ': pcs) (('I32 ':~ la) ': s) ((t ':~ Join pc (Join la level)) ': s)
    IStoreN ::
        (ModuleMems m ~ (mem ': mems)) =>
        Sing (level :: SecLevel) ->
        FlowsInto (Join pc (Join la lv)) level ->
        NarrowWidth t ->
        MemArg ->
        Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': ('I32 ':~ la) ': s) s
    {- Bulk memory. Operands, top first: the byte count, then the source (an address, a fill
       value, or an offset into the segment), then the destination address. A segment is named
       by an 'Elem' into the module's data index space, so it exists. SecWasm covers
       WebAssembly 1.0, which has no bulk memory, so these rules are ours: nothing is checked
       statically, and every byte written takes the join of the pc and the three operands'
       levels (they decide whether and where bytes move), joined with the byte's own level for a
       copy and the fill value's for a fill; a data segment is public. That join is carried as a
       singleton so the interpreter can write it. -}
    IMemCopy ::
        (ModuleMems m ~ (mem ': mems)) =>
        Sing (Join pc (Join ln (Join lsrc ldst))) ->
        Instr m f l (pc ': pcs) (pc ': pcs) (('I32 ':~ ln) ': ('I32 ':~ lsrc) ': ('I32 ':~ ldst) ': s) s
    IMemFill ::
        (ModuleMems m ~ (mem ': mems)) =>
        Sing (Join pc (Join ln (Join lsrc ldst))) ->
        Instr m f l (pc ': pcs) (pc ': pcs) (('I32 ':~ ln) ': ('I32 ':~ lsrc) ': ('I32 ':~ ldst) ': s) s
    IMemInit ::
        (ModuleMems m ~ (mem ': mems)) =>
        Sing (Join pc (Join ln (Join lsrc ldst))) ->
        Elem 'DataShape (ModuleData m) ->
        Instr m f l (pc ': pcs) (pc ': pcs) (('I32 ':~ ln) ': ('I32 ':~ lsrc) ': ('I32 ':~ ldst) ': s) s
    IDataDrop :: Elem 'DataShape (ModuleData m) -> Instr m f l p p s s
    {- Stack management. @drop@ works on any value type; @select@ (0x1B) on numeric operands and
       keeps the first operand when the condition is non-zero, the second otherwise. Its result
       depends on all three operands, so it is as secret as the most secret of them. -}
    IDrop :: Instr m f l p p (t ': s) s
    ISelect ::
        IsNum t ->
        Instr m f l (pc ': pcs) (pc ': pcs) (('I32 ':~ lc) ': (t ':~ l1) ': (t ':~ l2) ': s) ((t ':~ Join pc (Join lc (Join l1 l2))) ': s)
    {- Locals (from the @frame@) & globals (from the @mod@). A variable has one level, declared
       with it and fixed for good. A read yields a value at that level (and the pc). A write
       takes two witnesses: the pc flows into the variable's level, and so does the value. -}
    ILocalGet :: LocalRef (t ':~ lv) (FrameLocals f) -> Instr m f l (pc ': pcs) (pc ': pcs) s ((t ':~ Join pc lv) ': s)
    ILocalSet ::
        FlowsInto pc lvar ->
        FlowsInto lv lvar ->
        LocalRef (t ':~ lvar) (FrameLocals f) ->
        Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': s) s
    ILocalTee ::
        FlowsInto pc lvar ->
        FlowsInto lv lvar ->
        LocalRef (t ':~ lvar) (FrameLocals f) ->
        Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': s) ((t ':~ lv) ': s)
    IGlobalGet :: Elem ('GlobalType mut (t ':~ lv)) (ModuleGlobals m) -> Instr m f l (pc ': pcs) (pc ': pcs) s ((t ':~ Join pc lv) ': s)
    IGlobalSet ::
        FlowsInto pc lvar ->
        FlowsInto lv lvar ->
        Elem ('GlobalType 'Mutable (t ':~ lvar)) (ModuleGlobals m) ->
        Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': s) s
    {- Memory (requires the module to declare a memory): the same rules as the narrow forms. -}
    ILoad ::
        (ModuleMems m ~ (mem ': mems)) =>
        Sing (level :: SecLevel) ->
        IsNum t ->
        MemArg ->
        Instr m f l (pc ': pcs) (pc ': pcs) (('I32 ':~ la) ': s) ((t ':~ Join pc (Join la level)) ': s)
    IStore ::
        (ModuleMems m ~ (mem ': mems)) =>
        Sing (level :: SecLevel) ->
        FlowsInto (Join pc (Join la lv)) level ->
        IsNum t ->
        MemArg ->
        Instr m f l (pc ': pcs) (pc ': pcs) ((t ':~ lv) ': ('I32 ':~ la) ': s) s
    {- Relabelling. SecWasm accepts a value of a lower level wherever a higher one is expected,
       by subtyping; an intrinsically-typed AST has no subtyping, so the validator inserts
       'IRelabel' where the policy or a call demands it. 'IDeclassify' goes the other way and is
       trusted: it is the escape hatch a policy may enable, and with it the guarantee becomes "no
       leak except through the declassifications". Neither does anything at run time. -}
    IRelabel :: FlowsInto lv lv' -> Instr m f l p p ((t ':~ lv) ': s) ((t ':~ lv') ': s)
    IDeclassify :: Instr m f l p p ((t ':~ lv) ': s) ((t ':~ lv') ': s)
    {- Calls. The 'Append' witness lets the interpreter peel the arguments off the stack. The
       arguments must be at exactly the levels the function declares, and the results come back
       at the levels it declares. A function body is checked at a public pc
       ('Syntax.Functions.FunctionBody'), so a call is only allowed where the pc is public:
       called from a secret branch, the callee's writes would reveal the branch. For an indirect
       call the table index decides which function runs, so its level counts as well.
       TODO(ifc P1): SecWasm gives a function type a third part, a bound on the pc it may be
       called from; the body is checked at that bound and the witness here becomes
       @FlowsInto pc bound@. The field is missing from 'Syntax.Types.FuncTypeOf' (the @ifc@
       branch has no labelled calls either).
       TODO(ifc P2): arguments at a lower level than declared should be accepted, by inserting
       'IRelabel' before the call; today the levels must match exactly. -}
    ICall ::
        FlowsInto pc 'Low ->
        Append ps s full ->
        Elem ('FuncType ps rs) (ModuleFuncs m) ->
        Instr m f l (pc ': pcs) (pc ': pcs) full (rs ++ s)
    {- Indirect calls: the callee is an entry of the module's table, checked at run time against
       the expected type (a trap if it differs); the module must declare a table. The expected
       type is labelled, so the run-time check compares the levels too. -}
    ICallIndirect ::
        (ModuleTables m ~ (table ': tables)) =>
        FlowsInto (Join pc lv) 'Low ->
        Append ps s full ->
        Sing ('FuncType ps rs) ->
        Instr m f l (pc ': pcs) (pc ': pcs) (('I32 ':~ lv) ': full) (rs ++ s)
    {- Structured control. Bodies are typed in isolation (@ps -> rs@) within the same frame,
       framed over a polymorphic @s@. A block/if label carries its results; a loop its params.
       A body starts with one more pc entry than its surroundings: the current pc for a block,
       the current pc joined with the condition's level for an @if@. When the body ends its own
       entry is dropped, and the instruction's @pcOut@ is what the body left of the entries
       below, which a branch inside may have raised. After an @if@ either arm may have run, so
       the two results are joined entry by entry.
       A loop's body can run again, so it must be checked at a pc that still holds when control
       comes back: the entry it starts at, @pcLoop@, is at least the current pc and at least
       the entry the body ends with. (The @ifc@ branch asks for the same as an annotation.)
       TODO(ifc P2): SecWasm also raises the levels of the values already on the stack of the
       blocks a branch leaves, which its proof uses. Neither the @ifc@ branch nor this does.
       TODO(ifc P2): the two arms of an @if@ must produce exactly the same labelled types.
       Accepting arms at different levels needs the relabelling instruction (see 'ICall'). -}
    IBlock ::
        Append ps s full ->
        Expr m f (rs ': l) (pc ': pc ': pcs) (pcBody ': pcs') ps rs ->
        Instr m f l (pc ': pcs) pcs' full (rs ++ s)
    ILoop ::
        FlowsInto pc pcLoop ->
        FlowsInto pcBody pcLoop ->
        Append ps s full ->
        Expr m f (ps ': l) (pcLoop ': pc ': pcs) (pcBody ': pcs') ps rs ->
        Instr m f l (pc ': pcs) pcs' full (rs ++ s)
    IIf ::
        Append ps s full ->
        Expr m f (rs ': l) (Join pc lv ': pc ': pcs) (pcThen ': pcsThen) ps rs ->
        Expr m f (rs ': l) (Join pc lv ': pc ': pcs) (pcElse ': pcsElse) ps rs ->
        Instr m f l (pc ': pcs) (JoinEach pcsThen pcsElse) (('I32 ':~ lv) ': full) (rs ++ s)
    {- Branches. The 'Append' witness gives the branch width; the output (and the stack below
       the operands) is otherwise free. The decision to branch is as secret as the pc, joined
       with the condition's level if there is one. The values carried must be at least that
       secret ('AllAtLeast'), and the pc entries of the blocks the branch may leave are raised
       by it ('BranchTarget'). @br_table@ and @return@ raise every entry, which is more than
       needed for @br_table@ when all its targets are near. -}
    IBr ::
        AllAtLeast pc rs ->
        Append rs s full ->
        BranchTarget pc rs labels (pc ': pcs) pcs' ->
        Instr m f labels (pc ': pcs) pcs' full anyOut
    IBrIf ::
        AllAtLeast (Join pc lv) rs ->
        Append rs s full ->
        BranchTarget (Join pc lv) rs labels (pc ': pcs) pcs' ->
        Instr m f labels (pc ': pcs) pcs' (('I32 ':~ lv) ': full) full
    IBrTable ::
        AllAtLeast (Join pc lv) rs ->
        Append rs s full ->
        [Elem rs labels] ->
        Elem rs labels ->
        Instr m f labels (pc ': pcs) (RaiseAll (Join pc lv) (pc ': pcs)) (('I32 ':~ lv) ': full) anyOut
    IReturn ::
        AllAtLeast pc (FrameReturn f) ->
        Append (FrameReturn f) s full ->
        Instr m f l (pc ': pcs) (RaiseAll pc (pc ': pcs)) full anyOut
    {- Inert. A trap ends the run, which an observer can see, so @unreachable@ under a secret pc
       reveals something. SecWasm accepts this (its guarantee only covers runs that finish), and
       so do we: no check here. -}
    INop :: Instr m f l p p s s
    IUnreachable :: Instr m f l p p s anyOut

{- | A typed instruction sequence (a WebAssembly expression): the output shape of each
  instruction is the input of the next. Same context indices as 'Instr'.
-}
data
    Expr
        (mod :: ModuleShape)
        (frame :: FrameShape)
        (labels :: [LResultType])
        (pcIn :: PcStack)
        (pcOut :: PcStack)
        (stackIn :: [LValType])
        (stackOut :: [LValType])
    where
    INil :: Expr m f l p p s s
    (:.) ::
        Instr m f l p1 p2 s1 s2 ->
        Expr m f l p2 p3 s2 s3 ->
        Expr m f l p1 p3 s1 s3

infixr 5 :.

{- | Ergonomic forms of the framed/branching instructions: they build the 'Append' witness
  from the prefix's singleton (via 'SingI'), so call sites with concrete stack shapes need
  not write it. (Only the forms actually used by hand-written examples are provided; add
  more as needed.)
-}
call ::
    forall ps rs s m f l pcs.
    SingI ps =>
    Elem ('FuncType ps rs) (ModuleFuncs m) -> Instr m f l ('Low ': pcs) ('Low ': pcs) (ps ++ s) (rs ++ s)
call = ICall LowFlowsAnywhere (appendFromSing @ps @s (sing @ps))

{- | Specialised forms for the common case of an empty-result block/loop and a branch to
  an empty-result label. With @rs ~ '[]@ fixed, @rs ++ s@ reduces to @s@, so these infer
  cleanly — no @++@ for GHC to invert and no type applications needed at call sites. The loop
  form is for a public pc, where its two flow witnesses are trivial.
-}
block_ :: Expr m f ('[] ': l) (pc ': pc ': pcs) (pcBody ': pcs') '[] '[] -> Instr m f l (pc ': pcs) pcs' s s
block_ = IBlock ANil

loop_ :: Expr m f ('[] ': l) ('Low ': 'Low ': pcs) ('Low ': pcs') '[] '[] -> Instr m f l ('Low ': pcs) pcs' s s
loop_ = ILoop LowFlowsAnywhere LowFlowsAnywhere ANil

br_ :: BranchTarget pc '[] labels (pc ': pcs) pcs' -> Instr m f labels (pc ': pcs) pcs' s anyOut
br_ = IBr NothingCarried ANil

brIf_ :: BranchTarget (Join pc lv) '[] labels (pc ': pcs) pcs' -> Instr m f labels (pc ': pcs) pcs' (('I32 ':~ lv) ': s) s
brIf_ = IBrIf NothingCarried ANil
