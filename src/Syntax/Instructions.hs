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

  Between them, @check@ names the premise of the instruction's rule that only the machine
  can decide, if it has one ('DynamicCheck'). The interpreter has to present evidence for
  it in order to step past the instruction, so a check that the rule demands cannot be
  left out of 'Runtime.Interpreter.step' by mistake: see 'Runtime.Obligation.CheckPassed'.

  Every type on the stack, in the frame and in a label is a /labelled/ value type
  (@t ':~ l@, from "Syntax.TypesIFC"): a value type together with a security level, 'Low for
  public data and 'High for secret data. So this one type tracks information flow as well as
  value types. The rule for computed values is that a result is as secret as the most secret
  operand it was computed from, which the signatures below write as @Join l l'@. The levels
  exist only in the types. At run time a value is a bare machine word, exactly as before.

  We follow SecWasm (see "Syntax.TypesIFC"), and the instructions are at three stages:

    * /Done/: the numeric, comparison, conversion and @select@ instructions have their final
      signatures.
    * /Placeholder/: a few instructions produce a value whose level nothing constrains yet (a
      constant, a load, @memory.size@). The signature leaves that level free, so whoever builds
      the instruction chooses it. The validator always chooses 'Low today.
    * /Missing check/: the instructions that write somewhere (@local.set@, @global.set@, the
      stores) or that transfer control (@if@, the branches, the calls) do not yet check that the
      flow is allowed. Each has a @TODO(ifc …)@ beside it that says what the final signature
      needs. @grep -rn 'TODO(ifc' src test@ lists them all; P0 is a decision to take first, P1
      is needed for a sound system, P2 for real modules, and P3 is polish.

  The largest missing piece is the /program counter label/, written @pc@ in the TODOs. It is
  the level of the decisions that led control to the current instruction. Inside
  @(if (secret) …)@ the pc is 'High, and a write to a public variable there would reveal the
  secret, so every write has to check the pc as well as the value. The pc is not an index of
  this type yet (see the TODO on 'IBlock').
-}

-- TODO: organize instructions into groups: data, mem, ctrl and admin
-- TODO: [ValType] into ValStackType and remove ResultType
data
    Instr
        (mod :: ModuleShape)
        (frame :: FrameShape)
        (labels :: [LResultType])
        (check :: DynamicCheck)
        (stackIn :: [LValType])
        (stackOut :: [LValType])
    where
    {- Constants.
       TODO(ifc P2): the level of a constant is free (a placeholder). A literal is public, so
       the final signature is @t ':~ pc@ once the pc exists: public, but no less secret than the
       context that pushed it. -}
    IConst :: IsNum t -> HostType t -> Instr m f l 'NoDynamicCheck s ((t ':~ lv) ': s)
    {- Numeric: both operands and the result share the value type, and the result is as secret
       as the more secret operand. Final. -}
    IAdd :: IsNum t -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join lv lv') ': s)
    ISub :: IsNum t -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join lv lv') ': s)
    IMul :: IsNum t -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join lv lv') ': s)
    IDiv :: NumWithSign t -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join lv lv') ': s)
    IRem :: IsInt t -> Signedness -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join lv lv') ': s)
    {- Comparison (consume two @t@, produce an i32 boolean as secret as the operands). @eqz@ is
       integer-only; @eq@/@ne@ have no signedness; the ordered comparisons carry a 'NumWithSign'
       (signed on ints only). Final. -}
    IEqz :: IsInt t -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': s) (('I32 ':~ lv) ': s)
    IEq :: IsNum t -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ Join lv lv') ': s)
    INe :: IsNum t -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ Join lv lv') ': s)
    ILt :: NumWithSign t -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ Join lv lv') ': s)
    IGt :: NumWithSign t -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ Join lv lv') ': s)
    ILe :: NumWithSign t -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ Join lv lv') ': s)
    IGe :: NumWithSign t -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ Join lv lv') ': s)
    {- Integer bitwise / shift / count, and floating-point unary / binary (all same-type). A
       binary one joins the levels; a unary one keeps the operand's level. Final. -}
    IBitwise :: IsInt t -> BitwiseOp -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join lv lv') ': s)
    ICount :: IsInt t -> CountOp -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': s) ((t ':~ lv) ': s)
    IFloatUn :: IsFloat t -> FloatUnOp -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': s) ((t ':~ lv) ': s)
    IFloatBin :: IsFloat t -> FloatBinOp -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ Join lv lv') ': s)
    {- Conversions: pop one @from@, push one @to@ at the same level. The 'ConvertOp' is indexed
       by exactly those types, so the operand/result and the opcode cannot disagree. Final. -}
    IConvert :: ConvertOp from to -> Instr m f l 'NoDynamicCheck ((from ':~ lv) ': s) ((to ':~ lv) ': s)
    {- Memory size / grow and narrow load/store. SecWasm keeps a level for every byte of
       memory at run time, and gives each load and store a level @ℓ@ written in the
       instruction (the @Sing lm@ the loads carry):
         * A load at address level @la@ yields a value at @Join la ℓ@. At run time it checks
           that every byte it reads is at most @ℓ@, and traps otherwise; that is the
           @'BytesBelow lm@ premise in its type, which the interpreter discharges through
           'Runtime.MemInst.loadChecked'. Every load is elaborated at 'Low until a policy
           section says otherwise.
           TODO(ifc P0): the result should be @Join la (Join ℓ pc)@ once the pc index exists.
       TODO(ifc P1): memory levels are read but never written yet, so the level of
       @memory.size@ is free (a placeholder), and a store checks nothing:
         * A store of a value at @lv@ to an address at @la@ is allowed when
           @Join pc (Join la lv)@ flows into @ℓ@, which is a static check: the final signature
           takes a @Sing ℓ@ and a 'FlowsInto' witness. At run time it marks the bytes it writes
           with @ℓ@.
         * @memory.grow@ is allowed only in a public context with a public argument, and the
           new bytes are public. So its final signature fixes both levels, and the pc, to 'Low,
           and @memory.size@ yields a public value.
       The run-time half is described in "Runtime.MemInst". -}
    IMemSize :: (ModuleMems m ~ (mem ': mems)) => Instr m f l 'NoDynamicCheck s (('I32 ':~ lv) ': s)
    IMemGrow :: (ModuleMems m ~ (mem ': mems)) => Instr m f l 'NoDynamicCheck (('I32 ':~ lv) ': s) (('I32 ':~ lv) ': s)
    ILoadN ::
        (ModuleMems m ~ (mem ': mems)) =>
        Sing lm ->
        NarrowWidth t ->
        Signedness ->
        MemArg ->
        Instr m f l ('BytesBelow lm) (('I32 ':~ la) ': s) ((t ':~ Join la lm) ': s)
    IStoreN ::
        (ModuleMems m ~ (mem ': mems)) =>
        NarrowWidth t ->
        MemArg ->
        Instr m f l 'NoDynamicCheck ((t ':~ lv) ': ('I32 ':~ la) ': s) s
    {- Bulk memory. Operands, top first: the byte count, then the source (an address, a fill
       value, or an offset into the segment), then the destination address. A segment is named
       by an 'Elem' into the module's data index space, so it exists.
       TODO(ifc P2): SecWasm covers WebAssembly 1.0, which has no bulk memory, so these rules
       are ours to write. With a level per byte they need no static check beyond the pc: a
       copied byte keeps the level of its source joined with the levels of the three operands
       and the pc, a filled byte takes the level of the fill value joined with the same, and an
       initialised byte (a data segment is public) takes the operands' levels and the pc. -}
    IMemCopy :: (ModuleMems m ~ (mem ': mems)) => Instr m f l 'NoDynamicCheck (('I32 ':~ ln) ': ('I32 ':~ lsrc) ': ('I32 ':~ ldst) ': s) s
    IMemFill :: (ModuleMems m ~ (mem ': mems)) => Instr m f l 'NoDynamicCheck (('I32 ':~ ln) ': ('I32 ':~ lsrc) ': ('I32 ':~ ldst) ': s) s
    IMemInit ::
        (ModuleMems m ~ (mem ': mems)) =>
        Elem 'DataShape (ModuleData m) ->
        Instr m f l 'NoDynamicCheck (('I32 ':~ ln) ': ('I32 ':~ lsrc) ': ('I32 ':~ ldst) ': s) s
    IDataDrop :: Elem 'DataShape (ModuleData m) -> Instr m f l 'NoDynamicCheck s s
    {- Stack management. @drop@ works on any value type; @select@ (0x1B) on numeric operands and
       keeps the first operand when the condition is non-zero, the second otherwise. Its result
       depends on all three operands, so it is as secret as the most secret of them. Final. -}
    IDrop :: Instr m f l 'NoDynamicCheck (t ': s) s
    ISelect ::
        IsNum t ->
        Instr m f l 'NoDynamicCheck (('I32 ':~ lc) ': (t ':~ l1) ': (t ':~ l2) ': s) ((t ':~ Join lc (Join l1 l2)) ': s)
    {- Locals (from the @frame@) & globals (from the @mod@). A local or global has one level,
       declared with it and fixed for good; a read yields a value at that level.
       TODO(ifc P1): the writes demand a value at exactly the variable's level. They should
       accept any value that may flow into it: for a variable at @l@ and a value at @lv@, take a
       @FlowsInto (Join pc lv) l@ witness. The pc is part of the check because a write inside a
       secret branch reveals the branch condition even when the value written is public. -}
    ILocalGet :: LocalRef (t ':~ lv) (FrameLocals f) -> Instr m f l 'NoDynamicCheck s ((t ':~ lv) ': s)
    ILocalSet :: LocalRef (t ':~ lv) (FrameLocals f) -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': s) s
    ILocalTee :: LocalRef (t ':~ lv) (FrameLocals f) -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': s) ((t ':~ lv) ': s)
    IGlobalGet :: Elem ('GlobalType mut (t ':~ lv)) (ModuleGlobals m) -> Instr m f l 'NoDynamicCheck s ((t ':~ lv) ': s)
    IGlobalSet :: Elem ('GlobalType 'Mutable (t ':~ lv)) (ModuleGlobals m) -> Instr m f l 'NoDynamicCheck ((t ':~ lv) ': s) s
    {- Memory (requires the module to declare a memory). The comment on the narrow forms
       above covers these as well. -}
    ILoad ::
        (ModuleMems m ~ (mem ': mems)) =>
        Sing lm ->
        IsNum t ->
        MemArg ->
        Instr m f l ('BytesBelow lm) (('I32 ':~ la) ': s) ((t ':~ Join la lm) ': s)
    IStore ::
        (ModuleMems m ~ (mem ': mems)) =>
        IsNum t ->
        MemArg ->
        Instr m f l 'NoDynamicCheck ((t ':~ lv) ': ('I32 ':~ la) ': s) s
    {- Calls. The 'Append' witness lets the interpreter peel the arguments off the stack. The
       arguments must be at exactly the levels the function declares, and the results come back
       at the levels it declares.
       TODO(ifc P1): a call inside a secret branch runs the whole callee in a secret context.
       SecWasm therefore gives a function type a third part, a bound on the pc it may be called
       from, and the callee's body is checked under that bound. The final signature takes a
       @FlowsInto pc bound@ witness; for an indirect call the table index decides which function
       runs, so its level joins the pc in that check. The bound is missing from
       'Syntax.Types.FuncTypeOf'.
       TODO(ifc P2): arguments at a lower level than declared should be accepted. SecWasm does
       this by subtyping. An intrinsically-typed AST has no subtyping, so add an instruction that
       raises the level of the value on top of the stack (it takes a 'FlowsInto' witness and
       does nothing at run time), and have the validator insert it where needed. -}
    ICall ::
        Append ps s full ->
        Elem ('FuncType ps rs) (ModuleFuncs m) ->
        Instr m f l 'NoDynamicCheck full (rs ++ s)
    {- Indirect calls: the callee is an entry of the module's table, checked at run time against
       the expected type (a trap if it differs); the module must declare a table. The expected
       type is labelled, so the run-time check compares the levels too. -}
    ICallIndirect ::
        (ModuleTables m ~ (table ': tables)) =>
        Append ps s full ->
        Sing ('FuncType ps rs) ->
        Instr m f l 'NoDynamicCheck (('I32 ':~ lv) ': full) (rs ++ s)
    {- Structured control. Bodies are typed in isolation (@ps -> rs@) within the same frame,
       framed over a polymorphic @s@. A block/if label carries its results; a loop its params.
       TODO(ifc P0): nothing tracks the pc, so a program can leak through control flow: after
       @(if (secret) (then (local.set $public 1)))@ the public local reveals the secret. The
       plan, in the order to do it:
         1. Add a @pc :: SecLevel@ index to 'Instr' and 'Expr', and a pc to every label (the
            level its block's body runs at).
         2. 'IIf' checks its two bodies at @Join pc lv@, where @lv@ is the condition's level.
         3. A block's results must be at least as secret as the pc of its body, because which
            values come out depends on the decisions taken inside.
         4. A branch is allowed only to a label whose pc is at least @Join pc lv@ (just @pc@ for
            an unconditional branch), and 'IReturn' only when the function's bound is.
         5. The validator picks each block's pc before checking its body: the pc of the
            enclosing block, joined with the level of every condition that can make control
            leave the block early. With two levels this takes at most two passes.
       SecWasm is more permissive here: it lets the pc rise part-way through a block, at the
       branch. That needs the label context to change from one instruction to the next, which
       this type does not support, so we start with one pc per block. -}
    IBlock ::
        Append ps s full ->
        Expr m f (rs ': l) ps rs ->
        Instr m f l 'NoDynamicCheck full (rs ++ s)
    ILoop ::
        Append ps s full ->
        Expr m f (ps ': l) ps rs ->
        Instr m f l 'NoDynamicCheck full (rs ++ s)
    IIf ::
        Append ps s full ->
        Expr m f (rs ': l) ps rs ->
        Expr m f (rs ': l) ps rs ->
        Instr m f l 'NoDynamicCheck (('I32 ':~ lv) ': full) (rs ++ s)
    {- Branches. The witness gives the branch width; the output (and the stack below the
       operands) is otherwise free. The condition's level is ignored for now: see the
       TODO(ifc P0) on 'IBlock', step 4. -}
    IBr :: Append rs s full -> Elem rs labels -> Instr m f labels 'NoDynamicCheck full anyOut
    IBrIf :: Append rs s full -> Elem rs labels -> Instr m f labels 'NoDynamicCheck (('I32 ':~ lv) ': full) full
    IBrTable ::
        Append rs s full ->
        [Elem rs labels] ->
        Elem rs labels ->
        Instr m f labels 'NoDynamicCheck (('I32 ':~ lv) ': full) anyOut
    IReturn :: Append (FrameReturn f) s full -> Instr m f l 'NoDynamicCheck full anyOut
    {- Inert. A trap ends the run, which an observer can see, so @unreachable@ under a secret pc
       reveals something. SecWasm accepts this (its guarantee only covers runs that finish), and
       so do we: no check here. -}
    INop :: Instr m f l 'NoDynamicCheck s s
    IUnreachable :: Instr m f l 'NoDynamicCheck s anyOut

{- | A typed instruction sequence (a WebAssembly expression): the output shape of each
  instruction is the input of the next. Same context indices as 'Instr'.
-}
data
    Expr
        (mod :: ModuleShape)
        (frame :: FrameShape)
        (labels :: [LResultType])
        (stackIn :: [LValType])
        (stackOut :: [LValType])
    where
    INil :: Expr m f l s s
    (:.) ::
        Instr m f l check s1 s2 ->
        Expr m f l s2 s3 ->
        Expr m f l s1 s3

infixr 5 :.

{- | Ergonomic forms of the framed/branching instructions: they build the 'Append' witness
  from the prefix's singleton (via 'SingI'), so call sites with concrete stack shapes need
  not write it. (Only the forms actually used by hand-written examples are provided; add
  more as needed.)
-}
call ::
    forall ps rs s m f l.
    SingI ps =>
    Elem ('FuncType ps rs) (ModuleFuncs m) -> Instr m f l 'NoDynamicCheck (ps ++ s) (rs ++ s)
call = ICall (appendFromSing @ps @s (sing @ps))

{- | Specialised forms for the common case of an empty-result block/loop and a branch to
  an empty-result label. With @rs ~ '[]@ fixed, @rs ++ s@ reduces to @s@, so these infer
  cleanly — no @++@ for GHC to invert and no type applications needed at call sites.
-}
block_ :: Expr m f ('[] ': l) '[] '[] -> Instr m f l 'NoDynamicCheck s s
block_ = IBlock ANil

loop_ :: Expr m f ('[] ': l) '[] '[] -> Instr m f l 'NoDynamicCheck s s
loop_ = ILoop ANil

br_ :: Elem '[] labels -> Instr m f labels 'NoDynamicCheck s anyOut
br_ = IBr ANil

brIf_ :: Elem '[] labels -> Instr m f labels 'NoDynamicCheck (('I32 ':~ lv) ': s) s
brIf_ = IBrIf ANil
