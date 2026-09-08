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
import Validation.Shape (
    Append (..),
    Elem,
    FrameLocals,
    FrameReturn,
    FrameShape,
    ModuleFuncs,
    ModuleGlobals,
    ModuleMems,
    ModuleShape,
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
    {- CallIndirect :: TypeIdx -> RawInstr -}

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
-}
data
    Instr
        (mod :: ModuleShape)
        (frame :: FrameShape)
        (labels :: [ResultType])
        (stackIn :: [ValType])
        (stackOut :: [ValType])
    where
    {- Constants -}
    IConst :: IsNum t -> HostType t -> Instr m f l s (t ': s)
    {- Numeric (both operands and the result share the type) -}
    IAdd :: IsNum t -> Instr m f l (t ': t ': s) (t ': s)
    ISub :: IsNum t -> Instr m f l (t ': t ': s) (t ': s)
    IMul :: IsNum t -> Instr m f l (t ': t ': s) (t ': s)
    IDiv :: NumWithSign t -> Instr m f l (t ': t ': s) (t ': s)
    IRem :: IsInt t -> Signedness -> Instr m f l (t ': t ': s) (t ': s)
    {- Comparison (consume two @t@, produce an i32 boolean). @eqz@ is integer-only; @eq@/@ne@
       have no signedness; the ordered comparisons carry a 'NumWithSign' (signed on ints only). -}
    IEqz :: IsInt t -> Instr m f l (t ': s) ('I32 ': s)
    IEq :: IsNum t -> Instr m f l (t ': t ': s) ('I32 ': s)
    INe :: IsNum t -> Instr m f l (t ': t ': s) ('I32 ': s)
    ILt :: NumWithSign t -> Instr m f l (t ': t ': s) ('I32 ': s)
    IGt :: NumWithSign t -> Instr m f l (t ': t ': s) ('I32 ': s)
    ILe :: NumWithSign t -> Instr m f l (t ': t ': s) ('I32 ': s)
    IGe :: NumWithSign t -> Instr m f l (t ': t ': s) ('I32 ': s)
    {- Integer bitwise / shift / count, and floating-point unary / binary (all same-type) -}
    IBitwise :: IsInt t -> BitwiseOp -> Instr m f l (t ': t ': s) (t ': s)
    ICount :: IsInt t -> CountOp -> Instr m f l (t ': s) (t ': s)
    IFloatUn :: IsFloat t -> FloatUnOp -> Instr m f l (t ': s) (t ': s)
    IFloatBin :: IsFloat t -> FloatBinOp -> Instr m f l (t ': t ': s) (t ': s)
    {- Conversions: pop one @from@, push one @to@. The 'ConvertOp' is indexed by exactly those
       types, so the operand/result and the opcode cannot disagree. -}
    IConvert :: ConvertOp from to -> Instr m f l (from ': s) (to ': s)
    {- Memory size / grow and narrow load/store -}
    IMemSize :: (ModuleMems m ~ (mem ': mems)) => Instr m f l s ('I32 ': s)
    IMemGrow :: (ModuleMems m ~ (mem ': mems)) => Instr m f l ('I32 ': s) ('I32 ': s)
    ILoadN ::
        (ModuleMems m ~ (mem ': mems)) =>
        NarrowWidth t ->
        Signedness ->
        MemArg ->
        Instr m f l ('I32 ': s) (t ': s)
    IStoreN ::
        (ModuleMems m ~ (mem ': mems)) =>
        NarrowWidth t ->
        MemArg ->
        Instr m f l (t ': 'I32 ': s) s
    {- Stack management. @drop@ works on any value type; @select@ (0x1B) on numeric operands. -}
    IDrop :: Instr m f l (t ': s) s
    ISelect :: IsNum t -> Instr m f l ('I32 ': t ': t ': s) (t ': s)
    {- Locals (from the @frame@) & globals (from the @mod@) -}
    ILocalGet :: Elem t (FrameLocals f) -> Instr m f l s (t ': s)
    ILocalSet :: Elem t (FrameLocals f) -> Instr m f l (t ': s) s
    ILocalTee :: Elem t (FrameLocals f) -> Instr m f l (t ': s) (t ': s)
    IGlobalGet :: Elem ('GlobalType mut t) (ModuleGlobals m) -> Instr m f l s (t ': s)
    IGlobalSet :: Elem ('GlobalType 'Mutable t) (ModuleGlobals m) -> Instr m f l (t ': s) s
    {- Memory (requires the module to declare a memory) -}
    ILoad ::
        (ModuleMems m ~ (mem ': mems)) =>
        IsNum t ->
        MemArg ->
        Instr m f l ('I32 ': s) (t ': s)
    IStore ::
        (ModuleMems m ~ (mem ': mems)) =>
        IsNum t ->
        MemArg ->
        Instr m f l (t ': 'I32 ': s) s
    {- Calls. The 'Append' witness lets the interpreter peel the arguments off the stack. -}
    ICall ::
        Append ps s full ->
        Elem ('FuncType ps rs) (ModuleFuncs m) ->
        Instr m f l full (rs ++ s)
    {- Structured control. Bodies are typed in isolation (@ps -> rs@) within the same frame,
       framed over a polymorphic @s@. A block/if label carries its results; a loop its params. -}
    IBlock ::
        Append ps s full ->
        Expr m f (rs ': l) ps rs ->
        Instr m f l full (rs ++ s)
    ILoop ::
        Append ps s full ->
        Expr m f (ps ': l) ps rs ->
        Instr m f l full (rs ++ s)
    IIf ::
        Append ps s full ->
        Expr m f (rs ': l) ps rs ->
        Expr m f (rs ': l) ps rs ->
        Instr m f l ('I32 ': full) (rs ++ s)
    {- Branches. The witness gives the branch width; the output (and the stack below the
       operands) is otherwise free. -}
    IBr :: Append rs s full -> Elem rs labels -> Instr m f labels full anyOut
    IBrIf :: Append rs s full -> Elem rs labels -> Instr m f labels ('I32 ': full) full
    IBrTable ::
        Append rs s full ->
        [Elem rs labels] ->
        Elem rs labels ->
        Instr m f labels ('I32 ': full) anyOut
    IReturn :: Append (FrameReturn f) s full -> Instr m f l full anyOut
    {- Inert -}
    INop :: Instr m f l s s
    IUnreachable :: Instr m f l s anyOut

{- | A typed instruction sequence (a WebAssembly expression): the output shape of each
  instruction is the input of the next. Same context indices as 'Instr'.
-}
data
    Expr
        (mod :: ModuleShape)
        (frame :: FrameShape)
        (labels :: [ResultType])
        (stackIn :: [ValType])
        (stackOut :: [ValType])
    where
    INil :: Expr m f l s s
    (:.) ::
        Instr m f l s1 s2 ->
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
    Elem ('FuncType ps rs) (ModuleFuncs m) -> Instr m f l (ps ++ s) (rs ++ s)
call = ICall (appendFromSing @ps @s (sing @ps))

{- | Specialised forms for the common case of an empty-result block/loop and a branch to
  an empty-result label. With @rs ~ '[]@ fixed, @rs ++ s@ reduces to @s@, so these infer
  cleanly — no @++@ for GHC to invert and no type applications needed at call sites.
-}
block_ :: Expr m f ('[] ': l) '[] '[] -> Instr m f l s s
block_ = IBlock ANil

loop_ :: Expr m f ('[] ': l) '[] '[] -> Instr m f l s s
loop_ = ILoop ANil

br_ :: Elem '[] labels -> Instr m f labels s anyOut
br_ = IBr ANil

brIf_ :: Elem '[] labels -> Instr m f labels ('I32 ': s) s
brIf_ = IBrIf ANil
