{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | WebAssembly instructions, in their two forms, side by side:
--
--   * 'RawInstr' — the untyped, unvalidated tree the decoder produces (elaboration's input).
--   * 'Instr' — the intrinsically-typed form, indexed by the value-stack shapes, locals,
--     labels and module shape it runs within, so only well-typed programs are representable.
--     'Expr' is a sequence of them.
--
-- The @Raw@ prefix is the only thing distinguishing the two.
module Syntax.Instructions where

import Syntax.Immediates
import Syntax.Indices
import Syntax.Types
import Validation.Shape (Append (..), Elem, KnownAppend (..), ModuleFuncs, ModuleGlobals,
                       ModuleMems, ModuleShape, type (++))

-- | The untyped WebAssembly instruction AST: the raw, unvalidated representation produced by
--   the decoder. Numeric instructions carry a @SNumType t@ recording the type they operate
--   on; integer operations whose meaning depends on signedness carry a 'Signedness'.
data RawInstr where
    {- *** Control *** -}
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

    {- *** Locals & globals *** -}
    LocalGet :: LocalIdx -> RawInstr
    LocalSet :: LocalIdx -> RawInstr
    LocalTee :: LocalIdx -> RawInstr
    GlobalGet :: GlobalIdx -> RawInstr
    GlobalSet :: GlobalIdx -> RawInstr

    {- *** Memory *** -}
    Load :: SNumType t -> MemArg -> RawInstr
    Store :: SNumType t -> MemArg -> RawInstr
    -- narrow load/store: @width@ is the storage width in bytes (1, 2 or 4); loads also
    -- carry a 'Signedness' for sign/zero extension.
    LoadN :: SNumType t -> Int -> Signedness -> MemArg -> RawInstr
    StoreN :: SNumType t -> Int -> MemArg -> RawInstr
    MemorySize :: RawInstr
    MemoryGrow :: RawInstr

    {- *** Constants *** -}
    Const :: SNumType t -> ImmediateHostType t -> RawInstr

    {- *** Numeric *** -}
    Add :: SNumType t -> RawInstr
    Sub :: SNumType t -> RawInstr
    Mul :: SNumType t -> RawInstr
    Div :: SNumType t -> Signedness -> RawInstr
    Rem :: SNumType t -> Signedness -> RawInstr

    {- *** Integer bitwise / shift / count *** -}
    And :: SNumType t -> RawInstr
    Or :: SNumType t -> RawInstr
    Xor :: SNumType t -> RawInstr
    Shl :: SNumType t -> RawInstr
    Shr :: SNumType t -> Signedness -> RawInstr
    Rotl :: SNumType t -> RawInstr
    Rotr :: SNumType t -> RawInstr
    Clz :: SNumType t -> RawInstr
    Ctz :: SNumType t -> RawInstr
    Popcnt :: SNumType t -> RawInstr

    {- *** Floating-point unary / binary *** -}
    Abs :: SNumType t -> RawInstr
    Neg :: SNumType t -> RawInstr
    Sqrt :: SNumType t -> RawInstr
    Ceil :: SNumType t -> RawInstr
    Floor :: SNumType t -> RawInstr
    FloatTrunc :: SNumType t -> RawInstr
    Nearest :: SNumType t -> RawInstr
    Min :: SNumType t -> RawInstr
    Max :: SNumType t -> RawInstr
    Copysign :: SNumType t -> RawInstr

    {- *** Conversions *** -}
    Convert :: ConvertOp -> RawInstr

    {- *** Comparison *** -}
    Eqz :: SNumType t -> RawInstr
    Eq :: SNumType t -> RawInstr
    Ne :: SNumType t -> RawInstr
    Lt :: SNumType t -> Signedness -> RawInstr
    Gt :: SNumType t -> Signedness -> RawInstr
    Le :: SNumType t -> Signedness -> RawInstr
    Ge :: SNumType t -> Signedness -> RawInstr

    {- *** Stack management *** -}
    Drop :: RawInstr
    Select :: RawInstr

-- | The fixed-opcode type conversions. Each names its source and target concretely.
data ConvertOp
    = I32WrapI64
    | I64ExtendI32 Signedness
    | I32TruncF32 Signedness | I32TruncF64 Signedness
    | I64TruncF32 Signedness | I64TruncF64 Signedness
    | F32ConvertI32 Signedness | F32ConvertI64 Signedness
    | F64ConvertI32 Signedness | F64ConvertI64 Signedness
    | F32DemoteF64 | F64PromoteF32
    | I32ReinterpretF32 | F32ReinterpretI32
    | I64ReinterpretF64 | F64ReinterpretI64
    | I32Extend8S | I32Extend16S
    | I64Extend8S | I64Extend16S | I64Extend32S
    deriving (Eq, Show)
-- | Same-type operation groups, so the GADT (and interpreter) stay compact.
data BitwiseOp  = BwAnd | BwOr | BwXor | BwShl | BwShr Signedness | BwRotl | BwRotr
    deriving (Eq, Show)
data CountOp    = OpClz | OpCtz | OpPopcnt deriving (Eq, Show)
data FloatUnOp  = FAbs | FNeg | FSqrt | FCeil | FFloor | FTrunc | FNearest deriving (Eq, Show)
data FloatBinOp = FMin | FMax | FCopysign deriving (Eq, Show)

data Instr (shape    :: ModuleShape)
           (ret    :: [ValType])
           (locals :: [ValType])
           (labels :: [[ValType]])
           (si     :: [ValType])
           (so     :: [ValType])
  where
    {- Constants -}
    IConst :: SNumType t -> ImmediateHostType t -> Instr shape ret l lbl s ('Num t ': s)

    {- Numeric (both operands and the result share the type) -}
    IAdd :: SNumType t -> Instr shape ret l lbl ('Num t ': 'Num t ': s) ('Num t ': s)
    ISub :: SNumType t -> Instr shape ret l lbl ('Num t ': 'Num t ': s) ('Num t ': s)
    IMul :: SNumType t -> Instr shape ret l lbl ('Num t ': 'Num t ': s) ('Num t ': s)
    IDiv :: SNumType t -> Signedness -> Instr shape ret l lbl ('Num t ': 'Num t ': s) ('Num t ': s)
    IRem :: IsInt t -> Signedness -> Instr shape ret l lbl ('Num t ': 'Num t ': s) ('Num t ': s)

    {- Comparison (consume two @t@, produce an i32 boolean) -}
    IEqz :: SNumType t -> Instr shape ret l lbl ('Num t ': s) ('Num 'I32 ': s)
    IEq  :: SNumType t -> Instr shape ret l lbl ('Num t ': 'Num t ': s) ('Num 'I32 ': s)
    INe  :: SNumType t -> Instr shape ret l lbl ('Num t ': 'Num t ': s) ('Num 'I32 ': s)
    ILt  :: SNumType t -> Signedness -> Instr shape ret l lbl ('Num t ': 'Num t ': s) ('Num 'I32 ': s)
    IGt  :: SNumType t -> Signedness -> Instr shape ret l lbl ('Num t ': 'Num t ': s) ('Num 'I32 ': s)
    ILe  :: SNumType t -> Signedness -> Instr shape ret l lbl ('Num t ': 'Num t ': s) ('Num 'I32 ': s)
    IGe  :: SNumType t -> Signedness -> Instr shape ret l lbl ('Num t ': 'Num t ': s) ('Num 'I32 ': s)

    {- Integer bitwise / shift / count, and floating-point unary / binary (all same-type) -}
    IBitwise  :: IsInt t -> BitwiseOp -> Instr shape ret l lbl ('Num t ': 'Num t ': s) ('Num t ': s)
    ICount    :: IsInt t -> CountOp   -> Instr shape ret l lbl ('Num t ': s) ('Num t ': s)
    IFloatUn  :: IsFloat t -> FloatUnOp -> Instr shape ret l lbl ('Num t ': s) ('Num t ': s)
    IFloatBin :: IsFloat t -> FloatBinOp -> Instr shape ret l lbl ('Num t ': 'Num t ': s) ('Num t ': s)

    {- Conversions: pop one @from@, push one @to@ (the 'ConvertOp' is the term-level tag). -}
    IConvert :: SNumType from -> SNumType to -> ConvertOp
             -> Instr shape ret l lbl ('Num from ': s) ('Num to ': s)

    {- Memory size / grow and narrow load/store -}
    IMemSize :: (ModuleMems shape ~ (m ': ms)) => Instr shape ret l lbl s ('Num 'I32 ': s)
    IMemGrow :: (ModuleMems shape ~ (m ': ms)) => Instr shape ret l lbl ('Num 'I32 ': s) ('Num 'I32 ': s)
    ILoadN   :: (ModuleMems shape ~ (m ': ms)) => IsInt t -> Int -> Signedness -> MemArg
             -> Instr shape ret l lbl ('Num 'I32 ': s) ('Num t ': s)
    IStoreN  :: (ModuleMems shape ~ (m ': ms)) => IsInt t -> Int -> MemArg
             -> Instr shape ret l lbl ('Num t ': 'Num 'I32 ': s) s

    {- Stack management -}
    IDrop   :: Instr shape ret l lbl (t ': s) s
    ISelect :: Instr shape ret l lbl ('Num 'I32 ': t ': t ': s) (t ': s)

    {- Locals & globals -}
    ILocalGet :: Elem t locals -> Instr shape ret locals lbl s (t ': s)
    ILocalSet :: Elem t locals -> Instr shape ret locals lbl (t ': s) s
    ILocalTee :: Elem t locals -> Instr shape ret locals lbl (t ': s) (t ': s)
    IGlobalGet :: Elem ('GlobalType mut t) (ModuleGlobals shape) -> Instr shape ret l lbl s (t ': s)
    IGlobalSet :: Elem ('GlobalType 'Mutable t) (ModuleGlobals shape) -> Instr shape ret l lbl (t ': s) s

    {- Memory (requires the module to declare a memory) -}
    ILoad  :: (ModuleMems shape ~ (m ': ms)) => SNumType t -> MemArg
           -> Instr shape ret l lbl ('Num 'I32 ': s) ('Num t ': s)
    IStore :: (ModuleMems shape ~ (m ': ms)) => SNumType t -> MemArg
           -> Instr shape ret l lbl ('Num t ': 'Num 'I32 ': s) s

    {- Calls. The 'Append' witness lets the interpreter peel the arguments off the stack. -}
    ICall :: Append ps s full -> Elem ('FuncType ps rs) (ModuleFuncs shape)
          -> Instr shape ret l lbl full (rs ++ s)

    {- Structured control. Bodies are typed in isolation (@ps -> rs@), framed over a
       polymorphic @s@. A block/if label carries its results; a loop label its params. -}
    IBlock :: Append ps s full
           -> Expr shape ret l (rs ': lbl) ps rs
           -> Instr shape ret l lbl full (rs ++ s)
    ILoop  :: Append ps s full
           -> Expr shape ret l (ps ': lbl) ps rs
           -> Instr shape ret l lbl full (rs ++ s)
    IIf    :: Append ps s full
           -> Expr shape ret l (rs ': lbl) ps rs
           -> Expr shape ret l (rs ': lbl) ps rs
           -> Instr shape ret l lbl ('Num 'I32 ': full) (rs ++ s)

    {- Branches. The witness gives the branch width; the output (and the stack below the
       operands) is otherwise free. -}
    IBr      :: Append rs s full -> Elem rs labels -> Instr shape ret l labels full anyOut
    IBrIf    :: Append rs s full -> Elem rs labels -> Instr shape ret l labels ('Num 'I32 ': full) full
    IBrTable :: Append rs s full -> [Elem rs labels] -> Elem rs labels
             -> Instr shape ret l labels ('Num 'I32 ': full) anyOut
    IReturn  :: Append ret s full -> Instr shape ret l lbl full anyOut

    {- Inert -}
    INop         :: Instr shape ret l lbl s s
    IUnreachable :: Instr shape ret l lbl s anyOut

-- | A typed instruction sequence: the output shape of each instruction is the input of
--   the next.
data Expr (shape    :: ModuleShape)
              (ret    :: [ValType])
              (locals :: [ValType])
              (labels :: [[ValType]])
              (si     :: [ValType])
              (so     :: [ValType])
  where
    INil :: Expr shape ret l lbl s s
    (:.) :: Instr shape ret l lbl s1 s2
         -> Expr shape ret l lbl s2 s3
         -> Expr shape ret l lbl s1 s3

infixr 5 :.

-- | Ergonomic forms of the framed/branching instructions: they fill the 'Append' witness
--   from 'KnownAppend', so call sites with concrete stack shapes need not write it. Each
--   pins the witness's suffix with a type application so the result type is unambiguous.

block :: forall ps s shape ret l rs lbl. KnownAppend ps s
      => Expr shape ret l (rs ': lbl) ps rs -> Instr shape ret l lbl (ps ++ s) (rs ++ s)
block = IBlock (appendWitness @ps @s)

loop :: forall ps s shape ret l rs lbl. KnownAppend ps s
     => Expr shape ret l (ps ': lbl) ps rs -> Instr shape ret l lbl (ps ++ s) (rs ++ s)
loop = ILoop (appendWitness @ps @s)

if_ :: forall ps s shape ret l rs lbl. KnownAppend ps s
    => Expr shape ret l (rs ': lbl) ps rs
    -> Expr shape ret l (rs ': lbl) ps rs
    -> Instr shape ret l lbl ('Num 'I32 ': (ps ++ s)) (rs ++ s)
if_ = IIf (appendWitness @ps @s)

call :: forall ps rs s shape ret l lbl. KnownAppend ps s
     => Elem ('FuncType ps rs) (ModuleFuncs shape) -> Instr shape ret l lbl (ps ++ s) (rs ++ s)
call = ICall (appendWitness @ps @s)

br :: forall rs s shape ret l labels anyOut. KnownAppend rs s
   => Elem rs labels -> Instr shape ret l labels (rs ++ s) anyOut
br = IBr (appendWitness @rs @s)

brIf :: forall rs s shape ret l labels. KnownAppend rs s
     => Elem rs labels -> Instr shape ret l labels ('Num 'I32 ': (rs ++ s)) (rs ++ s)
brIf = IBrIf (appendWitness @rs @s)

brTable :: forall rs s shape ret l labels anyOut. KnownAppend rs s
        => [Elem rs labels] -> Elem rs labels
        -> Instr shape ret l labels ('Num 'I32 ': (rs ++ s)) anyOut
brTable = IBrTable (appendWitness @rs @s)

return_ :: forall ret s shape l lbl anyOut. KnownAppend ret s
        => Instr shape ret l lbl (ret ++ s) anyOut
return_ = IReturn (appendWitness @ret @s)

-- | Specialised forms for the common case of an empty-result block/loop and a branch to
--   an empty-result label. With @rs ~ '[]@ fixed, @rs ++ s@ reduces to @s@, so these infer
--   cleanly — no @++@ for GHC to invert and no type applications needed at call sites.

block_ :: Expr shape ret l ('[] ': lbl) '[] '[] -> Instr shape ret l lbl s s
block_ = IBlock ANil

loop_ :: Expr shape ret l ('[] ': lbl) '[] '[] -> Instr shape ret l lbl s s
loop_ = ILoop ANil

br_ :: Elem '[] labels -> Instr shape ret l labels s anyOut
br_ = IBr ANil

brIf_ :: Elem '[] labels -> Instr shape ret l labels ('Num 'I32 ': s) s
brIf_ = IBrIf ANil
