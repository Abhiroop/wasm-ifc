{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

{- | The information-flow-typed instruction set: 'Syntax.Instructions.Instr' with every stack,
  local, label and result type labelled by a security level ('LValType'), so the label of a
  computed value is the join of the labels it was computed from. Abhiroop's first cut
  (2026-09), ported onto the current instruction set. It is a parallel GADT for now: the raw
  AST, the operation groups and the elaborator are shared with "Syntax.Instructions", and
  nothing runs it yet.

  Open points, deliberately left for the design discussion rather than settled by the port:

    * the labels a constant, a load, a global read or @memory.size@ produce are free (any
      @lv@): placeholders until memories and globals carry a label of their own;
    * a branch or @if@ does not yet raise a program-counter label, and @select@ does not join
      the condition's label into its result, so implicit flows are not yet typed;
    * calls ('Syntax.Instructions.ICall', 'Syntax.Instructions.ICallIndirect') are absent:
      'FuncType' and 'Validation.Shape.ModuleFuncs' are over unlabelled 'ValType', and
      labelling function signatures is a decision, not a port;
    * the frame is given by its two components (@ret@ and @locals@) rather than a
      'Validation.Shape.FrameShape', which is over unlabelled types too.
-}
module Syntax.InstructionsIFC (
    Instr (..),
    Expr (..),

    -- * Smart constructors (empty-result label variants)
    block_,
    loop_,
    br_,
    brIf_,
) where

import Data.List.Singletons (type (++))
import Syntax.Immediates
import Syntax.Instructions (BitwiseOp, ConvertOp, CountOp, FloatBinOp, FloatUnOp)
import Syntax.Types
import Syntax.TypesIFC
import Validation.Shape (
    Append (..),
    DataShape (..),
    Elem,
    ModuleData,
    ModuleGlobals,
    ModuleMems,
    ModuleShape,
 )

{- | The labelled instruction. Read as 'Syntax.Instructions.Instr': the last two indices are
  the operand stack before and after, the others the typing context, here with the frame
  spelled out as the function's labelled result type @ret@ and labelled @locals@.
-}
data
    Instr
        (mod :: ModuleShape)
        (ret :: [LValType])
        (locals :: [LValType])
        (labels :: [[LValType]])
        (stackIn :: [LValType])
        (stackOut :: [LValType])
    where
    {- Constants. The label is free: a literal is public, so 'Low would do, but a free label
       lets it be used at any level without a separate relabelling step. -}
    IConst :: IsNum t -> HostType t -> Instr m r l lb s ((t ':~ lv) ': s)
    {- Numeric: both operands and the result share the type; the result's label is the join
       of the operands' labels. -}
    IAdd :: IsNum t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    ISub :: IsNum t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    IMul :: IsNum t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    IDiv :: NumWithSign t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    IRem :: IsInt t -> Signedness -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    {- Comparison: consume the operands, produce an i32 boolean labelled with their join. -}
    IEqz :: IsInt t -> Instr m r l lb ((t ':~ lv) ': s) (('I32 ':~ lv) ': s)
    IEq :: IsNum t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ (lv :/\ lv')) ': s)
    INe :: IsNum t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ (lv :/\ lv')) ': s)
    ILt :: NumWithSign t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ (lv :/\ lv')) ': s)
    IGt :: NumWithSign t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ (lv :/\ lv')) ': s)
    ILe :: NumWithSign t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ (lv :/\ lv')) ': s)
    IGe :: NumWithSign t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ (lv :/\ lv')) ': s)
    {- Integer bitwise / shift / count, and floating-point unary / binary. Binary operations
       join like the arithmetic ones; unary ones carry the operand's label through. -}
    IBitwise :: IsInt t -> BitwiseOp -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    ICount :: IsInt t -> CountOp -> Instr m r l lb ((t ':~ lv) ': s) ((t ':~ lv) ': s)
    IFloatUn :: IsFloat t -> FloatUnOp -> Instr m r l lb ((t ':~ lv) ': s) ((t ':~ lv) ': s)
    IFloatBin :: IsFloat t -> FloatBinOp -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    {- Conversions: one operand, so its label carries through. -}
    IConvert :: ConvertOp from to -> Instr m r l lb ((from ':~ lv) ': s) ((to ':~ lv) ': s)
    {- Memory size / grow and narrow load / store. The memory shape carries no label yet, so a
       load's result and @memory.size@ take a free label at the access site rather than the
       memory's own: a placeholder. -}
    IMemSize :: (ModuleMems m ~ (mem ': mems)) => Instr m r l lb s (('I32 ':~ lv) ': s)
    IMemGrow :: (ModuleMems m ~ (mem ': mems)) => Instr m r l lb (('I32 ':~ lv) ': s) (('I32 ':~ lv) ': s)
    ILoadN ::
        (ModuleMems m ~ (mem ': mems)) =>
        NarrowWidth t ->
        Signedness ->
        MemArg ->
        Instr m r l lb (('I32 ':~ lv) ': s) ((t ':~ lv') ': s)
    IStoreN ::
        (ModuleMems m ~ (mem ': mems)) =>
        NarrowWidth t ->
        MemArg ->
        Instr m r l lb ((t ':~ lv) ': ('I32 ':~ lv') ': s) s
    {- Bulk memory. Operands, top first: the byte count, then the source, then the destination;
       each with its own label, none of which reaches the memory yet (same placeholder). -}
    IMemCopy :: (ModuleMems m ~ (mem ': mems)) => Instr m r l lb (('I32 ':~ lv) ': ('I32 ':~ lv') ': ('I32 ':~ lv'') ': s) s
    IMemFill :: (ModuleMems m ~ (mem ': mems)) => Instr m r l lb (('I32 ':~ lv) ': ('I32 ':~ lv') ': ('I32 ':~ lv'') ': s) s
    IMemInit ::
        (ModuleMems m ~ (mem ': mems)) =>
        Elem 'DataShape (ModuleData m) ->
        Instr m r l lb (('I32 ':~ lv) ': ('I32 ':~ lv') ': ('I32 ':~ lv'') ': s) s
    IDataDrop :: Elem 'DataShape (ModuleData m) -> Instr m r l lb s s
    {- Stack management. @select@ keeps the operands' label and drops the condition's: an
       implicit flow left untyped for now (see the module header). -}
    IDrop :: Instr m r l lb (t ': s) s
    ISelect :: IsNum t -> Instr m r l lb (('I32 ':~ lv) ': (t ':~ lv') ': (t ':~ lv') ': s) ((t ':~ lv') ': s)
    {- Locals carry their label in the @locals@ context, so the 'Elem' recovers it. Globals
       are still declared by an unlabelled 'GlobalType', so a free label is attached at the
       access site: a placeholder, like memory. -}
    ILocalGet :: Elem t locals -> Instr m r locals lb s (t ': s)
    ILocalSet :: Elem t locals -> Instr m r locals lb (t ': s) s
    ILocalTee :: Elem t locals -> Instr m r locals lb (t ': s) (t ': s)
    IGlobalGet :: Elem ('GlobalType mut t) (ModuleGlobals m) -> Instr m r l lb s ((t ':~ lv) ': s)
    IGlobalSet :: Elem ('GlobalType 'Mutable t) (ModuleGlobals m) -> Instr m r l lb ((t ':~ lv) ': s) s
    {- Memory (requires the module to declare a memory); same placeholder as the narrow forms. -}
    ILoad ::
        (ModuleMems m ~ (mem ': mems)) =>
        IsNum t ->
        MemArg ->
        Instr m r l lb (('I32 ':~ lv) ': s) ((t ':~ lv') ': s)
    IStore ::
        (ModuleMems m ~ (mem ': mems)) =>
        IsNum t ->
        MemArg ->
        Instr m r l lb ((t ':~ lv) ': ('I32 ':~ lv') ': s) s
    {- Structured control. Bodies are typed in isolation (@ps -> rs@) within the same frame,
       framed over a polymorphic @s@. A block/if label carries its results; a loop its params.
       The condition's label is not yet raised into the bodies (no program-counter label). -}
    IBlock ::
        Append ps s full ->
        Expr m r l (rs ': lb) ps rs ->
        Instr m r l lb full (rs ++ s)
    ILoop ::
        Append ps s full ->
        Expr m r l (ps ': lb) ps rs ->
        Instr m r l lb full (rs ++ s)
    IIf ::
        Append ps s full ->
        Expr m r l (rs ': lb) ps rs ->
        Expr m r l (rs ': lb) ps rs ->
        Instr m r l lb (('I32 ':~ lv) ': full) (rs ++ s)
    {- Branches. The witness gives the branch width; the output (and the stack below the
       operands) is otherwise free. -}
    IBr :: Append rs s full -> Elem rs labels -> Instr m r l labels full anyOut
    IBrIf :: Append rs s full -> Elem rs labels -> Instr m r l labels (('I32 ':~ lv) ': full) full
    IBrTable ::
        Append rs s full ->
        [Elem rs labels] ->
        Elem rs labels ->
        Instr m r l labels (('I32 ':~ lv) ': full) anyOut
    IReturn :: Append ret s full -> Instr m ret l lb full anyOut
    {- Inert -}
    INop :: Instr m r l lb s s
    IUnreachable :: Instr m r l lb s anyOut

-- | A labelled instruction sequence: the output shape of each instruction is the input of the next.
data
    Expr
        (mod :: ModuleShape)
        (ret :: [LValType])
        (locals :: [LValType])
        (labels :: [[LValType]])
        (stackIn :: [LValType])
        (stackOut :: [LValType])
    where
    INil :: Expr m r l lb s s
    (:.) ::
        Instr m r l lb s1 s2 ->
        Expr m r l lb s2 s3 ->
        Expr m r l lb s1 s3

infixr 5 :.

{- | The empty-result forms of block, loop and branch, which need no 'Append' witness. The
  general forms want a singleton for a labelled prefix (there is none yet: 'SecLevel' has no
  generated singletons), so they wait for the first hand-written labelled example.
-}
block_ :: Expr m r l ('[] ': lb) '[] '[] -> Instr m r l lb s s
block_ = IBlock ANil

loop_ :: Expr m r l ('[] ': lb) '[] '[] -> Instr m r l lb s s
loop_ = ILoop ANil

br_ :: Elem '[] labels -> Instr m r l labels s anyOut
br_ = IBr ANil

brIf_ :: Elem '[] labels -> Instr m r l labels (('I32 ':~ lv) ': s) s
brIf_ = IBrIf ANil
