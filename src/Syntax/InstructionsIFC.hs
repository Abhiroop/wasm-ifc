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

  The open design points are @TODO(ifc Pn)@ comments beside the constructs they concern, here
  and in "Syntax.TypesIFC", "Validation.Shape", "Validation.Elaborate", "Runtime.Interpreter",
  "Runtime.Host", "Runtime.MemInst" and @test/Examples.hs@; @grep -rn 'TODO(ifc' src test@ lists
  them all. P0 is a decision to take before writing more code, P1 what the first sound system
  needs, P2 what validating and running real modules needs, P3 polish.
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

  TODO(ifc P0): parallel GADT, or the one 'Syntax.Instructions.Instr' generalised over the
  label? This copy mirrors it by hand, and the elaborator, 'Runtime.Interpreter.step' and the
  soundness argument would have to be copied the same way. Intuition: the IFC theorem is about
  /execution/ (noninterference of the machine), so the labelled instructions must be what
  'step' runs, or the theorem is about terms nobody runs. That argues for generalising: index
  the one 'Instr' by @[LValType]@ (with 'Validation.Shape.ModuleShape' and 'FrameShape' labelled
  too) and let today's interpreter be the everything-'Low instance; 'step' then erases labels
  (they are static), its progress and preservation carry over unchanged, and noninterference is
  the new theorem on top. The price is one more index everywhere; the gain is a single source
  of truth. Decide this first: every TODO below is otherwise written twice.

  TODO(ifc P2): @ret@ and @locals@ are spelled out instead of a 'Validation.Shape.FrameShape'
  because that one is over unlabelled 'ValType'; a labelled (or kind-polymorphic) 'FrameShape'
  falls out of the P0 decision.
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
       lets it be used at any level without a separate relabelling step.
       TODO(ifc P3): keep it free or fix it to 'Low? Free is sound (it is the subsumption
       @Low ⊑ l@ applied at the leaf) and lets the elaborator pick whatever label the context
       wants; fixing 'Low would need an explicit relabel instruction or subtyping on stacks. -}
    IConst :: IsNum t -> HostType t -> Instr m r l lb s ((t ':~ lv) ': s)
    {- Numeric: both operands and the result share the type; the result's label is the join
       of the operands' labels. -}
    IAdd :: IsNum t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    ISub :: IsNum t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    IMul :: IsNum t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    {- TODO(ifc P3): a trap is a termination channel: @div@ traps on a secret zero, and whether
       the program traps is observable (so is a memory access out of bounds at a secret address,
       and 'IUnreachable' under a secret pc). The usual answer is termination-insensitive
       noninterference (TINI): traps and divergence are outside the theorem. Fix the theorem's
       flavour early; it also settles what a loop with a secret guard may do ('ILoop'). -}
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
       memory's own: a placeholder.
       TODO(ifc P1): give the memory a label. Per-address labels are meaningless under computed
       addresses (which address a secret went to leaks the address), so SecWasm labels the whole
       linear memory with one level ℓmem. Then a load yields @ℓmem ⊔ ℓaddr@ (which cell is read
       depends on the address); a store needs @ℓaddr ⊔ ℓval ⊔ pc ⊑ ℓmem@ (address and pc decide
       whether and where a write happens, the value what); @memory.size@ and @memory.grow@ read
       and change a size whose history depends on every earlier @grow@'s pc, so they are ℓmem
       too. Where ℓmem lives: a field of 'Validation.Shape.MemShape' (regenerate its singletons)
       once the P0 structure question is settled. With one memory per module today, ℓmem is a
       single module-level constant, which keeps the first version simple. -}
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
       each with its own label, none of which reaches the memory yet (same placeholder).
       TODO(ifc P1): with ℓmem in place all three operands and the pc need @⊑ ℓmem@ (each decides
       which bytes move). @memory.init@ copies public bytes (a data segment is a constant of the
       module) into memory; @memory.copy@ moves bytes within the same memory, so the byte labels
       are ℓmem on both sides; @data.drop@ has no operands and only the pc to check. -}
    IMemCopy :: (ModuleMems m ~ (mem ': mems)) => Instr m r l lb (('I32 ':~ lv) ': ('I32 ':~ lv') ': ('I32 ':~ lv'') ': s) s
    IMemFill :: (ModuleMems m ~ (mem ': mems)) => Instr m r l lb (('I32 ':~ lv) ': ('I32 ':~ lv') ': ('I32 ':~ lv'') ': s) s
    IMemInit ::
        (ModuleMems m ~ (mem ': mems)) =>
        Elem 'DataShape (ModuleData m) ->
        Instr m r l lb (('I32 ':~ lv) ': ('I32 ':~ lv') ': ('I32 ':~ lv'') ': s) s
    IDataDrop :: Elem 'DataShape (ModuleData m) -> Instr m r l lb s s
    {- Stack management.
       TODO(ifc P1): 'ISelect' drops the condition's label, a leak: @select@ /is/ @cond ? a : b@,
       an explicit dependence on all three operands. Fix (one line): result label
       @lc :/\ l1 :/\ l2@, with the two operands allowed to differ, i.e.
       @Instr m r l lb (('I32 ':~ lc) ': (t ':~ l1) ': (t ':~ l2) ': s) ((t ':~ (lc :/\ l1 :/\ l2)) ': s)@.
       Left as merged so the fix is a visible decision, not a silent port. -}
    IDrop :: Instr m r l lb (t ': s) s
    ISelect :: IsNum t -> Instr m r l lb (('I32 ':~ lv) ': (t ':~ lv') ': (t ':~ lv') ': s) ((t ':~ lv') ': s)
    {- Locals carry their label in the @locals@ context, so the 'Elem' recovers it. Globals
       are still declared by an unlabelled 'GlobalType', so a free label is attached at the
       access site: a placeholder, like memory.
       TODO(ifc P1): 'ILocalSet', 'ILocalTee' and 'IGlobalSet' demand the /same/ labelled type
       on the stack as the variable's (the value sits at exactly @t@), so a public value cannot
       be stored into a secret local at all, and nothing stops a secret pc from writing a public
       one. They want the flow relation: with the variable at @vt ':~ l@ and the value at
       @vt ':~ lv@, require @lv ⊑ l@ (and @pc ⊑ l@ once the pc exists, see 'IIf'). That is what
       'Syntax.TypesIFC.CanFlowInto' was written for, and it is unused so far; but see the TODO
       on it: the elaborator must construct that evidence at validation time, so it should be
       a GADT witness like 'IsNum', carried as a field here, not a class constraint.
       TODO(ifc P1): globals need a label of their own. 'Syntax.Types.GlobalType' is
       @GlobalType Mutability ValType@ and 'Validation.Shape.ModuleGlobals' yields it unlabelled,
       hence the free @lv@ on 'IGlobalGet'. A labelled global type is the same decision as for
       memory and calls (the P0 structure question). Mutable globals are also how modules share
       state, so their labels are part of the module's interface: policy, not inference. -}
    ILocalGet :: Elem t locals -> Instr m r locals lb s (t ': s)
    ILocalSet :: Elem t locals -> Instr m r locals lb (t ': s) s
    ILocalTee :: Elem t locals -> Instr m r locals lb (t ': s) (t ': s)
    IGlobalGet :: Elem ('GlobalType mut t) (ModuleGlobals m) -> Instr m r l lb s ((t ':~ lv) ': s)
    IGlobalSet :: Elem ('GlobalType 'Mutable t) (ModuleGlobals m) -> Instr m r l lb ((t ':~ lv) ': s) s
    {- Memory (requires the module to declare a memory); same placeholder as the narrow forms,
       and the same TODO(ifc P1) rule once ℓmem exists: a load yields @ℓmem ⊔ ℓaddr@, a store
       needs @ℓaddr ⊔ ℓval ⊔ pc ⊑ ℓmem@. -}
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
    {- TODO(ifc P1): calls are absent. 'Syntax.Instructions.ICall' needs
       @Elem ('FuncType ps rs) (ModuleFuncs m)@ with @ps@ and @rs@ over unlabelled 'ValType',
       while @full@ and @rs ++ s@ here are over 'LValType'. A labelled function type has three
       parts: labelled parameters, labelled results, and a pc bound, the highest context the
       function may be called from, because a call inside a secret branch runs the whole callee
       under a secret pc (its stores and host calls would leak otherwise); @call@ then requires
       @pc ⊑ pcbound@ and the body is typed under @pcbound@. 'Syntax.Instructions.ICallIndirect'
       compares the expected 'FuncType' singleton with the table entry's at run time
       ('Runtime.TableInst'); with labelled types that comparison covers the labels, or table
       entries stay unlabelled and every indirect call gets the top pc bound. Host functions
       take their labelled types from the policy (see "Runtime.Host"): they are the sources and
       sinks. Blocked on the P0 structure question (a labelled 'Validation.Shape.ModuleFuncs'). -}

    {- Structured control. Bodies are typed in isolation (@ps -> rs@) within the same frame,
       framed over a polymorphic @s@. A block/if label carries its results; a loop its params.
       TODO(ifc P0): no program-counter label yet, so implicit flows are untyped: after
       @(if (secret) (then (local.set $public 1)))@ the public local reveals the secret. The
       structured control flow of WebAssembly makes the fix clean: the pc rises only at an
       @if@, @br_if@ or @br_table@ on a labelled condition, and falls back exactly at the end of
       the block whose label the branch targets, so blocks are the join points and the pc never
       needs lowering explicitly. Give every /label/ a pc, @labels :: [(SecLevel, [LValType])]@
       (or a pc index on 'Instr' and 'Expr' plus one per label). Then 'IIf' types both bodies
       under @pc ⊔ lv@ and its results come out @⊒ pc ⊔ lv@ (a value produced in a secret
       context is secret); 'IBrIf' and 'IBrTable' may only target a label whose pc is @⊒ lv@ and
       @⊒@ the current pc; 'IBlock' and 'ILoop' choose their label's pc and type the body under
       it; 'IReturn' targets the function's own label, whose pc is the function's pc bound (see
       the calls TODO above); every effect ('ILocalSet', 'IGlobalSet', the stores, host calls)
       checks @pc ⊑@ its target's label. This is SecWasm's rule set. A loop whose guard is a
       secret @br_if@ makes termination secret-dependent: allowed under TINI (see the trap TODO
       at 'IMul'). At run time nothing changes for a static system; a hybrid one keeps the pc
       on 'Runtime.Interpreter.Control' (see the TODO there). -}
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
       operands) is otherwise free. TODO(ifc P0): the label rule a branch must satisfy is in the
       pc TODO above: the target label's pc must be @⊒@ the condition's label and the current pc. -}
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

{- | The empty-result forms of block, loop and branch, which need no 'Append' witness.
  TODO(ifc P2): the general forms (@block@, @loop@, @if_@, @br@, @brIf@, @brTable@, @return_@
  in Abhiroop's version) built their witness from a @KnownAppend@ class; here they want
  'Validation.Shape.appendFromSing' on a @Sing (ps :: [LValType])@, which needs singletons for
  'SecLevel' and 'LValType' (see the TODO on 'Syntax.TypesIFC.KnownSecLevel') and a
  poly-kinded 'appendFromSing' (its body already is; only the signature pins @[ValType]@). Add
  them with the first labelled example that needs a non-empty label.
-}
block_ :: Expr m r l ('[] ': lb) '[] '[] -> Instr m r l lb s s
block_ = IBlock ANil

loop_ :: Expr m r l ('[] ': lb) '[] '[] -> Instr m r l lb s s
loop_ = ILoop ANil

br_ :: Elem '[] labels -> Instr m r l labels s anyOut
br_ = IBr ANil

brIf_ :: Elem '[] labels -> Instr m r l labels (('I32 ':~ lv) ': s) s
brIf_ = IBrIf ANil
