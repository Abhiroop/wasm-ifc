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

  The model we follow is SecWasm: Bastys, Algehed, Sjösten, Sabelfeld, "SecWasm: Information Flow Control for
  WebAssembly" (SAS 2022; the PLAS PDF is linked from TODO.md §F); the full rule set is in the
  technical report at <https://www.cse.chalmers.se/research/group/security/secwasm/>. Rule names
  below (T-LOAD, T-BR-IF, …) are the paper's, Fig. 10.

  The open design points are @TODO(ifc Pn)@ comments beside the constructs they concern, here
  and in "Syntax.TypesIFC", "Validation.Shape", "Validation.Elaborate", "Runtime.Interpreter",
  "Runtime.Host", "Runtime.MemInst", "Runtime.Trap" and @test/@; @grep -rn 'TODO(ifc' src test@
  lists them all. P0 is a decision to take before writing more code, P1 what the first sound
  system needs, P2 what validating and running real modules needs, P3 polish.

  __The recommended target, in one place__ (each TODO below is a piece of it). SecWasm is a
  /hybrid/ system: mostly static, with dynamic checks on memory reads only (§3.2). What is
  static goes into the indices; what is dynamic goes into 'Runtime.Interpreter.step' and
  'Runtime.MemInst.MemInst'. Concretely:

    * @Instr mod frame pc labels stackIn stackOut@ with @pc :: SecLevel@ the label of the
      control context, @labels :: [LabelShape]@ where a label carries the pc its block is typed
      under besides its result types, and a frame whose locals and results are labelled and
      which records the function's pc bound (SecWasm's @τ* →ℓ τ*@, Fig. 8).
    * The pc is /flow-insensitive/ here: fixed per block, computed by the elaborator in a
      pre-pass (see the TODO on 'IBlock'), and every value pushed under @pc@ carries a label
      @⊒ pc@. SecWasm's flow-sensitive stack-of-stacks with @lift@ (§3.3, §4.3) is the more
      permissive upgrade and is written up as a P3 at 'IBlock'.
    * SecWasm's subtyping @τ ⊑ τ'@ (used at calls, block results, sets) becomes an explicit
      relabelling instruction @IRelabel :: FlowsInto l l' -> Instr … ((t ':~ l) ': s) ((t ':~ l') ': s)@
      that the elaborator inserts: intrinsically-typed syntax has no subsumption, and explicit
      coercions are how a declarative system becomes algorithmic anyway.
    * Every side condition is a GADT witness carried by the instruction, as 'IsNum' and 'Append'
      are today: @FlowsInto l l'@ for @l ⊑ l'@, @StackAtLeast pc rs@ for "every result label is
      @⊒ pc@". The elaborator decides them on singletons ('Syntax.TypesIFC' TODOs); GHC never has
      to reason about a join symbolically.
    * Memory (T-LOAD, T-STORE, T-MEMORY-GROW): loads and stores carry a label immediate @ℓ@ as a
      singleton field; a load's result is @ℓa ⊔ ℓ ⊔ pc@ and its check @⨆ labels of the bytes read
      ⊑ ℓ@ is dynamic (a trap); a store's check @pc ⊔ ℓa ⊔ ℓv ⊑ ℓ@ is static and it relabels the
      bytes written to @ℓ@; @memory.grow@ is public-only. At run time labels are erased from
      values (@HostType (t ':~ l) = HostType t@) and kept per byte in 'Runtime.MemInst.MemInst'.
    * With everything labelled 'Low nothing can trap or be rejected that is not today, so the
      spec testsuite run at the bottom label is the regression test of the labelled machine.
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
  /execution/ (noninterference of the machine, SecWasm Thm. 1 / Cor. 1), so the labelled
  instructions must be what 'step' runs, or the theorem is about terms nobody runs; and SecWasm
  is hybrid, so 'step' /has/ to know the labels for the memory check anyway. That settles it in
  favour of generalising: index the one 'Instr' by @[LValType]@ (with
  'Validation.Shape.ModuleShape' and 'FrameShape' labelled too), let today's interpreter be the
  everything-'Low instance, keep values unlabelled at run time (@HostType@ ignores the label)
  and give only memory run-time labels. Progress and preservation carry over unchanged;
  noninterference is the new theorem on top. The price is one more index everywhere and a
  singleton for the label on loads and stores; the gain is a single source of truth and the
  spec suite as a free regression test. Decide this first: every TODO below is otherwise
  written twice.

  TODO(ifc P1): the missing index is the pc. Add @(pc :: SecLevel)@ next to the frame, and
  make @labels@ a list of a promoted @LabelShape = LabelShape SecLevel [LValType]@ (the pc the
  block's body is typed under, and its result types; a prose name, like 'FrameShape', rather
  than a tuple). Both are context, fixed at block entry, so the existing shape of the GADT
  (@labels@ threaded unchanged through a sequence) stays; that is exactly what the
  flow-insensitive choice buys (see 'IBlock').

  TODO(ifc P2): @ret@ and @locals@ are spelled out instead of a 'Validation.Shape.FrameShape'
  because that one is over unlabelled 'ValType'; the labelled 'FrameShape' also holds the
  function's pc bound. Falls out of the P0 decision.
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
       TODO(ifc P2): once @pc@ is an index, make it @(t ':~ pc) ': s@ ("a value pushed in a
       secret context is secret") and let the elaborator insert @IRelabel@ where a higher label
       is wanted. The free label is implicit subsumption at one leaf; the explicit relabel covers
       every place SecWasm uses @τ ⊑ τ'@ uniformly, and the @⊒ pc@ invariant on everything a block
       pushes is what makes the flat pc scheme sound (see 'IBlock'). -}
    IConst :: IsNum t -> HostType t -> Instr m r l lb s ((t ':~ lv) ': s)
    {- Numeric: both operands and the result share the type; the result's label is the join
       of the operands' labels (the explicit-flow rule; nothing to decide). With "values carry
       @⊒ pc@" this is closed: a join of labels @⊒ pc@ is @⊒ pc@. -}
    IAdd :: IsNum t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    ISub :: IsNum t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    IMul :: IsNum t -> Instr m r l lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    {- TODO(ifc P3): a trap is a termination channel: @div@ traps on a secret zero, and whether
       the program traps is observable (so is a memory access out of bounds at a secret address,
       'IUnreachable' under a secret pc, and the dynamic load check below). SecWasm's answer is
       termination-insensitive noninterference (TINI, Cor. 1): T-UNREACHABLE has no premise and
       traps end both runs; the paper lists termination and progress channels as non-goals (§1).
       Adopt the same: it also settles that a loop with a secret guard is fine ('ILoop'). -}
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
       TODO(ifc P1): follow SecWasm's memory model, which is fine-grained and flow-sensitive
       (§3.2): every byte carries a label, kept at run time, and the /instructions/ carry a label
       immediate, @t.load ℓ@ / @t.store ℓ@ (Fig. 8). (An earlier comment here proposed one label
       per memory; the paper rejects exactly that as too rigid, since compiled code keeps secret and
       public data in one linear memory, and per-byte labels are what let arrays and structs work.)
       The rules, with the pc index in place:
         * T-LOAD: @⟨i32⟨ℓa⟩ :: st, pc⟩ ⊢ t.load ℓ ⊣ ⟨t⟨ℓv⟩ :: st, pc⟩@ with @ℓv = ℓa ⊔ ℓ ⊔ pc@; the
           check that every byte read has label @⊑ ℓ@ is /dynamic/ (E-LOAD; it traps). So
           @ILoad :: Sing ℓ -> IsNum t -> MemArg -> Instr m f pc lb (('I32 ':~ ℓa) ': s) ((t ':~ (ℓa :/\ ℓ :/\ pc)) ': s)@
           and 'Runtime.Interpreter.step' reads the singleton, joins the bytes' labels and traps
           ('Runtime.Trap' TODO). The address label is in the result because /which/ cell is read
           depends on it.
         * T-STORE: the check @pc ⊔ ℓa ⊔ ℓv ⊑ ℓ@ is /static/ and there is no dynamic one; the bytes
           written get label @ℓ@ (E-STORE), so a public store over secret bytes makes them public
           again, soundly. So @IStore :: Sing ℓ -> FlowsInto (pc :/\ ℓa :/\ ℓv) ℓ -> IsNum t -> MemArg -> Instr m f pc lb ((t ':~ ℓv) ': ('I32 ':~ ℓa) ': s) s@.
         * T-MEMORY-GROW: @⟨i32⟨L⟩ :: st, L⟩ ⊢ memory.grow ⊣ ⟨i32⟨L⟩ :: st, L⟩@: public context,
           public argument, public result, and new bytes are labelled 'Low (the paper's Examples
           4–5 show the leak otherwise). So @IMemGrow :: Instr m f 'Low lb (('I32 ':~ 'Low) ': s) (('I32 ':~ 'Low) ': s)@,
           and since the size can then only ever depend on public data, @IMemSize@ yields
           @'I32 ':~ pc@ (public, joined with the context like every pushed value). Note that this
           forbids @memory.grow@ under a secret pc, which is what compiled @malloc@ does when
           called from a secret branch; SecWasm accepts that restriction and so should the first
           version.
         * Narrow loads and stores: the same rules; the width changes only how many bytes' labels
           are joined or written. -}
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
       TODO(ifc P2): beyond SecWasm (Wasm 1.0 has no bulk memory), so this is ours to define. With
       per-byte labels the natural rules need no immediates and no static check, only the pc:
       @memory.copy@ gives each written byte the label of the byte it came from, joined with the
       three operands' labels and @pc@ (which bytes move, and whether, depends on them);
       @memory.fill@ writes @ℓval ⊔ ℓops ⊔ pc@; @memory.init@ copies a data segment, a public
       constant of the module, so it writes @ℓops ⊔ pc@; @data.drop@ has no operands and no
       observable effect but a later trap (TINI). All of it is a per-byte computation in
       'Runtime.MemInst', dynamic like the load check. -}
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
       (The paper's Fig. 10 omits T-SELECT; the technical report has it, and this is the standard
       rule.) Left as merged so the fix is a visible decision, not a silent port. -}
    IDrop :: Instr m r l lb (t ': s) s
    ISelect :: IsNum t -> Instr m r l lb (('I32 ':~ lv) ': (t ':~ lv') ': (t ':~ lv') ': s) ((t ':~ lv') ': s)
    {- Locals carry their label in the @locals@ context, so the 'Elem' recovers it. Globals
       are still declared by an unlabelled 'GlobalType', so a free label is attached at the
       access site: a placeholder, like memory.
       TODO(ifc P1): locals and globals are /flow-insensitive/ in SecWasm (§5: "the
       flow-insensitive nature of the global and local variables"; the context @C@ of Fig. 10
       holds @locals τ*@ and @globals (mut? τ)*@), so their labels are declared once and the rules
       are the classic ones: a set needs @pc ⊔ ℓv ⊑ ℓx@, a get yields the declared label, joined
       with @pc@ under the "values carry @⊒ pc@" invariant. Today 'ILocalSet', 'ILocalTee' and
       'IGlobalSet' demand the /same/ labelled type on the stack as the variable's (the value sits
       at exactly @t@), so a public value cannot be stored into a secret local at all, and nothing
       stops a secret pc from writing a public one. Make them
       @ILocalSet :: FlowsInto (pc :/\ lv) l -> Elem (vt ':~ l) locals -> Instr m f pc lb ((vt ':~ lv) ': s) s@
       (and likewise tee and @global.set@), with 'ILocalGet' producing @vt ':~ (l :/\ pc)@. The
       witness is what 'Syntax.TypesIFC.CanFlowInto' was written for; see the TODO there for why
       it should be a GADT rather than a class.
       TODO(ifc P1): globals need a label of their own. 'Syntax.Types.GlobalType' is
       @GlobalType Mutability ValType@ and 'Validation.Shape.ModuleGlobals' yields it unlabelled,
       hence the free @lv@ on 'IGlobalGet'. SecWasm's @gt ::= mut? τ@ (Fig. 8) is the labelled
       form; it is the same decision as for calls (the P0 structure question). Globals are also
       SecWasm's /attacker model/: the attacker sees the final values of the globals whose label
       flows to theirs (§3.1), so global labels are the policy's most important part, not something
       to infer. -}
    ILocalGet :: Elem t locals -> Instr m r locals lb s (t ': s)
    ILocalSet :: Elem t locals -> Instr m r locals lb (t ': s) s
    ILocalTee :: Elem t locals -> Instr m r locals lb (t ': s) (t ': s)
    IGlobalGet :: Elem ('GlobalType mut t) (ModuleGlobals m) -> Instr m r l lb s ((t ':~ lv) ': s)
    IGlobalSet :: Elem ('GlobalType 'Mutable t) (ModuleGlobals m) -> Instr m r l lb ((t ':~ lv) ': s) s
    {- Memory (requires the module to declare a memory); same placeholder as the narrow forms,
       and the same TODO(ifc P1): T-LOAD and T-STORE as written out above, with the label
       immediate as a singleton field and the store's static check as a 'FlowsInto' witness. -}
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
       while @full@ and @rs ++ s@ here are over 'LValType'. SecWasm's function type is
       @τ* →ℓ τ*@ (Fig. 8): labelled parameters, labelled results, and @ℓ@ the function's pc bound,
       "an upper bound on the information that may flow into the execution of a function". The
       rules: T-CALL requires @pc ⊑ ℓ@ and the argument stack to be a /subtype/ of the parameters
       (the callee runs under @ℓ@, so a call inside a secret branch needs @ℓ = 'High@, and then
       every store and host call in the callee is checked against @'High@); T-CALL-INDIRECT
       additionally requires the function pointer's label to flow into @ℓ@: @pc ⊔ ℓidx ⊑ ℓf@.
       Encoding: the subtyping becomes @IRelabel@s the elaborator inserts before the call; the pc
       bound check is a field, @ICall :: FlowsInto pc ℓ -> Append ps s full -> Elem ('LFuncType ℓ ps rs) (ModuleFuncs m) -> …@;
       and make "result labels are @⊒ ℓ@" a well-formedness condition of labelled function types,
       so the callee's results satisfy the caller's "values carry @⊒ pc@" invariant for free (since
       @pc ⊑ ℓ@). For 'Syntax.Instructions.ICallIndirect' the run-time type check in
       'Runtime.TableInst' compares singletons; with labelled types the comparison covers the
       labels, and a mismatch stays the same trap. Host functions take their labelled types from
       the policy (see "Runtime.Host"). Blocked on the P0 structure question (a labelled
       'Validation.Shape.ModuleFuncs'). -}

    {- Structured control. Bodies are typed in isolation (@ps -> rs@) within the same frame,
       framed over a polymorphic @s@. A block/if label carries its results; a loop its params.
       TODO(ifc P0): no program-counter label yet, so implicit flows are untyped: after
       @(if (secret) (then (local.set $public 1)))@ the public local reveals the secret, and the
       paper's Example 8 leaks with @br_if@ alone. SecWasm (§3.3, §4.3) keeps a /stack-of-stacks/
       @γ@ of pairs @⟨st, pc⟩@, one per enclosing block, threaded through the typing judgment
       @γ, C ⊢ expr ⊣ γ'@; a branch @br_if i@ on a condition labelled @ℓ@ applies
       @lift(ℓ ⊔ pc)@ to entries @0..i@ (the remainder of the current block and of every block it
       can jump out of now runs conditionally, so their pcs /and the labels of the values already
       on their stacks/ are raised), and T-BLOCK merges the raised pc back into the enclosing
       entry when the block ends (@pc ⊔ pc''@), which is how the raise ends exactly at the end of
       the targeted block. That is flow-/sensitive/: the environment is state, not context.

       Recommended encoding, flow-/insensitive/ and much lighter on the types: every block gets
       /one/ pc for its whole body, fixed at entry, as the pc field of its 'LabelShape'; the
       elaborator computes it in a pre-pass over the raw body before elaborating it:
         @pc(B) = pc(parent B) ⊔ ⨆ { pc(site b) ⊔ ℓ(cond b) | b a br/br_if/br_table/return whose
           exit path leaves or ends at B }@, and an @if@'s arms are blocks with
           @pc ⊒ pc(parent) ⊔ ℓ(cond)@.
       Since @ℓ(cond b)@ comes from the data flow, which depends on the pcs (values carry @⊒ pc@),
       this is a joint fixpoint; over the two-point lattice it converges in a couple of sweeps, and
       T-LOOP already demands such a fixpoint explicitly (@pc ⊑ pc'@, @γ ⊑ γ'@, @st ⊑ st'@). What
       it costs: the code /before/ a raising branch in the same block is typed at the raised pc
       too, where SecWasm keeps it low (Example 6's @expr2@). What it buys: @labels@ stays an
       environment, no @lift@ type family, no 'Elem' proofs into a lifted environment, and the
       confinement argument becomes structural: WebAssembly's block locality (our 'Append' framing)
       means a block's body can only touch its own segment, every value it pushes is @⊒ pc@, and
       everything below is untouched. So the rules become:
         * 'IBlock'/'ILoop': the body is an @Expr m f pc' ('LabelShape pc' rs ': lb) ps rs@ with
           @FlowsInto pc pc'@ and @StackAtLeast pc' rs@ (a block's results are at least as secret
           as the context that produced them; the T-BR-IF premise @pc ⊔ ℓ ⊑ C.labels[i]@ is what
           rejects Example 8).
         * 'IIf': both arms under @pc'@ with @FlowsInto (pc :/\ lv) pc'@ (T-IF, tech report).
         * 'IBr': @FlowsInto pc pc_target@ and 'StackAtLeast' on the target's types;
           'IBrIf'/'IBrTable': the same with @pc :/\ lv@, for every target including the default.
         * 'IReturn': @FlowsInto pc ℓf@ where @ℓf@ is the function's pc bound, plus the return
           types @⊒ pc@ (T-RETURN); nothing else, because the pre-pass has already raised every
           enclosing block a @return@ under a secret pc can skip out of.
       TODO(ifc P3): the flow-sensitive upgrade, once the flat scheme works: thread @γ@ in and out
       (@Instr m f γin si γout so@), a @Lift ℓ γ@ type family, and elaboration that continues after
       a branch under the lifted environment. Only worth it if a case study is rejected by the
       flat scheme and accepted by the paper's. -}
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
       operands) is otherwise free. TODO(ifc P0): the rules are in the pc TODO above: an
       unconditional branch needs @pc ⊑@ the target's pc and types (T-BR), a conditional one
       @pc ⊔ ℓcond ⊑@ them (T-BR-IF), @br_table@ for every target and the default. -}
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
  them with the first labelled example that needs a non-empty label; hand-written examples
  will also have to pin every label (GHC cannot infer @lv@ from @lv :/\ lv' ~ 'High@).
-}
block_ :: Expr m r l ('[] ': lb) '[] '[] -> Instr m r l lb s s
block_ = IBlock ANil

loop_ :: Expr m r l ('[] ': lb) '[] '[] -> Instr m r l lb s s
loop_ = ILoop ANil

br_ :: Elem '[] labels -> Instr m r l labels s anyOut
br_ = IBr ANil

brIf_ :: Elem '[] labels -> Instr m r l labels (('I32 ':~ lv) ': s) s
brIf_ = IBrIf ANil
