{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

{- | The information-flow-typed instruction set: 'Syntax.Instructions.Instr' with every stack,
  local, label and result type labelled by a security level ('LValType'), a program-counter
  label indexing the control context, and every side condition of the typing rules carried as
  a witness the program has to supply. Abhiroop's first cut (2026-09), ported onto the current
  instruction set and then given the pc and the memory policy. It is a parallel GADT for now:
  the raw AST, the operation groups and the elaborator are shared with "Syntax.Instructions",
  and nothing runs it yet.

  The model we follow is SecWasm: Bastys, Algehed, Sjösten, Sabelfeld, "SecWasm: Information Flow Control for
  WebAssembly" (SAS 2022; the PLAS PDF is linked from TODO.md §F); the full rule set is in the
  technical report at <https://www.cse.chalmers.se/research/group/security/secwasm/>. Rule names
  below (T-LOAD, T-BR-IF, …) are the paper's, Fig. 10.

  The open design points are @TODO(ifc Pn)@ comments beside the constructs they concern, here
  and in "Syntax.TypesIFC", "Validation.Shape", "Validation.Elaborate", "Runtime.Interpreter",
  "Runtime.Host", "Runtime.MemInst", "Runtime.Trap" and @test/@; @grep -rn 'TODO(ifc' src test@
  lists them all. P0 is a decision to take before writing more code, P1 what the first sound
  system needs, P2 what validating and running real modules needs, P3 polish.

  __Where this stands.__ In place: the pc index and the flow-insensitive block pc, labelled
  locals with SecWasm's flow-insensitive get/set rules, explicit relabelling in place of the
  paper's subtyping, the branch and block rules with their @⊒ pc@ premises, @select@'s
  condition label, and — the one deliberate divergence from the paper — a /statically/ checked
  memory through a declared 'MemPolicy' ('ILoad'/'IStore' below). Still open, each with its
  TODO: globals (the last store with no label of its own), calls, and the bulk-memory
  operations, all three blocked on the same P0 question of a labelled 'ModuleShape'.

  __The shape of the system.__ SecWasm is a /hybrid/ system: mostly static, with a dynamic
  check on memory reads (§3.2). This layer is static throughout, because of how memory is
  modelled here (see 'Syntax.TypesIFC.MemPolicy'); what remains dynamic is the bounds check
  plain WebAssembly already does. Concretely:

    * @Instr mod policy ret locals pc labels stackIn stackOut@, with @pc@ the label of the
      control context and @labels@ a list of 'LabelShape' — each carrying the pc its block is
      typed under besides its result types.
    * The pc is /flow-insensitive/: fixed per block, and every value pushed under it carries a
      label @⊒ pc@ (each pushing rule either joins @pc@ in or demands a @FlowsInto pc@
      witness). SecWasm's flow-sensitive stack-of-stacks with @lift@ (§3.3, §4.3) is the more
      permissive upgrade, written up as a P3 at 'IBlock'.
    * SecWasm's subtyping @τ ⊑ τ'@ (used at calls, block results, sets) is the explicit
      'IRelabel': intrinsically-typed syntax has no subsumption, and explicit coercions are how
      a declarative system becomes algorithmic anyway.
    * Every side condition is a witness carried by the instruction, as 'Syntax.Types.IsNum' and
      'Validation.Shape.Append' are: 'FlowsInto' for @l ⊑ l'@, 'StackAtLeast' for "every result
      label is @⊒ pc@", 'SpanAt' for "this access lands in that span of memory". The elaborator
      decides them on singletons ('Syntax.TypesIFC.decideFlow'); GHC never has to reason about
      a join symbolically.
    * With everything labelled 'Low and one 'Low span covering memory, nothing can be rejected
      that is not rejected today, so the spec testsuite run at the bottom label is the
      regression test of the labelled machine.
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
  the operand stack before and after, the others the typing context — here the module shape,
  the memory policy the load and store proofs are relative to, the frame (spelled out as the
  function's labelled result type @ret@ and labelled @locals@), the pc, and the label context.

  TODO(ifc P0): parallel GADT, or the one 'Syntax.Instructions.Instr' generalised over the
  label? This copy mirrors it by hand, and the elaborator, 'Runtime.Interpreter.step' and the
  soundness argument would have to be copied the same way. Intuition: the IFC theorem is about
  /execution/ (noninterference of the machine, SecWasm Thm. 1 / Cor. 1), so the labelled
  instructions must be what 'step' runs, or the theorem is about terms nobody runs. That
  argues for generalising: index the one 'Instr' by @[LValType]@ (with
  'Validation.Shape.ModuleShape' and 'FrameShape' labelled too), let today's interpreter be the
  everything-'Low instance and keep values unlabelled at run time (@HostType@ ignores the
  label). Under the memory model here ('Syntax.TypesIFC.MemPolicy') 'step' needs no label
  state at all, only the span bounds, which makes that generalisation cheaper than it looked
  when the labels were per byte. Decide this first: the three TODOs left below (globals, calls,
  bulk memory) are all blocked on it.

  TODO(ifc P2): @ret@ and @locals@ are spelled out instead of a 'Validation.Shape.FrameShape'
  because that one is over unlabelled 'ValType'; the labelled frame also carries the function's
  pc bound @ℓf@, which 'IReturn' and (once they exist) calls are checked against. Falls out of
  the P0 decision.
-}
data
    Instr
        (mod :: ModuleShape)
        (policy :: MemPolicy)
        (ret :: [LValType])
        (locals :: [LValType])
        (pc :: SecLevel)
        (labels :: [LabelShape])
        (stackIn :: [LValType])
        (stackOut :: [LValType])
    where
    {- Constants. A literal is public, but it may be pushed at any level the context allows:
       the witness is the "values carry @⊒ pc@" invariant at this leaf, and it is what lets a
       constant be used as a secret without a separate relabelling step. -}
    IConst :: FlowsInto pc lv -> IsNum t -> HostType t -> Instr m pol r l pc lb s ((t ':~ lv) ': s)
    {- Explicit relabelling: SecWasm's subtyping @τ ⊑ τ'@ as an instruction, which the
       elaborator inserts wherever the paper appeals to subsumption. Raising only — there is no
       constructor of 'FlowsInto' that lowers a label, so this cannot declassify. -}
    IRelabel :: FlowsInto lv lv' -> Instr m pol r l pc lb ((t ':~ lv) ': s) ((t ':~ lv') ': s)
    {- Numeric: both operands and the result share the type; the result's label is the join
       of the operands' labels (the explicit-flow rule; nothing to decide). The @⊒ pc@
       invariant is closed under this: a join of labels @⊒ pc@ is @⊒ pc@. -}
    IAdd :: IsNum t -> Instr m pol r l pc lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    ISub :: IsNum t -> Instr m pol r l pc lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    IMul :: IsNum t -> Instr m pol r l pc lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    {- TODO(ifc P3): a trap is a termination channel: @div@ traps on a secret zero, and whether
       the program traps is observable (so is a memory access out of bounds at a secret address,
       'IUnreachable' under a secret pc, and the span bounds check below). SecWasm's answer is
       termination-insensitive noninterference (TINI, Cor. 1): T-UNREACHABLE has no premise and
       traps end both runs; the paper lists termination and progress channels as non-goals (§1).
       Adopt the same: it also settles that a loop with a secret guard is fine ('ILoop'). -}
    IDiv :: NumWithSign t -> Instr m pol r l pc lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    IRem :: IsInt t -> Signedness -> Instr m pol r l pc lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    {- Comparison: consume the operands, produce an i32 boolean labelled with their join. -}
    IEqz :: IsInt t -> Instr m pol r l pc lb ((t ':~ lv) ': s) (('I32 ':~ lv) ': s)
    IEq :: IsNum t -> Instr m pol r l pc lb ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ (lv :/\ lv')) ': s)
    INe :: IsNum t -> Instr m pol r l pc lb ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ (lv :/\ lv')) ': s)
    ILt :: NumWithSign t -> Instr m pol r l pc lb ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ (lv :/\ lv')) ': s)
    IGt :: NumWithSign t -> Instr m pol r l pc lb ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ (lv :/\ lv')) ': s)
    ILe :: NumWithSign t -> Instr m pol r l pc lb ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ (lv :/\ lv')) ': s)
    IGe :: NumWithSign t -> Instr m pol r l pc lb ((t ':~ lv) ': (t ':~ lv') ': s) (('I32 ':~ (lv :/\ lv')) ': s)
    {- Integer bitwise / shift / count, and floating-point unary / binary. Binary operations
       join like the arithmetic ones; unary ones carry the operand's label through. -}
    IBitwise :: IsInt t -> BitwiseOp -> Instr m pol r l pc lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    ICount :: IsInt t -> CountOp -> Instr m pol r l pc lb ((t ':~ lv) ': s) ((t ':~ lv) ': s)
    IFloatUn :: IsFloat t -> FloatUnOp -> Instr m pol r l pc lb ((t ':~ lv) ': s) ((t ':~ lv) ': s)
    IFloatBin :: IsFloat t -> FloatBinOp -> Instr m pol r l pc lb ((t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ (lv :/\ lv')) ': s)
    {- Conversions: one operand, so its label carries through. -}
    IConvert :: ConvertOp from to -> Instr m pol r l pc lb ((from ':~ lv) ': s) ((to ':~ lv) ': s)
    {- Memory size and grow (T-MEMORY-GROW): public context, public argument, public result.
       New bytes would be labelled 'Low, which is why growing may not happen under a secret pc
       (the paper's Examples 4–5 show the leak otherwise); pinning the index to @'Low@ is that
       premise. @memory.size@ can then only ever depend on public data, so it yields the pc
       like every other pushed value. Note that this forbids @memory.grow@ under a secret pc,
       which is what compiled @malloc@ does when called from a secret branch; SecWasm accepts
       that restriction and so does this.

       Under the policy of 'Syntax.TypesIFC.MemPolicy' the grown bytes lie beyond every
       declared span, so no 'SpanAt' can name them and no load or store can reach them: growth
       is visible to @memory.size@ but not addressable until the policy declares a span for it. -}
    IMemSize :: (ModuleMems m ~ (mem ': mems)) => Instr m pol r l pc lb s (('I32 ':~ pc) ': s)
    IMemGrow :: (ModuleMems m ~ (mem ': mems)) => Instr m pol r l 'Low lb (('I32 ':~ 'Low) ': s) (('I32 ':~ 'Low) ': s)
    {- Bulk memory.
       TODO(ifc P1): these do not carry a 'SpanAt' and so do not respect the memory policy —
       the one place left where memory can be written without a proof. They are beyond SecWasm
       (Wasm 1.0 has no bulk memory), so the rules are ours to define, and under the policy the
       natural ones are the span rules generalised to a range: a copy or a fill carries a span
       witness for its destination (and a copy a second one for its source), the static check
       is @pc ⊔ ⨆ operand labels ⊔ ℓsource ⊑ ℓdestination@, and the run-time obligation is that
       the whole range lies in the named span, which is the bounds check these already do.
       @memory.init@ copies a data segment, a public constant of the module, so its source
       label is 'Low; @data.drop@ has no operands and no observable effect but a later trap
       (TINI). Blocked only on writing it down — the shape is the same as 'IStore'. -}
    IMemCopy :: (ModuleMems m ~ (mem ': mems)) => Instr m pol r l pc lb (('I32 ':~ lv) ': ('I32 ':~ lv') ': ('I32 ':~ lv'') ': s) s
    IMemFill :: (ModuleMems m ~ (mem ': mems)) => Instr m pol r l pc lb (('I32 ':~ lv) ': ('I32 ':~ lv') ': ('I32 ':~ lv'') ': s) s
    IMemInit ::
        (ModuleMems m ~ (mem ': mems)) =>
        Elem 'DataShape (ModuleData m) ->
        Instr m pol r l pc lb (('I32 ':~ lv) ': ('I32 ':~ lv') ': ('I32 ':~ lv'') ': s) s
    IDataDrop :: Elem 'DataShape (ModuleData m) -> Instr m pol r l pc lb s s
    {- Stack management. @select@ /is/ @cond ? a : b@, an explicit dependence on all three
       operands, so the result takes the condition's label too; the two branches' labels are
       allowed to differ and are joined. (Fig. 10 omits T-SELECT; the technical report has it,
       and this is the standard rule.) -}
    IDrop :: Instr m pol r l pc lb (t ': s) s
    ISelect ::
        IsNum t ->
        Instr m pol r l pc lb (('I32 ':~ lc) ': (t ':~ lv) ': (t ':~ lv') ': s) ((t ':~ ((lc :/\ lv) :/\ lv')) ': s)
    {- Locals. SecWasm's locals are /flow-insensitive/ (§5: "the flow-insensitive nature of the
       global and local variables"; the context @C@ of Fig. 10 holds @locals τ*@): a local's
       label is declared once in the @locals@ context and never changes, so a get yields the
       declared label joined with the pc, and a set has to prove that what is written — the
       value's label joined with the context it is written from — may flow into the declared
       one. That premise, @pc ⊔ ℓv ⊑ ℓx@, is what rejects the classic implicit leak
       @(if (secret) (then (local.set $public 1)))@: inside the arm the pc is 'High, so the set
       into a 'Low local has no witness.

       @local.tee@ writes like a set and leaves the /operand/ on the stack, so the value that
       stays is the one that arrived, at its own label — not a re-read of the local. -}
    ILocalGet :: Elem (vt ':~ lx) locals -> Instr m pol r locals pc lb s ((vt ':~ (lx :/\ pc)) ': s)
    ILocalSet ::
        FlowsInto (pc :/\ lv) lx ->
        Elem (vt ':~ lx) locals ->
        Instr m pol r locals pc lb ((vt ':~ lv) ': s) s
    ILocalTee ::
        FlowsInto (pc :/\ lv) lx ->
        Elem (vt ':~ lx) locals ->
        Instr m pol r locals pc lb ((vt ':~ lv) ': s) ((vt ':~ lv) ': s)
    {- Globals: the last store with no label of its own, so a read still takes a free label at
       the access site (under the @⊒ pc@ witness) and a write is unchecked.
       TODO(ifc P1): 'Syntax.Types.GlobalType' is @GlobalType Mutability ValType@ and
       'Validation.Shape.ModuleGlobals' yields it unlabelled. SecWasm's @gt ::= mut? τ@ (Fig. 8)
       is the labelled form, and the rules are then the same flow-insensitive pair as locals:
       @global.get@ yields the declared label joined with @pc@, @global.set@ carries
       @FlowsInto (pc :/\ lv) lx@. Globals are also SecWasm's /attacker model/ — the attacker
       sees the final values of the globals whose label flows to theirs (§3.1) — so global
       labels are the policy's most important part, not something to infer. Blocked on the P0
       question (a labelled 'Validation.Shape.ModuleShape'); until then this is the layer's
       largest hole, and the reason no example writes a global. -}
    IGlobalGet ::
        FlowsInto pc lv ->
        Elem ('GlobalType mut vt) (ModuleGlobals m) ->
        Instr m pol r l pc lb s ((vt ':~ lv) ': s)
    IGlobalSet ::
        Elem ('GlobalType 'Mutable vt) (ModuleGlobals m) ->
        Instr m pol r l pc lb ((vt ':~ lv) ': s) s
    {- Memory (requires the module to declare a memory). These two are where the system departs
       from the paper, and the departure is the point: SecWasm labels memory per byte and
       flow-sensitively, so the label of what a load reads is run-time state and T-LOAD's
       premise @⨆ labels read ⊑ ℓ@ has to be checked dynamically, as a trap (E-LOAD) — the one
       dynamic check in an otherwise static system. Here the module instead /declares/ the
       labelled layout of its memory up front, as a 'Syntax.TypesIFC.MemPolicy' of consecutive
       spans, and each access carries a 'Syntax.TypesIFC.SpanAt' proof naming the span it
       targets. Because a span's label is fixed for the module's lifetime, the label of what a
       load reads is /static/, and the check disappears into the types:

         * T-LOAD becomes @ℓv = ℓspan ⊔ ℓa ⊔ pc@ with no premise left to check at run time. The
           address's label is in the result because /which/ cell is read depends on it.
         * T-STORE keeps its static premise, now against the span's declared label:
           @pc ⊔ ℓa ⊔ ℓv ⊑ ℓspan@, supplied as the 'FlowsInto' field. There is no relabelling of
           the bytes written (that is what flow-insensitivity means here), so unlike the paper a
           public store cannot make secret bytes public again.

       What is left dynamic is only what plain WebAssembly already checks: that the effective
       address really is inside the span the proof names. 'Syntax.TypesIFC.spanBounds' recovers
       the two numbers for it from the witness, and failure is an ordinary out-of-bounds trap
       (TINI, as above). The narrow forms are the same rules; the width changes only how many
       bytes the bounds check covers. -}
    ILoad ::
        (ModuleMems m ~ (mem ': mems)) =>
        SpanAt pol base bytes lspan ->
        IsNum t ->
        MemArg ->
        Instr m pol r l pc lb (('I32 ':~ la) ': s) ((t ':~ ((lspan :/\ la) :/\ pc)) ': s)
    IStore ::
        (ModuleMems m ~ (mem ': mems)) =>
        SpanAt pol base bytes lspan ->
        FlowsInto ((pc :/\ la) :/\ lv) lspan ->
        IsNum t ->
        MemArg ->
        Instr m pol r l pc lb ((t ':~ lv) ': ('I32 ':~ la) ': s) s
    ILoadN ::
        (ModuleMems m ~ (mem ': mems)) =>
        SpanAt pol base bytes lspan ->
        NarrowWidth t ->
        Signedness ->
        MemArg ->
        Instr m pol r l pc lb (('I32 ':~ la) ': s) ((t ':~ ((lspan :/\ la) :/\ pc)) ': s)
    IStoreN ::
        (ModuleMems m ~ (mem ': mems)) =>
        SpanAt pol base bytes lspan ->
        FlowsInto ((pc :/\ la) :/\ lv) lspan ->
        NarrowWidth t ->
        MemArg ->
        Instr m pol r l pc lb ((t ':~ lv) ': ('I32 ':~ la) ': s) s
    {- TODO(ifc P1): calls are absent. 'Syntax.Instructions.ICall' needs
       @Elem ('FuncType ps rs) (ModuleFuncs m)@ with @ps@ and @rs@ over unlabelled 'ValType',
       while the stacks here are over 'LValType'. SecWasm's function type is @τ* →ℓ τ*@
       (Fig. 8): labelled parameters, labelled results, and @ℓ@ the function's pc bound, "an
       upper bound on the information that may flow into the execution of a function". The
       rules: T-CALL requires @pc ⊑ ℓ@ and the argument stack to be a /subtype/ of the
       parameters (the callee runs under @ℓ@, so a call inside a secret branch needs
       @ℓ = 'High@, and then every store and host call in the callee is checked against 'High);
       T-CALL-INDIRECT additionally requires @pc ⊔ ℓidx ⊑ ℓf@. Encoding: the subtyping becomes
       'IRelabel's the elaborator inserts before the call; the pc bound is a field,
       @ICall :: FlowsInto pc ℓ -> Append ps s full -> Elem ('LFuncType ℓ ps rs) (ModuleFuncs m) -> …@;
       and "result labels are @⊒ ℓ@" becomes a well-formedness condition of labelled function
       types, so the callee's results satisfy the caller's @⊒ pc@ invariant for free. Host
       functions take their labelled types from the policy (see "Runtime.Host"). Blocked on the
       P0 structure question. -}

    {- Structured control. Bodies are typed in isolation (@ps -> rs@) within the same frame,
       framed over a polymorphic @s@, and now also under a pc of their own: a block is entered
       at some @pc'@ that the enclosing context may flow into, and everything it leaves behind
       is at least as secret as @pc'@ ('StackAtLeast'). An @if@ raises that pc by the
       condition's label (T-IF), which is what makes the arms' effects invisible to a @pc'@
       observer.

       The pc here is flow-/insensitive/: one pc for a whole block body, fixed at entry.
       SecWasm (§3.3, §4.3) instead keeps a /stack-of-stacks/ @γ@ of pairs @⟨st, pc⟩@, one per
       enclosing block, threaded through the judgment @γ, C ⊢ expr ⊣ γ'@; a branch @br_if i@ on
       a condition labelled @ℓ@ applies @lift(ℓ ⊔ pc)@ to entries @0..i@, and T-BLOCK merges the
       raised pc back when the block ends. That is flow-sensitive: the environment is state, not
       context. The flat scheme costs precision — the code /before/ a raising branch in the same
       block is typed at the raised pc too, where SecWasm keeps it low (Example 6's @expr2@) —
       and buys a great deal: @labels@ stays an environment threaded unchanged, there is no
       @lift@ type family and no 'Elem' into a lifted environment, and the confinement argument
       is structural (a block's body can only touch its own stack segment, by the 'Append'
       framing, and every value it pushes is @⊒ pc@).

       TODO(ifc P2): the elaborator has to /choose/ these pcs, in a pre-pass over the raw body
       before elaborating it:
         @pc(B) = pc(parent B) ⊔ ⨆ { pc(site b) ⊔ ℓ(cond b) | b a br/br_if/br_table/return whose
           exit path leaves or ends at B }@, with an @if@'s arms at @⊒ pc(parent) ⊔ ℓ(cond)@.
       Since @ℓ(cond b)@ comes from the data flow, which depends on the pcs, this is a joint
       fixpoint; over the two-point lattice it converges in a couple of sweeps, and T-LOOP
       already demands such a fixpoint explicitly (@pc ⊑ pc'@, @γ ⊑ γ'@, @st ⊑ st'@).
       TODO(ifc P3): the flow-sensitive upgrade, once the flat scheme works: thread @γ@ in and
       out (@Instr m pol f γin si γout so@), a @Lift ℓ γ@ type family, and elaboration that
       continues after a branch under the lifted environment. Only worth it if a case study is
       rejected by the flat scheme and accepted by the paper's. -}
    IBlock ::
        FlowsInto pc pc' ->
        StackAtLeast pc' rs ->
        Append ps s full ->
        Expr m pol r l pc' ('LabelShape pc' rs ': lb) ps rs ->
        Instr m pol r l pc lb full (rs ++ s)
    ILoop ::
        FlowsInto pc pc' ->
        StackAtLeast pc' ps ->
        Append ps s full ->
        Expr m pol r l pc' ('LabelShape pc' ps ': lb) ps rs ->
        Instr m pol r l pc lb full (rs ++ s)
    IIf ::
        FlowsInto (pc :/\ lv) pc' ->
        StackAtLeast pc' rs ->
        Append ps s full ->
        Expr m pol r l pc' ('LabelShape pc' rs ': lb) ps rs ->
        Expr m pol r l pc' ('LabelShape pc' rs ': lb) ps rs ->
        Instr m pol r l pc lb (('I32 ':~ lv) ': full) (rs ++ s)
    {- Branches. The 'Append' witness gives the branch width; the output (and the stack below
       the operands) is otherwise free. The flow witness is T-BR's @pc ⊑ C.labels[i].pc@ (and
       T-BR-IF's @pc ⊔ ℓcond ⊑ …@, which is what rejects the paper's Example 8), and
       'StackAtLeast' is the premise that what the branch carries out is at least as secret as
       the context it jumps to. @br_table@ types every target and the default at one pc; the
       pre-pass above normalises them to their join. -}
    IBr ::
        FlowsInto pc pcTarget ->
        StackAtLeast pcTarget rs ->
        Append rs s full ->
        Elem ('LabelShape pcTarget rs) labels ->
        Instr m pol r l pc labels full anyOut
    IBrIf ::
        FlowsInto (pc :/\ lv) pcTarget ->
        StackAtLeast pcTarget rs ->
        Append rs s full ->
        Elem ('LabelShape pcTarget rs) labels ->
        Instr m pol r l pc labels (('I32 ':~ lv) ': full) full
    IBrTable ::
        FlowsInto (pc :/\ lv) pcTarget ->
        StackAtLeast pcTarget rs ->
        Append rs s full ->
        [Elem ('LabelShape pcTarget rs) labels] ->
        Elem ('LabelShape pcTarget rs) labels ->
        Instr m pol r l pc labels (('I32 ':~ lv) ': full) anyOut
    {- T-RETURN: the results a @return@ carries out are @⊒ pc@, so a secret context cannot
       return a public value. The paper also requires @pc ⊑ ℓf@, the function's own pc bound;
       @ℓf@ arrives with the labelled frame (the P2 TODO on 'Instr') and has no consumer until
       calls exist, since nothing can yet observe a callee's context. -}
    IReturn :: StackAtLeast pc ret -> Append ret s full -> Instr m pol ret l pc lb full anyOut
    {- Inert -}
    INop :: Instr m pol r l pc lb s s
    IUnreachable :: Instr m pol r l pc lb s anyOut

-- | A labelled instruction sequence: the output shape of each instruction is the input of the next.
data
    Expr
        (mod :: ModuleShape)
        (policy :: MemPolicy)
        (ret :: [LValType])
        (locals :: [LValType])
        (pc :: SecLevel)
        (labels :: [LabelShape])
        (stackIn :: [LValType])
        (stackOut :: [LValType])
    where
    INil :: Expr m pol r l pc lb s s
    (:.) ::
        Instr m pol r l pc lb s1 s2 ->
        Expr m pol r l pc lb s2 s3 ->
        Expr m pol r l pc lb s1 s3

infixr 5 :.

{- | The empty-result forms of block, loop and branch, which need no 'Append' witness and
  whose 'StackAtLeast' premise is trivial. Each still takes the flow witness that raises the
  pc, since that is the whole content of the rule once the results are empty.
  TODO(ifc P2): the general forms (@block@, @loop@, @if_@, @br@, @brIf@, @brTable@, @return_@
  in Abhiroop's version) built their witness from a @KnownAppend@ class; here they want
  'Validation.Shape.appendFromSing' on a @Sing (ps :: [LValType])@, which needs singletons for
  'Syntax.TypesIFC.LValType' and a poly-kinded 'appendFromSing' (its body already is; only the
  signature pins @[ValType]@). Add them with the first labelled example that needs a non-empty
  block result.
-}
block_ ::
    FlowsInto pc pc' ->
    Expr m pol r l pc' ('LabelShape pc' '[] ': lb) '[] '[] ->
    Instr m pol r l pc lb s s
block_ flow = IBlock flow AtLeastNil ANil

loop_ ::
    FlowsInto pc pc' ->
    Expr m pol r l pc' ('LabelShape pc' '[] ': lb) '[] '[] ->
    Instr m pol r l pc lb s s
loop_ flow = ILoop flow AtLeastNil ANil

br_ ::
    FlowsInto pc pcTarget ->
    Elem ('LabelShape pcTarget '[]) labels ->
    Instr m pol r l pc labels s anyOut
br_ flow = IBr flow AtLeastNil ANil

brIf_ ::
    FlowsInto (pc :/\ lv) pcTarget ->
    Elem ('LabelShape pcTarget '[]) labels ->
    Instr m pol r l pc labels (('I32 ':~ lv) ': s) s
brIf_ flow = IBrIf flow AtLeastNil ANil
