/-
The lift-free typing rules on a core of WebAssembly, and a big-step semantics for it.

The core has one value type (a number), local and global variables, and the structured
control flow that the rules are about: blocks, loops and conditionals with parameters and
results, `br`, `br_if` and `br_table`, calls of the module's functions, and a memory whose
cells carry a level, with SecWasm's run-time check on loads. A global may be declared
preserved: it may then be written under a secret pc, and the construct in which the pc became
secret must leave it as it found it, which is checked at run time.

The typing judgment is the paper's `Ls ⊢ e : P | st ⇒ P' | st'` (appendix B, "The Rules"):
`Ls` lists the types of the enclosing labels, innermost first, `P` is the pc stack, and `st`
is the labelled type of the current block's segment of the operand stack. A branch raises the
pcs of the blocks it may leave and no label of a value (no lift), and a `br_if` that is not
taken leaves the values it would have carried at their own labels.
-/

namespace WasmIfc

/-- A security level: public (`L`) or secret (`H`). -/
inductive Lab where
  | L
  | H
  deriving DecidableEq

namespace Lab

/-- `le a b`: information at level `a` may flow to level `b`. -/
def le (a b : Lab) : Prop := a = H → b = H

/-- The least level above both. -/
def join : Lab → Lab → Lab
  | L, L => L
  | _, _ => H

end Lab

/-- A labelled type stack, top first. All values have one type, so a labelled type is its label. -/
abbrev STy := List Lab

/-- A pc stack, the innermost block first. -/
abbrev Pcs := List Lab

/-- `AllGe a st`: the level `a` flows into every label of `st`. -/
def AllGe (a : Lab) (st : STy) : Prop := ∀ l, l ∈ st → Lab.le a l

/-- Pointwise order on lists of levels of the same length (type stacks, pc stacks). -/
inductive SFlows : List Lab → List Lab → Prop where
  | nil : SFlows [] []
  | cons {a b : Lab} {s t : List Lab} : Lab.le a b → SFlows s t → SFlows (a :: s) (b :: t)

/-- `raise a P i` joins `a` to the entries `0` to `i` of `P`. -/
def raise (a : Lab) : Pcs → Nat → Pcs
  | [], _ => []
  | p :: ps, 0 => a.join p :: ps
  | p :: ps, i + 1 => a.join p :: raise a ps i

/-- The entrywise join of two pc stacks. -/
def joinEach : Pcs → Pcs → Pcs
  | p :: ps, q :: qs => p.join q :: joinEach ps qs
  | _, _ => []

/-- Instructions. A block type is the labelled types of its parameters and of its results. -/
inductive Instr where
  | const (n : Nat)
  | binop (f : Nat → Nat → Nat)
  /-- an operation on one value, `ref.is_null` among them -/
  | unop (f : Nat → Nat)
  /-- an operation on two values that traps where it is not defined: a division, a remainder -/
  | partialBinop (f : Nat → Nat → Option Nat)
  /-- an operation on one value that traps where it is not defined: a float truncated to an integer -/
  | partialUnop (f : Nat → Option Nat)
  /-- the top of the stack twice: with `unop` and `ite`, what `br_on_null` is elaborated to -/
  | dup
  | select
  | drop
  | nop
  /-- raise labels of the current segment (the paper's `relabel_results`) -/
  | relabel
  | localGet (i : Nat)
  | localSet (i : Nat)
  | localTee (i : Nat)
  | globalGet (i : Nat)
  | globalSet (i : Nat)
  /-- `load m w lm`: read a value of `w` bytes of the memory `m`, each of which must be labelled at most `lm` -/
  | load (m w : Nat) (lm : Lab)
  /-- `store m w lm`: write the low `w` bytes of a value to the memory `m` and label them `lm` -/
  | store (m w : Nat) (lm : Lab)
  | memSize (m : Nat)
  | memGrow (m : Nat)
  /-- read an entry of the table `x`, as a reference -/
  | tableGet (x : Nat)
  /-- write a reference to an entry of the table `x` -/
  | tableSet (x : Nat)
  /-- write one reference to a range of entries of the table `x` -/
  | tableFill (x : Nat)
  /-- `tableCopy xd xs`: copy a range of entries of the table `xs` to the table `xd` -/
  | tableCopy (xd xs : Nat)
  /-- how many entries the table `x` has -/
  | tableSize (x : Nat)
  /-- add entries to the table `x`, which hold one reference; the old size, or `growFailed` -/
  | tableGrow (x : Nat)
  /-- `tableInit x k`: copy references of the element segment `k` to the table `x` -/
  | tableInit (x k : Nat)
  /-- `elemDrop k`: the element segment `k` is empty from now on -/
  | elemDrop (k : Nat)
  /-- a host call that reads from a descriptor into the first memory -/
  | hostRead
  /-- a host call that writes cells of the first memory to a descriptor -/
  | hostWrite
  /-- a host call that opens a file in a directory, as a new descriptor (`path_open`) -/
  | hostOpen
  /-- `fill m lm`: write one value to a range of cells of the memory `m` and label them `lm` -/
  | fill (m : Nat) (lm : Lab)
  /--
  `copy md ms lm`: copy a range of cells of the memory `ms` to the memory `md`; each keeps its
  level, raised by `lm`
  -/
  | copy (md ms : Nat) (lm : Lab)
  /-- `memInit m k lm`: copy bytes of the data segment `k` into the memory `m` and label them `lm` -/
  | memInit (m k : Nat) (lm : Lab)
  /-- `dataDrop k`: the data segment `k` is empty from now on -/
  | dataDrop (k : Nat)
  /--
  `block keep ps rs body`: where control comes out of the block, by its end or by a branch to
  its label, the globals `keep` must hold what they held at its start, or the run traps
  -/
  | block (keep : List Nat) (ps rs : STy) (body : List Instr)
  | loop (keep : List Nat) (ps rs : STy) (body : List Instr)
  | ite (keep : List Nat) (ps rs : STy) (thn els : List Instr)
  /--
  The iterations of a loop's body. No program contains this instruction: a loop runs it, so that
  what the loop compares is what the globals held when it was first entered.
  -/
  | iter (ps rs : STy) (body : List Instr)
  | br (i : Nat)
  | brIf (i : Nat)
  /-- `brTable ts d`: the targets, and the default one -/
  | brTable (ts : List Nat) (d : Nat)
  /-- `return`: a branch to the function's label, the outermost one -/
  | ret
  | call (i : Nat)
  /-- `return_call`: call a function and return what it returns -/
  | retCall (i : Nat)
  /-- `return_call_indirect`: the indirect call, as a tail call -/
  | retCallIndirect (x : Nat) (ps : STy) (b : Lab) (rs : STy)
  /-- `callIndirect x ps b rs`: call the function an entry of the table `x` names, expected at the type `ps -[b]-> rs` -/
  | callIndirect (x : Nat) (ps : STy) (b : Lab) (rs : STy)
  /-- `callRef ps b rs`: call the function a reference on the stack names, expected at the type `ps -[b]-> rs` -/
  | callRef (ps : STy) (b : Lab) (rs : STy)
  | unreachable
  /-- `throw t k`: throw an exception of tag `t`, which carries `k` values -/
  | throw (t k : Nat)
  /-- `throw_ref`: throw the exception a reference on the stack is to, again -/
  | throwRef
  /--
  `tryTable keep ps rs clauses body`: a block that catches exceptions. A clause is a tag, or
  none for every exception, with the label of the context around the block that it branches
  to, and whether the branch carries a reference to the exception besides (`catch_ref`,
  `catch_all_ref`).
  -/
  | tryTable (keep : List Nat) (ps rs : STy) (clauses : List (Option Nat × Nat × Bool)) (body : List Instr)

/-- A function type: the parameters, the bound on the pc of its callers, and the results. -/
structure FuncTy where
  params : STy
  bound : Lab
  results : STy

/--
The levels of the local variables of the function being typed, those of the global variables,
and the types of the module's functions.
-/
structure Ctx where
  locals : Nat → Lab
  globals : Nat → Lab
  /-- the globals the policy declares preserved (public ones, as the stack pointer of compiled C) -/
  preserved : Nat → Prop
  funcs : List FuncTy
  /-- the level of each table: one level for all its entries, its size included -/
  table : Nat → Lab
  /-- how many values an exception of each tag carries; they are public -/
  tags : List Nat

/--
A clause is typed if its label takes what it catches: the public values of its tag, or nothing,
and one more value if it catches by reference. The reference is public as the values are.
-/
def ClauseOk (C : Ctx) (Ls : List STy) : Option Nat × Nat × Bool → Prop
  | (some t, j, false) => ∃ k target, C.tags[t]? = some k ∧ Ls[j]? = some target ∧ target.length = k
  | (some t, j, true) =>
      ∃ k target, C.tags[t]? = some k ∧ Ls[j]? = some target ∧ target.length = k + 1
  | (none, j, false) => Ls[j]? = some []
  | (none, j, true) => ∃ l, Ls[j]? = some [l]

/--
`Restores C pcEnd after keep`: whether control coming out of a block, a loop or a conditional has
to find the preserved globals as they were at its start. It has to if the pc drops there:
`pcEnd` is the most secret pc of the construct's own entry of the pc stack, and `after` the pc
stack in force after it. Otherwise every preserved global is among those the construct compares.
-/
def Restores (C : Ctx) (pcEnd : Lab) (after : Pcs) (keep : List Nat) : Prop :=
  (∀ q, after.head? = some q → Lab.le pcEnd q) ∨ ∀ i, C.preserved i → i ∈ keep

/--
`Typed C Ls e P st P' st'`: under the labels `Ls`, the sequence `e` takes the pc stack `P` and
the segment `st` to `P'` and `st'`. Each rule types an instruction followed by the rest of its
sequence. The code after a transfer (`br`, `br_table`, `return`, a tail call, `throw`, `unreachable`) is not typed, as the
elaborator does not build its typed form.
-/
inductive Typed (C : Ctx) : List STy → List Instr → Pcs → STy → Pcs → STy → Prop where
  | nil {Ls P st} : Typed C Ls [] P st P st
  | const {Ls rest pc Pr st P' st'} (n : Nat) :
      Typed C Ls rest (pc :: Pr) (pc :: st) P' st' →
      Typed C Ls (.const n :: rest) (pc :: Pr) st P' st'
  | binop {Ls rest pc Pr l0 l1 st P' st'} (f : Nat → Nat → Nat) :
      Typed C Ls rest (pc :: Pr) (((l0.join l1).join pc) :: st) P' st' →
      Typed C Ls (.binop f :: rest) (pc :: Pr) (l0 :: l1 :: st) P' st'
  | unop {Ls rest pc Pr l st P' st'} (f : Nat → Nat) :
      Typed C Ls rest (pc :: Pr) ((l.join pc) :: st) P' st' →
      Typed C Ls (.unop f :: rest) (pc :: Pr) (l :: st) P' st'
  /-- An operation that may trap is typed as one that does not: whether it traps is not observed. -/
  | partialBinop {Ls rest pc Pr l0 l1 st P' st'} (f : Nat → Nat → Option Nat) :
      Typed C Ls rest (pc :: Pr) (((l0.join l1).join pc) :: st) P' st' →
      Typed C Ls (.partialBinop f :: rest) (pc :: Pr) (l0 :: l1 :: st) P' st'
  | partialUnop {Ls rest pc Pr l st P' st'} (f : Nat → Option Nat) :
      Typed C Ls rest (pc :: Pr) ((l.join pc) :: st) P' st' →
      Typed C Ls (.partialUnop f :: rest) (pc :: Pr) (l :: st) P' st'
  | dup {Ls rest P l st P' st'} :
      Typed C Ls rest P (l :: l :: st) P' st' →
      Typed C Ls (.dup :: rest) P (l :: st) P' st'
  | select {Ls rest pc Pr lc l1 l2 st P' st'} :
      Typed C Ls rest (pc :: Pr) ((pc.join (lc.join (l1.join l2))) :: st) P' st' →
      Typed C Ls (.select :: rest) (pc :: Pr) (lc :: l1 :: l2 :: st) P' st'
  | drop {Ls rest P l st P' st'} :
      Typed C Ls rest P st P' st' →
      Typed C Ls (.drop :: rest) P (l :: st) P' st'
  | nop {Ls rest P st P' st'} :
      Typed C Ls rest P st P' st' →
      Typed C Ls (.nop :: rest) P st P' st'
  | relabel {Ls rest P st st1 P' st'} :
      SFlows st st1 →
      Typed C Ls rest P st1 P' st' →
      Typed C Ls (.relabel :: rest) P st P' st'
  | localGet {Ls rest pc Pr st P' st'} (i : Nat) :
      Typed C Ls rest (pc :: Pr) (((C.locals i).join pc) :: st) P' st' →
      Typed C Ls (.localGet i :: rest) (pc :: Pr) st P' st'
  | localSet {Ls rest pc Pr l st P' st'} (i : Nat) :
      Lab.le pc (C.locals i) → Lab.le l (C.locals i) →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.localSet i :: rest) (pc :: Pr) (l :: st) P' st'
  | localTee {Ls rest pc Pr l st P' st'} (i : Nat) :
      Lab.le pc (C.locals i) → Lab.le l (C.locals i) →
      Typed C Ls rest (pc :: Pr) (l :: st) P' st' →
      Typed C Ls (.localTee i :: rest) (pc :: Pr) (l :: st) P' st'
  | globalGet {Ls rest pc Pr st P' st'} (i : Nat) :
      Typed C Ls rest (pc :: Pr) (((C.globals i).join pc) :: st) P' st' →
      Typed C Ls (.globalGet i :: rest) (pc :: Pr) st P' st'
  | globalSet {Ls rest pc Pr l st P' st'} (i : Nat) :
      ¬ C.preserved i → Lab.le pc (C.globals i) → Lab.le l (C.globals i) →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.globalSet i :: rest) (pc :: Pr) (l :: st) P' st'
  /--
  A write to a preserved global: the pc need not flow into the global, and the value may be as
  secret as the pc. Under a public pc this is the ordinary rule.
  -/
  | globalSetPreserved {Ls rest pc Pr l st P' st'} (i : Nat) :
      C.preserved i → Lab.le l pc →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.globalSet i :: rest) (pc :: Pr) (l :: st) P' st'
  | load {Ls rest pc Pr la st P' st'} (m w : Nat) (lm : Lab) :
      Typed C Ls rest (pc :: Pr) (((la.join lm).join pc) :: st) P' st' →
      Typed C Ls (.load m w lm :: rest) (pc :: Pr) (la :: st) P' st'
  | store {Ls rest pc Pr lv la st P' st'} (m w : Nat) (lm : Lab) :
      Lab.le ((pc.join la).join lv) lm →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.store m w lm :: rest) (pc :: Pr) (lv :: la :: st) P' st'
  /-- `memory.fill`: the cells get a level at least the pc's, the count's, the value's and the address's. -/
  | fill {Ls rest pc Pr ln lv ld st P' st'} (m : Nat) (lm : Lab) :
      Lab.le (pc.join (ln.join (lv.join ld))) lm →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.fill m lm :: rest) (pc :: Pr) (ln :: lv :: ld :: st) P' st'
  /--
  `memory.copy`, within a memory or between two: each copied cell keeps its own level, raised by
  one that is at least the pc's, the count's and the two addresses'. No check is made: the
  levels move with the values.
  -/
  | copy {Ls rest pc Pr ln lsrc ld st P' st'} (md ms : Nat) (lm : Lab) :
      Lab.le (pc.join (ln.join (lsrc.join ld))) lm →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.copy md ms lm :: rest) (pc :: Pr) (ln :: lsrc :: ld :: st) P' st'
  /-- What is read from the table is as secret as the table, the index and the pc. -/
  | tableGet {Ls rest pc Pr li st P' st'} (x : Nat) :
      Typed C Ls rest (pc :: Pr) ((pc.join (li.join (C.table x))) :: st) P' st' →
      Typed C Ls (.tableGet x :: rest) (pc :: Pr) (li :: st) P' st'
  /-- A write to the table needs the pc, the index and the value to flow into the table's level. -/
  | tableSet {Ls rest pc Pr lv li st P' st'} (x : Nat) :
      Lab.le (pc.join (li.join lv)) (C.table x) →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.tableSet x :: rest) (pc :: Pr) (lv :: li :: st) P' st'
  /--
  A host call is made under a public pc with public arguments: where to put what is read, how
  much at most, the descriptor, and where to put how much was read. What it stores is labelled
  at run time, with the descriptor's level.
  -/
  | hostRead {Ls rest Pr st P' st'} :
      Typed C Ls rest (Lab.L :: Pr) st P' st' →
      Typed C Ls (.hostRead :: rest) (Lab.L :: Pr) (Lab.L :: Lab.L :: Lab.L :: Lab.L :: st) P' st'
  /-- The cells a host call takes are checked at run time against the descriptor's level. -/
  | hostWrite {Ls rest Pr st P' st'} :
      Typed C Ls rest (Lab.L :: Pr) st P' st' →
      Typed C Ls (.hostWrite :: rest) (Lab.L :: Pr) (Lab.L :: Lab.L :: Lab.L :: st) P' st'
  /--
  Opening a file is a host call: under a public pc, with public arguments (where to put the new
  descriptor, the open flags, the length and the address of the name, the directory's
  descriptor). Its status is public. The name's bytes are checked at run time to be public.
  -/
  | hostOpen {Ls rest Pr st P' st'} :
      Typed C Ls rest (Lab.L :: Pr) (Lab.L :: st) P' st' →
      Typed C Ls (.hostOpen :: rest) (Lab.L :: Pr)
        (Lab.L :: Lab.L :: Lab.L :: Lab.L :: Lab.L :: st) P' st'
  /-- `memory.init`: as `memory.fill`, with the segment's bytes for the value. A segment is public. -/
  | memInit {Ls rest pc Pr ln lsrc ld st P' st'} (m k : Nat) (lm : Lab) :
      Lab.le (pc.join (ln.join (lsrc.join ld))) lm →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.memInit m k lm :: rest) (pc :: Pr) (ln :: lsrc :: ld :: st) P' st'
  /-- `data.drop` has no premise, under any pc. -/
  | dataDrop {Ls rest P st P' st'} (k : Nat) :
      Typed C Ls rest P st P' st' →
      Typed C Ls (.dataDrop k :: rest) P st P' st'
  /-- `table.fill`: as `table.set`, with the count. -/
  | tableFill {Ls rest pc Pr ln lv li st P' st'} (x : Nat) :
      Lab.le (pc.join (ln.join (lv.join li))) (C.table x) →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.tableFill x :: rest) (pc :: Pr) (ln :: lv :: li :: st) P' st'
  /--
  `table.copy`: the pc, the count, the two indices and the level of the table copied from flow
  into the level of the table copied to.
  -/
  | tableCopy {Ls rest pc Pr ln lsrc ld st P' st'} (xd xs : Nat) :
      Lab.le (pc.join (ln.join (lsrc.join (ld.join (C.table xs))))) (C.table xd) →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.tableCopy xd xs :: rest) (pc :: Pr) (ln :: lsrc :: ld :: st) P' st'
  /-- `table.size`: the size of the table is as secret as the table. -/
  | tableSize {Ls rest pc Pr st P' st'} (x : Nat) :
      Typed C Ls rest (pc :: Pr) (pc.join (C.table x) :: st) P' st' →
      Typed C Ls (.tableSize x :: rest) (pc :: Pr) st P' st'
  /-- `table.grow` is a write to the table, and its result is as secret as the table. -/
  | tableGrow {Ls rest pc Pr ln lv st P' st'} (x : Nat) :
      Lab.le (pc.join (ln.join lv)) (C.table x) →
      Typed C Ls rest (pc :: Pr) (pc.join (C.table x) :: st) P' st' →
      Typed C Ls (.tableGrow x :: rest) (pc :: Pr) (ln :: lv :: st) P' st'
  /-- `table.init`: as `table.fill`, with the segment's references for the value. A segment is public. -/
  | tableInit {Ls rest pc Pr ln lsrc ld st P' st'} (x k : Nat) :
      Lab.le (pc.join (ln.join (lsrc.join ld))) (C.table x) →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.tableInit x k :: rest) (pc :: Pr) (ln :: lsrc :: ld :: st) P' st'
  /-- `elem.drop` has no premise, under any pc. -/
  | elemDrop {Ls rest P st P' st'} (k : Nat) :
      Typed C Ls rest P st P' st' →
      Typed C Ls (.elemDrop k :: rest) P st P' st'
  /-- The size of a memory is public. -/
  | memSize {Ls rest pc Pr st P' st'} (m : Nat) :
      Typed C Ls rest (pc :: Pr) (pc :: st) P' st' →
      Typed C Ls (.memSize m :: rest) (pc :: Pr) st P' st'
  /-- A memory grows only under a public pc, by a public amount, so that its size stays public. -/
  | memGrow {Ls rest pc Pr l st P' st'} (m : Nat) :
      Lab.le (pc.join l) Lab.L →
      Typed C Ls rest (pc :: Pr) (pc :: st) P' st' →
      Typed C Ls (.memGrow m :: rest) (pc :: Pr) (l :: st) P' st'
  /-- The results are at least the pc at which the body starts (the paper's Property (E)). -/
  | block {Ls rest pc Pr tin keep ps rs body p P1 st P' st'} :
      SFlows tin ps → AllGe pc rs → Restores C p P1 keep →
      Typed C (rs :: Ls) body (pc :: pc :: Pr) ps (p :: P1) rs →
      Typed C Ls rest P1 (rs ++ st) P' st' →
      Typed C Ls (.block keep ps rs body :: rest) (pc :: Pr) (tin ++ st) P' st'
  /-- The body starts at a pc `pcL` of the rule's choice, and must end at most there. -/
  | loop {Ls rest pc Pr pcL tin keep ps rs body p P1 st P' st'} :
      Lab.le pc pcL → Lab.le p pcL → SFlows tin ps → AllGe pcL rs → Restores C pcL P1 keep →
      Typed C (ps :: Ls) body (pcL :: pc :: Pr) ps (p :: P1) rs →
      Typed C Ls rest P1 (rs ++ st) P' st' →
      Typed C Ls (.loop keep ps rs body :: rest) (pc :: Pr) (tin ++ st) P' st'
  /--
  The iterations of a loop's body, as the loop's rule types them: the body is typed under the
  loop's label, and the iterations stand where a block's body would, under a label that
  nothing branches to. The code after them is not typed.
  -/
  | iter {Ls l0 rest pcL Pb ps rs body p P1} :
      Lab.le p pcL → AllGe pcL rs →
      Typed C (ps :: Ls) body (pcL :: Pb) ps (p :: P1) rs →
      Typed C (l0 :: Ls) (.iter ps rs body :: rest) (pcL :: Pb) ps (pcL :: P1) rs
  | ite {Ls rest pc Pr l tin keep ps rs thn els p1 P1 p2 P2 st P' st'} :
      SFlows tin ps → AllGe (pc.join l) rs → Restores C (p1.join p2) (joinEach P1 P2) keep →
      Typed C (rs :: Ls) thn (pc.join l :: pc :: Pr) ps (p1 :: P1) rs →
      Typed C (rs :: Ls) els (pc.join l :: pc :: Pr) ps (p2 :: P2) rs →
      Typed C Ls rest (joinEach P1 P2) (rs ++ st) P' st' →
      Typed C Ls (.ite keep ps rs thn els :: rest) (pc :: Pr) (l :: (tin ++ st)) P' st'
  | br {Ls rest pc Pr i rs carried st stAny} :
      Ls[i]? = some rs → AllGe pc rs → SFlows carried rs →
      Typed C Ls (.br i :: rest) (pc :: Pr) (carried ++ st) (raise pc (pc :: Pr) i) stAny
  /-- Not taken, the carried values keep their own labels. -/
  | brIf {Ls rest pc Pr l i rs carried st P' st'} :
      Ls[i]? = some rs → AllGe (pc.join l) rs → SFlows carried rs →
      Typed C Ls rest (raise (pc.join l) (pc :: Pr) i) (carried ++ st) P' st' →
      Typed C Ls (.brIf i :: rest) (pc :: Pr) (l :: (carried ++ st)) P' st'
  /-- The repaired rule: the pcs are raised down to a depth `k` that no target exceeds. -/
  | brTable {Ls rest pc Pr l ts d k rs carried st stAny} :
      (∀ t, t ∈ d :: ts → Ls[t]? = some rs ∧ t ≤ k) → AllGe (pc.join l) rs → SFlows carried rs →
      Typed C Ls (.brTable ts d :: rest) (pc :: Pr) (l :: (carried ++ st))
        (raise (pc.join l) (pc :: Pr) k) stAny
  /-- `return` is typed as the branch to the outermost label, which raises every pc. -/
  | ret {Ls rest pc Pr rs carried st stAny} :
      Ls[Ls.length - 1]? = some rs → AllGe pc rs → SFlows carried rs →
      Typed C Ls (.ret :: rest) (pc :: Pr) (carried ++ st)
        (raise pc (pc :: Pr) (Ls.length - 1)) stAny
  /-- The caller's pc flows into the callee's bound. The arguments keep their own labels, below the parameters'. -/
  | call {Ls rest pc Pr i ft targs st P' st'} :
      C.funcs[i]? = some ft → Lab.le pc ft.bound → SFlows targs ft.params →
      Typed C Ls rest (pc :: Pr) (ft.results ++ st) P' st' →
      Typed C Ls (.call i :: rest) (pc :: Pr) (targs ++ st) P' st'
  /--
  A tail call is typed as the call followed by the `return` it stands for: the premises of the
  call, then those of `return` on what the callee returns, which flows into the function's
  results.
  -/
  | retCall {Ls rest pc Pr i ft ret targs st stAny} :
      C.funcs[i]? = some ft → Lab.le pc ft.bound → SFlows targs ft.params →
      Ls[Ls.length - 1]? = some ret → AllGe pc ret → SFlows ft.results ret →
      Typed C Ls (.retCall i :: rest) (pc :: Pr) (targs ++ st)
        (raise pc (pc :: Pr) (Ls.length - 1)) stAny
  /--
  The pc, the level of the table index and the level of the table flow into the bound of the
  expected type, whose results are at least its bound (the type is well formed, as the paper's
  rule for functions asks of every function type).
  -/
  | callIndirect {Ls rest pc Pr l x ps b rs targs st P' st'} :
      Lab.le (pc.join (l.join (C.table x))) b → AllGe b rs → SFlows targs ps →
      Typed C Ls rest (pc :: Pr) (rs ++ st) P' st' →
      Typed C Ls (.callIndirect x ps b rs :: rest) (pc :: Pr) (l :: (targs ++ st)) P' st'
  /-- An indirect tail call: the premises of the indirect call, then those of `return`. -/
  | retCallIndirect {Ls rest pc Pr l x ps b rs ret targs st stAny} :
      Lab.le (pc.join (l.join (C.table x))) b → AllGe b rs → SFlows targs ps →
      Ls[Ls.length - 1]? = some ret → AllGe pc ret → SFlows rs ret →
      Typed C Ls (.retCallIndirect x ps b rs :: rest) (pc :: Pr) (l :: (targs ++ st))
        (raise pc (pc :: Pr) (Ls.length - 1)) stAny
  /--
  A call through a reference is an indirect call without the table: the reference decides the
  callee as a table index does, so its level is in the premise on the bound.
  -/
  | callRef {Ls rest pc Pr l ps b rs targs st P' st'} :
      Lab.le (pc.join l) b → AllGe b rs → SFlows targs ps →
      Typed C Ls rest (pc :: Pr) (rs ++ st) P' st' →
      Typed C Ls (.callRef ps b rs :: rest) (pc :: Pr) (l :: (targs ++ st)) P' st'
  | unreachable {Ls rest P st stAny} :
      Typed C Ls (.unreachable :: rest) P st P stAny
  /-- An exception is thrown only under a public pc, and carries public values. -/
  | throw {Ls rest Pr t k args st stAny} :
      C.tags[t]? = some k → args.length = k → (∀ l, l ∈ args → l = Lab.L) →
      Typed C Ls (.throw t k :: rest) (Lab.L :: Pr) (args ++ st) (Lab.L :: Pr) stAny
  /-- An exception is thrown again only under a public pc, from a public reference. -/
  | throwRef {Ls rest Pr st stAny} :
      Typed C Ls (.throwRef :: rest) (Lab.L :: Pr) (Lab.L :: st) (Lab.L :: Pr) stAny
  /--
  A `try_table` is typed only under a public pc, and otherwise as a block. A clause branches
  under that pc, so it raises none.
  -/
  | tryTable {Ls rest Pr tin keep ps rs clauses body p P1 st P' st'} :
      SFlows tin ps → Restores C p P1 keep → (∀ c, c ∈ clauses → ClauseOk C Ls c) →
      Typed C (rs :: Ls) body (Lab.L :: Lab.L :: Pr) ps (p :: P1) rs →
      Typed C Ls rest P1 (rs ++ st) P' st' →
      Typed C Ls (.tryTable keep ps rs clauses body :: rest) (Lab.L :: Pr) (tin ++ st) P' st'

/--
A function: its type, the levels of its local variables that are not parameters, the globals
that must hold at its return what they held at the call, and its body.
-/
structure Func where
  ty : FuncTy
  extra : List Lab
  keep : List Nat
  body : List Instr

/--
The levels of a function's local variables. Local `i` is the `i`-th parameter counted from the
top of the caller's stack, then the other locals in order; a local the function does not
declare is public. (WebAssembly numbers the parameters from the bottom. The order plays no
part in the proofs.)
-/
def Func.locals (f : Func) : Nat → Lab := fun i => ((f.ty.params ++ f.extra)[i]?).getD Lab.L

/-- The context in which the body of `f` is typed. -/
def Ctx.enter (C : Ctx) (f : Func) : Ctx := { C with locals := f.locals }

/--
A module is well typed if each function has the type the context gives it and its body is
typed as the paper's rule for functions says: under the one label of the function, whose type
is the result type, from the empty segment, at the function's bound. If the pc may be secret
when the function returns, every preserved global is among those compared at the return.
-/
def WellTyped (C : Ctx) (F : List Func) : Prop :=
  ∀ (i : Nat) (f : Func), F[i]? = some f →
    C.funcs[i]? = some f.ty ∧
      ∃ p, Typed (C.enter f) [f.ty.results] f.body [f.ty.bound] [] [p] f.ty.results ∧
        (p = Lab.L ∨ ∀ j, C.preserved j → j ∈ f.keep)

/--
The values of the local and of the global variables, and the memories: each byte's value and
level, how many bytes each memory has, and how many it may grow to.
-/
structure State where
  loc : Nat → Nat
  glob : Nat → Nat
  /-- the memories: the byte at an address of a memory, and its level -/
  mem : Nat → Nat → Nat
  lab : Nat → Nat → Lab
  /-- the tables: an entry of a table names a function or is null -/
  tbl : Nat → Nat → Option Nat
  /-- how many entries each table has, and how many it may grow to -/
  tsize : Nat → Nat
  tcap : Nat → Nat
  /-- the element segments, of references; a dropped one is empty -/
  elems : Nat → List (Option Nat)
  /-- how many bytes each memory has, and how many it may grow to -/
  size : Nat → Nat
  cap : Nat → Nat
  /-- the level of each channel of the host: a stream, a directory, a file -/
  chan : Nat → Lab
  /-- what has been written to each channel, the latest first -/
  out : Nat → List Nat
  /-- what is left to read from each channel -/
  inp : Nat → List Nat
  /-- the data segments; a dropped one is empty -/
  segs : Nat → List Nat
  /-- the exceptions kept for the references to them: reference `i + 1` is to the `i`-th -/
  exns : List (Nat × List Nat)
  /-- the descriptor table: the channel each open descriptor is to -/
  fdt : Nat → Option Nat
  /-- the names of the files in each directory; a directory is a channel -/
  names : Nat → List (List Nat)
  /-- the channel of the file with a name in a directory -/
  file : Nat → List Nat → Nat

/-- Two states have the same table `x`: its entries, its size and its limit. -/
def State.sameTable (s t : State) (x : Nat) : Prop :=
  s.tbl x = t.tbl x ∧ s.tsize x = t.tsize x ∧ s.tcap x = t.tcap x

theorem State.sameTable.symm {s t : State} {x : Nat} (h : s.sameTable t x) : t.sameTable s x :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem State.sameTable.trans {s t u : State} {x : Nat} (h1 : s.sameTable t x)
    (h2 : t.sameTable u x) : s.sameTable u x :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

/-- Two states have the same descriptor table and the same names of files in every directory. -/
def State.sameHost (s t : State) : Prop := s.fdt = t.fdt ∧ s.names = t.names ∧ s.file = t.file

theorem State.sameHost.symm {s t : State} (h : s.sameHost t) : t.sameHost s :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem State.sameHost.trans {s t u : State} (h1 : s.sameHost t) (h2 : t.sameHost u) :
    s.sameHost u :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

/-- The exceptions a state keeps for the references to them carry what their tags say. -/
def ExnOk (C : Ctx) (s : State) : Prop := ∀ e, e ∈ s.exns → C.tags[e.1]? = some e.2.length

def State.setLoc (s : State) (i v : Nat) : State :=
  { s with loc := fun j => if j = i then v else s.loc j }

def State.setGlob (s : State) (i v : Nat) : State :=
  { s with glob := fun j => if j = i then v else s.glob j }

/-- Write a cell and give it a level. -/
def State.setMem (s : State) (m a v : Nat) (l : Lab) : State :=
  { s with mem := fun y x => if y = m ∧ x = a then v else s.mem y x,
           lab := fun y x => if y = m ∧ x = a then l else s.lab y x }

/-- A table entry as a value: zero for null, and the function's index plus one. -/
def refOf : Option Nat → Nat
  | none => 0
  | some i => i + 1

def ofRef : Nat → Option Nat
  | 0 => none
  | i + 1 => some i

/-- The state with the entries of the table `x` replaced. -/
def State.withTbl (s : State) (x : Nat) (entries : Nat → Option Nat) : State :=
  { s with tbl := fun y => if y = x then entries else s.tbl y }

/-- Write the entry `e` at `c` of the table `x`. -/
def State.setTbl (s : State) (x c : Nat) (e : Option Nat) : State :=
  s.withTbl x (fun j => if j = c then e else s.tbl x j)

/-- Write the entry `e` to the `n` entries from `c` of the table `x`. -/
def State.fillTbl (s : State) (x c : Nat) (e : Option Nat) (n : Nat) : State :=
  s.withTbl x (fun j => if c ≤ j ∧ j < c + n then e else s.tbl x j)

/-- Copy the `n` entries from `a` of the table `xs` to those from `d` of the table `xd`. -/
def State.copyTbl (s : State) (xd xs d a n : Nat) : State :=
  s.withTbl xd (fun j => if d ≤ j ∧ j < d + n then s.tbl xs (a + (j - d)) else s.tbl xd j)

/-- Copy the `n` references from `a` of the element segment `k` to the entries from `d` of the table `x`. -/
def State.initTbl (s : State) (x k d a n : Nat) : State :=
  s.withTbl x (fun j => if d ≤ j ∧ j < d + n then ((s.elems k)[a + (j - d)]?).getD none else s.tbl x j)

def State.dropElem (s : State) (k : Nat) : State :=
  { s with elems := fun j => if j = k then [] else s.elems j }

/-- The function an entry of the table `x` names: none if it is null or beyond the table. -/
def State.entry (s : State) (x c : Nat) : Option Nat := if c < s.tsize x then s.tbl x c else none

/-- Write `v` to the `n` cells from `a` of the memory `m`, and give them the level `l`. -/
def State.fill (s : State) (m a v n : Nat) (l : Lab) : State :=
  { s with mem := fun y x => if y = m ∧ a ≤ x ∧ x < a + n then v else s.mem y x,
           lab := fun y x => if y = m ∧ a ≤ x ∧ x < a + n then l else s.lab y x }

/--
Copy the `n` cells from `a` of the memory `ms` to those from `d` of the memory `md`: each value
with its level, raised by `l`.
-/
def State.copy (s : State) (md ms d a n : Nat) (l : Lab) : State :=
  { s with mem := fun y x => if y = md ∧ d ≤ x ∧ x < d + n then s.mem ms (a + (x - d)) else s.mem y x,
           lab := fun y x => if y = md ∧ d ≤ x ∧ x < d + n then l.join (s.lab ms (a + (x - d)))
                             else s.lab y x }

/-- Write the values `vs` to the cells from `a` of the memory `m`, and give them the level `l`. -/
def State.put (s : State) (m a : Nat) (vs : List Nat) (l : Lab) : State :=
  { s with mem := fun y x => if y = m ∧ a ≤ x ∧ x < a + vs.length then (vs[x - a]?).getD 0 else s.mem y x,
           lab := fun y x => if y = m ∧ a ≤ x ∧ x < a + vs.length then l else s.lab y x }

/-- Take `k` values off what is left to read from the descriptor `fd`. -/
def State.consume (s : State) (fd k : Nat) : State :=
  { s with inp := fun d => if d = fd then (s.inp fd).drop k else s.inp d }

/-- The value of the `w` bytes from `a` of the memory `m`, the first the least significant. -/
def State.word (s : State) (m : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | a, w + 1 => s.mem m a + 256 * s.word m (a + 1) w

/-- The low `w` bytes of a value, the least significant first. -/
def bytesOf (v : Nat) : Nat → List Nat
  | 0 => []
  | w + 1 => v % 256 :: bytesOf (v / 256) w

def State.dropSeg (s : State) (k : Nat) : State :=
  { s with segs := fun j => if j = k then [] else s.segs j }

/-- The `k` cells from `a` of the first memory, which is the one the host reads and writes. -/
def State.cells (s : State) (a k : Nat) : List Nat := (List.range k).map (fun i => s.mem 0 (a + i))

/-- Write the values `vs` to the descriptor `fd`. -/
def State.emit (s : State) (fd : Nat) (vs : List Nat) : State :=
  { s with out := fun d => if d = fd then vs ++ s.out d else s.out d }

/-- The status of a host call that found no file of the name it was given. -/
def noEntry : Nat := 44

/-- The descriptor a newly opened file gets: the least from 3 on that the table does not have. -/
def State.fresh (s : State) (d : Nat) : Prop :=
  3 ≤ d ∧ s.fdt d = none ∧ ∀ j, 3 ≤ j → j < d → s.fdt j ≠ none

/--
Open the file named `x` in the directory `c` as the descriptor `d`. A name that the directory
does not have is added to it, and its file starts with nothing to read and nothing written.
-/
def State.openAt (s : State) (c : Nat) (x : List Nat) (d : Nat) : State :=
  { s with fdt := fun j => if j = d then some (s.file c x) else s.fdt j,
           names := fun k => if k = c ∧ x ∉ s.names c then x :: s.names c else s.names k,
           inp := fun k => if k = s.file c x ∧ x ∉ s.names c then [] else s.inp k,
           out := fun k => if k = s.file c x ∧ x ∉ s.names c then [] else s.out k }

/-- What `memory.grow` gives when the memory cannot grow. -/
def growFailed : Nat := 0xFFFFFFFF

/--
`memory.grow` of the memory `m` by `d` cells: the old size and the memory with `d` more cells,
which are zero and public, or `growFailed` and the memory as it was, if it would exceed its
limit.
-/
def State.grow (s : State) (m d : Nat) : Nat × State :=
  if s.size m + d ≤ s.cap m then
    (s.size m, { s with size := fun y => if y = m then s.size m + d else s.size y,
                        mem := fun y x => if y = m ∧ s.size m ≤ x then 0 else s.mem y x,
                        lab := fun y x => if y = m ∧ s.size m ≤ x then Lab.L else s.lab y x })
  else (growFailed, s)

/--
`table.grow` by `d` entries that hold `e`: the old size and the larger table, or `growFailed`
and the table as it was, if it would exceed its limit.
-/
def State.growTbl (s : State) (x d : Nat) (e : Option Nat) : Nat × State :=
  if s.tsize x + d ≤ s.tcap x then
    (s.tsize x, { s with tsize := fun y => if y = x then s.tsize x + d else s.tsize y,
                         tbl := fun y => if y = x then (fun j => if s.tsize x ≤ j then e else s.tbl x j)
                                         else s.tbl y })
  else (growFailed, s)

/-- `Kept keep s t`: the globals `keep` hold in `t` what they held in `s`. -/
def Kept (keep : List Nat) (s t : State) : Prop := ∀ i, i ∈ keep → t.glob i = s.glob i

/--
How a sequence ends: at its end, with the current segment of the stack, by a branch to the
`i`-th enclosing label with the values the branch carries, or by an exception of tag `t` with
the values it carries, which nothing in the sequence caught.
-/
inductive Out where
  | normal (σ : List Nat) (s : State)
  | br (i : Nat) (w : List Nat) (s : State)
  | exn (t : Nat) (w : List Nat) (s : State)
  /--
  An exception that left the callee of a tail call. The function that made the tail call is
  gone by then, so no `try_table` of its own catches it: it passes them all, and is an
  ordinary exception again for whoever called the function.
  -/
  | tailExn (t : Nat) (w : List Nat) (s : State)

def Out.state : Out → State
  | .normal _ s => s
  | .br _ _ s => s
  | .exn _ _ s => s
  | .tailExn _ _ s => s

def Out.isBr : Out → Prop
  | .normal _ _ => False
  | .br _ _ _ => True
  | .exn _ _ _ => False
  | .tailExn _ _ _ => False

/-- The exception a function's body ends by, if it does: its own or that of a tail call's callee. -/
def Out.thrown : Out → Option (Nat × List Nat × State)
  | .exn t w s => some (t, w, s)
  | .tailExn t w s => some (t, w, s)
  | _ => none

/-- What a block continues with after its body: the body's results, or the values of a branch to its own label. -/
def Out.lands : Out → Option (List Nat × State)
  | .normal σ s => some (σ, s)
  | .br 0 w s => some (w, s)
  | .br (_ + 1) _ _ => none
  | .exn _ _ _ => none
  | .tailExn _ _ _ => none

/-- A branch past the block, as the block's own outcome; an exception passes a block as it is. -/
def Out.exits : Out → Option Out
  | .br (i + 1) w s => some (.br i w s)
  | .exn t w s => some (.exn t w s)
  | .tailExn t w s => some (.tailExn t w s)
  | _ => none

/--
The first clause for an exception of tag `t`: the label it branches to, whether the branch
carries the exception's values, and whether it carries a reference to the exception.
-/
def catches : List (Option Nat × Nat × Bool) → Nat → Option (Nat × Bool × Bool)
  | [], _ => none
  | (some t', j, r) :: cs, t => if t' = t then some (j, true, r) else catches cs t
  | (none, j, r) :: _, _ => some (j, false, r)

/--
What a clause hands to its label for an exception of tag `t` with the values `w`, and the state
then: the values if the clause is for the tag, and for a clause by reference a new reference
on top of them, for which the state keeps the exception.
-/
def State.handed (s : State) (t : Nat) (w : List Nat) (carry : Bool) : Bool → List Nat × State
  | false => (if carry then w else [], s)
  | true => ((s.exns.length + 1) :: (if carry then w else []),
      { s with exns := s.exns ++ [(t, w)] })

/--
A body's outcome as its `try_table` sees it: an exception that a clause catches is a branch to
the clause's label, counted from inside the block.
-/
def Out.caught (cs : List (Option Nat × Nat × Bool)) : Out → Out
  | .exn t w s =>
    match catches cs t with
    | some (j, carry, r) => .br (j + 1) (s.handed t w carry r).1 (s.handed t w carry r).2
    | none => .exn t w s
  | o => o

/-- The target a `br_table` selects. -/
def tableTarget (ts : List Nat) (d c : Nat) : Nat := (ts[c]?).getD d

/-- The local variables of a new activation: the arguments, top first, and zeros. -/
def frame (args : List Nat) : Nat → Nat := fun i => (args[i]?).getD 0

/--
`Eval F n ls e σ s o`: in the module `F`, with enclosing labels of arities `ls`, the sequence
`e` on the segment `σ` and the state `s` ends as `o`. The semantics is big-step, and `n` is
the size of the derivation. A block's body runs on the block's parameters alone; what lies
below them on the stack waits for the body's results. A call runs the callee's body on an
empty segment with its own local variables, and the caller's are as before when it returns.
A trap is the absence of a rule: `unreachable` has none, an operation that is not defined on
its operands (a division by zero) has none, a `load` and a `store` have one only
if their bytes are within the memory, an instruction on the table only if the entries it
names are within the table, and a `load` only if, besides, the level of every byte
it reads flows into the level the load declares (SecWasm's run-time check), and an
indirect call only if the table entry names a function with the expected parameters and
results whose bound is at least the expected one (SecWasm's other run-time check). A block,
a loop and a conditional go on only if the globals they name hold what they held at the
construct's start (`Kept`), and so does a call for the globals its callee names. A branch
further out skips the comparison of the constructs it leaves.

An exception leaves the blocks and the calls it passes without their comparisons, and the
caller's local variables are its own again. The exception of a tail call's callee is not
offered to the clauses of the function that made the tail call (`Out.tailExn`). A `try_table` is a block whose body's outcome is
first looked up in its clauses (`Out.caught`).

A loop runs the iterations of its body (`iter`) as a block runs its body, so the state it
compares with is the one at its first entry. The iterations are evaluated under the labels of
the loop's place, with one in front that nothing branches to; the body sees the loop's label
there instead.
-/
inductive Eval (F : List Func) : Nat → List Nat → List Instr → List Nat → State → Out → Prop where
  | nil {ls σ s} : Eval F 0 ls [] σ s (.normal σ s)
  | const {n ls rest σ s o} (v : Nat) :
      Eval F n ls rest (v :: σ) s o → Eval F (n + 1) ls (.const v :: rest) σ s o
  | binop {n ls rest a b σ s o} (f : Nat → Nat → Nat) :
      Eval F n ls rest (f b a :: σ) s o → Eval F (n + 1) ls (.binop f :: rest) (a :: b :: σ) s o
  | unop {n ls rest a σ s o} (f : Nat → Nat) :
      Eval F n ls rest (f a :: σ) s o → Eval F (n + 1) ls (.unop f :: rest) (a :: σ) s o
  | partialBinop {n ls rest a b v σ s o} (f : Nat → Nat → Option Nat) :
      f b a = some v →
      Eval F n ls rest (v :: σ) s o → Eval F (n + 1) ls (.partialBinop f :: rest) (a :: b :: σ) s o
  | partialUnop {n ls rest a v σ s o} (f : Nat → Option Nat) :
      f a = some v →
      Eval F n ls rest (v :: σ) s o → Eval F (n + 1) ls (.partialUnop f :: rest) (a :: σ) s o
  | dup {n ls rest a σ s o} :
      Eval F n ls rest (a :: a :: σ) s o → Eval F (n + 1) ls (.dup :: rest) (a :: σ) s o
  | select {n ls rest c v1 v2 σ s o} :
      Eval F n ls rest ((if c = 0 then v1 else v2) :: σ) s o →
      Eval F (n + 1) ls (.select :: rest) (c :: v1 :: v2 :: σ) s o
  | drop {n ls rest v σ s o} :
      Eval F n ls rest σ s o → Eval F (n + 1) ls (.drop :: rest) (v :: σ) s o
  | nop {n ls rest σ s o} :
      Eval F n ls rest σ s o → Eval F (n + 1) ls (.nop :: rest) σ s o
  | relabel {n ls rest σ s o} :
      Eval F n ls rest σ s o → Eval F (n + 1) ls (.relabel :: rest) σ s o
  | localGet {n ls rest σ s o} (i : Nat) :
      Eval F n ls rest (s.loc i :: σ) s o → Eval F (n + 1) ls (.localGet i :: rest) σ s o
  | localSet {n ls rest v σ s o} (i : Nat) :
      Eval F n ls rest σ (s.setLoc i v) o → Eval F (n + 1) ls (.localSet i :: rest) (v :: σ) s o
  | localTee {n ls rest v σ s o} (i : Nat) :
      Eval F n ls rest (v :: σ) (s.setLoc i v) o →
      Eval F (n + 1) ls (.localTee i :: rest) (v :: σ) s o
  | globalGet {n ls rest σ s o} (i : Nat) :
      Eval F n ls rest (s.glob i :: σ) s o → Eval F (n + 1) ls (.globalGet i :: rest) σ s o
  | globalSet {n ls rest v σ s o} (i : Nat) :
      Eval F n ls rest σ (s.setGlob i v) o → Eval F (n + 1) ls (.globalSet i :: rest) (v :: σ) s o
  | load {n ls rest a σ s o} (m w : Nat) (lm : Lab) :
      a + w ≤ s.size m → (∀ i, i < w → Lab.le (s.lab m (a + i)) lm) →
      Eval F n ls rest (s.word m a w :: σ) s o → Eval F (n + 1) ls (.load m w lm :: rest) (a :: σ) s o
  | store {n ls rest v a σ s o} (m w : Nat) (lm : Lab) :
      a + w ≤ s.size m →
      Eval F n ls rest σ (s.put m a (bytesOf v w) lm) o →
      Eval F (n + 1) ls (.store m w lm :: rest) (v :: a :: σ) s o
  | fill {n ls rest k v a σ s o} (m : Nat) (lm : Lab) :
      a + k ≤ s.size m →
      Eval F n ls rest σ (s.fill m a v k lm) o →
      Eval F (n + 1) ls (.fill m lm :: rest) (k :: v :: a :: σ) s o
  | copy {n ls rest k b a σ s o} (md ms : Nat) (lm : Lab) :
      a + k ≤ s.size md → b + k ≤ s.size ms →
      Eval F n ls rest σ (s.copy md ms a b k lm) o →
      Eval F (n + 1) ls (.copy md ms lm :: rest) (k :: b :: a :: σ) s o
  | tableGet {n ls rest c σ s o} (x : Nat) :
      c < s.tsize x →
      Eval F n ls rest (refOf (s.tbl x c) :: σ) s o →
      Eval F (n + 1) ls (.tableGet x :: rest) (c :: σ) s o
  | tableSet {n ls rest v c σ s o} (x : Nat) :
      c < s.tsize x →
      Eval F n ls rest σ (s.setTbl x c (ofRef v)) o →
      Eval F (n + 1) ls (.tableSet x :: rest) (v :: c :: σ) s o
  /--
  Read at most `k` values from the channel `c` of the descriptor `fd` into the cells from `a`,
  and how many they were into the cell `np`: all of it at the channel's level. A descriptor
  that the table does not have is a trap.
  -/
  | hostRead {n ls rest np k a fd c σ s o} :
      s.fdt fd = some c → a + k ≤ s.size 0 → np < s.size 0 →
      Eval F n ls rest σ
        (((s.put 0 a ((s.inp c).take k) (s.chan c)).setMem 0 np ((s.inp c).take k).length
          (s.chan c)).consume c k) o →
      Eval F (n + 1) ls (.hostRead :: rest) (np :: k :: a :: fd :: σ) s o
  /--
  Write the `k` cells from `a` to the channel `c` of the descriptor `fd`: a trap if one is more
  secret than it.
  -/
  | hostWrite {n ls rest k a fd c σ s o} :
      s.fdt fd = some c → a + k ≤ s.size 0 →
      (∀ x, a ≤ x → x < a + k → Lab.le (s.lab 0 x) (s.chan c)) →
      Eval F n ls rest σ (s.emit c (s.cells a k)) o →
      Eval F (n + 1) ls (.hostWrite :: rest) (k :: a :: fd :: σ) s o
  /--
  Open the file whose name is the `k` cells from `a`, in the directory `c` of the descriptor
  `fd`: a trap if a byte of the name is secret. If the directory has the name, or the flags
  `o` ask for the file to be made (`O_CREAT`, their lowest bit), the new descriptor is put in
  the cell `p` as a public value and the status is 0.
  -/
  | hostOpen {n ls rest p o k a fd c d σ s out} :
      s.fdt fd = some c → a + k ≤ s.size 0 → p < s.size 0 →
      (∀ x, a ≤ x → x < a + k → s.lab 0 x = Lab.L) →
      (s.cells a k ∈ s.names c ∨ o % 2 = 1) → s.fresh d →
      Eval F n ls rest (0 :: σ) ((s.openAt c (s.cells a k) d).setMem 0 p d Lab.L) out →
      Eval F (n + 1) ls (.hostOpen :: rest) (p :: o :: k :: a :: fd :: σ) s out
  /-- Otherwise nothing is opened, and the status says so. -/
  | hostOpenNone {n ls rest p o k a fd c σ s out} :
      s.fdt fd = some c → a + k ≤ s.size 0 → p < s.size 0 →
      (∀ x, a ≤ x → x < a + k → s.lab 0 x = Lab.L) →
      s.cells a k ∉ s.names c → o % 2 ≠ 1 →
      Eval F n ls rest (noEntry :: σ) s out →
      Eval F (n + 1) ls (.hostOpen :: rest) (p :: o :: k :: a :: fd :: σ) s out
  /-- A trap if the bytes asked for are not in the segment, which is so of any byte of a dropped one. -/
  | memInit {n ls rest c b a σ s o} (m k : Nat) (lm : Lab) :
      a + c ≤ s.size m → b + c ≤ (s.segs k).length →
      Eval F n ls rest σ (s.put m a (((s.segs k).drop b).take c) lm) o →
      Eval F (n + 1) ls (.memInit m k lm :: rest) (c :: b :: a :: σ) s o
  | dataDrop {n ls rest σ s o} (k : Nat) :
      Eval F n ls rest σ (s.dropSeg k) o → Eval F (n + 1) ls (.dataDrop k :: rest) σ s o
  | tableFill {n ls rest k v c σ s o} (x : Nat) :
      c + k ≤ s.tsize x →
      Eval F n ls rest σ (s.fillTbl x c (ofRef v) k) o →
      Eval F (n + 1) ls (.tableFill x :: rest) (k :: v :: c :: σ) s o
  | tableCopy {n ls rest k b a σ s o} (xd xs : Nat) :
      a + k ≤ s.tsize xd → b + k ≤ s.tsize xs →
      Eval F n ls rest σ (s.copyTbl xd xs a b k) o →
      Eval F (n + 1) ls (.tableCopy xd xs :: rest) (k :: b :: a :: σ) s o
  | tableSize {n ls rest σ s o} (x : Nat) :
      Eval F n ls rest (s.tsize x :: σ) s o → Eval F (n + 1) ls (.tableSize x :: rest) σ s o
  | tableGrow {n ls rest d v σ s o} (x : Nat) :
      Eval F n ls rest ((s.growTbl x d (ofRef v)).1 :: σ) (s.growTbl x d (ofRef v)).2 o →
      Eval F (n + 1) ls (.tableGrow x :: rest) (d :: v :: σ) s o
  /-- A trap if the references asked for are not in the segment, which is so of any of a dropped one. -/
  | tableInit {n ls rest c b a σ s o} (x k : Nat) :
      a + c ≤ s.tsize x → b + c ≤ (s.elems k).length →
      Eval F n ls rest σ (s.initTbl x k a b c) o →
      Eval F (n + 1) ls (.tableInit x k :: rest) (c :: b :: a :: σ) s o
  | elemDrop {n ls rest σ s o} (k : Nat) :
      Eval F n ls rest σ (s.dropElem k) o → Eval F (n + 1) ls (.elemDrop k :: rest) σ s o
  | memSize {n ls rest σ s o} (m : Nat) :
      Eval F n ls rest (s.size m :: σ) s o → Eval F (n + 1) ls (.memSize m :: rest) σ s o
  | memGrow {n ls rest d σ s o} (m : Nat) :
      Eval F n ls rest ((s.grow m d).1 :: σ) (s.grow m d).2 o →
      Eval F (n + 1) ls (.memGrow m :: rest) (d :: σ) s o
  | blockCont {n1 n2 ls rest keep ps rs body vs base s ob σ1 s1 o} :
      vs.length = ps.length →
      Eval F n1 (rs.length :: ls) body vs s ob → ob.lands = some (σ1, s1) → Kept keep s s1 →
      Eval F n2 ls rest (σ1 ++ base) s1 o →
      Eval F (n1 + n2 + 1) ls (.block keep ps rs body :: rest) (vs ++ base) s o
  | blockExit {n1 ls rest keep ps rs body vs base s ob o} :
      vs.length = ps.length →
      Eval F n1 (rs.length :: ls) body vs s ob → ob.exits = some o →
      Eval F (n1 + 1) ls (.block keep ps rs body :: rest) (vs ++ base) s o
  | loopCont {n1 n2 ls rest keep ps rs body vs base s ob σ1 s1 o} :
      vs.length = ps.length →
      Eval F n1 (rs.length :: ls) [.iter ps rs body] vs s ob → ob.lands = some (σ1, s1) →
      Kept keep s s1 →
      Eval F n2 ls rest (σ1 ++ base) s1 o →
      Eval F (n1 + n2 + 1) ls (.loop keep ps rs body :: rest) (vs ++ base) s o
  | loopExit {n1 ls rest keep ps rs body vs base s ob o} :
      vs.length = ps.length →
      Eval F n1 (rs.length :: ls) [.iter ps rs body] vs s ob → ob.exits = some o →
      Eval F (n1 + 1) ls (.loop keep ps rs body :: rest) (vs ++ base) s o
  /-- The body ends: the loop is done. -/
  | iterDone {n ls rest ps rs body vs s σ1 s1} :
      Eval F n (ps.length :: ls.tail) body vs s (.normal σ1 s1) →
      Eval F (n + 1) ls (.iter ps rs body :: rest) vs s (.normal σ1 s1)
  /-- The body branches to the loop's label: another iteration. -/
  | iterAgain {n1 n2 ls rest ps rs body vs s w s1 o} :
      Eval F n1 (ps.length :: ls.tail) body vs s (.br 0 w s1) →
      Eval F n2 ls (.iter ps rs body :: rest) w s1 o →
      Eval F (n1 + n2 + 1) ls (.iter ps rs body :: rest) vs s o
  /-- The body branches past the loop. -/
  | iterExit {n ls rest ps rs body vs s i w s1} :
      Eval F n (ps.length :: ls.tail) body vs s (.br (i + 1) w s1) →
      Eval F (n + 1) ls (.iter ps rs body :: rest) vs s (.br (i + 1) w s1)
  | iterExn {n ls rest ps rs body vs s t w s1} :
      Eval F n (ps.length :: ls.tail) body vs s (.exn t w s1) →
      Eval F (n + 1) ls (.iter ps rs body :: rest) vs s (.exn t w s1)
  | iterTailExn {n ls rest ps rs body vs s t w s1} :
      Eval F n (ps.length :: ls.tail) body vs s (.tailExn t w s1) →
      Eval F (n + 1) ls (.iter ps rs body :: rest) vs s (.tailExn t w s1)
  | iteCont {n1 n2 ls rest keep ps rs thn els c vs base s ob σ1 s1 o} :
      vs.length = ps.length →
      Eval F n1 (rs.length :: ls) (if c = 0 then els else thn) vs s ob → ob.lands = some (σ1, s1) →
      Kept keep s s1 →
      Eval F n2 ls rest (σ1 ++ base) s1 o →
      Eval F (n1 + n2 + 1) ls (.ite keep ps rs thn els :: rest) (c :: (vs ++ base)) s o
  | iteExit {n1 ls rest keep ps rs thn els c vs base s ob o} :
      vs.length = ps.length →
      Eval F n1 (rs.length :: ls) (if c = 0 then els else thn) vs s ob → ob.exits = some o →
      Eval F (n1 + 1) ls (.ite keep ps rs thn els :: rest) (c :: (vs ++ base)) s o
  | br {ls rest i n σ s} :
      ls[i]? = some n → Eval F 1 ls (.br i :: rest) σ s (.br i (σ.take n) s)
  | brIfTaken {ls rest i n c σ s} :
      c ≠ 0 → ls[i]? = some n → Eval F 1 ls (.brIf i :: rest) (c :: σ) s (.br i (σ.take n) s)
  | brIfNot {n ls rest i σ s o} :
      Eval F n ls rest σ s o → Eval F (n + 1) ls (.brIf i :: rest) (0 :: σ) s o
  | brTable {ls rest ts d c n σ s} :
      ls[tableTarget ts d c]? = some n →
      Eval F 1 ls (.brTable ts d :: rest) (c :: σ) s (.br (tableTarget ts d c) (σ.take n) s)
  | ret {ls rest n σ s} :
      ls[ls.length - 1]? = some n →
      Eval F 1 ls (.ret :: rest) σ s (.br (ls.length - 1) (σ.take n) s)
  /-- The callee ends at the end of its body or by a branch to its label (a `return`). -/
  | call {n1 n2 ls rest i f args base s ob r t o} :
      F[i]? = some f → args.length = f.ty.params.length →
      Eval F n1 [f.ty.results.length] f.body [] { s with loc := frame args } ob →
      ob.lands = some (r, t) → Kept f.keep s t →
      Eval F n2 ls rest (r ++ base) { t with loc := s.loc } o →
      Eval F (n1 + n2 + 1) ls (.call i :: rest) (args ++ base) s o
  | callIndirect {n1 n2 ls rest x ps b rs c i f args base s ob r t o} :
      s.entry x c = some i → F[i]? = some f → f.ty.params = ps → f.ty.results = rs → Lab.le b f.ty.bound →
      args.length = ps.length →
      Eval F n1 [rs.length] f.body [] { s with loc := frame args } ob →
      ob.lands = some (r, t) → Kept f.keep s t →
      Eval F n2 ls rest (r ++ base) { t with loc := s.loc } o →
      Eval F (n1 + n2 + 1) ls (.callIndirect x ps b rs :: rest) (c :: (args ++ base)) s o
  /-- A tail call: the function returns what the callee returns, if the callee's comparison passes. -/
  | retCall {n1 ls rest i f args base s ob r t} :
      F[i]? = some f → args.length = f.ty.params.length →
      Eval F n1 [f.ty.results.length] f.body [] { s with loc := frame args } ob →
      ob.lands = some (r, t) → Kept f.keep s t →
      Eval F (n1 + 1) ls (.retCall i :: rest) (args ++ base) s
        (.br (ls.length - 1) r { t with loc := s.loc })
  | retCallExn {n1 ls rest i f args base s ob t w u} :
      F[i]? = some f → args.length = f.ty.params.length →
      Eval F n1 [f.ty.results.length] f.body [] { s with loc := frame args } ob →
      ob.thrown = some (t, w, u) →
      Eval F (n1 + 1) ls (.retCall i :: rest) (args ++ base) s (.tailExn t w { u with loc := s.loc })
  | retCallIndirect {n1 ls rest x ps b rs c i f args base s ob r t} :
      s.entry x c = some i → F[i]? = some f → f.ty.params = ps → f.ty.results = rs → Lab.le b f.ty.bound →
      args.length = ps.length →
      Eval F n1 [rs.length] f.body [] { s with loc := frame args } ob →
      ob.lands = some (r, t) → Kept f.keep s t →
      Eval F (n1 + 1) ls (.retCallIndirect x ps b rs :: rest) (c :: (args ++ base)) s
        (.br (ls.length - 1) r { t with loc := s.loc })
  | retCallIndirectExn {n1 ls rest x ps b rs c i f args base s ob t w u} :
      s.entry x c = some i → F[i]? = some f → f.ty.params = ps → f.ty.results = rs → Lab.le b f.ty.bound →
      args.length = ps.length →
      Eval F n1 [rs.length] f.body [] { s with loc := frame args } ob →
      ob.thrown = some (t, w, u) →
      Eval F (n1 + 1) ls (.retCallIndirect x ps b rs :: rest) (c :: (args ++ base)) s
        (.tailExn t w { u with loc := s.loc })
  | callExn {n1 ls rest i f args base s ob t w u} :
      F[i]? = some f → args.length = f.ty.params.length →
      Eval F n1 [f.ty.results.length] f.body [] { s with loc := frame args } ob →
      ob.thrown = some (t, w, u) →
      Eval F (n1 + 1) ls (.call i :: rest) (args ++ base) s (.exn t w { u with loc := s.loc })
  | callIndirectExn {n1 ls rest x ps b rs c i f args base s ob t w u} :
      s.entry x c = some i → F[i]? = some f → f.ty.params = ps → f.ty.results = rs → Lab.le b f.ty.bound →
      args.length = ps.length →
      Eval F n1 [rs.length] f.body [] { s with loc := frame args } ob →
      ob.thrown = some (t, w, u) →
      Eval F (n1 + 1) ls (.callIndirect x ps b rs :: rest) (c :: (args ++ base)) s
        (.exn t w { u with loc := s.loc })
  /-- A null reference is a trap; so is a function that an indirect call would refuse. -/
  | callRef {n1 n2 ls rest ps b rs c i f args base s ob r t o} :
      ofRef c = some i → F[i]? = some f → f.ty.params = ps → f.ty.results = rs → Lab.le b f.ty.bound →
      args.length = ps.length →
      Eval F n1 [rs.length] f.body [] { s with loc := frame args } ob →
      ob.lands = some (r, t) → Kept f.keep s t →
      Eval F n2 ls rest (r ++ base) { t with loc := s.loc } o →
      Eval F (n1 + n2 + 1) ls (.callRef ps b rs :: rest) (c :: (args ++ base)) s o
  | callRefExn {n1 ls rest ps b rs c i f args base s ob t w u} :
      ofRef c = some i → F[i]? = some f → f.ty.params = ps → f.ty.results = rs → Lab.le b f.ty.bound →
      args.length = ps.length →
      Eval F n1 [rs.length] f.body [] { s with loc := frame args } ob →
      ob.thrown = some (t, w, u) →
      Eval F (n1 + 1) ls (.callRef ps b rs :: rest) (c :: (args ++ base)) s
        (.exn t w { u with loc := s.loc })
  | throw {ls rest t k σ s} : Eval F 1 ls (.throw t k :: rest) σ s (.exn t (σ.take k) s)
  /-- The null reference is a trap. -/
  | throwRef {ls rest i t w σ s} :
      s.exns[i]? = some (t, w) → Eval F 1 ls (.throwRef :: rest) ((i + 1) :: σ) s (.exn t w s)
  | tryCont {n1 n2 ls rest keep ps rs clauses body vs base s ob σ1 s1 o} :
      vs.length = ps.length →
      Eval F n1 (rs.length :: ls) body vs s ob → (ob.caught clauses).lands = some (σ1, s1) →
      Kept keep s s1 →
      Eval F n2 ls rest (σ1 ++ base) s1 o →
      Eval F (n1 + n2 + 1) ls (.tryTable keep ps rs clauses body :: rest) (vs ++ base) s o
  | tryExit {n1 ls rest keep ps rs clauses body vs base s ob o} :
      vs.length = ps.length →
      Eval F n1 (rs.length :: ls) body vs s ob → (ob.caught clauses).exits = some o →
      Eval F (n1 + 1) ls (.tryTable keep ps rs clauses body :: rest) (vs ++ base) s o

end WasmIfc
