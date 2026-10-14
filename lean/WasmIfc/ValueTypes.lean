/-
Value types. The judgment `LTyped` of `Defs.lean` has one type for all values, so a labelled
type is its label. This file has the judgment with labelled value types `t⟨ℓ⟩`, as the paper
writes them and as `Syntax.Instructions` has them: a stack type is a list of pairs of a value
type and a level, an instruction asks for the types its operands have in WebAssembly, and a
memory and a table have an address type, `i32` or `i64`.

The semantics does not look at types: a value is a number whatever its type. So nothing is to
be proved again. `Typed.erase` says that a derivation with value types, with the types
forgotten, is a derivation of `LTyped`, and the theorems for a module that is well typed with
value types follow from those of `Statement.lean` and `Machine.lean`.
-/
import WasmIfc.Machine

namespace WasmIfc

/-- The value types: the numbers, the vectors, and the references to functions and to exceptions. -/
inductive VTy where
  | i32
  | i64
  | f32
  | f64
  | v128
  | funcref
  | exnref
  deriving DecidableEq

/-- A labelled value type, the paper's `t⟨ℓ⟩`. -/
abbrev LTy := VTy × Lab

/-- A stack type with value types, top first. -/
abbrev VSTy := List LTy

/-- The labels of a stack type: what `LTyped` knows of it. -/
def labelsOf (st : VSTy) : STy := st.map Prod.snd

/-- The value types of a stack type. -/
def typesOf (st : VSTy) : List VTy := st.map Prod.fst

/-- The order on stack types: the same value types, and the labels flow. -/
inductive VFlows : VSTy → VSTy → Prop where
  | nil : VFlows [] []
  | cons {t : VTy} {a b : Lab} {s s' : VSTy} :
      Lab.le a b → VFlows s s' → VFlows ((t, a) :: s) ((t, b) :: s')

theorem VFlows.labelsOf : ∀ {s s' : VSTy}, VFlows s s' → SFlows (labelsOf s) (labelsOf s')
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h hs.labelsOf

theorem labels_append (a b : VSTy) : labelsOf (a ++ b) = labelsOf a ++ labelsOf b := by
  simp [labelsOf]

/-- A function type with value types. -/
structure VFuncTy where
  params : VSTy
  bound : Lab
  results : VSTy

def VFuncTy.erase (ft : VFuncTy) : FuncTy := ⟨labelsOf ft.params, ft.bound, labelsOf ft.results⟩

/--
The context with value types: the labelled types of the locals and the globals, the function
types, the level of each table, the types of the values that an exception of each tag carries
(top of the stack first), and the address type of each memory and of each table, which is
`i32`, or `i64` for a 64-bit one.
-/
structure VCtx where
  locals : Nat → LTy
  globals : Nat → LTy
  preserved : Nat → Prop
  funcs : List VFuncTy
  table : Nat → Lab
  tags : List (List VTy)
  addr : Nat → VTy
  taddr : Nat → VTy

/-- The context that `LTyped` sees. -/
def VCtx.erase (C : VCtx) : Ctx where
  locals := fun i => (C.locals i).2
  globals := fun i => (C.globals i).2
  preserved := C.preserved
  funcs := C.funcs.map VFuncTy.erase
  table := C.table
  tags := C.tags.map List.length

/-- The type of a count of cells or entries moved between two memories or tables: `i32` unless both are 64-bit. -/
def minAddr (a b : VTy) : VTy := if a = .i64 ∧ b = .i64 then .i64 else .i32

/-- A clause of a `try_table` with value types: its label takes the values of its tag, and a reference besides. -/
def VClauseOk (C : VCtx) (Ls : List VSTy) : Option Nat × Nat × Bool → Prop
  | (some t, j, false) => ∃ ts target, C.tags[t]? = some ts ∧ Ls[j]? = some target ∧ typesOf target = ts
  | (some t, j, true) =>
      ∃ ts target, C.tags[t]? = some ts ∧ Ls[j]? = some target ∧ typesOf target = .exnref :: ts
  | (none, j, false) => Ls[j]? = some []
  | (none, j, true) => ∃ l, Ls[j]? = some [(.exnref, l)]

/--
`Typed C Ls e P st P' st'`: the judgment `LTyped` with value types. Each rule is the rule
of the same name there, with the types that the instruction's operands and results have in
WebAssembly. A block type of an instruction is the labels of the block's types (`labelsOf`).
An operation on one or two values may give a value of another type (a comparison, a
conversion). There is no rule for `iter`, which no program contains.
-/
inductive Typed (C : VCtx) : List VSTy → List Instr → Pcs → VSTy → Pcs → VSTy → Prop where
  | nil {Ls P st} : Typed C Ls [] P st P st
  | const {Ls rest pc Pr st P' st'} (t : VTy) (n : Nat) :
      Typed C Ls rest (pc :: Pr) ((t, pc) :: st) P' st' →
      Typed C Ls (.const n :: rest) (pc :: Pr) st P' st'
  | binop {Ls rest pc Pr l0 l1 st P' st'} (t t' : VTy) (f : Nat → Nat → Nat) :
      Typed C Ls rest (pc :: Pr) ((t', (l0.join l1).join pc) :: st) P' st' →
      Typed C Ls (.binop f :: rest) (pc :: Pr) ((t, l0) :: (t, l1) :: st) P' st'
  | unop {Ls rest pc Pr l st P' st'} (t t' : VTy) (f : Nat → Nat) :
      Typed C Ls rest (pc :: Pr) ((t', l.join pc) :: st) P' st' →
      Typed C Ls (.unop f :: rest) (pc :: Pr) ((t, l) :: st) P' st'
  | partialBinop {Ls rest pc Pr l0 l1 st P' st'} (t : VTy) (f : Nat → Nat → Option Nat) :
      Typed C Ls rest (pc :: Pr) ((t, (l0.join l1).join pc) :: st) P' st' →
      Typed C Ls (.partialBinop f :: rest) (pc :: Pr) ((t, l0) :: (t, l1) :: st) P' st'
  | partialUnop {Ls rest pc Pr l st P' st'} (t t' : VTy) (f : Nat → Option Nat) :
      Typed C Ls rest (pc :: Pr) ((t', l.join pc) :: st) P' st' →
      Typed C Ls (.partialUnop f :: rest) (pc :: Pr) ((t, l) :: st) P' st'
  | dup {Ls rest P τ st P' st'} :
      Typed C Ls rest P (τ :: τ :: st) P' st' →
      Typed C Ls (.dup :: rest) P (τ :: st) P' st'
  | select {Ls rest pc Pr lc l1 l2 st P' st'} (t : VTy) :
      Typed C Ls rest (pc :: Pr) ((t, pc.join (lc.join (l1.join l2))) :: st) P' st' →
      Typed C Ls (.select :: rest) (pc :: Pr) ((.i32, lc) :: (t, l1) :: (t, l2) :: st) P' st'
  | drop {Ls rest P τ st P' st'} :
      Typed C Ls rest P st P' st' →
      Typed C Ls (.drop :: rest) P (τ :: st) P' st'
  | nop {Ls rest P st P' st'} :
      Typed C Ls rest P st P' st' →
      Typed C Ls (.nop :: rest) P st P' st'
  | relabel {Ls rest P st st1 P' st'} :
      VFlows st st1 →
      Typed C Ls rest P st1 P' st' →
      Typed C Ls (.relabel :: rest) P st P' st'
  | localGet {Ls rest pc Pr st P' st'} (i : Nat) :
      Typed C Ls rest (pc :: Pr) (((C.locals i).1, (C.locals i).2.join pc) :: st) P' st' →
      Typed C Ls (.localGet i :: rest) (pc :: Pr) st P' st'
  | localSet {Ls rest pc Pr l st P' st'} (i : Nat) :
      Lab.le pc (C.locals i).2 → Lab.le l (C.locals i).2 →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.localSet i :: rest) (pc :: Pr) (((C.locals i).1, l) :: st) P' st'
  | localTee {Ls rest pc Pr l st P' st'} (i : Nat) :
      Lab.le pc (C.locals i).2 → Lab.le l (C.locals i).2 →
      Typed C Ls rest (pc :: Pr) (((C.locals i).1, l) :: st) P' st' →
      Typed C Ls (.localTee i :: rest) (pc :: Pr) (((C.locals i).1, l) :: st) P' st'
  | globalGet {Ls rest pc Pr st P' st'} (i : Nat) :
      Typed C Ls rest (pc :: Pr) (((C.globals i).1, (C.globals i).2.join pc) :: st) P' st' →
      Typed C Ls (.globalGet i :: rest) (pc :: Pr) st P' st'
  | globalSet {Ls rest pc Pr l st P' st'} (i : Nat) :
      ¬ C.preserved i → Lab.le pc (C.globals i).2 → Lab.le l (C.globals i).2 →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.globalSet i :: rest) (pc :: Pr) (((C.globals i).1, l) :: st) P' st'
  | globalSetPreserved {Ls rest pc Pr l st P' st'} (i : Nat) :
      C.preserved i → Lab.le l pc →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.globalSet i :: rest) (pc :: Pr) (((C.globals i).1, l) :: st) P' st'
  /-- The address has the memory's address type; the value read has the type the load names. -/
  | load {Ls rest pc Pr la st P' st'} (t : VTy) (m w : Nat) (lm : Lab) :
      Typed C Ls rest (pc :: Pr) ((t, (la.join lm).join pc) :: st) P' st' →
      Typed C Ls (.load m w lm :: rest) (pc :: Pr) ((C.addr m, la) :: st) P' st'
  | store {Ls rest pc Pr lv la st P' st'} (t : VTy) (m w : Nat) (lm : Lab) :
      Lab.le ((pc.join la).join lv) lm →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.store m w lm :: rest) (pc :: Pr) ((t, lv) :: (C.addr m, la) :: st) P' st'
  | fill {Ls rest pc Pr ln lv ld st P' st'} (m : Nat) (lm : Lab) :
      Lab.le (pc.join (ln.join (lv.join ld))) lm →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.fill m lm :: rest) (pc :: Pr)
        ((C.addr m, ln) :: (.i32, lv) :: (C.addr m, ld) :: st) P' st'
  | copy {Ls rest pc Pr ln lsrc ld st P' st'} (md ms : Nat) (lm : Lab) :
      Lab.le (pc.join (ln.join (lsrc.join ld))) lm →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.copy md ms lm :: rest) (pc :: Pr)
        ((minAddr (C.addr md) (C.addr ms), ln) :: (C.addr ms, lsrc) :: (C.addr md, ld) :: st) P' st'
  | tableGet {Ls rest pc Pr li st P' st'} (x : Nat) :
      Typed C Ls rest (pc :: Pr) ((.funcref, pc.join (li.join (C.table x))) :: st) P' st' →
      Typed C Ls (.tableGet x :: rest) (pc :: Pr) ((C.taddr x, li) :: st) P' st'
  | tableSet {Ls rest pc Pr lv li st P' st'} (x : Nat) :
      Lab.le (pc.join (li.join lv)) (C.table x) →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.tableSet x :: rest) (pc :: Pr) ((.funcref, lv) :: (C.taddr x, li) :: st) P' st'
  /-- A host call takes and returns 32-bit integers. -/
  | hostRead {Ls rest Pr st P' st'} :
      Typed C Ls rest (Lab.L :: Pr) ((.i32, Lab.L) :: st) P' st' →
      Typed C Ls (.hostRead :: rest) (Lab.L :: Pr)
        ((.i32, Lab.L) :: (.i32, Lab.L) :: (.i32, Lab.L) :: (.i32, Lab.L) :: st) P' st'
  | hostWrite {Ls rest Pr st P' st'} :
      Typed C Ls rest (Lab.L :: Pr) ((.i32, Lab.L) :: st) P' st' →
      Typed C Ls (.hostWrite :: rest) (Lab.L :: Pr)
        ((.i32, Lab.L) :: (.i32, Lab.L) :: (.i32, Lab.L) :: st) P' st'
  | hostGet {Ls rest Pr st P' st'} :
      Typed C Ls rest (Lab.L :: Pr) ((.i32, Lab.L) :: st) P' st' →
      Typed C Ls (.hostGet :: rest) (Lab.L :: Pr)
        ((.i32, Lab.L) :: (.i32, Lab.L) :: (.i32, Lab.L) :: (.i32, Lab.L) :: st) P' st'
  | hostCtl {Ls rest Pr st P' st'} :
      Typed C Ls rest (Lab.L :: Pr) ((.i32, Lab.L) :: st) P' st' →
      Typed C Ls (.hostCtl :: rest) (Lab.L :: Pr)
        ((.i32, Lab.L) :: (.i32, Lab.L) :: (.i32, Lab.L) :: st) P' st'
  | hostPoll {Ls rest Pr st P' st'} :
      Typed C Ls rest (Lab.L :: Pr) ((.i32, Lab.L) :: st) P' st' →
      Typed C Ls (.hostPoll :: rest) (Lab.L :: Pr)
        ((.i32, Lab.L) :: (.i32, Lab.L) :: (.i32, Lab.L) :: (.i32, Lab.L) :: st) P' st'
  | hostExit {Ls rest Pr st stAny} :
      Typed C Ls (.hostExit :: rest) (Lab.L :: Pr) ((.i32, Lab.L) :: st) (Lab.L :: Pr) stAny
  | hostOpen {Ls rest Pr st P' st'} :
      Typed C Ls rest (Lab.L :: Pr) ((.i32, Lab.L) :: st) P' st' →
      Typed C Ls (.hostOpen :: rest) (Lab.L :: Pr)
        ((.i32, Lab.L) :: (.i32, Lab.L) :: (.i32, Lab.L) :: (.i32, Lab.L) :: (.i32, Lab.L) :: st) P' st'
  | memInit {Ls rest pc Pr ln lsrc ld st P' st'} (m k : Nat) (lm : Lab) :
      Lab.le (pc.join (ln.join (lsrc.join ld))) lm →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.memInit m k lm :: rest) (pc :: Pr)
        ((.i32, ln) :: (.i32, lsrc) :: (C.addr m, ld) :: st) P' st'
  | dataDrop {Ls rest P st P' st'} (k : Nat) :
      Typed C Ls rest P st P' st' →
      Typed C Ls (.dataDrop k :: rest) P st P' st'
  | tableFill {Ls rest pc Pr ln lv li st P' st'} (x : Nat) :
      Lab.le (pc.join (ln.join (lv.join li))) (C.table x) →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.tableFill x :: rest) (pc :: Pr)
        ((C.taddr x, ln) :: (.funcref, lv) :: (C.taddr x, li) :: st) P' st'
  | tableCopy {Ls rest pc Pr ln lsrc ld st P' st'} (xd xs : Nat) :
      Lab.le (pc.join (ln.join (lsrc.join (ld.join (C.table xs))))) (C.table xd) →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.tableCopy xd xs :: rest) (pc :: Pr)
        ((minAddr (C.taddr xd) (C.taddr xs), ln) :: (C.taddr xs, lsrc) :: (C.taddr xd, ld) :: st) P' st'
  | tableSize {Ls rest pc Pr st P' st'} (x : Nat) :
      Typed C Ls rest (pc :: Pr) ((C.taddr x, pc.join (C.table x)) :: st) P' st' →
      Typed C Ls (.tableSize x :: rest) (pc :: Pr) st P' st'
  | tableGrow {Ls rest pc Pr ln lv st P' st'} (x : Nat) :
      Lab.le (pc.join (ln.join lv)) (C.table x) →
      Typed C Ls rest (pc :: Pr) ((C.taddr x, pc.join (C.table x)) :: st) P' st' →
      Typed C Ls (.tableGrow x :: rest) (pc :: Pr) ((C.taddr x, ln) :: (.funcref, lv) :: st) P' st'
  | tableInit {Ls rest pc Pr ln lsrc ld st P' st'} (x k : Nat) :
      Lab.le (pc.join (ln.join (lsrc.join ld))) (C.table x) →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.tableInit x k :: rest) (pc :: Pr)
        ((.i32, ln) :: (.i32, lsrc) :: (C.taddr x, ld) :: st) P' st'
  | elemDrop {Ls rest P st P' st'} (k : Nat) :
      Typed C Ls rest P st P' st' →
      Typed C Ls (.elemDrop k :: rest) P st P' st'
  /-- The size of a memory and what it grows by have the memory's address type. -/
  | memSize {Ls rest pc Pr st P' st'} (m : Nat) :
      Typed C Ls rest (pc :: Pr) ((C.addr m, pc) :: st) P' st' →
      Typed C Ls (.memSize m :: rest) (pc :: Pr) st P' st'
  | memGrow {Ls rest pc Pr l st P' st'} (m : Nat) :
      Lab.le (pc.join l) Lab.L →
      Typed C Ls rest (pc :: Pr) ((C.addr m, pc) :: st) P' st' →
      Typed C Ls (.memGrow m :: rest) (pc :: Pr) ((C.addr m, l) :: st) P' st'
  /-- The instruction's block type is the labels of `ps` and `rs`. -/
  | block {Ls rest pc Pr tin keep ps rs body p P1 st P' st'} :
      VFlows tin ps → AllGe pc (labelsOf rs) → Restores C.erase p P1 keep →
      Typed C (rs :: Ls) body (pc :: pc :: Pr) ps (p :: P1) rs →
      Typed C Ls rest P1 (rs ++ st) P' st' →
      Typed C Ls (.block keep (labelsOf ps) (labelsOf rs) body :: rest) (pc :: Pr) (tin ++ st) P' st'
  | loop {Ls rest pc Pr pcL tin keep ps rs body p P1 st P' st'} :
      Lab.le pc pcL → Lab.le p pcL → VFlows tin ps → AllGe pcL (labelsOf rs) →
      Restores C.erase pcL P1 keep →
      Typed C (ps :: Ls) body (pcL :: pc :: Pr) ps (p :: P1) rs →
      Typed C Ls rest P1 (rs ++ st) P' st' →
      Typed C Ls (.loop keep (labelsOf ps) (labelsOf rs) body :: rest) (pc :: Pr) (tin ++ st) P' st'
  | ite {Ls rest pc Pr l tin keep ps rs thn els p1 P1 p2 P2 st P' st'} :
      VFlows tin ps → AllGe (pc.join l) (labelsOf rs) →
      Restores C.erase (p1.join p2) (joinEach P1 P2) keep →
      Typed C (rs :: Ls) thn (pc.join l :: pc :: Pr) ps (p1 :: P1) rs →
      Typed C (rs :: Ls) els (pc.join l :: pc :: Pr) ps (p2 :: P2) rs →
      Typed C Ls rest (joinEach P1 P2) (rs ++ st) P' st' →
      Typed C Ls (.ite keep (labelsOf ps) (labelsOf rs) thn els :: rest) (pc :: Pr)
        ((.i32, l) :: (tin ++ st)) P' st'
  | br {Ls rest pc Pr i rs carried st stAny} :
      Ls[i]? = some rs → AllGe pc (labelsOf rs) → VFlows carried rs →
      Typed C Ls (.br i :: rest) (pc :: Pr) (carried ++ st) (raise pc (pc :: Pr) i) stAny
  | brIf {Ls rest pc Pr l i rs carried st P' st'} :
      Ls[i]? = some rs → AllGe (pc.join l) (labelsOf rs) → VFlows carried rs →
      Typed C Ls rest (raise (pc.join l) (pc :: Pr) i) (carried ++ st) P' st' →
      Typed C Ls (.brIf i :: rest) (pc :: Pr) ((.i32, l) :: (carried ++ st)) P' st'
  | brTable {Ls rest pc Pr l ts d k rs carried st stAny} :
      (∀ t, t ∈ d :: ts → Ls[t]? = some rs ∧ t ≤ k) → AllGe (pc.join l) (labelsOf rs) →
      VFlows carried rs →
      Typed C Ls (.brTable ts d :: rest) (pc :: Pr) ((.i32, l) :: (carried ++ st))
        (raise (pc.join l) (pc :: Pr) k) stAny
  | ret {Ls rest pc Pr rs carried st stAny} :
      Ls[Ls.length - 1]? = some rs → AllGe pc (labelsOf rs) → VFlows carried rs →
      Typed C Ls (.ret :: rest) (pc :: Pr) (carried ++ st)
        (raise pc (pc :: Pr) (Ls.length - 1)) stAny
  | call {Ls rest pc Pr i ft targs st P' st'} :
      C.funcs[i]? = some ft → Lab.le pc ft.bound → VFlows targs ft.params →
      Typed C Ls rest (pc :: Pr) (ft.results ++ st) P' st' →
      Typed C Ls (.call i :: rest) (pc :: Pr) (targs ++ st) P' st'
  | retCall {Ls rest pc Pr i ft ret targs st stAny} :
      C.funcs[i]? = some ft → Lab.le pc ft.bound → VFlows targs ft.params →
      Ls[Ls.length - 1]? = some ret → AllGe pc (labelsOf ret) → VFlows ft.results ret →
      Typed C Ls (.retCall i :: rest) (pc :: Pr) (targs ++ st)
        (raise pc (pc :: Pr) (Ls.length - 1)) stAny
  /-- The index has the table's address type; the expected type is the labels of `ps` and `rs`. -/
  | callIndirect {Ls rest pc Pr l x ps b rs targs st P' st'} :
      Lab.le (pc.join (l.join (C.table x))) b → VFlows targs ps →
      Typed C Ls rest (pc :: Pr) (rs ++ st) P' st' →
      Typed C Ls (.callIndirect x (labelsOf ps) b (labelsOf rs) :: rest) (pc :: Pr)
        ((C.taddr x, l) :: (targs ++ st)) P' st'
  | retCallIndirect {Ls rest pc Pr l x ps b rs ret targs st stAny} :
      Lab.le (pc.join (l.join (C.table x))) b → VFlows targs ps →
      Ls[Ls.length - 1]? = some ret → AllGe pc (labelsOf ret) → VFlows rs ret →
      Typed C Ls (.retCallIndirect x (labelsOf ps) b (labelsOf rs) :: rest) (pc :: Pr)
        ((C.taddr x, l) :: (targs ++ st)) (raise pc (pc :: Pr) (Ls.length - 1)) stAny
  | callRef {Ls rest pc Pr l ps b rs targs st P' st'} :
      Lab.le (pc.join l) b → VFlows targs ps →
      Typed C Ls rest (pc :: Pr) (rs ++ st) P' st' →
      Typed C Ls (.callRef (labelsOf ps) b (labelsOf rs) :: rest) (pc :: Pr)
        ((.funcref, l) :: (targs ++ st)) P' st'
  | unreachable {Ls rest P st stAny} :
      Typed C Ls (.unreachable :: rest) P st P stAny
  /-- An exception carries public values of its tag's types. -/
  | throw {Ls rest Pr t ts args st stAny} :
      C.tags[t]? = some ts → typesOf args = ts → (∀ l, l ∈ labelsOf args → l = Lab.L) →
      Typed C Ls (.throw t ts.length :: rest) (Lab.L :: Pr) (args ++ st) (Lab.L :: Pr) stAny
  | throwRef {Ls rest Pr st stAny} :
      Typed C Ls (.throwRef :: rest) (Lab.L :: Pr) ((.exnref, Lab.L) :: st) (Lab.L :: Pr) stAny
  | tryTable {Ls rest Pr tin keep ps rs clauses body p P1 st P' st'} :
      VFlows tin ps → Restores C.erase p P1 keep → (∀ c, c ∈ clauses → VClauseOk C Ls c) →
      Typed C (rs :: Ls) body (Lab.L :: Lab.L :: Pr) ps (p :: P1) rs →
      Typed C Ls rest P1 (rs ++ st) P' st' →
      Typed C Ls (.tryTable keep (labelsOf ps) (labelsOf rs) clauses body :: rest) (Lab.L :: Pr)
        (tin ++ st) P' st'

/-! ### Forgetting the value types -/

theorem getElem?_labels {Ls : List VSTy} {i : Nat} {rs : VSTy} (h : Ls[i]? = some rs) :
    (Ls.map labelsOf)[i]? = some (labelsOf rs) := by
  simp [h]

theorem last_labels {Ls : List VSTy} {rs : VSTy} (h : Ls[Ls.length - 1]? = some rs) :
    (Ls.map labelsOf)[(Ls.map labelsOf).length - 1]? = some (labelsOf rs) := by
  simp [h]

theorem VClauseOk.erase {C : VCtx} {Ls : List VSTy} {c : Option Nat × Nat × Bool}
    (h : VClauseOk C Ls c) : ClauseOk C.erase (Ls.map labelsOf) c := by
  obtain ⟨t, j, r⟩ := c
  cases t with
  | none =>
    cases r with
    | false => exact getElem?_labels (rs := []) h
    | true =>
      obtain ⟨l, hl⟩ := h
      exact ⟨l, getElem?_labels hl⟩
  | some t =>
    cases r with
    | false =>
      obtain ⟨ts, target, ht, hl, hty⟩ := h
      refine ⟨ts.length, labelsOf target, by simp [VCtx.erase, ht], getElem?_labels hl, ?_⟩
      simp [labelsOf, ← hty, typesOf]
    | true =>
      obtain ⟨ts, target, ht, hl, hty⟩ := h
      refine ⟨ts.length, labelsOf target, by simp [VCtx.erase, ht], getElem?_labels hl, ?_⟩
      have := congrArg List.length hty
      simpa [labelsOf, typesOf] using this

/--
A derivation with value types is, with the types forgotten, a derivation of `LTyped`: of the
same instructions, from the labels of the same stack types, in the context that keeps the
labels.
-/
theorem Typed.erase {C : VCtx} {Ls : List VSTy} {e : List Instr} {P P' : Pcs} {st st' : VSTy}
    (h : Typed C Ls e P st P' st') :
    LTyped C.erase (Ls.map labelsOf) e P (labelsOf st) P' (labelsOf st') := by
  induction h with
  | nil => exact .nil
  | const t n _ ih => exact .const n ih
  | binop t t' f _ ih => exact .binop f ih
  | unop t t' f _ ih => exact .unop f ih
  | partialBinop t f _ ih => exact .partialBinop f ih
  | partialUnop t t' f _ ih => exact .partialUnop f ih
  | dup _ ih => exact .dup ih
  | select t _ ih => exact .select ih
  | drop _ ih => exact .drop ih
  | nop _ ih => exact .nop ih
  | relabel hfl _ ih => exact .relabel hfl.labelsOf ih
  | localGet i _ ih => exact .localGet i ih
  | localSet i h1 h2 _ ih => exact .localSet i h1 h2 ih
  | localTee i h1 h2 _ ih => exact .localTee i h1 h2 ih
  | globalGet i _ ih => exact .globalGet i ih
  | globalSet i h1 h2 h3 _ ih => exact .globalSet i h1 h2 h3 ih
  | globalSetPreserved i h1 h2 _ ih => exact .globalSetPreserved i h1 h2 ih
  | load t m w lm _ ih => exact .load m w lm ih
  | store t m w lm h1 _ ih => exact .store m w lm h1 ih
  | fill m lm h1 _ ih => exact .fill m lm h1 ih
  | copy md ms lm h1 _ ih => exact .copy md ms lm h1 ih
  | tableGet x _ ih => exact .tableGet x ih
  | tableSet x h1 _ ih => exact .tableSet x h1 ih
  | hostRead _ ih => exact .hostRead ih
  | hostWrite _ ih => exact .hostWrite ih
  | hostGet _ ih => exact .hostGet ih
  | hostCtl _ ih => exact .hostCtl ih
  | hostPoll _ ih => exact .hostPoll ih
  | hostOpen _ ih => exact .hostOpen ih
  | hostExit => exact .hostExit
  | memInit m k lm h1 _ ih => exact .memInit m k lm h1 ih
  | dataDrop k _ ih => exact .dataDrop k ih
  | tableFill x h1 _ ih => exact .tableFill x h1 ih
  | tableCopy xd xs h1 _ ih => exact .tableCopy xd xs h1 ih
  | tableSize x _ ih => exact .tableSize x ih
  | tableGrow x h1 _ ih => exact .tableGrow x h1 ih
  | tableInit x k h1 _ ih => exact .tableInit x k h1 ih
  | elemDrop k _ ih => exact .elemDrop k ih
  | memSize m _ ih => exact .memSize m ih
  | memGrow m h1 _ ih => exact .memGrow m h1 ih
  | block hfl hge hres _ _ ihb ihr =>
    rw [labels_append] at ihr ⊢
    exact .block hfl.labelsOf hge hres ihb ihr
  | loop h1 h2 hfl hge hres _ _ ihb ihr =>
    rw [labels_append] at ihr ⊢
    exact .loop h1 h2 hfl.labelsOf hge hres ihb ihr
  | ite hfl hge hres _ _ _ iht ihe ihr =>
    rw [labels_append] at ihr
    simp only [labelsOf, List.map_cons, List.map_append] at iht ihe ihr ⊢
    exact .ite hfl.labelsOf hge hres iht ihe ihr
  | br hl hge hfl =>
    rw [labels_append]
    exact .br (getElem?_labels hl) hge hfl.labelsOf
  | brIf hl hge hfl _ ih =>
    rw [labels_append] at ih
    simp only [labelsOf, List.map_cons, List.map_append] at ih ⊢
    exact .brIf (getElem?_labels hl) hge hfl.labelsOf ih
  | brTable hl hge hfl =>
    simp only [labelsOf, List.map_cons, List.map_append]
    exact .brTable (fun t ht => ⟨getElem?_labels (hl t ht).1, (hl t ht).2⟩) hge hfl.labelsOf
  | @ret Ls rest pc Pr rs carried st stAny hl hge hfl =>
    rw [labels_append]
    have h := LTyped.ret (C := C.erase) (rest := rest) (pc := pc) (Pr := Pr) (st := labelsOf st)
      (stAny := labelsOf stAny) (last_labels hl) hge hfl.labelsOf
    rw [List.length_map] at h
    exact h
  | call hf hb hfl _ ih =>
    rw [labels_append] at ih ⊢
    exact .call (ft := VFuncTy.erase _) (by simp [VCtx.erase, hf]) hb hfl.labelsOf ih
  | @retCall Ls rest pc Pr i ft ret targs st stAny hf hb hfl hl hge hres =>
    rw [labels_append]
    have h := LTyped.retCall (C := C.erase) (rest := rest) (pc := pc) (Pr := Pr) (st := labelsOf st)
      (stAny := labelsOf stAny) (i := i) (ft := ft.erase) (by simp [VCtx.erase, hf]) hb hfl.labelsOf
      (last_labels hl) hge hres.labelsOf
    rw [List.length_map] at h
    exact h
  | callIndirect h1 hfl _ ih =>
    rw [labels_append] at ih
    simp only [labelsOf, List.map_cons, List.map_append] at ih ⊢
    exact .callIndirect h1 hfl.labelsOf ih
  | @retCallIndirect Ls rest pc Pr l x ps b rs ret targs st stAny h1 hfl hl hgr hres =>
    have h := LTyped.retCallIndirect (C := C.erase) (rest := rest) (pc := pc) (Pr := Pr)
      (st := labelsOf st) (stAny := labelsOf stAny) (l := l) (x := x) h1 hfl.labelsOf
      (last_labels hl) hgr hres.labelsOf
    rw [List.length_map] at h
    simpa only [labelsOf, List.map_cons, List.map_append] using h
  | callRef h1 hfl _ ih =>
    rw [labels_append] at ih
    simp only [labelsOf, List.map_cons, List.map_append] at ih ⊢
    exact .callRef h1 hfl.labelsOf ih
  | unreachable => exact .unreachable
  | throw ht hty hpub =>
    rw [labels_append]
    refine .throw (by simp [VCtx.erase, ht]) ?_ hpub
    simp [labelsOf, ← hty, typesOf]
  | throwRef => exact .throwRef
  | tryTable hfl hres hcl _ _ ihb ihr =>
    rw [labels_append] at ihr ⊢
    exact .tryTable hfl.labelsOf hres (fun c hc => (hcl c hc).erase) ihb ihr

/-- The pc stacks only rise (the paper's `lem:rise`), with value types as without. -/
theorem rise {C : VCtx} {Ls : List VSTy} {e : List Instr} {P P' : Pcs} {st st' : VSTy}
    (h : Typed C Ls e P st P' st') : SFlows P P' :=
  rise_labels h.erase

/-! ### Modules and the theorems -/

/-- A function with value types. -/
structure VFunc where
  ty : VFuncTy
  extra : VSTy
  keep : List Nat
  body : List Instr

def VFunc.erase (f : VFunc) : Func := ⟨f.ty.erase, labelsOf f.extra, f.keep, f.body⟩

/-- The labelled types of a function's locals; one it does not declare is a public `i32`. -/
def VFunc.locals (f : VFunc) : Nat → LTy := fun i => ((f.ty.params ++ f.extra)[i]?).getD (.i32, Lab.L)

def VCtx.enter (C : VCtx) (f : VFunc) : VCtx := { C with locals := f.locals }

theorem VCtx.erase_enter (C : VCtx) (f : VFunc) : (C.enter f).erase = C.erase.enter f.erase := by
  have hloc : (fun i => (f.locals i).2) = f.erase.locals := by
    funext i
    show (((f.ty.params ++ f.extra)[i]?).getD (.i32, Lab.L)).2 =
      ((labelsOf f.ty.params ++ labelsOf f.extra)[i]?).getD Lab.L
    rw [← labels_append]
    unfold labelsOf
    rw [List.getElem?_map]
    cases (f.ty.params ++ f.extra)[i]? <;> rfl
  simp only [VCtx.erase, VCtx.enter, Ctx.enter, hloc]

/-- `WellLTyped` with value types: every function's body is typed, with value types, at its type. -/
def WellTyped (C : VCtx) (F : List VFunc) : Prop :=
  ∀ (i : Nat) (f : VFunc), F[i]? = some f →
    C.funcs[i]? = some f.ty ∧ AllGe f.ty.bound (labelsOf f.ty.results) ∧
      ∃ p, Typed (C.enter f) [f.ty.results] f.body [f.ty.bound] [] [p] f.ty.results ∧
        (p = Lab.L ∨ ∀ j, C.preserved j → j ∈ f.keep)

/-- A module that is well typed with value types is well typed with the types forgotten. -/
theorem WellTyped.erase {C : VCtx} {F : List VFunc} (h : WellTyped C F) :
    WellLTyped C.erase (F.map VFunc.erase) := by
  intro i g hg
  rw [List.getElem?_map] at hg
  cases hf : F[i]? with
  | none => simp [hf] at hg
  | some f =>
    simp only [hf, Option.map_some, Option.some.injEq] at hg
    subst hg
    obtain ⟨hty, hge, p, hbody, hret⟩ := h i f hf
    refine ⟨by simp [VCtx.erase, hty, VFunc.erase], hge, p, ?_, hret⟩
    have := hbody.erase
    rw [VCtx.erase_enter] at this
    exact this

/--
Noninterference for a module that is well typed with value types: `noninterference_labels`, with the
function's type and the context read through `labelsOf` and `VCtx.erase`.
-/
theorem noninterference {C : VCtx} {F : List VFunc} (hF : WellTyped C F)
    (hpub : ∀ i, C.preserved i → (C.globals i).2 = Lab.L) {i : Nat} {f : VFunc}
    (hf : F[i]? = some f) {a0 a1 : List Nat} {s0 s1 : State} {e0 e1 : Ended}
    (ha : StkRel (labelsOf f.ty.params) a0 a1) (hs : LowEq C.erase s0 s1)
    (h0 : Invoke (F.map VFunc.erase) f.erase a0 s0 e0)
    (h1 : Invoke (F.map VFunc.erase) f.erase a1 s1 e1) :
    (∃ r0 t0 r1 t1, e0 = .returned r0 t0 ∧ e1 = .returned r1 t1 ∧
      StkRel (labelsOf f.ty.results) r0 r1 ∧ LowEq C.erase t0 t1) ∨
    (∃ tag w t0 t1, e0 = .threw tag w t0 ∧ e1 = .threw tag w t1 ∧ LowEq C.erase t0 t1) :=
  noninterference_labels hF.erase hpub (i := i) (by simp [hf]) ha hs h0 h1

/-- The same for two runs of the machine. -/
theorem machine_noninterference {C : VCtx} {F : List VFunc}
    (hF : WellTyped C F) (hpub : ∀ i, C.preserved i → (C.globals i).2 = Lab.L) {i : Nat}
    {f : VFunc} (hf : F[i]? = some f) {a0 a1 : List Nat} {s0 s1 : State} {e0 e1 : Ended}
    (ha : StkRel (labelsOf f.ty.params) a0 a1) (hs : LowEq C.erase s0 s1)
    (h0 : Runs (F.map VFunc.erase) (Config.entry f.erase a0 s0) e0)
    (h1 : Runs (F.map VFunc.erase) (Config.entry f.erase a1 s1) e1) :
    (∃ r0 t0 r1 t1, e0 = .returned r0 t0 ∧ e1 = .returned r1 t1 ∧
      StkRel (labelsOf f.ty.results) r0 r1 ∧ LowEq C.erase t0 t1) ∨
    (∃ tag w t0 t1, e0 = .threw tag w t0 ∧ e1 = .threw tag w t1 ∧ LowEq C.erase t0 t1) :=
  noninterference hF hpub hf ha hs (refinement h0) (refinement h1)

/-! ### An example: a 64-bit memory -/

/-- Memory 0 is a 64-bit memory; the locals are public 64-bit integers. -/
def wideCtx : VCtx where
  locals := fun _ => (.i64, Lab.L)
  globals := fun _ => (.i32, Lab.L)
  preserved := fun _ => False
  funcs := []
  table := fun _ => Lab.L
  tags := []
  addr := fun _ => .i64
  taddr := fun _ => .i32

/-- A 64-bit address, and a load of a 64-bit float from it, declared secret. -/
def wideLoad : List Instr := [.localGet 0, .load 0 8 Lab.H, .drop]

theorem wideLoad_typed : Typed wideCtx [[]] wideLoad [Lab.L] [] [Lab.L] [] :=
  .localGet 0 (.load .f64 0 8 Lab.H (.drop .nil))

/-- With the types forgotten it is typed by `LTyped`. -/
example : LTyped wideCtx.erase [[]] wideLoad [Lab.L] [] [Lab.L] [] :=
  wideLoad_typed.erase

/-- A 32-bit address for the 64-bit memory is not typed. -/
example (P' : Pcs) (st' : VSTy) :
    ¬ Typed wideCtx [[]] [.load 0 8 Lab.H] [Lab.L] [(.i32, Lab.L)] P' st' := by
  intro h
  cases h

end WasmIfc
