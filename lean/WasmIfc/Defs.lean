/-
The lift-free typing rules on a core of WebAssembly, and a big-step semantics for it.

The core has one value type (a number), local and global variables, and the structured
control flow that the rules are about: blocks, loops and conditionals with parameters and
results, `br`, `br_if` and `br_table`, and calls of the module's functions. It has no memory.

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
  | select
  | drop
  | nop
  /-- raise labels of the current segment (the paper's `relabel_results`) -/
  | relabel
  | localGet (i : Nat)
  | localSet (i : Nat)
  | globalGet (i : Nat)
  | globalSet (i : Nat)
  | block (ps rs : STy) (body : List Instr)
  | loop (ps rs : STy) (body : List Instr)
  | ite (ps rs : STy) (thn els : List Instr)
  | br (i : Nat)
  | brIf (i : Nat)
  /-- `brTable ts d`: the targets, and the default one -/
  | brTable (ts : List Nat) (d : Nat)
  | call (i : Nat)
  | unreachable

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
  funcs : List FuncTy

/--
`Typed C Ls e P st P' st'`: under the labels `Ls`, the sequence `e` takes the pc stack `P` and
the segment `st` to `P'` and `st'`. Each rule types an instruction followed by the rest of its
sequence. The code after a transfer (`br`, `br_table`, `unreachable`) is not typed, as the
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
  | globalGet {Ls rest pc Pr st P' st'} (i : Nat) :
      Typed C Ls rest (pc :: Pr) (((C.globals i).join pc) :: st) P' st' →
      Typed C Ls (.globalGet i :: rest) (pc :: Pr) st P' st'
  | globalSet {Ls rest pc Pr l st P' st'} (i : Nat) :
      Lab.le pc (C.globals i) → Lab.le l (C.globals i) →
      Typed C Ls rest (pc :: Pr) st P' st' →
      Typed C Ls (.globalSet i :: rest) (pc :: Pr) (l :: st) P' st'
  /-- The results are at least the pc at which the body starts (the paper's Property (E)). -/
  | block {Ls rest pc Pr tin ps rs body p P1 st P' st'} :
      SFlows tin ps → AllGe pc rs →
      Typed C (rs :: Ls) body (pc :: pc :: Pr) ps (p :: P1) rs →
      Typed C Ls rest P1 (rs ++ st) P' st' →
      Typed C Ls (.block ps rs body :: rest) (pc :: Pr) (tin ++ st) P' st'
  /-- The body starts at a pc `pcL` of the rule's choice, and must end at most there. -/
  | loop {Ls rest pc Pr pcL tin ps rs body p P1 st P' st'} :
      Lab.le pc pcL → Lab.le p pcL → SFlows tin ps → AllGe pcL rs →
      Typed C (ps :: Ls) body (pcL :: pc :: Pr) ps (p :: P1) rs →
      Typed C Ls rest P1 (rs ++ st) P' st' →
      Typed C Ls (.loop ps rs body :: rest) (pc :: Pr) (tin ++ st) P' st'
  | ite {Ls rest pc Pr l tin ps rs thn els p1 P1 p2 P2 st P' st'} :
      SFlows tin ps → AllGe (pc.join l) rs →
      Typed C (rs :: Ls) thn (pc.join l :: pc :: Pr) ps (p1 :: P1) rs →
      Typed C (rs :: Ls) els (pc.join l :: pc :: Pr) ps (p2 :: P2) rs →
      Typed C Ls rest (joinEach P1 P2) (rs ++ st) P' st' →
      Typed C Ls (.ite ps rs thn els :: rest) (pc :: Pr) (l :: (tin ++ st)) P' st'
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
  /-- The caller's pc flows into the callee's bound. The arguments keep their own labels, below the parameters'. -/
  | call {Ls rest pc Pr i ft targs st P' st'} :
      C.funcs[i]? = some ft → Lab.le pc ft.bound → SFlows targs ft.params →
      Typed C Ls rest (pc :: Pr) (ft.results ++ st) P' st' →
      Typed C Ls (.call i :: rest) (pc :: Pr) (targs ++ st) P' st'
  | unreachable {Ls rest P st stAny} :
      Typed C Ls (.unreachable :: rest) P st P stAny

/-- A function: its type, the levels of its local variables that are not parameters, and its body. -/
structure Func where
  ty : FuncTy
  extra : List Lab
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
is the result type, from the empty segment, at the function's bound.
-/
def WellTyped (C : Ctx) (F : List Func) : Prop :=
  ∀ (i : Nat) (f : Func), F[i]? = some f →
    C.funcs[i]? = some f.ty ∧
      ∃ P', Typed (C.enter f) [f.ty.results] f.body [f.ty.bound] [] P' f.ty.results

/-- The values of the local and of the global variables. -/
structure State where
  loc : Nat → Nat
  glob : Nat → Nat

def State.setLoc (s : State) (i v : Nat) : State :=
  { s with loc := fun j => if j = i then v else s.loc j }

def State.setGlob (s : State) (i v : Nat) : State :=
  { s with glob := fun j => if j = i then v else s.glob j }

/--
How a sequence ends: at its end, with the current segment of the stack, or by a branch to the
`i`-th enclosing label with the values the branch carries.
-/
inductive Out where
  | normal (σ : List Nat) (s : State)
  | br (i : Nat) (w : List Nat) (s : State)

def Out.state : Out → State
  | .normal _ s => s
  | .br _ _ s => s

def Out.isBr : Out → Prop
  | .normal _ _ => False
  | .br _ _ _ => True

/-- What a block continues with after its body: the body's results, or the values of a branch to its own label. -/
def Out.lands : Out → Option (List Nat × State)
  | .normal σ s => some (σ, s)
  | .br 0 w s => some (w, s)
  | .br (_ + 1) _ _ => none

/-- A branch past the block, as the block's own outcome. -/
def Out.exits : Out → Option Out
  | .br (i + 1) w s => some (.br i w s)
  | _ => none

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
`unreachable` has no rule: it traps.
-/
inductive Eval (F : List Func) : Nat → List Nat → List Instr → List Nat → State → Out → Prop where
  | nil {ls σ s} : Eval F 0 ls [] σ s (.normal σ s)
  | const {n ls rest σ s o} (v : Nat) :
      Eval F n ls rest (v :: σ) s o → Eval F (n + 1) ls (.const v :: rest) σ s o
  | binop {n ls rest a b σ s o} (f : Nat → Nat → Nat) :
      Eval F n ls rest (f b a :: σ) s o → Eval F (n + 1) ls (.binop f :: rest) (a :: b :: σ) s o
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
  | globalGet {n ls rest σ s o} (i : Nat) :
      Eval F n ls rest (s.glob i :: σ) s o → Eval F (n + 1) ls (.globalGet i :: rest) σ s o
  | globalSet {n ls rest v σ s o} (i : Nat) :
      Eval F n ls rest σ (s.setGlob i v) o → Eval F (n + 1) ls (.globalSet i :: rest) (v :: σ) s o
  | blockCont {n1 n2 ls rest ps rs body vs base s ob σ1 s1 o} :
      vs.length = ps.length →
      Eval F n1 (rs.length :: ls) body vs s ob → ob.lands = some (σ1, s1) →
      Eval F n2 ls rest (σ1 ++ base) s1 o →
      Eval F (n1 + n2 + 1) ls (.block ps rs body :: rest) (vs ++ base) s o
  | blockExit {n1 ls rest ps rs body vs base s ob o} :
      vs.length = ps.length →
      Eval F n1 (rs.length :: ls) body vs s ob → ob.exits = some o →
      Eval F (n1 + 1) ls (.block ps rs body :: rest) (vs ++ base) s o
  | loopDone {n1 n2 ls rest ps rs body vs base s σ1 s1 o} :
      vs.length = ps.length →
      Eval F n1 (ps.length :: ls) body vs s (.normal σ1 s1) →
      Eval F n2 ls rest (σ1 ++ base) s1 o →
      Eval F (n1 + n2 + 1) ls (.loop ps rs body :: rest) (vs ++ base) s o
  | loopAgain {n1 n2 ls rest ps rs body vs base s w s1 o} :
      vs.length = ps.length →
      Eval F n1 (ps.length :: ls) body vs s (.br 0 w s1) →
      Eval F n2 ls (.loop ps rs body :: rest) (w ++ base) s1 o →
      Eval F (n1 + n2 + 1) ls (.loop ps rs body :: rest) (vs ++ base) s o
  | loopExit {n1 ls rest ps rs body vs base s ob o} :
      vs.length = ps.length →
      Eval F n1 (ps.length :: ls) body vs s ob → ob.exits = some o →
      Eval F (n1 + 1) ls (.loop ps rs body :: rest) (vs ++ base) s o
  | iteCont {n1 n2 ls rest ps rs thn els c vs base s ob σ1 s1 o} :
      vs.length = ps.length →
      Eval F n1 (rs.length :: ls) (if c = 0 then els else thn) vs s ob → ob.lands = some (σ1, s1) →
      Eval F n2 ls rest (σ1 ++ base) s1 o →
      Eval F (n1 + n2 + 1) ls (.ite ps rs thn els :: rest) (c :: (vs ++ base)) s o
  | iteExit {n1 ls rest ps rs thn els c vs base s ob o} :
      vs.length = ps.length →
      Eval F n1 (rs.length :: ls) (if c = 0 then els else thn) vs s ob → ob.exits = some o →
      Eval F (n1 + 1) ls (.ite ps rs thn els :: rest) (c :: (vs ++ base)) s o
  | br {ls rest i n σ s} :
      ls[i]? = some n → Eval F 1 ls (.br i :: rest) σ s (.br i (σ.take n) s)
  | brIfTaken {ls rest i n c σ s} :
      c ≠ 0 → ls[i]? = some n → Eval F 1 ls (.brIf i :: rest) (c :: σ) s (.br i (σ.take n) s)
  | brIfNot {n ls rest i σ s o} :
      Eval F n ls rest σ s o → Eval F (n + 1) ls (.brIf i :: rest) (0 :: σ) s o
  | brTable {ls rest ts d c n σ s} :
      ls[tableTarget ts d c]? = some n →
      Eval F 1 ls (.brTable ts d :: rest) (c :: σ) s (.br (tableTarget ts d c) (σ.take n) s)
  /-- The callee ends at the end of its body or by a branch to its label (a `return`). -/
  | call {n1 n2 ls rest i f args base s ob r t o} :
      F[i]? = some f → args.length = f.ty.params.length →
      Eval F n1 [f.ty.results.length] f.body [] { loc := frame args, glob := s.glob } ob →
      ob.lands = some (r, t) →
      Eval F n2 ls rest (r ++ base) { loc := s.loc, glob := t.glob } o →
      Eval F (n1 + n2 + 1) ls (.call i :: rest) (args ++ base) s o

end WasmIfc
