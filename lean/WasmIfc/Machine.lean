import WasmIfc.Statement

/-!
# The machine, and that the big-step semantics describes it

A small-step machine for the core, shaped like the interpreter's `step`
(`src/Runtime/Interpreter.hs`): a configuration is a state (the store and the local variables),
the operands of the current block, the rest of the block, and a control stack of labels and
call boundaries. One transition runs one instruction.

`refinement` says that a run of the machine from the call of a function to an end is a
derivation of `Eval` with the same end, and `machine_noninterference` is the theorem of
`Statement.lean` about two runs of the machine. What remains by inspection is that this
machine is the Haskell one; `STATEMENTS.md` puts the two side by side.
-/

namespace WasmIfc

/--
An entry of the control stack.

A label holds what is needed where control comes out of its block: the globals the block
compares and the state at its start (`keep`, `recorded`), the operands that were below the
block's own, and the code after the block. A `try_table`'s label holds its clauses too; that of
a block or a conditional has none. A loop's label holds the loop's body besides, which a branch
to it runs again.

A call boundary holds the same for the caller, and the caller's local variables. It has a list
of comparisons, since a tail call adds its callee's to those of the function it replaces.
-/
inductive Frame where
  | label (n : Nat) (clauses : List (Option Nat × Nat × Bool)) (keep : List Nat) (recorded : State)
      (base : List Nat) (rest : List Instr)
  | loop (ps rs : STy) (body : List Instr) (keep : List Nat) (recorded : State)
      (base : List Nat) (rest : List Instr)
  | call (n : Nat) (checks : List (List Nat × State)) (locals : Nat → Nat)
      (base : List Nat) (rest : List Instr)

/-- A configuration of the machine. The local variables are those of `s`. -/
structure Config where
  s : State
  σ : List Nat
  e : List Instr
  K : List Frame

/-- What a transition gives: the next configuration, or the end of the run. -/
inductive Next where
  | go (c : Config)
  | stop (e : Ended)

/-- The arities of the labels of the running function: its blocks', then its own. -/
def labels : List Frame → List Nat
  | [] => []
  | .label n _ _ _ _ _ :: K => n :: labels K
  | .loop ps _ _ _ _ _ _ :: K => ps.length :: labels K
  | .call n _ _ _ _ :: _ => [n]

/-- The boundary of the running function, and the control stack of its caller. -/
def boundary : List Frame →
    Option (List (List Nat × State) × (Nat → Nat) × List Nat × List Instr × List Frame)
  | [] => none
  | .label _ _ _ _ _ _ :: K => boundary K
  | .loop _ _ _ _ _ _ _ :: K => boundary K
  | .call _ checks locals base rest :: K => some (checks, locals, base, rest, K)

/--
`Basic i σ s σ' s'`: the instruction `i`, which is not one of control, takes the operands `σ`
and the state `s` to `σ'` and `s'`. An instruction that traps takes them nowhere.
-/
inductive Basic : Instr → List Nat → State → List Nat → State → Prop where
  | const {σ s} (v : Nat) : Basic (.const v) σ s (v :: σ) s
  | binop {a b σ s} (f : Nat → Nat → Nat) : Basic (.binop f) (a :: b :: σ) s (f b a :: σ) s
  | unop {a σ s} (f : Nat → Nat) : Basic (.unop f) (a :: σ) s (f a :: σ) s
  | partialBinop {a b v σ s} (f : Nat → Nat → Option Nat) :
      f b a = some v → Basic (.partialBinop f) (a :: b :: σ) s (v :: σ) s
  | partialUnop {a v σ s} (f : Nat → Option Nat) :
      f a = some v → Basic (.partialUnop f) (a :: σ) s (v :: σ) s
  | dup {a σ s} : Basic .dup (a :: σ) s (a :: a :: σ) s
  | select {c v1 v2 σ s} :
      Basic .select (c :: v1 :: v2 :: σ) s ((if c = 0 then v1 else v2) :: σ) s
  | drop {v σ s} : Basic .drop (v :: σ) s σ s
  | nop {σ s} : Basic .nop σ s σ s
  | relabel {σ s} : Basic .relabel σ s σ s
  | localGet {σ s} (i : Nat) : Basic (.localGet i) σ s (s.loc i :: σ) s
  | localSet {v σ s} (i : Nat) : Basic (.localSet i) (v :: σ) s σ (s.setLoc i v)
  | localTee {v σ s} (i : Nat) : Basic (.localTee i) (v :: σ) s (v :: σ) (s.setLoc i v)
  | globalGet {σ s} (i : Nat) : Basic (.globalGet i) σ s (s.glob i :: σ) s
  | globalSet {v σ s} (i : Nat) : Basic (.globalSet i) (v :: σ) s σ (s.setGlob i v)
  | load {a σ s} (w : Nat) (lm : Lab) :
      a + w ≤ s.size → (∀ i, i < w → Lab.le (s.lab (a + i)) lm) →
      Basic (.load w lm) (a :: σ) s (s.word a w :: σ) s
  | store {v a σ s} (w : Nat) (lm : Lab) :
      a + w ≤ s.size → Basic (.store w lm) (v :: a :: σ) s σ (s.put a (bytesOf v w) lm)
  | fill {k v a σ s} (lm : Lab) :
      a + k ≤ s.size → Basic (.fill lm) (k :: v :: a :: σ) s σ (s.fill a v k lm)
  | copy {k b a σ s} (lm : Lab) :
      a + k ≤ s.size → b + k ≤ s.size →
      Basic (.copy lm) (k :: b :: a :: σ) s σ (s.copy a b k lm)
  | copyTo {k b a σ s} (lm : Lab) :
      a + k ≤ s.size2 → b + k ≤ s.size →
      Basic (.copyTo lm) (k :: b :: a :: σ) s σ (s.copyTo a b k lm)
  | copyFrom {k b a σ s} (lm : Lab) :
      a + k ≤ s.size → b + k ≤ s.size2 →
      Basic (.copyFrom lm) (k :: b :: a :: σ) s σ (s.copyFrom a b k lm)
  | tableGet {c σ s} : c < s.tsize → Basic .tableGet (c :: σ) s (refOf (s.tbl c) :: σ) s
  | tableSet {v c σ s} :
      c < s.tsize → Basic .tableSet (v :: c :: σ) s σ (s.setTbl c (ofRef v))
  | tableFill {k v c σ s} :
      c + k ≤ s.tsize → Basic .tableFill (k :: v :: c :: σ) s σ (s.fillTbl c (ofRef v) k)
  | tableCopy {k b a σ s} :
      a + k ≤ s.tsize → b + k ≤ s.tsize →
      Basic .tableCopy (k :: b :: a :: σ) s σ (s.copyTbl a b k)
  | tableSize {σ s} : Basic .tableSize σ s (s.tsize :: σ) s
  | tableGrow {d v σ s} :
      Basic .tableGrow (d :: v :: σ) s ((s.growTbl d (ofRef v)).1 :: σ) (s.growTbl d (ofRef v)).2
  | hostRead {np k a fd c σ s} :
      s.fdt fd = some c → a + k ≤ s.size → np < s.size →
      Basic .hostRead (np :: k :: a :: fd :: σ) s σ
        (((s.put a ((s.inp c).take k) (s.chan c)).setMem np ((s.inp c).take k).length
          (s.chan c)).consume c k)
  | hostWrite {k a fd c σ s} :
      s.fdt fd = some c → a + k ≤ s.size →
      (∀ x, a ≤ x → x < a + k → Lab.le (s.lab x) (s.chan c)) →
      Basic .hostWrite (k :: a :: fd :: σ) s σ (s.emit c (s.cells a k))
  | hostOpen {p o k a fd c d σ s} :
      s.fdt fd = some c → a + k ≤ s.size → p < s.size →
      (∀ x, a ≤ x → x < a + k → s.lab x = Lab.L) →
      (s.cells a k ∈ s.names c ∨ o % 2 = 1) → s.fresh d →
      Basic .hostOpen (p :: o :: k :: a :: fd :: σ) s (0 :: σ)
        ((s.openAt c (s.cells a k) d).setMem p d Lab.L)
  | hostOpenNone {p o k a fd c σ s} :
      s.fdt fd = some c → a + k ≤ s.size → p < s.size →
      (∀ x, a ≤ x → x < a + k → s.lab x = Lab.L) →
      s.cells a k ∉ s.names c → o % 2 ≠ 1 →
      Basic .hostOpen (p :: o :: k :: a :: fd :: σ) s (noEntry :: σ) s
  | memInit {c b a σ s} (k : Nat) (lm : Lab) :
      a + c ≤ s.size → b + c ≤ (s.segs k).length →
      Basic (.memInit k lm) (c :: b :: a :: σ) s σ (s.put a (((s.segs k).drop b).take c) lm)
  | dataDrop {σ s} (k : Nat) : Basic (.dataDrop k) σ s σ (s.dropSeg k)
  | memSize {σ s} : Basic .memSize σ s (s.size :: σ) s
  | memGrow {d σ s} : Basic .memGrow (d :: σ) s ((s.grow d).1 :: σ) (s.grow d).2
  /-- a conditional branch that is not taken -/
  | brIfNot {σ s} (i : Nat) : Basic (.brIf i) (0 :: σ) s σ s

/--
`Unwind K i w s c`: a branch to the `i`-th label with the values `w` leaves the control stack
`K` and the state `s` for the configuration `c`. The labels it passes are dropped with their
comparisons. A block's label is left for the code after the block, behind the block's
comparison; a loop's label stays, and the body runs again; the function's own label is its
boundary, and the branch a return.
-/
inductive Unwind : List Frame → Nat → List Nat → State → Config → Prop where
  | label {n cl keep g base rest K w s} :
      Kept keep g s → Unwind (.label n cl keep g base rest :: K) 0 w s ⟨s, w ++ base, rest, K⟩
  | loop {ps rs body keep g base rest K w s} :
      Unwind (.loop ps rs body keep g base rest :: K) 0 w s
        ⟨s, w, body, .loop ps rs body keep g base rest :: K⟩
  | call {n checks locals base rest K w s} :
      (∀ c, c ∈ checks → Kept c.1 c.2 s) →
      Unwind (.call n checks locals base rest :: K) 0 w s
        ⟨{ s with loc := locals }, w ++ base, rest, K⟩
  | pastLabel {n cl keep g base rest K i w s c} :
      Unwind K i w s c → Unwind (.label n cl keep g base rest :: K) (i + 1) w s c
  | pastLoop {ps rs body keep g base rest K i w s c} :
      Unwind K i w s c → Unwind (.loop ps rs body keep g base rest :: K) (i + 1) w s c

/--
`Raise K t w s nx`: an exception of tag `t` with the values `w` leaves the control stack `K`
and the state `s` for `nx`. The first label with a clause for it turns it into a branch from
around its block, with a new reference to the exception if the clause is by reference. A call boundary gives the caller its local variables back and no comparison
is made. Below the last boundary the exception ends the run.
-/
inductive Raise : List Frame → Nat → List Nat → State → Next → Prop where
  | escaped {t w s} : Raise [] t w s (.stop (.threw t w s))
  | caught {n cl keep g base rest K t w s j carry r c} :
      catches cl t = some (j, carry, r) →
      Unwind K j (s.handed t w carry r).1 (s.handed t w carry r).2 c →
      Raise (.label n cl keep g base rest :: K) t w s (.go c)
  | pastLabel {n cl keep g base rest K t w s nx} :
      catches cl t = none → Raise K t w s nx → Raise (.label n cl keep g base rest :: K) t w s nx
  | pastLoop {ps rs body keep g base rest K t w s nx} :
      Raise K t w s nx → Raise (.loop ps rs body keep g base rest :: K) t w s nx
  | pastCall {n checks locals base rest K t w s nx} :
      Raise K t w { s with loc := locals } nx →
      Raise (.call n checks locals base rest :: K) t w s nx

/--
One transition of the machine. Where the current block has ended, the top of the control stack
says what follows. A call pushes a boundary and runs the callee's body on no operands; a tail
call puts its callee in the place of the running function, whose labels are dropped.
-/
inductive Step (F : List Func) : Config → Next → Prop where
  | basic {i σ s σ' s' rest K} :
      Basic i σ s σ' s' → Step F ⟨s, σ, i :: rest, K⟩ (.go ⟨s', σ', rest, K⟩)
  | block {keep ps rs body rest vs base s K} :
      vs.length = ps.length →
      Step F ⟨s, vs ++ base, .block keep ps rs body :: rest, K⟩
        (.go ⟨s, vs, body, .label rs.length [] keep s base rest :: K⟩)
  | tryTable {keep ps rs clauses body rest vs base s K} :
      vs.length = ps.length →
      Step F ⟨s, vs ++ base, .tryTable keep ps rs clauses body :: rest, K⟩
        (.go ⟨s, vs, body, .label rs.length clauses keep s base rest :: K⟩)
  | loop {keep ps rs body rest vs base s K} :
      vs.length = ps.length →
      Step F ⟨s, vs ++ base, .loop keep ps rs body :: rest, K⟩
        (.go ⟨s, vs, body, .loop ps rs body keep s base rest :: K⟩)
  | ite {keep ps rs thn els rest c vs base s K} :
      vs.length = ps.length →
      Step F ⟨s, c :: (vs ++ base), .ite keep ps rs thn els :: rest, K⟩
        (.go ⟨s, vs, if c = 0 then els else thn, .label rs.length [] keep s base rest :: K⟩)
  | br {i n σ s rest K c} :
      (labels K)[i]? = some n → Unwind K i (σ.take n) s c →
      Step F ⟨s, σ, .br i :: rest, K⟩ (.go c)
  | brIf {i n v σ s rest K c} :
      v ≠ 0 → (labels K)[i]? = some n → Unwind K i (σ.take n) s c →
      Step F ⟨s, v :: σ, .brIf i :: rest, K⟩ (.go c)
  | brTable {ts d n v σ s rest K c} :
      (labels K)[tableTarget ts d v]? = some n → Unwind K (tableTarget ts d v) (σ.take n) s c →
      Step F ⟨s, v :: σ, .brTable ts d :: rest, K⟩ (.go c)
  | ret {n σ s rest K c} :
      (labels K)[(labels K).length - 1]? = some n →
      Unwind K ((labels K).length - 1) (σ.take n) s c →
      Step F ⟨s, σ, .ret :: rest, K⟩ (.go c)
  | endLabel {n cl keep g base rest K σ s} :
      Kept keep g s →
      Step F ⟨s, σ, [], .label n cl keep g base rest :: K⟩ (.go ⟨s, σ ++ base, rest, K⟩)
  | endLoop {ps rs body keep g base rest K σ s} :
      Kept keep g s →
      Step F ⟨s, σ, [], .loop ps rs body keep g base rest :: K⟩ (.go ⟨s, σ ++ base, rest, K⟩)
  | endCall {n checks locals base rest K σ s} :
      (∀ c, c ∈ checks → Kept c.1 c.2 s) →
      Step F ⟨s, σ, [], .call n checks locals base rest :: K⟩
        (.go ⟨{ s with loc := locals }, σ ++ base, rest, K⟩)
  | done {σ s} : Step F ⟨s, σ, [], []⟩ (.stop (.returned σ s))
  | call {i f args base rest s K} :
      F[i]? = some f → args.length = f.ty.params.length →
      Step F ⟨s, args ++ base, .call i :: rest, K⟩
        (.go ⟨{ s with loc := frame args }, [], f.body,
          .call f.ty.results.length [(f.keep, s)] s.loc base rest :: K⟩)
  | callIndirect {ps b rs v i f args base rest s K} :
      s.entry v = some i → F[i]? = some f → f.ty.params = ps → f.ty.results = rs →
      Lab.le b f.ty.bound → args.length = ps.length →
      Step F ⟨s, v :: (args ++ base), .callIndirect ps b rs :: rest, K⟩
        (.go ⟨{ s with loc := frame args }, [], f.body,
          .call rs.length [(f.keep, s)] s.loc base rest :: K⟩)
  | callRef {ps b rs v i f args base rest s K} :
      ofRef v = some i → F[i]? = some f → f.ty.params = ps → f.ty.results = rs →
      Lab.le b f.ty.bound → args.length = ps.length →
      Step F ⟨s, v :: (args ++ base), .callRef ps b rs :: rest, K⟩
        (.go ⟨{ s with loc := frame args }, [], f.body,
          .call rs.length [(f.keep, s)] s.loc base rest :: K⟩)
  | retCall {i f args base rest s K checks locals base' rest' K'} :
      F[i]? = some f → args.length = f.ty.params.length →
      boundary K = some (checks, locals, base', rest', K') →
      Step F ⟨s, args ++ base, .retCall i :: rest, K⟩
        (.go ⟨{ s with loc := frame args }, [], f.body,
          .call f.ty.results.length ((f.keep, s) :: checks) locals base' rest' :: K'⟩)
  | retCallIndirect {ps b rs v i f args base rest s K checks locals base' rest' K'} :
      s.entry v = some i → F[i]? = some f → f.ty.params = ps → f.ty.results = rs →
      Lab.le b f.ty.bound → args.length = ps.length →
      boundary K = some (checks, locals, base', rest', K') →
      Step F ⟨s, v :: (args ++ base), .retCallIndirect ps b rs :: rest, K⟩
        (.go ⟨{ s with loc := frame args }, [], f.body,
          .call rs.length ((f.keep, s) :: checks) locals base' rest' :: K'⟩)
  | throw {t k σ s rest K nx} :
      Raise K t (σ.take k) s nx → Step F ⟨s, σ, .throw t k :: rest, K⟩ nx
  | throwRef {i t w σ s rest K nx} :
      s.exns[i]? = some (t, w) → Raise K t w s nx →
      Step F ⟨s, (i + 1) :: σ, .throwRef :: rest, K⟩ nx

/-- A run of the machine to its end. A run that traps or goes on forever has none. -/
inductive Runs (F : List Func) : Config → Ended → Prop where
  | stop {c e} : Step F c (.stop e) → Runs F c e
  | go {c c' e} : Step F c (.go c') → Runs F c' e → Runs F c e

/--
The configuration that calls `f` from outside on the arguments `a` in the state `s`: the body
on no operands, above the one boundary that compares the globals `f` names and gives the local
variables of whoever called back.
-/
def Config.entry (f : Func) (a : List Nat) (s : State) : Config :=
  ⟨{ s with loc := frame a }, [], f.body, [.call f.ty.results.length [(f.keep, s)] s.loc [] []]⟩

/-! ### From a run of the machine to a derivation -/

theorem Basic.eval {F : List Func} {n : Nat} {ls : List Nat} {i : Instr} {rest : List Instr}
    {σ σ' : List Nat} {s s' : State} {o : Out} (h : Basic i σ s σ' s')
    (he : Eval F n ls rest σ' s' o) : Eval F (n + 1) ls (i :: rest) σ s o := by
  cases h with
  | hostOpen h1 h2 h3 h4 h5 h6 => exact .hostOpen h1 h2 h3 h4 h5 h6 he
  | hostOpenNone h1 h2 h3 h4 h5 h6 => exact .hostOpenNone h1 h2 h3 h4 h5 h6 he
  | _ => constructor <;> assumption

theorem caught_nil (o : Out) : o.caught [] = o := by
  cases o <;> rfl

/--
What the iterations of a loop's body make of one run of the body: the outcome of the
iterations from there on.
-/
inductive IterOut (F : List Func) (ls : List Nat) (ps rs : STy) (body : List Instr) :
    Out → Out → Prop where
  | done {σ s} : IterOut F ls ps rs body (.normal σ s) (.normal σ s)
  | again {m w s o} :
      Eval F m ls [.iter ps rs body] w s o → IterOut F ls ps rs body (.br 0 w s) o
  | exit {i w s} : IterOut F ls ps rs body (.br (i + 1) w s) (.br (i + 1) w s)
  | exn {t w s} : IterOut F ls ps rs body (.exn t w s) (.exn t w s)
  | tailExn {t w s} : IterOut F ls ps rs body (.tailExn t w s) (.tailExn t w s)

theorem IterOut.eval {F : List Func} {l n : Nat} {ls : List Nat} {ps rs : STy}
    {body : List Instr} {vs : List Nat} {s : State} {ob o : Out}
    (hb : Eval F n (ps.length :: ls) body vs s ob) (h : IterOut F (l :: ls) ps rs body ob o) :
    ∃ m, Eval F m (l :: ls) [.iter ps rs body] vs s o := by
  cases h with
  | done => exact ⟨_, .iterDone hb⟩
  | again hr => exact ⟨_, .iterAgain hb hr⟩
  | exit => exact ⟨_, .iterExit hb⟩
  | exn => exact ⟨_, .iterExn hb⟩
  | tailExn => exact ⟨_, .iterTailExn hb⟩

/--
`Fin F K o e`: the current block ends as `o` under the control stack `K`, and by the big-step
semantics the run then ends as `e`. Each entry of the stack is the premises that the rule of
its construct has after the body's.
-/
inductive Fin (F : List Func) : List Frame → Out → Ended → Prop where
  | returned {σ s} : Fin F [] (.normal σ s) (.returned σ s)
  | threw {t w s} : Fin F [] (.exn t w s) (.threw t w s)
  | labelLand {n cl keep g base rest K ob σ1 s1 m o e} :
      (ob.caught cl).lands = some (σ1, s1) → Kept keep g s1 →
      Eval F m (labels K) rest (σ1 ++ base) s1 o → Fin F K o e →
      Fin F (.label n cl keep g base rest :: K) ob e
  | labelExit {n cl keep g base rest K ob o e} :
      (ob.caught cl).exits = some o → Fin F K o e →
      Fin F (.label n cl keep g base rest :: K) ob e
  | loopLand {ps rs body keep g base rest K ob obi σ1 s1 m o e} :
      IterOut F (rs.length :: labels K) ps rs body ob obi → obi.lands = some (σ1, s1) →
      Kept keep g s1 → Eval F m (labels K) rest (σ1 ++ base) s1 o → Fin F K o e →
      Fin F (.loop ps rs body keep g base rest :: K) ob e
  | loopExit {ps rs body keep g base rest K ob obi o e} :
      IterOut F (rs.length :: labels K) ps rs body ob obi → obi.exits = some o → Fin F K o e →
      Fin F (.loop ps rs body keep g base rest :: K) ob e
  | callLand {n checks locals base rest K ob r t m o e} :
      ob.lands = some (r, t) → (∀ c, c ∈ checks → Kept c.1 c.2 t) →
      Eval F m (labels K) rest (r ++ base) { t with loc := locals } o → Fin F K o e →
      Fin F (.call n checks locals base rest :: K) ob e
  | callThrown {n checks locals base rest K ob t w u e} :
      ob.thrown = some (t, w, u) → Fin F K (.exn t w { u with loc := locals }) e →
      Fin F (.call n checks locals base rest :: K) ob e

/-- A configuration ends as `e` by the big-step semantics. -/
def Sem (F : List Func) (c : Config) (e : Ended) : Prop :=
  ∃ n o, Eval F n (labels c.K) c.e c.σ c.s o ∧ Fin F c.K o e

def SemNext (F : List Func) : Next → Ended → Prop
  | .go c, e => Sem F c e
  | .stop e', e => e' = e

theorem Unwind.fin {F : List Func} {K : List Frame} {i : Nat} {w : List Nat} {s : State}
    {c : Config} {e : Ended} (h : Unwind K i w s c) : Sem F c e → Fin F K (.br i w s) e := by
  induction h with
  | label hk =>
    rintro ⟨n, o, he, hf⟩
    exact .labelLand rfl hk he hf
  | loop =>
    rintro ⟨n, o, he, hf⟩
    cases hf with
    | loopLand hi hl hk hr hf' =>
      obtain ⟨m, hit⟩ := hi.eval he
      exact .loopLand (.again hit) hl hk hr hf'
    | loopExit hi hx hf' =>
      obtain ⟨m, hit⟩ := hi.eval he
      exact .loopExit (.again hit) hx hf'
  | call hk =>
    rintro ⟨n, o, he, hf⟩
    exact .callLand rfl hk he hf
  | pastLabel _ ih => exact fun hs => .labelExit rfl (ih hs)
  | pastLoop _ ih => exact fun hs => .loopExit .exit rfl (ih hs)

theorem Raise.fin {F : List Func} {K : List Frame} {t : Nat} {w : List Nat} {s : State}
    {nx : Next} {e : Ended} (h : Raise K t w s nx) : SemNext F nx e → Fin F K (.exn t w s) e := by
  induction h with
  | escaped =>
    intro hs
    cases hs
    exact .threw
  | caught hc hu =>
    intro hs
    exact .labelExit (by simp [Out.caught, hc, Out.exits]) (hu.fin hs)
  | pastLabel hc _ ih =>
    intro hs
    exact .labelExit (by simp [Out.caught, hc, Out.exits]) (ih hs)
  | pastLoop _ ih => exact fun hs => .loopExit .exn rfl (ih hs)
  | pastCall _ ih => exact fun hs => .callThrown rfl (ih hs)

theorem labels_pos {K : List Frame}
    {x : List (List Nat × State) × (Nat → Nat) × List Nat × List Instr × List Frame}
    (h : boundary K = some x) : 0 < (labels K).length := by
  induction K with
  | nil => simp [boundary] at h
  | cons fr K ih =>
    cases fr <;> simp [labels]

/-- A return, seen from inside the function's blocks: a branch to the outermost label. -/
theorem boundary_ret {F : List Func} {K K' : List Frame} {checks : List (List Nat × State)}
    {locals : Nat → Nat} {base : List Nat} {rest : List Instr} {r : List Nat} {t : State}
    {m : Nat} {o : Out} {e : Ended} (h : boundary K = some (checks, locals, base, rest, K'))
    (hk : ∀ c, c ∈ checks → Kept c.1 c.2 t)
    (he : Eval F m (labels K') rest (r ++ base) { t with loc := locals } o) (hf : Fin F K' o e) :
    Fin F K (.br ((labels K).length - 1) r t) e := by
  induction K with
  | nil => simp [boundary] at h
  | cons fr K ih =>
    cases fr with
    | label n cl keep g base0 rest0 =>
      have hpos := labels_pos (K := K) h
      have hidx : (labels (.label n cl keep g base0 rest0 :: K)).length - 1
          = ((labels K).length - 1) + 1 := by
        simp only [labels, List.length_cons]
        omega
      rw [hidx]
      exact .labelExit rfl (ih h)
    | loop ps rs body keep g base0 rest0 =>
      have hpos := labels_pos (K := K) h
      have hidx : (labels (.loop ps rs body keep g base0 rest0 :: K)).length - 1
          = ((labels K).length - 1) + 1 := by
        simp only [labels, List.length_cons]
        omega
      rw [hidx]
      exact .loopExit .exit rfl (ih h)
    | call n checks0 locals0 base0 rest0 =>
      simp only [boundary, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      exact .callLand rfl hk he hf

/-- The exception of a tail call's callee passes the labels of the function that made the call. -/
theorem boundary_thrown {F : List Func} {K K' : List Frame} {checks : List (List Nat × State)}
    {locals : Nat → Nat} {base : List Nat} {rest : List Instr} {t : Nat} {w : List Nat}
    {u : State} {e : Ended} (h : boundary K = some (checks, locals, base, rest, K'))
    (hf : Fin F K' (.exn t w { u with loc := locals }) e) : Fin F K (.tailExn t w u) e := by
  induction K with
  | nil => simp [boundary] at h
  | cons fr K ih =>
    cases fr with
    | label n cl keep g base0 rest0 => exact .labelExit rfl (ih h)
    | loop ps rs body keep g base0 rest0 => exact .loopExit .tailExn rfl (ih h)
    | call n checks0 locals0 base0 rest0 =>
      simp only [boundary, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      exact .callThrown rfl hf

/-- One transition back: what the big-step semantics says of the next configuration, it says of this one. -/
theorem Step.sem {F : List Func} {c : Config} {nx : Next} {e : Ended} (h : Step F c nx)
    (hs : SemNext F nx e) : Sem F c e := by
  cases h with
  | basic hb =>
    obtain ⟨n, o, he, hf⟩ := hs
    exact ⟨_, o, hb.eval he, hf⟩
  | block hvs =>
    obtain ⟨n, o, he, hf⟩ := hs
    cases hf with
    | labelLand hl hk hr hf' =>
      rw [caught_nil] at hl
      exact ⟨_, _, .blockCont hvs he hl hk hr, hf'⟩
    | labelExit hx hf' =>
      rw [caught_nil] at hx
      exact ⟨_, _, .blockExit hvs he hx, hf'⟩
  | tryTable hvs =>
    obtain ⟨n, o, he, hf⟩ := hs
    cases hf with
    | labelLand hl hk hr hf' => exact ⟨_, _, .tryCont hvs he hl hk hr, hf'⟩
    | labelExit hx hf' => exact ⟨_, _, .tryExit hvs he hx, hf'⟩
  | loop hvs =>
    obtain ⟨n, o, he, hf⟩ := hs
    cases hf with
    | loopLand hi hl hk hr hf' =>
      obtain ⟨m, hit⟩ := hi.eval he
      exact ⟨_, _, .loopCont hvs hit hl hk hr, hf'⟩
    | loopExit hi hx hf' =>
      obtain ⟨m, hit⟩ := hi.eval he
      exact ⟨_, _, .loopExit hvs hit hx, hf'⟩
  | ite hvs =>
    obtain ⟨n, o, he, hf⟩ := hs
    cases hf with
    | labelLand hl hk hr hf' =>
      rw [caught_nil] at hl
      exact ⟨_, _, .iteCont hvs he hl hk hr, hf'⟩
    | labelExit hx hf' =>
      rw [caught_nil] at hx
      exact ⟨_, _, .iteExit hvs he hx, hf'⟩
  | br hn hu => exact ⟨_, _, .br hn, hu.fin hs⟩
  | brIf hv hn hu => exact ⟨_, _, .brIfTaken hv hn, hu.fin hs⟩
  | brTable hn hu => exact ⟨_, _, .brTable hn, hu.fin hs⟩
  | ret hn hu => exact ⟨_, _, .ret hn, hu.fin hs⟩
  | endLabel hk =>
    obtain ⟨n, o, he, hf⟩ := hs
    exact ⟨_, _, .nil, .labelLand rfl hk he hf⟩
  | endLoop hk =>
    obtain ⟨n, o, he, hf⟩ := hs
    exact ⟨_, _, .nil, .loopLand .done rfl hk he hf⟩
  | endCall hk =>
    obtain ⟨n, o, he, hf⟩ := hs
    exact ⟨_, _, .nil, .callLand rfl hk he hf⟩
  | done =>
    cases hs
    exact ⟨_, _, .nil, .returned⟩
  | call hf hargs =>
    obtain ⟨n, o, he, hfin⟩ := hs
    cases hfin with
    | callLand hl hk hr hf' =>
      exact ⟨_, _, .call hf hargs he hl (hk _ (List.mem_singleton.2 rfl)) hr, hf'⟩
    | callThrown hth hf' => exact ⟨_, _, .callExn hf hargs he hth, hf'⟩
  | callIndirect htbl hf hps hrs hbd hargs =>
    obtain ⟨n, o, he, hfin⟩ := hs
    cases hfin with
    | callLand hl hk hr hf' =>
      exact ⟨_, _, .callIndirect htbl hf hps hrs hbd hargs he hl
        (hk _ (List.mem_singleton.2 rfl)) hr, hf'⟩
    | callThrown hth hf' => exact ⟨_, _, .callIndirectExn htbl hf hps hrs hbd hargs he hth, hf'⟩
  | callRef href hf hps hrs hbd hargs =>
    obtain ⟨n, o, he, hfin⟩ := hs
    cases hfin with
    | callLand hl hk hr hf' =>
      exact ⟨_, _, .callRef href hf hps hrs hbd hargs he hl
        (hk _ (List.mem_singleton.2 rfl)) hr, hf'⟩
    | callThrown hth hf' => exact ⟨_, _, .callRefExn href hf hps hrs hbd hargs he hth, hf'⟩
  | retCall hf hargs hb =>
    obtain ⟨n, o, he, hfin⟩ := hs
    cases hfin with
    | callLand hl hk hr hf' =>
      exact ⟨_, _, .retCall hf hargs he hl (hk _ (List.mem_cons_self ..)),
        boundary_ret hb (fun c hc => hk c (List.mem_cons_of_mem _ hc)) hr hf'⟩
    | callThrown hth hf' =>
      exact ⟨_, _, .retCallExn hf hargs he hth, boundary_thrown hb hf'⟩
  | retCallIndirect htbl hf hps hrs hbd hargs hb =>
    obtain ⟨n, o, he, hfin⟩ := hs
    cases hfin with
    | callLand hl hk hr hf' =>
      exact ⟨_, _, .retCallIndirect htbl hf hps hrs hbd hargs he hl (hk _ (List.mem_cons_self ..)),
        boundary_ret hb (fun c hc => hk c (List.mem_cons_of_mem _ hc)) hr hf'⟩
    | callThrown hth hf' =>
      exact ⟨_, _, .retCallIndirectExn htbl hf hps hrs hbd hargs he hth, boundary_thrown hb hf'⟩
  | throw hr => exact ⟨_, _, .throw, hr.fin hs⟩
  | throwRef he hr => exact ⟨_, _, .throwRef he, hr.fin hs⟩

theorem Runs.sem {F : List Func} {c : Config} {e : Ended} (h : Runs F c e) : Sem F c e := by
  induction h with
  | stop hs => exact hs.sem rfl
  | go hs _ ih => exact hs.sem ih

/--
Refinement: a run of the machine from the call of a function to its end is a derivation of the
big-step semantics with the same end. No typing is assumed. The converse is not claimed and
not needed: the theorem below is about the runs the machine has.
-/
theorem refinement {F : List Func} {f : Func} {a : List Nat} {s : State} {e : Ended}
    (h : Runs F (Config.entry f a s) e) : Invoke F f a s e := by
  obtain ⟨n, o, he, hf⟩ := h.sem
  cases hf with
  | callLand hl hk hr hf' =>
    cases hr with
    | nil =>
      cases hf' with
      | returned =>
        have hinv := Invoke.returned he hl (hk _ (List.mem_singleton.2 rfl))
        simpa using hinv
  | callThrown hth hf' =>
    cases hf' with
    | threw => exact .threw he hth

/--
Noninterference of the machine. Take a well-typed module in which the preserved globals are
public, one of its functions, and two runs of the machine that call it from low-equivalent
states on arguments that agree where its parameters are public. If both runs end, both return
or both end by the same exception with the same values; the results of two returns agree
where the function's result type is public; and the two final states are low-equivalent.
-/
theorem machine_noninterference {C : Ctx} {F : List Func} (hF : WellTyped C F)
    (hpub : ∀ i, C.preserved i → C.globals i = Lab.L) {i : Nat} {f : Func} (hf : F[i]? = some f)
    {a0 a1 : List Nat} {s0 s1 : State} {e0 e1 : Ended}
    (ha : StkRel f.ty.params a0 a1) (hs : LowEq C s0 s1)
    (h0 : Runs F (Config.entry f a0 s0) e0) (h1 : Runs F (Config.entry f a1 s1) e1) :
    (∃ r0 t0 r1 t1, e0 = .returned r0 t0 ∧ e1 = .returned r1 t1 ∧
      StkRel f.ty.results r0 r1 ∧ LowEq C t0 t1) ∨
    (∃ tag w t0 t1, e0 = .threw tag w t0 ∧ e1 = .threw tag w t1 ∧ LowEq C t0 t1) :=
  noninterference hF hpub hf ha hs (refinement h0) (refinement h1)

end WasmIfc
