/-
Noninterference for the lift-free rules (`ni`), and its statement for a function body (`tini`).

Two runs of a typed sequence from inputs that agree where public end in outcomes related by
`OutRel`: either they end the same way, with results that agree where public, or they have
taken different paths under a secret pc and at least one of them is on its way out of a block.
In the second case nothing is said of their stacks. None is needed: the run that stays behind
runs on under a secret pc (`confine`), and where the two meet again, at the end of a block
that one left by a branch, the block's result type is all secret.

The preserved globals are apart from the other public variables. The two runs agree on them
where the pc is public (`PresOr`). Under a secret pc each run may write them, and where the pc
drops again, at the end of a block, a loop, a conditional or a call, the construct has compared
them with their values at its start, where the runs agreed (`pres_after`, `pres_after_call`).
-/
import WasmIfc.Confinement

namespace WasmIfc

variable {F : List Func}

theorem Lab.le_H (a : Lab) : Lab.le a Lab.H := fun _ => rfl

theorem Lab.eq_H_of_ne_L {a : Lab} (h : a ≠ Lab.L) : a = Lab.H := by
  cases a <;> simp_all

/-- Two conditions that agree if their level is public: they agree, or the level is secret. -/
theorem cond_cases {l : Lab} {c0 c1 : Nat} (hc : l = Lab.L → c0 = c1) : c0 = c1 ∨ l = Lab.H := by
  cases l with
  | L => exact .inl (hc rfl)
  | H => exact .inr rfl

/-- The target a table selects is one the rule covers. -/
theorem table_target_info {Ls : List STy} {ts : List Nat} {d k n c : Nat} {rs : STy}
    (hall : ∀ t, t ∈ d :: ts → Ls[t]? = some rs ∧ t ≤ k)
    (hn : (Ls.map List.length)[tableTarget ts d c]? = some n) :
    Ls[tableTarget ts d c]? = some rs ∧ tableTarget ts d c ≤ k ∧ n = rs.length := by
  obtain ⟨h1, h2⟩ := hall _ (tableTarget_mem ts d c)
  exact ⟨h1, h2, arity_eq h1 hn⟩

theorem Info.hiUpTo_zero {Ls : List STy} {P : Pcs} {st : STy} {o : Out} (h : Info Ls P st o)
    (hbr : o.isBr) : HiUpTo 0 P := by
  cases o with
  | normal σ s => exact False.elim hbr
  | br i w s =>
    obtain ⟨_, _, _, _, h4⟩ := h
    exact h4.mono (Nat.zero_le _)
  | exn t w s => exact False.elim hbr

theorem OutRel.mono {C : Ctx} {Ls : List STy} {P P' : Pcs} {st : STy} {o0 o1 : Out}
    (hf : SFlows P P') (h : OutRel C Ls P st o0 o1) : OutRel C Ls P' st o0 o1 :=
  h.elim (fun h => .inl (h.mono hf)) (fun h => .inr ⟨h.1.mono hf, h.2⟩)

/-! ### Preserved globals where the pc stack changes -/

/-- Into a block, whose own pc is at least the pc in force. -/
theorem PresOr.enter {C : Ctx} {pc q : Lab} {Pr : Pcs} {s t : State} (hq : Lab.le pc q)
    (h : PresOr C 0 (pc :: Pr) s t) : PresOr C 0 (q :: pc :: Pr) s t := by
  rcases h with h | h
  · exact .inl h
  · have hpc := h.head
    subst hpc
    have hqH := hq rfl
    subst hqH
    exact .inr (hiUpTo_zero_cons _)

/-- Into a callee, whose bound is at least the caller's pc. -/
theorem PresOr.call {C : Ctx} {f : Func} {pc b : Lab} {Pr : Pcs} {s0 s1 : State}
    {a0 a1 : List Nat} (hb : Lab.le pc b) (h : PresOr C 0 (pc :: Pr) s0 s1) :
    PresOr (C.enter f) 0 [b] { s0 with loc := frame a0 } { s1 with loc := frame a1 } := by
  rcases h with h | h
  · exact .inl (fun i hi => h i hi)
  · have hpc := h.head
    subst hpc
    have hbH := hb rfl
    subst hbH
    exact .inr (hiUpTo_zero_cons _)

theorem Restores.mono {C : Ctx} {p q : Lab} {after : Pcs} {keep : List Nat} (hpq : Lab.le p q)
    (h : Restores C q after keep) : Restores C p after keep :=
  h.imp (fun h r hr => Lab.le_trans hpq (h r hr)) id

/-! ### After the body of a block or of a conditional -/

/--
How the outcomes of two runs of a block's body relate: as `OutRel` says, or apart with a result
type that is all secret (the two arms of a conditional on a secret).
-/
def BodyRel (C : Ctx) (Ls : List STy) (rs : STy) (P : Pcs) (ob0 ob1 : Out) : Prop :=
  Sync C (rs :: Ls) P rs ob0 ob1 ∨
    (Loose C (rs :: Ls) P rs ob0 ob1 ∧ HiUpTo 0 P ∧ (AllGe Lab.H rs ∨ ob0.isBr ∨ ob1.isBr))

theorem OutRel.toBody {C : Ctx} {Ls : List STy} {rs : STy} {P : Pcs} {ob0 ob1 : Out}
    (h : OutRel C (rs :: Ls) P rs ob0 ob1) : BodyRel C Ls rs P ob0 ob1 :=
  h.elim .inl (fun h => .inr ⟨h.1, h.2.elim h.1.2.1.hiUpTo_zero h.1.2.2.hiUpTo_zero, .inr h.2⟩)

theorem allH_of_lands {Ls : List STy} {rs : STy} {P : Pcs} {ob : Out} {x : List Nat × State}
    (h : Info (rs :: Ls) P rs ob) (hbr : ob.isBr) (hl : ob.lands = some x) : AllGe Lab.H rs := by
  cases ob with
  | normal σ s => exact False.elim hbr
  | br i w s =>
    cases i with
    | zero =>
      obtain ⟨rs', h1, h2, _, _⟩ := h
      simp at h1
      subst h1
      exact h2
    | succ i => simp [Out.lands] at hl
  | exn t w s => exact False.elim hbr

/-- Both runs go on after the block: their stacks agree where public. -/
theorem join_land_land {C : Ctx} {Ls : List STy} {rs st : STy} {p : Lab} {P1 : Pcs}
    {keep : List Nat} {ob0 ob1 : Out} {σ0 σ1 b0 b1 : List Nat} {e0 e1 t0 t1 : State}
    (h : BodyRel C Ls rs (p :: P1) ob0 ob1) (hl0 : ob0.lands = some (σ0, t0))
    (hl1 : ob1.lands = some (σ1, t1)) (hb : StkRel st b0 b1)
    (hres : Restores C p P1 keep) (hentry : PresOr C 0 P1 e0 e1)
    (hk0 : Kept keep e0 t0) (hk1 : Kept keep e1 t1) :
    StkRel (rs ++ st) (σ0 ++ b0) (σ1 ++ b1) ∧ StRel C t0 t1 ∧ PresOr C 0 P1 t0 t1 := by
  rcases h with hs | ⟨⟨hst, hi0, hi1⟩, hP, hx⟩
  · cases hs with
    | normal hσ hss hpp =>
      simp [Out.lands] at hl0 hl1
      obtain ⟨rfl, rfl⟩ := hl0
      obtain ⟨rfl, rfl⟩ := hl1
      exact ⟨hσ.append hb, hss, pres_after hres hentry hk0 hk1 hpp⟩
    | @br i rs' w0 w1 u0 u1 hLs hσ hss hpp =>
      cases i with
      | zero =>
        simp [Out.lands] at hl0 hl1
        obtain ⟨rfl, rfl⟩ := hl0
        obtain ⟨rfl, rfl⟩ := hl1
        simp at hLs
        subst hLs
        exact ⟨hσ.append hb, hss, pres_after hres hentry hk0 hk1 hpp⟩
      | succ i => simp [Out.lands] at hl0
    | exn _ _ _ _ => simp [Out.lands] at hl0
  · obtain ⟨hlen0, hst0⟩ := lands_info hi0 hl0
    obtain ⟨hlen1, hst1⟩ := lands_info hi1 hl1
    have hall : AllGe Lab.H rs := by
      rcases hx with h | h | h
      · exact h
      · exact allH_of_lands hi0 h hl0
      · exact allH_of_lands hi1 h hl1
    subst hst0 hst1
    exact ⟨(StkRel.of_allH hall hlen0 hlen1).append hb, hst,
      pres_after hres hentry hk0 hk1 (.inr hP)⟩

/-- Both runs branch past the block. -/
theorem join_exit_exit {C : Ctx} {Ls : List STy} {rs : STy} {p : Lab} {P1 : Pcs}
    {ob0 ob1 o0 o1 : Out} (h : BodyRel C Ls rs (p :: P1) ob0 ob1)
    (hx0 : ob0.exits = some o0) (hx1 : ob1.exits = some o1) (st : STy) :
    OutRel C Ls P1 st o0 o1 := by
  rcases h with hs | ⟨⟨hst, hi0, hi1⟩, _, _⟩
  · cases hs with
    | normal _ _ _ => simp [Out.exits] at hx0
    | @br i rs' w0 w1 u0 u1 hLs hσ hss hpp =>
      cases i with
      | zero => simp [Out.exits] at hx0
      | succ i =>
        simp [Out.exits] at hx0 hx1
        subst hx0 hx1
        exact .inl (.br (by simpa using hLs) hσ hss (hpp.imp id HiUpTo.tail))
    | exn h0 h1 h2 h3 =>
      simp [Out.exits] at hx0 hx1
      subst hx0 hx1
      exact .inl (.exn h0 h1 h2 h3)
  · obtain ⟨hs0, hb0, hinfo0⟩ := exits_info hi0 hx0
    obtain ⟨hs1, _, hinfo1⟩ := exits_info hi1 hx1
    refine .inr ⟨⟨?_, hinfo0 st, hinfo1 st⟩, .inl hb0⟩
    rw [hs0, hs1]
    exact hst

/-- The first run goes on after the block and the second branches past it. -/
theorem join_land_exit {C : Ctx} {Ls : List STy} {rs : STy} {p : Lab} {P1 : Pcs}
    {ob0 ob1 o1 : Out} {σ0 : List Nat} {t0 : State} (h : BodyRel C Ls rs (p :: P1) ob0 ob1)
    (hl0 : ob0.lands = some (σ0, t0)) (hx1 : ob1.exits = some o1) :
    σ0.length = rs.length ∧ StRel C t0 o1.state ∧ o1.isBr ∧ ∀ st, Info Ls P1 st o1 := by
  rcases h with hs | ⟨⟨hst, hi0, hi1⟩, _, _⟩
  · cases hs with
    | normal _ _ _ => simp [Out.exits] at hx1
    | @br i rs' w0 w1 u0 u1 hLs hσ hss hpp =>
      cases i with
      | zero => simp [Out.exits] at hx1
      | succ i => simp [Out.lands] at hl0
    | exn _ _ _ _ => simp [Out.lands] at hl0
  · obtain ⟨hlen0, hst0⟩ := lands_info hi0 hl0
    obtain ⟨hs1, hb1, hinfo1⟩ := exits_info hi1 hx1
    refine ⟨hlen0, ?_, hb1, hinfo1⟩
    rw [← hst0, hs1]
    exact hst

/-- The first run branches past the block and the second goes on after it. -/
theorem join_exit_land {C : Ctx} {Ls : List STy} {rs : STy} {p : Lab} {P1 : Pcs}
    {ob0 ob1 o0 : Out} {σ1 : List Nat} {t1 : State} (h : BodyRel C Ls rs (p :: P1) ob0 ob1)
    (hx0 : ob0.exits = some o0) (hl1 : ob1.lands = some (σ1, t1)) :
    σ1.length = rs.length ∧ StRel C o0.state t1 ∧ o0.isBr ∧ ∀ st, Info Ls P1 st o0 := by
  rcases h with hs | ⟨⟨hst, hi0, hi1⟩, _, _⟩
  · cases hs with
    | normal _ _ _ => simp [Out.exits] at hx0
    | @br i rs' w0 w1 u0 u1 hLs hσ hss hpp =>
      cases i with
      | zero => simp [Out.exits] at hx0
      | succ i => simp [Out.lands] at hl1
    | exn _ _ _ _ => simp [Out.lands] at hl1
  · obtain ⟨hlen1, hst1⟩ := lands_info hi1 hl1
    obtain ⟨hs0, hb0, hinfo0⟩ := exits_info hi0 hx0
    refine ⟨hlen1, ?_, hb0, hinfo0⟩
    rw [← hst1, hs0]
    exact hst

/--
What a block does after its body: the rest of the sequence, if the globals it names hold what
they held in the state `e` at its start, or a branch further out.
-/
inductive Cont (F : List Func) (ls : List Nat) (keep : List Nat) (e : State) (rest : List Instr)
    (base : List Nat) (ob : Out) (n : Nat) (o : Out) : Prop where
  | land {m : Nat} {σ1 : List Nat} {s1 : State} :
      ob.lands = some (σ1, s1) → Kept keep e s1 → m < n → Eval F m ls rest (σ1 ++ base) s1 o →
      Cont F ls keep e rest base ob n o
  | exit : ob.exits = some o → Cont F ls keep e rest base ob n o

theorem block_inv {n : Nat} {ls keep : List Nat} {ps rs : STy} {body rest : List Instr}
    {σ : List Nat} {s : State} {o : Out} (h : Eval F n ls (.block keep ps rs body :: rest) σ s o) :
    ∃ vs base n1 ob, σ = vs ++ base ∧ vs.length = ps.length ∧ n1 < n ∧
      Eval F n1 (rs.length :: ls) body vs s ob ∧ Cont F ls keep s rest base ob n o := by
  cases h with
  | blockCont hvs hb hl hk hr =>
    exact ⟨_, _, _, _, rfl, hvs, by omega, hb, .land hl hk (by omega) hr⟩
  | blockExit hvs hb hx => exact ⟨_, _, _, _, rfl, hvs, by omega, hb, .exit hx⟩

/-- A loop is a block around the iterations of its body. -/
theorem loop_inv {n : Nat} {ls keep : List Nat} {ps rs : STy} {body rest : List Instr}
    {σ : List Nat} {s : State} {o : Out} (h : Eval F n ls (.loop keep ps rs body :: rest) σ s o) :
    ∃ vs base n1 ob, σ = vs ++ base ∧ vs.length = ps.length ∧ n1 < n ∧
      Eval F n1 (rs.length :: ls) [.iter ps rs body] vs s ob ∧ Cont F ls keep s rest base ob n o := by
  cases h with
  | loopCont hvs hb hl hk hr =>
    exact ⟨_, _, _, _, rfl, hvs, by omega, hb, .land hl hk (by omega) hr⟩
  | loopExit hvs hb hx => exact ⟨_, _, _, _, rfl, hvs, by omega, hb, .exit hx⟩

theorem ite_inv {n : Nat} {ls keep : List Nat} {ps rs : STy} {thn els rest : List Instr}
    {σ : List Nat} {s : State} {o : Out} (h : Eval F n ls (.ite keep ps rs thn els :: rest) σ s o) :
    ∃ c vs base n1 ob, σ = c :: (vs ++ base) ∧ vs.length = ps.length ∧ n1 < n ∧
      Eval F n1 (rs.length :: ls) (if c = 0 then els else thn) vs s ob ∧
      Cont F ls keep s rest base ob n o := by
  cases h with
  | iteCont hvs hb hl hk hr =>
    exact ⟨_, _, _, _, _, rfl, hvs, by omega, hb, .land hl hk (by omega) hr⟩
  | iteExit hvs hb hx => exact ⟨_, _, _, _, _, rfl, hvs, by omega, hb, .exit hx⟩

/-- A `try_table` is a block whose body's outcome is first looked up in its clauses. -/
theorem try_inv {n : Nat} {ls keep : List Nat} {ps rs : STy} {cs : List (Option Nat × Nat)}
    {body rest : List Instr} {σ : List Nat} {s : State} {o : Out}
    (h : Eval F n ls (.tryTable keep ps rs cs body :: rest) σ s o) :
    ∃ vs base n1 ob, σ = vs ++ base ∧ vs.length = ps.length ∧ n1 < n ∧
      Eval F n1 (rs.length :: ls) body vs s ob ∧ Cont F ls keep s rest base (ob.caught cs) n o := by
  cases h with
  | tryCont hvs hb hl hk hr =>
    exact ⟨_, _, _, _, rfl, hvs, by omega, hb, .land hl hk (by omega) hr⟩
  | tryExit hvs hb hx => exact ⟨_, _, _, _, rfl, hvs, by omega, hb, .exit hx⟩

/-- The label of the clause that catches an exception takes what the branch to it carries. -/
theorem catches_ok {C : Ctx} {Ls : List STy} : ∀ {cs : List (Option Nat × Nat)} {t k j : Nat}
    {carry : Bool} {w : List Nat}, (∀ c, c ∈ cs → ClauseOk C Ls c) →
    catches cs t = some (j, carry) → C.tags[t]? = some k → w.length = k →
    ∃ target, Ls[j]? = some target ∧ (if carry then w else []).length = target.length
  | [], _, _, _, _, _, _, h, _, _ => by simp [catches] at h
  | (some t', j') :: cs, t, k, j, carry, w, hcl, h, htag, hlen => by
      by_cases ht : t' = t
      · simp [catches, ht] at h
        obtain ⟨rfl, rfl⟩ := h
        subst ht
        have hc : ClauseOk C Ls (some t', j') := hcl _ List.mem_cons_self
        obtain ⟨k', target, h1, h2, h3⟩ := hc
        rw [htag] at h1
        cases h1
        exact ⟨target, h2, by simp [hlen, h3]⟩
      · simp [catches, ht] at h
        exact catches_ok (fun c hc => hcl c (List.mem_cons_of_mem _ hc)) h htag hlen
  | (none, j') :: cs, t, k, j, carry, w, hcl, h, _, _ => by
      simp [catches] at h
      obtain ⟨rfl, rfl⟩ := h
      have hc : ClauseOk C Ls (none, j') := hcl _ List.mem_cons_self
      exact ⟨[], hc, by simp⟩

/--
The outcomes of two runs of a `try_table`'s body, after its clauses. The two runs throw the
same exception or none, since one is thrown only under a public pc, so the same clause catches
it in both, with the same values.
-/
theorem caught_rel {C : Ctx} {Ls : List STy} {rs : STy} {P : Pcs} {cs : List (Option Nat × Nat)}
    {ob0 ob1 : Out} (hcl : ∀ c, c ∈ cs → ClauseOk C Ls c)
    (h : OutRel C (rs :: Ls) P rs ob0 ob1) : BodyRel C Ls rs P (ob0.caught cs) (ob1.caught cs) := by
  rcases h with hs | ⟨hl, hbr⟩
  · cases hs with
    | normal h1 h2 h3 => exact .inl (.normal h1 h2 h3)
    | br h0 h1 h2 h3 => exact .inl (.br h0 h1 h2 h3)
    | @exn t k w s0 s1 htag hlen hst hpe =>
      simp only [Out.caught]
      cases hcat : catches cs t with
      | none => exact .inl (.exn htag hlen hst hpe)
      | some jc =>
        obtain ⟨j, carry⟩ := jc
        obtain ⟨target, hj, hpay⟩ := catches_ok hcl hcat htag hlen
        exact .inl (.br (by simpa using hj) (StkRel.same hpay) hst (.inl hpe))
  · have e0 : ob0.caught cs = ob0 := by
      cases ob0 <;> first | rfl | exact False.elim hl.2.1
    have e1 : ob1.caught cs = ob1 := by
      cases ob1 <;> first | rfl | exact False.elim hl.2.2
    rw [e0, e1]
    exact OutRel.toBody (.inr ⟨hl, hbr⟩)

/--
The two runs after the body of a block, of a conditional or of a loop (whose body is its
iterations), given noninterference for the rest of the sequence on smaller derivations of the
first run. `e0` and `e1` are the states at the construct's start.
-/
theorem after_body {C : Ctx} {Ls : List STy} {rs st st' : STy} {p : Lab} {P1 P' : Pcs}
    {keep : List Nat} {rest : List Instr} {ob0 ob1 o0 o1 : Out} {base0 base1 : List Nat}
    {e0 e1 : State} {n0 n1 : Nat}
    (hF : WellTyped C F)
    (hIH : ∀ m, m < n0 → ∀ (σ0 : List Nat) (s0 : State) (o0 : Out) (m1 : Nat) (σ1 : List Nat)
      (s1 : State) (o1 : Out), Eval F m (Ls.map List.length) rest σ0 s0 o0 →
      Eval F m1 (Ls.map List.length) rest σ1 s1 o1 → StkRel (rs ++ st) σ0 σ1 → StRel C s0 s1 →
      PresOr C 0 P1 s0 s1 → OutRel C Ls P' st' o0 o1)
    (hrest : Typed C Ls rest P1 (rs ++ st) P' st')
    (hrel : BodyRel C Ls rs (p :: P1) ob0 ob1)
    (hbase : StkRel st base0 base1)
    (hres : Restores C p P1 keep) (hentry : PresOr C 0 P1 e0 e1)
    (hc0 : Cont F (Ls.map List.length) keep e0 rest base0 ob0 n0 o0)
    (hc1 : Cont F (Ls.map List.length) keep e1 rest base1 ob1 n1 o1) : OutRel C Ls P' st' o0 o1 := by
  cases hc0 with
  | land hl0 hk0 hm0 he0 =>
    cases hc1 with
    | land hl1 hk1 hm1 he1 =>
      obtain ⟨hσ, hs, hp⟩ := join_land_land hrel hl0 hl1 hbase hres hentry hk0 hk1
      exact hIH _ hm0 _ _ _ _ _ _ _ he0 he1 hσ hs hp
    | exit hx1 =>
      obtain ⟨hlen0, hs, hbr1, hinfo1⟩ := join_land_exit hrel hl0 hx1
      have hP1 : HiUpTo 0 P1 := (hinfo1 st').hiUpTo_zero hbr1
      obtain ⟨hs0, hi0⟩ := confine _ hF hrest hP1
        (by simp only [List.length_append, hlen0, hbase.length_left]) he0
      exact .inr ⟨⟨hs.conf_left hs0, hi0, (hinfo1 st').mono (rise hrest)⟩, .inr hbr1⟩
  | exit hx0 =>
    cases hc1 with
    | land hl1 hk1 hm1 he1 =>
      obtain ⟨hlen1, hs, hbr0, hinfo0⟩ := join_exit_land hrel hx0 hl1
      have hP1 : HiUpTo 0 P1 := (hinfo0 st').hiUpTo_zero hbr0
      obtain ⟨hs1, hi1⟩ := confine _ hF hrest hP1
        (by simp only [List.length_append, hlen1, hbase.length_right]) he1
      exact .inr ⟨⟨hs.conf_right hs1, (hinfo0 st').mono (rise hrest), hi1⟩, .inl hbr0⟩
    | exit hx1 => exact (join_exit_exit hrel hx0 hx1 st').mono (rise hrest)

/-! ### The iterations of a loop's body -/

/-- What the iterations do after one run of the body: end, go round again, or branch past the loop. -/
inductive IterCont (F : List Func) (ls : List Nat) (ps rs : STy) (body rest : List Instr) (ob : Out)
    (n : Nat) (o : Out) : Prop where
  | done {σ1 : List Nat} {s1 : State} :
      ob = .normal σ1 s1 → o = .normal σ1 s1 → IterCont F ls ps rs body rest ob n o
  | again {m : Nat} {w : List Nat} {s1 : State} :
      ob = .br 0 w s1 → m < n → Eval F m ls (.iter ps rs body :: rest) w s1 o →
      IterCont F ls ps rs body rest ob n o
  | exit {i : Nat} {w : List Nat} {s1 : State} :
      ob = .br (i + 1) w s1 → o = .br (i + 1) w s1 → IterCont F ls ps rs body rest ob n o
  | exn {t : Nat} {w : List Nat} {s1 : State} :
      ob = .exn t w s1 → o = .exn t w s1 → IterCont F ls ps rs body rest ob n o

theorem iter_inv {n k : Nat} {ls : List Nat} {ps rs : STy} {body rest : List Instr}
    {σ : List Nat} {s : State} {o : Out} (h : Eval F n (k :: ls) (.iter ps rs body :: rest) σ s o) :
    ∃ n1 ob, n1 < n ∧ Eval F n1 (ps.length :: ls) body σ s ob ∧
      IterCont F (k :: ls) ps rs body rest ob n o := by
  cases h with
  | iterDone hb => exact ⟨_, _, by omega, hb, .done rfl rfl⟩
  | iterAgain hb hr => exact ⟨_, _, by omega, hb, .again rfl (by omega) hr⟩
  | iterExit hb => exact ⟨_, _, by omega, hb, .exit rfl rfl⟩
  | iterExn hb => exact ⟨_, _, by omega, hb, .exn rfl rfl⟩

/--
A run that is on its own after one run of a loop's body under a secret pc: whatever the
iterations then do, the public variables stay as they were and the outcome is as `Info` says.
-/
theorem iter_alone {C : Ctx} {Ls : List STy} {l0 ps rs : STy} {body rest : List Instr}
    {Pb P1 : Pcs} {p : Lab} {ob o : Out} {n : Nat} (hF : WellTyped C F) (hge : AllGe Lab.H rs)
    (hbody : Typed C (ps :: Ls) body (Lab.H :: Pb) ps (p :: P1) rs)
    (hi : Info (ps :: Ls) (p :: P1) rs ob)
    (hc : IterCont F ((l0 :: Ls).map List.length) ps rs body rest ob n o) :
    Conf C ob.state o.state ∧ Info (l0 :: Ls) (Lab.H :: P1) rs o := by
  cases hc with
  | done hob ho =>
    subst hob ho
    exact ⟨Conf.refl _ _, hi⟩
  | again hob hm he =>
    subst hob
    obtain ⟨rs', h1, _, h3, _⟩ := hi
    simp at h1
    subst h1
    exact confine _ hF (Typed.iter (Lab.le_H p) hge hbody) (hiUpTo_zero_cons _) h3 he
  | exit hob ho =>
    subst hob ho
    obtain ⟨rs', h1, h2, h3, h4⟩ := hi
    exact ⟨Conf.refl _ _, rs', by simpa using h1, h2, h3,
      HiUpTo.sflows (.cons (Lab.le_H p) (SFlows.refl _)) h4⟩
  | exn hob ho =>
    subst hob
    exact False.elim hi

/--
Two runs that went apart under a secret pc, where the type they end at is all secret: if both
reached the end, their results need not agree, so they ended the same way.
-/
theorem loose_to_out {C : Ctx} {Ls : List STy} {P : Pcs} {st : STy} {o0 o1 : Out}
    (hall : AllGe Lab.H st) (hP : HiUpTo 0 P) (h : Loose C Ls P st o0 o1) :
    OutRel C Ls P st o0 o1 := by
  obtain ⟨hst, hi0, hi1⟩ := h
  cases o0 with
  | br i w s => exact .inr ⟨⟨hst, hi0, hi1⟩, .inl trivial⟩
  | exn t w s => exact False.elim hi0
  | normal σ0 s0 =>
    cases o1 with
    | br i w s => exact .inr ⟨⟨hst, hi0, hi1⟩, .inr trivial⟩
    | exn t w s => exact False.elim hi1
    | normal σ1 s1 => exact .inl (.normal (StkRel.of_allH hall hi0 hi1) hst (.inr hP))

/-- The values a branch carries agree where the label's type is public. -/
theorem carried_rel {carried rs st : STy} {σ0 σ1 : List Nat} (hfl : SFlows carried rs)
    (hσ : StkRel (carried ++ st) σ0 σ1) :
    StkRel rs (σ0.take rs.length) (σ1.take rs.length) := by
  have h := StkRel.take hσ
  rw [hfl.length_eq] at h
  exact h.mono hfl

/-! ### Noninterference -/

/--
What a call does after the callee's body: the rest of the caller's sequence, if the globals the
callee names hold what they held at the call, or the exception that left the callee.
-/
inductive CallCont (F : List Func) (ls : List Nat) (keep : List Nat) (s : State) (rest : List Instr)
    (base : List Nat) (ob : Out) (n : Nat) (o : Out) : Prop where
  | land {m : Nat} {r : List Nat} {t : State} :
      ob.lands = some (r, t) → Kept keep s t → m < n →
      Eval F m ls rest (r ++ base) { t with loc := s.loc } o → CallCont F ls keep s rest base ob n o
  | exn {t : Nat} {w : List Nat} {u : State} :
      ob = .exn t w u → o = .exn t w { u with loc := s.loc } → CallCont F ls keep s rest base ob n o

theorem call_inv {n i : Nat} {ls : List Nat} {rest : List Instr} {σ : List Nat} {s : State}
    {o : Out} (h : Eval F n ls (.call i :: rest) σ s o) :
    ∃ f args base n1 ob, F[i]? = some f ∧ σ = args ++ base ∧ args.length = f.ty.params.length ∧
      n1 < n ∧ Eval F n1 [f.ty.results.length] f.body [] { s with loc := frame args } ob ∧
      CallCont F ls f.keep s rest base ob n o := by
  cases h with
  | call hf hargs hb hl hk hr =>
    exact ⟨_, _, _, _, _, hf, rfl, hargs, by omega, hb, .land hl hk (by omega) hr⟩
  | callExn hf hargs hb => exact ⟨_, _, _, _, _, hf, rfl, hargs, by omega, hb, .exn rfl rfl⟩

theorem callIndirect_inv {n : Nat} {ls : List Nat} {ps rs : STy} {b : Lab} {rest : List Instr}
    {σ : List Nat} {s : State} {o : Out} (h : Eval F n ls (.callIndirect ps b rs :: rest) σ s o) :
    ∃ c i f args base n1 ob, s.tbl c = some i ∧ F[i]? = some f ∧ f.ty = ⟨ps, b, rs⟩ ∧
      σ = c :: (args ++ base) ∧ args.length = ps.length ∧ n1 < n ∧
      Eval F n1 [rs.length] f.body [] { s with loc := frame args } ob ∧
      CallCont F ls f.keep s rest base ob n o := by
  cases h with
  | callIndirect htbl hf hty hargs hb hl hk hr =>
    exact ⟨_, _, _, _, _, _, _, htbl, hf, hty, rfl, hargs, by omega, hb, .land hl hk (by omega) hr⟩
  | callIndirectExn htbl hf hty hargs hb =>
    exact ⟨_, _, _, _, _, _, _, htbl, hf, hty, rfl, hargs, by omega, hb, .exn rfl rfl⟩

/--
Two related outcomes of a function body. Either both leave it, with results and states that
agree where public, and with the preserved globals equal unless the pc they end under is
secret; or both end by the same exception with the same values.
-/
theorem fun_result {C : Ctx} {rs : STy} {P : Pcs} {o0 o1 : Out} (h : OutRel C [rs] P rs o0 o1) :
    (∃ r0 t0 r1 t1, o0.lands = some (r0, t0) ∧ o1.lands = some (r1, t1) ∧
      StkRel rs r0 r1 ∧ StRel C t0 t1 ∧ PresOr C 0 P t0 t1) ∨
    (∃ t k w u0 u1, o0 = .exn t w u0 ∧ o1 = .exn t w u1 ∧ C.tags[t]? = some k ∧ w.length = k ∧
      StRel C u0 u1 ∧ PresEq C u0 u1) := by
  rcases h with hsync | ⟨⟨hst, hi0, hi1⟩, hbr⟩
  · cases hsync with
    | normal hσ hss hpp => exact .inl ⟨_, _, _, _, rfl, rfl, hσ, hss, hpp⟩
    | @br i rs' w0 w1 u0 u1 hLs hσ hss hpp =>
      cases i with
      | zero =>
        simp at hLs
        subst hLs
        exact .inl ⟨_, _, _, _, rfl, rfl, hσ, hss, hpp⟩
      | succ i => simp at hLs
    | exn h0 h1 h2 h3 => exact .inr ⟨_, _, _, _, _, rfl, rfl, h0, h1, h2, h3⟩
  · obtain ⟨r0, t0, hl0, hlen0, hst0, hall0⟩ := top_lands hi0
    obtain ⟨r1, t1, hl1, hlen1, hst1, hall1⟩ := top_lands hi1
    refine .inl ⟨r0, t0, r1, t1, hl0, hl1, StkRel.of_allH (hbr.elim hall0 hall1) hlen0 hlen1, ?_,
      .inr (hbr.elim hi0.hiUpTo_zero hi1.hiUpTo_zero)⟩
    rw [← hst0, ← hst1]
    exact hst

theorem ni : ∀ (n0 : Nat) {C : Ctx} {Ls : List STy} {e : List Instr} {P P' : Pcs}
    {st st' : STy} {σ0 : List Nat} {s0 : State} {o0 : Out} {n1 : Nat} {σ1 : List Nat}
    {s1 : State} {o1 : Out}, WellTyped C F →
    Typed C Ls e P st P' st' →
    Eval F n0 (Ls.map List.length) e σ0 s0 o0 → Eval F n1 (Ls.map List.length) e σ1 s1 o1 →
    StkRel st σ0 σ1 → StRel C s0 s1 → PresOr C 0 P s0 s1 → OutRel C Ls P' st' o0 o1 := by
  intro n0
  induction n0 using Nat.strongRecOn with
  | ind n0 ih =>
    intro C Ls e P P' st st' σ0 s0 o0 n1 σ1 s1 o1 hF ht he0 he1 hσ hs hp
    cases ht with
    | nil =>
      cases he0
      cases he1
      exact .inl (.normal hσ hs hp)
    | const v ht' =>
      cases he0 with
      | const _ he0' =>
        cases he1 with
        | const _ he1' => exact ih _ (by omega) hF ht' he0' he1' (.cons (fun _ => rfl) hσ) hs hp
    | binop f ht' =>
      cases he0 with
      | binop _ he0' =>
        cases he1 with
        | binop _ he1' =>
          cases hσ with
          | cons h0 hσa =>
            cases hσa with
            | cons h1 hσb =>
              refine ih _ (by omega) hF ht' he0' he1' (.cons (fun hl => ?_) hσb) hs hp
              obtain ⟨hl01, _⟩ := Lab.join_eq_L hl
              obtain ⟨hl0, hl1⟩ := Lab.join_eq_L hl01
              rw [h0 hl0, h1 hl1]
    | select ht' =>
      cases he0 with
      | select he0' =>
        cases he1 with
        | select he1' =>
          cases hσ with
          | cons hc hσa =>
            cases hσa with
            | cons h1 hσb =>
              cases hσb with
              | cons h2 hσc =>
                refine ih _ (by omega) hF ht' he0' he1' (.cons (fun hl => ?_) hσc) hs hp
                obtain ⟨_, hl'⟩ := Lab.join_eq_L hl
                obtain ⟨hlc, hl''⟩ := Lab.join_eq_L hl'
                obtain ⟨hl1, hl2⟩ := Lab.join_eq_L hl''
                rw [hc hlc, h1 hl1, h2 hl2]
    | drop ht' =>
      cases he0 with
      | drop he0' =>
        cases he1 with
        | drop he1' =>
          cases hσ with
          | cons _ hσ' => exact ih _ (by omega) hF ht' he0' he1' hσ' hs hp
    | nop ht' =>
      cases he0 with
      | nop he0' =>
        cases he1 with
        | nop he1' => exact ih _ (by omega) hF ht' he0' he1' hσ hs hp
    | relabel hf ht' =>
      cases he0 with
      | relabel he0' =>
        cases he1 with
        | relabel he1' => exact ih _ (by omega) hF ht' he0' he1' (hσ.mono hf) hs hp
    | localGet i ht' =>
      cases he0 with
      | localGet _ he0' =>
        cases he1 with
        | localGet _ he1' =>
          exact ih _ (by omega) hF ht' he0' he1'
            (.cons (fun hl => hs.1 i (Lab.join_eq_L hl).1) hσ) hs hp
    | localSet i hpc hl ht' =>
      cases he0 with
      | localSet _ he0' =>
        cases he1 with
        | localSet _ he1' =>
          cases hσ with
          | cons hv hσ' =>
            exact ih _ (by omega) hF ht' he0' he1' hσ'
              (hs.setLoc (fun hi => hv (Lab.eq_L_of_le hl hi))) (hp.of_glob rfl rfl)
    | localTee i hpc hl ht' =>
      cases he0 with
      | localTee _ he0' =>
        cases he1 with
        | localTee _ he1' =>
          cases hσ with
          | cons hv hσ' =>
            exact ih _ (by omega) hF ht' he0' he1' (.cons hv hσ')
              (hs.setLoc (fun hi => hv (Lab.eq_L_of_le hl hi))) (hp.of_glob rfl rfl)
    | globalGet i ht' =>
      cases he0 with
      | globalGet _ he0' =>
        cases he1 with
        | globalGet _ he1' =>
          refine ih _ (by omega) hF ht' he0' he1' (.cons (fun hl => ?_) hσ) hs hp
          obtain ⟨hg, hpcL⟩ := Lab.join_eq_L hl
          -- A preserved global is read as a public value only under a public pc, where the runs agree on it.
          by_cases hpi : C.preserved i
          · rcases hp with he | hh
            · exact he i hpi
            · have hH := hh.head
              rw [hpcL] at hH
              cases hH
          · exact hs.2.1 i hg hpi
    | globalSet i hnp hpc hl ht' =>
      cases he0 with
      | globalSet _ he0' =>
        cases he1 with
        | globalSet _ he1' =>
          cases hσ with
          | cons hv hσ' =>
            exact ih _ (by omega) hF ht' he0' he1' hσ'
              (hs.setGlob (fun hi => hv (Lab.eq_L_of_le hl hi)))
              (hp.imp (PresEq.setGlob (fun hpi => absurd hpi hnp)) id)
    | globalSetPreserved i hpi hl ht' =>
      cases he0 with
      | globalSet _ he0' =>
        cases he1 with
        | globalSet _ he1' =>
          cases hσ with
          | cons hv hσ' =>
            refine ih _ (by omega) hF ht' he0' he1' hσ' (hs.setGlob_preserved _ _ hpi) ?_
            -- The values written agree, or their level is secret and so is the pc.
            rcases cond_cases hv with hvv | hlH
            · exact hp.imp (PresEq.setGlob (fun _ => hvv)) id
            · have hpcH := hl hlH
              subst hpcH
              exact .inr (hiUpTo_zero_cons _)
    | load lm ht' =>
      cases he0 with
      | load _ hsz0 hlab0 he0' =>
        cases he1 with
        | load _ hsz1 hlab1 he1' =>
          cases hσ with
          | cons ha hσ' =>
            refine ih _ (by omega) hF ht' he0' he1' (.cons (fun hl => ?_) hσ') hs hp
            obtain ⟨hl', _⟩ := Lab.join_eq_L hl
            obtain ⟨hla, hlm⟩ := Lab.join_eq_L hl'
            have haa := ha hla
            subst haa
            subst hlm
            exact hs.2.2.1 _ (Lab.eq_L_of_le hlab0 rfl) (Lab.eq_L_of_le hlab1 rfl)
    | store lm hle ht' =>
      cases he0 with
      | store _ hsz0 he0' =>
        cases he1 with
        | store _ hsz1 he1' =>
          cases hσ with
          | cons hv hσa =>
            cases hσa with
            | cons ha hσb =>
              refine ih _ (by omega) hF ht' he0' he1' hσb (hs.setMem (fun hlm => ?_))
                (hp.of_glob rfl rfl)
              have hj := Lab.eq_L_of_le hle hlm
              obtain ⟨hj', hlv⟩ := Lab.join_eq_L hj
              obtain ⟨_, hla⟩ := Lab.join_eq_L hj'
              exact ⟨ha hla, hv hlv⟩
    | memSize ht' =>
      cases he0 with
      | memSize he0' =>
        cases he1 with
        | memSize he1' =>
          exact ih _ (by omega) hF ht' he0' he1' (.cons (fun _ => hs.2.2.2.2.1) hσ) hs hp
    | memGrow hle ht' =>
      cases he0 with
      | memGrow he0' =>
        cases he1 with
        | memGrow he1' =>
          cases hσ with
          | cons hv hσ' =>
            -- the pc and the amount are public, so the two runs grow alike
            have hd := hv (Lab.join_eq_L (Lab.eq_L_of_le hle rfl)).2
            subst hd
            obtain ⟨hres, hs'⟩ := hs.grow _
            exact ih _ (by omega) hF ht' he0' he1' (.cons (fun _ => hres) hσ') hs'
              (hp.of_glob (State.grow_glob _ _) (State.grow_glob _ _))
    | block hfl hge hres hbody hrest =>
      obtain ⟨vs0, base0, m0, ob0, rfl, hvs0, hm0, hb0, hc0⟩ := block_inv he0
      obtain ⟨vs1, base1, m1, ob1, rfl, hvs1, hm1, hb1, hc1⟩ := block_inv he1
      obtain ⟨hvs, hbase⟩ := StkRel.split hσ (hvs0.trans hfl.length_eq.symm)
        (hvs1.trans hfl.length_eq.symm)
      have hrel := (ih _ hm0 hF hbody hb0 hb1 (hvs.mono hfl) hs (hp.enter (Lab.le_refl _))).toBody
      exact after_body hF
        (fun m hm σ0 s0 o0 m1 σ1 s1 o1 h0 h1 hσ hs hp => ih m hm hF hrest h0 h1 hσ hs hp)
        hrest hrel hbase hres (hp.mono (rise hbody).tail) hc0 hc1
    | loop hpc hpl hfl hge hres hbody hrest =>
      -- A loop is a block around the iterations of its body, which end at the loop's own pc.
      obtain ⟨vs0, base0, m0, ob0, rfl, hvs0, hm0, hb0, hc0⟩ := loop_inv he0
      obtain ⟨vs1, base1, m1, ob1, rfl, hvs1, hm1, hb1, hc1⟩ := loop_inv he1
      obtain ⟨hvs, hbase⟩ := StkRel.split hσ (hvs0.trans hfl.length_eq.symm)
        (hvs1.trans hfl.length_eq.symm)
      have hrel := (ih _ hm0 hF (Typed.iter hpl hge hbody) hb0 hb1 (hvs.mono hfl) hs
        (hp.enter hpc)).toBody
      exact after_body hF
        (fun m hm σ0 s0 o0 m1 σ1 s1 o1 h0 h1 hσ hs hp => ih m hm hF hrest h0 h1 hσ hs hp)
        hrest hrel hbase hres (hp.mono (rise hbody).tail) hc0 hc1
    | iter hpl hge hbody =>
      obtain ⟨m0, ob0, hm0, hb0, hc0⟩ := iter_inv he0
      obtain ⟨m1, ob1, hm1, hb1, hc1⟩ := iter_inv he1
      rcases ih _ hm0 hF hbody hb0 hb1 hσ hs hp with hsync | ⟨hloose, hbr⟩
      · cases hsync with
        | normal hσb hsb hpb =>
          -- both bodies end: the loop is done in both runs
          cases hc0 with
          | done hob0 ho0 =>
            cases hob0
            subst ho0
            cases hc1 with
            | done hob1 ho1 =>
              cases hob1
              subst ho1
              exact .inl (.normal hσb hsb (hpb.mono (.cons hpl (SFlows.refl _))))
            | again hob1 _ _ => cases hob1
            | exit hob1 _ => cases hob1
            | exn hob1 _ => cases hob1
          | again hob0 _ _ => cases hob0
          | exit hob0 _ => cases hob0
          | exn hob0 _ => cases hob0
        | exn htag hlen hsb hpe =>
          -- both bodies throw the same exception, which leaves the loop
          cases hc0 with
          | done hob0 _ => cases hob0
          | again hob0 _ _ => cases hob0
          | exit hob0 _ => cases hob0
          | exn hob0 ho0 =>
            cases hob0
            subst ho0
            cases hc1 with
            | done hob1 _ => cases hob1
            | again hob1 _ _ => cases hob1
            | exit hob1 _ => cases hob1
            | exn hob1 ho1 =>
              cases hob1
              subst ho1
              exact .inl (.exn htag hlen hsb hpe)
        | @br i rs' w0 w1 u0 u1 hLs hσb hsb hpb =>
          cases i with
          | zero =>
            -- both go round again
            simp at hLs
            subst hLs
            cases hc0 with
            | done hob0 _ => cases hob0
            | again hob0 hmr0 hr0 =>
              cases hob0
              cases hc1 with
              | done hob1 _ => cases hob1
              | again hob1 hmr1 hr1 =>
                cases hob1
                refine ih _ hmr0 hF (Typed.iter hpl hge hbody) hr0 hr1 hσb hsb ?_
                rcases hpb with h | h
                · exact .inl h
                · have hH := hpl h.head
                  subst hH
                  exact .inr (hiUpTo_zero_cons _)
              | exit hob1 _ => cases hob1
              | exn hob1 _ => cases hob1
            | exit hob0 _ => cases hob0
            | exn hob0 _ => cases hob0
          | succ i =>
            -- both branch past the loop
            cases hc0 with
            | done hob0 _ => cases hob0
            | again hob0 _ _ => cases hob0
            | exit hob0 ho0 =>
              cases hob0
              subst ho0
              cases hc1 with
              | done hob1 _ => cases hob1
              | again hob1 _ _ => cases hob1
              | exit hob1 ho1 =>
                cases hob1
                subst ho1
                exact .inl (.br (by simpa using hLs) hσb hsb (hpb.mono (.cons hpl (SFlows.refl _))))
              | exn hob1 _ => cases hob1
            | exn hob0 _ => cases hob0
      · -- the runs went apart in the body, under a secret pc: each iterates on its own
        obtain ⟨hst, hi0, hi1⟩ := hloose
        have hpH := hbr.elim (fun h => (hi0.hiUpTo_zero h).head) (fun h => (hi1.hiUpTo_zero h).head)
        have hpcL := hpl hpH
        subst hpcL
        obtain ⟨hc0', hi0'⟩ := iter_alone hF hge hbody hi0 hc0
        obtain ⟨hc1', hi1'⟩ := iter_alone hF hge hbody hi1 hc1
        exact loose_to_out hge (hiUpTo_zero_cons _)
          ⟨(hst.conf_left hc0').conf_right hc1', hi0', hi1'⟩
    | ite hfl hge hres h1 h2 hrest =>
      obtain ⟨c0, vs0, base0, m0, ob0, rfl, hvs0, hm0, hb0, hc0⟩ := ite_inv he0
      obtain ⟨c1, vs1, base1, m1, ob1, rfl, hvs1, hm1, hb1, hc1⟩ := ite_inv he1
      have hentry := hp.mono (sflows_joinEach (rise h1).tail (rise h2).tail).2.2
      cases hσ with
      | cons hc hσ' =>
        obtain ⟨hvs, hbase⟩ := StkRel.split hσ' (hvs0.trans hfl.length_eq.symm)
          (hvs1.trans hfl.length_eq.symm)
        rcases cond_cases hc with hcc | hlH
        · subst hcc
          obtain ⟨p', Px, harm, hPx, hple⟩ := arm_typed h1 h2 c0
          have hrel := ((ih _ hm0 hF harm hb0 hb1 (hvs.mono hfl) hs
            (hp.enter (Lab.le_join_left _ _))).mono (SFlows.cons (Lab.le_refl p') hPx)).toBody
          exact after_body hF
            (fun m hm σ0 s0 o0 m1 σ1 s1 o1 h0 h1 hσ hs hp => ih m hm hF hrest h0 h1 hσ hs hp)
            hrest hrel hbase (hres.mono hple) hentry hc0 hc1
        · subst hlH
          rw [Lab.join_H] at hge h1 h2
          obtain ⟨pa, Pa, harm0, hPa, _⟩ := arm_typed h1 h2 c0
          obtain ⟨pb, Pb, harm1, hPb, _⟩ := arm_typed h1 h2 c1
          obtain ⟨hs0, hi0⟩ := confine _ hF harm0 (hiUpTo_zero_cons _) hvs0 hb0
          obtain ⟨hs1, hi1⟩ := confine _ hF harm1 (hiUpTo_zero_cons _) hvs1 hb1
          have hrel : BodyRel C _ _ (Lab.H :: joinEach _ _) ob0 ob1 :=
            .inr ⟨⟨(hs.conf_left hs0).conf_right hs1, hi0.mono (.cons (Lab.le_H _) hPa),
              hi1.mono (.cons (Lab.le_H _) hPb)⟩, hiUpTo_zero_cons _, .inl hge⟩
          have hresH := hres.mono (p := Lab.H) (fun _ => by
            rw [(rise h1).head rfl]
            exact Lab.H_join _)
          exact after_body hF
            (fun m hm σ0 s0 o0 m1 σ1 s1 o1 h0 h1 hσ hs hp => ih m hm hF hrest h0 h1 hσ hs hp)
            hrest hrel hbase hresH hentry hc0 hc1
    | br hLs hge hfl =>
      cases he0 with
      | br hn0 =>
        cases he1 with
        | br hn1 =>
          have e0 := arity_eq hLs hn0
          have e1 := arity_eq hLs hn1
          subst e0 e1
          exact .inl (.br hLs (carried_rel hfl hσ) hs (hp.br (Nat.le_refl _) (Lab.le_refl _)))
    | brIf hLs hge hfl hrest =>
      cases he0 with
      | brIfTaken hc0 hn0 =>
        have e0 := arity_eq hLs hn0
        subst e0
        cases he1 with
        | brIfTaken hc1 hn1 =>
          have e1 := arity_eq hLs hn1
          subst e1
          cases hσ with
          | cons hc hσ' =>
            exact .inl (.br hLs (carried_rel hfl hσ') hs
              ((hp.br (Nat.le_refl _) (Lab.le_join_left _ _)).mono (rise hrest)))
        | brIfNot he1' =>
          cases hσ with
          | cons hc hσ' =>
            have hlH := (cond_cases hc).resolve_left hc0
            subst hlH
            rw [Lab.join_H] at hge hrest
            obtain ⟨hs1, hi1⟩ := confine _ hF hrest (hiUpTo_raise _ 0 _ (Nat.zero_le _))
              hσ'.length_right he1'
            refine .inr ⟨⟨hs.conf_right hs1, ⟨_, hLs, hge, ?_,
              HiUpTo.sflows (rise hrest) (hiUpTo_raise _ _ _ (Nat.le_refl _))⟩, hi1⟩, .inl trivial⟩
            have h1 := hσ'.length_left
            have h2 := hfl.length_eq
            simp only [List.length_append] at h1
            simp only [List.length_take]
            omega
      | brIfNot he0' =>
        cases he1 with
        | brIfTaken hc1 hn1 =>
          have e1 := arity_eq hLs hn1
          subst e1
          cases hσ with
          | cons hc hσ' =>
            have hlH := (cond_cases hc).resolve_left (fun h => hc1 h.symm)
            subst hlH
            rw [Lab.join_H] at hge hrest
            obtain ⟨hs0, hi0⟩ := confine _ hF hrest (hiUpTo_raise _ 0 _ (Nat.zero_le _))
              hσ'.length_left he0'
            refine .inr ⟨⟨hs.conf_left hs0, hi0, ⟨_, hLs, hge, ?_,
              HiUpTo.sflows (rise hrest) (hiUpTo_raise _ _ _ (Nat.le_refl _))⟩⟩, .inr trivial⟩
            have h1 := hσ'.length_right
            have h2 := hfl.length_eq
            simp only [List.length_append] at h1
            simp only [List.length_take]
            omega
        | brIfNot he1' =>
          cases hσ with
          | cons hc hσ' =>
            exact ih _ (by omega) hF hrest he0' he1' hσ' hs
              (hp.br (Nat.zero_le _) (Lab.le_join_left _ _))
    | brTable hall hge hfl =>
      cases he0 with
      | brTable hn0 =>
        cases he1 with
        | brTable hn1 =>
          cases hσ with
          | cons hc hσ' =>
            obtain ⟨hLs0, hk0, e0⟩ := table_target_info hall hn0
            obtain ⟨hLs1, hk1, e1⟩ := table_target_info hall hn1
            subst e0 e1
            rcases cond_cases hc with hcc | hlH
            · subst hcc
              exact .inl (.br hLs0 (carried_rel hfl hσ') hs (hp.br hk0 (Lab.le_join_left _ _)))
            · subst hlH
              rw [Lab.join_H] at hge ⊢
              have h1 := hσ'.length_left
              have h2 := hσ'.length_right
              have h3 := hfl.length_eq
              simp only [List.length_append] at h1 h2
              refine .inr ⟨⟨hs, ⟨_, hLs0, hge, ?_, hiUpTo_raise _ _ _ hk0⟩,
                ⟨_, hLs1, hge, ?_, hiUpTo_raise _ _ _ hk1⟩⟩, .inl trivial⟩
              · simp only [List.length_take]; omega
              · simp only [List.length_take]; omega
    | ret hLs hge hfl =>
      cases he0 with
      | ret hn0 =>
        cases he1 with
        | ret hn1 =>
          simp only [List.length_map] at hn0 hn1 ⊢
          have e0 := arity_eq hLs hn0
          have e1 := arity_eq hLs hn1
          subst e0 e1
          exact .inl (.br hLs (carried_rel hfl hσ) hs (hp.br (Nat.le_refl _) (Lab.le_refl _)))
    | call hft hpc hfl hrest =>
      obtain ⟨f0, args0, base0, m0, ob0, hf0, rfl, hargs0, hm0, hb0, hc0⟩ := call_inv he0
      obtain ⟨f1, args1, base1, m1, ob1, hf1, rfl, hargs1, hm1, hb1, hc1⟩ := call_inv he1
      cases hf0.symm.trans hf1
      obtain ⟨hty, q, hbodyT, hret⟩ := hF _ _ hf0
      cases hft.symm.trans hty
      obtain ⟨hargs, hbase⟩ := StkRel.split hσ (hargs0.trans hfl.length_eq.symm)
        (hargs1.trans hfl.length_eq.symm)
      have hrel := ih _ hm0 (hF.enter _) hbodyT hb0 hb1 .nil
        (StRel.enter (hargs.mono hfl) hs) (hp.call hpc)
      rcases fun_result hrel with ⟨r0, t0, r1, t1, hl0', hl1', hres, hst, hpt⟩ |
        ⟨t, k, w, u0, u1, ho0, ho1, htag, hlen, hst, hpe⟩
      · cases hc0 with
        | land hl0 hk0 hmr0 hr0 =>
          cases hc1 with
          | land hl1 hk1 hmr1 hr1 =>
            rw [hl0] at hl0'
            cases hl0'
            rw [hl1] at hl1'
            cases hl1'
            exact ih _ hmr0 hF hrest hr0 hr1 (hres.append hbase) (StRel.leave hs hst)
              (PresOr.of_glob rfl rfl
                (pres_after_call hret hp hk0 hk1 (hpt.imp (fun h i hi => h i hi) id)))
          | exn hob1 _ => subst hob1; simp [Out.lands] at hl1'
        | exn hob0 _ => subst hob0; simp [Out.lands] at hl0'
      · -- both callees end by the same exception, which leaves both callers
        subst ho0 ho1
        cases hc0 with
        | land hl0 _ _ _ => simp [Out.lands] at hl0
        | exn hob0 ho0 =>
          cases hob0
          subst ho0
          cases hc1 with
          | land hl1 _ _ _ => simp [Out.lands] at hl1
          | exn hob1 ho1 =>
            cases hob1
            subst ho1
            exact .inl (.exn htag hlen (StRel.leave hs hst) (fun i hi => hpe i hi))
    | callIndirect hpc hge hfl hrest =>
      obtain ⟨c0, i0, f0, args0, base0, m0, ob0, htbl0, hf0, hty0, rfl, hargs0, hm0, hb0, hc0⟩ :=
        callIndirect_inv he0
      obtain ⟨c1, i1, f1, args1, base1, m1, ob1, htbl1, hf1, hty1, rfl, hargs1, hm1, hb1, hc1⟩ :=
        callIndirect_inv he1
      cases hσ with
      | cons hc hσ' =>
        obtain ⟨hargs, hbase⟩ := StkRel.split hσ' (hargs0.trans hfl.length_eq.symm)
          (hargs1.trans hfl.length_eq.symm)
        obtain ⟨_, q0, hbody0, hret0⟩ := hF _ _ hf0
        obtain ⟨_, q1, hbody1, hret1⟩ := hF _ _ hf1
        rw [hty0] at hbody0
        rw [hty1] at hbody1
        rcases cond_cases hc with hcc | hlH
        · -- the same table entry: the same function, as for a direct call
          subst hcc
          rw [hs.2.2.2.1] at htbl0
          cases htbl0.symm.trans htbl1
          cases hf0.symm.trans hf1
          have hrel := ih _ hm0 (hF.enter _) hbody0 hb0 hb1 .nil
            (StRel.enter (hty0 ▸ hargs.mono hfl) hs)
            (hp.call (Lab.le_trans (Lab.le_join_left _ _) hpc))
          rcases fun_result hrel with ⟨r0, t0, r1, t1, hl0', hl1', hres, hst, hpt⟩ |
            ⟨t, k, w, u0, u1, ho0, ho1, htag, hlen, hst, hpe⟩
          · cases hc0 with
            | land hl0 hk0 hmr0 hr0 =>
              cases hc1 with
              | land hl1 hk1 hmr1 hr1 =>
                rw [hl0] at hl0'
                cases hl0'
                rw [hl1] at hl1'
                cases hl1'
                exact ih _ hmr0 hF hrest hr0 hr1 (hres.append hbase) (StRel.leave hs hst)
                  (PresOr.of_glob rfl rfl
                    (pres_after_call hret0 hp hk0 hk1 (hpt.imp (fun h i hi => h i hi) id)))
              | exn hob1 _ => subst hob1; simp [Out.lands] at hl1'
            | exn hob0 _ => subst hob0; simp [Out.lands] at hl0'
          · subst ho0 ho1
            cases hc0 with
            | land hl0 _ _ _ => simp [Out.lands] at hl0
            | exn hob0 ho0 =>
              cases hob0
              subst ho0
              cases hc1 with
              | land hl1 _ _ _ => simp [Out.lands] at hl1
              | exn hob1 ho1 =>
                cases hob1
                subst ho1
                exact .inl (.exn htag hlen (StRel.leave hs hst) (fun i hi => hpe i hi))
        · -- a secret index: two functions of the expected type, each run under a secret pc
          subst hlH
          have hbound := hpc (Lab.join_H _)
          subst hbound
          obtain ⟨hcf0, hi0⟩ := confine _ (hF.enter _) hbody0 (hiUpTo_zero_cons _) rfl hb0
          obtain ⟨hcf1, hi1⟩ := confine _ (hF.enter _) hbody1 (hiUpTo_zero_cons _) rfl hb1
          obtain ⟨r0, t0, hl0', hlen0, hst0, _⟩ := top_lands hi0
          obtain ⟨r1, t1, hl1', hlen1, hst1, _⟩ := top_lands hi1
          cases hc0 with
          | exn hob0 _ => subst hob0; exact False.elim hi0
          | land hl0 hk0 hmr0 hr0 =>
            cases hc1 with
            | exn hob1 _ => subst hob1; exact False.elim hi1
            | land hl1 hk1 hmr1 hr1 =>
              rw [hl0] at hl0'
              cases hl0'
              rw [hl1] at hl1'
              cases hl1'
              refine ih _ hmr0 hF hrest hr0 hr1
                ((StkRel.of_allH hge hlen0 hlen1).append hbase)
                ((hs.conf_left (Conf.call (hst0 ▸ hcf0))).conf_right (Conf.call (hst1 ▸ hcf1)))
                (PresOr.of_glob rfl rfl ?_)
              -- Each callee ends under a secret pc, so each compared the preserved globals
              -- with their values at the call.
              have hq0 : q0 = Lab.H := (rise hbody0).head rfl
              have hq1 : q1 = Lab.H := (rise hbody1).head rfl
              have hcov0 := hret0.resolve_left (by rw [hq0]; decide)
              have hcov1 := hret1.resolve_left (by rw [hq1]; decide)
              rcases hp with he | hh
              · exact .inl (fun i hi =>
                  ((hk0 i (hcov0 i hi)).trans (he i hi)).trans (hk1 i (hcov1 i hi)).symm)
              · exact .inr hh
    | throw htag hlen hall =>
      cases he0 with
      | throw =>
        cases he1 with
        | throw =>
          -- under a public pc the two runs agree on the preserved globals, and the values are public
          have hpe : PresEq C s0 s1 := hp.resolve_right (fun h => absurd h.head (by decide))
          have htake := StkRel.take_public hall hσ
          rw [hlen] at htake
          rw [htake]
          refine .inl (.exn htag ?_ hs hpe)
          have h1 := hσ.length_right
          simp only [List.length_append] at h1
          simp only [List.length_take]
          omega
    | tryTable hfl hres hcl hbody hrest =>
      obtain ⟨vs0, base0, m0, ob0, rfl, hvs0, hm0, hb0, hc0⟩ := try_inv he0
      obtain ⟨vs1, base1, m1, ob1, rfl, hvs1, hm1, hb1, hc1⟩ := try_inv he1
      obtain ⟨hvs, hbase⟩ := StkRel.split hσ (hvs0.trans hfl.length_eq.symm)
        (hvs1.trans hfl.length_eq.symm)
      have hrel := caught_rel hcl
        (ih _ hm0 hF hbody hb0 hb1 (hvs.mono hfl) hs (hp.enter (Lab.le_refl _)))
      exact after_body hF
        (fun m hm σ0 s0 o0 m1 σ1 s1 o1 h0 h1 hσ hs hp => ih m hm hF hrest h0 h1 hσ hs hp)
        hrest hrel hbase hres (hp.mono (rise hbody).tail) hc0 hc1
    | unreachable => cases he0

/-! ### A function of a well-typed module -/

/--
Termination-insensitive noninterference for a function of a well-typed module. Take two calls
of the function, from states that agree where public (the global variables, the preserved ones
included, and the memory cells that are public in both), with arguments that agree where the
function's parameters are public. If both end, then either both return or both end by the same
exception with the same values, and the states they leave agree where public. If they return,
their results agree where the result type is public, and they agree on the preserved globals
too if both runs pass the comparison that the function's return makes, as a callee's does: a
run that fails it traps. If they end by an exception, they agree on the preserved globals. A
call returns at the end of the body or by a branch to the function's label, which is what
`return` is; a call that traps or runs forever does not end. The function may call the module's
functions, itself included.
-/
theorem tini {C : Ctx} (hF : WellTyped C F) {i : Nat} {f : Func} (hf : F[i]? = some f)
    {a0 a1 : List Nat} {s0 s1 : State} {n0 n1 : Nat} {o0 o1 : Out}
    (h0 : Eval F n0 [f.ty.results.length] f.body [] { s0 with loc := frame a0 } o0)
    (h1 : Eval F n1 [f.ty.results.length] f.body [] { s1 with loc := frame a1 } o1)
    (ha : StkRel f.ty.params a0 a1) (hs : StRel C s0 s1) (hp : PresEq C s0 s1) :
    (∃ r0 t0 r1 t1, o0.lands = some (r0, t0) ∧ o1.lands = some (r1, t1) ∧
      StkRel f.ty.results r0 r1 ∧ StRel C { t0 with loc := s0.loc } { t1 with loc := s1.loc } ∧
      (Kept f.keep s0 t0 → Kept f.keep s1 t1 → PresEq C t0 t1)) ∨
    (∃ t w u0 u1, o0 = .exn t w u0 ∧ o1 = .exn t w u1 ∧
      StRel C { u0 with loc := s0.loc } { u1 with loc := s1.loc } ∧ PresEq C u0 u1) := by
  obtain ⟨_, q, hbody, hret⟩ := hF _ _ hf
  rcases fun_result (ni n0 (hF.enter f) hbody h0 h1 .nil (StRel.enter ha hs)
      (.inl (fun i hi => hp i hi))) with
    ⟨r0, t0, r1, t1, hl0, hl1, hres, hst, hpt⟩ | ⟨t, k, w, u0, u1, ho0, ho1, _, _, hst, hpe⟩
  · refine .inl ⟨r0, t0, r1, t1, hl0, hl1, hres, StRel.leave hs hst, fun hk0 hk1 => ?_⟩
    rcases pres_after_call (P := [Lab.L]) hret (.inl hp) hk0 hk1
      (hpt.imp (fun h i hi => h i hi) id) with h | h
    · exact h
    · exact absurd h.head (by decide)
  · exact .inr ⟨t, w, u0, u1, ho0, ho1, StRel.leave hs hst, fun i hi => hpe i hi⟩

end WasmIfc
