/-
Noninterference for the lift-free rules (`ni`), and its statement for a function body (`tini`).

Two runs of a typed sequence from inputs that agree where public end in outcomes related by
`OutRel`: either they end the same way, with results that agree where public, or they have
taken different paths under a secret pc and at least one of them is on its way out of a block.
In the second case nothing is said of their stacks. None is needed: the run that stays behind
runs on under a secret pc (`confine`), and where the two meet again, at the end of a block
that one left by a branch, the block's result type is all secret.
-/
import WasmIfc.Confinement

namespace WasmIfc

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

theorem OutRel.mono {C : Ctx} {Ls : List STy} {P P' : Pcs} {st : STy} {o0 o1 : Out}
    (hf : SFlows P P') (h : OutRel C Ls P st o0 o1) : OutRel C Ls P' st o0 o1 :=
  h.elim .inl (fun h => .inr ⟨h.1.mono hf, h.2⟩)

/-! ### After the body of a block or of a conditional -/

/--
How the outcomes of two runs of a block's body relate: as `OutRel` says, or apart with a result
type that is all secret (the two arms of a conditional on a secret).
-/
def BodyRel (C : Ctx) (Ls : List STy) (rs : STy) (P : Pcs) (ob0 ob1 : Out) : Prop :=
  Sync C (rs :: Ls) rs ob0 ob1 ∨
    (Loose C (rs :: Ls) P rs ob0 ob1 ∧ (AllGe Lab.H rs ∨ ob0.isBr ∨ ob1.isBr))

theorem OutRel.toBody {C : Ctx} {Ls : List STy} {rs : STy} {P : Pcs} {ob0 ob1 : Out}
    (h : OutRel C (rs :: Ls) P rs ob0 ob1) : BodyRel C Ls rs P ob0 ob1 :=
  h.elim .inl (fun h => .inr ⟨h.1, .inr h.2⟩)

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

/-- Both runs go on after the block: their stacks agree where public. -/
theorem join_land_land {C : Ctx} {Ls : List STy} {rs st : STy} {P : Pcs} {ob0 ob1 : Out}
    {σ0 σ1 b0 b1 : List Nat} {t0 t1 : State}
    (h : BodyRel C Ls rs P ob0 ob1) (hl0 : ob0.lands = some (σ0, t0))
    (hl1 : ob1.lands = some (σ1, t1)) (hb : StkRel st b0 b1) :
    StkRel (rs ++ st) (σ0 ++ b0) (σ1 ++ b1) ∧ StRel C t0 t1 := by
  rcases h with hs | ⟨⟨hst, hi0, hi1⟩, hx⟩
  · cases hs with
    | normal hσ hss =>
      simp [Out.lands] at hl0 hl1
      obtain ⟨rfl, rfl⟩ := hl0
      obtain ⟨rfl, rfl⟩ := hl1
      exact ⟨hσ.append hb, hss⟩
    | @br i rs' w0 w1 u0 u1 hLs hσ hss =>
      cases i with
      | zero =>
        simp [Out.lands] at hl0 hl1
        obtain ⟨rfl, rfl⟩ := hl0
        obtain ⟨rfl, rfl⟩ := hl1
        simp at hLs
        subst hLs
        exact ⟨hσ.append hb, hss⟩
      | succ i => simp [Out.lands] at hl0
  · obtain ⟨hlen0, hst0⟩ := lands_info hi0 hl0
    obtain ⟨hlen1, hst1⟩ := lands_info hi1 hl1
    have hall : AllGe Lab.H rs := by
      rcases hx with h | h | h
      · exact h
      · exact allH_of_lands hi0 h hl0
      · exact allH_of_lands hi1 h hl1
    refine ⟨(StkRel.of_allH hall hlen0 hlen1).append hb, ?_⟩
    rw [← hst0, ← hst1]
    exact hst

/-- Both runs branch past the block. -/
theorem join_exit_exit {C : Ctx} {Ls : List STy} {rs : STy} {p : Lab} {P1 : Pcs}
    {ob0 ob1 o0 o1 : Out} (h : BodyRel C Ls rs (p :: P1) ob0 ob1)
    (hx0 : ob0.exits = some o0) (hx1 : ob1.exits = some o1) (st : STy) :
    OutRel C Ls P1 st o0 o1 := by
  rcases h with hs | ⟨⟨hst, hi0, hi1⟩, _⟩
  · cases hs with
    | normal _ _ => simp [Out.exits] at hx0
    | @br i rs' w0 w1 u0 u1 hLs hσ hss =>
      cases i with
      | zero => simp [Out.exits] at hx0
      | succ i =>
        simp [Out.exits] at hx0 hx1
        subst hx0 hx1
        exact .inl (.br (by simpa using hLs) hσ hss)
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
  rcases h with hs | ⟨⟨hst, hi0, hi1⟩, _⟩
  · cases hs with
    | normal _ _ => simp [Out.exits] at hx1
    | @br i rs' w0 w1 u0 u1 hLs hσ hss =>
      cases i with
      | zero => simp [Out.exits] at hx1
      | succ i => simp [Out.lands] at hl0
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
  rcases h with hs | ⟨⟨hst, hi0, hi1⟩, _⟩
  · cases hs with
    | normal _ _ => simp [Out.exits] at hx0
    | @br i rs' w0 w1 u0 u1 hLs hσ hss =>
      cases i with
      | zero => simp [Out.exits] at hx0
      | succ i => simp [Out.lands] at hl1
  · obtain ⟨hlen1, hst1⟩ := lands_info hi1 hl1
    obtain ⟨hs0, hb0, hinfo0⟩ := exits_info hi0 hx0
    refine ⟨hlen1, ?_, hb0, hinfo0⟩
    rw [← hst1, hs0]
    exact hst

/-- What a block does after its body: the rest of the sequence, or a branch further out. -/
inductive Cont (ls : List Nat) (rest : List Instr) (base : List Nat) (ob : Out) (n : Nat)
    (o : Out) : Prop where
  | land {m : Nat} {σ1 : List Nat} {s1 : State} :
      ob.lands = some (σ1, s1) → m < n → Eval m ls rest (σ1 ++ base) s1 o →
      Cont ls rest base ob n o
  | exit : ob.exits = some o → Cont ls rest base ob n o

theorem block_inv {n : Nat} {ls : List Nat} {ps rs : STy} {body rest : List Instr}
    {σ : List Nat} {s : State} {o : Out} (h : Eval n ls (.block ps rs body :: rest) σ s o) :
    ∃ vs base n1 ob, σ = vs ++ base ∧ vs.length = ps.length ∧ n1 < n ∧
      Eval n1 (rs.length :: ls) body vs s ob ∧ Cont ls rest base ob n o := by
  cases h with
  | blockCont hvs hb hl hr => exact ⟨_, _, _, _, rfl, hvs, by omega, hb, .land hl (by omega) hr⟩
  | blockExit hvs hb hx => exact ⟨_, _, _, _, rfl, hvs, by omega, hb, .exit hx⟩

theorem ite_inv {n : Nat} {ls : List Nat} {ps rs : STy} {thn els rest : List Instr}
    {σ : List Nat} {s : State} {o : Out} (h : Eval n ls (.ite ps rs thn els :: rest) σ s o) :
    ∃ c vs base n1 ob, σ = c :: (vs ++ base) ∧ vs.length = ps.length ∧ n1 < n ∧
      Eval n1 (rs.length :: ls) (if c = 0 then els else thn) vs s ob ∧ Cont ls rest base ob n o := by
  cases h with
  | iteCont hvs hb hl hr => exact ⟨_, _, _, _, _, rfl, hvs, by omega, hb, .land hl (by omega) hr⟩
  | iteExit hvs hb hx => exact ⟨_, _, _, _, _, rfl, hvs, by omega, hb, .exit hx⟩

/--
The two runs after the body of a block or of a conditional, given noninterference for the rest
of the sequence on smaller derivations of the first run.
-/
theorem after_body {C : Ctx} {Ls : List STy} {rs st st' : STy} {p : Lab} {P1 P' : Pcs}
    {rest : List Instr} {ob0 ob1 o0 o1 : Out} {base0 base1 : List Nat} {n0 n1 : Nat}
    (hIH : ∀ m, m < n0 → ∀ (σ0 : List Nat) (s0 : State) (o0 : Out) (m1 : Nat) (σ1 : List Nat)
      (s1 : State) (o1 : Out), Eval m (Ls.map List.length) rest σ0 s0 o0 →
      Eval m1 (Ls.map List.length) rest σ1 s1 o1 → StkRel (rs ++ st) σ0 σ1 → StRel C s0 s1 →
      OutRel C Ls P' st' o0 o1)
    (hrest : Typed C Ls rest P1 (rs ++ st) P' st')
    (hrel : BodyRel C Ls rs (p :: P1) ob0 ob1)
    (hbase : StkRel st base0 base1)
    (hc0 : Cont (Ls.map List.length) rest base0 ob0 n0 o0)
    (hc1 : Cont (Ls.map List.length) rest base1 ob1 n1 o1) : OutRel C Ls P' st' o0 o1 := by
  cases hc0 with
  | land hl0 hm0 he0 =>
    cases hc1 with
    | land hl1 hm1 he1 =>
      obtain ⟨hσ, hs⟩ := join_land_land hrel hl0 hl1 hbase
      exact hIH _ hm0 _ _ _ _ _ _ _ he0 he1 hσ hs
    | exit hx1 =>
      obtain ⟨hlen0, hs, hbr1, hinfo1⟩ := join_land_exit hrel hl0 hx1
      have hP1 : HiUpTo 0 P1 := (hinfo1 st').hiUpTo_zero hbr1
      obtain ⟨hs0, hi0⟩ := confine C _ hrest hP1
        (by simp only [List.length_append, hlen0, hbase.length_left]) he0
      exact .inr ⟨⟨hs0.symm.trans hs, hi0, (hinfo1 st').mono (rise hrest)⟩, .inr hbr1⟩
  | exit hx0 =>
    cases hc1 with
    | land hl1 hm1 he1 =>
      obtain ⟨hlen1, hs, hbr0, hinfo0⟩ := join_exit_land hrel hx0 hl1
      have hP1 : HiUpTo 0 P1 := (hinfo0 st').hiUpTo_zero hbr0
      obtain ⟨hs1, hi1⟩ := confine C _ hrest hP1
        (by simp only [List.length_append, hlen1, hbase.length_right]) he1
      exact .inr ⟨⟨hs.trans hs1, (hinfo0 st').mono (rise hrest), hi1⟩, .inl hbr0⟩
    | exit hx1 => exact (join_exit_exit hrel hx0 hx1 st').mono (rise hrest)

/-! ### After the body of a loop -/

/-- What a loop does after its body: the rest of the sequence, another iteration, or a branch further out. -/
inductive LoopCont (ls : List Nat) (ps rs : STy) (body rest : List Instr) (base : List Nat)
    (ob : Out) (n : Nat) (o : Out) : Prop where
  | done {m : Nat} {σ1 : List Nat} {s1 : State} :
      ob = .normal σ1 s1 → m < n → Eval m ls rest (σ1 ++ base) s1 o →
      LoopCont ls ps rs body rest base ob n o
  | again {m : Nat} {w : List Nat} {s1 : State} :
      ob = .br 0 w s1 → m < n → Eval m ls (.loop ps rs body :: rest) (w ++ base) s1 o →
      LoopCont ls ps rs body rest base ob n o
  | exit : ob.exits = some o → LoopCont ls ps rs body rest base ob n o

theorem loop_inv {n : Nat} {ls : List Nat} {ps rs : STy} {body rest : List Instr}
    {σ : List Nat} {s : State} {o : Out} (h : Eval n ls (.loop ps rs body :: rest) σ s o) :
    ∃ vs base n1 ob, σ = vs ++ base ∧ vs.length = ps.length ∧ n1 < n ∧
      Eval n1 (ps.length :: ls) body vs s ob ∧ LoopCont ls ps rs body rest base ob n o := by
  cases h with
  | loopDone hvs hb hr => exact ⟨_, _, _, _, rfl, hvs, by omega, hb, .done rfl (by omega) hr⟩
  | loopAgain hvs hb hr => exact ⟨_, _, _, _, rfl, hvs, by omega, hb, .again rfl (by omega) hr⟩
  | loopExit hvs hb hx => exact ⟨_, _, _, _, rfl, hvs, by omega, hb, .exit hx⟩

/--
A run that is on its own from the state `t` on: it reaches the code after the loop with the
public variables as in `t` and the loop's results on the stack, or it branches past the loop.
-/
def Tail (C : Ctx) (Ls : List STy) (P1 : Pcs) (rs : STy) (rest : List Instr) (base : List Nat)
    (t : State) (n : Nat) (o : Out) : Prop :=
  (∃ m σb s2, m < n ∧ σb.length = rs.length ∧ StRel C t s2 ∧
      Eval m (Ls.map List.length) rest (σb ++ base) s2 o) ∨
    (StRel C t o.state ∧ o.isBr ∧ ∀ st, Info Ls P1 st o)

theorem loop_tail {C : Ctx} {Ls : List STy} {ps rs : STy} {body rest : List Instr} {Pb P1 : Pcs}
    {p : Lab} {base : List Nat} {ob o : Out} {n : Nat}
    (hbody : Typed C (ps :: Ls) body (Lab.H :: Pb) ps (p :: P1) rs)
    (hi : Info (ps :: Ls) (p :: P1) rs ob)
    (hc : LoopCont (Ls.map List.length) ps rs body rest base ob n o) :
    Tail C Ls P1 rs rest base ob.state n o := by
  cases hc with
  | done hob hm he =>
    subst hob
    exact .inl ⟨_, _, _, hm, hi, StRel.refl _ _, he⟩
  | again hob hm he =>
    subst hob
    obtain ⟨rs', h1, _, h3, _⟩ := hi
    simp at h1
    subst h1
    rcases loop_alone C _ hbody h3 rfl he with ⟨m, σb, s2, hm', hlen, hs2, he2⟩ | h
    · exact .inl ⟨m, σb, s2, by omega, hlen, hs2, he2⟩
    · exact .inr h
  | exit hx =>
    obtain ⟨hst, hbr, hinfo⟩ := exits_info hi hx
    refine .inr ⟨?_, hbr, hinfo⟩
    rw [hst]
    exact StRel.refl _ _

/-- Two runs that are each on their own, after a loop whose result type is all secret. -/
theorem after_tails {C : Ctx} {Ls : List STy} {rs st st' : STy} {P1 P' : Pcs}
    {rest : List Instr} {o0 o1 : Out} {base0 base1 : List Nat} {t0 t1 : State} {n0 n1 : Nat}
    (hIH : ∀ m, m < n0 → ∀ (σ0 : List Nat) (s0 : State) (o0 : Out) (m1 : Nat) (σ1 : List Nat)
      (s1 : State) (o1 : Out), Eval m (Ls.map List.length) rest σ0 s0 o0 →
      Eval m1 (Ls.map List.length) rest σ1 s1 o1 → StkRel (rs ++ st) σ0 σ1 → StRel C s0 s1 →
      OutRel C Ls P' st' o0 o1)
    (hrest : Typed C Ls rest P1 (rs ++ st) P' st') (hall : AllGe Lab.H rs)
    (hbase : StkRel st base0 base1) (hs : StRel C t0 t1)
    (h0 : Tail C Ls P1 rs rest base0 t0 n0 o0) (h1 : Tail C Ls P1 rs rest base1 t1 n1 o1) :
    OutRel C Ls P' st' o0 o1 := by
  rcases h0 with ⟨m0, σ0, s0, hm0, hlen0, hs0, he0⟩ | ⟨hs0, hbr0, hinfo0⟩
  · rcases h1 with ⟨m1, σ1, s1, hm1, hlen1, hs1, he1⟩ | ⟨hs1, hbr1, hinfo1⟩
    · exact hIH _ hm0 _ _ _ _ _ _ _ he0 he1 ((StkRel.of_allH hall hlen0 hlen1).append hbase)
        (hs0.symm.trans (hs.trans hs1))
    · have hP1 := (hinfo1 st').hiUpTo_zero hbr1
      obtain ⟨hs0', hi0⟩ := confine C _ hrest hP1
        (by simp only [List.length_append, hlen0, hbase.length_left]) he0
      exact .inr ⟨⟨(hs0.trans hs0').symm.trans (hs.trans hs1), hi0,
        (hinfo1 st').mono (rise hrest)⟩, .inr hbr1⟩
  · rcases h1 with ⟨m1, σ1, s1, hm1, hlen1, hs1, he1⟩ | ⟨hs1, hbr1, hinfo1⟩
    · have hP1 := (hinfo0 st').hiUpTo_zero hbr0
      obtain ⟨hs1', hi1⟩ := confine C _ hrest hP1
        (by simp only [List.length_append, hlen1, hbase.length_right]) he1
      exact .inr ⟨⟨hs0.symm.trans (hs.trans (hs1.trans hs1')), (hinfo0 st').mono (rise hrest),
        hi1⟩, .inl hbr0⟩
    · exact .inr ⟨⟨hs0.symm.trans (hs.trans hs1), (hinfo0 st').mono (rise hrest),
        (hinfo1 st').mono (rise hrest)⟩, .inl hbr0⟩

/-- The values a branch carries agree where the label's type is public. -/
theorem carried_rel {carried rs st : STy} {σ0 σ1 : List Nat} (hfl : SFlows carried rs)
    (hσ : StkRel (carried ++ st) σ0 σ1) :
    StkRel rs (σ0.take rs.length) (σ1.take rs.length) := by
  have h := StkRel.take hσ
  rw [hfl.length_eq] at h
  exact h.mono hfl

/-! ### Noninterference -/

theorem ni (C : Ctx) : ∀ (n0 : Nat) {Ls : List STy} {e : List Instr} {P P' : Pcs}
    {st st' : STy} {σ0 : List Nat} {s0 : State} {o0 : Out} {n1 : Nat} {σ1 : List Nat}
    {s1 : State} {o1 : Out},
    Typed C Ls e P st P' st' →
    Eval n0 (Ls.map List.length) e σ0 s0 o0 → Eval n1 (Ls.map List.length) e σ1 s1 o1 →
    StkRel st σ0 σ1 → StRel C s0 s1 → OutRel C Ls P' st' o0 o1 := by
  intro n0
  induction n0 using Nat.strongRecOn with
  | ind n0 ih =>
    intro Ls e P P' st st' σ0 s0 o0 n1 σ1 s1 o1 ht he0 he1 hσ hs
    cases ht with
    | nil =>
      cases he0
      cases he1
      exact .inl (.normal hσ hs)
    | const v ht' =>
      cases he0 with
      | const _ he0' =>
        cases he1 with
        | const _ he1' => exact ih _ (by omega) ht' he0' he1' (.cons (fun _ => rfl) hσ) hs
    | binop f ht' =>
      cases he0 with
      | binop _ he0' =>
        cases he1 with
        | binop _ he1' =>
          cases hσ with
          | cons h0 hσ' =>
            cases hσ' with
            | cons h1 hσ'' =>
              refine ih _ (by omega) ht' he0' he1' (.cons (fun hl => ?_) hσ'') hs
              obtain ⟨hl01, _⟩ := Lab.join_eq_L hl
              obtain ⟨hl0, hl1⟩ := Lab.join_eq_L hl01
              rw [h0 hl0, h1 hl1]
    | select ht' =>
      cases he0 with
      | select he0' =>
        cases he1 with
        | select he1' =>
          cases hσ with
          | cons hc hσ' =>
            cases hσ' with
            | cons h1 hσ'' =>
              cases hσ'' with
              | cons h2 hσ''' =>
                refine ih _ (by omega) ht' he0' he1' (.cons (fun hl => ?_) hσ''') hs
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
          | cons _ hσ' => exact ih _ (by omega) ht' he0' he1' hσ' hs
    | nop ht' =>
      cases he0 with
      | nop he0' =>
        cases he1 with
        | nop he1' => exact ih _ (by omega) ht' he0' he1' hσ hs
    | relabel hf ht' =>
      cases he0 with
      | relabel he0' =>
        cases he1 with
        | relabel he1' => exact ih _ (by omega) ht' he0' he1' (hσ.mono hf) hs
    | localGet i ht' =>
      cases he0 with
      | localGet _ he0' =>
        cases he1 with
        | localGet _ he1' =>
          exact ih _ (by omega) ht' he0' he1'
            (.cons (fun hl => hs.1 i (Lab.join_eq_L hl).1) hσ) hs
    | localSet i hpc hl ht' =>
      cases he0 with
      | localSet _ he0' =>
        cases he1 with
        | localSet _ he1' =>
          cases hσ with
          | cons hv hσ' =>
            exact ih _ (by omega) ht' he0' he1' hσ'
              (hs.setLoc (fun hi => hv (Lab.eq_L_of_le hl hi)))
    | globalGet i ht' =>
      cases he0 with
      | globalGet _ he0' =>
        cases he1 with
        | globalGet _ he1' =>
          exact ih _ (by omega) ht' he0' he1'
            (.cons (fun hl => hs.2 i (Lab.join_eq_L hl).1) hσ) hs
    | globalSet i hpc hl ht' =>
      cases he0 with
      | globalSet _ he0' =>
        cases he1 with
        | globalSet _ he1' =>
          cases hσ with
          | cons hv hσ' =>
            exact ih _ (by omega) ht' he0' he1' hσ'
              (hs.setGlob (fun hi => hv (Lab.eq_L_of_le hl hi)))
    | block hfl hge hbody hrest =>
      obtain ⟨vs0, base0, m0, ob0, rfl, hvs0, hm0, hb0, hc0⟩ := block_inv he0
      obtain ⟨vs1, base1, m1, ob1, rfl, hvs1, hm1, hb1, hc1⟩ := block_inv he1
      obtain ⟨hvs, hbase⟩ := StkRel.split hσ (hvs0.trans hfl.length_eq.symm)
        (hvs1.trans hfl.length_eq.symm)
      have hrel := (ih _ hm0 hbody hb0 hb1 (hvs.mono hfl) hs).toBody
      exact after_body (fun m hm σ0 s0 o0 m1 σ1 s1 o1 h0 h1 hσ hs => ih m hm hrest h0 h1 hσ hs)
        hrest hrel hbase hc0 hc1
    | loop hpc hp hfl hge hbody hrest =>
      obtain ⟨vs0, base0, m0, ob0, rfl, hvs0, hm0, hb0, hc0⟩ := loop_inv he0
      obtain ⟨vs1, base1, m1, ob1, rfl, hvs1, hm1, hb1, hc1⟩ := loop_inv he1
      obtain ⟨hvs, hbase⟩ := StkRel.split hσ (hvs0.trans hfl.length_eq.symm)
        (hvs1.trans hfl.length_eq.symm)
      rcases ih _ hm0 hbody hb0 hb1 (hvs.mono hfl) hs with hsync | ⟨hloose, hbr⟩
      · cases hsync with
        | normal hσb hsb =>
          cases hc0 with
          | done hob0 hmr0 hr0 =>
            cases hob0
            cases hc1 with
            | done hob1 hmr1 hr1 =>
              cases hob1
              exact ih _ hmr0 hrest hr0 hr1 (hσb.append hbase) hsb
            | again hob1 _ _ => cases hob1
            | exit hx1 => simp [Out.exits] at hx1
          | again hob0 _ _ => cases hob0
          | exit hx0 => simp [Out.exits] at hx0
        | @br i rs' w0 w1 u0 u1 hLs hσb hsb =>
          cases i with
          | zero =>
            simp at hLs
            subst hLs
            cases hc0 with
            | done hob0 _ _ => cases hob0
            | again hob0 hmr0 hr0 =>
              cases hob0
              cases hc1 with
              | done hob1 _ _ => cases hob1
              | again hob1 hmr1 hr1 =>
                cases hob1
                exact ih _ hmr0 (Typed.loop hpc hp (SFlows.refl _) hge hbody hrest) hr0 hr1
                  (hσb.append hbase) hsb
              | exit hx1 => simp [Out.exits] at hx1
            | exit hx0 => simp [Out.exits] at hx0
          | succ i =>
            cases hc0 with
            | done hob0 _ _ => cases hob0
            | again hob0 _ _ => cases hob0
            | exit hx0 =>
              cases hc1 with
              | done hob1 _ _ => cases hob1
              | again hob1 _ _ => cases hob1
              | exit hx1 =>
                simp [Out.exits] at hx0 hx1
                subst hx0 hx1
                exact .inl (.br (by simpa using hLs) hσb hsb)
      · obtain ⟨hst, hi0, hi1⟩ := hloose
        have hpcL := hp (by
          rcases hbr with h | h
          · exact (hi0.hiUpTo_zero h).head
          · exact (hi1.hiUpTo_zero h).head)
        subst hpcL
        exact after_tails
          (fun m hm σ0 s0 o0 m1 σ1 s1 o1 h0 h1 hσ hs => ih m hm hrest h0 h1 hσ hs)
          hrest hge hbase hst (loop_tail hbody hi0 hc0) (loop_tail hbody hi1 hc1)
    | ite hfl hge h1 h2 hrest =>
      obtain ⟨c0, vs0, base0, m0, ob0, rfl, hvs0, hm0, hb0, hc0⟩ := ite_inv he0
      obtain ⟨c1, vs1, base1, m1, ob1, rfl, hvs1, hm1, hb1, hc1⟩ := ite_inv he1
      cases hσ with
      | cons hc hσ' =>
        obtain ⟨hvs, hbase⟩ := StkRel.split hσ' (hvs0.trans hfl.length_eq.symm)
          (hvs1.trans hfl.length_eq.symm)
        rcases cond_cases hc with hcc | hlH
        · subst hcc
          obtain ⟨p', Px, harm, hPx⟩ := arm_typed h1 h2 c0
          have hrel := ((ih _ hm0 harm hb0 hb1 (hvs.mono hfl) hs).mono
            (SFlows.cons (Lab.le_refl p') hPx)).toBody
          exact after_body
            (fun m hm σ0 s0 o0 m1 σ1 s1 o1 h0 h1 hσ hs => ih m hm hrest h0 h1 hσ hs)
            hrest hrel hbase hc0 hc1
        · subst hlH
          rw [Lab.join_H] at hge h1 h2
          obtain ⟨pa, Pa, harm0, hPa⟩ := arm_typed h1 h2 c0
          obtain ⟨pb, Pb, harm1, hPb⟩ := arm_typed h1 h2 c1
          obtain ⟨hs0, hi0⟩ := confine C _ harm0 (hiUpTo_zero_cons _) hvs0 hb0
          obtain ⟨hs1, hi1⟩ := confine C _ harm1 (hiUpTo_zero_cons _) hvs1 hb1
          have hrel : BodyRel C _ _ (Lab.H :: joinEach _ _) ob0 ob1 :=
            .inr ⟨⟨hs0.symm.trans (hs.trans hs1), hi0.mono (.cons (Lab.le_H _) hPa),
              hi1.mono (.cons (Lab.le_H _) hPb)⟩, .inl hge⟩
          exact after_body
            (fun m hm σ0 s0 o0 m1 σ1 s1 o1 h0 h1 hσ hs => ih m hm hrest h0 h1 hσ hs)
            hrest hrel hbase hc0 hc1
    | br hLs hge hfl =>
      cases he0 with
      | br hn0 =>
        cases he1 with
        | br hn1 =>
          have e0 := arity_eq hLs hn0
          have e1 := arity_eq hLs hn1
          subst e0 e1
          exact .inl (.br hLs (carried_rel hfl hσ) hs)
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
          | cons hc hσ' => exact .inl (.br hLs (carried_rel hfl hσ') hs)
        | brIfNot he1' =>
          cases hσ with
          | cons hc hσ' =>
            have hlH := (cond_cases hc).resolve_left hc0
            subst hlH
            rw [Lab.join_H] at hge hrest
            obtain ⟨hs1, hi1⟩ := confine C _ hrest (hiUpTo_raise _ 0 _ (Nat.zero_le _))
              hσ'.length_right he1'
            refine .inr ⟨⟨hs.trans hs1, ⟨_, hLs, hge, ?_,
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
            obtain ⟨hs0, hi0⟩ := confine C _ hrest (hiUpTo_raise _ 0 _ (Nat.zero_le _))
              hσ'.length_left he0'
            refine .inr ⟨⟨hs0.symm.trans hs, hi0, ⟨_, hLs, hge, ?_,
              HiUpTo.sflows (rise hrest) (hiUpTo_raise _ _ _ (Nat.le_refl _))⟩⟩, .inr trivial⟩
            have h1 := hσ'.length_right
            have h2 := hfl.length_eq
            simp only [List.length_append] at h1
            simp only [List.length_take]
            omega
        | brIfNot he1' =>
          cases hσ with
          | cons hc hσ' => exact ih _ (by omega) hrest he0' he1' hσ' hs
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
              exact .inl (.br hLs0 (carried_rel hfl hσ') hs)
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
    | unreachable => cases he0

/-! ### A function body -/

theorem top_lands {rs : STy} {P : Pcs} {o : Out} (h : Info [rs] P rs o) :
    ∃ r t, o.lands = some (r, t) ∧ r.length = rs.length ∧ o.state = t ∧
      (o.isBr → AllGe Lab.H rs) := by
  cases o with
  | normal σ s => exact ⟨σ, s, rfl, h, rfl, fun hbr => False.elim hbr⟩
  | br i w s =>
    obtain ⟨rs', h1, h2, h3, _⟩ := h
    cases i with
    | zero =>
      simp at h1
      subst h1
      exact ⟨w, s, rfl, h3, rfl, fun _ => h2⟩
    | succ i => simp at h1

/--
Termination-insensitive noninterference for a function body. The body is typed as the paper's
rule for functions types it: under the one label of the function, whose type is the function's
result type `rs`, from the empty stack, at the pc `pc` (the function's bound). Two runs from
states that agree on the public variables, if both end, end with results that agree where `rs`
is public and in states that agree on the public variables. A run ends at the end of the body
or by a branch to the function's label, which is how `return` leaves it.
-/
theorem tini {C : Ctx} {rs : STy} {body : List Instr} {pc : Lab} {P' : Pcs} {n0 n1 : Nat}
    {s0 s1 : State} {o0 o1 : Out}
    (ht : Typed C [rs] body [pc] [] P' rs)
    (h0 : Eval n0 [rs.length] body [] s0 o0) (h1 : Eval n1 [rs.length] body [] s1 o1)
    (hs : StRel C s0 s1) :
    ∃ r0 t0 r1 t1, o0.lands = some (r0, t0) ∧ o1.lands = some (r1, t1) ∧
      StkRel rs r0 r1 ∧ StRel C t0 t1 := by
  have h : OutRel C [rs] P' rs o0 o1 := ni C n0 ht h0 h1 .nil hs
  rcases h with hsync | ⟨⟨hst, hi0, hi1⟩, hbr⟩
  · cases hsync with
    | normal hσ hss => exact ⟨_, _, _, _, rfl, rfl, hσ, hss⟩
    | @br i rs' w0 w1 u0 u1 hLs hσ hss =>
      cases i with
      | zero =>
        simp at hLs
        subst hLs
        exact ⟨_, _, _, _, rfl, rfl, hσ, hss⟩
      | succ i => simp at hLs
  · obtain ⟨r0, t0, hl0, hlen0, hst0, hall0⟩ := top_lands hi0
    obtain ⟨r1, t1, hl1, hlen1, hst1, hall1⟩ := top_lands hi1
    refine ⟨r0, t0, r1, t1, hl0, hl1, StkRel.of_allH (hbr.elim hall0 hall1) hlen0 hlen1, ?_⟩
    rw [← hst0, ← hst1]
    exact hst

end WasmIfc
