/-
One run under a secret pc: it changes nothing the attacker sees, and it leaves by a branch only
to a label whose type is all secret (`confine`). A loop whose body is typed under a secret pc
is such a run from its second iteration on, although the loop itself may be entered under a
public pc (`loop_alone`).
-/
import WasmIfc.Basic

namespace WasmIfc

variable {F : List Func}

theorem hiUpTo_zero_cons (P : Pcs) : HiUpTo 0 (Lab.H :: P) := by
  intro k p hk hp
  have hk0 : k = 0 := by omega
  subst hk0
  simpa using hp.symm

theorem hiUpTo_zero_raise (a : Lab) (P : Pcs) (i : Nat) : HiUpTo 0 (raise a (Lab.H :: P) i) := by
  intro k p hk hp
  have hk0 : k = 0 := by omega
  subst hk0
  cases i <;> simpa [raise, Lab.join_H] using hp.symm

/-- The arity the semantics has for a label is the length of the label's type. -/
theorem arity_eq {Ls : List STy} {i n : Nat} {rs : STy} (h : Ls[i]? = some rs)
    (hn : (Ls.map List.length)[i]? = some n) : n = rs.length := by
  simp [List.getElem?_map, h] at hn
  exact hn.symm

theorem tableTarget_mem (ts : List Nat) (d c : Nat) : tableTarget ts d c ∈ d :: ts := by
  unfold tableTarget
  cases h : ts[c]? with
  | none => simp
  | some x => simp [List.mem_of_getElem? h]

/-- What a block continues with has the shape of the block's results. -/
theorem lands_info {Ls : List STy} {rs : STy} {P : Pcs} {ob : Out} {σ1 : List Nat} {s1 : State}
    (h : Info (rs :: Ls) P rs ob) (hl : ob.lands = some (σ1, s1)) :
    σ1.length = rs.length ∧ ob.state = s1 := by
  cases ob with
  | normal σ s =>
    simp [Out.lands] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact ⟨h, rfl⟩
  | br i w s =>
    cases i with
    | zero =>
      simp [Out.lands] at hl
      obtain ⟨rfl, rfl⟩ := hl
      obtain ⟨rs', h1, _, h3, _⟩ := h
      simp at h1
      subst h1
      exact ⟨h3, rfl⟩
    | succ i => simp [Out.lands] at hl

/-- A branch past a block is, seen from outside the block, a branch under a secret pc again. -/
theorem exits_info {Ls : List STy} {l0 : STy} {p : Lab} {P1 : Pcs} {st : STy} {ob o : Out}
    (h : Info (l0 :: Ls) (p :: P1) st ob) (hx : ob.exits = some o) :
    o.state = ob.state ∧ o.isBr ∧ ∀ st2, Info Ls P1 st2 o := by
  cases ob with
  | normal σ s => simp [Out.exits] at hx
  | br i w s =>
    cases i with
    | zero => simp [Out.exits] at hx
    | succ i =>
      simp [Out.exits] at hx
      subst hx
      obtain ⟨rs, h1, h2, h3, h4⟩ := h
      exact ⟨rfl, trivial, fun _ => ⟨rs, by simpa using h1, h2, h3, h4.tail⟩⟩

/-- A function body ends at its end or by a branch to the function's label, with as many values as it has results. -/
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

/-- The arm a condition selects is typed, and ends below the join of the two arms' pc stacks. -/
theorem arm_typed {C : Ctx} {Ls : List STy} {thn els : List Instr} {pcl pc p1 p2 : Lab}
    {Pr P1 P2 : Pcs} {ps rs : STy}
    (h1 : Typed C (rs :: Ls) thn (pcl :: pc :: Pr) ps (p1 :: P1) rs)
    (h2 : Typed C (rs :: Ls) els (pcl :: pc :: Pr) ps (p2 :: P2) rs) (c : Nat) :
    ∃ p' P', Typed C (rs :: Ls) (if c = 0 then els else thn) (pcl :: pc :: Pr) ps (p' :: P') rs ∧
      SFlows P' (joinEach P1 P2) := by
  have hj := sflows_joinEach (rise h1).tail (rise h2).tail
  by_cases hc : c = 0
  · exact ⟨p2, P2, by simpa [hc] using h2, hj.2.1⟩
  · exact ⟨p1, P1, by simpa [hc] using h1, hj.1⟩

/--
Confinement. A typed sequence that starts under a secret pc leaves the public variables as
they were, and its outcome is as `Info` describes.
-/
theorem confine : ∀ (n : Nat) {C : Ctx} {Ls : List STy} {e : List Instr} {P P' : Pcs}
    {st st' : STy} {σ : List Nat} {s : State} {o : Out}, WellTyped C F →
    Typed C Ls e P st P' st' → HiUpTo 0 P → σ.length = st.length →
    Eval F n (Ls.map List.length) e σ s o → StRel C s o.state ∧ Info Ls P' st' o := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro C Ls e P P' st st' σ s o hF ht hP hlen he
    cases he with
    | nil =>
      cases ht with
      | nil => exact ⟨StRel.refl _ _, hlen⟩
    | const v he' =>
      cases ht with
      | const _ ht' => exact ih _ (by omega) hF ht' hP (by simp [hlen]) he'
    | binop f he' =>
      cases ht with
      | binop _ ht' => exact ih _ (by omega) hF ht' hP (by simpa using hlen) he'
    | select he' =>
      cases ht with
      | select ht' => exact ih _ (by omega) hF ht' hP (by simpa using hlen) he'
    | drop he' =>
      cases ht with
      | drop ht' => exact ih _ (by omega) hF ht' hP (by simpa using hlen) he'
    | nop he' =>
      cases ht with
      | nop ht' => exact ih _ (by omega) hF ht' hP hlen he'
    | relabel he' =>
      cases ht with
      | relabel hf ht' => exact ih _ (by omega) hF ht' hP (hlen.trans hf.length_eq) he'
    | localGet i he' =>
      cases ht with
      | localGet _ ht' => exact ih _ (by omega) hF ht' hP (by simp [hlen]) he'
    | localSet i he' =>
      cases ht with
      | localSet _ hpc hl ht' =>
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF ht' hP (by simpa using hlen) he'
        exact ⟨(StRel.setLoc_high _ _ (hpc hP.head)).trans h1, h2⟩
    | globalGet i he' =>
      cases ht with
      | globalGet _ ht' => exact ih _ (by omega) hF ht' hP (by simp [hlen]) he'
    | globalSet i he' =>
      cases ht with
      | globalSet _ hpc hl ht' =>
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF ht' hP (by simpa using hlen) he'
        exact ⟨(StRel.setGlob_high _ _ (hpc hP.head)).trans h1, h2⟩
    | blockCont hvs hb hl hr =>
      cases ht with
      | block hfl hge hbody hrest =>
        have hpc := hP.head
        subst hpc
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) hF hbody (hiUpTo_zero_cons _) hvs hb
        obtain ⟨hlen1, hst1⟩ := lands_info hi1 hl
        have hfl' := hfl.length_eq
        have hbase : (_ ++ _ : List Nat).length = (_ ++ _ : STy).length := hlen
        simp only [List.length_append] at hbase
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF hrest (HiUpTo.sflows (rise hbody).tail hP)
          (by simp only [List.length_append]; omega) hr
        exact ⟨(hst1 ▸ hs1).trans h1, h2⟩
    | blockExit hvs hb hx =>
      cases ht with
      | block hfl hge hbody hrest =>
        have hpc := hP.head
        subst hpc
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) hF hbody (hiUpTo_zero_cons _) hvs hb
        obtain ⟨hst, _, hinfo⟩ := exits_info hi1 hx
        exact ⟨hst ▸ hs1, (hinfo _).mono (rise hrest)⟩
    | loopDone hvs hb hr =>
      cases ht with
      | loop hpc hp hfl hge hbody hrest =>
        have hpcL := hpc hP.head
        subst hpcL
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) hF hbody (hiUpTo_zero_cons _) hvs hb
        have hlen1 : (_ : List Nat).length = (_ : STy).length := hi1
        have hfl' := hfl.length_eq
        have hbase : (_ ++ _ : List Nat).length = (_ ++ _ : STy).length := hlen
        simp only [List.length_append] at hbase
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF hrest (HiUpTo.sflows (rise hbody).tail hP)
          (by simp only [List.length_append]; omega) hr
        exact ⟨hs1.trans h1, h2⟩
    | loopAgain hvs hb hr =>
      cases ht with
      | loop hpc hp hfl hge hbody hrest =>
        have hpcL := hpc hP.head
        subst hpcL
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) hF hbody (hiUpTo_zero_cons _) hvs hb
        obtain ⟨rs', hr1, _, hr3, _⟩ := hi1
        simp at hr1
        subst hr1
        have hfl' := hfl.length_eq
        have hbase : (_ ++ _ : List Nat).length = (_ ++ _ : STy).length := hlen
        simp only [List.length_append] at hbase
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF
          (Typed.loop hpc hp (SFlows.refl _) hge hbody hrest) hP
          (by simp only [List.length_append]; omega) hr
        exact ⟨hs1.trans h1, h2⟩
    | loopExit hvs hb hx =>
      cases ht with
      | loop hpc hp hfl hge hbody hrest =>
        have hpcL := hpc hP.head
        subst hpcL
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) hF hbody (hiUpTo_zero_cons _) hvs hb
        obtain ⟨hst, _, hinfo⟩ := exits_info hi1 hx
        exact ⟨hst ▸ hs1, (hinfo _).mono (rise hrest)⟩
    | iteCont hvs hb hl hr =>
      cases ht with
      | ite hfl hge h1 h2 hrest =>
        have hpc := hP.head
        subst hpc
        obtain ⟨p', Px, harm, hPx⟩ := arm_typed h1 h2 _
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) hF harm (by rw [Lab.H_join]; exact hiUpTo_zero_cons _) hvs hb
        obtain ⟨hlen1, hst1⟩ := lands_info hi1 hl
        have hfl' := hfl.length_eq
        have hbase : (_ :: (_ ++ _) : List Nat).length = (_ :: (_ ++ _) : STy).length := hlen
        simp only [List.length_append, List.length_cons] at hbase
        obtain ⟨h3, h4⟩ := ih _ (by omega) hF hrest
          (HiUpTo.sflows (sflows_joinEach (rise h1).tail (rise h2).tail).2.2 hP)
          (by simp only [List.length_append]; omega) hr
        exact ⟨(hst1 ▸ hs1).trans h3, h4⟩
    | iteExit hvs hb hx =>
      cases ht with
      | ite hfl hge h1 h2 hrest =>
        have hpc := hP.head
        subst hpc
        obtain ⟨p', Px, harm, hPx⟩ := arm_typed h1 h2 _
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) hF harm (by rw [Lab.H_join]; exact hiUpTo_zero_cons _) hvs hb
        obtain ⟨hst, _, hinfo⟩ := exits_info hi1 hx
        exact ⟨hst ▸ hs1, ((hinfo _).mono hPx).mono (rise hrest)⟩
    | br hn =>
      cases ht with
      | br hLs hge hfl =>
        have hpc := hP.head
        subst hpc
        have hn' := arity_eq hLs hn
        have hfl' := hfl.length_eq
        have hbase : _ = (_ ++ _ : STy).length := hlen
        simp only [List.length_append] at hbase
        refine ⟨StRel.refl _ _, _, hLs, hge, ?_, hiUpTo_raise _ _ _ (Nat.le_refl _)⟩
        simp only [List.length_take]; omega
    | brIfTaken hc hn =>
      cases ht with
      | brIf hLs hge hfl hrest =>
        have hpc := hP.head
        subst hpc
        have hn' := arity_eq hLs hn
        have hfl' := hfl.length_eq
        have hbase : (_ :: _ : List Nat).length = (_ :: (_ ++ _) : STy).length := hlen
        simp only [List.length_append, List.length_cons] at hbase
        rw [Lab.H_join] at hge hrest
        refine ⟨StRel.refl _ _, _, hLs, hge, ?_, ?_⟩
        · simp only [List.length_take]; omega
        · exact HiUpTo.sflows (rise hrest) (hiUpTo_raise _ _ _ (Nat.le_refl _))
    | brIfNot he' =>
      cases ht with
      | brIf hLs hge hfl hrest =>
        have hpc := hP.head
        subst hpc
        exact ih _ (by omega) hF hrest (hiUpTo_zero_raise _ _ _) (by simpa using hlen) he'
    | brTable hn =>
      cases ht with
      | brTable hall hge hfl =>
        have hpc := hP.head
        subst hpc
        obtain ⟨hLs, hk⟩ := hall _ (tableTarget_mem _ _ _)
        have hn' := arity_eq hLs hn
        have hfl' := hfl.length_eq
        have hbase : (_ :: _ : List Nat).length = (_ :: (_ ++ _) : STy).length := hlen
        simp only [List.length_append, List.length_cons] at hbase
        rw [Lab.H_join] at hge ⊢
        refine ⟨StRel.refl _ _, _, hLs, hge, ?_, hiUpTo_raise _ _ _ hk⟩
        simp only [List.length_take]; omega
    | call hf hargs hb hl hr =>
      cases ht with
      | call hft hpc hfl hrest =>
        obtain ⟨hty, P'', hbodyT⟩ := hF _ _ hf
        cases hft.symm.trans hty
        have hbound := hpc hP.head
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) (hF.enter _) hbodyT
          (by rw [hbound]; exact hiUpTo_zero_cons _) rfl hb
        obtain ⟨r', t', hl', hlen', hst', _⟩ := top_lands hi1
        rw [hl] at hl'
        cases hl'
        have hfl' := hfl.length_eq
        have hbase : (_ ++ _ : List Nat).length = (_ ++ _ : STy).length := hlen
        simp only [List.length_append] at hbase
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF hrest hP
          (by simp only [List.length_append]; omega) hr
        exact ⟨(StRel.call_conf (hst' ▸ hs1)).trans h1, h2⟩

/--
A loop whose body is typed under a secret pc, run from some iteration on. Either it reaches the
code after the loop, by a strictly smaller derivation, with the public variables as they were
and the loop's results on the stack; or it leaves by a branch past the loop.
-/
theorem loop_alone : ∀ (n : Nat) {C : Ctx} {Ls : List STy} {ps rs : STy} {body rest : List Instr}
    {Pb P1 : Pcs} {p : Lab} {σ vs base : List Nat} {s : State} {o : Out}, WellTyped C F →
    Typed C (ps :: Ls) body (Lab.H :: Pb) ps (p :: P1) rs → vs.length = ps.length →
    σ = vs ++ base →
    Eval F n (Ls.map List.length) (.loop ps rs body :: rest) σ s o →
    (∃ m σb s2, m < n ∧ σb.length = rs.length ∧ StRel C s s2 ∧
        Eval F m (Ls.map List.length) rest (σb ++ base) s2 o) ∨
      (StRel C s o.state ∧ o.isBr ∧ ∀ st, Info Ls P1 st o) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro C Ls ps rs body rest Pb P1 p σ vs base s o hF hbody hvs hσ he
    cases he with
    | loopDone hvs' hb hr =>
      obtain ⟨rfl, rfl⟩ := List.append_inj hσ (hvs'.trans hvs.symm)
      obtain ⟨hs1, hi1⟩ := confine _ hF hbody (hiUpTo_zero_cons _) hvs hb
      exact .inl ⟨_, _, _, by omega, hi1, hs1, hr⟩
    | loopAgain hvs' hb hr =>
      obtain ⟨rfl, rfl⟩ := List.append_inj hσ (hvs'.trans hvs.symm)
      obtain ⟨hs1, hi1⟩ := confine _ hF hbody (hiUpTo_zero_cons _) hvs hb
      obtain ⟨rs', hr1, _, hr3, _⟩ := hi1
      simp at hr1
      subst hr1
      rcases ih _ (by omega) hF hbody hr3 rfl hr with ⟨m, σb, s2, hm, hlen, hs2, he2⟩ | ⟨hs2, hbr, hinfo⟩
      · exact .inl ⟨m, σb, s2, by omega, hlen, hs1.trans hs2, he2⟩
      · exact .inr ⟨hs1.trans hs2, hbr, hinfo⟩
    | loopExit hvs' hb hx =>
      obtain ⟨rfl, rfl⟩ := List.append_inj hσ (hvs'.trans hvs.symm)
      obtain ⟨hs1, hi1⟩ := confine _ hF hbody (hiUpTo_zero_cons _) hvs hb
      obtain ⟨hst, hbr, hinfo⟩ := exits_info hi1 hx
      exact .inr ⟨hst ▸ hs1, hbr, hinfo⟩

end WasmIfc
