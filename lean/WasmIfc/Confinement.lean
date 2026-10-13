/-
One run under a secret pc: it changes nothing the attacker sees but the preserved globals, and
it leaves by a branch only to a label whose type is all secret (`confine`). The iterations of
a loop whose body is typed under a secret pc are such a run, although the loop itself may be
entered under a public pc.
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
  | exn t w s => exact False.elim h

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
  | exn t w s => exact False.elim h

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
  | exn t w s => exact False.elim h

/-- The arm a condition selects is typed, and ends below the join of the two arms' pc stacks. -/
theorem arm_typed {C : Ctx} {Ls : List STy} {thn els : List Instr} {pcl pc p1 p2 : Lab}
    {Pr P1 P2 : Pcs} {ps rs : STy}
    (h1 : Typed C (rs :: Ls) thn (pcl :: pc :: Pr) ps (p1 :: P1) rs)
    (h2 : Typed C (rs :: Ls) els (pcl :: pc :: Pr) ps (p2 :: P2) rs) (c : Nat) :
    ∃ p' P', Typed C (rs :: Ls) (if c = 0 then els else thn) (pcl :: pc :: Pr) ps (p' :: P') rs ∧
      SFlows P' (joinEach P1 P2) ∧ Lab.le p' (p1.join p2) := by
  have hj := sflows_joinEach (rise h1).tail (rise h2).tail
  by_cases hc : c = 0
  · exact ⟨p2, P2, by simpa [hc] using h2, hj.2.1, Lab.le_join_right _ _⟩
  · exact ⟨p1, P1, by simpa [hc] using h1, hj.1, Lab.le_join_left _ _⟩

/--
Confinement. A typed sequence that starts under a secret pc leaves the public variables as
they were, except the preserved globals, and its outcome is as `Info` describes. In
particular it does not end by an exception.
-/
theorem confine : ∀ (n : Nat) {C : Ctx} {Ls : List STy} {e : List Instr} {P P' : Pcs}
    {st st' : STy} {σ : List Nat} {s : State} {o : Out}, WellTyped C F →
    Typed C Ls e P st P' st' → HiUpTo 0 P → σ.length = st.length →
    Eval F n (Ls.map List.length) e σ s o → Conf C s o.state ∧ Info Ls P' st' o := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro C Ls e P P' st st' σ s o hF ht hP hlen he
    cases he with
    | nil =>
      cases ht with
      | nil => exact ⟨Conf.refl _ _, hlen⟩
    | const v he' =>
      cases ht with
      | const _ ht' => exact ih _ (by omega) hF ht' hP (by simp [hlen]) he'
    | binop f he' =>
      cases ht with
      | binop _ ht' => exact ih _ (by omega) hF ht' hP (by simpa using hlen) he'
    | unop f he' =>
      cases ht with
      | unop _ ht' => exact ih _ (by omega) hF ht' hP (by simpa using hlen) he'
    | dup he' =>
      cases ht with
      | dup ht' => exact ih _ (by omega) hF ht' hP (by simpa using hlen) he'
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
        exact ⟨(Conf.setLoc_high _ _ (hpc hP.head)).trans h1, h2⟩
    | localTee i he' =>
      cases ht with
      | localTee _ hpc hl ht' =>
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF ht' hP hlen he'
        exact ⟨(Conf.setLoc_high _ _ (hpc hP.head)).trans h1, h2⟩
    | globalGet i he' =>
      cases ht with
      | globalGet _ ht' => exact ih _ (by omega) hF ht' hP (by simp [hlen]) he'
    | globalSet i he' =>
      cases ht with
      | globalSet _ hnp hpc hl ht' =>
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF ht' hP (by simpa using hlen) he'
        exact ⟨(Conf.setGlob_high _ _ (hpc hP.head)).trans h1, h2⟩
      | globalSetPreserved _ hpi hl ht' =>
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF ht' hP (by simpa using hlen) he'
        exact ⟨(Conf.setGlob_preserved _ _ hpi).trans h1, h2⟩
    | fill lm hb he' =>
      cases ht with
      | fill _ hle ht' =>
        have hpc := hP.head
        subst hpc
        have hlm := hle (Lab.H_join _)
        subst hlm
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF ht' (hiUpTo_zero_cons _) (by simpa using hlen) he'
        exact ⟨(Conf.fill_high _ _ _ _ _).trans h1, h2⟩
    | copy lm hb hb' he' =>
      cases ht with
      | copy _ hle ht' =>
        have hpc := hP.head
        subst hpc
        have hlm := hle (Lab.H_join _)
        subst hlm
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF ht' (hiUpTo_zero_cons _) (by simpa using hlen) he'
        exact ⟨(Conf.copy_high _ _ _ _ _).trans h1, h2⟩
    | tableGet he' =>
      cases ht with
      | tableGet ht' => exact ih _ (by omega) hF ht' hP (by simpa using hlen) he'
    | tableSet he' =>
      cases ht with
      | tableSet hle ht' =>
        have hpc := hP.head
        subst hpc
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF ht' (hiUpTo_zero_cons _) (by simpa using hlen) he'
        exact ⟨(Conf.setTbl_high _ _ _ (hle (Lab.H_join _))).trans h1, h2⟩
    | hostRead hb hb' he' =>
      cases ht with
      | hostRead _ => exact absurd hP.head (by decide)
    | hostWrite hb hchk he' =>
      cases ht with
      | hostWrite _ => exact absurd hP.head (by decide)
    | memSize he' =>
      cases ht with
      | memSize ht' => exact ih _ (by omega) hF ht' hP (by simp [hlen]) he'
    | memGrow he' =>
      cases ht with
      | memGrow hle ht' =>
        have hpc := hP.head
        subst hpc
        exact absurd (hle (Lab.H_join _)) (by decide)
    | load lm hsz hlab he' =>
      cases ht with
      | load _ ht' => exact ih _ (by omega) hF ht' hP (by simpa using hlen) he'
    | store lm hsz he' =>
      cases ht with
      | store _ hle ht' =>
        have hpc := hP.head
        subst hpc
        have hlm := hle (by rw [Lab.H_join, Lab.H_join])
        subst hlm
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF ht' (hiUpTo_zero_cons _) (by simpa using hlen) he'
        exact ⟨(Conf.setMem_high _ _ _ _).trans h1, h2⟩
    | blockCont hvs hb hl hk hr =>
      cases ht with
      | block hfl hge hres hbody hrest =>
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
      | block hfl hge hres hbody hrest =>
        have hpc := hP.head
        subst hpc
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) hF hbody (hiUpTo_zero_cons _) hvs hb
        obtain ⟨hst, _, hinfo⟩ := exits_info hi1 hx
        exact ⟨hst ▸ hs1, (hinfo _).mono (rise hrest)⟩
    | loopCont hvs hb hl hk hr =>
      cases ht with
      | loop hpc hp hfl hge hres hbody hrest =>
        have hpcL := hpc hP.head
        subst hpcL
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) hF (Typed.iter hp hge hbody) (hiUpTo_zero_cons _) hvs hb
        obtain ⟨hlen1, hst1⟩ := lands_info hi1 hl
        have hfl' := hfl.length_eq
        have hbase : (_ ++ _ : List Nat).length = (_ ++ _ : STy).length := hlen
        simp only [List.length_append] at hbase
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF hrest (HiUpTo.sflows (rise hbody).tail hP)
          (by simp only [List.length_append]; omega) hr
        exact ⟨(hst1 ▸ hs1).trans h1, h2⟩
    | loopExit hvs hb hx =>
      cases ht with
      | loop hpc hp hfl hge hres hbody hrest =>
        have hpcL := hpc hP.head
        subst hpcL
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) hF (Typed.iter hp hge hbody) (hiUpTo_zero_cons _) hvs hb
        obtain ⟨hst, _, hinfo⟩ := exits_info hi1 hx
        exact ⟨hst ▸ hs1, (hinfo _).mono (rise hrest)⟩
    | iterDone hb =>
      cases ht with
      | iter hp hge hbody =>
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) hF hbody hP hlen hb
        exact ⟨hs1, hi1⟩
    | iterAgain hb hr =>
      cases ht with
      | iter hp hge hbody =>
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) hF hbody hP hlen hb
        obtain ⟨rs', hr1, _, hr3, _⟩ := hi1
        simp at hr1
        subst hr1
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF (Typed.iter hp hge hbody) hP hr3 hr
        exact ⟨hs1.trans h1, h2⟩
    | iterExit hb =>
      cases ht with
      | iter hp hge hbody =>
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) hF hbody hP hlen hb
        obtain ⟨rs', hr1, hr2, hr3, hr4⟩ := hi1
        exact ⟨hs1, rs', by simpa using hr1, hr2, hr3,
          HiUpTo.sflows (.cons hp (SFlows.refl _)) hr4⟩
    | iterExn hb =>
      cases ht with
      | iter hp hge hbody => exact False.elim (ih _ (by omega) hF hbody hP hlen hb).2
    | throw =>
      cases ht with
      | throw _ _ _ => exact absurd hP.head (by decide)
    | tryCont hvs hb hl hk hr =>
      cases ht with
      | tryTable _ _ _ _ _ => exact absurd hP.head (by decide)
    | tryExit hvs hb hx =>
      cases ht with
      | tryTable _ _ _ _ _ => exact absurd hP.head (by decide)
    | retCall hf hargs hb hl hk =>
      cases ht with
      | retCall hft hpc hfl hLs hge hres =>
        obtain ⟨hty, P'', hbodyT, _⟩ := hF _ _ hf
        cases hft.symm.trans hty
        have hpcH := hP.head
        subst hpcH
        have hbound := hpc rfl
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) (hF.enter _) hbodyT
          (by rw [hbound]; exact hiUpTo_zero_cons _) rfl hb
        obtain ⟨r', t', hl', hlen', hst', _⟩ := top_lands hi1
        rw [hl] at hl'
        cases hl'
        simp only [List.length_map]
        exact ⟨Conf.call (hst' ▸ hs1), _, hLs, hge, hlen'.trans hres.length_eq,
          hiUpTo_raise _ _ _ (Nat.le_refl _)⟩
    | retCallExn hf hargs hb =>
      cases ht with
      | retCall hft hpc hfl hLs hge hres =>
        obtain ⟨hty, P'', hbodyT, _⟩ := hF _ _ hf
        cases hft.symm.trans hty
        have hbound := hpc hP.head
        exact False.elim (ih _ (by omega) (hF.enter _) hbodyT
          (by rw [hbound]; exact hiUpTo_zero_cons _) rfl hb).2
    | callExn hf hargs hb =>
      cases ht with
      | call hft hpc hfl hrest =>
        obtain ⟨hty, P'', hbodyT, _⟩ := hF _ _ hf
        cases hft.symm.trans hty
        have hbound := hpc hP.head
        exact False.elim (ih _ (by omega) (hF.enter _) hbodyT
          (by rw [hbound]; exact hiUpTo_zero_cons _) rfl hb).2
    | callIndirectExn htbl hf hty hargs hb =>
      cases ht with
      | callIndirect hpc hge hfl hrest =>
        obtain ⟨_, P'', hbodyT, _⟩ := hF _ _ hf
        rw [hty] at hbodyT
        have hpcH := hP.head
        subst hpcH
        have hbound := hpc (Lab.H_join _)
        subst hbound
        exact False.elim (ih _ (by omega) (hF.enter _) hbodyT (hiUpTo_zero_cons _) rfl hb).2
    | callRef href hf hty hargs hb hl hk hr =>
      cases ht with
      | callRef hpc hge hfl hrest =>
        obtain ⟨_, P'', hbodyT, _⟩ := hF _ _ hf
        rw [hty] at hbodyT
        have hpcH := hP.head
        subst hpcH
        have hbound := hpc (Lab.H_join _)
        subst hbound
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) (hF.enter _) hbodyT (hiUpTo_zero_cons _) rfl hb
        obtain ⟨r', t', hl', hlen', hst', _⟩ := top_lands hi1
        dsimp only at hlen'
        rw [hl] at hl'
        cases hl'
        have hfl' := hfl.length_eq
        have hbase : (_ :: (_ ++ _) : List Nat).length = (_ :: (_ ++ _) : STy).length := hlen
        simp only [List.length_append, List.length_cons] at hbase
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF hrest hP
          (by simp only [List.length_append]; omega) hr
        exact ⟨(Conf.call (hst' ▸ hs1)).trans h1, h2⟩
    | callRefExn href hf hty hargs hb =>
      cases ht with
      | callRef hpc hge hfl hrest =>
        obtain ⟨_, P'', hbodyT, _⟩ := hF _ _ hf
        rw [hty] at hbodyT
        have hpcH := hP.head
        subst hpcH
        have hbound := hpc (Lab.H_join _)
        subst hbound
        exact False.elim (ih _ (by omega) (hF.enter _) hbodyT (hiUpTo_zero_cons _) rfl hb).2
    | iteCont hvs hb hl hk hr =>
      cases ht with
      | ite hfl hge hres h1 h2 hrest =>
        have hpc := hP.head
        subst hpc
        obtain ⟨p', Px, harm, hPx, _⟩ := arm_typed h1 h2 _
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
      | ite hfl hge hres h1 h2 hrest =>
        have hpc := hP.head
        subst hpc
        obtain ⟨p', Px, harm, hPx, _⟩ := arm_typed h1 h2 _
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
        refine ⟨Conf.refl _ _, _, hLs, hge, ?_, hiUpTo_raise _ _ _ (Nat.le_refl _)⟩
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
        refine ⟨Conf.refl _ _, _, hLs, hge, ?_, ?_⟩
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
        refine ⟨Conf.refl _ _, _, hLs, hge, ?_, hiUpTo_raise _ _ _ hk⟩
        simp only [List.length_take]; omega
    | ret hn =>
      cases ht with
      | ret hLs hge hfl =>
        have hpc := hP.head
        subst hpc
        simp only [List.length_map] at hn ⊢
        have hn' := arity_eq hLs hn
        have hfl' := hfl.length_eq
        have hbase : _ = (_ ++ _ : STy).length := hlen
        simp only [List.length_append] at hbase
        refine ⟨Conf.refl _ _, _, hLs, hge, ?_, hiUpTo_raise _ _ _ (Nat.le_refl _)⟩
        simp only [List.length_take]; omega
    | call hf hargs hb hl hk hr =>
      cases ht with
      | call hft hpc hfl hrest =>
        obtain ⟨hty, P'', hbodyT, _⟩ := hF _ _ hf
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
        exact ⟨(Conf.call (hst' ▸ hs1)).trans h1, h2⟩
    | callIndirect htbl hf hty hargs hb hl hk hr =>
      cases ht with
      | callIndirect hpc hge hfl hrest =>
        obtain ⟨_, P'', hbodyT, _⟩ := hF _ _ hf
        rw [hty] at hbodyT
        have hpcH := hP.head
        subst hpcH
        have hbound := hpc (Lab.H_join _)
        subst hbound
        obtain ⟨hs1, hi1⟩ := ih _ (by omega) (hF.enter _) hbodyT (hiUpTo_zero_cons _) rfl hb
        obtain ⟨r', t', hl', hlen', hst', _⟩ := top_lands hi1
        dsimp only at hlen'
        rw [hl] at hl'
        cases hl'
        have hfl' := hfl.length_eq
        have hbase : (_ :: (_ ++ _) : List Nat).length = (_ :: (_ ++ _) : STy).length := hlen
        simp only [List.length_append, List.length_cons] at hbase
        obtain ⟨h1, h2⟩ := ih _ (by omega) hF hrest hP
          (by simp only [List.length_append]; omega) hr
        exact ⟨(Conf.call (hst' ▸ hs1)).trans h1, h2⟩

end WasmIfc
