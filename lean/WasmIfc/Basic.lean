/-
Relations between two runs, and the facts about levels, type stacks and pc stacks that the
proofs use.
-/
import WasmIfc.Defs

namespace WasmIfc

namespace Lab

theorem le_refl (a : Lab) : le a a := fun h => h

theorem le_trans {a b c : Lab} (h1 : le a b) (h2 : le b c) : le a c := fun h => h2 (h1 h)

theorem le_join_left (a b : Lab) : le a (a.join b) := by
  cases a <;> cases b <;> simp [le, join]

theorem le_join_right (a b : Lab) : le b (a.join b) := by
  cases a <;> cases b <;> simp [le, join]

theorem H_join (b : Lab) : H.join b = H := by cases b <;> rfl

theorem join_H (a : Lab) : a.join H = H := by cases a <;> rfl

theorem join_eq_L {a b : Lab} (h : a.join b = L) : a = L ∧ b = L := by
  cases a <;> cases b <;> simp_all [join]

theorem eq_L_of_ne_H {a : Lab} (h : a ≠ H) : a = L := by
  cases a <;> simp_all

/--
Two table indices that agree if their level is public: they agree and the table is public, or
whatever depends on the index and the table is secret.
-/
theorem table_cases {l : Lab} (lt : Lab) {c0 c1 : Nat} (hc : l = L → c0 = c1) :
    (c0 = c1 ∧ lt = L) ∨ ∀ x : Lab, x.join (l.join lt) = H := by
  cases l <;> cases lt
  · exact .inl ⟨hc rfl, rfl⟩
  · exact .inr (fun x => by cases x <;> rfl)
  · exact .inr (fun x => by cases x <;> rfl)
  · exact .inr (fun x => by cases x <;> rfl)

/-- A level that something public flows from need not be public; one that flows to public is. -/
theorem eq_L_of_le {a b : Lab} (h : le a b) (hb : b = L) : a = L := by
  cases a <;> cases b <;> simp_all [le]

end Lab

/-! ### Pointwise order -/

theorem SFlows.refl : ∀ s : List Lab, SFlows s s
  | [] => .nil
  | a :: s => .cons (Lab.le_refl a) (SFlows.refl s)

theorem SFlows.trans {s t u : List Lab} (h1 : SFlows s t) (h2 : SFlows t u) : SFlows s u := by
  induction h1 generalizing u with
  | nil => cases h2; exact .nil
  | cons hab _ ih =>
    cases h2 with
    | cons hbc h2' => exact .cons (Lab.le_trans hab hbc) (ih h2')

theorem SFlows.length_eq {s t : List Lab} (h : SFlows s t) : s.length = t.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem SFlows.tail {a b : Lab} {s t : List Lab} (h : SFlows (a :: s) (b :: t)) : SFlows s t := by
  cases h with
  | cons _ h' => exact h'

theorem SFlows.head {a b : Lab} {s t : List Lab} (h : SFlows (a :: s) (b :: t)) : Lab.le a b := by
  cases h with
  | cons h' _ => exact h'

theorem sflows_raise (a : Lab) : ∀ (P : Pcs) (i : Nat), SFlows P (raise a P i)
  | [], _ => .nil
  | p :: ps, 0 => .cons (Lab.le_join_right a p) (SFlows.refl ps)
  | p :: ps, i + 1 => .cons (Lab.le_join_right a p) (sflows_raise a ps i)

/-- Two pc stacks above a common one are below their entrywise join, and so is the common one. -/
theorem sflows_joinEach {a b c : List Lab} (h1 : SFlows a b) (h2 : SFlows a c) :
    SFlows b (joinEach b c) ∧ SFlows c (joinEach b c) ∧ SFlows a (joinEach b c) := by
  induction h1 generalizing c with
  | nil => cases h2; exact ⟨.nil, .nil, .nil⟩
  | cons hab _ ih =>
    cases h2 with
    | cons hac h2' =>
      obtain ⟨i1, i2, i3⟩ := ih h2'
      exact ⟨.cons (Lab.le_join_left _ _) i1, .cons (Lab.le_join_right _ _) i2,
        .cons (Lab.le_trans hab (Lab.le_join_left _ _)) i3⟩

/-! ### Secret pcs -/

/-- The entries `0` to `i` of a pc stack, as far as it has them, are secret. -/
def HiUpTo (i : Nat) (P : Pcs) : Prop := ∀ k p, k ≤ i → P[k]? = some p → p = Lab.H

theorem HiUpTo.mono {i j : Nat} {P : Pcs} (hji : j ≤ i) (h : HiUpTo i P) : HiUpTo j P :=
  fun k p hk hp => h k p (Nat.le_trans hk hji) hp

theorem HiUpTo.head {i : Nat} {p : Lab} {P : Pcs} (h : HiUpTo i (p :: P)) : p = Lab.H :=
  h 0 p (Nat.zero_le _) (by simp)

theorem HiUpTo.tail {i : Nat} {p : Lab} {P : Pcs} (h : HiUpTo (i + 1) (p :: P)) : HiUpTo i P :=
  fun k q hk hq => h (k + 1) q (by omega) (by simpa using hq)

theorem HiUpTo.cons {i : Nat} {P : Pcs} (h : HiUpTo i P) : HiUpTo (i + 1) (Lab.H :: P) := by
  intro k p hk hp
  cases k with
  | zero => simpa using hp.symm
  | succ k => exact h k p (by omega) (by simpa using hp)

theorem HiUpTo.sflows {P P' : Pcs} (hf : SFlows P P') : ∀ {i : Nat}, HiUpTo i P → HiUpTo i P' := by
  induction hf with
  | nil => intro i h; exact h
  | cons hab _ ih =>
    intro i h k p hk hp
    cases k with
    | zero =>
      rename_i a b s t _
      have hb : b = p := by simpa using hp
      subst hb
      exact hab (h 0 a (Nat.zero_le _) (by simp))
    | succ k =>
      cases i with
      | zero => omega
      | succ i => exact ih (HiUpTo.tail h) k p (by omega) (by simpa using hp)

theorem hiUpTo_raise : ∀ (P : Pcs) (i j : Nat), i ≤ j → HiUpTo i (raise Lab.H P j)
  | [], _, j, _ => by intro k p _ hp; cases j <;> simp [raise] at hp
  | q :: P, i, 0, hij => by
      intro k p hk hp
      have hk0 : k = 0 := by omega
      subst hk0
      simpa [raise, Lab.H_join] using hp.symm
  | q :: P, i, j + 1, hij => by
      intro k p hk hp
      cases k with
      | zero => simpa [raise, Lab.H_join] using hp.symm
      | succ k =>
        have hp' : (raise Lab.H P j)[k]? = some p := by simpa [raise] using hp
        exact hiUpTo_raise P (i - 1) j (by omega) k p (by omega) hp'

theorem raise_cons (a p : Lab) (P : Pcs) (i : Nat) : ∃ P', raise a (p :: P) i = a.join p :: P' := by
  cases i <;> exact ⟨_, rfl⟩

/-- If the pc does not drop after a construct that ends under a secret pc, the pc after it is secret. -/
theorem hiUpTo_of_noDrop {pcEnd : Lab} {after : Pcs}
    (h : ∀ q, after.head? = some q → Lab.le pcEnd q) (hp : pcEnd = Lab.H) : HiUpTo 0 after := by
  intro k p hk hkp
  have hk0 : k = 0 := by omega
  subst hk0
  exact h p (by rw [List.head?_eq_getElem?]; exact hkp) hp

/-! ### Two stacks that agree where the type is public -/

/-- `StkRel st σ0 σ1`: the stacks have the shape of `st` and hold equal values at its public positions. -/
inductive StkRel : STy → List Nat → List Nat → Prop where
  | nil : StkRel [] [] []
  | cons {l : Lab} {v0 v1 : Nat} {st : STy} {σ0 σ1 : List Nat} :
      (l = Lab.L → v0 = v1) → StkRel st σ0 σ1 → StkRel (l :: st) (v0 :: σ0) (v1 :: σ1)

theorem StkRel.length_left {st : STy} {a b : List Nat} (h : StkRel st a b) : a.length = st.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem StkRel.length_right {st : STy} {a b : List Nat} (h : StkRel st a b) : b.length = st.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem StkRel.symm {st : STy} {a b : List Nat} (h : StkRel st a b) : StkRel st b a := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih => exact .cons (fun hl => (hv hl).symm) ih

theorem StkRel.mono {st st' : STy} {a b : List Nat} (hf : SFlows st st') (h : StkRel st a b) :
    StkRel st' a b := by
  induction hf generalizing a b with
  | nil => exact h
  | cons hab _ ih =>
    cases h with
    | cons hv h' => exact .cons (fun hl => hv (Lab.eq_L_of_le hab hl)) (ih h')

theorem StkRel.append {s t : STy} {a b c d : List Nat} (h1 : StkRel s a b) (h2 : StkRel t c d) :
    StkRel (s ++ t) (a ++ c) (b ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons hv _ ih => exact .cons hv ih

theorem StkRel.split : ∀ {s t : STy} {a b c d : List Nat}, StkRel (s ++ t) (a ++ c) (b ++ d) →
    a.length = s.length → b.length = s.length → StkRel s a b ∧ StkRel t c d
  | [], _, [], [], _, _, h, _, _ => ⟨.nil, h⟩
  | l :: s, _, x :: a, y :: b, _, _, h, ha, hb => by
      cases h with
      | cons hv h' =>
        obtain ⟨h1, h2⟩ := StkRel.split h' (by simpa using ha) (by simpa using hb)
        exact ⟨.cons hv h1, h2⟩
  | [], _, _ :: _, _, _, _, _, ha, _ => by simp at ha
  | [], _, [], _ :: _, _, _, _, _, hb => by simp at hb
  | _ :: _, _, [], _, _, _, _, ha, _ => by simp at ha
  | _ :: _, _, _ :: _, [], _, _, _, _, hb => by simp at hb

theorem StkRel.take : ∀ {s t : STy} {a b : List Nat}, StkRel (s ++ t) a b →
    StkRel s (a.take s.length) (b.take s.length)
  | [], _, _, _, _ => by simpa using StkRel.nil
  | l :: s, _, _, _, h => by
      cases h with
      | cons hv h' => simpa using StkRel.cons hv (StkRel.take h')

theorem StkRel.of_allH : ∀ {st : STy} {a b : List Nat}, AllGe Lab.H st →
    a.length = st.length → b.length = st.length → StkRel st a b
  | [], [], [], _, _, _ => .nil
  | l :: st, x :: a, y :: b, h, ha, hb => by
      refine .cons (fun hl => ?_) (StkRel.of_allH (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
        (by simpa using ha) (by simpa using hb))
      have : l = Lab.H := h l (List.mem_cons_self) rfl
      simp_all
  | [], _ :: _, _, _, ha, _ => by simp at ha
  | [], [], _ :: _, _, _, hb => by simp at hb
  | _ :: _, [], _, _, ha, _ => by simp at ha
  | _ :: _, _ :: _, [], _, _, hb => by simp at hb

/-- Values at public types agree in two related stacks. -/
theorem StkRel.take_public : ∀ {args st : STy} {a b : List Nat},
    (∀ l, l ∈ args → l = Lab.L) → StkRel (args ++ st) a b →
    a.take args.length = b.take args.length
  | [], _, _, _, _, _ => by simp
  | l :: args, _, _, _, hall, h => by
      cases h with
      | cons hv h' =>
        have ih := StkRel.take_public (fun l' hl' => hall l' (List.mem_cons_of_mem _ hl')) h'
        simp [hv (hall l List.mem_cons_self), ih]

/-- A stack is related to itself at any type of its shape. -/
theorem StkRel.same : ∀ {st : STy} {w : List Nat}, w.length = st.length → StkRel st w w
  | [], [], _ => .nil
  | _ :: _, _ :: _, h => .cons (fun _ => rfl) (StkRel.same (by simpa using h))
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-! ### Two states that agree where public, and one state after a run under a secret pc -/

/--
The data segments of two runs: one that both still have is the same in both. A run may have
dropped a segment under a secret pc, so one of the two may be empty where the other is not;
`memory.init` then traps in that run unless it asks for no byte.
-/
def SegRel (s t : State) : Prop := ∀ k, s.segs k = t.segs k ∨ s.segs k = [] ∨ t.segs k = []

/--
What the attacker sees of the host: the levels of the descriptors, and for a public descriptor
what was written to it and what is left to read from it.
-/
def IoRel (s t : State) : Prop :=
  s.chan = t.chan ∧ (∀ d, s.chan d = Lab.L → s.out d = t.out d ∧ s.inp d = t.inp d) ∧
    SegRel s t

theorem IoRel.symm {s t : State} (h : IoRel s t) : IoRel t s :=
  ⟨h.1.symm, fun d hd => ⟨(h.2.1 d (h.1 ▸ hd)).1.symm, (h.2.1 d (h.1 ▸ hd)).2.symm⟩,
    fun k => (h.2.2 k).elim (fun e => .inl e.symm)
      (fun e => e.elim (fun a => .inr (.inr a)) (fun b => .inr (.inl b)))⟩

/-- A run under a secret pc makes no host call. It may drop data segments. -/
def IoSame (s t : State) : Prop :=
  s.chan = t.chan ∧ s.out = t.out ∧ s.inp = t.inp ∧ ∀ k, t.segs k = s.segs k ∨ t.segs k = []

theorem IoSame.refl (s : State) : IoSame s s := ⟨rfl, rfl, rfl, fun _ => .inl rfl⟩

theorem IoSame.trans {s t u : State} (h1 : IoSame s t) (h2 : IoSame t u) : IoSame s u :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1,
    fun k => (h2.2.2.2 k).elim
      (fun e => (h1.2.2.2 k).elim (fun e1 => .inl (e.trans e1)) (fun e1 => .inr (e.trans e1))) .inr⟩

theorem IoRel.conf_left {s s' t : State} (h : IoRel s t) (hc : IoSame s s') : IoRel s' t := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  refine ⟨h1.symm.trans h.1, fun d hd => by rw [← h2, ← h3]; exact h.2.1 d (h1 ▸ hd), fun k => ?_⟩
  rcases h4 k with e | e
  · rw [e]; exact h.2.2 k
  · exact .inr (.inl e)

/-- The second memory in two runs: as the first, a cell that is public in both holds the same. -/
def Mem2Rel (s t : State) : Prop :=
  (∀ a, s.lab2 a = Lab.L → t.lab2 a = Lab.L → s.mem2 a = t.mem2 a) ∧ s.size2 = t.size2

/-- The second memory after a run under a secret pc: as the first. -/
def Mem2Conf (s t : State) : Prop :=
  (∀ a, t.lab2 a = Lab.L → s.lab2 a = Lab.L ∧ s.mem2 a = t.mem2 a) ∧ s.size2 = t.size2

theorem Mem2Conf.refl (s : State) : Mem2Conf s s := ⟨fun _ h => ⟨h, rfl⟩, rfl⟩

theorem Mem2Conf.trans {s t u : State} (h1 : Mem2Conf s t) (h2 : Mem2Conf t u) : Mem2Conf s u :=
  ⟨fun a ha => ⟨(h1.1 a (h2.1 a ha).1).1, ((h1.1 a (h2.1 a ha).1).2).trans (h2.1 a ha).2⟩,
    h1.2.trans h2.2⟩

theorem Mem2Rel.symm {s t : State} (h : Mem2Rel s t) : Mem2Rel t s :=
  ⟨fun a ha hb => (h.1 a hb ha).symm, h.2.symm⟩

theorem Mem2Rel.conf_left {s s' t : State} (h : Mem2Rel s t) (hc : Mem2Conf s s') : Mem2Rel s' t :=
  ⟨fun a ha hb => (hc.1 a ha).2.symm.trans (h.1 a (hc.1 a ha).1 hb), hc.2.symm.trans h.2⟩

/--
What two runs' states share whatever the levels, and the second memory: the limit on the
memory, the exceptions kept for references, which are as their tags say, the descriptor table
and the names of the files in every directory. A reference to an exception is made, and a
file is opened, only under a public pc.
-/
def Limits (C : Ctx) (s t : State) : Prop :=
  s.cap = t.cap ∧ s.exns = t.exns ∧ ExnOk C s ∧ Mem2Rel s t ∧ s.sameHost t

theorem Limits.symm {C : Ctx} {s t : State} (h : Limits C s t) : Limits C t s :=
  ⟨h.1.symm, h.2.1.symm, fun e he => h.2.2.1 e (by rw [h.2.1]; exact he), h.2.2.2.1.symm,
    h.2.2.2.2.symm⟩

theorem Limits.conf_left {C : Ctx} {s s' t : State} (h : Limits C s t)
    (hc : s.cap = s'.cap ∧ s.exns = s'.exns ∧ Mem2Conf s s' ∧ s.sameHost s') : Limits C s' t :=
  ⟨hc.1.symm.trans h.1, hc.2.1.symm.trans h.2.1, fun e he => h.2.2.1 e (by rw [hc.2.1]; exact he),
    h.2.2.2.1.conf_left hc.2.2.1, hc.2.2.2.symm.trans h.2.2.2.2⟩

/--
`StRel C s t`: two runs' states agree on the public variables and on the memory cells that are
public in both. A cell that is secret in one of them is not compared: a load that declares it
public traps in that run. The preserved globals are not compared here: they agree only where
the pc is public (`PresOr`).
-/
def StRel (C : Ctx) (s t : State) : Prop :=
  (∀ i, C.locals i = Lab.L → s.loc i = t.loc i) ∧
    (∀ i, C.globals i = Lab.L → ¬ C.preserved i → s.glob i = t.glob i) ∧
    (∀ a, s.lab a = Lab.L → t.lab a = Lab.L → s.mem a = t.mem a) ∧
    (C.table = Lab.L → s.sameTable t) ∧ s.size = t.size ∧ Limits C s t ∧ IoRel s t

theorem StRel.symm {C : Ctx} {s t : State} (h : StRel C s t) : StRel C t s :=
  ⟨fun i hi => (h.1 i hi).symm, fun i hi hn => (h.2.1 i hi hn).symm,
    fun a ha hb => (h.2.2.1 a hb ha).symm, fun hl => (h.2.2.2.1 hl).symm, h.2.2.2.2.1.symm,
    h.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.symm⟩

/-- The two runs' states agree on the preserved globals. -/
def PresEq (C : Ctx) (s t : State) : Prop := ∀ i, C.preserved i → s.glob i = t.glob i

/--
`PresOr C i P s t`: the two runs' states agree on the preserved globals, unless the entries `0`
to `i` of the pc stack are secret. Under a secret pc a run may have written a preserved global.
-/
def PresOr (C : Ctx) (i : Nat) (P : Pcs) (s t : State) : Prop := PresEq C s t ∨ HiUpTo i P

theorem PresOr.mono {C : Ctx} {i : Nat} {P P' : Pcs} {s t : State} (hf : SFlows P P')
    (h : PresOr C i P s t) : PresOr C i P' s t :=
  h.imp id (HiUpTo.sflows hf)

/-- States with the same globals as two related ones. -/
theorem PresOr.of_glob {C : Ctx} {i : Nat} {P : Pcs} {s t s' t' : State} (hs : s'.glob = s.glob)
    (ht : t'.glob = t.glob) (h : PresOr C i P s t) : PresOr C i P s' t' :=
  h.imp (fun hp j hj => by rw [hs, ht]; exact hp j hj) id

/-- A branch under the pc `pc` raises the pcs it leaves by at least `pc`. -/
theorem PresOr.br {C : Ctx} {pc a : Lab} {Pr : Pcs} {s t : State} {i k : Nat} (hik : i ≤ k)
    (ha : Lab.le pc a) (h : PresOr C 0 (pc :: Pr) s t) : PresOr C i (raise a (pc :: Pr) k) s t := by
  rcases h with h | h
  · exact .inl h
  · have hpc := h.head
    subst hpc
    have haH := ha rfl
    subst haH
    exact .inr (hiUpTo_raise _ _ _ hik)

theorem PresEq.setGlob {C : Ctx} {s t : State} {i v0 v1 : Nat} (hv : C.preserved i → v0 = v1)
    (h : PresEq C s t) : PresEq C (s.setGlob i v0) (t.setGlob i v1) := by
  intro j hj
  by_cases hji : j = i
  · subst hji; simp [State.setGlob, hv hj]
  · simp [State.setGlob, hji, h j hj]

/--
`Conf C s t`: `t` is what a run under a secret pc may make of `s`. The public variables are as
they were, except the preserved globals, which it may have written. A cell that is public in
`t` was public in `s` and has its value; a cell may have become secret. (SecWasm's Definition 6, with the convention (C5) of the paper's appendix.)
-/
def Conf (C : Ctx) (s t : State) : Prop :=
  (∀ i, C.locals i = Lab.L → s.loc i = t.loc i) ∧
    (∀ i, C.globals i = Lab.L → ¬ C.preserved i → s.glob i = t.glob i) ∧
    (∀ a, t.lab a = Lab.L → s.lab a = Lab.L ∧ s.mem a = t.mem a) ∧
    (C.table = Lab.L → s.sameTable t) ∧ s.size = t.size ∧
    (s.cap = t.cap ∧ s.exns = t.exns ∧ Mem2Conf s t ∧ s.sameHost t) ∧ IoSame s t

theorem Conf.refl (C : Ctx) (s : State) : Conf C s s :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ h => ⟨h, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, .refl _, rfl, rfl, rfl⟩, .refl _⟩

theorem Conf.trans {C : Ctx} {s t u : State} (h1 : Conf C s t) (h2 : Conf C t u) : Conf C s u :=
  ⟨fun i hi => (h1.1 i hi).trans (h2.1 i hi), fun i hi hn => (h1.2.1 i hi hn).trans (h2.2.1 i hi hn),
    fun a ha => ⟨(h1.2.2.1 a (h2.2.2.1 a ha).1).1,
      ((h1.2.2.1 a (h2.2.2.1 a ha).1).2).trans (h2.2.2.1 a ha).2⟩,
    fun hl => (h1.2.2.2.1 hl).trans (h2.2.2.2.1 hl),
    h1.2.2.2.2.1.trans h2.2.2.2.2.1,
    ⟨h1.2.2.2.2.2.1.1.trans h2.2.2.2.2.2.1.1, h1.2.2.2.2.2.1.2.1.trans h2.2.2.2.2.2.1.2.1,
      h1.2.2.2.2.2.1.2.2.1.trans h2.2.2.2.2.2.1.2.2.1,
      h1.2.2.2.2.2.1.2.2.2.trans h2.2.2.2.2.2.1.2.2.2⟩,
    h1.2.2.2.2.2.2.trans h2.2.2.2.2.2.2⟩

/-- The first run goes on alone under a secret pc: the two still agree. -/
theorem StRel.conf_left {C : Ctx} {s s' t : State} (h : StRel C s t) (hc : Conf C s s') :
    StRel C s' t :=
  ⟨fun i hi => (hc.1 i hi).symm.trans (h.1 i hi),
    fun i hi hn => (hc.2.1 i hi hn).symm.trans (h.2.1 i hi hn),
    fun a ha hb => (hc.2.2.1 a ha).2.symm.trans (h.2.2.1 a (hc.2.2.1 a ha).1 hb),
    fun hl => (hc.2.2.2.1 hl).symm.trans (h.2.2.2.1 hl), hc.2.2.2.2.1.symm.trans h.2.2.2.2.1,
    h.2.2.2.2.2.1.conf_left hc.2.2.2.2.2.1, h.2.2.2.2.2.2.conf_left hc.2.2.2.2.2.2⟩

/-- The second run goes on alone under a secret pc: the two still agree. -/
theorem StRel.conf_right {C : Ctx} {s t t' : State} (h : StRel C s t) (hc : Conf C t t') :
    StRel C s t' :=
  (h.symm.conf_left hc).symm

theorem StRel.setLoc {C : Ctx} {s t : State} {i v0 v1 : Nat} (hv : C.locals i = Lab.L → v0 = v1)
    (h : StRel C s t) : StRel C (s.setLoc i v0) (t.setLoc i v1) := by
  refine ⟨fun j hj => ?_, h.2⟩
  by_cases hji : j = i
  · subst hji; simp [State.setLoc, hv hj]
  · simp [State.setLoc, hji, h.1 j hj]

theorem StRel.setGlob {C : Ctx} {s t : State} {i v0 v1 : Nat} (hv : C.globals i = Lab.L → v0 = v1)
    (h : StRel C s t) : StRel C (s.setGlob i v0) (t.setGlob i v1) := by
  refine ⟨h.1, fun j hj hn => ?_, h.2.2⟩
  by_cases hji : j = i
  · subst hji; simp [State.setGlob, hv hj]
  · simp [State.setGlob, hji, h.2.1 j hj hn]

/-- Two writes to a preserved global: the states are compared elsewhere than there. -/
theorem StRel.setGlob_preserved {C : Ctx} {s t : State} {i : Nat} (v0 v1 : Nat)
    (hi : C.preserved i) (h : StRel C s t) : StRel C (s.setGlob i v0) (t.setGlob i v1) := by
  refine ⟨h.1, fun j hj hn => ?_, h.2.2⟩
  by_cases hji : j = i
  · subst hji; exact absurd hi hn
  · simp [State.setGlob, hji, h.2.1 j hj hn]

/--
Two stores at the same level. At a public level the addresses and the values agree. At a
secret level they need not, and each run's cell becomes secret.
-/
theorem StRel.setMem {C : Ctx} {s t : State} {a0 a1 v0 v1 : Nat} {lm : Lab}
    (hv : lm = Lab.L → a0 = a1 ∧ v0 = v1) (h : StRel C s t) :
    StRel C (s.setMem a0 v0 lm) (t.setMem a1 v1 lm) := by
  refine ⟨h.1, h.2.1, fun x hx hy => ?_, h.2.2.2⟩
  cases lm with
  | L =>
    obtain ⟨rfl, rfl⟩ := hv rfl
    by_cases hxa : x = a0
    · simp [State.setMem, hxa]
    · simp only [State.setMem, hxa, ite_false] at hx hy ⊢
      exact h.2.2.1 x hx hy
  | H =>
    by_cases hx0 : x = a0
    · simp [State.setMem, hx0] at hx
    · by_cases hx1 : x = a1
      · simp [State.setMem, hx1] at hy
      · simp only [State.setMem, hx0, hx1, ite_false] at hx hy ⊢
        exact h.2.2.1 x hx hy

/-- A write to a secret local variable leaves the state as the attacker sees it. -/
theorem Conf.setLoc_high {C : Ctx} (s : State) {i : Nat} (v : Nat) (hi : C.locals i = Lab.H) :
    Conf C s (s.setLoc i v) := by
  refine ⟨fun j hj => ?_, fun _ _ _ => rfl, fun _ h => ⟨h, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, .refl _, rfl, rfl, rfl⟩, .refl _⟩
  by_cases hji : j = i
  · subst hji; rw [hi] at hj; cases hj
  · simp [State.setLoc, hji]

theorem Conf.setGlob_high {C : Ctx} (s : State) {i : Nat} (v : Nat) (hi : C.globals i = Lab.H) :
    Conf C s (s.setGlob i v) := by
  refine ⟨fun _ _ => rfl, fun j hj _ => ?_, fun _ h => ⟨h, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, .refl _, rfl, rfl, rfl⟩, .refl _⟩
  by_cases hji : j = i
  · subst hji; rw [hi] at hj; cases hj
  · simp [State.setGlob, hji]

/-- A write to a preserved global is one a run under a secret pc may make. -/
theorem Conf.setGlob_preserved {C : Ctx} (s : State) {i : Nat} (v : Nat) (hi : C.preserved i) :
    Conf C s (s.setGlob i v) := by
  refine ⟨fun _ _ => rfl, fun j _ hn => ?_, fun _ h => ⟨h, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, .refl _, rfl, rfl, rfl⟩, .refl _⟩
  by_cases hji : j = i
  · subst hji; exact absurd hi hn
  · simp [State.setGlob, hji]

/-- A store at a secret level makes its cell secret and touches no other. -/
theorem Conf.setMem_high (C : Ctx) (s : State) (a v : Nat) : Conf C s (s.setMem a v Lab.H) := by
  refine ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun x hx => ?_, fun _ => ⟨rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, .refl _, rfl, rfl, rfl⟩, .refl _⟩
  by_cases hxa : x = a
  · simp [State.setMem, hxa] at hx
  · simp only [State.setMem, hxa, ite_false] at hx ⊢
    exact ⟨hx, trivial⟩

/-- Two writes to the table. If the table is public, the indices and the references agree. -/
theorem StRel.setTbl {C : Ctx} {s t : State} {c0 c1 : Nat} {e0 e1 : Option Nat}
    (hv : C.table = Lab.L → c0 = c1 ∧ e0 = e1) (h : StRel C s t) :
    StRel C (s.setTbl c0 e0) (t.setTbl c1 e1) := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun hl => ?_, h.2.2.2.2⟩
  obtain ⟨rfl, rfl⟩ := hv hl
  exact ⟨by simp [State.setTbl, (h.2.2.2.1 hl).1], (h.2.2.2.1 hl).2⟩

/-- Two states that differ in a public table at most as two others that agree on it do. -/
theorem StRel.tbl {C : Ctx} {s t s' t' : State} (h : StRel C s t)
    (hs : { s with tbl := s'.tbl, tsize := s'.tsize, tcap := s'.tcap } = s')
    (ht : { t with tbl := t'.tbl, tsize := t'.tsize, tcap := t'.tcap } = t')
    (htbl : C.table = Lab.L → s'.sameTable t') : StRel C s' t' := by
  rw [← hs, ← ht]
  exact ⟨h.1, h.2.1, h.2.2.1, htbl, h.2.2.2.2⟩

/-- Any write to a secret table leaves the state as the attacker sees it. -/
theorem Conf.tbl_high {C : Ctx} (s : State) (tbl : Nat → Option Nat) (n : Nat)
    (hl : C.table = Lab.H) : Conf C s { s with tbl := tbl, tsize := n } := by
  refine ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ h => ⟨h, rfl⟩, fun h => ?_, rfl, ⟨rfl, rfl, .refl _, rfl, rfl, rfl⟩, .refl _⟩
  rw [hl] at h
  cases h

/-- A write to a secret table leaves the state as the attacker sees it. -/
theorem Conf.setTbl_high {C : Ctx} (s : State) (c : Nat) (e : Option Nat) (hl : C.table = Lab.H) :
    Conf C s (s.setTbl c e) := by
  refine ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ h => ⟨h, rfl⟩, fun h => ?_, rfl, ⟨rfl, rfl, .refl _, rfl, rfl, rfl⟩, .refl _⟩
  rw [hl] at h
  cases h

/--
Two fills at the same level. At a public level the ranges and the value agree. At a secret
level they need not, and each run's range becomes secret.
-/
theorem StRel.fill {C : Ctx} {s t : State} {a0 a1 v0 v1 k0 k1 : Nat} {lm : Lab}
    (hv : lm = Lab.L → a0 = a1 ∧ v0 = v1 ∧ k0 = k1) (h : StRel C s t) :
    StRel C (s.fill a0 v0 k0 lm) (t.fill a1 v1 k1 lm) := by
  refine ⟨h.1, h.2.1, fun x hx hy => ?_, h.2.2.2⟩
  cases lm with
  | L =>
    obtain ⟨rfl, rfl, rfl⟩ := hv rfl
    by_cases hr : a0 ≤ x ∧ x < a0 + k0
    · simp [State.fill, hr]
    · simp only [State.fill, hr, ite_false] at hx hy ⊢
      exact h.2.2.1 x hx hy
  | H =>
    by_cases hr0 : a0 ≤ x ∧ x < a0 + k0
    · simp [State.fill, hr0] at hx
    · by_cases hr1 : a1 ≤ x ∧ x < a1 + k1
      · simp [State.fill, hr1] at hy
      · simp only [State.fill, hr0, hr1, ite_false] at hx hy ⊢
        exact h.2.2.1 x hx hy

theorem Conf.fill_high (C : Ctx) (s : State) (a v k : Nat) : Conf C s (s.fill a v k Lab.H) := by
  refine ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun x hx => ?_, fun _ => ⟨rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, .refl _, rfl, rfl, rfl⟩, .refl _⟩
  by_cases hr : a ≤ x ∧ x < a + k
  · simp [State.fill, hr] at hx
  · simp only [State.fill, hr, ite_false] at hx ⊢
    exact ⟨hx, trivial⟩

/--
Two copies at the same level. At a public level the ranges agree, and a copied cell is public
in both runs only if its source was, where the two runs agree. At a secret level each run's
destination becomes secret.
-/
theorem StRel.copy {C : Ctx} {s t : State} {d0 d1 a0 a1 k0 k1 : Nat} {lm : Lab}
    (hv : lm = Lab.L → d0 = d1 ∧ a0 = a1 ∧ k0 = k1) (h : StRel C s t) :
    StRel C (s.copy d0 a0 k0 lm) (t.copy d1 a1 k1 lm) := by
  refine ⟨h.1, h.2.1, fun x hx hy => ?_, h.2.2.2⟩
  cases lm with
  | L =>
    obtain ⟨rfl, rfl, rfl⟩ := hv rfl
    by_cases hr : d0 ≤ x ∧ x < d0 + k0
    · simp only [State.copy, hr] at hx hy ⊢
      exact h.2.2.1 _ (Lab.join_eq_L hx).2 (Lab.join_eq_L hy).2
    · simp only [State.copy, hr, ite_false] at hx hy ⊢
      exact h.2.2.1 x hx hy
  | H =>
    by_cases hr0 : d0 ≤ x ∧ x < d0 + k0
    · simp [State.copy, hr0, Lab.H_join] at hx
    · by_cases hr1 : d1 ≤ x ∧ x < d1 + k1
      · simp [State.copy, hr1, Lab.H_join] at hy
      · simp only [State.copy, hr0, hr1, ite_false] at hx hy ⊢
        exact h.2.2.1 x hx hy

theorem Conf.copy_high (C : Ctx) (s : State) (d a k : Nat) : Conf C s (s.copy d a k Lab.H) := by
  refine ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun x hx => ?_, fun _ => ⟨rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, .refl _, rfl, rfl, rfl⟩, .refl _⟩
  by_cases hr : d ≤ x ∧ x < d + k
  · simp [State.copy, hr, Lab.H_join] at hx
  · simp only [State.copy, hr, ite_false] at hx ⊢
    exact ⟨hx, trivial⟩

/-- The two states have the same descriptor table and names of files. -/
theorem StRel.host {C : Ctx} {s t : State} (h : StRel C s t) : s.sameHost t := h.2.2.2.2.2.1.2.2.2.2

/-- A copy to the second memory, as one within the memory. -/
theorem StRel.copyTo {C : Ctx} {s t : State} {d0 d1 a0 a1 k0 k1 : Nat} {lm : Lab}
    (hv : lm = Lab.L → d0 = d1 ∧ a0 = a1 ∧ k0 = k1) (h : StRel C s t) :
    StRel C (s.copyTo d0 a0 k0 lm) (t.copyTo d1 a1 k1 lm) := by
  obtain ⟨h1, h2, h3, h4, h5, ⟨hcap, hex, hok, ⟨hm2, hs2⟩, hh⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ⟨hcap, hex, hok, ⟨fun x hx hy => ?_, hs2⟩, hh⟩, h7⟩
  cases lm with
  | L =>
    obtain ⟨rfl, rfl, rfl⟩ := hv rfl
    by_cases hr : d0 ≤ x ∧ x < d0 + k0
    · simp only [State.copyTo, hr] at hx hy ⊢
      exact h3 _ (Lab.join_eq_L hx).2 (Lab.join_eq_L hy).2
    · simp only [State.copyTo, hr, ite_false] at hx hy ⊢
      exact hm2 x hx hy
  | H =>
    by_cases hr0 : d0 ≤ x ∧ x < d0 + k0
    · simp [State.copyTo, hr0, Lab.H_join] at hx
    · by_cases hr1 : d1 ≤ x ∧ x < d1 + k1
      · simp [State.copyTo, hr1, Lab.H_join] at hy
      · simp only [State.copyTo, hr0, hr1, ite_false] at hx hy ⊢
        exact hm2 x hx hy

/-- A copy from the second memory, as one within the memory. -/
theorem StRel.copyFrom {C : Ctx} {s t : State} {d0 d1 a0 a1 k0 k1 : Nat} {lm : Lab}
    (hv : lm = Lab.L → d0 = d1 ∧ a0 = a1 ∧ k0 = k1) (h : StRel C s t) :
    StRel C (s.copyFrom d0 a0 k0 lm) (t.copyFrom d1 a1 k1 lm) := by
  have hm2 := h.2.2.2.2.2.1.2.2.2.1.1
  refine ⟨h.1, h.2.1, fun x hx hy => ?_, h.2.2.2⟩
  cases lm with
  | L =>
    obtain ⟨rfl, rfl, rfl⟩ := hv rfl
    by_cases hr : d0 ≤ x ∧ x < d0 + k0
    · simp only [State.copyFrom, hr] at hx hy ⊢
      exact hm2 _ (Lab.join_eq_L hx).2 (Lab.join_eq_L hy).2
    · simp only [State.copyFrom, hr, ite_false] at hx hy ⊢
      exact h.2.2.1 x hx hy
  | H =>
    by_cases hr0 : d0 ≤ x ∧ x < d0 + k0
    · simp [State.copyFrom, hr0, Lab.H_join] at hx
    · by_cases hr1 : d1 ≤ x ∧ x < d1 + k1
      · simp [State.copyFrom, hr1, Lab.H_join] at hy
      · simp only [State.copyFrom, hr0, hr1, ite_false] at hx hy ⊢
        exact h.2.2.1 x hx hy

theorem Conf.copyTo_high (C : Ctx) (s : State) (d a k : Nat) : Conf C s (s.copyTo d a k Lab.H) := by
  refine ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ h => ⟨h, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩, rfl,
    ⟨rfl, rfl, ⟨fun x hx => ?_, rfl⟩, rfl, rfl, rfl⟩, .refl _⟩
  by_cases hr : d ≤ x ∧ x < d + k
  · simp [State.copyTo, hr, Lab.H_join] at hx
  · simp only [State.copyTo, hr, ite_false] at hx ⊢
    exact ⟨hx, trivial⟩

theorem Conf.copyFrom_high (C : Ctx) (s : State) (d a k : Nat) :
    Conf C s (s.copyFrom d a k Lab.H) := by
  refine ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun x hx => ?_, fun _ => ⟨rfl, rfl, rfl⟩, rfl,
    ⟨rfl, rfl, .refl _, rfl, rfl, rfl⟩, .refl _⟩
  by_cases hr : d ≤ x ∧ x < d + k
  · simp [State.copyFrom, hr, Lab.H_join] at hx
  · simp only [State.copyFrom, hr, ite_false] at hx ⊢
    exact ⟨hx, trivial⟩

/-! ### The host -/

/--
Two host calls store what they read at the same level. At a public level the address and the
values agree. At a secret level they need not, and each run's cells become secret.
-/
theorem StRel.put {C : Ctx} {s t : State} {a0 a1 : Nat} {vs0 vs1 : List Nat} {lm : Lab}
    (hv : lm = Lab.L → a0 = a1 ∧ vs0 = vs1) (h : StRel C s t) :
    StRel C (s.put a0 vs0 lm) (t.put a1 vs1 lm) := by
  refine ⟨h.1, h.2.1, fun x hx hy => ?_, h.2.2.2⟩
  cases lm with
  | L =>
    obtain ⟨rfl, rfl⟩ := hv rfl
    by_cases hr : a0 ≤ x ∧ x < a0 + vs0.length
    · simp [State.put, hr]
    · simp only [State.put, hr, ite_false] at hx hy ⊢
      exact h.2.2.1 x hx hy
  | H =>
    by_cases hr0 : a0 ≤ x ∧ x < a0 + vs0.length
    · simp [State.put, hr0] at hx
    · by_cases hr1 : a1 ≤ x ∧ x < a1 + vs1.length
      · simp [State.put, hr1] at hy
      · simp only [State.put, hr0, hr1, ite_false] at hx hy ⊢
        exact h.2.2.1 x hx hy

/-- A store at a secret level makes its bytes secret and touches no other. -/
theorem Conf.put_high (C : Ctx) (s : State) (a : Nat) (vs : List Nat) : Conf C s (s.put a vs Lab.H) := by
  refine ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun x hx => ?_, fun _ => ⟨rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, .refl _, rfl, rfl, rfl⟩, .refl _⟩
  by_cases hr : a ≤ x ∧ x < a + vs.length
  · simp [State.put, hr] at hx
  · simp only [State.put, hr, ite_false] at hx ⊢
    exact ⟨hx, trivial⟩

theorem bytesOf_length (v : Nat) : ∀ w, (bytesOf v w).length = w
  | 0 => rfl
  | w + 1 => by simp [bytesOf, bytesOf_length (v / 256) w]

/-- Two words whose bytes agree are the same. -/
theorem word_eq {s t : State} : ∀ (w a : Nat), (∀ i, i < w → s.mem (a + i) = t.mem (a + i)) →
    s.word a w = t.word a w
  | 0, _, _ => rfl
  | w + 1, a, h => by
      have h0 := h 0 (Nat.succ_pos w)
      have hrest := word_eq w (a + 1) (fun i hi => by
        have := h (i + 1) (Nat.succ_lt_succ hi)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
      simp only [State.word]
      rw [hrest]
      simpa using h0

/-- Two reads of the same descriptor, of the same amount, leave what the attacker sees to read alike. -/
theorem StRel.consume {C : Ctx} {s t : State} (fd k : Nat) (h : StRel C s t) :
    StRel C (s.consume fd k) (t.consume fd k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hc, hio, hseg⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, hc, fun d hd => ⟨(hio d hd).1, ?_⟩, hseg⟩
  by_cases hdf : d = fd
  · subst hdf
    simp [State.consume, (hio d hd).2]
  · simp [State.consume, hdf, (hio d hd).2]

/--
Two writes of the same cells to the same descriptor, each after its check: if the descriptor is
public, the cells are public in both runs, so the two wrote the same.
-/
theorem StRel.emit {C : Ctx} {s t : State} {fd a k : Nat} (h : StRel C s t)
    (h0 : ∀ x, a ≤ x → x < a + k → Lab.le (s.lab x) (s.chan fd))
    (h1 : ∀ x, a ≤ x → x < a + k → Lab.le (t.lab x) (t.chan fd)) :
    StRel C (s.emit fd (s.cells a k)) (t.emit fd (t.cells a k)) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, hc, hio, hseg⟩ := h
  refine ⟨g1, g2, g3, g4, g5, g6, hc, fun d hd => ⟨?_, (hio d hd).2⟩, hseg⟩
  by_cases hdf : d = fd
  · subst hdf
    have hd' : s.chan d = Lab.L := hd
    have hcells : s.cells a k = t.cells a k := by
      unfold State.cells
      apply List.map_congr_left
      intro i hi
      have hik : i < k := List.mem_range.mp hi
      exact g3 (a + i) (Lab.eq_L_of_le (h0 (a + i) (by omega) (by omega)) hd')
        (Lab.eq_L_of_le (h1 (a + i) (by omega) (by omega)) (hc ▸ hd'))
    simp [State.emit, hcells, (hio d hd').1]
  · simp [State.emit, hdf, (hio d hd).1]

/-! ### Opening a file -/

theorem State.fresh_unique {s : State} {d d' : Nat} (h : s.fresh d) (h' : s.fresh d') : d = d' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  rcases Nat.lt_trichotomy d d' with hlt | heq | hgt
  · exact absurd h2 (h3' d h1 hlt)
  · exact heq
  · exact absurd h2' (h3 d' h1' hgt)

/-- Two runs with the same descriptor table give a new file the same descriptor. -/
theorem State.fresh_same {s t : State} {d d' : Nat} (h : s.fdt = t.fdt) (h0 : s.fresh d)
    (h1 : t.fresh d') : d = d' := by
  unfold State.fresh at h0
  rw [h] at h0
  exact State.fresh_unique h0 h1

/-- Cells that are public in both runs hold the same in both. -/
theorem StRel.cells_public {C : Ctx} {s t : State} {a k : Nat} (h : StRel C s t)
    (h0 : ∀ x, a ≤ x → x < a + k → s.lab x = Lab.L)
    (h1 : ∀ x, a ≤ x → x < a + k → t.lab x = Lab.L) : s.cells a k = t.cells a k := by
  unfold State.cells
  apply List.map_congr_left
  intro i hi
  have hik : i < k := List.mem_range.mp hi
  exact h.2.2.1 (a + i) (h0 (a + i) (by omega) (by omega)) (h1 (a + i) (by omega) (by omega))

/-- Two runs open the same file in the same directory as the same descriptor. -/
theorem StRel.openAt {C : Ctx} {s t : State} (c : Nat) (x : List Nat) (d : Nat)
    (h : StRel C s t) : StRel C (s.openAt c x d) (t.openAt c x d) := by
  obtain ⟨h1, h2, h3, h4, h5, ⟨hcap, hex, hok, hm2, hfdt, hnames, hfile⟩, hc, hio, hseg⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ⟨hcap, hex, hok, hm2, ?_, ?_, hfile⟩, hc, fun k hk => ?_, hseg⟩
  · simp only [State.openAt, hfdt, hfile]
  · simp only [State.openAt, hnames]
  · simp only [State.openAt, hnames, hfile]
    by_cases hnew : k = t.file c x ∧ x ∉ t.names c
    · simp [hnew]
    · simp only [hnew, ite_false]
      exact hio k hk

/-! ### Data segments -/

theorem StRel.dropSeg {C : Ctx} {s t : State} (k : Nat) (h : StRel C s t) :
    StRel C (s.dropSeg k) (t.dropSeg k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hc, hio, hseg⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, hc, hio, fun j => ?_⟩
  by_cases hj : j = k
  · simp [State.dropSeg, hj]
  · simpa [State.dropSeg, hj] using hseg j

theorem Conf.dropSeg (C : Ctx) (s : State) (k : Nat) : Conf C s (s.dropSeg k) := by
  refine ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ h => ⟨h, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, .refl _, rfl, rfl, rfl⟩, rfl,
    rfl, rfl, fun j => ?_⟩
  by_cases hj : j = k <;> simp [State.dropSeg, hj]

/--
The bytes two runs take from a segment, each within the segment it has: the same. If one run
has dropped the segment, it takes no byte, and then neither does the other.
-/
theorem seg_payload {C : Ctx} {s t : State} (h : StRel C s t) {k b c : Nat}
    (h0 : b + c ≤ (s.segs k).length) (h1 : b + c ≤ (t.segs k).length) :
    ((s.segs k).drop b).take c = ((t.segs k).drop b).take c := by
  rcases h.2.2.2.2.2.2.2.2 k with e | e | e
  · rw [e]
  · rw [e] at h0
    have hc : c = 0 := by simp at h0; omega
    subst hc
    simp
  · rw [e] at h1
    have hc : c = 0 := by simp at h1; omega
    subst hc
    simp

/-- The memory grows by the same amount in two runs: the same result, and states that still agree. -/
theorem StRel.grow {C : Ctx} {s t : State} (d : Nat) (h : StRel C s t) :
    (s.grow d).1 = (t.grow d).1 ∧ StRel C (s.grow d).2 (t.grow d).2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  unfold State.grow
  rw [h5, h6.1]
  by_cases hc : t.size + d ≤ t.cap
  · simp only [hc, ite_true]
    refine ⟨trivial, fun i hi => h1 i hi, fun i hi hn => h2 i hi hn, fun a ha hb => ?_, h4, rfl,
      ⟨rfl, h6.2.1, h6.2.2⟩, h7⟩
    by_cases hsz : t.size ≤ a
    · simp [hsz]
    · simp only [hsz, ite_false] at ha hb ⊢
      exact h3 a ha hb
  · simp only [hc, ite_false]
    exact ⟨trivial, h1, h2, h3, h4, h5, h6, h7⟩

theorem State.grow_glob (s : State) (d : Nat) : (s.grow d).2.glob = s.glob := by
  unfold State.grow
  split <;> rfl

/-! ### A clause that catches by reference -/

theorem State.handed_glob (s : State) (t : Nat) (w : List Nat) (carry r : Bool) :
    (s.handed t w carry r).2.glob = s.glob := by
  cases r <;> rfl

/--
The same exception, caught by the same clause in two runs: the label gets the same values, with
the same reference if the clause is by reference, and the states still agree.
-/
theorem StRel.handed {C : Ctx} {s0 s1 : State} {t k : Nat} {w : List Nat} (carry r : Bool)
    (htag : C.tags[t]? = some k) (hlen : w.length = k) (h : StRel C s0 s1) :
    (s0.handed t w carry r).1 = (s1.handed t w carry r).1 ∧
      StRel C (s0.handed t w carry r).2 (s1.handed t w carry r).2 := by
  cases r with
  | false => exact ⟨rfl, h⟩
  | true =>
    obtain ⟨h1, h2, h3, h4, h5, ⟨hcap, hex, hok, hh⟩, h7⟩ := h
    refine ⟨by simp [State.handed, hex], h1, h2, h3, h4, h5,
      ⟨hcap, by simp [State.handed, hex], fun e he => ?_, hh⟩, h7⟩
    rcases List.mem_append.1 he with hin | hin
    · exact hok e hin
    · simp only [List.mem_singleton] at hin
      subst hin
      simp [htag, hlen]

/-! ### The table grows -/

theorem State.growTbl_glob (s : State) (d : Nat) (e : Option Nat) :
    (s.growTbl d e).2.glob = s.glob := by
  unfold State.growTbl
  split <;> rfl

/-- `table.grow` changes the table and nothing else. -/
theorem State.growTbl_eq (s : State) (d : Nat) (e : Option Nat) :
    { s with tbl := (s.growTbl d e).2.tbl, tsize := (s.growTbl d e).2.tsize,
             tcap := (s.growTbl d e).2.tcap } = (s.growTbl d e).2 := by
  unfold State.growTbl
  split <;> rfl

/-- The same table grows alike in two runs: the same result and the same table again. -/
theorem State.growTbl_same {s t : State} (d : Nat) (e : Option Nat) (h : s.sameTable t) :
    (s.growTbl d e).1 = (t.growTbl d e).1 ∧ (s.growTbl d e).2.sameTable (t.growTbl d e).2 := by
  obtain ⟨htb, hts, htc⟩ := h
  unfold State.growTbl State.sameTable
  rw [hts, htc]
  split
  · simp [htb]
  · exact ⟨rfl, htb, hts, htc⟩

/-- Two runs grow the table. If the table is public, they grow it alike. -/
theorem StRel.growTbl {C : Ctx} {s t : State} {d0 d1 : Nat} {e0 e1 : Option Nat}
    (hv : C.table = Lab.L → d0 = d1 ∧ e0 = e1) (h : StRel C s t) :
    StRel C (s.growTbl d0 e0).2 (t.growTbl d1 e1).2 ∧
      (C.table = Lab.L → (s.growTbl d0 e0).1 = (t.growTbl d1 e1).1) := by
  refine ⟨h.tbl (State.growTbl_eq _ _ _) (State.growTbl_eq _ _ _) (fun hl => ?_), fun hl => ?_⟩
  · obtain ⟨rfl, rfl⟩ := hv hl
    exact (State.growTbl_same _ _ (h.2.2.2.1 hl)).2
  · obtain ⟨rfl, rfl⟩ := hv hl
    exact (State.growTbl_same _ _ (h.2.2.2.1 hl)).1

/-- A secret table that grows leaves the state as the attacker sees it. -/
theorem Conf.growTbl_high {C : Ctx} (s : State) (d : Nat) (e : Option Nat)
    (hl : C.table = Lab.H) : Conf C s (s.growTbl d e).2 := by
  unfold State.growTbl
  split
  · exact Conf.tbl_high _ _ _ hl
  · exact Conf.refl _ _

/-! ### Calls -/

/-- Arguments that agree where the parameters are public make frames that agree on the public locals. -/
theorem frame_rel {ps : STy} {a b : List Nat} (h : StkRel ps a b) :
    ∀ (extra : List Lab) (i : Nat), ((ps ++ extra)[i]?).getD Lab.L = Lab.L →
      (a[i]?).getD 0 = (b[i]?).getD 0 := by
  induction h with
  | nil => intro _ _ _; rfl
  | cons hv _ ih =>
    intro extra i hi
    cases i with
    | zero => simpa using hv (by simpa using hi)
    | succ i => simpa using ih extra i (by simpa using hi)

/-- The states in which two calls of `f` start its body. -/
theorem StRel.enter {C : Ctx} {f : Func} {a0 a1 : List Nat} {s0 s1 : State}
    (ha : StkRel f.ty.params a0 a1) (hs : StRel C s0 s1) :
    StRel (C.enter f) { s0 with loc := frame a0 } { s1 with loc := frame a1 } :=
  ⟨fun i hi => frame_rel ha f.extra i hi, hs.2⟩

/-- The states in which two callers go on: their own locals, and the rest as the callees left it. -/
theorem StRel.leave {C : Ctx} {f : Func} {s0 s1 t0 t1 : State} (hs : StRel C s0 s1)
    (ht : StRel (C.enter f) t0 t1) :
    StRel C { t0 with loc := s0.loc } { t1 with loc := s1.loc } :=
  ⟨hs.1, ht.2⟩

/-- A callee that ran under a secret pc leaves the caller's state as such a run may. -/
theorem Conf.call {C : Ctx} {f : Func} {args : List Nat} {s t : State}
    (h : Conf (C.enter f) { s with loc := frame args } t) : Conf C s { t with loc := s.loc } :=
  ⟨fun _ _ => rfl, h.2⟩

theorem WellTyped.enter {C : Ctx} {F : List Func} (h : WellTyped C F) (g : Func) :
    WellTyped (C.enter g) F := fun i f hf => h i f hf

/-! ### Preserved globals where control comes out of a construct -/

/--
The preserved globals after a block, a loop or a conditional that both runs come out of. The
runs agreed on them at its start unless the pc after it is secret (`hentry`), and at its end
unless its own pc was secret (`hend`). If its pc was secret and the pc after it is not, the pc
drops, so the construct compared them with their values at its start, in both runs.
-/
theorem pres_after {C : Ctx} {p : Lab} {P1 : Pcs} {keep : List Nat} {e0 e1 t0 t1 : State}
    (hres : Restores C p P1 keep) (hentry : PresOr C 0 P1 e0 e1) (hk0 : Kept keep e0 t0)
    (hk1 : Kept keep e1 t1) (hend : PresOr C 0 (p :: P1) t0 t1) : PresOr C 0 P1 t0 t1 := by
  rcases hend with h | h
  · exact .inl h
  · rcases hres with hr | hc
    · exact .inr (hiUpTo_of_noDrop hr h.head)
    · rcases hentry with he | he
      · exact .inl (fun i hi =>
          ((hk0 i (hc i hi)).trans (he i hi)).trans (hk1 i (hc i hi)).symm)
      · exact .inr he

/--
The preserved globals after a call that both runs return from, for a callee that ends under the
pc `p`: it returns under a public pc, or it compared them with their values at the call.
-/
theorem pres_after_call {C : Ctx} {p : Lab} {P : Pcs} {keep : List Nat} {e0 e1 t0 t1 : State}
    (hret : p = Lab.L ∨ ∀ j, C.preserved j → j ∈ keep) (hentry : PresOr C 0 P e0 e1)
    (hk0 : Kept keep e0 t0) (hk1 : Kept keep e1 t1) (hend : PresOr C 0 [p] t0 t1) :
    PresOr C 0 P t0 t1 := by
  rcases hentry with he | he
  · rcases hret with hp | hc
    · rcases hend with h | h
      · exact .inl h
      · rw [hp] at h; exact absurd h.head (by decide)
    · exact .inl (fun i hi => ((hk0 i (hc i hi)).trans (he i hi)).trans (hk1 i (hc i hi)).symm)
  · exact .inr he

/-! ### What is known of one run's outcome, and how two outcomes relate -/

/--
What a run under a secret pc guarantees of its outcome. At the end of the sequence, the segment
has the shape of its type. A branch goes to a label whose type is all secret, carries as many
values as that type has, and the pcs of the blocks it leaves are secret.
-/
def Info (Ls : List STy) (P : Pcs) (st : STy) : Out → Prop
  | .normal σ _ => σ.length = st.length
  | .br i w _ => ∃ rs, Ls[i]? = some rs ∧ AllGe Lab.H rs ∧ w.length = rs.length ∧ HiUpTo i P
  | .exn _ _ _ => False
  | .tailExn _ _ _ => False

theorem Info.not_thrown {Ls : List STy} {P : Pcs} {st : STy} {o : Out} {x : Nat × List Nat × State}
    (h : Info Ls P st o) (hx : o.thrown = some x) : False := by
  cases o with
  | normal σ s => simp [Out.thrown] at hx
  | br i w s => simp [Out.thrown] at hx
  | exn t w s => exact h
  | tailExn t w s => exact h

/-- An outcome that a block goes on after is not an exception. -/
theorem lands_thrown {o : Out} {x : List Nat × State} {y : Nat × List Nat × State}
    (hl : o.lands = some x) (hy : o.thrown = some y) : False := by
  cases o with
  | normal σ s => simp [Out.thrown] at hy
  | br i w s => simp [Out.thrown] at hy
  | exn t w s => simp [Out.lands] at hl
  | tailExn t w s => simp [Out.lands] at hl

theorem Info.mono {Ls : List STy} {P P' : Pcs} {st : STy} {o : Out} (hf : SFlows P P')
    (h : Info Ls P st o) : Info Ls P' st o := by
  cases o with
  | normal σ s => exact h
  | br i w s =>
    obtain ⟨rs, h1, h2, h3, h4⟩ := h
    exact ⟨rs, h1, h2, h3, HiUpTo.sflows hf h4⟩
  | exn t w s => exact h
  | tailExn t w s => exact h

/--
The two runs ended the same way, with segments or carried values that agree where public. They
agree on the preserved globals too, unless the pc they end under is secret: after a branch,
that is the pcs of the blocks it leaves.
-/
inductive Sync (C : Ctx) (Ls : List STy) (P : Pcs) (st : STy) : Out → Out → Prop where
  | normal {σ0 σ1 : List Nat} {s0 s1 : State} :
      StkRel st σ0 σ1 → StRel C s0 s1 → PresOr C 0 P s0 s1 →
      Sync C Ls P st (.normal σ0 s0) (.normal σ1 s1)
  | br {i : Nat} {rs : STy} {w0 w1 : List Nat} {s0 s1 : State} :
      Ls[i]? = some rs → StkRel rs w0 w1 → StRel C s0 s1 → PresOr C i P s0 s1 →
      Sync C Ls P st (.br i w0 s0) (.br i w1 s1)
  /-- The same exception with the same values, thrown under a public pc. -/
  | exn {t k : Nat} {w : List Nat} {s0 s1 : State} :
      C.tags[t]? = some k → w.length = k → StRel C s0 s1 → PresEq C s0 s1 →
      Sync C Ls P st (.exn t w s0) (.exn t w s1)
  /-- The same, for the exception of a tail call's callee. -/
  | tailExn {t k : Nat} {w : List Nat} {s0 s1 : State} :
      C.tags[t]? = some k → w.length = k → StRel C s0 s1 → PresEq C s0 s1 →
      Sync C Ls P st (.tailExn t w s0) (.tailExn t w s1)

theorem Sync.mono {C : Ctx} {Ls : List STy} {P P' : Pcs} {st : STy} {o0 o1 : Out}
    (hf : SFlows P P') (h : Sync C Ls P st o0 o1) : Sync C Ls P' st o0 o1 := by
  cases h with
  | normal h1 h2 h3 => exact .normal h1 h2 (h3.mono hf)
  | br h0 h1 h2 h3 => exact .br h0 h1 h2 (h3.mono hf)
  | exn h0 h1 h2 h3 => exact .exn h0 h1 h2 h3
  | tailExn h0 h1 h2 h3 => exact .tailExn h0 h1 h2 h3

/-- The two runs took different paths under a secret pc: their states agree, and each is as `Info` says. -/
def Loose (C : Ctx) (Ls : List STy) (P : Pcs) (st : STy) (o0 o1 : Out) : Prop :=
  StRel C o0.state o1.state ∧ Info Ls P st o0 ∧ Info Ls P st o1

/--
The relation between the outcomes of two runs of a typed sequence from related inputs: in step,
or apart with at least one of them on its way out of a block.
-/
def OutRel (C : Ctx) (Ls : List STy) (P : Pcs) (st : STy) (o0 o1 : Out) : Prop :=
  Sync C Ls P st o0 o1 ∨ (Loose C Ls P st o0 o1 ∧ (o0.isBr ∨ o1.isBr))

theorem Loose.mono {C : Ctx} {Ls : List STy} {P P' : Pcs} {st : STy} {o0 o1 : Out}
    (hf : SFlows P P') (h : Loose C Ls P st o0 o1) : Loose C Ls P' st o0 o1 :=
  ⟨h.1, h.2.1.mono hf, h.2.2.mono hf⟩

/-! ### Pc stacks only rise (the paper's `lem:rise`) -/

theorem rise {C : Ctx} {Ls : List STy} {e : List Instr} {P P' : Pcs} {st st' : STy}
    (h : Typed C Ls e P st P' st') : SFlows P P' := by
  induction h with
  | nil => exact SFlows.refl _
  | const _ _ ih => exact ih
  | binop _ _ ih => exact ih
  | unop _ _ ih => exact ih
  | dup _ ih => exact ih
  | select _ ih => exact ih
  | drop _ ih => exact ih
  | nop _ ih => exact ih
  | relabel _ _ ih => exact ih
  | localGet _ _ ih => exact ih
  | localSet _ _ _ _ ih => exact ih
  | localTee _ _ _ _ ih => exact ih
  | globalGet _ _ ih => exact ih
  | globalSet _ _ _ _ _ ih => exact ih
  | globalSetPreserved _ _ _ _ ih => exact ih
  | load _ _ _ ih => exact ih
  | store _ _ _ _ ih => exact ih
  | fill _ _ _ ih => exact ih
  | copy _ _ _ ih => exact ih
  | copyTo _ _ _ ih => exact ih
  | copyFrom _ _ _ ih => exact ih
  | tableGet _ ih => exact ih
  | tableSet _ _ ih => exact ih
  | hostRead _ ih => exact ih
  | hostWrite _ ih => exact ih
  | hostOpen _ ih => exact ih
  | memInit _ _ _ _ ih => exact ih
  | dataDrop _ _ ih => exact ih
  | tableFill _ _ ih => exact ih
  | tableCopy _ _ ih => exact ih
  | tableSize _ ih => exact ih
  | tableGrow _ _ ih => exact ih
  | memSize _ ih => exact ih
  | memGrow _ _ ih => exact ih
  | block _ _ _ _ _ ihb ihr => exact SFlows.trans ihb.tail ihr
  | loop _ _ _ _ _ _ _ ihb ihr => exact SFlows.trans ihb.tail ihr
  | iter _ _ _ ih => exact .cons (Lab.le_refl _) ih.tail
  | ite _ _ _ _ _ _ ih1 ih2 ihr => exact SFlows.trans (sflows_joinEach ih1.tail ih2.tail).2.2 ihr
  | br _ _ _ => exact sflows_raise _ _ _
  | brIf _ _ _ _ ih => exact SFlows.trans (sflows_raise _ _ _) ih
  | brTable _ _ _ => exact sflows_raise _ _ _
  | ret _ _ _ => exact sflows_raise _ _ _
  | retCall _ _ _ _ _ _ => exact sflows_raise _ _ _
  | retCallIndirect _ _ _ _ _ _ => exact sflows_raise _ _ _
  | call _ _ _ _ ih => exact ih
  | callIndirect _ _ _ _ ih => exact ih
  | callRef _ _ _ _ ih => exact ih
  | unreachable => exact SFlows.refl _
  | throw _ _ _ => exact SFlows.refl _
  | throwRef => exact SFlows.refl _
  | tryTable _ _ _ _ _ ihb ihr => exact SFlows.trans ihb.tail ihr

end WasmIfc
