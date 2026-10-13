/-
The statement of the development, in the paper's terms: low equivalence (the paper's
definition of the attacker), a call of a function from outside, and noninterference for such
a call. A reader who checks statements and leaves the proofs to Lean reads this file after
`Defs.lean`; `lean/STATEMENTS.md` is the guide.
-/
import WasmIfc.Noninterference

namespace WasmIfc

/--
Low equivalence of two states, for the levels of `C`. The two states agree on what the
attacker may know: the public local variables, the public globals, every byte of memory that
is public in both, the size of the memory and its limit, the function table if it is public,
the levels of the host's descriptors, and for each public descriptor what was written to it
and what is left to read from it. A data segment that both states still have is the same in
both (one of them may have dropped it).
-/
def LowEq (C : Ctx) (s t : State) : Prop :=
  (∀ i, C.locals i = Lab.L → s.loc i = t.loc i) ∧
  (∀ i, C.globals i = Lab.L → s.glob i = t.glob i) ∧
  (∀ a, s.lab a = Lab.L → t.lab a = Lab.L → s.mem a = t.mem a) ∧
  s.size = t.size ∧ s.cap = t.cap ∧
  (C.table = Lab.L → s.sameTable t) ∧
  s.chan = t.chan ∧
  (∀ d, s.chan d = Lab.L → s.out d = t.out d ∧ s.inp d = t.inp d) ∧
  (∀ k, s.segs k = t.segs k ∨ s.segs k = [] ∨ t.segs k = [])

/-- Low equivalence is the two relations of the proof together, if the preserved globals are public. -/
theorem LowEq.split {C : Ctx} {s t : State} (hpub : ∀ i, C.preserved i → C.globals i = Lab.L)
    (h : LowEq C s t) : StRel C s t ∧ PresEq C s t := by
  obtain ⟨hloc, hglob, hmem, hsize, hcap, htbl, hchan, hio, hseg⟩ := h
  exact ⟨⟨hloc, fun i hi _ => hglob i hi, hmem, htbl, hsize, hcap, hchan, hio, hseg⟩,
    fun i hi => hglob i (hpub i hi)⟩

theorem LowEq.join {C : Ctx} {s t : State} (h : StRel C s t) (hp : PresEq C s t) : LowEq C s t := by
  obtain ⟨hloc, hglob, hmem, htbl, hsize, hcap, hchan, hio, hseg⟩ := h
  refine ⟨hloc, fun i hi => ?_, hmem, hsize, hcap, htbl, hchan, hio, hseg⟩
  by_cases hpi : C.preserved i
  · exact hp i hpi
  · exact hglob i hi hpi

/-- How a call from outside ends, if it ends: with results or with an exception, and in a state. -/
inductive Ended where
  | returned (results : List Nat) (s : State)
  | threw (tag : Nat) (values : List Nat) (s : State)

/--
`Invoke F f a s e`: the function `f`, called from outside on the arguments `a` (the last one
first) in the state `s`, ends as `e`. It returns at the end of its body or by a branch to its
label, and only if the globals it compares hold what they held at the call, as for a call
from inside the module; or an exception leaves it. The local variables of whoever called are
theirs again afterwards. A call that traps or does not terminate ends in no way.
-/
inductive Invoke (F : List Func) (f : Func) (a : List Nat) (s : State) : Ended → Prop where
  | returned {n : Nat} {o : Out} {r : List Nat} {t : State} :
      Eval F n [f.ty.results.length] f.body [] { s with loc := frame a } o →
      o.lands = some (r, t) → Kept f.keep s t →
      Invoke F f a s (.returned r { t with loc := s.loc })
  | threw {n tag : Nat} {o : Out} {w : List Nat} {u : State} :
      Eval F n [f.ty.results.length] f.body [] { s with loc := frame a } o →
      o.thrown = some (tag, w, u) →
      Invoke F f a s (.threw tag w { u with loc := s.loc })

/--
Termination-insensitive noninterference (the paper's theorem, on the core). Take a well-typed
module in which the preserved globals are public, one of its functions, and two calls of it
from outside, from low-equivalent states and with arguments that agree where the function's
parameters are public. If both calls end, then both return or both end by the same exception
with the same values. If they return, their results agree where the function's result type
is public. In both cases the states they end in are low-equivalent.
-/
theorem noninterference {C : Ctx} {F : List Func} (hF : WellTyped C F)
    (hpub : ∀ i, C.preserved i → C.globals i = Lab.L) {i : Nat} {f : Func} (hf : F[i]? = some f)
    {a0 a1 : List Nat} {s0 s1 : State} {e0 e1 : Ended}
    (ha : StkRel f.ty.params a0 a1) (hs : LowEq C s0 s1)
    (h0 : Invoke F f a0 s0 e0) (h1 : Invoke F f a1 s1 e1) :
    (∃ r0 t0 r1 t1, e0 = .returned r0 t0 ∧ e1 = .returned r1 t1 ∧
      StkRel f.ty.results r0 r1 ∧ LowEq C t0 t1) ∨
    (∃ tag w t0 t1, e0 = .threw tag w t0 ∧ e1 = .threw tag w t1 ∧ LowEq C t0 t1) := by
  obtain ⟨hst, hpe⟩ := hs.split hpub
  cases h0 with
  | returned he0 hl0 hk0 =>
    cases h1 with
    | returned he1 hl1 hk1 =>
      rcases tini hF hf he0 he1 ha hst hpe with ⟨r0, t0, r1, t1, hl0', hl1', hres, hrel, hpres⟩ |
        ⟨tag, w, u0, u1, ho0, _, _, _⟩
      · rw [hl0] at hl0'
        cases hl0'
        rw [hl1] at hl1'
        cases hl1'
        exact .inl ⟨_, _, _, _, rfl, rfl, hres, LowEq.join hrel (fun i hi => hpres hk0 hk1 i hi)⟩
      · exact (lands_thrown hl0 ho0).elim
    | threw he1 ht1 =>
      rcases tini hF hf he0 he1 ha hst hpe with ⟨r0, t0, r1, t1, _, hl1', _, _, _⟩ |
        ⟨tag, w, u0, u1, ho0, _, _, _⟩
      · exact (lands_thrown hl1' ht1).elim
      · exact (lands_thrown hl0 ho0).elim
  | threw he0 ht0 =>
    cases h1 with
    | returned he1 hl1 hk1 =>
      rcases tini hF hf he0 he1 ha hst hpe with ⟨r0, t0, r1, t1, hl0', _, _, _, _⟩ |
        ⟨tag, w, u0, u1, _, ho1, _, _⟩
      · exact (lands_thrown hl0' ht0).elim
      · exact (lands_thrown hl1 ho1).elim
    | threw he1 ht1 =>
      rcases tini hF hf he0 he1 ha hst hpe with ⟨r0, t0, r1, t1, hl0', _, _, _, _⟩ |
        ⟨tag, w, u0, u1, ho0, ho1, hrel, hpres⟩
      · exact (lands_thrown hl0' ht0).elim
      · cases ht0.symm.trans ho0
        cases ht1.symm.trans ho1
        exact .inr ⟨_, _, _, _, rfl, rfl, LowEq.join hrel (fun i hi => hpres i hi)⟩

end WasmIfc
