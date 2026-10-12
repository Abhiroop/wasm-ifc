/-
Two programs, to see that the judgments are inhabited as intended: one that the rules type and
that runs, and one with an implicit flow that they reject.
-/
import WasmIfc.Noninterference

namespace WasmIfc

/-- Local variable 0 is secret; every other variable is public. -/
def exampleCtx : Ctx where
  locals := fun i => if i = 0 then Lab.H else Lab.L
  globals := fun _ => Lab.L
  funcs := []

/--
A constant, then a block that a `br_if` leaves if the secret local is not zero, then a write of
the constant to a public global. The write follows the block, so it happens in every run.
-/
def writeAfterBlock : List Instr :=
  [.const 7, .block [] [] [.localGet 0, .brIf 0, .nop], .globalSet 0]

/-- It is typed under a public pc: after the block the pc is public again. -/
example : Typed exampleCtx [[]] writeAfterBlock [Lab.L] [] [Lab.L] [] := by
  refine .const 7 (Typed.block (tin := []) (st := [Lab.L]) (p := Lab.H) (P1 := [Lab.L]) .nil
    (fun _ h => nomatch h) ?_ ?_)
  · refine .localGet 0 (Typed.brIf (rs := []) (carried := []) (st := []) rfl
      (fun _ h => nomatch h) .nil (.nop .nil))
  · exact .globalSet 0 (fun h => nomatch h) (fun h => nomatch h) .nil

/-- A run in which the branch is taken, and one in which it is not: both write 7. -/
example (s : State) (h : s.loc 0 = 5) :
    Eval [] 5 [0] writeAfterBlock [] s (.normal [] (s.setGlob 0 7)) := by
  refine .const 7 (Eval.blockCont (n1 := 2) (n2 := 1) (vs := []) (base := [7])
    (ob := .br 0 [] s) (σ1 := []) (s1 := s) rfl ?_ rfl (.globalSet 0 .nil))
  refine .localGet 0 ?_
  rw [h]
  exact Eval.brIfTaken (ls := [0, 0]) (i := 0) (n := 0) (c := 5) (σ := []) (by decide) rfl

example (s : State) (h : s.loc 0 = 0) :
    Eval [] 6 [0] writeAfterBlock [] s (.normal [] (s.setGlob 0 7)) := by
  refine .const 7 (Eval.blockCont (n1 := 3) (n2 := 1) (vs := []) (base := [7])
    (ob := .normal [] s) (σ1 := []) (s1 := s) rfl ?_ rfl (.globalSet 0 .nil))
  refine .localGet 0 ?_
  rw [h]
  exact .brIfNot (.nop .nil)

/-- The same write inside the block, after the branch, depends on the secret. -/
def writeInsideBlock : List Instr :=
  [.block [] [] [.localGet 0, .brIf 0, .const 7, .globalSet 0]]

/-- What a typing of a block says, with the segment's type as a variable. -/
theorem block_typed_inv {C : Ctx} {Ls : List STy} {ps rs : STy} {body rest : List Instr}
    {P P' : Pcs} {st st' : STy} (h : Typed C Ls (.block ps rs body :: rest) P st P' st') :
    ∃ pc Pr p P1, P = pc :: Pr ∧ Typed C (rs :: Ls) body (pc :: pc :: Pr) ps (p :: P1) rs := by
  cases h with
  | block _ _ hbody _ => exact ⟨_, _, _, _, rfl, hbody⟩

/-- What a typing of a `br_if` says of the code after it. -/
theorem brIf_typed_inv {C : Ctx} {Ls : List STy} {i : Nat} {rest : List Instr}
    {P P' : Pcs} {st st' : STy} (h : Typed C Ls (.brIf i :: rest) P st P' st') :
    ∃ pc Pr l st1, P = pc :: Pr ∧ st = l :: st1 ∧
      Typed C Ls rest (raise (pc.join l) (pc :: Pr) i) st1 P' st' := by
  cases h with
  | brIf _ _ _ hrest => exact ⟨_, _, _, _, rfl, rfl, hrest⟩

/-- It is not typed, at any pc, with any result: the write is under a secret pc. -/
example (pc : Lab) (P' : Pcs) (st st' : STy) :
    ¬ Typed exampleCtx [[]] writeInsideBlock [pc] st P' st' := by
  intro h
  obtain ⟨pc', Pr, p, P1, hP, hbody⟩ := block_typed_inv h
  cases hP
  cases hbody with
  | localGet _ h1 =>
    obtain ⟨pc', Pr, l, st1, hP, hst, h2⟩ := brIf_typed_inv h1
    cases hP
    cases hst
    simp only [raise] at h2
    cases h2 with
    | const _ h3 =>
      cases h3 with
      | globalSet _ hpc _ _ =>
        have hH : Lab.le Lab.H Lab.L := by
          cases pc <;> simpa [Lab.join, exampleCtx] using hpc
        exact absurd (hH rfl) (by decide)

/-! ### Memory -/

/-- Store the secret local at address 0 in a cell labelled secret, and read it back as a secret. -/
def storeSecret : List Instr :=
  [.const 0, .localGet 0, .store Lab.H, .const 0, .load Lab.H, .drop]

example : Typed exampleCtx [[]] storeSecret [Lab.L] [] [Lab.L] [] :=
  .const 0 (.localGet 0 (.store Lab.H (fun _ => rfl) (.const 0 (.load Lab.H (.drop .nil)))))

/-- The run: the cell holds the secret and is labelled so, and the load's check passes. -/
example (s : State) :
    Eval [] 6 [0] storeSecret [] s (.normal [] (s.setMem 0 (s.loc 0) Lab.H)) :=
  .const 0 (.localGet 0 (.store Lab.H (.const 0 (.load Lab.H (by simp [State.setMem, Lab.le])
    (.drop .nil)))))

/-- The same store into a cell labelled public is not typed. -/
example (pc : Lab) (P' : Pcs) (st' : STy) :
    ¬ Typed exampleCtx [[]] [.const 0, .localGet 0, .store Lab.L] [pc] [] P' st' := by
  intro h
  cases h with
  | const _ h1 =>
    cases h1 with
    | localGet _ h2 =>
      cases h2 with
      | store _ hle _ =>
        have hH : Lab.le Lab.H Lab.L := by
          cases pc <;> simpa [Lab.join, exampleCtx] using hle
        exact absurd (hH rfl) (by decide)

/-! ### A module of two functions -/

/-- Function 0 returns its public parameter; function 1 calls it on a constant. -/
def identity : Func := { ty := ⟨[Lab.L], Lab.L, [Lab.L]⟩, extra := [], body := [.localGet 0] }

def callsIdentity : Func :=
  { ty := ⟨[], Lab.L, [Lab.L]⟩, extra := [], body := [.const 3, .call 0] }

def moduleCtx : Ctx where
  locals := fun _ => Lab.L
  globals := fun _ => Lab.L
  funcs := [identity.ty, callsIdentity.ty]

example : WellTyped moduleCtx [identity, callsIdentity] := by
  intro i f hf
  match i, hf with
  | 0, hf =>
    cases hf
    exact ⟨rfl, _, .localGet 0 .nil⟩
  | 1, hf =>
    cases hf
    exact ⟨rfl, _, .const 3 (Typed.call (ft := identity.ty) (targs := [Lab.L]) (st := []) rfl
      (Lab.le_refl _) (SFlows.refl _) .nil)⟩
  | i + 2, hf => simp at hf

end WasmIfc
