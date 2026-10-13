/-
Two programs, to see that the judgments are inhabited as intended: one that the rules type and
that runs, and one with an implicit flow that they reject.
-/
import WasmIfc.Machine

namespace WasmIfc

/-- Local variable 0 is secret; every other variable is public. -/
def exampleCtx : Ctx where
  locals := fun i => if i = 0 then Lab.H else Lab.L
  globals := fun _ => Lab.L
  preserved := fun _ => False
  funcs := []
  table := fun _ => Lab.L
  tags := []

/--
A constant, then a block that a `br_if` leaves if the secret local is not zero, then a write of
the constant to a public global. The write follows the block, so it happens in every run.
-/
def writeAfterBlock : List Instr :=
  [.const 7, .block [] [] [] [.localGet 0, .brIf 0, .nop], .globalSet 0]

/-- It is typed under a public pc: after the block the pc is public again. -/
example : Typed exampleCtx [[]] writeAfterBlock [Lab.L] [] [Lab.L] [] := by
  refine .const 7 (Typed.block (tin := []) (st := [Lab.L]) (p := Lab.H) (P1 := [Lab.L]) .nil
    (fun _ h => nomatch h) (.inr (fun _ h => nomatch h)) ?_ ?_)
  · refine .localGet 0 (Typed.brIf (rs := []) (carried := []) (st := []) rfl
      (fun _ h => nomatch h) .nil (.nop .nil))
  · exact .globalSet 0 (fun h => h) (fun h => nomatch h) (fun h => nomatch h) .nil

/-- A run in which the branch is taken, and one in which it is not: both write 7. -/
example (s : State) (h : s.loc 0 = 5) :
    Eval [] 5 [0] writeAfterBlock [] s (.normal [] (s.setGlob 0 7)) := by
  refine .const 7 (Eval.blockCont (n1 := 2) (n2 := 1) (vs := []) (base := [7])
    (ob := .br 0 [] s) (σ1 := []) (s1 := s) rfl ?_ rfl (fun _ h => nomatch h) (.globalSet 0 .nil))
  refine .localGet 0 ?_
  rw [h]
  exact Eval.brIfTaken (ls := [0, 0]) (i := 0) (n := 0) (c := 5) (σ := []) (by decide) rfl

example (s : State) (h : s.loc 0 = 0) :
    Eval [] 6 [0] writeAfterBlock [] s (.normal [] (s.setGlob 0 7)) := by
  refine .const 7 (Eval.blockCont (n1 := 3) (n2 := 1) (vs := []) (base := [7])
    (ob := .normal [] s) (σ1 := []) (s1 := s) rfl ?_ rfl (fun _ h => nomatch h) (.globalSet 0 .nil))
  refine .localGet 0 ?_
  rw [h]
  exact .brIfNot (.nop .nil)

/-- The same write inside the block, after the branch, depends on the secret. -/
def writeInsideBlock : List Instr :=
  [.block [] [] [] [.localGet 0, .brIf 0, .const 7, .globalSet 0]]

/-- What a typing of a block says, with the segment's type as a variable. -/
theorem block_typed_inv {C : Ctx} {Ls : List STy} {keep : List Nat} {ps rs : STy}
    {body rest : List Instr} {P P' : Pcs} {st st' : STy}
    (h : Typed C Ls (.block keep ps rs body :: rest) P st P' st') :
    ∃ pc Pr p P1, P = pc :: Pr ∧ Typed C (rs :: Ls) body (pc :: pc :: Pr) ps (p :: P1) rs := by
  cases h with
  | block _ _ _ hbody _ => exact ⟨_, _, _, _, rfl, hbody⟩

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
      | globalSet _ _ hpc _ _ =>
        have hH : Lab.le Lab.H Lab.L := by
          cases pc <;> simpa [Lab.join, exampleCtx] using hpc
        exact absurd (hH rfl) (by decide)
      | globalSetPreserved _ hpi _ _ => exact hpi

/-! ### An operation that traps -/

/-- Division of natural numbers, not defined for the divisor 0. -/
def divide (a b : Nat) : Option Nat := if b = 0 then none else some (a / b)

/-- 6 divided by 2 runs and leaves 3. -/
example (s : State) : Eval [] 3 [0] [.const 6, .const 2, .partialBinop divide] [] s (.normal [3] s) :=
  .const 6 (.const 2 (.partialBinop divide rfl .nil))

/-- 6 divided by 0 has no evaluation, of any size and with any outcome: the run traps. -/
example (s : State) (n : Nat) (o : Out) :
    ¬ Eval [] n [0] [.const 6, .const 0, .partialBinop divide] [] s o := by
  intro h
  cases h with
  | const _ h1 =>
    cases h1 with
    | const _ h2 =>
      cases h2 with
      | partialBinop _ hv _ => simp [divide] at hv

/-- The quotient of a secret is secret, and the division is typed as any operation on two values. -/
example : Typed exampleCtx [[]] [.const 6, .localGet 0, .partialBinop divide, .drop] [Lab.L] [] [Lab.L] [] :=
  .const 6 (.localGet 0 (.partialBinop divide (.drop .nil)))

/-! ### Memory -/

/-- Store the secret local in four bytes at address 0, labelled secret, and read it back as a secret. -/
def storeSecret : List Instr :=
  [.const 0, .localGet 0, .store 4 Lab.H, .const 0, .load 4 Lab.H, .drop]

example : Typed exampleCtx [[]] storeSecret [Lab.L] [] [Lab.L] [] :=
  .const 0 (.localGet 0 (.store 4 Lab.H (fun _ => rfl) (.const 0 (.load 4 Lab.H (.drop .nil)))))

/-- The run: the four bytes hold the secret and are labelled so, and the load's check passes. -/
example (s : State) (hs : 4 ≤ s.size) :
    Eval [] 6 [0] storeSecret [] s (.normal [] (s.put 0 (bytesOf (s.loc 0) 4) Lab.H)) :=
  .const 0 (.localGet 0 (.store 4 Lab.H (by omega) (.const 0 (.load 4 Lab.H (by simpa [State.put] using hs)
    (fun _ _ _ => rfl) (.drop .nil)))))

/-- The same store into a cell labelled public is not typed. -/
example (pc : Lab) (P' : Pcs) (st' : STy) :
    ¬ Typed exampleCtx [[]] [.const 0, .localGet 0, .store 4 Lab.L] [pc] [] P' st' := by
  intro h
  cases h with
  | const _ h1 =>
    cases h1 with
    | localGet _ h2 =>
      cases h2 with
      | store _ _ hle _ =>
        have hH : Lab.le Lab.H Lab.L := by
          cases pc <;> simpa [Lab.join, exampleCtx] using hle
        exact absurd (hH rfl) (by decide)

/-! ### Two tables -/

/-- Table 0 is public and table 1 is secret. -/
def tablesCtx : Ctx where
  locals := fun _ => Lab.L
  globals := fun _ => Lab.L
  preserved := fun _ => False
  funcs := []
  table := fun x => if x = 0 then Lab.L else Lab.H
  tags := []

/-- One entry copied from the public table to the secret one is typed. -/
example : Typed tablesCtx [[]] [.const 0, .const 0, .const 1, .tableCopy 1 0] [Lab.L] [] [Lab.L] [] :=
  .const 0 (.const 0 (.const 1 (.tableCopy 1 0 (fun _ => rfl) .nil)))

/-- The copy from the secret table to the public one is not typed, at any pc. -/
example (pc : Lab) (P' : Pcs) (st' : STy) :
    ¬ Typed tablesCtx [[]] [.const 0, .const 0, .const 1, .tableCopy 0 1] [pc] [] P' st' := by
  intro h
  cases h with
  | const _ h1 =>
    cases h1 with
    | const _ h2 =>
      cases h2 with
      | const _ h3 =>
        cases h3 with
        | tableCopy _ _ hle _ =>
          have hH : Lab.le Lab.H Lab.L := by
            cases pc <;> simpa [Lab.join, tablesCtx] using hle
          exact absurd (hH rfl) (by decide)

/--
A run: the first reference of element segment 0 goes to entry 0 of table 1, and the segment
is dropped. It needs the table to have an entry and the segment a reference.
-/
example (s : State) (htable : 1 ≤ s.tsize 1) (hsegment : 1 ≤ (s.elems 0).length) :
    Eval [] 5 [0] [.const 0, .const 0, .const 1, .tableInit 1 0, .elemDrop 0] [] s
      (.normal [] ((s.initTbl 1 0 0 0 1).dropElem 0)) :=
  .const 0 (.const 0 (.const 1 (.tableInit 1 0 (by omega) (by omega) (.elemDrop 0 .nil))))

/-! ### A module of two functions -/

/-- Function 0 returns its public parameter; function 1 calls it on a constant. -/
def identity : Func :=
  { ty := ⟨[Lab.L], Lab.L, [Lab.L]⟩, extra := [], keep := [], body := [.localGet 0] }

def callsIdentity : Func :=
  { ty := ⟨[], Lab.L, [Lab.L]⟩, extra := [], keep := [], body := [.const 3, .call 0] }

def moduleCtx : Ctx where
  locals := fun _ => Lab.L
  globals := fun _ => Lab.L
  preserved := fun _ => False
  funcs := [identity.ty, callsIdentity.ty]
  table := fun _ => Lab.L
  tags := []

example : WellTyped moduleCtx [identity, callsIdentity] := by
  intro i f hf
  match i, hf with
  | 0, hf =>
    cases hf
    exact ⟨rfl, _, .localGet 0 .nil, .inl rfl⟩
  | 1, hf =>
    cases hf
    exact ⟨rfl, _, .const 3 (Typed.call (ft := identity.ty) (targs := [Lab.L]) (st := []) rfl
      (Lab.le_refl _) (SFlows.refl _) .nil), .inl rfl⟩
  | i + 2, hf => simp at hf

/-- A function body that keeps a copy of its result in a local and returns. -/
example : Typed moduleCtx [[Lab.L]] [.const 3, .localTee 0, .ret] [Lab.L] [] [Lab.L] [Lab.L] :=
  .const 3 (.localTee 0 (fun h => nomatch h) (fun h => nomatch h)
    (Typed.ret (rs := [Lab.L]) (carried := [Lab.L]) (st := []) rfl (fun _ _ h => nomatch h)
      (SFlows.refl _)))

example (s : State) :
    Eval [] 3 [1] [.const 3, .localTee 0, .ret] [] s (.br 0 [3] (s.setLoc 0 3)) :=
  .const 3 (.localTee 0 (Eval.ret (n := 1) rfl))

/-! ### A preserved global -/

/-- Global 0 is preserved, as the stack pointer of compiled C is; local 0 is secret. -/
def frameCtx : Ctx where
  locals := fun i => if i = 0 then Lab.H else Lab.L
  globals := fun _ => Lab.L
  preserved := fun i => i = 0
  funcs := []
  table := fun _ => Lab.L
  tags := []

/-- What the secret selects: move the global, and put it back. -/
def moves : List Instr := [.globalGet 0, .const 16, .globalSet 0, .globalSet 0]

/--
If the secret local is not zero, move the global and put it back, as the prologue and the
epilogue of a function called there do. The conditional compares global 0.
-/
def moveAndRestore (keep : List Nat) : List Instr := [.localGet 0, .ite keep [] [] moves []]

/-- It is typed: the writes are under a secret pc, and the conditional compares the global. -/
example : Typed frameCtx [[]] (moveAndRestore [0]) [Lab.L] [] [Lab.L] [] := by
  refine .localGet 0 (Typed.ite (tin := []) (st := []) (p1 := Lab.H) (P1 := [Lab.L])
    (p2 := Lab.H) (P2 := [Lab.L]) .nil (fun _ h => nomatch h)
    (.inr (fun i (hi : i = 0) => by simp [hi])) ?_ .nil .nil)
  exact .globalGet 0 (.const 16 (.globalSetPreserved 0 rfl (fun _ => rfl)
    (.globalSetPreserved 0 rfl (fun _ => rfl) .nil)))

/-- A run that takes the branch: the global is moved and restored, and the comparison passes. -/
example (s : State) (h : s.loc 0 = 5) :
    Eval [] 6 [0] (moveAndRestore [0]) [] s
      (.normal [] ((s.setGlob 0 16).setGlob 0 (s.glob 0))) := by
  refine .localGet 0 ?_
  rw [h]
  refine Eval.iteCont (n1 := 4) (n2 := 0) (vs := []) (base := [])
    (ob := .normal [] ((s.setGlob 0 16).setGlob 0 (s.glob 0))) rfl ?_ rfl ?_ .nil
  · exact .globalGet 0 (.const 16 (.globalSet 0 (.globalSet 0 .nil)))
  · intro i hi
    simp at hi
    subst hi
    simp [State.setGlob]

/-- What a typing of a conditional says, with the segment's type as a variable. -/
theorem ite_typed_inv {C : Ctx} {Ls : List STy} {keep : List Nat} {ps rs : STy}
    {thn els rest : List Instr} {P P' : Pcs} {st st' : STy}
    (h : Typed C Ls (.ite keep ps rs thn els :: rest) P st P' st') :
    ∃ pc Pr l st1 p1 P1 p2 P2, P = pc :: Pr ∧ st = l :: st1 ∧
      Restores C (p1.join p2) (joinEach P1 P2) keep ∧
      Typed C (rs :: Ls) thn (pc.join l :: pc :: Pr) ps (p1 :: P1) rs ∧
      Typed C (rs :: Ls) els (pc.join l :: pc :: Pr) ps (p2 :: P2) rs := by
  cases h with
  | ite _ _ hres h1 h2 _ => exact ⟨_, _, _, _, _, _, _, _, rfl, rfl, hres, h1, h2⟩

/-- Without the comparison it is not typed: the pc drops after the conditional. -/
example (P' : Pcs) (st' : STy) : ¬ Typed frameCtx [[]] (moveAndRestore []) [Lab.L] [] P' st' := by
  intro h
  cases h with
  | localGet _ h1 =>
    obtain ⟨pc, Pr, l, st1, p1, P1, p2, P2, hP, hst, hres, hthn, hels⟩ := ite_typed_inv h1
    cases hP
    cases hst
    cases hels
    have hp1 : p1 = Lab.H := (rise hthn).head rfl
    have hP1 : P1 = [Lab.L] := by
      cases hthn with
      | globalGet _ a =>
        cases a with
        | const _ b =>
          cases b with
          | globalSet _ hnp _ _ _ => exact absurd rfl hnp
          | globalSetPreserved _ _ _ c =>
            cases c with
            | globalSet _ hnp _ _ _ => exact absurd rfl hnp
            | globalSetPreserved _ _ _ d => cases d; rfl
    subst hp1 hP1
    rcases hres with hr | hc
    · exact absurd (hr Lab.L rfl rfl) (by decide)
    · exact absurd (hc 0 rfl) (by simp)

/-! ### Exceptions -/

/-- Tag 0 carries one value; local 0 is secret. -/
def tagCtx : Ctx where
  locals := fun i => if i = 0 then Lab.H else Lab.L
  globals := fun _ => Lab.L
  preserved := fun _ => False
  funcs := []
  table := fun _ => Lab.L
  tags := [1]

/-- Throw 5 in a `try_table` whose clause for the tag branches to the function's label. -/
def throwsAndCatches : List Instr :=
  [.tryTable [] [] [] [(some 0, 0, false)] [.const 5, .throw 0 1], .const 9]

example : Typed tagCtx [[Lab.L]] throwsAndCatches [Lab.L] [] [Lab.L] [Lab.L] := by
  refine Typed.tryTable (tin := []) (st := []) (p := Lab.L) (P1 := [Lab.L]) .nil
    (.inl (fun _ _ h => nomatch h)) (fun c hc => ?_) ?_ (.const 9 .nil)
  · simp at hc
    subst hc
    exact ⟨1, [Lab.L], rfl, rfl, rfl⟩
  · exact .const 5 (Typed.throw (args := [Lab.L]) (st := []) rfl rfl (by simp))

/-- The run: the exception is caught, and the function returns the value it carried. -/
example (s : State) : Eval [] 3 [1] throwsAndCatches [] s (.br 0 [5] s) :=
  Eval.tryExit (vs := []) (base := []) (ob := .exn 0 [5] s) rfl (.const 5 .throw) rfl

/-- An exception thrown where a secret decided is not typed: the pc there is secret. -/
example (P' : Pcs) (st' : STy) :
    ¬ Typed tagCtx [[]] [.localGet 0, .ite [] [] [] [.const 5, .throw 0 1] []] [Lab.L] [] P' st' := by
  intro h
  cases h with
  | localGet _ h1 =>
    obtain ⟨pc, Pr, l, st1, p1, P1, p2, P2, hP, hst, _, hthn, _⟩ := ite_typed_inv h1
    cases hP
    cases hst
    cases hthn with
    | const _ a => cases a

/-! ### Runs of the machine -/

/-- The function with the body above: no parameters, one public result. -/
def catcher : Func where
  ty := ⟨[], Lab.L, [Lab.L]⟩
  extra := []
  keep := []
  body := throwsAndCatches

/-- The comparison of a function that names no global. -/
theorem nothingKept {s t : State} : ∀ c, c ∈ [(([] : List Nat), s)] → Kept c.1 c.2 t := by
  intro c hc i hi
  cases List.mem_singleton.1 hc
  cases hi

/-- The machine's run of it, in four transitions: the clause's branch is the function's return. -/
example (s : State) : Runs [catcher] (Config.entry catcher [] s) (.returned [5] s) :=
  .go (.tryTable (vs := []) (base := []) rfl) <|
  .go (.basic (.const 5)) <|
  .go (.throw (.caught (j := 0) (carry := true) (r := false) rfl (.call nothingKept))) <|
  .stop .done

/-- So the big-step semantics has the same end for the call. -/
example (s : State) : Invoke [catcher] catcher [] s (.returned [5] s) :=
  refinement (.go (.tryTable (vs := []) (base := []) rfl) <|
    .go (.basic (.const 5)) <|
    .go (.throw (.caught (j := 0) (carry := true) (r := false) rfl (.call nothingKept))) <|
    .stop .done)

/-- A function that throws 5. -/
def thrower : Func where
  ty := ⟨[], Lab.L, [Lab.L]⟩
  extra := []
  keep := []
  body := [.const 5, .throw 0 1]

/-- A tail call of it in a `try_table` that catches every exception. -/
def tailCaller : Func where
  ty := ⟨[], Lab.L, [Lab.L]⟩
  extra := []
  keep := []
  body := [.tryTable [] [] [] [(none, 0, false)] [.retCall 0], .const 9]

/--
The exception leaves the call: the tail call replaced the function that had the `try_table`,
so nothing catches it.
-/
example (s : State) : Runs [thrower, tailCaller] (Config.entry tailCaller [] s) (.threw 0 [5] s) :=
  .go (.tryTable (vs := []) (base := []) rfl) <|
  .go (.retCall (args := []) (base := []) (f := thrower) rfl rfl rfl) <|
  .go (.basic (.const 5)) <|
  .stop (.throw (.pastCall .escaped))

/--
A `try_table` whose clause catches every exception by reference and branches to the block
around it, and after the block the exception is thrown again from the reference.
-/
def rethrower : Func where
  ty := ⟨[], Lab.L, []⟩
  extra := []
  keep := []
  body := [.block [] [] [Lab.L]
    [.tryTable [] [] [] [(none, 0, true)] [.const 5, .throw 0 1], .unreachable], .throwRef]

/-- The run from a state that keeps no exception: it keeps one at the end, which left the call. -/
example (s : State) :
    Runs [rethrower] (Config.entry rethrower [] { s with exns := [] })
      (.threw 0 [5] { s with exns := [(0, [5])] }) :=
  .go (.block (vs := []) (base := []) rfl) <|
  .go (.tryTable (vs := []) (base := []) rfl) <|
  .go (.basic (.const 5)) <|
  .go (.throw (.caught (j := 0) (carry := false) (r := true) rfl
    (.label (fun _ h => nomatch h)))) <|
  .stop (.throwRef (i := 0) rfl (.pastCall .escaped))

/-- Open the file with the empty name in the directory of descriptor 3, making it if need be. -/
def opener : Func where
  ty := ⟨[], Lab.L, [Lab.L]⟩
  extra := []
  keep := []
  body := [.const 3, .const 0, .const 0, .const 1, .const 0, .hostOpen]

/--
The run, from a state where descriptor 3 is to the channel 9 and descriptor 4 is free: the
status is 0, and descriptor 4 is to the file of that name in that directory.
-/
example (s : State) (hdir : s.fdt 3 = some 9) (hfree : s.fdt 4 = none) (hsize : 0 < s.size) :
    ∃ t, Runs [opener] (Config.entry opener [] s) (.returned [0] t) ∧
      t.fdt 4 = some (s.file 9 []) := by
  have hfresh : State.fresh { s with loc := frame [] } 4 :=
    ⟨by decide, hfree, fun j h1 h2 => by
      have hj : j = 3 := by omega
      subst hj
      simp [hdir]⟩
  refine ⟨_, .go (.basic (.const 3)) <| .go (.basic (.const 0)) <| .go (.basic (.const 0)) <|
    .go (.basic (.const 1)) <| .go (.basic (.const 0)) <|
    .go (.basic (.hostOpen (c := 9) (d := 4) hdir (Nat.zero_le _) hsize
      (fun x h1 h2 => absurd h2 (by omega)) (.inr rfl) hfresh)) <|
    .go (.endCall nothingKept) <| .stop .done, ?_⟩
  simp [State.openAt, State.setMem, State.cells]

end WasmIfc
