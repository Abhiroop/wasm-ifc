/-
The three programs of the paper's findings. The first leaks, and SecWasm's printed rule for
`br_table` accepts it (`SecWasmPrinted.lean`): here it is shown to have no typing, and to have
two runs that differ in a public global. The other two are secure programs that SecWasm's
rules for `call` and `br_if` reject: here each is typed. The theorems under the paper's names
are about `Typed`, the judgment with value types (`ValueTypes.lean`); those with the suffix
`_labels` are about its label part, `LTyped`.
-/
import WasmIfc.ValueTypes

namespace WasmIfc

/-- Local variable 0 is a secret `i32`. Global 0 is a public `i32`, not preserved. No functions. -/
def leakTypedCtx : VCtx where
  locals := fun i => (.i32, if i = 0 then Lab.H else Lab.L)
  globals := fun _ => (.i32, Lab.L)
  preserved := fun _ => False
  funcs := []
  table := fun _ => Lab.L
  tags := []
  addr := fun _ => .i32
  taddr := fun _ => .i32

/-- The same with the types forgotten: the context of `LTyped`, and of SecWasm's printed rules. -/
def leakCtx : Ctx := leakTypedCtx.erase

/-! ### (a) The leak that the printed rule for `br_table` accepts -/

/--
Four nested blocks. The innermost branches on the secret local: index 0 leaves the innermost
block, every other index leaves all four. A write of 1 to the public global follows the third
block inside the fourth, so it happens exactly if the secret is 0.

    (block (block (block (block (br_table 0 3 (local.get 0))))) (global.set 0 (i32.const 1)))
-/
def leak : List Instr :=
  [.block [] [] []
    [.block [] [] [] [.block [] [] [] [.block [] [] [] [.localGet 0, .brTable [0] 3]]],
     .const 1, .globalSet 0]]

/-- What a typing of a block says: of its body, and of the code after it. -/
theorem block_typed_parts {C : Ctx} {Ls : List STy} {keep : List Nat} {ps rs : STy}
    {body rest : List Instr} {P P' : Pcs} {st st' : STy}
    (h : LTyped C Ls (.block keep ps rs body :: rest) P st P' st') :
    ∃ pc Pr p P1 st1, P = pc :: Pr ∧ LTyped C (rs :: Ls) body (pc :: pc :: Pr) ps (p :: P1) rs ∧
      LTyped C Ls rest P1 st1 P' st' := by
  cases h with
  | block _ _ _ hbody hrest => exact ⟨_, _, _, _, _, rfl, hbody, hrest⟩

/-- What a typing of an empty sequence says. -/
theorem nil_typed_parts {C : Ctx} {Ls : List STy} {P P' : Pcs} {st st' : STy}
    (h : LTyped C Ls [] P st P' st') : P' = P := by
  cases h
  rfl

/-- What a typing of a `br_table` says: the pcs are raised down to a depth that no target exceeds. -/
theorem brTable_typed_parts {C : Ctx} {Ls : List STy} {ts : List Nat} {d : Nat}
    {rest : List Instr} {P P' : Pcs} {st st' : STy}
    (h : LTyped C Ls (.brTable ts d :: rest) P st P' st') :
    ∃ pc Pr l st1 k, P = pc :: Pr ∧ st = l :: st1 ∧ (∀ t, t ∈ d :: ts → t ≤ k) ∧
      P' = raise (pc.join l) (pc :: Pr) k := by
  cases h with
  | brTable htargets _ _ => exact ⟨_, _, _, _, _, rfl, rfl, fun t ht => (htargets t ht).2, rfl⟩

/-- A secret raised down to depth 3 or more makes the first four of five public pcs secret. -/
theorem raise_four {k : Nat} (h : 3 ≤ k) :
    ∃ p, raise Lab.H [Lab.L, Lab.L, Lab.L, Lab.L, Lab.L] k = [Lab.H, Lab.H, Lab.H, Lab.H, p] := by
  match k, h with
  | 3, _ => exact ⟨_, rfl⟩
  | k + 4, _ => cases k <;> exact ⟨_, rfl⟩

/--
The leak has no typing in SecWasm+ from a public pc, for any labels around it, any segment
before it, and any pc stack and segment after it: the pc of the third block is secret after
the `br_table`, and the write to the public global follows that block.
-/
theorem leak_not_typed_labels (Ls : List STy) (st : STy) (P' : Pcs) (st' : STy) :
    ¬ LTyped leakCtx Ls leak [Lab.L] st P' st' := by
  intro h
  obtain ⟨_, _, _, _, _, hP, h3, _⟩ := block_typed_parts h
  cases hP
  obtain ⟨_, _, p2, P2, _, hP, h2, hwrite⟩ := block_typed_parts h3
  cases hP
  obtain ⟨_, _, p1, P1, _, hP, h1, hend2⟩ := block_typed_parts h2
  cases hP
  obtain ⟨_, _, p0, P0, _, hP, h0, hend1⟩ := block_typed_parts h1
  cases hP
  have e2 := nil_typed_parts hend2
  have e1 := nil_typed_parts hend1
  cases h0 with
  | localGet _ hbranch =>
    obtain ⟨_, _, _, _, k, hP, hst, htargets, hout⟩ := brTable_typed_parts hbranch
    cases hP
    cases hst
    obtain ⟨p, hp⟩ := raise_four (htargets 3 (by simp))
    rw [show Lab.L.join ((leakCtx.locals 0).join Lab.L) = Lab.H from rfl, hp] at hout
    cases hout
    cases e1
    cases e2
    cases hwrite with
    | const _ hset =>
      cases hset with
      | globalSet _ _ hpc _ _ => exact absurd (hpc rfl) (by decide)
      | globalSetPreserved _ hpres _ _ => exact hpres

/-- The leak has no typing with value types either: one would be a typing without them. -/
theorem leak_not_typed (Ls : List VSTy) (st : VSTy) (P' : Pcs) (st' : VSTy) :
    ¬ Typed leakTypedCtx Ls leak [Lab.L] st P' st' :=
  fun h => leak_not_typed_labels _ _ _ _ h.erase

/-- An index that is not 0 takes the table's default. -/
theorem tableTarget_default {c : Nat} (h : c ≠ 0) : tableTarget [0] 3 c = 3 := by
  match c, h with
  | c + 1, _ => simp [tableTarget]

/--
Two runs of the leak, from states whose secret local is 0 and is not 0: the first ends with 1
in the public global, the second with the global as it was. The states may agree on everything
but the secret local.
-/
theorem leak_runs_differ (ls : List Nat) (s t : State) (hs : s.loc 0 = 0) (ht : t.loc 0 ≠ 0) :
    Eval [] 8 ls leak [] s (.normal [] (s.setGlob 0 1)) ∧ Eval [] 6 ls leak [] t (.normal [] t) := by
  constructor
  · refine Eval.blockCont (n1 := 7) (n2 := 0) (vs := []) (base := []) (ob := .normal [] (s.setGlob 0 1))
      rfl ?_ rfl (fun _ h => nomatch h) .nil
    refine Eval.blockCont (n1 := 4) (n2 := 2) (vs := []) (base := []) (ob := .normal [] s)
      rfl ?_ rfl (fun _ h => nomatch h) (.const 1 (.globalSet 0 .nil))
    refine Eval.blockCont (n1 := 3) (n2 := 0) (vs := []) (base := []) (ob := .normal [] s)
      rfl ?_ rfl (fun _ h => nomatch h) .nil
    refine Eval.blockCont (n1 := 2) (n2 := 0) (vs := []) (base := []) (ob := .br 0 [] s)
      rfl ?_ rfl (fun _ h => nomatch h) .nil
    refine .localGet 0 ?_
    rw [hs]
    exact Eval.brTable (ts := [0]) (d := 3) (c := 0) (n := 0) (σ := []) rfl
  · refine Eval.blockCont (n1 := 5) (n2 := 0) (vs := []) (base := []) (ob := .br 0 [] t)
      rfl ?_ rfl (fun _ h => nomatch h) .nil
    refine Eval.blockExit (n1 := 4) (vs := []) (base := []) (ob := .br 1 [] t) rfl ?_ rfl
    refine Eval.blockExit (n1 := 3) (vs := []) (base := []) (ob := .br 2 [] t) rfl ?_ rfl
    refine Eval.blockExit (n1 := 2) (vs := []) (base := []) (ob := .br 3 [] t) rfl ?_ rfl
    refine .localGet 0 ?_
    have hrun := Eval.brTable (F := []) (ls := 0 :: 0 :: 0 :: 0 :: ls) (rest := []) (ts := [0])
      (d := 3) (c := t.loc 0) (n := 0) (σ := []) (s := t) (by rw [tableTarget_default ht]; rfl)
    rw [tableTarget_default ht] at hrun
    exact hrun

/--
The public global after the two runs, from states that agree on it: 1 after the first, and
what it held after the second. The final states differ on it unless it held 1.
-/
theorem leak_runs_globals (s t : State) (h : s.glob 0 = t.glob 0) :
    (s.setGlob 0 1).glob 0 = 1 ∧ t.glob 0 = s.glob 0 := by
  simp [State.setGlob, h]

/-! ### (b) Secure, and rejected by SecWasm's rule for `call` -/

/--
Local 0 is a secret `i32`, and function 0 takes a public `i32` under a secret pc and returns
nothing.
-/
def callTypedCtx : VCtx where
  locals := fun i => (.i32, if i = 0 then Lab.H else Lab.L)
  globals := fun _ => (.i32, Lab.L)
  preserved := fun _ => False
  funcs := [⟨[(.i32, Lab.L)], Lab.H, []⟩]
  table := fun _ => Lab.L
  tags := []
  addr := fun _ => .i32
  taddr := fun _ => .i32

/--
A public constant, then a block that takes it: a `br_if` on the secret local leaves the block,
and otherwise the function is called on the constant. The argument is public and was pushed
before the secret decided anything.

    const 7; block (param L) [local.get 0; br_if 0; call 0]
-/
def callAfterSecretBranch : List Instr :=
  [.const 7, .block [] [Lab.L] [] [.localGet 0, .brIf 0, .call 0]]

/-- It is typed under a public pc: the argument keeps its public label under the secret pc. -/
theorem call_after_secret_branch_typed :
    Typed callTypedCtx [[]] callAfterSecretBranch [Lab.L] [] [Lab.L] [] := by
  refine .const .i32 7 (Typed.block (tin := [(.i32, Lab.L)]) (ps := [(.i32, Lab.L)]) (rs := [])
    (st := []) (p := Lab.H) (P1 := [Lab.L]) (.cons (fun h => h) .nil) (fun _ h => nomatch h)
    (.inr (fun _ h => nomatch h)) ?_ .nil)
  refine .localGet 0 (Typed.brIf (rs := []) (carried := []) (st := [(.i32, Lab.L)]) rfl
    (fun _ h => nomatch h) .nil ?_)
  exact Typed.call (ft := ⟨[(.i32, Lab.L)], Lab.H, []⟩) (targs := [(.i32, Lab.L)]) (st := []) rfl
    (fun _ => rfl) (.cons (fun h => h) .nil) .nil

theorem call_after_secret_branch_typed_labels :
    LTyped callTypedCtx.erase [[]] callAfterSecretBranch [Lab.L] [] [Lab.L] [] :=
  call_after_secret_branch_typed.erase

/-! ### (c) Secure, and rejected by SecWasm's rule for `br_if` -/

/-- Local 0 (the condition) and local 1 are public `i32`s; local 2 is a secret one. -/
def branchTypedCtx : VCtx where
  locals := fun i => (.i32, if i = 2 then Lab.H else Lab.L)
  globals := fun _ => (.i32, Lab.L)
  preserved := fun _ => False
  funcs := []
  table := fun _ => Lab.L
  tags := []
  addr := fun _ => .i32
  taddr := fun _ => .i32

/--
A block with a secret result. A `br_if` on the public condition leaves it with a public
constant; otherwise the constant is written to the public local, and the secret local is the
result. The constant is public where it is written, although the label it would be carried
to is secret.

    block (result H) [const 7; local.get 0; br_if 0; local.set 1; local.get 2; br 0]
-/
def writeAfterPublicBranch : List Instr :=
  [.block [] [] [Lab.H] [.const 7, .localGet 0, .brIf 0, .localSet 1, .localGet 2, .br 0]]

/-- It is typed under a public pc: a `br_if` that is not taken leaves the labels of what it would carry. -/
theorem write_after_public_branch_typed :
    Typed branchTypedCtx [[]] writeAfterPublicBranch [Lab.L] [] [Lab.L] [(.i32, Lab.H)] := by
  refine Typed.block (tin := []) (ps := []) (rs := [(.i32, Lab.H)]) (st := []) (p := Lab.L)
    (P1 := [Lab.L]) .nil (fun _ _ h => nomatch h) (.inl (fun _ _ h => nomatch h)) ?_ .nil
  refine .const .i32 7 (.localGet 0 (Typed.brIf (rs := [(.i32, Lab.H)]) (carried := [(.i32, Lab.L)])
    (st := []) rfl (fun _ _ h => nomatch h) (.cons (fun _ => rfl) .nil) ?_))
  refine .localSet 1 (fun h => nomatch h) (fun h => nomatch h) (.localGet 2 ?_)
  exact Typed.br (rs := [(.i32, Lab.H)]) (carried := [(.i32, Lab.H)]) (st := []) rfl
    (fun _ _ h => nomatch h) (.cons (fun h => h) .nil)

theorem write_after_public_branch_typed_labels :
    LTyped branchTypedCtx.erase [[]] writeAfterPublicBranch [Lab.L] [] [Lab.L] [Lab.H] :=
  write_after_public_branch_typed.erase

end WasmIfc
