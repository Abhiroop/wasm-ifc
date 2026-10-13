/-
SecWasm's typing rules as printed (Bastys et al., full version, Fig. 13), for the five
instructions of the leak of `Findings.lean`: `const`, `local.get`, `global.set`, `block` and
`br_table`. The judgment is on a stack of stacks: one entry per enclosing block, each a
labelled type stack with a pc, and a branch lifts entries of it.

The printed rule for `br_table` lifts as many entries as the table has targets. The leak has
two targets, the deeper of which is the fourth block, so the printed rule leaves the pc of
the third block public, and types the write that follows it (`printed_rule_accepts_leak`).
With the lift down to the deepest target, as the rule for `br_if` lifts down to its target,
the leak has no typing (`repaired_rule_rejects_leak`). The two runs that differ on the public
global are `leak_runs_differ`, and SecWasm+ rejects the program by `leak_not_typed`.
-/
import WasmIfc.Findings

namespace WasmIfc
namespace SecWasm

/-- An entry of the stack of stacks: the labelled type stack of a block, top first, and its pc. -/
abbrev Entry := STy × Lab

/-- A stack of stacks, the innermost block first. -/
abbrev SoS := List Entry

/-- `lift a e` raises every label of the entry and its pc by `a`. -/
def lift (a : Lab) (e : Entry) : Entry := (e.1.map a.join, a.join e.2)

/-- The order on stacks of stacks: entry by entry, label by label and pc by pc. -/
inductive Below : SoS → SoS → Prop where
  | nil : Below [] []
  | cons {st st' : STy} {pc pc' : Lab} {γ γ' : SoS} :
      SFlows st st' → Lab.le pc pc' → Below γ γ' → Below ((st, pc) :: γ) ((st', pc') :: γ')

theorem Below.refl : ∀ γ : SoS, Below γ γ
  | [] => .nil
  | (st, _) :: γ => .cons (SFlows.refl st) (fun h => h) (Below.refl γ)

/-- The targets of `br_table ts d`, the default one last: the vector that the printed rule calls `i^m`. -/
def targets (ts : List Nat) (d : Nat) : List Nat := ts ++ [d]

/--
`Typed lifted C Ls e γ γ'`: under the labels `Ls`, the sequence `e` takes the stack of stacks
`γ` to `γ'`. Each rule types an instruction followed by the rest of its sequence, which is
the printed rule composed with T-Seq. The parameter `lifted` says how many entries below the
current one a `br_table` lifts, given its targets; everything else is as printed.
-/
inductive Typed (lifted : List Nat → Nat) (C : Ctx) : List STy → List Instr → SoS → SoS → Prop where
  | nil {Ls γ} : Typed lifted C Ls [] γ γ
  /-- T-Const -/
  | const {Ls rest st pc γ γ'} (n : Nat) :
      Typed lifted C Ls rest ((pc :: st, pc) :: γ) γ' →
      Typed lifted C Ls (.const n :: rest) ((st, pc) :: γ) γ'
  /-- T-Get-Local -/
  | localGet {Ls rest st pc γ γ'} (i : Nat) :
      Typed lifted C Ls rest (((C.locals i).join pc :: st, pc) :: γ) γ' →
      Typed lifted C Ls (.localGet i :: rest) ((st, pc) :: γ) γ'
  /-- T-Set-Global: the pc and the value's label flow into the global's -/
  | globalSet {Ls rest l st pc γ γ'} (i : Nat) :
      Lab.le (pc.join l) (C.globals i) →
      Typed lifted C Ls rest ((st, pc) :: γ) γ' →
      Typed lifted C Ls (.globalSet i :: rest) ((l :: st, pc) :: γ) γ'
  /--
  T-Block: the body is typed on a new entry with the block's parameters, above the current
  entry without them. After the block, the pc is joined with the pc that the body left in the
  current entry.
  -/
  | block {Ls rest keep ps rs body σ st pc γ pc' st' pc'' γ1 γ'} :
      σ = ps ++ st →
      Typed lifted C (rs :: Ls) body ((ps, pc) :: (st, pc) :: γ) ((rs, pc') :: (st', pc'') :: γ1) →
      Typed lifted C Ls rest ((rs ++ st', pc.join pc'') :: γ1) γ' →
      Typed lifted C Ls (.block keep ps rs body :: rest) ((σ, pc) :: γ) γ'
  /--
  T-Br-Table: every target has the same label type `st`, the entries below the current one
  may be raised (`γ ⊑ γ1`), and the pc and the index's label flow into what is carried. The
  current entry and the first `lifted (targets ts d)` entries below it are lifted by the pc
  and the index's label.
  -/
  | brTable {Ls rest ts d l σ st st' pc γ γ1 γ'} :
      σ = st ++ st' →
      (∀ t, t ∈ targets ts d → Ls[t]? = some st) →
      1 ≤ (targets ts d).length → lifted (targets ts d) ≤ γ.length →
      Below γ γ1 → AllGe (pc.join l) st →
      Typed lifted C Ls rest
        (lift (l.join pc) (σ, pc) :: ((γ1.take (lifted (targets ts d))).map (lift (l.join pc)) ++
          γ1.drop (lifted (targets ts d)))) γ' →
      Typed lifted C Ls (.brTable ts d :: rest) ((l :: σ, pc) :: γ) γ'

/-- The printed rule lifts `γ'[0 : m - 1]`, where `m` is the number of targets. -/
def printed (targets : List Nat) : Nat := targets.length

/-- The repair lifts down to the deepest target, as T-Br-If lifts `γ'[0 : i - 1]` for its target `i`. -/
def repaired (targets : List Nat) : Nat := targets.foldr max 0

/--
The printed rules type the leak as a function body (T-Func: one entry with an empty stack, no
labels, here with a public bound and no results). The `br_table` has two targets, so the lift
covers the first and the second block, and the third block's pc stays public.
-/
theorem printed_rule_accepts_leak :
    Typed printed leakCtx [] leak [([], Lab.L)] [([], Lab.L)] := by
  refine Typed.block (st := []) (pc' := Lab.L) (st' := []) (pc'' := Lab.L) (γ1 := []) rfl ?_ .nil
  refine Typed.block (st := []) (pc' := Lab.H) (st' := []) (pc'' := Lab.L) (γ1 := [([], Lab.L)]) rfl ?_
    (.const 1 (.globalSet 0 (fun h => nomatch h) .nil))
  refine Typed.block (st := []) (pc' := Lab.H) (st' := []) (pc'' := Lab.H)
    (γ1 := [([], Lab.L), ([], Lab.L)]) rfl ?_ .nil
  refine Typed.block (st := []) (pc' := Lab.H) (st' := []) (pc'' := Lab.H)
    (γ1 := [([], Lab.H), ([], Lab.L), ([], Lab.L)]) rfl ?_ .nil
  refine .localGet 0 (Typed.brTable (st := []) (st' := []) rfl ?_ (by decide) (by decide)
    (Below.refl _) (fun _ h => nomatch h) .nil)
  intro t ht
  have : t = 0 ∨ t = 3 := by simpa [targets] using ht
  rcases this with rfl | rfl <;> rfl

/-- In any typing by these rules, the write to the public global of the leak is under a public pc. -/
theorem write_under_public_pc {lifted : List Nat → Nat} {Ls : List STy} {rest : List Instr}
    {st : STy} {pc : Lab} {γ γ' : SoS}
    (h : Typed lifted leakCtx Ls (.globalSet 0 :: rest) ((st, pc) :: γ) γ') : pc = Lab.L := by
  cases h with
  | globalSet _ hle _ =>
    cases pc
    · rfl
    · exact absurd (hle rfl) (by decide)

/--
With the lift down to the deepest target, the leak has no typing from a public pc, whatever
the stack of stacks after it: the lift covers the third block, so the pc is secret at the write.
-/
theorem repaired_rule_rejects_leak (γ' : SoS) :
    ¬ Typed repaired leakCtx [] leak [([], Lab.L)] γ' := by
  intro h
  cases h with
  | block hσ h3 _ =>
    cases hσ
    cases h3 with
    | block hσ h2 hwrite =>
      cases hσ
      cases h2 with
      | block hσ h1 hend2 =>
        cases hσ
        cases h1 with
        | block hσ h0 hend1 =>
          cases hσ
          cases h0 with
          | localGet _ hbranch =>
            cases hbranch with
            | brTable hσ _ _ _ hbelow _ hend0 =>
              -- the four entries below the innermost block, as the rule raised them
              cases hbelow with
              | cons hst1 _ hbelow =>
                cases hbelow with
                | cons hst2 _ hbelow =>
                  cases hbelow with
                  | cons hst3 _ hbelow =>
                    cases hbelow with
                    | cons hst4 _ hbelow =>
                      cases hbelow
                      cases hst1
                      cases hst2
                      cases hst3
                      cases hst4
                      cases hend0
                      cases hend1
                      cases hend2
                      cases hwrite with
                      | const _ hset =>
                        have hpc := write_under_public_pc hset
                        simp [Lab.join, leakCtx] at hpc

/--
The same leak two blocks deep: the write follows the first block inside the second, and the
table's targets are the two blocks.

    (block (block (br_table 0 1 (local.get 0))) (global.set 0 (i32.const 1)))
-/
def shallowLeak : List Instr :=
  [.block [] [] [] [.block [] [] [] [.localGet 0, .brTable [0] 1], .const 1, .globalSet 0]]

/--
The printed rules reject it: with two targets the lift reaches the second block. The printed
rule is wrong only for a target deeper than the number of targets.
-/
theorem printed_rule_rejects_shallow_leak (γ' : SoS) :
    ¬ Typed printed leakCtx [] shallowLeak [([], Lab.L)] γ' := by
  intro h
  cases h with
  | block hσ h1 _ =>
    cases hσ
    cases h1 with
    | block hσ h0 hwrite =>
      cases hσ
      cases h0 with
      | localGet _ hbranch =>
        cases hbranch with
        | brTable hσ _ _ _ hbelow _ hend0 =>
          cases hbelow with
          | cons hst1 _ hbelow =>
            cases hbelow with
            | cons hst2 _ hbelow =>
              cases hbelow
              cases hst1
              cases hst2
              cases hend0
              cases hwrite with
              | const _ hset =>
                have hpc := write_under_public_pc hset
                simp [Lab.join, leakCtx] at hpc

/--
The first finding in one statement. The printed rules type the leak, and it has two runs,
from states that agree on the public global and differ in the secret local, after which the
public global differs.
-/
theorem printed_rule_unsound (s t : State) (hs : s.loc 0 = 0) (ht : t.loc 0 ≠ 0)
    (hglobal : s.glob 0 = t.glob 0) (hnot1 : s.glob 0 ≠ 1) :
    Typed printed leakCtx [] leak [([], Lab.L)] [([], Lab.L)] ∧
      ∃ s' t', Eval [] 8 [] leak [] s (.normal [] s') ∧ Eval [] 6 [] leak [] t (.normal [] t') ∧
        s'.glob 0 ≠ t'.glob 0 := by
  obtain ⟨hrun1, hrun2⟩ := leak_runs_differ [] s t hs ht
  refine ⟨printed_rule_accepts_leak, _, _, hrun1, hrun2, ?_⟩
  rw [(leak_runs_globals s t hglobal).1, ← hglobal]
  exact fun h => hnot1 h.symm

end SecWasm
end WasmIfc
