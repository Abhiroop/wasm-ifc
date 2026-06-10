import Mathlib.Data.List.Basic
import Mathlib.Data.Int.Basic

namespace WasmIFC

-- ============================================================
-- Types and Shapes
-- ============================================================

inductive ValType : Type where
  | I32 : ValType
  | I64 : ValType
  | F32 : ValType
  | F64 : ValType

def ValStackShape   := List ValType
def LocalsShape     := List ValType
def LabelStackShape := List ValStackShape

-- ============================================================
-- Raw untyped instructions (from the Wasm spec)
-- ============================================================

inductive RawInstr : Type where
  | i32Add : RawInstr
  | i32Sub : RawInstr
  | i32Mul : RawInstr
  | i32Div : RawInstr
  | i64Add : RawInstr
  | i64Sub : RawInstr
  | i64Mul : RawInstr
  | i64Div : RawInstr
  | drop   : RawInstr

-- ============================================================
-- Wasm spec validation judgment
-- Key: lives in Type, not Prop, so we can eliminate it into Type
-- (needed for fromB: proof-relevant derivation, not proof-irrelevant)
-- ============================================================

inductive WasmTyping : LocalsShape → RawInstr → ValStackShape → ValStackShape → Type where
  | I32Add : ∀ {locals s}, WasmTyping locals RawInstr.i32Add (ValType.I32 :: ValType.I32 :: s) (ValType.I32 :: s)
  | I32Sub : ∀ {locals s}, WasmTyping locals RawInstr.i32Sub (ValType.I32 :: ValType.I32 :: s) (ValType.I32 :: s)
  | I32Mul : ∀ {locals s}, WasmTyping locals RawInstr.i32Mul (ValType.I32 :: ValType.I32 :: s) (ValType.I32 :: s)
  | I32Div : ∀ {locals s}, WasmTyping locals RawInstr.i32Div (ValType.I32 :: ValType.I32 :: s) (ValType.I32 :: s)
  | I64Add : ∀ {locals s}, WasmTyping locals RawInstr.i64Add (ValType.I64 :: ValType.I64 :: s) (ValType.I64 :: s)
  | I64Sub : ∀ {locals s}, WasmTyping locals RawInstr.i64Sub (ValType.I64 :: ValType.I64 :: s) (ValType.I64 :: s)
  | I64Mul : ∀ {locals s}, WasmTyping locals RawInstr.i64Mul (ValType.I64 :: ValType.I64 :: s) (ValType.I64 :: s)
  | I64Div : ∀ {locals s}, WasmTyping locals RawInstr.i64Div (ValType.I64 :: ValType.I64 :: s) (ValType.I64 :: s)
  | Drop   : ∀ {locals s t}, WasmTyping locals RawInstr.drop (t :: s) s

-- ============================================================
-- The Haskell GADT (intrinsically typed)
-- ============================================================

inductive Instruction : ValStackShape → ValStackShape → LocalsShape → Type where
  | I32Add : ∀ {s locals}, Instruction (ValType.I32 :: ValType.I32 :: s) (ValType.I32 :: s) locals
  | I32Sub : ∀ {s locals}, Instruction (ValType.I32 :: ValType.I32 :: s) (ValType.I32 :: s) locals
  | I32Mul : ∀ {s locals}, Instruction (ValType.I32 :: ValType.I32 :: s) (ValType.I32 :: s) locals
  | I32Div : ∀ {s locals}, Instruction (ValType.I32 :: ValType.I32 :: s) (ValType.I32 :: s) locals
  | I64Add : ∀ {s locals}, Instruction (ValType.I64 :: ValType.I64 :: s) (ValType.I64 :: s) locals
  | I64Sub : ∀ {s locals}, Instruction (ValType.I64 :: ValType.I64 :: s) (ValType.I64 :: s) locals
  | I64Mul : ∀ {s locals}, Instruction (ValType.I64 :: ValType.I64 :: s) (ValType.I64 :: s) locals
  | I64Div : ∀ {s locals}, Instruction (ValType.I64 :: ValType.I64 :: s) (ValType.I64 :: s) locals
  | Drop   : ∀ {s locals t}, Instruction (t :: s) s locals

-- ============================================================
-- Isomorphism index + carriers
-- ============================================================

def WasmIndex := ValStackShape × ValStackShape × LocalsShape

def InstrA : WasmIndex → Type
  | (pre, post, locals) => Instruction pre post locals

def InstrB : WasmIndex → Type
  | (pre, post, locals) => Σ r : RawInstr, WasmTyping locals r pre post

-- ============================================================
-- to / from
-- ============================================================

def toB {pre post locals} (i : Instruction pre post locals)
    : Σ r : RawInstr, WasmTyping locals r pre post :=
  match i with
  | Instruction.I32Add => ⟨RawInstr.i32Add, WasmTyping.I32Add⟩
  | Instruction.I32Sub => ⟨RawInstr.i32Sub, WasmTyping.I32Sub⟩
  | Instruction.I32Mul => ⟨RawInstr.i32Mul, WasmTyping.I32Mul⟩
  | Instruction.I32Div => ⟨RawInstr.i32Div, WasmTyping.I32Div⟩
  | Instruction.I64Add => ⟨RawInstr.i64Add, WasmTyping.I64Add⟩
  | Instruction.I64Sub => ⟨RawInstr.i64Sub, WasmTyping.I64Sub⟩
  | Instruction.I64Mul => ⟨RawInstr.i64Mul, WasmTyping.I64Mul⟩
  | Instruction.I64Div => ⟨RawInstr.i64Div, WasmTyping.I64Div⟩
  | Instruction.Drop   => ⟨RawInstr.drop,   WasmTyping.Drop⟩

def fromB {pre post locals} (r : Σ r : RawInstr, WasmTyping locals r pre post)
    : Instruction pre post locals :=
  match r.1, r.2 with
  | RawInstr.i32Add, WasmTyping.I32Add => Instruction.I32Add
  | RawInstr.i32Sub, WasmTyping.I32Sub => Instruction.I32Sub
  | RawInstr.i32Mul, WasmTyping.I32Mul => Instruction.I32Mul
  | RawInstr.i32Div, WasmTyping.I32Div => Instruction.I32Div
  | RawInstr.i64Add, WasmTyping.I64Add => Instruction.I64Add
  | RawInstr.i64Sub, WasmTyping.I64Sub => Instruction.I64Sub
  | RawInstr.i64Mul, WasmTyping.I64Mul => Instruction.I64Mul
  | RawInstr.i64Div, WasmTyping.I64Div => Instruction.I64Div
  | RawInstr.drop,   WasmTyping.Drop   => Instruction.Drop

-- ============================================================
-- Round-trip proofs
-- ============================================================

theorem from_to {pre post locals} (t : Instruction pre post locals)
    : fromB (toB t) = t :=
  match t with
  | Instruction.I32Add => rfl
  | Instruction.I32Sub => rfl
  | Instruction.I32Mul => rfl
  | Instruction.I32Div => rfl
  | Instruction.I64Add => rfl
  | Instruction.I64Sub => rfl
  | Instruction.I64Mul => rfl
  | Instruction.I64Div => rfl
  | Instruction.Drop   => rfl



theorem to_from {pre post locals} (r : Σ r : RawInstr, WasmTyping locals r pre post)
    : toB (fromB r) = r := by
  obtain ⟨raw, typing⟩ := r
  match raw, typing with
  | RawInstr.i32Add, WasmTyping.I32Add => rfl
  | RawInstr.i32Sub, WasmTyping.I32Sub => rfl
  | RawInstr.i32Mul, WasmTyping.I32Mul => rfl
  | RawInstr.i32Div, WasmTyping.I32Div => rfl
  | RawInstr.i64Add, WasmTyping.I64Add => rfl
  | RawInstr.i64Sub, WasmTyping.I64Sub => rfl
  | RawInstr.i64Mul, WasmTyping.I64Mul => rfl
  | RawInstr.i64Div, WasmTyping.I64Div => rfl
  | RawInstr.drop,   WasmTyping.Drop   => rfl

-- ============================================================
-- Isomorphism record
-- ============================================================

structure Iso (A B : WasmIndex → Type) : Type 1 where
  forth      : ∀ {i}, A i → B i
  back       : ∀ {i}, B i → A i
  back_forth : ∀ {i} (t : A i), back (forth t) = t
  forth_back : ∀ {i} (t : B i), forth (back t) = t

def WasmIsomorphism : Iso InstrA InstrB :=
  { forth      := fun i => toB i
  , back       := fun r => fromB r
  , back_forth := fun t => from_to t
  , forth_back := fun r => to_from r
  }

-- ============================================================
-- Runtime values
-- ============================================================

inductive Value : ValType → Type where
  | VI32 : Int → Value ValType.I32
  | VI64 : Int → Value ValType.I64

-- Typed value stack
inductive ValueStack : ValStackShape → Type where
  | nil  : ValueStack []
  | cons : ∀ {t s}, Value t → ValueStack s → ValueStack (t :: s)

notation:67 v " ∷ₛ " vs => ValueStack.cons v vs
notation "[]ₛ"           => ValueStack.nil

-- ============================================================
-- Small-step reduction relation on value stacks
-- WasmTyping lives in Type so we can match on it;
-- StepRel is a specification so it lives in Prop
-- ============================================================

inductive StepRel : ∀ {s s'}, ValueStack s → ValueStack s' → Prop where
  | I32Add : ∀ {rhs lhs : Int} {s} {rest : ValueStack s},
      StepRel (Value.VI32 rhs ∷ₛ Value.VI32 lhs ∷ₛ rest) (Value.VI32 (lhs + rhs) ∷ₛ rest)
  | I32Sub : ∀ {rhs lhs : Int} {s} {rest : ValueStack s},
      StepRel (Value.VI32 rhs ∷ₛ Value.VI32 lhs ∷ₛ rest) (Value.VI32 (lhs - rhs) ∷ₛ rest)
  | I32Mul : ∀ {rhs lhs : Int} {s} {rest : ValueStack s},
      StepRel (Value.VI32 rhs ∷ₛ Value.VI32 lhs ∷ₛ rest) (Value.VI32 (lhs * rhs) ∷ₛ rest)
  | I32Div : ∀ {rhs lhs : Int} {s} {rest : ValueStack s},
      rhs ≠ 0 →
      StepRel (Value.VI32 rhs ∷ₛ Value.VI32 lhs ∷ₛ rest) (Value.VI32 (lhs / rhs) ∷ₛ rest)
  | I64Add : ∀ {rhs lhs : Int} {s} {rest : ValueStack s},
      StepRel (Value.VI64 rhs ∷ₛ Value.VI64 lhs ∷ₛ rest) (Value.VI64 (lhs + rhs) ∷ₛ rest)
  | I64Sub : ∀ {rhs lhs : Int} {s} {rest : ValueStack s},
      StepRel (Value.VI64 rhs ∷ₛ Value.VI64 lhs ∷ₛ rest) (Value.VI64 (lhs - rhs) ∷ₛ rest)
  | I64Mul : ∀ {rhs lhs : Int} {s} {rest : ValueStack s},
      StepRel (Value.VI64 rhs ∷ₛ Value.VI64 lhs ∷ₛ rest) (Value.VI64 (lhs * rhs) ∷ₛ rest)
  | I64Div : ∀ {rhs lhs : Int} {s} {rest : ValueStack s},
      rhs ≠ 0 →
      StepRel (Value.VI64 rhs ∷ₛ Value.VI64 lhs ∷ₛ rest) (Value.VI64 (lhs / rhs) ∷ₛ rest)
  | Drop   : ∀ {t s} {v : Value t} {rest : ValueStack s},
      StepRel (v ∷ₛ rest) rest

-- ============================================================
-- Evaluator (stepValues)
-- ============================================================


def stepValues {pre post locals}
    (t : Instruction pre post locals) (vs : ValueStack pre) : Option (ValueStack post) :=
  match t, vs with
  | Instruction.I32Add, (Value.VI32 rhs ∷ₛ Value.VI32 lhs ∷ₛ rest) =>
      some (Value.VI32 (lhs + rhs) ∷ₛ rest)
  | Instruction.I32Sub, (Value.VI32 rhs ∷ₛ Value.VI32 lhs ∷ₛ rest) =>
      some (Value.VI32 (lhs - rhs) ∷ₛ rest)
  | Instruction.I32Mul, (Value.VI32 rhs ∷ₛ Value.VI32 lhs ∷ₛ rest) =>
      some (Value.VI32 (lhs * rhs) ∷ₛ rest)
  | Instruction.I32Div, (Value.VI32 rhs ∷ₛ Value.VI32 lhs ∷ₛ rest) =>
      if heq : rhs = 0 then none
      else some (Value.VI32 (lhs / rhs) ∷ₛ rest)
  | Instruction.I64Add, (Value.VI64 rhs ∷ₛ Value.VI64 lhs ∷ₛ rest) =>
      some (Value.VI64 (lhs + rhs) ∷ₛ rest)
  | Instruction.I64Sub, (Value.VI64 rhs ∷ₛ Value.VI64 lhs ∷ₛ rest) =>
      some (Value.VI64 (lhs - rhs) ∷ₛ rest)
  | Instruction.I64Mul, (Value.VI64 rhs ∷ₛ Value.VI64 lhs ∷ₛ rest) =>
      some (Value.VI64 (lhs * rhs) ∷ₛ rest)
  | Instruction.I64Div, (Value.VI64 rhs ∷ₛ Value.VI64 lhs ∷ₛ rest) =>
      if heq : rhs = 0 then none
      else some (Value.VI64 (lhs / rhs) ∷ₛ rest)
  | Instruction.Drop, (v ∷ₛ rest) =>
      some rest

-- ============================================================
-- step_correct: evaluator soundness w.r.t. the reduction relation
-- ============================================================
theorem step_correct {pre post locals}
    (t : Instruction pre post locals)
    (vs : ValueStack pre)
    {result : ValueStack post}
    (h : stepValues t vs = some result)
    : StepRel vs result := by
  cases t with
  | I32Add =>
      cases vs with
      | cons v rest => cases v with
        | VI32 rhs => cases rest with
          | cons v2 rest2 => cases v2 with
            | VI32 lhs =>
                simp [stepValues] at h
                exact h ▸ StepRel.I32Add
  | I32Sub =>
      cases vs with
      | cons v rest => cases v with
        | VI32 rhs => cases rest with
          | cons v2 rest2 => cases v2 with
            | VI32 lhs =>
                simp [stepValues] at h
                exact h ▸ StepRel.I32Sub
  | I32Mul =>
      cases vs with
      | cons v rest => cases v with
        | VI32 rhs => cases rest with
          | cons v2 rest2 => cases v2 with
            | VI32 lhs =>
                simp [stepValues] at h
                exact h ▸ StepRel.I32Mul
  | I32Div =>
      cases vs with
      | cons v rest => cases v with
        | VI32 rhs => cases rest with
          | cons v2 rest2 => cases v2 with
            | VI32 lhs =>
                simp [stepValues] at h
                obtain ⟨heq, hstack⟩ := h
                exact hstack ▸ StepRel.I32Div heq
  | I64Add =>
      cases vs with
      | cons v rest => cases v with
        | VI64 rhs => cases rest with
          | cons v2 rest2 => cases v2 with
            | VI64 lhs =>
                simp [stepValues] at h
                exact h ▸ StepRel.I64Add
  | I64Sub =>
      cases vs with
      | cons v rest => cases v with
        | VI64 rhs => cases rest with
          | cons v2 rest2 => cases v2 with
            | VI64 lhs =>
                simp [stepValues] at h
                exact h ▸ StepRel.I64Sub
  | I64Mul =>
      cases vs with
      | cons v rest => cases v with
        | VI64 rhs => cases rest with
          | cons v2 rest2 => cases v2 with
            | VI64 lhs =>
                simp [stepValues] at h
                exact h ▸ StepRel.I64Mul
  | I64Div =>
      cases vs with
      | cons v rest => cases v with
        | VI64 rhs => cases rest with
          | cons v2 rest2 => cases v2 with
            | VI64 lhs =>
                simp [stepValues] at h
                obtain ⟨heq, hstack⟩ := h
                exact hstack ▸ StepRel.I64Div heq
  | Drop =>
      cases vs with
      | cons v rest =>
          simp [stepValues] at h
          exact h ▸ StepRel.Drop





-- ============================================================
-- Adequacy record
-- ============================================================

structure WasmAdequacy {pre post locals} (t : Instruction pre post locals) : Type 1 where
  syntactic : Iso InstrA InstrB
  semantic  : ∀ (vs : ValueStack pre) {result : ValueStack post},
              stepValues t vs = some result → StepRel vs result

def adequate {pre post locals} (t : Instruction pre post locals) : WasmAdequacy t :=
  { syntactic := WasmIsomorphism
  , semantic  := step_correct t
  }

end WasmIFC
