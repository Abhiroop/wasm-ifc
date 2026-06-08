module WASM-IFC where

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Value types matching your Haskell WasmType
data ValType : Set where
  I32 : ValType
  I64 : ValType
  F32 : ValType
  F64 : ValType

-- Stack shapes
ValStackShape : Set
ValStackShape = List ValType

-- For now locals and labels are also lists of val types
LocalsShape : Set
LocalsShape = List ValType

LabelStackShape : Set
LabelStackShape = List ValStackShape

-- Raw untyped instructions -- just names, no indices
-- These come from the Wasm spec
data RawInstr : Set where
  i32-add : RawInstr
  i32-sub : RawInstr
  i32-mul : RawInstr
  i32-div : RawInstr
  i64-add : RawInstr
  i64-sub : RawInstr
  i64-mul : RawInstr
  i64-div : RawInstr
  drop    : RawInstr

-- The Wasm spec validation judgment
-- locals ⊢ instr : pre ⇒ post
data _⊢_∶_⇒_ :
    LocalsShape → RawInstr → ValStackShape → ValStackShape → Set where

  I32Add : ∀ {locals s}
         → locals ⊢ i32-add ∶ (I32 ∷ I32 ∷ s) ⇒ (I32 ∷ s)

  I32Sub : ∀ {locals s}
         → locals ⊢ i32-sub ∶ (I32 ∷ I32 ∷ s) ⇒ (I32 ∷ s)

  I32Mul : ∀ {locals s}
         → locals ⊢ i32-mul ∶ (I32 ∷ I32 ∷ s) ⇒ (I32 ∷ s)

  I32Div : ∀ {locals s}
         → locals ⊢ i32-div ∶ (I32 ∷ I32 ∷ s) ⇒ (I32 ∷ s)

  I64Add : ∀ {locals s}
         → locals ⊢ i64-add ∶ (I64 ∷ I64 ∷ s) ⇒ (I64 ∷ s)

  I64Sub : ∀ {locals s}
         → locals ⊢ i64-sub ∶ (I64 ∷ I64 ∷ s) ⇒ (I64 ∷ s)

  I64Mul : ∀ {locals s}
         → locals ⊢ i64-mul ∶ (I64 ∷ I64 ∷ s) ⇒ (I64 ∷ s)

  I64Div : ∀ {locals s}
         → locals ⊢ i64-div ∶ (I64 ∷ I64 ∷ s) ⇒ (I64 ∷ s)

  Drop   : ∀ {locals s t}
         → locals ⊢ drop ∶ (t ∷ s) ⇒ s

-- The Haskell GADT
data Instruction : ValStackShape → ValStackShape → LocalsShape → Set where
  I32Add : ∀ {s locals} → Instruction (I32 ∷ I32 ∷ s) (I32 ∷ s) locals
  I32Sub : ∀ {s locals} → Instruction (I32 ∷ I32 ∷ s) (I32 ∷ s) locals
  I32Mul : ∀ {s locals} → Instruction (I32 ∷ I32 ∷ s) (I32 ∷ s) locals
  I32Div : ∀ {s locals} → Instruction (I32 ∷ I32 ∷ s) (I32 ∷ s) locals
  I64Add : ∀ {s locals} → Instruction (I64 ∷ I64 ∷ s) (I64 ∷ s) locals
  I64Sub : ∀ {s locals} → Instruction (I64 ∷ I64 ∷ s) (I64 ∷ s) locals
  I64Mul : ∀ {s locals} → Instruction (I64 ∷ I64 ∷ s) (I64 ∷ s) locals
  I64Div : ∀ {s locals} → Instruction (I64 ∷ I64 ∷ s) (I64 ∷ s) locals
  Drop   : ∀ {s locals t} → Instruction (t ∷ s) s locals

-- The isomorphism
-- to: Haskell GADT → raw instr + spec proof
to : ∀ {pre post locals}
   → Instruction pre post locals
   → Σ RawInstr (λ r → locals ⊢ r ∶ pre ⇒ post)
to I32Add = i32-add , I32Add
to I32Sub = i32-sub , I32Sub
to I32Mul = i32-mul , I32Mul
to I32Div = i32-div , I32Div
to I64Add = i64-add , I64Add
to I64Sub = i64-sub , I64Sub
to I64Mul = i64-mul , I64Mul
to I64Div = i64-div , I64Div
to Drop   = drop    , Drop

-- from: raw instr + spec proof → your GADT
from : ∀ {pre post locals}
     → Σ RawInstr (λ r → locals ⊢ r ∶ pre ⇒ post)
     → Instruction pre post locals
from (i32-add , I32Add) = I32Add
from (i32-sub , I32Sub) = I32Sub
from (i32-mul , I32Mul) = I32Mul
from (i32-div , I32Div) = I32Div
from (i64-add , I64Add) = I64Add
from (i64-sub , I64Sub) = I64Sub
from (i64-mul , I64Mul) = I64Mul
from (i64-div , I64Div) = I64Div
from (drop    , Drop)   = Drop

-- round trip proofs
from-to : ∀ {pre post locals} (t : Instruction pre post locals)
        → from (to t) ≡ t
from-to I32Add = refl
from-to I32Sub = refl
from-to I32Mul = refl
from-to I32Div = refl
from-to I64Add = refl
from-to I64Sub = refl
from-to I64Mul = refl
from-to I64Div = refl
from-to Drop   = refl

to-from : ∀ {pre post locals} (r : Σ RawInstr (λ r → locals ⊢ r ∶ pre ⇒ post))
        → to (from r) ≡ r
to-from (i32-add , I32Add) = refl
to-from (i32-sub , I32Sub) = refl
to-from (i32-mul , I32Mul) = refl
to-from (i32-div , I32Div) = refl
to-from (i64-add , I64Add) = refl
to-from (i64-sub , I64Sub) = refl
to-from (i64-mul , I64Mul) = refl
to-from (i64-div , I64Div) = refl
to-from (drop    , Drop)   = refl


-- Isomorphism (syntactic)
record _≅_ {I : Set} (A B : I → Set) : Set where
  field
    forth      : ∀ {i} → A i → B i
    back       : ∀ {i} → B i → A i
    back-forth : ∀ {i} (t : A i) → back (forth t) ≡ t
    forth-back : ∀ {i} (t : B i) → forth (back t) ≡ t


-- The index shared by both sides
WasmIndex : Set
WasmIndex = ValStackShape × ValStackShape × LocalsShape

-- Haskell GADT reindexed
InstrA : WasmIndex → Set
InstrA (pre , post , locals) = Instruction pre post locals

-- The spec judgment reindexed
InstrB : WasmIndex → Set
InstrB (pre , post , locals) = Σ RawInstr (λ r → locals ⊢ r ∶ pre ⇒ post)

WasmIsomorphism : InstrA ≅ InstrB
WasmIsomorphism = record
  { forth      = to
  ; back       = from
  ; back-forth = from-to
  ; forth-back = to-from
  }
