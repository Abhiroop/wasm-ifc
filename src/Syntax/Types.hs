{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{- | The core WASM types — the value type, function/global/memory types, and the small
  operand tags (signedness, memory immediates). Library singletons (from @singletons-base@)
  are generated for these so the intrinsically-typed layer can reflect them between the term
  and type levels.

  This module exports openly (no explicit list): for a single-constructor type the generated
  @Sing@ constructor and its type synonym share a name (e.g. @SFuncType@), so importers must
  pull the constructors in via an open import — a named export would only bring the synonym.
-}
module Syntax.Types where

import Data.Singletons.Base.TH
import Data.Word (Word32)

{- | A WebAssembly value type, as one flat enumeration. The spec's nested grammar
  (@valtype ::= numtype | vectype | reftype@) is NOT encoded as constructors — that would
  force a wrapper into every type index (@'Num 'I32@). Instead the sub-categories are recovered
  as refinement-witness GADTs ('IsNum', 'IsInt', 'IsFloat' below): a value of @IsInt t@ is a
  proof that @t@ is an integer type that also says which one. So a stack index reads
  @'I32 ': 'I32@.

  Crucially, an instruction the spec restricts to a sub-category takes the corresponding
  witness, /not/ a bare @Sing (t :: ValType)@: @i32.add@ is @'IsNum' t@, @i32.eqz@ is
  @'IsInt' t@. The restriction is then enforced by construction and does not depend on which
  constructors 'ValType' currently happens to have — adding @FuncRef@/@V128@ cannot silently
  make @funcref.add@ representable.
-}
data ValType = I32 | I64 | F32 | F64 -- later: | V128 | FuncRef | ExternRef
    deriving stock (Eq, Show)

-- Singletons for the value type: the intrinsically-typed layer reflects these between the
-- term and type levels (e.g. a @Sing (s :: [ValType])@ stack shape, or a constant's type).
$(genSingletons [''ValType])

-- Decidable equality on the value-type singletons, so elaboration can compare stack types
-- with the library's 'Data.Singletons.Decide.decideEquality' instead of hand-rolling it.
$(singDecideInstances [''ValType])

{- | Evidence that a value type is a numeric type (the spec's @numtype@), refined to which
  one. Carried by every instruction the spec restricts to @numtype@ — @const@, @add@/@sub@/
  @mul@/@div@, the comparisons, @load@/@store@, conversions, @select@ — so none of them can
  be built at a non-numeric type. Carrying the witness both restricts the type and identifies
  the concrete one, so it doubles as the singleton the interpreter dispatches on.
-}
data IsNum (t :: ValType) where
    NumI32 :: IsNum 'I32
    NumI64 :: IsNum 'I64
    NumF32 :: IsNum 'F32
    NumF64 :: IsNum 'F64

{- | Evidence that a value type is one of the two integer types, refined to its width.
  Carried by integer-only instructions (@eqz@, the bitwise/shift/count ops, narrow load/
  store) so their interpretation is total (no float/ref case can arise).
-}
data IsInt (t :: ValType) where
    IntI32 :: IsInt 'I32
    IntI64 :: IsInt 'I64

-- | The floating-point counterpart of 'IsInt', carried by float-only instructions.
data IsFloat (t :: ValType) where
    FloatF32 :: IsFloat 'F32
    FloatF64 :: IsFloat 'F64

{- | Refine a value-type singleton to numeric (resp. integer, floating-point) evidence, or
  fail if it is of another kind. Elaboration uses these to reject e.g. @funcref.add@,
  @f32.and@ or @i32.sqrt@.
-}
numType :: Sing (t :: ValType) -> Maybe (IsNum t)
numType SI32 = Just NumI32
numType SI64 = Just NumI64
numType SF32 = Just NumF32
numType SF64 = Just NumF64

-- | The width in bytes of a numeric type (4 for i32/f32, 8 for i64/f64).
numBytes :: IsNum t -> Int
numBytes NumI32 = 4
numBytes NumF32 = 4
numBytes NumI64 = 8
numBytes NumF64 = 8

-- | Recover the value-type singleton from a numeric witness.
numSing :: IsNum t -> Sing t
numSing NumI32 = SI32
numSing NumI64 = SI64
numSing NumF32 = SF32
numSing NumF64 = SF64

intType :: Sing (t :: ValType) -> Maybe (IsInt t)
intType SI32 = Just IntI32
intType SI64 = Just IntI64
intType SF32 = Nothing
intType SF64 = Nothing

floatType :: Sing (t :: ValType) -> Maybe (IsFloat t)
floatType SF32 = Just FloatF32
floatType SF64 = Just FloatF64
floatType SI32 = Nothing
floatType SI64 = Nothing

{- | A numeric operand for the operations that are signed/unsigned on integers but have a
  single form on floats — division and the ordered comparisons (@lt@/@gt@/@le@/@ge@). An
  integer carries its 'Signedness'; a float carries none, so a signed float comparison or
  division is unrepresentable.
-}
data SignedNum (t :: ValType) where
    IntWithSign :: IsInt t -> Signedness -> SignedNum t
    FloatNoSign :: IsFloat t -> SignedNum t

signedNum :: Sing (t :: ValType) -> Signedness -> Maybe (SignedNum t)
signedNum st sign = case intType st of
    Just isInt -> Just (IntWithSign isInt sign)
    Nothing -> FloatNoSign <$> floatType st

{- | The storage width of a narrow integer load/store: one or two bytes for any integer, plus
  four bytes for @i64@ only (a narrow access must be strictly narrower than the value, so an
  @i32@ has no four-byte narrow form). Makes an out-of-range width unrepresentable.
-}
data NarrowWidth (t :: ValType) where
    Narrow8 :: IsInt t -> NarrowWidth t
    Narrow16 :: IsInt t -> NarrowWidth t
    Narrow32 :: NarrowWidth 'I64

-- | The width in bytes a 'NarrowWidth' stands for (1, 2 or 4).
narrowBytes :: NarrowWidth t -> Int
narrowBytes (Narrow8 _) = 1
narrowBytes (Narrow16 _) = 2
narrowBytes Narrow32 = 4

narrowWidth :: Sing (t :: ValType) -> Int -> Maybe (NarrowWidth t)
narrowWidth st 1 = Narrow8 <$> intType st
narrowWidth st 2 = Narrow16 <$> intType st
narrowWidth SI64 4 = Just Narrow32
narrowWidth _ _ = Nothing

{- | A result type — the stack shape a block, loop, if, or function yields (the spec's
  @resulttype@). It is exactly a list of value types; the synonym names the intent so
  indices like a label context read as @[ResultType]@ rather than a bare @[[ValType]]@.
-}
type ResultType = [ValType]

data FuncType = FuncType [ValType] [ValType] deriving stock (Eq, Show)
type BlockType = FuncType

data Limits = Limits
    { min :: Word32
    , max :: Maybe Word32
    }
    deriving stock (Eq, Show)
data AddrType = AddrI32 | AddrI64 deriving stock (Eq, Show)
data MemType = MemType
    { addrtype :: AddrType
    , limits :: Limits
    }
    deriving stock (Eq, Show)

-- (The type-level counterpart of 'MemType' is 'Validation.Shape.MemShape'.)

{- data TableType = TableType Limits RefType deriving stock (Eq, Show) -}

data Mutability = Immutable | Mutable deriving stock (Eq, Show)
data GlobalType = GlobalType Mutability ValType deriving stock (Eq, Show)

{- | Signed vs. unsigned interpretation of an integer operation. Stored values are raw bit
  patterns; signedness is chosen per operation, not per value.
-}
data Signedness = Signed | Unsigned deriving stock (Eq, Show)

{- | A memory immediate. Alignment is advisory (ignored at run time); @offset@ is added to
  the dynamic address.
-}
data MemArg = MemArg {alignment :: Word32, offset :: Word32} deriving stock (Eq, Show)

-- Singletons for the remaining promotable types. Split from the 'NumType'/'ValType' splice
-- above because Template Haskell needs each type defined before its splice, and
-- 'IsInt'/'intType' (which use the number-type singleton) sit in between.
$(genSingletons [''Mutability, ''AddrType, ''FuncType, ''GlobalType])
