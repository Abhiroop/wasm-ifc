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
  force a wrapper into every type index (@'Num 'I32@). Instead the sub-categories are
  recovered as refinement-witness GADTs ('IsInt', 'IsFloat' below): a value of @IsInt t@ is
  a proof that @t@ is an integer type that also says which one. So a stack index reads
  @'I32 ': 'I32@, and \"this op needs an integer\" is an 'IsInt' argument. (Over the current
  four constructors \"numeric\" is the whole type, so it needs no witness yet; when ref/vec
  types join the union an @IsNum@ witness — and the corresponding @intIsNum@/@floatIsNum@
  widenings — would be added the same way.)
-}
data ValType = I32 | I64 | F32 | F64 -- later: | V128 | FuncRef | ExternRef
    deriving stock (Eq, Show)

-- Singletons for the value type: the intrinsically-typed layer reflects these between the
-- term and type levels (e.g. a @Sing (s :: [ValType])@ stack shape, or a constant's type).
$(genSingletons [''ValType])

-- Decidable equality on the value-type singletons, so elaboration can compare stack types
-- with the library's 'Data.Singletons.Decide.decideEquality' instead of hand-rolling it.
$(singDecideInstances [''ValType])

{- | Evidence that a value type is one of the two integer types, refined to its width.
  Carried by integer-only instructions so their interpretation is total (no float/ref case
  can arise), turning what would be a runtime @error@ into an unrepresentable state. This is
  the Haskell analogue of \"implements the integer sub-interface\": carrying it both
  restricts the type and tells you which concrete one it is.
-}
data IsInt (t :: ValType) where
    IntI32 :: IsInt 'I32
    IntI64 :: IsInt 'I64

-- | The floating-point counterpart of 'IsInt', carried by float-only instructions.
data IsFloat (t :: ValType) where
    FloatF32 :: IsFloat 'F32
    FloatF64 :: IsFloat 'F64

{- | Refine a value-type singleton to integer (resp. floating-point) evidence, or fail if it
  is of the other kind. Elaboration uses these to reject e.g. @f32.and@ or @i32.sqrt@.
-}
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
