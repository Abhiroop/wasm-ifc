{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- | The core WASM types — number and value types, function/global/memory types, and the
--   small operand tags (signedness, memory immediates). Singletons are generated for the
--   number and value types so the intrinsically-typed layer can reflect them between the
--   term and type levels.
module Syntax.Types where

import Data.Singletons.TH
import Data.Word (Word32)

data NumType = I32 | I64 | F32 | F64 deriving (Eq, Show)

{- data RefType = FuncRef | ExternRef | ... deriving (Eq, Show) -}

{- data VecType = V128 deriving (Eq, Show) -}

newtype ValType = Num NumType {- | Ref RefType | Vec VecType -} deriving (Eq, Show)

-- Singletons for the number and value types: the intrinsically-typed layer needs to
-- reflect these between the term and type levels (e.g. a @Sing (s :: [ValType])@ stack
-- shape, or the type carried by a constant).
$(genSingletons [''NumType, ''ValType])

-- | Evidence that a number type is one of the two integer types, refined to its width.
--   Carried by integer-only instructions so their interpretation is total (no float case
--   can arise), turning what would be a runtime @error@ into an unrepresentable state.
data IsInt (t :: NumType) where
    IntI32 :: IsInt 'I32
    IntI64 :: IsInt 'I64

-- | The floating-point counterpart of 'IsInt', carried by float-only instructions.
data IsFloat (t :: NumType) where
    FloatF32 :: IsFloat 'F32
    FloatF64 :: IsFloat 'F64

-- | Refine a number-type singleton to integer (resp. floating-point) evidence, or fail if
--   it is of the other kind. Elaboration uses these to reject e.g. @f32.and@ or @i32.sqrt@.
intType :: SNumType t -> Maybe (IsInt t)
intType SI32 = Just IntI32
intType SI64 = Just IntI64
intType SF32 = Nothing
intType SF64 = Nothing

floatType :: SNumType t -> Maybe (IsFloat t)
floatType SF32 = Just FloatF32
floatType SF64 = Just FloatF64
floatType SI32 = Nothing
floatType SI64 = Nothing

newtype ResultType = ResultType [ValType] deriving (Eq, Show)
data FuncType = FuncType [ValType] [ValType] deriving (Eq, Show)
type BlockType = FuncType

data Limits = Limits
    { min :: Word32
    , max :: Maybe Word32
    } deriving (Eq, Show)
data AddrType = AddrI32 | AddrI64 deriving (Eq, Show)
data MemType = MemType
    { addrtype :: AddrType
    , limits :: Limits
    } deriving (Eq, Show)
-- (The type-level counterpart of 'MemType' is 'Validation.Shape.MemShape'.)

{- data TableType = TableType Limits RefType deriving (Eq, Show) -}

data Mutability = Immutable | Mutable deriving (Eq, Show)
data GlobalType = GlobalType Mutability ValType deriving (Eq, Show)

-- | Signed vs. unsigned interpretation of an integer operation. Stored values are raw bit
--   patterns; signedness is chosen per operation, not per value.
data Signedness = Signed | Unsigned deriving (Eq, Show)

-- | A memory immediate. Alignment is advisory (ignored at run time); @offset@ is added to
--   the dynamic address.
data MemArg = MemArg { alignment :: Word32, offset :: Word32 } deriving (Eq, Show)
