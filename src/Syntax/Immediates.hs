{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

{- | What an instruction carries besides its operands: the host representation of a constant
  ('HostType', also the representation of every value at run time), a memory access's
  alignment and offset ('MemArg'), the signed or unsigned reading of an integer operation
  ('Signedness'), and the operand refinements that pair such a choice with a value-type witness
  ('NumWithSign', 'NarrowWidth').
-}
module Syntax.Immediates (
    HostType,
    MemArg (..),
    Signedness (..),
    NumWithSign (..),
    decideNumWithSign,
    NarrowWidth (..),
    narrowBytes,
    narrowInt,
    decideNarrow,
) where

import Data.Kind (Type)
import Data.Singletons (Sing)
import Data.Word (Word32, Word64)

import Syntax.Types

{- | The host (Haskell) type that represents each WASM value type — used both for a constant's
  immediate literal and for the values held on the operand stack, locals and globals.
-}
type family HostType (t :: ValType) :: Type where
    HostType 'I32 = Word32
    HostType 'I64 = Word64
    HostType 'F32 = Float
    HostType 'F64 = Double

{- | A memory immediate. Alignment is advisory (ignored at run time); @offset@ is added to
  the dynamic address.
-}
data MemArg = MemArg {alignment :: Word32, offset :: Word32} deriving stock (Eq, Show)

{- | Signed vs. unsigned interpretation of an integer operation. Stored values are raw bit
  patterns; signedness is chosen per operation, not per value.
-}
data Signedness = Signed | Unsigned deriving stock (Eq, Show)

{- | A numeric operand for the operations that are signed/unsigned on integers but have a
  single form on floats — division and the ordered comparisons (@lt@/@gt@/@le@/@ge@). An
  integer carries its 'Signedness'; a float carries none, so a signed float comparison or
  division is unrepresentable.
-}
data NumWithSign (t :: ValType) where
    IntsHaveSign :: IsInt t -> Signedness -> NumWithSign t
    FloatsHaveNoSign :: IsFloat t -> NumWithSign t

decideNumWithSign :: Sing (t :: ValType) -> Signedness -> Maybe (NumWithSign t)
decideNumWithSign st sign = case decideInt st of
    Just isInt -> Just (IntsHaveSign isInt sign)
    Nothing -> FloatsHaveNoSign <$> decideFloat st

{- | The storage width of a narrow integer load/store: one or two bytes for any integer, plus
  four bytes for @i64@ only (a narrow access must be strictly narrower than the value, so an
  @i32@ has no four-byte narrow form). Makes an out-of-range width unrepresentable.
-}
data NarrowWidth (t :: ValType) where
    OneByte :: IsInt t -> NarrowWidth t
    TwoBytes :: IsInt t -> NarrowWidth t
    FourBytes :: NarrowWidth 'I64

-- | The width in bytes a 'NarrowWidth' stands for (1, 2 or 4).
narrowBytes :: NarrowWidth t -> Int
narrowBytes (OneByte _) = 1
narrowBytes (TwoBytes _) = 2
narrowBytes FourBytes = 4

-- | The integer type a narrow access is for; a four-byte narrow access is only ever an i64's.
narrowInt :: NarrowWidth t -> IsInt t
narrowInt (OneByte isInt) = isInt
narrowInt (TwoBytes isInt) = isInt
narrowInt FourBytes = I64IsInt

decideNarrow :: Sing (t :: ValType) -> Int -> Maybe (NarrowWidth t)
decideNarrow st 1 = OneByte <$> decideInt st
decideNarrow st 2 = TwoBytes <$> decideInt st
decideNarrow SI64 4 = Just FourBytes
decideNarrow _ _ = Nothing
