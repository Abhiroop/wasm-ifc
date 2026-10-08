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
    Reference (..),
    withReference,
    nullReference,
    isNullReference,
    referenceTo,
    referent,
    MemArg (..),
    AccessSite (..),
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
    HostType 'FuncRef = Reference
    HostType 'ExternRef = Reference

{- | A reference as a machine holds it: null, or the index of what it refers to. For a
  @funcref@ that is a function of the module, by its place in the function index space; for an
  @externref@ it is whatever number the host uses for its value. Like every other value it is
  one word, zero for null (which is also what a local starts at), so it is kept in a frame
  unchanged. A @funcref@ is only made by @ref.func@ and by element segments, both of which
  validation resolves to a function that exists, and no instruction computes on references.
-}
newtype Reference = Reference Word64 deriving stock (Eq, Show)

-- | What a reference witness says about the representation: a value of that type is a 'Reference'.
withReference :: IsRef t -> ((HostType t ~ Reference) => result) -> result
withReference FuncRefIsRef result = result
withReference ExternRefIsRef result = result

nullReference :: Reference
nullReference = Reference 0

isNullReference :: Reference -> Bool
isNullReference (Reference word) = word == 0

-- | The reference to the thing with this index.
referenceTo :: Word32 -> Reference
referenceTo index = Reference (fromIntegral index + 1)

-- | The index a reference refers to, or 'Nothing' for null.
referent :: Reference -> Maybe Word32
referent (Reference word) = if word == 0 then Nothing else Just (fromIntegral (word - 1))

{- | A memory immediate. Alignment is advisory (ignored at run time); @offset@ is added to
  the dynamic address.
-}
data MemArg = MemArg {alignment :: Word32, offset :: Word32} deriving stock (Eq, Show)

{- | Where a load sits in the module, so that the trap of its run-time check can name it the way
  a policy declares it. A load written as an instruction is named by its function's index and
  its position among that function's memory accesses (the policy's @load F N@); one written as
  a call to an @ifc@ ghost import, by its function's index and the position of the call among
  that function's calls to ghost accesses.
-}
data AccessSite
    = AccessAt Word32 Word32
    | GhostCallAt Word32 Word32
    deriving stock (Eq, Show)

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
