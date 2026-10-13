{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{- | The core WASM types — the value type with its sub-category witnesses, and the function,
  global, memory and table types. Library singletons (from @singletons-base@) are generated for
  these so the intrinsically-typed layer can reflect them between the term and type levels.
  (What an instruction carries besides its operands lives in "Syntax.Immediates".)

  This module exports openly (no explicit list): for a single-constructor type the generated
  @Sing@ constructor and its type synonym share a name (e.g. @SFuncType@), so importers must
  pull the constructors in via an open import — a named export would only bring the synonym.
-}
module Syntax.Types where

import Data.Singletons.Base.TH
import Data.Word (Word32, Word64)

{- | A WebAssembly value type, as one flat enumeration. The spec's nested grammar
  (@valtype ::= numtype | vectype | reftype@) is NOT encoded as constructors — that would
  force a wrapper into every type index (@'Num 'I32@). Instead the sub-categories are recovered
  as refinement-witness GADTs ('IsNum', 'IsInt', 'IsFloat' below): a value of @IsInt t@ is a
  proof that @t@ is an integer type that also says which one. So a stack index reads
  @'I32 ': 'I32@.

  Crucially, an instruction the spec restricts to a sub-category takes the corresponding
  witness, /not/ a bare @Sing (t :: ValType)@: @i32.add@ is @'IsNum' t@, @i32.eqz@ is
  @'IsInt' t@. The restriction is then enforced by construction and does not depend on which
  constructors 'ValType' currently happens to have: @FuncRef@ and @V128@ came later, and
  @funcref.add@ did not become representable.
-}
data ValType = I32 | I64 | F32 | F64 | V128 | FuncRef | ExternRef | ExnRef
    deriving stock (Eq, Show)

-- Singletons for the value type: the intrinsically-typed layer reflects these between the
-- term and type levels (e.g. a @Sing (s :: [ValType])@ stack shape, or a constant's type).
$(genSingletons [''ValType])

-- Decidable equality on the value-type singletons, so elaboration can compare stack types
-- with the library's 'Data.Singletons.Decide.decideEquality' instead of hand-rolling it.
$(singDecideInstances [''ValType])

{- | Whether two value types are the same, with the evidence: what the library's
  'Data.Singletons.Decide.decideEquality' answers, by a direct comparison. The library's goes
  through a class dictionary and builds a refutation nobody reads; an indirect call compares
  types on every call, and paid for both.
-}
sameValType :: Sing (a :: ValType) -> Sing (b :: ValType) -> Maybe (a :~: b)
sameValType a b = case a of
    SI32 -> case b of SI32 -> Just Refl; _ -> Nothing
    SI64 -> case b of SI64 -> Just Refl; _ -> Nothing
    SF32 -> case b of SF32 -> Just Refl; _ -> Nothing
    SF64 -> case b of SF64 -> Just Refl; _ -> Nothing
    SV128 -> case b of SV128 -> Just Refl; _ -> Nothing
    SFuncRef -> case b of SFuncRef -> Just Refl; _ -> Nothing
    SExternRef -> case b of SExternRef -> Just Refl; _ -> Nothing
    SExnRef -> case b of SExnRef -> Just Refl; _ -> Nothing

{- | Evidence that a value type is a numeric type (the spec's @numtype@), refined to which
  one. Carried by every instruction the spec restricts to @numtype@ — @const@, @add@/@sub@/
  @mul@/@div@, the comparisons, @load@/@store@, conversions, @select@ — so none of them can
  be built at a non-numeric type. Carrying the witness both restricts the type and identifies
  the concrete one, so it doubles as the singleton the interpreter dispatches on.
-}
data IsNum (t :: ValType) where
    I32IsNum :: IsNum 'I32
    I64IsNum :: IsNum 'I64
    F32IsNum :: IsNum 'F32
    F64IsNum :: IsNum 'F64

{- | Evidence that a value type is one of the two integer types, refined to its width.
  Carried by integer-only instructions (@eqz@, the bitwise/shift/count ops, narrow load/
  store) so their interpretation is total (no float/ref case can arise).
-}
data IsInt (t :: ValType) where
    I32IsInt :: IsInt 'I32
    I64IsInt :: IsInt 'I64

-- | The floating-point counterpart of 'IsInt', carried by float-only instructions.
data IsFloat (t :: ValType) where
    F32IsFloat :: IsFloat 'F32
    F64IsFloat :: IsFloat 'F64

{- | Decide whether a value type is numeric (resp. integer, floating-point), yielding the
  evidence when it is — the same shape as the library's 'decideEquality'. Elaboration uses
  these to reject e.g. @funcref.add@, @f32.and@ or @i32.sqrt@.
-}
decideNum :: Sing (t :: ValType) -> Maybe (IsNum t)
decideNum SI32 = Just I32IsNum
decideNum SI64 = Just I64IsNum
decideNum SF32 = Just F32IsNum
decideNum SF64 = Just F64IsNum
decideNum SV128 = Nothing
decideNum SFuncRef = Nothing
decideNum SExternRef = Nothing
decideNum SExnRef = Nothing

-- | The width in bytes of a numeric type (4 for i32/f32, 8 for i64/f64).
numBytes :: IsNum t -> Int
numBytes I32IsNum = 4
numBytes F32IsNum = 4
numBytes I64IsNum = 8
numBytes F64IsNum = 8

-- | Recover the value-type singleton from a numeric witness.
numSing :: IsNum t -> Sing t
numSing I32IsNum = SI32
numSing I64IsNum = SI64
numSing F32IsNum = SF32
numSing F64IsNum = SF64

decideInt :: Sing (t :: ValType) -> Maybe (IsInt t)
decideInt SI32 = Just I32IsInt
decideInt SI64 = Just I64IsInt
decideInt SF32 = Nothing
decideInt SF64 = Nothing
decideInt SV128 = Nothing
decideInt SFuncRef = Nothing
decideInt SExternRef = Nothing
decideInt SExnRef = Nothing

decideFloat :: Sing (t :: ValType) -> Maybe (IsFloat t)
decideFloat SF32 = Just F32IsFloat
decideFloat SF64 = Just F64IsFloat
decideFloat SI32 = Nothing
decideFloat SI64 = Nothing
decideFloat SV128 = Nothing
decideFloat SFuncRef = Nothing
decideFloat SExternRef = Nothing
decideFloat SExnRef = Nothing

{- | Evidence that a value type is a reference type (the spec's @reftype@), refined to which
  one: a reference to a function of the module, to a value of the host that the module cannot
  inspect, or to an exception that was thrown. Carried by the instructions on references and
  by a table's element type.
-}
data IsRef (t :: ValType) where
    FuncRefIsRef :: IsRef 'FuncRef
    ExternRefIsRef :: IsRef 'ExternRef
    ExnRefIsRef :: IsRef 'ExnRef

decideRef :: Sing (t :: ValType) -> Maybe (IsRef t)
decideRef SFuncRef = Just FuncRefIsRef
decideRef SExternRef = Just ExternRefIsRef
decideRef SExnRef = Just ExnRefIsRef
decideRef SI32 = Nothing
decideRef SI64 = Nothing
decideRef SF32 = Nothing
decideRef SF64 = Nothing
decideRef SV128 = Nothing

-- | Recover the value-type singleton from a reference witness.
refSing :: IsRef t -> Sing t
refSing FuncRefIsRef = SFuncRef
refSing ExternRefIsRef = SExternRef
refSing ExnRefIsRef = SExnRef

{- | A result type — the stack shape a block, loop, if, or function yields (the spec's
  @resulttype@). It is exactly a list of value types; the synonym names the intent so
  indices like a label context read as @[ResultType]@ rather than a bare @[[ValType]]@.
-}
type ResultType = [ValType]

{- | A function type, generic in what it calls a value type. The decoder produces it over plain
  'ValType' ('FuncType'). The shapes the typed AST is indexed by use
  'Syntax.TypesIFC.LabelledFuncType' instead, which also carries the bound on the calling
  context that SecWasm's function types have.
-}
data FuncTypeOf v = FuncType [v] [v] deriving stock (Eq, Show)

-- | A function type as decoded: over unlabelled value types.
type FuncType = FuncTypeOf ValType

{- | What a reference refers to, as a module writes it: any function, any external value or any
  exception; none of each (the type of a reference that can only be null); or a function of
  one of the module's function types, by the type's index. Garbage collection's heap types are
  not here.
-}
data HeapType = AnyFunction | NoFunction | AnyExtern | NoExtern | AnyException | NoException | OfType Word32
    deriving stock (Eq, Show)

{- | A value type as a module writes it. A 'ValType' is what the typed program knows of it: of a
  reference, which of the three kinds it is. The module also says whether the reference may be
  null and, for a function, of which type it is (the typed function references of WebAssembly
  3.0). Those are checked on the module as written ("Validation.References") and are not in
  the types of the typed program, which finds them out when it uses the reference.
-}
data WrittenType = Plain ValType | RefTo Bool HeapType
    deriving stock (Eq, Show)

-- | What the typed program knows of a written type.
erasedType :: WrittenType -> ValType
erasedType (Plain t) = t
erasedType (RefTo _ heap) = case heap of
    AnyFunction -> FuncRef
    NoFunction -> FuncRef
    OfType _ -> FuncRef
    AnyExtern -> ExternRef
    NoExtern -> ExternRef
    AnyException -> ExnRef
    NoException -> ExnRef

-- | A type of the typed program as a module that says no more would write it: a reference that may be null, to anything of its kind.
lifted :: ValType -> WrittenType
lifted t = case t of
    FuncRef -> RefTo True AnyFunction
    ExternRef -> RefTo True AnyExtern
    ExnRef -> RefTo True AnyException
    _ -> Plain t

{- | A written type with the function types it names written out, so that it means the same
  outside its module: what the types of an import and of what another module exports are
  compared as. (Without recursive types a function type names earlier ones only, so writing
  them out ends.)
-}
data ClosedType = ClosedPlain ValType | ClosedRef Bool ClosedHeap
    deriving stock (Eq, Show)

data ClosedHeap = Abstract HeapType | FunctionOf [ClosedType] [ClosedType]
    deriving stock (Eq, Show)

-- | A written type, closed over its module's function types.
closed :: [FuncTypeOf WrittenType] -> WrittenType -> ClosedType
closed types t = case t of
    Plain plain -> ClosedPlain plain
    RefTo nullable (OfType i) -> ClosedRef nullable $ case drop (fromIntegral i) types of
        FuncType params results : _ -> FunctionOf (map (closed (take (fromIntegral i) types)) params) (map (closed (take (fromIntegral i) types)) results)
        [] -> Abstract NoFunction
    RefTo nullable heap -> ClosedRef nullable (Abstract heap)

-- | @closedBelow a b@: a value of type @a@ may go where one of type @b@ is expected.
closedBelow :: ClosedType -> ClosedType -> Bool
closedBelow a b = case (a, b) of
    (ClosedPlain x, ClosedPlain y) -> x == y
    (ClosedRef nullable heap, ClosedRef nullable' heap') -> (not nullable || nullable') && heapBelow heap heap'
    _ -> False
  where
    heapBelow heap heap' = case (heap, heap') of
        (FunctionOf _ _, Abstract AnyFunction) -> True
        (Abstract NoFunction, Abstract AnyFunction) -> True
        (Abstract NoFunction, FunctionOf _ _) -> True
        (Abstract NoExtern, Abstract AnyExtern) -> True
        (Abstract NoException, Abstract AnyException) -> True
        _ -> heap == heap'

erasedFuncType :: FuncTypeOf WrittenType -> FuncType
erasedFuncType (FuncType params results) = FuncType (map erasedType params) (map erasedType results)

type BlockType = FuncType

-- | The size limits of a memory (in pages) or a table (in entries), as wide as the widest address.
data Limits = Limits
    { min :: Word64
    , max :: Maybe Word64
    }
    deriving stock (Eq, Show)

data AddrType = AddrI32 | AddrI64 deriving stock (Eq, Show)
data MemType = MemType
    { addrType :: AddrType
    , limits :: Limits
    }
    deriving stock (Eq, Show)

-- (The type-level counterpart of 'MemType' is 'Validation.Shape.MemShape'.)

{- data TableType = TableType Limits RefType deriving stock (Eq, Show) -}

{- | Whether a global may be written. 'Preserved' is a mutable global that a security policy
  marks ("Validation.Policy"): code may change it where a secret decided the control flow,
  provided it has its old value again when that code ends, which the machine checks. A decoded
  module has none; the stack pointer of compiled C is the one that needs it.
-}
data Mutability = Immutable | Mutable | Preserved deriving stock (Eq, Show)

-- | A global's type, generic in its value type for the same reason as 'FuncTypeOf'.
data GlobalTypeOf v = GlobalType Mutability v deriving stock (Eq, Show)

-- | A global's type as decoded: over unlabelled value types.
type GlobalType = GlobalTypeOf ValType

-- Singletons for the remaining promotable types. Split from the 'ValType' splice above because
-- Template Haskell needs each type defined before its splice, and the witnesses (which use the
-- value-type singleton) sit in between.
$(genSingletons [''Mutability, ''AddrType, ''FuncTypeOf, ''GlobalTypeOf])

{- | The value type of an address into a memory (or of an index into a table) of the given
  address type: what the instructions on it take and what @memory.size@ yields.
-}
type AddrVal :: AddrType -> ValType
type family AddrVal at where
    AddrVal 'AddrI32 = 'I32
    AddrVal 'AddrI64 = 'I64

addrValSing :: Sing (at :: AddrType) -> Sing (AddrVal at)
addrValSing SAddrI32 = SI32
addrValSing SAddrI64 = SI64

{- | The address type of a count of bytes that @memory.copy@ takes between two memories: the
  narrower of theirs.
-}
type MinAddr :: AddrType -> AddrType -> AddrType
type family MinAddr a b where
    MinAddr 'AddrI64 'AddrI64 = 'AddrI64
    MinAddr 'AddrI32 b = 'AddrI32
    MinAddr 'AddrI64 'AddrI32 = 'AddrI32

minAddrSing :: Sing (a :: AddrType) -> Sing (b :: AddrType) -> Sing (MinAddr a b)
minAddrSing SAddrI64 SAddrI64 = SAddrI64
minAddrSing SAddrI32 _ = SAddrI32
minAddrSing SAddrI64 SAddrI32 = SAddrI32
