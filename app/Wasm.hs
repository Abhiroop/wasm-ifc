{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{- | A type-safe embedded domain-specific language (DSL) for WebAssembly.
This module uses advanced Haskell type system features to ensure that
WebAssembly programs are stack-safe and type-correct at compile time.
-}
module Wasm where

-- (Length, WasmType(I64, I32), WasmType, ValStackShape, type (:+>+), CheckTopVecEqual, BlockType (..), FuncName, FuncTypeAnn (..), Take, FuncTypeAnn (..), Reverse, KnownWasmType (ForI32), LabelStackShape, GetLabelType, GetLabelCreationValStackLength, SomeValStackShape(..), KnownValStackShape (KnownValVNil, KnownValCons), GetSpecificValVec, LabelShape(..))

import Data.Bits
import Data.Int (Int32, Int64)
import Data.Word (Word32, Word64, Word8)
import Types
import Utils
import WasmModule

{-
TODO Summary:
1. Line 37: Better error messages
2. Line 66: Handle division by zero at type level if WASM spec allows
3. Line 139: Handle uninitialized local variables according to WASM spec
4. Line 297: missing WASM instructions
-}

{-
=============================================================================
LOCAL VARIABLE CONTEXT
=============================================================================
-}


{- TODO: Better error messages
   Improve type error messages for common mistakes like:
   - Stack underflow
   - Type mismatches
   - Invalid local access
-}

{-
=============================================================================
INSTRUCTIONS
=============================================================================
-}

{- | WebAssembly instructions with static stack and local variable tracking.
Each instruction is parameterized by:
  - inputStack: the stack shape before the instruction
  - outputStack: the stack shape after the instruction
  - locals: the local variable context (currently unchanged by most instructions)
-}
data
    Instruction
        (inputStack :: ValStackShape)
        (outputStack :: ValStackShape)
        (locals :: LocalsShape)
        (wasmModule :: WasmModule shape)
        (inputLabels :: LabelStackShape)
        (outputLabels :: LabelStackShape)
        (inSecPC :: [SecLevel])
        (outSecPC :: [SecLevel])
    where
    -- Constants: push a literal value onto the stack
    I32Const ::
        KnownSecLevel l ->
        Int32 ->
        Instruction
            inputStack
            ((I32 :~ (l :/\ Index Z secPC) ': inputStack) :: ValStackShape)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC
    -- i32 arithmetic operators (all pop two values, push one result)
    I32Add ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ l1 :/\ l2 :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC
    I32Sub ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC
    I32Mul ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC
    I32Div ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC
    -- TODO: Handle division by zero at type level if WASM spec allows,
    --       otherwise document that this fails at runtime
    --       In spec it is defined as: if i2 is 0, then the result is undefined.
    --       Also I think division exists for signed and unsigned ints
    I32RemU ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- remainder operation (unsigned)
            --      if i2 is zero then the output is undefined
    I32RemS ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- remainder operation (signed)
            --      if i2 is zero then the output is undefined -> the result has the sign of the first operator

    -- i32 comparison operators (pop two values, push i32 boolean result)
    I32EqZ ::
        Instruction
            ((I32 :~ l) ': inputStack)
            ((I32 :~ l :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- test if zero
    I32Eq ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- equal
    I32Neq ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- inequality
    I32LtS ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- less than (signed)
    I32LtU ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC 
            secPC-- less than (unsigned)
    I32LeS ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- less or equal (signed)
    I32LeU ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- less or equal (unsigned)
    I32GtS ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- greater than (signed)
    I32GtU ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- greater than (unsigned)
    I32GeS ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- greater or equal (signed)
    I32GeU ::
        Instruction
            ((I32 :~ l1) ': (I32 :~ l2) ': inputStack)
            ((I32 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- greater or equal (unsigned)
            -- more operators (e.g. bitwise negation, bitwise conjunction, ..., min, max)

    -- i64 arithmetic operators
    I64Const ::
        KnownSecLevel l ->
        Int64 ->
        Instruction
            inputStack
            ((I64 :~ (l :/\ t)) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            (t ': secPC)
            (t ': secPC)
    -- i64 arithmetic operators (all pop two values, push one result)

    I64Add ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC
    I64Sub ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC
    I64Mul ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC
    I64Div ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC
    -- differentiation signed vs unsigned?
    I64RemU ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC 
            secPC -- remainder operation (unsigned)
            --      if i2 is zero then the output is undefined
    I64RemS ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- remaidner operaton (signed)
            --      if i2 is zero then the output is undefined -> the result has the sign of the first operator

    -- I64 comparison operators
    I64EqZ ::
        Instruction
            ((I64 :~ l) ': inputStack)
            ((I64 :~ l :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- test if equal to zero
    I64Eq ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- equal
    I64Neq ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- inequality
    I64LeS ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- less or equal (signed)
    I64LeU ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- less or equal (unsigned)
    I64LtS ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- less than (signed)
    I64LtU ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- less than (unsigned)
    I64GtS ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- greater than (signed)
    I64GtU ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- greater than (unsigned)
    I64GeS ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- greater or equal (signed)
    I64GeU ::
        Instruction
            ((I64 :~ l1) ': (I64 :~ l2) ': inputStack)
            ((I64 :~ (l1 :/\ l2) :/\ Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- greater or equal (unsigned)

    -- Stack manipulation
    Drop ::
        Instruction
            (dropped ': inputStack)
            inputStack
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- remove top value from stack

    -- Local variable operations
    -- LocalGet: push the value of a local variable onto the stack
    LocalGet :: -- TODO: either restrict this such that low can only be get in low and high in high or have the unsafeCoerce
        (n ~ Length locals) =>
        SFin i n ->
        Instruction
            inputStack
            (CombineLocalSecLevel (Index i locals) (Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- pop a value from stack and store it in a local variable
    LocalSet :: -- TODO actually comment below not quite accurate -> we can only set the exact security level and type since we have it typed that way
        (n ~ Length locals
        , CanFlow (Index Z secPC) (GetSecLevel (Index i locals)) ~ 'True
        , CanFlow l (GetSecLevel (Index i locals)) ~ 'True) => -- we can only set a local if the current secPC is can flow into the level the local slot has
        SFin i n ->
        Instruction
            (GetWasmType (Index i locals) :~ l ': inputStack)
            -- ( GetWasmType (Index i locals) :~ GetSecLevel (Index i locals) :/\ Index Z secPC ': inputStack) => could do it like this but then need unsafeCoerce
            inputStack
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- pop val from stack
    -- pop val from stack
    -- push val to stack
    -- push val to stack
    -- localSet
    -- pop val from stack
    -- local[i] = val
    -- => in the end value is still on top of the stack as well as saved in the locals
    -- => technically the stack looks the same at the start and at the end?
    LocalTee ::
        (n ~ Length locals
        , CanFlow (Index Z secPC) (GetSecLevel (Index i locals)) ~ 'True
        , CanFlow l (GetSecLevel (Index i locals)) ~ 'True) =>
        SFin i n ->
        Instruction
            (GetWasmType (Index i locals) :~ l ': inputStack)
            (GetWasmType (Index i locals) :~ l ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC
    -- TODO: Handle uninitialized local variables according to WASM spec

    -- GlobalGet: push the value of a global variable onto the stack
    -- SAME HERE AS IN LOCALS
    GlobalGet ::
        forall
            (i :: Nat)
            (n :: Nat)
            (shape :: WasmModuleShape)
            (inputStack :: ValStackShape)
            (wasmModule :: WasmModule shape)
            (locals :: LocalsShape)
            (inputLabels :: LabelStackShape)
            (secPC :: [SecLevel]).
        (n ~ Length (GetGlobals wasmModule)) =>
        SFin i n ->
        Instruction
            inputStack
            (CombineSecLevel (GlobalTypeToWasmType (Index i (GetGlobals wasmModule))) (Index Z secPC) ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC
    -- GlobalSet: pop a value from stack and store it in a global variable => global type must be mutable where do we check this
    GlobalSet ::
        forall
            (i :: Nat)
            (n :: Nat)
            (shape :: WasmModuleShape)
            (inputStack :: ValStackShape)
            (wasmModule :: WasmModule shape)
            (locals :: LocalsShape)
            (inputLabels :: LabelStackShape)
            (secPC :: [SecLevel])
            (l :: SecLevel).
        ( n ~ Length (GetGlobals wasmModule)
        , IsVarMutability (GetMutability (Index i (GetGlobals wasmModule))) ~ 'True
        , CanFlow (Index Z secPC) (GetSecLevel (GlobalTypeToWasmType (Index i (GetGlobals wasmModule)))) ~ 'True
        , CanFlow l (GetSecLevel (GlobalTypeToWasmType (Index i (GetGlobals wasmModule)))) ~ 'True
        ) =>
        SFin i n ->
        Instruction
            (GetWasmType (GlobalTypeToWasmType (Index i (GetGlobals wasmModule))) :~ l ': inputStack) -- can do same here as local.set?
            inputStack
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- MEMORY INSTRUCTIONS
    -- need to make this an annotated Function such that we can know whether we load an I32, I64, F32, F64
    -- do we even have to access the memory like this: (Index offset (GetMems wasmModule))
    -- this simply returns a memory type which includes the limits of the memory
    -- We need the forall in order to use MemoryLoad @I32
    -- type equality ~ or :~:
    MemoryLoad ::
        forall
            (wasmtype :: WasmType)
            (secLevel :: SecLevel)
            (i :: Nat)
            (n :: Nat)
            (shape :: WasmModuleShape)
            (align :: Word32)
            (offset :: Word64)
            (inputStack :: ValStackShape)
            (wasmModule :: WasmModule shape)
            (locals :: LocalsShape)
            (inputLabels :: LabelStackShape)
            (lAddr :: SecLevel)
            (secPC :: [SecLevel]).
         (Loadable wasmtype
        , n ~ Length (GetMems wasmModule)
        , CanFlow (Index Z secPC) secLevel ~ 'True -- make sure we cannot annotate as low when the loaded value will be annotated with high anyways
        , CanFlow lAddr secLevel ~ 'True) => -- same as above
        SFin i n ->
        MemArg align offset -> -- ignore alignment for now, also not 100% sure why i32 has to be on top of stack
        Instruction
            (I64 :~ lAddr ': inputStack)
            (wasmtype :~ lAddr :/\ Index Z secPC :/\ secLevel ': inputStack)
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- MemoryStore: pop address and value from stack, store value at address in memory
    -- should we also make this annoted with the wasmtype?
    -- MemoryStore :: MemArg offset alignment -- add  constraint on limit of memory
    --          -> Instruction (I64 :> wasmtype :> inputStack) inputStack locals wasmModule

    -- MemoryStore with annotation to specify the type that is stored
    MemoryStore ::
        forall
            (wasmtype :: WasmType)
            (i :: Nat)
            (n :: Nat)
            (shape :: WasmModuleShape)
            (align :: Word32)
            (offset :: Word64)
            (inputStack :: ValStackShape)
            (wasmModule :: WasmModule shape)
            (locals :: LocalsShape)
            (inputLabels :: LabelStackShape)
            (lAddr :: SecLevel)
            (secLevel :: SecLevel)
            (secPC :: [SecLevel]).
        ( n ~ Length (GetMems wasmModule)
        , -- alignment must be multiple of 4 if wasmtype is I32 and multiple of 8 if wasmtype is I64
          -- ModEq align (ByteSize wasmtype) ~ 0, This one would only work with alignment also were a Nat not a word => however maybe we can evendo this at tha type level and keep it as a Word32 at execution time.
          Loadable wasmtype
        --  , CanFlow (Index Z secPC) secLevel ~ 'True, CanFlow secLevel lAddr ~ 'True -- anything can be stored anywhere so do not care about an annotation or anything
        ) =>
        SFin i n ->
        MemArg align offset ->
        Instruction
            -- also the the security level of the wasm type does not matter does it? so could just put a random l
            (I64 :~ lAddr ': wasmtype :~ secLevel ': inputStack) -- But we cannot store the security level of that value. So are we just overly cautious and mark everything coming from memory as high security level?
            inputStack
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            secPC -- Control flow instructions
    -- Block: a sequence of instructions that can be exited early with 'br'
    -- The stack shape arithmetic (+>+) ensures the block result sits on top of the input stack
    -- typeidx|[valtype?] => typeidx points to a type in the type section.
    -- valtype? represents a function type like [] -> [valtype?]
    -- so result of block can only be exactly one or no value
    -- also the result is the label type
    -- also the parameters of the block must be validated to be on top of the stack before entering!
    -- Block :: LabelIndex
    --       -> KnownStackShape outputShape -- represents the optional valtype however what about the typeidx? can't know the function type
    --       -> InstructionSequence inputStack (outputShape +>+ inputStack) locals wasmModule inputLabels outputLabels
    --       -> Instruction inputStack (outputShape +>+ inputStack) locals wasmModule inputLabels outputLabels

    -- technically the type like this would be defined at a type index in the types module
    -- Alternatively we can define just a WasmType in BlockType and then it would be the same as the func type []->[WasmType] => how should we go about it ? implement the types module? however not quite sure how we add types to the type module.
    Block ::
        forall
            (shape :: WasmModuleShape)
            (paramsStack :: ValStackShape)
            (resStack :: ValStackShape)
            (inputStack :: ValStackShape)
            (outputStack :: ValStackShape)
            (locals :: LocalsShape)
            (wasmModule :: WasmModule shape)
            (inputLabels :: LabelStackShape)
            (secPC :: [SecLevel])
            (outSecPC :: [SecLevel])
            (topSecPC :: SecLevel)
            (untouchableStack :: ValStackShape)
            (topSecPCOut :: SecLevel).
        ( inputStack ~ paramsStack +>+: untouchableStack
        , outputStack ~ resStack +>+: untouchableStack
        , topSecPC ~ Index Z secPC
        , CanFlow topSecPC topSecPCOut ~ 'True
        ) =>
        BlockType paramsStack resStack -> -- represents the optional valtype however what about the typeidx? can't know the function type
        InstructionSequence
            (paramsStack +>+: untouchableStack)
            (resStack +>+: untouchableStack)
            locals
            wasmModule
            ('LabelShape resStack (Length inputStack :- Length paramsStack) ': inputLabels)
            ('LabelShape resStack (Length inputStack :- Length paramsStack) ': inputLabels)
            (topSecPC ': secPC)
            (topSecPCOut ': outSecPC) ->
        Instruction (paramsStack +>+: untouchableStack) (resStack +>+: untouchableStack) locals 
            wasmModule inputLabels inputLabels secPC outSecPC
    -- Loop: a sequence of instructions that can be restarted with 'br'
    Loop :: -- Don't see a way of doing fix point -> therefore we just treat everything that is on top of unreachable stack as high sec level (really harsh overapproximation)
        forall
            (secLevelAnnotation :: SecLevel)
            (shape :: WasmModuleShape)
            (paramsStack :: ValStackShape)
            (resStack :: ValStackShape)
            (inputStack :: ValStackShape)
            (outputStack :: ValStackShape)
            (locals :: LocalsShape)
            (wasmModule :: WasmModule shape)
            (inputLabels :: LabelStackShape)
            (secPC :: [SecLevel])
            (outSecPC :: [SecLevel])
            (outSecLevel :: SecLevel)
            (untouchableStack :: ValStackShape).
        ( CheckTopVecEqual paramsStack inputStack ~ 'True
        , CheckTopVecEqual resStack outputStack ~ 'True
        , inputStack ~ paramsStack +>+: untouchableStack
        , outputStack ~ resStack +>+: untouchableStack -- ensure that the parameters of the block are on top of the input stack
        , CanFlow outSecLevel secLevelAnnotation ~ 'True -- we want to ensure that it cannot be annotated with low if there is a brif and the sec level changes to high
        ) =>
        BlockType paramsStack resStack ->
        InstructionSequence
            (paramsStack +>+:untouchableStack)
            (resStack +>+: untouchableStack)
            locals
            wasmModule
            ('LabelShape paramsStack (Length inputStack :- Length paramsStack) ': inputLabels)
            ('LabelShape paramsStack (Length inputStack :- Length paramsStack) ': inputLabels)
            (secLevelAnnotation ': secPC)
            (outSecLevel ': outSecPC) ->
        Instruction (paramsStack +>+: untouchableStack) (resStack +>+: untouchableStack) locals 
            wasmModule inputLabels inputLabels secPC outSecPC
    -- If: conditional execution (pops i32 condition, executes one of two branches)
    If :: forall paramsStack resStack inputStack outputStack outputStack1 outputStack2 locals wasmModule inputLabels secPC lCond untouchableStack outTopSecPC1 outTopSecPC2
        outSecPC1 outSecPC2.
        ( 
        outputStack ~ CombineSecTypes outputStack1 outputStack2
        , inputStack ~ paramsStack +>+: untouchableStack
        , outputStack ~ resStack +>+: untouchableStack
        , CanFlow (lCond :/\ Index Z secPC) outTopSecPC1 ~ 'True
        , CanFlow (lCond :/\ Index Z secPC) outTopSecPC2 ~ 'True
        , Length outSecPC1 ~ Length outSecPC2
        , Length outSecPC1 ~ Length secPC
        , Length outSecPC2 ~ Length secPC
        ) =>
        BlockType paramsStack resStack ->
        InstructionSequence
            (paramsStack +>+: untouchableStack)
            outputStack1
            locals
            wasmModule
            ('LabelShape resStack (Length inputStack :- Length paramsStack) ': inputLabels)
            ('LabelShape resStack (Length inputStack :- Length paramsStack) ': inputLabels)
            ((lCond :/\ Index Z secPC) ': secPC)
            (outTopSecPC1 ': outSecPC1) -> -- then branch
        InstructionSequence
            (paramsStack +>+: untouchableStack)
            outputStack2
            locals
            wasmModule
            ('LabelShape resStack (Length inputStack :- Length paramsStack) ': inputLabels)
            ('LabelShape resStack (Length inputStack :- Length paramsStack) ': inputLabels)
            ((lCond :/\ Index Z secPC) ': secPC)
            (outTopSecPC2 ': outSecPC2) -> -- else branch
        Instruction
            (I32 :~ lCond ': (paramsStack +>+:untouchableStack)) -- l condition says whether the condition itself is high or low security level
            outputStack
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            (CombineSecLevelStacks outSecPC1 outSecPC2)
    -- Br: unconditional branch to a label
    -- Nat is the nesting depth of how many nested blocks/loops to break out of
    -- I guess this means we need an additional stack or vector that stores the current
    -- block nesting depth
    -- this is needed because we want to be able to validate that the labelidx
    -- is not out of bounds.
    -- 2. need to validate that the input stack is some wasmtypes and the the labeltype

    -- Version that is close to what should be done in execution
    -- Br    ::  (LessThan n (StackLength labels) ~ 'True, -- check whether labelidx is valid
    --             PopTopUntilLabelFromStack n (StackLength (GetLabelType n labels)) Empty inputStack ~ GetLabelType n labels) =>
    --             -- second constraint checks:
    --             -- pops the top of the stack until the correctly nested label is found
    --             -- removes all the labels on the inputStack until there
    --             -- checks the arity of the label type
    --             -- returns the top of the stack with the correct arity
    --             -- compares whether now the top of the stack is equal to the label type
    --           StackIndex n
    --           -> Instruction inputStack outputStack locals wasmModule labels

    -- This does not compile
    -- Br   :: forall (i::Nat) (l :: Nat) (n ::Nat) (m::Nat) (inputLabels :: LabelStack ('S l)) (inputStack :: StackShape) (outputStack :: StackShape) (locals :: LocalsShape n) (wasmModule :: WasmModule m).
    --         StackIndex i l
    --         -> Instruction (GetLabelType i inputLabels +>+ inputStack) outputStack locals wasmModule inputLabels (RemoveLabels i inputLabels) -- after branching, the labels above the target label are removed from the label stack?

    -- This version compiles
    -- Checks whether the top of the input stack is equal to the label type as a constraint

    -- Br    :: forall (i :: Nat) (l :: Nat) (shape :: WasmModuleShape) (inputLabels :: LabelStackShape) (inputStack :: ValStackShape) (outputStack :: ValStackShape)  (locals :: LocalsShape) (wasmModule :: WasmModule shape) .
    --     (CheckTopVecEqual (GetLabelType (Index i inputLabels)) inputStack ~ 'True,
    --     (Take (Arity (Index i inputLabels)) inputStack :+>+
    --       Take (Height (Index i inputLabels)) (Reverse inputStack))
    --       ~ outputStack,
    --       l ~ Length inputLabels
    --     ) =>
    --         SFin i l
    --         -> Instruction inputStack
    --                        outputStack
    --                        locals
    --                        wasmModule
    --                        inputLabels
    --                        inputLabels

    -- Br ::
    --     forall
    --         (i :: Nat)
    --         (l :: Nat)
    --         (shape :: WasmModuleShape)
    --         (targetLabel :: LabelShape)
    --         (remainingLabels :: LabelStackShape)
    --         (inputLabels :: LabelStackShape)
    --         (inputStack :: ValStackShape)
    --         (outputStack :: ValStackShape)
    --         (locals :: LocalsShape)
    --         (wasmModule :: WasmModule shape)
    --         (topLabel :: LabelShape)
    --         (tailLabels :: LabelStackShape)
    --         (aboveInnermostLabel :: ValStackShape)
    --         (secPC :: [SecLevel]).
    --     ( topLabel : tailLabels ~ inputLabels
    --     , aboveInnermostLabel ~ Reverse (Drop (Height topLabel) (Reverse inputStack))
    --     , targetLabel : remainingLabels ~ Drop i inputLabels
    --     , CheckTopVecEqualInclSecLevel (GetLabelType targetLabel) aboveInnermostLabel ~ 'True
    --     -- actually remove this constraint because it stopped as from adding random things after branch which is actually possible in wasm
    --     -- , ( Take (Arity targetLabel) inputStack
    --     --         +>+: Reverse (Take (Height targetLabel) (Reverse inputStack))
    --     --   )
    --     --     ~ outputStack
    --     , l ~ Length inputLabels
    --     , LessThan l (Length secPC) ~ 'True
    --     ) =>
    --     SFin i l ->
    --     Instruction
    --         inputStack
    --         outputStack
    --     --     ( Take (Arity targetLabel) inputStack
    --     --         +>+: Reverse (Take (Height targetLabel) (Reverse inputStack))
    --     --   )
    --         locals
    --         wasmModule
    --         inputLabels
    --         inputLabels
    --         secPC
    --         secPC

    -- Option 2 looks more like rule:
    Br ::
        -- forall
        --     (i :: Nat)
        --     (l :: Nat)
        --     (shape :: WasmModuleShape)
        --     (targetLabel :: LabelShape)
        --     (remainingLabels :: LabelStackShape)
        --     (inputLabels :: LabelStackShape)
        --     (inputStack :: ValStackShape)
        --     (outputStack :: ValStackShape)
        --     (locals :: LocalsShape)
        --     (wasmModule :: WasmModule shape)
        --     (topLabel :: LabelShape)
        --     (tailLabels :: LabelStackShape)
        --     (aboveInnermostLabel :: ValStackShape)
        --     (topL :: SecLevel)
        --     (targetSecLevel :: SecLevel)
        --     (outTargetSecLevel :: SecLevel)
        --     (restSecPC :: [SecLevel])
        --     (outTopSecLevels :: [SecLevel])
        --     (secPC :: [SecLevel])
        --     (unchangedSecPC :: [SecLevel]).
        ( targetLabel : remainingLabels ~ Drop i inputLabels
        , topL ': restSecPC ~ secPC
        , targetSecLevel ': unchangedSecPC ~ Drop i secPC
        , CombineSecLevelList topL (Take i secPC) ~ outTopSecLevels -- everything between current and target sec level
        , outTargetSecLevel ~ (topL :/\ targetSecLevel) -- the target sec level is also influenced
        , topLabel : tailLabels ~ inputLabels
        , aboveInnermostLabel ~ Reverse (Drop (Height topLabel) (Reverse inputStack))
        , CheckTopVecEqualInclSecLevel (GetLabelType targetLabel) aboveInnermostLabel ~ 'True
        -- actually remove this constraint because it stopped as from adding random things after branch which is actually possible in wasm
        -- , ( Take (Arity targetLabel) inputStack
        --         +>+: Reverse (Take (Height targetLabel) (Reverse inputStack))
        --   )
        --     ~ outputStack
        , l ~ Length inputLabels
        , LessThan l (S (Length restSecPC)) ~ 'True
        , LessThan l (Length secPC) ~ 'True
        ) =>
        SFin i l ->
        Instruction
            inputStack
            outputStack
        --     ( Take (Arity targetLabel) inputStack
        --         +>+: Reverse (Take (Height targetLabel) (Reverse inputStack))
        --   )
            locals
            wasmModule
            inputLabels
            inputLabels
            secPC
            (outTopSecLevels +>+: (outTargetSecLevel ': unchangedSecPC))

    -- BrIf: conditional branch (pops i32 condition)
    -- DINA: Problem => either we branch then we have the conditions below for the outputStack or we don't branch
    -- and then the outputStack is just the inputStack minus the i32 condition
    -- According to SecWasm all labels until i+1 should be tainted, and the level of the condition should be able to flow into the level of the block that the target label flows into
    BrIf ::
        forall
            (i :: Nat)
            (l :: Nat)
            (shape :: WasmModuleShape)
            (targetLabel :: LabelShape)
            (remainingLabels :: LabelStackShape)
            (inputLabels :: LabelStackShape)
            (inputStack :: ValStackShape)
            (locals :: LocalsShape)
            (wasmModule :: WasmModule shape)
            (secPC :: [SecLevel])
            (restSecPC :: [SecLevel])
            (topL :: SecLevel)
            (targetSecLevel :: SecLevel)
            (unchangedSecPC :: [SecLevel])
            (outTopSecLevels :: [SecLevel])
            (outTargetSecLevel :: SecLevel)
            (lCond :: SecLevel). -- whether condition is high or low security level
        ( targetLabel : remainingLabels ~ Drop i inputLabels
        , l ~ Length inputLabels
        , LessThan l (S (Length restSecPC)) ~ 'True
        , topL ': restSecPC ~ secPC
        , targetSecLevel ': unchangedSecPC ~ Drop i secPC
        , CombineSecLevelList (lCond :/\ topL) (Take i secPC) ~ outTopSecLevels -- everything between current and target sec level
        , outTargetSecLevel ~ (lCond :/\ topL :/\ targetSecLevel) -- the target sec level is also influenced
        ) =>
        SFin i l ->
        Instruction
            (I32 :~ lCond ': inputStack)
            inputStack
            locals
            wasmModule
            inputLabels
            inputLabels
            (topL ': restSecPC)
            (outTopSecLevels +>+: (outTargetSecLevel ': unchangedSecPC))

    -- "naive" way
    Call ::
        FuncName ->
        FuncTypeAnn inputStack outputStack ->
        Instruction inputStack outputStack locals
            wasmModule inputLabels outputLabels secPC secPC
    -- Call  :: FuncName f -> Instruction (GetParamsOf (GetTypeOfFunc f wasmModule)) (GetResultsOf (GetTypeOfFunc f wasmModule)) locals wasmModule inputLabels outputLabels

    Leave ::
        Instruction
            inputStack
            inputStack
            locals
            wasmModule
            (topLabel ': outputLabels)
            outputLabels
            secPC
            secPC

-- TODO: missing WASM instructions

class Loadable (wasmType :: WasmType) where
    byteSize :: WasmType
    load :: MemoryArray -> Word64 -> RuntimeTypeOf wasmType
    store :: MemoryArray -> Word64 -> RuntimeTypeOf wasmType -> MemoryArray

readByte :: MemoryArray -> Int -> Word8
readByte mem addr = mem !! addr

instance Loadable I32 where
    byteSize = I32
    load memArray addr =
        let byte0 = readByte memArray (fromIntegral addr)
            byte1 = readByte memArray (fromIntegral (addr + 1))
            byte2 = readByte memArray (fromIntegral (addr + 2))
            byte3 = readByte memArray (fromIntegral (addr + 3))
         in fromIntegral
                ( (fromIntegral byte0 :: RuntimeTypeOf I32)
                    + (fromIntegral byte1 `shiftL` 8 :: RuntimeTypeOf I32)
                    + (fromIntegral byte2 `shiftL` 16 :: RuntimeTypeOf I32)
                    + (fromIntegral byte3 `shiftL` 24 :: RuntimeTypeOf I32)
                ) ::
                RuntimeTypeOf I32
    store memArray addr value =
        let byte0 = fromIntegral (value .&. 0xFF) :: Word8
            byte1 = fromIntegral ((value `shiftR` 8) .&. 0xFF) :: Word8
            byte2 = fromIntegral ((value `shiftR` 16) .&. 0xFF) :: Word8
            byte3 = fromIntegral ((value `shiftR` 24) .&. 0xFF) :: Word8
            -- take addr mem ++ [val] ++ drop (addr + 1) mem
            memArray1 =
                take (fromIntegral addr) memArray
                    ++ [byte0]
                    ++ drop (fromIntegral addr + 1) memArray
            memArray2 =
                take (fromIntegral (addr + 1)) memArray1
                    ++ [byte1]
                    ++ drop (fromIntegral (addr + 1) + 1) memArray1
            memArray3 =
                take (fromIntegral (addr + 2)) memArray2
                    ++ [byte2]
                    ++ drop (fromIntegral (addr + 2) + 1) memArray2
            memArray4 =
                take (fromIntegral (addr + 3)) memArray3
                    ++ [byte3]
                    ++ drop (fromIntegral (addr + 3) + 1) memArray3
         in memArray4

instance Loadable I64 where
    byteSize = I64
    load memArray addr =
        let byte0 = readByte memArray (fromIntegral addr)
            byte1 = readByte memArray (fromIntegral (addr + 1))
            byte2 = readByte memArray (fromIntegral (addr + 2))
            byte3 = readByte memArray (fromIntegral (addr + 3))
            byte4 = readByte memArray (fromIntegral (addr + 4))
            byte5 = readByte memArray (fromIntegral (addr + 5))
            byte6 = readByte memArray (fromIntegral (addr + 6))
            byte7 = readByte memArray (fromIntegral (addr + 7))
         in fromIntegral byte0
                + (fromIntegral byte1 `shiftL` 8)
                + (fromIntegral byte2 `shiftL` 16)
                + (fromIntegral byte3 `shiftL` 24)
                + (fromIntegral byte4 `shiftL` 32)
                + (fromIntegral byte5 `shiftL` 40)
                + (fromIntegral byte6 `shiftL` 48)
                + (fromIntegral byte7 `shiftL` 56) ::
                RuntimeTypeOf I64
    store memArray addr value =
        let byte0 = fromIntegral (value .&. 0xFF) :: Word8
            byte1 = fromIntegral ((value `shiftR` 8) .&. 0xFF) :: Word8
            byte2 = fromIntegral ((value `shiftR` 16) .&. 0xFF) :: Word8
            byte3 = fromIntegral ((value `shiftR` 24) .&. 0xFF) :: Word8
            byte4 = fromIntegral ((value `shiftR` 32) .&. 0xFF) :: Word8
            byte5 = fromIntegral ((value `shiftR` 40) .&. 0xFF) :: Word8
            byte6 = fromIntegral ((value `shiftR` 48) .&. 0xFF) :: Word8
            byte7 = fromIntegral ((value `shiftR` 56) .&. 0xFF) :: Word8
            memArray1 =
                take (fromIntegral addr) memArray
                    ++ [byte0]
                    ++ drop (fromIntegral addr + 1) memArray
            memArray2 =
                take (fromIntegral (addr + 1)) memArray1
                    ++ [byte1]
                    ++ drop (fromIntegral (addr + 1) + 1) memArray1
            memArray3 =
                take (fromIntegral (addr + 2)) memArray2
                    ++ [byte2]
                    ++ drop (fromIntegral (addr + 2) + 1) memArray2
            memArray4 =
                take (fromIntegral (addr + 3)) memArray3
                    ++ [byte3]
                    ++ drop (fromIntegral (addr + 3) + 1) memArray3
            memArray5 =
                take (fromIntegral (addr + 4)) memArray4
                    ++ [byte4]
                    ++ drop (fromIntegral (addr + 4) + 1) memArray4
            memArray6 =
                take (fromIntegral (addr + 5)) memArray5
                    ++ [byte5]
                    ++ drop (fromIntegral (addr + 5) + 1) memArray5
            memArray7 =
                take (fromIntegral (addr + 6)) memArray6
                    ++ [byte6]
                    ++ drop (fromIntegral (addr + 6) + 1) memArray6
            memArray8 =
                take (fromIntegral (addr + 7)) memArray7
                    ++ [byte7]
                    ++ drop (fromIntegral (addr + 7) + 1) memArray7
         in memArray8

{-
=============================================================================
INSTRUCTION SEQUENCES
=============================================================================
-}

{- | A sequence of WebAssembly instructions.
This represents a linear sequence of instructions where the output stack
of one instruction becomes the input stack of the next.
-}
infixr 5 :| -- Right-associative, like list construction

data
    InstructionSequence
        (initialVal :: ValStackShape)
        (finalVal :: ValStackShape)
        (locals :: LocalsShape)
        (wasmModule :: WasmModule shape)
        (initialLab :: LabelStackShape)
        (finalLab :: LabelStackShape)
        (inSecPC :: [SecLevel])
        (outSecPC :: [SecLevel])
    where
    End ::
        InstructionSequence
            initialVal
            initialVal
            locals
            wasmModule
            initialLab
            initialLab
            inSecPC
            inSecPC -- Base case: empty sequence (identity)
    (:|) :: (
            Length inSecPC ~ Length outSecPC
            , Length inSecPC ~ Length intermediateSecPC
            , Length outSecPC ~ Length intermediateSecPC
            ) =>
        Instruction
            initialVal
            intermediateVal
            locals
            wasmModule
            initialLab
            intermediateLab
            inSecPC
            intermediateSecPC -- need this for branch if instructions
            -- Inductive case: first instruction
        -> InstructionSequence
            intermediateVal
            finalVal
            locals
            wasmModule
            intermediateLab
            finalLab
            intermediateSecPC
            outSecPC -- rest of sequence
        -> InstructionSequence
            initialVal
            finalVal
            locals
            wasmModule
            initialLab
            finalLab
            inSecPC
            outSecPC -- combined sequence

{-
=============================================================================
FUNCTIONS
=============================================================================
-}

{- | A complete WebAssembly function.
Functions start with an empty stack and produce the specified final stack shape.
The locals context represents the function's parameters and local variables.
-}
data
    Function
        (inputStack :: ValStackShape)
        (resultStack :: ValStackShape)
        (locals :: LocalsShape)
        (outputLabels :: LabelStackShape)
        (wasmModule :: WasmModule shape)
        (secPC :: [SecLevel])
        (outSecPC :: [SecLevel])
    where
    Function ::
        FuncTypeAnn inputStack resultStack ->
        InstructionSequence
            inputStack
            resultStack
            locals
            wasmModule
            outputLabels
            outputLabels
            secPC
            outSecPC ->
        Function inputStack resultStack locals outputLabels wasmModule secPC outSecPC

-- add a new type that captures the function type annotation, i.e.
-- FuncTypeAnn inputStack resultStack ->
