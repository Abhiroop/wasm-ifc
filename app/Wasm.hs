{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


-- | A type-safe embedded domain-specific language (DSL) for WebAssembly.
-- This module uses advanced Haskell type system features to ensure that
-- WebAssembly programs are stack-safe and type-correct at compile time.
module Wasm where

import Data.Int (Int32, Int64)
import Data.Word (Word32, Word64)
import Types --(Length, WasmType(I64, I32), WasmType, ValStackShape, type (:+>+), CheckTopVecEqual, BlockType (..), FuncName, FuncTypeAnn (..), Take, FuncTypeAnn (..), Reverse, KnownWasmType (ForI32), LabelStackShape, GetLabelType, GetLabelCreationValStackLength, SomeValStackShape(..), KnownValStackShape (KnownValVNil, KnownValCons), GetSpecificValVec, LabelShape(..))
import Utils
import WasmModule (WasmModule(..), GetGlobals, GlobalTypeToWasmType, MemArg(SMemArg), WasmModuleShape(..), GetMemoriesShape, GetGlobalsShape, GlobalType(..), Mutability(..))

{-
=============================================================================
LOCAL VARIABLE CONTEXT
=============================================================================
-}

-- | Reference to a local variable slot (0-indexed).
type SlotIndex = Nat

type LocalsShape = [WasmType]

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

-- | WebAssembly instructions with static stack and local variable tracking.
-- Each instruction is parameterized by:
--   - inputStack: the stack shape before the instruction
--   - outputStack: the stack shape after the instruction
--   - locals: the local variable context (currently unchanged by most instructions)
data Instruction (inputStack :: ValStackShape) (outputStack :: ValStackShape) (locals :: LocalsShape) (wasmModule::WasmModule shape) (inputLabels:: LabelStackShape) (outputLabels :: LabelStackShape) where -- 

    -- Constants: push a literal value onto the stack
    I32Const :: Int32 -> Instruction inputStack ((I32 ': inputStack) :: ValStackShape) locals wasmModule inputLabels inputLabels

    -- i32 arithmetic operators (all pop two values, push one result)
    I32Add :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels
    I32Sub :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels
    I32Mul :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels
    I32Div :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels
    -- TODO: Handle division by zero at type level if WASM spec allows,
    --       otherwise document that this fails at runtime
    --       In spec it is defined as: if i2 is 0, then the result is undefined.
    --       Also I think division exists for signed and unsigned ints
    I32RemU :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels  --remainder operation (unsigned)
    --      if i2 is zero then the output is undefined
    I32RemS :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels  -- remainder operation (signed)
    --      if i2 is zero then the output is undefined -> the result has the sign of the first operator

    -- i32 comparison operators (pop two values, push i32 boolean result)
    I32EqZ :: Instruction (I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels            -- test if zero
    I32Eq  :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- equal
    I32Neq :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- inequality
    I32LtS :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- less than (signed)
    I32LtU :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- less than (unsigned)
    I32LeS :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- less or equal (signed)
    I32LeU :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- less or equal (unsigned)
    I32GtS :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- greater than (signed)
    I32GtU :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- greater than (unsigned)
    I32GeS :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- greater or equal (signed)
    I32GeU :: Instruction (I32 ': I32 ': inputStack) (I32 ': inputStack) locals wasmModule inputLabels inputLabels    -- greater or equal (unsigned)
    -- more operators (e.g. bitwise negation, bitwise conjunction, ..., min, max)

    -- i64 arithmetic operators
    I64Const :: Int64 -> Instruction inputStack ((I64 ': inputStack) :: ValStackShape) locals wasmModule inputLabels inputLabels
     -- i64 arithmetic operators (all pop two values, push one result)

    I64Add :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels
    I64Sub :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels
    I64Mul :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels
    I64Div :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels
    -- differentiation signed vs unsigned?
    I64RemU :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels --remainder operation (unsigned)
    --      if i2 is zero then the output is undefined
    I64RemS :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels -- remaidner operaton (signed)
    --      if i2 is zero then the output is undefined -> the result has the sign of the first operator

    -- I64 comparison operators
    I64EqZ :: Instruction (I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- test if equal to zero
    I64Eq  :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- equal
    I64Neq :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- inequality
    I64LeS :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- less or equal (signed)
    I64LeU :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- less or equal (unsigned)
    I64LtS :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- less than (signed)
    I64LtU :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- less than (unsigned)
    I64GtS :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- greater than (signed)
    I64GtU :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- greater than (unsigned)
    I64GeS :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- greater or equal (signed)
    I64GeU :: Instruction (I64 ': I64 ': inputStack) (I64 ': inputStack) locals wasmModule inputLabels inputLabels   -- greater or equal (unsigned)


    -- Stack manipulation
    Drop :: Instruction (dropped ': inputStack) inputStack locals wasmModule inputLabels inputLabels   -- remove top value from stack

    -- Local variable operations
    -- LocalGet: push the value of a local variable onto the stack
    LocalGet :: SFin i n
             -> Instruction inputStack (Index i locals ': inputStack) locals wasmModule inputLabels inputLabels

    -- LocalSet: pop a value from stack and store it in a local variable
    LocalSet :: SFin i n
             -> Instruction (Index i locals ': inputStack) inputStack locals wasmModule inputLabels inputLabels
    -- LocalTee:
    -- pop val from stack
    -- push val to stack
    -- push val to stack
    -- localSet
        -- pop val from stack
        -- local[i] = val
    -- => in the end value is still on top of the stack as well as saved in the locals
        -- => technically the stack looks the same at the start and at the end?
    LocalTee :: SFin i n
             -> Instruction (Index i locals ': inputStack) (Index i locals ': inputStack) locals wasmModule inputLabels inputLabels
    -- TODO: Handle uninitialized local variables according to WASM spec

    -- GlobalGet: push the value of a global variable onto the stack
    GlobalGet :: forall (i :: Nat) (n :: Nat) (m :: Nat) (l :: Nat) (ivs :: Nat) (shape :: WasmModuleShape) (inputStack :: ValStackShape) (wasmModule :: WasmModule shape) (locals :: LocalsShape) (inputLabels :: LabelStackShape).
        (n ~ GetGlobalsShape shape) =>
        SFin i n
        -> Instruction inputStack (GlobalTypeToWasmType (Index i (GetGlobals wasmModule)) ': inputStack) locals wasmModule inputLabels inputLabels

    -- GlobalSet: pop a value from stack and store it in a global variable => global type must be mutable where do we check this
    GlobalSet :: forall (i :: Nat) (n :: Nat) (m :: Nat) (l :: Nat) (ivs :: Nat) (shape :: WasmModuleShape) (inputStack :: ValStackShape) (wasmModule :: WasmModule shape) (locals :: LocalsShape) (inputLabels :: LabelStackShape).
        (n ~ GetGlobalsShape shape) =>
        SFin i n
        -> Instruction (GlobalTypeToWasmType (Index i (GetGlobals wasmModule)) ': inputStack) inputStack locals wasmModule inputLabels inputLabels


    -- MEMORY INSTRUCTIONS
    -- need to make this an annotated Function such that we can know whether we load an I32, I64, F32, F64
    -- do we even have to access the memory like this: (Index offset (GetMems wasmModule))
        -- this simply returns a memory type which includes the limits of the memory
    -- We need the forall in order to use MemoryLoad @I32
    -- type equality ~ or :~:
    MemoryLoad :: forall (wasmtype::WasmType) (i :: Nat) (n :: Nat) (m :: Nat) (k :: Nat) (ivs :: Nat) (shape :: WasmModuleShape) (align :: Word32) (offset :: Word64) (inputStack :: ValStackShape) (wasmModule :: WasmModule shape) (locals :: LocalsShape) (inputLabels :: LabelStackShape) .
        (n ~ GetMemoriesShape shape) => 
             SFin i n
             -> MemArg align offset  -- ignore alignment for now, also not 100% sure why i32 has to be on top of stack
             -> Instruction (I32 ': inputStack) (wasmtype ': inputStack) locals wasmModule inputLabels inputLabels
    -- MemoryStore: pop address and value from stack, store value at address in memory
        -- should we also make this annoted with the wasmtype?
    -- MemoryStore :: MemArg offset alignment -- add  constraint on limit of memory
    --          -> Instruction (I32 :> wasmtype :> inputStack) inputStack locals wasmModule

    -- MemoryStore with annotation to specify the type that is stored
    MemoryStore :: forall (wasmtype :: WasmType) (i :: Nat) (n :: Nat) (shape :: WasmModuleShape) align offset inputStack (wasmModule :: WasmModule shape) locals inputLabels outputLabels.
        (n ~ GetMemoriesShape shape) => 
        SFin i n
        -> MemArg align offset
        -> Instruction (I32 ': wasmtype ': inputStack) inputStack locals wasmModule inputLabels outputLabels


    -- Control flow instructions
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
    Block :: forall (shape :: WasmModuleShape) (paramsStack :: ValStackShape) (resStack :: ValStackShape) (inputStack :: ValStackShape) (outputStack :: ValStackShape) (locals :: LocalsShape) (wasmModule :: WasmModule shape) (inputLabels :: LabelStackShape).
            (CheckTopVecEqual paramsStack inputStack ~ 'True,
                CheckTopVecEqual resStack outputStack ~ 'True)  -- ensure that the parameters of the block are on top of the input stack
          => BlockType paramsStack resStack -- represents the optional valtype however what about the typeidx? can't know the function type
          -> InstructionSequence inputStack outputStack locals wasmModule ('LabelShape resStack (Length inputStack) ': inputLabels) ('LabelShape resStack (Length inputStack) ': inputLabels)
          -> Instruction inputStack outputStack locals wasmModule inputLabels inputLabels

    -- Loop: a sequence of instructions that can be restarted with 'br'
    Loop  :: forall (shape :: WasmModuleShape) (paramsStack :: ValStackShape) (resStack :: ValStackShape) (inputStack :: ValStackShape) (outputStack :: ValStackShape) (locals :: LocalsShape) (wasmModule :: WasmModule shape) (inputLabels :: LabelStackShape).
            (CheckTopVecEqual paramsStack inputStack ~ 'True,
                CheckTopVecEqual resStack outputStack ~ 'True)  -- ensure that the parameters of the block are on top of the input stack
          => BlockType paramsStack resStack
          -> InstructionSequence inputStack outputStack locals wasmModule ('LabelShape paramsStack (Length inputStack) ': inputLabels) ( 'LabelShape paramsStack (Length inputStack) ': inputLabels)
          -> Instruction inputStack outputStack locals wasmModule inputLabels inputLabels

    -- If: conditional execution (pops i32 condition, executes one of two branches)
    If    :: (CheckTopVecEqual ( paramsStack) ( inputStack) ~ 'True,
                CheckTopVecEqual ( resStack) ( outputStack) ~ 'True)  -- ensure that the parameters of the block are on top of the input stack
          => BlockType paramsStack resStack
          -> InstructionSequence inputStack outputStack locals wasmModule ('LabelShape resStack (Length inputStack) ': inputLabels) ('LabelShape resStack (Length inputStack) ': inputLabels)     -- then branch
          -> InstructionSequence inputStack outputStack locals wasmModule ('LabelShape resStack (Length inputStack) ': inputLabels) ('LabelShape resStack (Length inputStack) ': inputLabels)     -- else branch
          -> Instruction (I32 ': inputStack) outputStack locals wasmModule inputLabels inputLabels

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

    Br    :: forall (i :: Nat) (l :: Nat) (shape :: WasmModuleShape) (targetLabel :: LabelShape) (remainingLabels :: LabelStackShape) (inputLabels :: LabelStackShape) (inputStack :: ValStackShape) (outputStack :: ValStackShape)  (locals :: LocalsShape) (wasmModule :: WasmModule shape) .
        (CheckTopVecEqual (GetLabelType (Index i inputLabels)) inputStack ~ 'True,
        targetLabel : remainingLabels ~ Drop i inputLabels,
        (Take (Arity targetLabel) inputStack :+>+
          Take (Height targetLabel) (Reverse inputStack))
          ~ outputStack,
          l ~ Length inputLabels
        ) => 
            SFin i l
            -> Instruction inputStack
                           outputStack
                           locals
                           wasmModule
                           inputLabels
                           inputLabels

    -- BrIf: conditional branch (pops i32 condition)
    -- DINA: Problem => either we branch then we have the conditions below for the outputStack or we don't branch
    -- and then the outputStack is just the inputStack minus the i32 condition
    BrIf  :: forall (i :: Nat) (l :: Nat) (shape :: WasmModuleShape) (targetLabel :: LabelShape) (remainingLabels :: LabelStackShape) (inputLabels :: LabelStackShape) (inputStack :: ValStackShape) (locals :: LocalsShape) (wasmModule :: WasmModule shape) .
    -- inputStack ~ outputStack =>
        -- (CheckTopVecEqual (GetLabelType (Index i inputLabels)) (  inputStack) ~ 'True) =>
        (targetLabel : remainingLabels ~ Drop i inputLabels,
         l ~ Length inputLabels) =>
        SFin i l
        -> Instruction (I32 ': inputStack) inputStack locals wasmModule inputLabels inputLabels

    -- "naive" way
    Call  :: FuncName -> FuncTypeAnn inputStack outputStack -> Instruction inputStack outputStack locals wasmModule inputLabels outputLabels 

    -- here we need to po
    -- Call  :: FuncName f -> Instruction (GetParamsOf (GetTypeOfFunc f wasmModule)) (GetResultsOf (GetTypeOfFunc f wasmModule)) locals wasmModule inputLabels outputLabels 

    Leave :: Instruction inputStack inputStack locals wasmModule (topLabel ': outputLabels) outputLabels

    -- TODO: missing WASM instructions

{-
=============================================================================
INSTRUCTION SEQUENCES
=============================================================================
-}

-- | A sequence of WebAssembly instructions.
-- This represents a linear sequence of instructions where the output stack
-- of one instruction becomes the input stack of the next.
infixr 5 :|  -- Right-associative, like list construction
data InstructionSequence (inputStack :: ValStackShape) (outputStack :: ValStackShape) (locals :: LocalsShape) (wasmModule :: WasmModule shape) (inputLabels :: LabelStackShape) (outputLabels :: LabelStackShape) where
    End  :: InstructionSequence inputStack inputStack locals wasmModule inputLabels inputLabels   -- Base case: empty sequence (identity)
    (:|) :: Instruction initialStack intermediateStack locals wasmModule inputLabels intermediateLabels               -- Inductive case: first instruction
         -> InstructionSequence intermediateStack finalStack locals wasmModule intermediateLabels outputLabels                          -- rest of sequence
         -> InstructionSequence initialStack finalStack locals wasmModule inputLabels outputLabels                              -- combined sequence

{-
=============================================================================
FUNCTIONS
=============================================================================
-}

-- | A complete WebAssembly function.
-- Functions start with an empty stack and produce the specified final stack shape.
-- The locals context represents the function's parameters and local variables.
data Function (inputStack :: ValStackShape) (resultStack :: ValStackShape) (locals :: LocalsShape) (outputLabels :: LabelStackShape) (wasmModule :: WasmModule shape) where
    Function :: FuncTypeAnn inputStack resultStack -> InstructionSequence inputStack resultStack locals wasmModule outputLabels outputLabels -> Function inputStack resultStack locals outputLabels wasmModule
    -- add a new type that captures the function type annotation, i.e.
    -- FuncTypeAnn inputStack resultStack ->



