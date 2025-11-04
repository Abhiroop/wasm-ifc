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
import Types (WasmType(I64, I32), RuntimeTypeOf, WasmType, StackShape(..), type (+>+), StackIndex (..), GetLabelType, LabelStack(..), RemoveLabels, CheckTopEqual, BlockType (..), SStackShape(..), FuncName, FuncTypeAnn (..), GetNthLabelType, StackLength, ReduceStackToLength, stackShapeLen, Take, Drop, Len, GetLabelCreationStackLength, CheckEqualStacks, FuncTypeAnn (..))
import Utils
import WasmModule (WasmModule(..), GetGlobals, GlobalTypeToWasmType, MemArg(SMemArg), GlobalsShape, WasmModuleShape, GlobalType (GlobalTypeMW), KnownMutability(SVar, SConst))

{-
=============================================================================
LOCAL VARIABLE CONTEXT
=============================================================================
-}

-- | Reference to a local variable slot (0-indexed).
type SlotIndex = Nat

type LocalsShape n = Vec n WasmType

{- TODO: Better error messages
   Improve type error messages for common mistakes like:
   - Stack underflow
   - Type mismatches
   - Invalid local access
-}

{-
=============================================================================
CONTROL FLOW LABELS
=============================================================================
-}

-- | Labels for control flow (blocks, loops, branches).
-- TODO: This should be made type-safe to prevent referencing invalid labels
-- Currently just an Int, but should track label scopes and validity.
type LabelIndex = Int

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
data Instruction (inputStack :: StackShape) (outputStack :: StackShape) (locals :: LocalsShape m) (wasmModule::WasmModule shape) (inputLabels:: LabelStack k) (outputLabels :: LabelStack l) where -- 

    -- Constants: push a literal value onto the stack
    I32Const :: Int32 -> Instruction inputStack (I32 :> inputStack) locals wasmModule inputLabels inputLabels

    -- i32 arithmetic operators (all pop two values, push one result)
    I32Add :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels
    I32Sub :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels
    I32Mul :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels
    I32Div :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels
    -- TODO: Handle division by zero at type level if WASM spec allows,
    --       otherwise document that this fails at runtime
    --       In spec it is defined as: if i2 is 0, then the result is undefined.
    --       Also I think division exists for signed and unsigned ints
    I32RemU :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels  --remainder operation (unsigned)
    --      if i2 is zero then the output is undefined
    I32RemS :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels  -- remainder operation (signed)
    --      if i2 is zero then the output is undefined -> the result has the sign of the first operator

    -- i32 comparison operators (pop two values, push i32 boolean result)
    I32EqZ :: Instruction (I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels            -- test if zero
    I32Eq  :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels    -- equal
    I32Neq :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels    -- inequality
    I32LtS :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels    -- less than (signed)
    I32LtU :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels    -- less than (unsigned)
    I32LeS :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels    -- less or equal (signed)
    I32LeU :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels    -- less or equal (unsigned)
    I32GtS :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels    -- greater than (signed)
    I32GtU :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels    -- greater than (unsigned)
    I32GeS :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels    -- greater or equal (signed)
    I32GeU :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals wasmModule inputLabels inputLabels    -- greater or equal (unsigned)

    -- more operators (e.g. bitwise negation, bitwise conjunction, ..., min, max)

    -- i64 arithmetic operators
    I64Add :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels
    I64Sub :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels
    I64Mul :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels
    I64Div :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels
    -- differentiation signed vs unsigned?
    I64RemU :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels --remainder operation (unsigned)
    --      if i2 is zero then the output is undefined
    I64RemS :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels -- remaidner operaton (signed)
    --      if i2 is zero then the output is undefined -> the result has the sign of the first operator

    -- I64 comparison operators
    I64EqZ :: Instruction (I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels   -- test if equal to zero
    I64Eq  :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels   -- equal
    I64Neq :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels   -- inequality
    I64LeS :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels   -- less or equal (signed)
    I64LeU :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels   -- less or equal (unsigned)
    I64LtS :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels   -- less than (signed)
    I64LtU :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels   -- less than (unsigned)
    I64GtS :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels   -- greater than (signed)
    I64GtU :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels   -- greater than (unsigned)
    I64GeS :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels   -- greater or equal (signed)
    I64GeU :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals wasmModule inputLabels inputLabels   -- greater or equal (unsigned)



    -- Stack manipulation
    Drop :: Instruction (dropped :> inputStack) inputStack locals wasmModule inputLabels inputLabels   -- remove top value from stack

    -- Local variable operations
    -- LocalGet: push the value of a local variable onto the stack
    LocalGet :: SFin i n
             -> Instruction inputStack ((Index i locals) :> inputStack) locals wasmModule inputLabels inputLabels

    -- LocalSet: pop a value from stack and store it in a local variable
    LocalSet :: SFin i n
             -> Instruction (Index i locals :> inputStack) inputStack locals wasmModule inputLabels inputLabels

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
             -> Instruction (Index i locals :> inputStack) (Index i locals :> inputStack) locals wasmModule inputLabels inputLabels
    -- TODO: Handle uninitialized local variables according to WASM spec

    -- GlobalGet: push the value of a global variable onto the stack
    GlobalGet :: forall (i :: Nat) (n :: Nat) (m :: Nat) (l :: Nat) (j :: Nat) (shape :: WasmModuleShape) (inputStack :: StackShape) (wasmModule :: WasmModule shape) (locals :: LocalsShape m) (inputLabels :: LabelStack l).
        SFin i n
        -> Instruction inputStack (GlobalTypeToWasmType (Index i (GetGlobals wasmModule)) :> inputStack) locals wasmModule inputLabels inputLabels

    -- GlobalSet: pop a value from stack and store it in a global variable => global type must be mutable where do we check this
    GlobalSet :: SFin i n
              -> Instruction (GlobalTypeToWasmType (Index i (GetGlobals wasmModule)) :> inputStack) inputStack locals wasmModule inputLabels inputLabels


    -- MEMORY INSTRUCTIONS
    -- need to make this an annotated Function such that we can know whether we load an I32, I64, F32, F64
    -- do we even have to access the memory like this: (Index offset (GetMems wasmModule))
        -- this simply returns a memory type which includes the limits of the memory
    -- We need the forall in order to use MemoryLoad @I32
    -- type equality ~ or :~:
    MemoryLoad :: forall (wasmtype::WasmType) (m :: Nat) (k :: Nat) (l :: Nat) (i :: Nat) (shape :: WasmModuleShape) (align :: Word32) (offset :: Word64) (inputStack :: StackShape) (wasmModule :: WasmModule shape) (locals :: LocalsShape m) (inputLabels :: LabelStack k) (outputLabels :: LabelStack l).
            MemArg align offset  -- ignore alignment for now, also not 100% sure why i32 has to be on top of stack
             -> Instruction (I32 :> inputStack) (wasmtype :> inputStack) locals wasmModule inputLabels outputLabels
    -- MemoryStore: pop address and value from stack, store value at address in memory
        -- should we also make this annoted with the wasmtype?
    -- MemoryStore :: MemArg offset alignment -- add  constraint on limit of memory
    --          -> Instruction (I32 :> wasmtype :> inputStack) inputStack locals wasmModule

    -- MemoryStore with annotation to specify the type that is stored
    MemoryStore :: forall (wasmtype :: WasmType) align offset inputStack wasmModule locals inputLabels outputLabels.
        MemArg align offset
        -> Instruction (I32 :> wasmtype :> inputStack) inputStack locals wasmModule inputLabels outputLabels


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
    Block :: forall (m :: Nat) (l :: Nat) (p :: Nat) (r :: Nat) (i :: Nat) (o :: Nat) (shape :: WasmModuleShape) (paramsStack :: StackShape) (resStack :: StackShape) (inputStack :: StackShape)(outputStack :: StackShape) (locals :: LocalsShape m) (wasmModule :: WasmModule shape) (inputLabels :: LabelStack l).
            (CheckTopEqual paramsStack inputStack ~ 'True,
                CheckTopEqual resStack outputStack ~ 'True)  -- ensure that the parameters of the block are on top of the input stack
          => BlockType paramsStack resStack -- represents the optional valtype however what about the typeidx? can't know the function type
          -> InstructionSequence inputStack outputStack locals wasmModule ('(resStack, StackLength inputStack) :>: inputLabels) ('(resStack, StackLength inputStack) :>: inputLabels)
          -> Instruction inputStack outputStack locals wasmModule inputLabels inputLabels

    -- Loop: a sequence of instructions that can be restarted with 'br'
    Loop  :: forall (m :: Nat) (l :: Nat) (p :: Nat) (r :: Nat) (i :: Nat) (o :: Nat) (shape :: WasmModuleShape) (paramsStack :: StackShape) (resStack :: StackShape) (inputStack :: StackShape) (outputStack :: StackShape) (locals :: LocalsShape m) (wasmModule :: WasmModule shape) (inputLabels :: LabelStack l).
            (CheckTopEqual paramsStack inputStack ~ 'True,
                CheckTopEqual resStack outputStack ~ 'True)  -- ensure that the parameters of the block are on top of the input stack
          => BlockType paramsStack resStack
          -> InstructionSequence inputStack outputStack locals wasmModule ('(paramsStack, StackLength inputStack) :>: inputLabels) ('(paramsStack, StackLength inputStack) :>: inputLabels)
          -> Instruction inputStack outputStack locals wasmModule inputLabels inputLabels

    -- If: conditional execution (pops i32 condition, executes one of two branches)
    If    :: (CheckTopEqual paramsStack inputStack ~ 'True,
                CheckTopEqual resStack outputStack ~ 'True)  -- ensure that the parameters of the block are on top of the input stack
          => BlockType paramsStack resStack
          -> InstructionSequence inputStack outputStack locals wasmModule ('(resStack, StackLength inputStack) :>: inputLabels) ('(resStack, StackLength inputStack) :>: inputLabels)     -- then branch
          -> InstructionSequence inputStack outputStack locals wasmModule ('(resStack, StackLength inputStack) :>: inputLabels) ('(resStack, StackLength inputStack) :>: inputLabels)     -- else branch
          -> Instruction (I32 :> inputStack) outputStack locals wasmModule inputLabels inputLabels

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
    Br    :: forall (i :: Nat) (l :: Nat) (n :: Nat) (shape :: WasmModuleShape) (inputLabels :: LabelStack l) (inputStack :: StackShape) (outputStack :: StackShape) (locals :: LocalsShape n) (wasmModule :: WasmModule shape) (baseStack :: StackShape).
        (CheckTopEqual (GetLabelType i inputLabels) inputStack ~ 'True,
                  (Take (Len (GetLabelType i inputLabels)) inputStack +>+ baseStack) ~ outputStack
        ) =>
            StackIndex i l
            -> Instruction inputStack
                           outputStack
                           locals
                           wasmModule
                           inputLabels
                           (RemoveLabels i inputLabels) --XXX: Potential error

    -- BrIf: conditional branch (pops i32 condition)
    -- TODO: Maybe use SFin as well
    BrIf  :: StackIndex i l -> Instruction (I32 :> inputStack) inputStack locals wasmModule inputLabels outputLabels

    -- "naive" way
    Call  :: FuncName -> FuncTypeAnn inputStack outputStack -> Instruction inputStack outputStack locals wasmModule inputLabels outputLabels 

    -- here we need to po
    -- Call  :: FuncName f -> Instruction (GetParamsOf (GetTypeOfFunc f wasmModule)) (GetResultsOf (GetTypeOfFunc f wasmModule)) locals wasmModule inputLabels outputLabels 

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
data InstructionSequence (inputStack :: StackShape) (outputStack :: StackShape) (locals :: LocalsShape n) (wasmModule :: WasmModule shape) (inputLabels :: LabelStack k) (outputLabels :: LabelStack l) where
    End  :: InstructionSequence inputStack inputStack locals wasmModule inputLabels outputLabels   -- Base case: empty sequence (identity)
    (:|) :: Instruction initialStack intermediateStack locals wasmModule inputLabels outputLabels               -- Inductive case: first instruction
         -> InstructionSequence intermediateStack finalStack locals wasmModule inputLabels outputLabels                          -- rest of sequence
         -> InstructionSequence initialStack finalStack locals wasmModule inputLabels outputLabels                              -- combined sequence

{-
=============================================================================
FUNCTIONS
=============================================================================
-}

-- | A complete WebAssembly function.
-- Functions start with an empty stack and produce the specified final stack shape.
-- The locals context represents the function's parameters and local variables.
data Function (inputStack :: StackShape) (resultStack :: StackShape) (locals :: LocalsShape n) (outputLabels :: LabelStack l) where
    Function :: FuncTypeAnn inputStack resultStack -> InstructionSequence inputStack resultStack locals wasmModule outputLabels outputLabels -> Function inputStack resultStack locals outputLabels
    -- add a new type that captures the function type annotation, i.e.
    -- FuncTypeAnn inputStack resultStack ->

{-
=============================================================================
EXAMPLE FUNCTIONS
=============================================================================
-}

-- Example Call in Function
callExample :: Function Empty (I32 :> Empty) (I32 :<| I32 :<| VNil) Types.EmptyLabels
callExample = Function (FFuncTypeAnn Empty (I32 :> Empty)) $
       LocalGet SFZ    -- get first parameter
    :| LocalGet (SFS SFZ)  -- get second parameter
    :| Call "add2" (FFuncTypeAnn (I32 :> (I32 :> Empty)) (I32 :> Empty)) -- call add2 function
    :| End

-- Example MemoryLoad
-- the locals are the two I32 integers that are used to compute the address of the memory load
memLoadSequence :: Function Empty (I64 :> Empty) (I32 :<| I32 :<| VNil) Types.EmptyLabels
memLoadSequence = Function (FFuncTypeAnn Empty (I64 :> Empty)) $
       LocalGet SFZ
    :| MemoryLoad @I64 SMemArg 
    :| LocalGet (SFS SFZ)
    :| MemoryLoad @I64 SMemArg 
    :| I64Add 
    :| End

-- Example MemoryStore
memstoresequence :: Function Empty Empty (I32 :<| I64 :<| VNil) Types.EmptyLabels
memstoresequence = Function (FFuncTypeAnn Empty Empty) $
       LocalGet (SFS SFZ)  -- get the address
    :| LocalGet SFZ      -- get the value to store
    :| MemoryStore @I64 SMemArg 
    :| End

-- add1Sequence :: InstructionSequence (I32 :> I32 :> Empty) (I32 :> Empty) 'VNil ('WasmModule '[]) ('WasmModule '[])
add1Sequence :: forall {n :: Nat} {k :: Nat} {shape :: WasmModuleShape} {inputStack :: StackShape} {locals :: LocalsShape n} {wasmModule :: WasmModule shape} {inputLabels :: LabelStack k}. InstructionSequence (I32 :> (I32 :> inputStack)) (I32 :> inputStack) locals wasmModule inputLabels inputLabels
add1Sequence = I32Add :| End

-- addSubSequence :: InstructionSequence (I32 :> (I32 :> (I32 :> Empty))) (I32 :> Empty) 'VNil (WasmModule Z) ('WasmModule '[]) -- only 3 I32 because the result of the add is the first argument of the subtract
addSubSequence :: forall {n :: Nat} {k :: Nat} {shape :: WasmModuleShape} {inputStack :: StackShape} {locals :: LocalsShape n} {wasmModule :: WasmModule shape} {inputLabels :: LabelStack k}. InstructionSequence (I32 :> (I32 :> (I32 :> inputStack))) (I32 :> inputStack) locals wasmModule inputLabels inputLabels
addSubSequence = I32Add :| (I32Sub :| End)

-- | Example 1: Add two integers
-- Takes two i32 parameters (slots 0 and 1), returns their sum
add2 :: Function Empty (I32 :> Empty) (I32 :<| I32 :<| VNil) Types.EmptyLabels -- Function resultStack locals (repr the function parameters)
add2 = Function (FFuncTypeAnn Empty (I32 :> Empty)) $
    -- Local slots: (0) first parameter, (1) second parameter
       LocalGet SFZ    -- Push first parameter
    :| LocalGet (SFS SFZ)     -- Push second parameter
    :| I32Add               -- Add them (pops 2, pushes 1 result)
    :| End

-- | Example 2: Factorial function using iteration
-- Takes one i32 parameter, returns its factorial
factorial :: Function Empty (I32 :> Empty) (I32 :<| I32 :<| VNil) Types.EmptyLabels
factorial = Function (FFuncTypeAnn Empty (I32 :> Empty)) $
    -- Local slots: (0) input parameter (also used as counter), (1) accumulator
    -- Initialize accumulator to 1
       I32Const 1
    :| LocalSet (SFS SFZ)
    -- :| I32Const 0
    -- Main computation block
    :| Block (BTParamsResults SEmpty SEmpty) (
        -- Check if n <= 1 (base case)
           LocalGet SFZ
        :| I32Const 1
        :| I32LeS
        :| BrIf StackIndexZ             -- Exit block if n <= 1
        -- Iterative loop for factorial computation
        :| Loop (BTParamsResults SEmpty SEmpty) (
            -- accumulator *= n
               LocalGet (SFS SFZ)
            :| LocalGet SFZ
            :| I32Mul
            :| LocalSet (SFS SFZ)
            -- n -= 1
            :| LocalGet SFZ
            :| I32Const 1
            :| I32Sub
            :| LocalSet SFZ
            -- Continue if n > 1
            :| LocalGet SFZ
            :| I32Const 1
            :| I32GtS
            :| BrIf (StackIndexS StackIndexZ)             -- Branch back to loop start
            :| End)
        :| End)
    -- Return the accumulated result
    :| LocalGet (SFS SFZ)
    :| End

-- | Example 3: Function that returns nothing (void function).
-- Demonstrates different return types - this one returns Empty stack.
printNumber :: Function Empty Empty (I32 :<| VNil) Types.EmptyLabels
printNumber = Function (FFuncTypeAnn Empty Empty) $
    -- Just consume the parameter without returning anything
       LocalGet slotZero
    :| Drop
    :| End
    where
      -- example: here we are saying that
      -- extract the zeroth index from
      -- a vector of size 2
      slotZero :: SFin 'Z ('S ('S 'Z))
      slotZero = SFZ

-- | Example 4: Function with more complex local variable patterns.
-- Takes one parameter, uses three local variables for intermediate calculations.
complexCalculation :: Function Empty (I32 :> Empty) (I32 :<| I32 :<| I32 :<| I32 :<| VNil) Types.EmptyLabels
complexCalculation = Function (FFuncTypeAnn Empty (I32 :> Empty)) $
    -- Local slots: (0) input, (1) temp1, (2) temp2, (3) result
    -- temp1 = input * 2
       LocalGet SFZ
    :| I32Const 2
    :| I32Mul
    :| LocalSet (SFS SFZ)
    -- temp2 = input + 10
    :| LocalGet SFZ
    :| I32Const 10
    :| I32Add
    -- TODO: Need more slot witnesses for slots 2 and 3
    -- This is incomplete but shows the pattern
    :| End

-- | Example 5: Conditional logic with If instruction.
-- Returns the absolute value of the input.
absoluteValue :: Function Empty (I32 :> Empty) (I32 :<| VNil) Types.EmptyLabels
absoluteValue = Function (FFuncTypeAnn Empty (I32 :> Empty)) $
    -- Check if input is negative
       LocalGet SFZ
    :| I32Const 0
    :| I32LtS              -- Is input < 0?
    :| If (BTParamsResults SEmpty SEmpty)
        -- Then branch: negate the number (0 - input)
        (  I32Const 0
        :| LocalGet SFZ
        :| I32Sub
        :| End)
        -- Else branch: return input as-is
        (  LocalGet SFZ
        :| End)
    :| End

-- Bad example (fails at compile time)
--nestedControlFlow :: Function (I32 :> Empty) (I32 ': I32 ': '[])
--nestedControlFlow = Function $
--    -- Outer block
--       Block 0 (ReturnsOne ForI32) (
--           LocalGet SFZ
--        :| I32Const 10
--        :| I32GtS
--        :| BrIf 0  -- Exit outer block if input > 10
--        -- Inner block
--        :| Block 1 NoReturn (
--               LocalGet SFZ
--            :| I32Const 5
--            :| I32LtS
--            :| BrIf 1  -- Exit inner block if input < 5
--            -- If we're here, 5 <= input <= 10
--            :| LocalGet SFZ
--            :| I32Const 2
--            :| I32Mul
--            :| LocalSet (SFS SFZ)
--            :| End)
--        -- Default case: return input unchanged
--        :| LocalGet SFZ
--        :| End)
--    :| LocalGet (SFS SFZ)  -- Return the result
--    :| End

{-
=============================================================================
INTERPRETER
=============================================================================
-}

-- | Runtime representation of the WebAssembly stack.
-- This is the actual data structure that holds stack values during execution.
data Stack (stackShape :: StackShape) where
    EmptyStack :: Stack Empty
    Push       :: RuntimeTypeOf wasmType -> Stack stackShape -> Stack (wasmType :> stackShape)



stackLength :: Stack stackShape -> SNat (StackLength stackShape)
stackLength EmptyStack       = SZ
stackLength (Push _ rest) = SS (stackLength rest)


-- -- Hello existential type!
-- data SomeStack = forall s. SomeStack (Stack s)


-- XXX: TODO: the type should specify that you are not taking more than
-- what the stack has
-- takeStack :: Int -> Stack stackShape -> Stack stackShape'
-- takeStack = undefined
-- takeStack 0 _ = EmptyStack
-- takeStack n (Push x xs) = Push x (takeStack (n - 1) xs)


takeStack :: SNat n -> Stack s -> (Stack (Take n s), Stack (Drop n s))
takeStack SZ stk = (EmptyStack, stk)
takeStack (SS n) (Push x xs) =
  let (taken, rest) = takeStack n xs
  in (Push x taken, rest)


-- stackLength :: Stack stackShape -> Nat
-- stackLength EmptyStack       = Z
-- stackLength (Push _ rest) = S (stackLength rest)


concatStacks :: Stack s1 -> Stack s2 -> Stack (s1 +>+ s2)
concatStacks EmptyStack s2       = s2
concatStacks (Push val rest) s2 = Push val (concatStacks rest s2)


popNthLabel :: ( GetLabelCreationStackLength n restLabelsShape ~ stackLen
               , GetLabelType n restLabelsShape ~ rightLabelStack) =>
               StackIndex n l
            -> Labels restLabelsShape
            -> (SStackShape rightLabelStack, SNat stackLen)
popNthLabel StackIndexZ (ConsLabels sstackShape lenInputStack _) = (sstackShape, lenInputStack)
popNthLabel (StackIndexS idx) (ConsLabels _ _ rest) = popNthLabel idx rest
popNthLabel _ NoLabels = error "Index out of bounds in popNthLabel"

reduceStackToLength :: forall n stackShape. SNat n -> Stack stackShape -> Stack (ReduceStackToLength n stackShape)
reduceStackToLength SZ _ = EmptyStack
reduceStackToLength (SS n) (Push val rest) = Push val (reduceStackToLength n rest)
reduceStackToLength _ EmptyStack = error "Cannot reduce stack to length greater than its current length"

-- reduceStackToLength :: Nat -> Stack stackShape -> Stack stackshape'
-- reduceStackToLength = undefined
-- reduceStackToLength SZ _ = EmptyStack
-- reduceStackToLength (SS n) (Push val rest) = Push val (reduceStackToLength n rest)
-- reduceStackToLength _ EmptyStack = error "Cannot reduce stack to length greater than its current length"


-- reduceStackToSome :: Nat -> Stack s -> SomeStack
-- reduceStackToSome n stk = go n stk
--   where
--     go :: Nat -> Stack x -> SomeStack
--     go Z     xs         = SomeStack xs
--     go (S k) (Push _ t) = go k t
--     go (S _) EmptyStack = SomeStack EmptyStack


removeLabelsUntilStackIdx :: forall n l (inputLabelStack :: LabelStack l). StackIndex n l -> Labels inputLabelStack -> Labels (RemoveLabels n inputLabelStack)
removeLabelsUntilStackIdx StackIndexZ (ConsLabels _ _ rest) = rest
removeLabelsUntilStackIdx (StackIndexS idx) (ConsLabels _ _ rest) = removeLabelsUntilStackIdx idx rest


firstTuple :: (a, b) -> a
firstTuple (a,b) = a

sndTuple :: (a,b) -> b
sndTuple (a,b) = b

-- popOne :: Stack stackShape -> RuntimeTypeOf wasmType
popOne :: Stack (wasmType :> stackShape) -> RuntimeTypeOf wasmType
popOne (Push val _) = val

popZero :: Stack stackShape -> (Stack 'Empty, Stack stackShape)
popZero rest = (EmptyStack, rest)


-- popN :: (GreaterZero t1 ~ 'True) => Proxy t1 -> Stack (popShape +>+ stackShape) -> (Stack popShape, Stack stackShape)
-- popN n (Push val rest) = (Push val (firstTuple (popN (n-1) rest)), sndTuple (popN (n-1) rest))
-- (Num n, stackLength popShape ~ n) =>
-- popNFromStack :: (IfIntZero n (popShape ~ Empty)) => Proxy n -> Stack (popShape +>+ stackShape) -> (Stack popShape, Stack stackShape)
-- popNFromStack 0 stackShape = (EmptyStack, stackShape)
-- popNFromStack n (Push val rest) =
--     let (popShape, remaining) = popNFromStack (n - 1) rest
--     in (Push val popShape, remaining)

-- | Runtime representation of the WebAssembly locals.
-- This is the actual data structure that holds local values during execution.
data Locals (localsShape :: LocalsShape n) where
    NoLocals   :: Locals 'VNil
    ConsLocals :: RuntimeTypeOf wasmType -> Locals localsShape -> Locals (wasmType :<| localsShape)

data Globals (globalsShape :: GlobalsShape n) where
    NoGlobals   :: Globals 'VNil
    ConsGlobals :: RuntimeTypeOf wasmType -> KnownMutability m -> Globals globalsShape -> Globals (GlobalTypeMW m wasmType :<| globalsShape)

data Labels (labelsShape :: LabelStack n) where
    NoLabels :: Labels 'Types.EmptyLabels
    ConsLabels  :: SStackShape labelStackShape -> SNat m -> Labels restLabelsShape -> Labels ('(labelStackShape, m) :>: restLabelsShape)
-- data Memory (memsShape :: MemoriesShape n) where
--     NoMems   :: Memory 'VNil
--     ConsMems :: MemoryType -> Memory memsShape -> Memory (MemoryType :<| memsShape)


data RuntimeContext (stackShape :: StackShape) (localsShape :: LocalsShape n) (wasmModule :: WasmModule shape) (labelsShape :: LabelStack m) = RuntimeContext
    { stack  :: Stack stackShape,
      locals :: Locals localsShape,
      globals :: Globals (GetGlobals wasmModule), -- :: GlobalsShape (GetGlobalsShape shape)),
      labels :: Labels labelsShape
      -- TODO: labels, tables, etc.
    }

-- function to get the value of a local variable at a given index
getLocalValue :: SFin i n -> Locals localsShape -> RuntimeTypeOf (Index i localsShape)
getLocalValue SFZ (ConsLocals val _) = val
getLocalValue (SFS idx) (ConsLocals _ rest) = getLocalValue idx rest
getLocalValue _ NoLocals = error "Index out of bounds in getLocalValue"

-- function to set the value of a local variable at a given index
setLocalValue :: SFin i n -> RuntimeTypeOf (Index i localsShape) -> Locals localsShape -> Locals localsShape
setLocalValue SFZ newVal (ConsLocals _ rest) = ConsLocals newVal rest
setLocalValue (SFS idx) newVal (ConsLocals val rest) = ConsLocals val (setLocalValue idx newVal rest)
setLocalValue _ _ NoLocals = error "Index out of bounds in setLocalValue"

-- function to get the value of a global variable at a given index
getGlobalValue :: SFin i n -> Globals globalsShape -> RuntimeTypeOf (GlobalTypeToWasmType (Index i globalsShape))
getGlobalValue SFZ (ConsGlobals val _ _) = val
getGlobalValue (SFS idx) (ConsGlobals _ _ rest) = getGlobalValue idx rest
getGlobalValue _ NoGlobals = error "Index out of bounds in getGlobalValue"

--function to set the value of a global variable at a given index, mutability has to be var
setGlobalValue :: SFin i n -> RuntimeTypeOf (GlobalTypeToWasmType (Index i globalsShape)) -> Globals globalsShape -> Globals globalsShape
setGlobalValue SFZ newVal (ConsGlobals _ SVar rest) = ConsGlobals newVal SVar rest
setGlobalValue (SFS idx) newVal (ConsGlobals oldVal SVar rest) = ConsGlobals oldVal SVar (setGlobalValue idx newVal rest)
setGlobalValue _ _ (ConsGlobals _ SConst _) = error "Cannot set value of a constant global variable" -- TODO: double check this
setGlobalValue _ _ NoGlobals = error "Index out of bounds in setGlobalValue"

-- TODO
executeInstruction :: forall inputStack outputStack locals wasmModule inputLabels outputLabels .
                      Instruction inputStack outputStack locals wasmModule inputLabels outputLabels
                   -> RuntimeContext inputStack locals wasmModule inputLabels
                   -> RuntimeContext outputStack locals wasmModule outputLabels
executeInstruction instr prevCtxt@(RuntimeContext prevStack prevLocals prevGlobal prevLabels) = case instr of
    I32Const val -> RuntimeContext (Push val prevStack) prevLocals prevGlobal prevLabels
    I32Add       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 + val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
    I32Sub       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val1 - val2 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels 
    I32Mul       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 * val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
    I32Div       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `div` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
    I32RemU      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `mod` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
    I32RemS      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `mod` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
    I32EqZ       -> case prevStack of
                      Push val rest ->
                          let result = if val == 0 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
    I32Eq        -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 == val2 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels

    I32Neq       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 /= val2 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels

    I32LtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 < val1 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels

    I32LtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if (fromIntegral val2 :: Word32) < (fromIntegral val1 :: Word32) then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels

    I32LeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 <= val1 then (1 :: Int32) else (0 :: Int32)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels

    I32LeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 <= val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels

    I32GtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 > val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I32GtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 > val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I32GeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 >= val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I32GeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 >= val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64Add       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 + val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64Sub       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 - val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64Mul       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 * val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64Div       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `div` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64RemU      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `mod` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64RemS      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `mod` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64EqZ       -> case prevStack of
                      Push val rest ->
                          let result = if val == 0 then (1 :: Int64) else (0 :: Int64)
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64Eq        -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 == val2 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64Neq       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 /= val2 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64LtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 < val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64LtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 < val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64LeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 <= val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64LeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 <= val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64GtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 > val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64GtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 > val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64GeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 >= val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    I64GeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 >= val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobal prevLabels
 
    Drop         -> case prevStack of
                      Push _ rest -> RuntimeContext rest prevLocals prevGlobal prevLabels

    LocalGet idx -> case getLocalValue idx prevLocals of
                      val -> RuntimeContext (Push val prevStack) prevLocals prevGlobal prevLabels

    LocalSet idx -> case prevStack of
                      Push val rest ->
                          let newLocals = setLocalValue idx val prevLocals
                          in RuntimeContext rest newLocals prevGlobal prevLabels

    LocalTee idx -> case prevStack of
                      Push val rest ->
                          let newLocals = setLocalValue idx val prevLocals
                          in RuntimeContext (Push val rest) newLocals prevGlobal prevLabels

    GlobalGet idx -> case getGlobalValue idx prevGlobal of
                      val -> RuntimeContext (Push val prevStack) prevLocals prevGlobal prevLabels
    GlobalSet idx -> case prevStack of
                      Push val rest -> RuntimeContext rest prevLocals (setGlobalValue idx val prevGlobal) prevLabels
    MemoryLoad arg -> undefined
    MemoryStore arg -> undefined
    Block (BTParamsResults _ (res :: SStackShape resStack)) instrSeq ->
      let newLabels = ConsLabels res (stackLength prevStack) (labels prevCtxt)
          newContext =
            executeInstructionSequence instrSeq (prevCtxt { labels = newLabels } :: RuntimeContext inputStack locals wasmModule ('(resStack, StackLength inputStack) :>: inputLabels))
      in newContext { labels = prevLabels }
    Loop (BTParamsResults (params :: SStackShape paramsStack) _) instrSeq -> 
                let newLabels = ConsLabels params (stackLength prevStack) (labels prevCtxt)
                    newContext = executeInstructionSequence instrSeq (prevCtxt { labels = newLabels } :: RuntimeContext inputStack locals wasmModule ('(paramsStack, StackLength inputStack) :>: inputLabels))
                in newContext { labels = prevLabels }
    If (BTParamsResults _ (res :: SStackShape resStack)) thenSeq elseSeq -> case prevStack of
        Push cond (rest :: Stack inputStackWOCond) ->
            if cond /= 0
            then 
                let newLabels = ConsLabels res (stackLength rest) (labels prevCtxt)
                    newCtxt = executeInstructionSequence thenSeq (prevCtxt { labels = newLabels, stack = rest } :: RuntimeContext inputStackWOCond locals wasmModule ('(resStack, StackLength inputStackWOCond) :>: inputLabels))
                in newCtxt { labels = prevLabels }

            else 
                let newLabels = ConsLabels res (stackLength rest) (labels prevCtxt)
                    newCtxt = executeInstructionSequence elseSeq (prevCtxt { labels = newLabels, stack = rest } :: RuntimeContext inputStackWOCond locals wasmModule ('(resStack, StackLength inputStackWOCond) :>: inputLabels))
                in newCtxt { labels = prevLabels }
    Br (labelIdx :: StackIndex i n) -> undefined

            -- DINA: not solved recursively like in specs but rather
            -- 1. remove all labels above the target label and get the length of the stack at creation of label (line 803)
              -- a) for this we now also save the length of the stack on the labelstack on creation (see block instr e.g.)
            -- 2. remove everything from the stack that was added after the creation of the label
              -- a) this we do with the reduceStackToLength function
            -- 3. push the label type onto the stack since this is the expected stack after branching
              -- a) IGNORE FOR NOW: However, here I am also not sure whether technically we should push back
              --    the top n elements from the input stack in order for it to really be correct?
            -- CURRENT PROBLEM: Cannot deduce the concatination of the input stack and the label type to outputStack  
        -- let (labelType, lenStackBeforeLabelCreation) = popNthLabel labelIdx prevLabels

        --     -- prevStack :: Stack inputStack
        --     -- stackToKeep :: Stack s where s is prefix of inputStack of length (stackShapeLen labelType)
        --     -- baseStack   :: Stack s2 where s2 is a suffix of inputStack of length lenStackBeforeLabelCreation
        --     -- finalStack  :: Stack (s +>+ s2) where (s +>+ s2) ~ outputStack


        --     (stackToKeep, _) = takeStack (stackShapeLen labelType) prevStack
        --     -- stackToKeep :: Stack (Take (Len (GetLabelType i inputLabels)) inputStack)
        --     --                             Len (s :: StackShape) :: Nat
        --     baseStack  = reduceStackToLength lenStackBeforeLabelCreation prevStack
        --     -- Stack (ReduceStackToLength stackLen inputStack) -- where stackLen comes from popNthLabel
        --     finalStack = concatStacks stackToKeep baseStack --  :: Stack ((Take ......) +>+ s2) 
        --  in prevCtxt {
        --       stack = finalStack,
        --       labels = removeLabelsUntilStackIdx labelIdx prevLabels :: Labels (RemoveLabels i inputLabels)
        --      }  :: RuntimeContext outputStack locals wasmModule (RemoveLabels i inputLabels)

    BrIf labelIdx-> undefined
    Call funcName (FFuncTypeAnn params res) -> undefined -- executeFunction (Function Empty outputStack params (ConsLabels res prevLabels)) (RuntimeContext prevStack prevLocals prevGlobal prevLabels)

executeInstructionSequence :: InstructionSequence inputStack outputStack locals wasmModule inputLabels inputLabels
                           -> RuntimeContext inputStack locals wasmModule inputLabels
                           -> RuntimeContext outputStack locals wasmModule inputLabels
executeInstructionSequence instrSeq prevCtxt@(RuntimeContext inputStack prevLocals prevWasmModule prevLabels) = case instrSeq of
    End -> RuntimeContext inputStack prevLocals prevWasmModule prevLabels
    (instr :| rest) ->
        let intermediateContext = executeInstruction instr prevCtxt
        in executeInstructionSequence rest intermediateContext

executeFunction :: Function inputStack outputStack locals labels
                   -> RuntimeContext inputStack locals globals labels
                   -> RuntimeContext outputStack locals globals labels
executeFunction func@(Function (FFuncTypeAnn params res) instrSeq) prevCtxt = undefined
    -- let newCtxt = executeInstructionSequence instrSeq (prevCtxt { stack = EmptyStack, locals = params }) :: RuntimeContext Empty locals globals labels
    -- in newCtxt { stack = concatStacks res (stack prevCtxt) }
