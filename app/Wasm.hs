{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeApplications #-}


-- | A type-safe embedded domain-specific language (DSL) for WebAssembly.
-- This module uses advanced Haskell type system features to ensure that
-- WebAssembly programs are stack-safe and type-correct at compile time.
module Wasm where

import Data.Int (Int32)
import Data.Word (Word32, Word64)
import Data.Type.Equality (type (:~:))
import GHC.TypeLits (Nat) -- , type (-))
-- import GHC.TypeError (TypeError, ErrorMessage(..))
import Types (WasmType(I64, I32), KnownWasmType (..), RuntimeTypeOf, WasmType, StackShape(..), type (+>+), StackLength, StackIndex (..), GetLabelType, LabelStack(..), RemoveLabels, KnownStackShape(..), CheckTopEqual, BlockType (..), SStackShape(..), FuncName, FuncTypeAnn (..))
import Utils
import WasmModule (WasmModule(..), GetGlobals, GlobalTypeToWasmType, MemArg(SMemArg), GetMems, Mutability, GlobalsShape)
import qualified Types as WasmOrLabelType
import Data.Kind (Type)

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
data Instruction (inputStack :: StackShape) (outputStack :: StackShape) (locals :: LocalsShape m) (wasmModule::WasmModule) (inputLabels:: LabelStack k) (outputLabels :: LabelStack l) where -- 

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
    GlobalGet :: forall (i :: SNat) (n :: SNat) (m :: SNat) (l :: SNat) (inputStack :: StackShape) (wasmModule :: (WasmModule {globals :: GlobalsShape k mems})) (locals :: LocalsShape m) (inputLabels :: LabelStack l).
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
    MemoryLoad :: forall (wasmtype::WasmType) (n :: SNat) (m :: SNat) (k :: SNat) (l :: SNat) (align :: Word32) (offset :: Word64) (inputStack :: StackShape) (wasmModule :: WasmModule) (locals :: LocalsShape m) (inputLabels :: LabelStack k) (outputLabels :: LabelStack l).
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
    Block :: forall (n :: SNat) (m :: SNat) (l :: SNat) (paramsStack :: StackShape) (resStack :: StackShape) (inputStack :: StackShape)(outputStack :: StackShape) (locals :: LocalsShape m) (wasmModule :: WasmModule) (inputLabels :: LabelStack l) (outputLabels :: LabelStack l).
            (CheckTopEqual paramsStack inputStack ~ 'True,
                CheckTopEqual resStack outputStack ~ 'True)  -- ensure that the parameters of the block are on top of the input stack
          => BlockType paramsStack resStack -- represents the optional valtype however what about the typeidx? can't know the function type
          -> InstructionSequence inputStack outputStack locals wasmModule (resStack :>: inputLabels) (resStack :>: outputLabels)
          -> Instruction inputStack outputStack locals wasmModule inputLabels outputLabels

    -- Loop: a sequence of instructions that can be restarted with 'br'
    Loop  :: forall (n :: SNat) (m :: SNat) (l :: SNat) (paramsStack :: StackShape) (resStack :: StackShape) (inputStack :: StackShape)(outputStack :: StackShape) (locals :: LocalsShape m) (wasmModule :: WasmModule) (inputLabels :: LabelStack l) (outputLabels :: LabelStack l).
            (CheckTopEqual paramsStack inputStack ~ 'True,
                CheckTopEqual resStack outputStack ~ 'True)  -- ensure that the parameters of the block are on top of the input stack
          => BlockType paramsStack resStack
          -> InstructionSequence inputStack outputStack locals wasmModule (paramsStack :>: inputLabels) (paramsStack :>: outputLabels)
          -> Instruction inputStack outputStack locals wasmModule inputLabels outputLabels

    -- If: conditional execution (pops i32 condition, executes one of two branches)
    If    :: InstructionSequence inputStack outputStack locals wasmModule inputLabels outputLabels     -- then branch
          -> InstructionSequence inputStack outputStack locals wasmModule inputLabels outputLabels     -- else branch
          -> Instruction (I32 :> inputStack) outputStack locals wasmModule inputLabels outputLabels

    -- Br: unconditional branch to a label
        -- SNat is the nesting depth of how many nested blocks/loops to break out of
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
    -- Br   :: forall (i::SNat) (l :: SNat) (n ::SNat) (m::SNat) (inputLabels :: LabelStack ('S l)) (inputStack :: StackShape) (outputStack :: StackShape) (locals :: LocalsShape n) (wasmModule :: WasmModule m).
    --         StackIndex i l
    --         -> Instruction (GetLabelType i inputLabels +>+ inputStack) outputStack locals wasmModule inputLabels (RemoveLabels i inputLabels) -- after branching, the labels above the target label are removed from the label stack?

    -- This version compiles
    -- Checks whether the top of the input stack is equal to the label type as a constraint
    Br    :: forall (i :: SNat) (l :: SNat) (n :: SNat) (m :: SNat) (inputLabels :: LabelStack (S l)) (inputStack :: StackShape) (outputStack :: StackShape) (locals :: LocalsShape n) (wasmModule :: WasmModule).
        CheckTopEqual (GetLabelType i inputLabels) inputStack ~ 'True =>
            StackIndex i (S l)
            -> Instruction inputStack outputStack locals wasmModule inputLabels (RemoveLabels i inputLabels)

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
data InstructionSequence (inputStack :: StackShape) (outputStack :: StackShape) (locals :: LocalsShape n) (wasmModule :: WasmModule) (inputLabels :: LabelStack k) (outputLabels :: LabelStack l) where
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
    Function :: InstructionSequence inputStack resultStack locals wasmModule EmptyLabels outputLabels -> Function inputStack resultStack locals outputLabels
    -- add a new type that captures the function type annotation, i.e.
    -- FuncTypeAnn inputStack resultStack ->

{-
=============================================================================
EXAMPLE FUNCTIONS
=============================================================================
-}

-- Example Call in Function
callExample :: Function Empty (I32 :> Empty) (I32 :<| I32 :<| VNil) EmptyLabels
callExample = Function $
       LocalGet SFZ    -- get first parameter
    :| LocalGet (SFS SFZ)  -- get second parameter
    :| Call "add2" (FFuncTypeAnn (I32 :> (I32 :> Empty)) (I32 :> Empty)) -- call add2 function
    :| End

-- Example MemoryLoad
-- the locals are the two I32 integers that are used to compute the address of the memory load
memLoadSequence :: Function Empty (I64 :> Empty) (I32 :<| I32 :<| VNil) EmptyLabels
memLoadSequence = Function $
       LocalGet SFZ
    :| MemoryLoad @I64 SMemArg 
    :| LocalGet (SFS SFZ)
    :| MemoryLoad @I64 SMemArg 
    :| I64Add 
    :| End

-- Example MemoryStore
memstoresequence :: Function Empty Empty (I32 :<| I64 :<| VNil) EmptyLabels
memstoresequence = Function $
       LocalGet (SFS SFZ)  -- get the address
    :| LocalGet SFZ      -- get the value to store
    :| MemoryStore @I64 SMemArg 
    :| End

-- add1Sequence :: InstructionSequence (I32 :> I32 :> Empty) (I32 :> Empty) 'VNil ('WasmModule '[]) ('WasmModule '[])
add1Sequence :: forall {n :: SNat} {k :: SNat} {l :: SNat} {inputStack :: StackShape} {locals :: LocalsShape n} {wasmModule :: WasmModule} {inputLabels :: LabelStack k} {outputLabels :: LabelStack l}. InstructionSequence (I32 :> (I32 :> inputStack)) (I32 :> inputStack) locals wasmModule inputLabels outputLabels
add1Sequence = I32Add :| End

-- addSubSequence :: InstructionSequence (I32 :> (I32 :> (I32 :> Empty))) (I32 :> Empty) 'VNil (WasmModule Z) ('WasmModule '[]) -- only 3 I32 because the result of the add is the first argument of the subtract
addSubSequence :: forall {n :: SNat} {k :: SNat} {l :: SNat} {inputStack :: StackShape} {locals :: LocalsShape n} {wasmModule :: WasmModule} {inputLabels :: LabelStack k} {outputLabels :: LabelStack l}. InstructionSequence (I32 :> (I32 :> (I32 :> inputStack))) (I32 :> inputStack) locals wasmModule inputLabels outputLabels
addSubSequence = I32Add :| (I32Sub :| End)

-- | Example 1: Add two integers
-- Takes two i32 parameters (slots 0 and 1), returns their sum
add2 :: Function Empty (I32 :> Empty) (I32 :<| I32 :<| VNil) EmptyLabels -- Function resultStack locals (repr the function parameters)
add2 = Function $
    -- Local slots: (0) first parameter, (1) second parameter
       LocalGet SFZ    -- Push first parameter
    :| LocalGet (SFS SFZ)     -- Push second parameter
    :| I32Add               -- Add them (pops 2, pushes 1 result)
    :| End

-- | Example 2: Factorial function using iteration
-- Takes one i32 parameter, returns its factorial
factorial :: Function Empty (I32 :> Empty) (I32 :<| I32 :<| VNil) EmptyLabels
factorial = Function $
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
printNumber :: Function Empty Empty (I32 :<| VNil) EmptyLabels
printNumber = Function $
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
complexCalculation :: Function Empty (I32 :> Empty) (I32 :<| I32 :<| I32 :<| I32 :<| VNil) EmptyLabels
complexCalculation = Function $
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
absoluteValue :: Function Empty (I32 :> Empty) (I32 :<| VNil) EmptyLabels
absoluteValue = Function $
    -- Check if input is negative
       LocalGet SFZ
    :| I32Const 0
    :| I32LtS              -- Is input < 0?
    :| If
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

-- | Runtime representation of the WebAssembly locals.
-- This is the actual data structure that holds local values during execution.
data Locals (localsShape :: LocalsShape n) where
    NoLocals   :: Locals 'VNil
    ConsLocals :: RuntimeTypeOf wasmType -> Locals localsShape -> Locals (wasmType :<| localsShape)

data Globals (globalsShape :: GlobalsShape n) where
    NoGlobals   :: Globals 'VNil
    ConsGlobals :: RuntimeTypeOf (GlobalTypeToWasmType wasmType) -> Mutability -> Globals globalsShape -> Globals (wasmType :<| globalsShape)

data RuntimeContext (stackShape :: StackShape) (localsShape :: LocalsShape n) (wasmModule :: WasmModule) = forall (m :: SNat). RuntimeContext
    { stack  :: Stack stackShape,
      locals :: Locals localsShape,
      globals :: Globals ((GetGlobals wasmModule) :: GlobalsShape m)
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

-- TODO
executeInstruction :: Instruction inputStack outputStack locals wasmModule inputLabels outputLabels
                   -> RuntimeContext inputStack locals globals
                   -> RuntimeContext outputStack locals globals
executeInstruction instr (RuntimeContext prevStack prevLocals prevGlobals) = case instr of
    I32Const val -> RuntimeContext (Push val prevStack) prevLocals prevGlobals
    I32Add       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 + val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
    I32Sub       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val1 - val2 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
    I32Mul       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 * val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
    I32Div       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `div` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
    I32RemU      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `mod` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
    I32RemS      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `mod` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
    I32EqZ       -> case prevStack of
                      Push val rest ->
                          let result = if val == 0 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
    I32Eq        -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 == val2 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I32Neq       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 /= val2 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I32LtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 < val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I32LtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 < val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I32LeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 <= val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I32LeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 <= val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I32GtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 > val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I32GtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 > val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I32GeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 >= val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I32GeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 >= val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64Add       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 + val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64Sub       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 - val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64Mul       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 * val1
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64Div       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `div` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64RemU      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `mod` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64RemS      -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = val2 `mod` val1 -- TODO double check the order!!
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64EqZ       -> case prevStack of
                      Push val rest ->
                          let result = if val == 0 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64Eq        -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 == val2 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64Neq       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val1 /= val2 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64LtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 < val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64LtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 < val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64LeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 <= val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64LeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 <= val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64GtS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 > val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64GtU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 > val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64GeS       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 >= val1 then 1 else 0
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    I64GeU       -> case prevStack of
                      Push val1 (Push val2 rest) ->
                          let result = if val2 >= val1 then 1 else 0 -- TODO: Check whether we should implement explicit WASM type for unsigned integers
                          in RuntimeContext (Push result rest) prevLocals prevGlobals
 
    Drop         -> case prevStack of
                      Push _ rest -> RuntimeContext rest prevLocals prevGlobals
 
    LocalGet idx -> case getLocalValue idx prevLocals of
                      val -> RuntimeContext (Push val prevStack) prevLocals prevGlobals
 
    LocalSet idx -> case prevStack of
                      Push val rest ->
                          let newLocals = setLocalValue idx val prevLocals
                          in RuntimeContext rest newLocals prevGlobals
 
    LocalTee idx -> case prevStack of
                      Push val rest ->
                          let newLocals = setLocalValue idx val prevLocals
                          in RuntimeContext (Push val rest) newLocals prevGlobals
 
    GlobalGet idx -> undefined
    GlobalSet idx-> undefined
    MemoryLoad arg-> undefined
    MemoryStore arg-> undefined
    Block btype seq-> undefined
    Loop labelIdx seq-> undefined
    If thenSeq elseSeq-> undefined
    Br labelIdx  -> undefined
    BrIf labelIdx-> undefined
    Call funcName typeAnn -> undefined

executeInstructionSequence :: InstructionSequence inputStack outputStack locals wasmModule inputLabels outputLabels
                           -> RuntimeContext inputStack locals globals
                           -> RuntimeContext outputStack locals globals
executeInstructionSequence = undefined

executeFunction :: Function inputStack outputStack locals labels
                   -> RuntimeContext Empty locals globals
                   -> RuntimeContext outputStack locals globals
executeFunction = undefined
