{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExplicitForAll #-}

-- | A type-safe embedded domain-specific language (DSL) for WebAssembly.
-- This module uses advanced Haskell type system features to ensure that
-- WebAssembly programs are stack-safe and type-correct at compile time.
module Wasm where

import Data.Int (Int32)
import GHC.TypeLits (Nat) -- , type (-))
-- import GHC.TypeError (TypeError, ErrorMessage(..))
import Types (WasmType(I64, I32), KnownWasmType, RuntimeTypeOf, WasmType)
import Utils
import WasmModule (WasmModule(..), GlobalsShape, GetGlobals)

{-
=============================================================================
STACK REPRESENTATION
=============================================================================
-}

-- | Type-level representation of the WebAssembly stack.
-- The stack grows to the right: (I32 :> I32 :> Empty) means two I32s on stack.
infixr 5 :>  -- Right-associative operator with precedence 5
data StackShape = Empty | (:>) WasmType StackShape

-- | Stack concatenation at the type level.
-- This combines two stack shapes: upper sits on top of lower.
-- Example: (I32 :> Empty) +>+ (I32 :> I32 :> Empty) = (I32 :> I32 :> I32 :> Empty)
type family (upper :: StackShape) +>+ (lower :: StackShape) :: StackShape where
    upper +>+ Empty = upper
    (top :> upper) +>+ lower = top :> (upper +>+ lower)

-- | Singleton type for stack shapes that we expect to return from blocks.
-- This lets us specify at the type level what shape a block should produce.
data KnownStackShape (stackShape :: StackShape) where
    NoReturn   :: KnownStackShape Empty                    -- Block returns nothing
    ReturnsOne :: KnownWasmType t -> KnownStackShape (t :> Empty)  -- Block returns one value

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
type Label = Int

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
data Instruction (inputStack :: StackShape) (outputStack :: StackShape) (locals :: LocalsShape n) (inputModule::WasmModule n) (outputModule::WasmModule n) where

    -- Constants: push a literal value onto the stack
    I32Const :: Int32 -> Instruction inputStack (I32 :> inputStack) locals inputModule outputModule

    -- i32 arithmetic operators (all pop two values, push one result)
    I32Add :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule
    I32Sub :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule
    I32Mul :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule
    I32Div :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule
    -- TODO: Handle division by zero at type level if WASM spec allows,
    --       otherwise document that this fails at runtime
    --       In spec it is defined as: if i2 is 0, then the result is undefined.
    --       Also I think division exists for signed and unsigned ints
    I32RemU :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule --remainder operation (unsigned)
    --      if i2 is zero then the output is undefined
    I32RemS :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule -- remaidner operaton (signed)
    --      if i2 is zero then the output is undefined -> the result has the sign of the first operator

    -- i32 comparison operators (pop two values, push i32 boolean result)
    I32EqZ :: Instruction (I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule           -- test if zero
    I32Eq  :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule   -- equal
    I32Neq :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule   -- inequality
    I32LtS :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule   -- less than (signed)
    I32LtU :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule   -- less than (unsigned)
    I32LeS :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule   -- less or equal (signed)
    I32LeU :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule   -- less or equal (unsigned)
    I32GtS :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule   -- greater than (signed)
    I32GtU :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule   -- greater than (unsigned)
    I32GeS :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule   -- greater or equal (signed)
    I32GeU :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals inputModule outputModule   -- greater or equal (unsigned)

    -- more operators (e.g. bitwise negation, bitwise conjunction, ..., min, max)

    -- i64 arithmetic operators
    I64Add :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule
    I64Sub :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule
    I64Mul :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule
    I64Div :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule
    -- differentiation signed vs unsigned?
    I64RemU :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule --remainder operation (unsigned)
    --      if i2 is zero then the output is undefined
    I64RemS :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule -- remaidner operaton (signed)
    --      if i2 is zero then the output is undefined -> the result has the sign of the first operator

    -- i64 comparison operators
    I64EqZ :: Instruction (I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule            -- test if equal to zero
    I64Eq  :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule     -- equal
    I64Neq :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule     -- inequality
    I64LtS :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule     -- less than (signed)
    I64LtU :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule     -- less than (unsigned)
    I64LeS :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule     -- less or equal (signed)
    I64LeU :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule     -- less or equal (unsigned)
    I64GtS :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule     -- greater than (signed)
    I64GtU :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule     -- greater than (unsigned)
    I64GeS :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule     -- greater or equal (signed)
    I64GeU :: Instruction (I64 :> I64 :> inputStack) (I64 :> inputStack) locals inputModule outputModule     -- greater or equal (unsigned)



    -- Stack manipulation
    Drop :: Instruction (dropped :> inputStack) inputStack locals inputModule outputModule  -- remove top value from stack

    -- Local variable operations
    -- LocalGet: push the value of a local variable onto the stack
    LocalGet :: SFin i n
             -> Instruction inputStack (Index i locals :> inputStack) locals inputModule outputModule

    -- LocalSet: pop a value from stack and store it in a local variable
    LocalSet :: SFin i n
             -> Instruction (Index i locals :> inputStack) inputStack locals inputModule outputModule
    -- TODO: Handle uninitialized local variables according to WASM spec

    -- GlobalGet: push the value of a global variable onto the stack
    -- ABHI: Call the type family defined in WasmModule.hs to do the desired
    --       kind conversion i.e. GlobalType -> WasmType and it will work!
    GlobalGet ::
        SFin i n 
        -> Instruction inputStack (Index i (GetGlobals inputModule) :> inputStack) locals inputModule outputModule
    
    -- GlobalSet: pop a value from stack and store it in a global variable => global type must be mutable where do we check this
    -- GlobalSet :: SFin i n
    --           -> Instruction (Index i inputModule :> inputStack) inputStack locals inputModule outputModule

    -- Control flow instructions
    -- Block: a sequence of instructions that can be exited early with 'br'
    -- The stack shape arithmetic (+>+) ensures the block result sits on top of the input stack
    -- typeidx|[valtype?] => typeidx points to a type in the type section.
    -- valtype? represents a function type like [] -> [valtype?]
    Block :: Label
          -> KnownStackShape outputShape -- represents the optional valtype however what about the typeidx? can't know the function type
          -> InstructionSequence inputStack (outputShape +>+ inputStack) locals inputModule outputModule
          -> Instruction inputStack (outputShape +>+ inputStack) locals inputModule outputModule

    -- Loop: a sequence of instructions that can be restarted with 'br'
    -- also technically the loop inst has the same blocktype annotation as block
    -- this part is missing here
    Loop  :: Label
          -> InstructionSequence inputStack inputStack locals inputModule outputModule
          -> Instruction inputStack inputStack locals inputModule outputModule

    -- If: conditional execution (pops i32 condition, executes one of two branches)
    If    :: InstructionSequence inputStack outputStack locals inputModule outputModule    -- then branch
          -> InstructionSequence inputStack outputStack locals inputModule outputModule    -- else branch
          -> Instruction (I32 :> inputStack) outputStack locals inputModule outputModule

    -- Br: unconditional branch to a label
    -- TODO: Make labels type-safe to prevent invalid references
    Br    :: Label -> Instruction inputStack outputStack locals inputModule outputModule

    -- BrIf: conditional branch (pops i32 condition)
    -- TODO: Make labels type-safe to prevent invalid references
    BrIf  :: Label -> Instruction (I32 :> inputStack) inputStack locals inputModule outputModule

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
data InstructionSequence (inputStack :: StackShape) (outputStack :: StackShape) (locals :: LocalsShape n) (inputModule :: WasmModule n) (outputModule :: WasmModule n) where
    End  :: InstructionSequence inputStack inputStack locals inputModule outputModule                -- Base case: empty sequence (identity)
    (:|) :: Instruction initialStack intermediateStack locals inputModule outputModule               -- Inductive case: first instruction
         -> InstructionSequence intermediateStack finalStack locals inputModule outputModule                         -- rest of sequence
         -> InstructionSequence initialStack finalStack locals inputModule outputModule                              -- combined sequence

{-
=============================================================================
FUNCTIONS
=============================================================================
-}

-- | A complete WebAssembly function.
-- Functions start with an empty stack and produce the specified final stack shape.
-- The locals context represents the function's parameters and local variables.
data Function (resultStack :: StackShape) (locals :: LocalsShape n) where
    Function :: InstructionSequence Empty resultStack locals inputModule outputModule -> Function resultStack locals

{-
=============================================================================
EXAMPLE FUNCTIONS
=============================================================================
-}


-- add1Sequence :: InstructionSequence (I32 :> I32 :> Empty) (I32 :> Empty) 'VNil ('WasmModule '[]) ('WasmModule '[])
add1Sequence :: forall {n :: SNat} {inputStack :: StackShape} {locals :: LocalsShape n} {inputModule :: WasmModule n} {outputModule :: WasmModule n}. InstructionSequence (I32 :> (I32 :> inputStack)) (I32 :> inputStack) locals inputModule outputModule
add1Sequence = I32Add :| End

-- addSubSequence :: InstructionSequence (I32 :> (I32 :> (I32 :> Empty))) (I32 :> Empty) 'VNil (WasmModule Z) ('WasmModule '[]) -- only 3 I32 because the result of the add is the first argument of the subtract
addSubSequence :: forall {n :: SNat} {inputStack :: StackShape} {locals :: LocalsShape n} {inputModule :: WasmModule n} {outputModule :: WasmModule n}. InstructionSequence (I32 :> (I32 :> (I32 :> inputStack))) (I32 :> inputStack) locals inputModule outputModule
addSubSequence = I32Add :| (I32Sub :| End)

-- | Example 1: Add two integers
-- Takes two i32 parameters (slots 0 and 1), returns their sum
add2 :: Function (I32 :> Empty) (I32 :<| I32 :<| VNil)  -- Function resultStack locals (repr the function parameters)
add2 = Function $
    -- Local slots: (0) first parameter, (1) second parameter
       LocalGet SFZ    -- Push first parameter
    :| LocalGet (SFS SFZ)     -- Push second parameter
    :| I32Add               -- Add them (pops 2, pushes 1 result)
    :| End

-- | Example 2: Factorial function using iteration
-- Takes one i32 parameter, returns its factorial
factorial :: Function (I32 :> Empty) (I32 :<| I32 :<| VNil)
factorial = Function $
    -- Local slots: (0) input parameter (also used as counter), (1) accumulator
    -- Initialize accumulator to 1
       I32Const 1
    :| LocalSet (SFS SFZ)
    -- Main computation block
    :| Block 0 NoReturn (
        -- Check if n <= 1 (base case)
           LocalGet SFZ
        :| I32Const 1
        :| I32LeS
        :| BrIf 0              -- Exit block if n <= 1
        -- Iterative loop for factorial computation
        :| Loop 1 (
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
            :| BrIf 1             -- Branch back to loop start
            :| End)
        :| End)
    -- Return the accumulated result
    :| LocalGet (SFS SFZ)
    :| End

-- | Example 3: Function that returns nothing (void function).
-- Demonstrates different return types - this one returns Empty stack.
printNumber :: Function Empty (I32 :<| VNil)
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
complexCalculation :: Function (I32 :> Empty) (I32 :<| I32 :<| I32 :<| I32 :<| VNil)
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
absoluteValue :: Function (I32 :> Empty) (I32 :<| VNil)
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

data RuntimeContext (stackShape :: StackShape) (localsShape :: LocalsShape n) = RuntimeContext
    { stack  :: Stack stackShape,
      locals :: Locals localsShape
      -- TODO: labels, tables, etc.
    }

-- TODO
executeInstruction :: Instruction inputStack outputStack locals inputModule outputModule
                   -> RuntimeContext inputStack locals
                   -> RuntimeContext outputStack locals
executeInstruction = undefined

executeInstructionSequence :: InstructionSequence inputStack outputStack locals inputModule outputModule
                           -> RuntimeContext inputStack locals
                           -> RuntimeContext outputStack locals
executeInstructionSequence = undefined

executeFunction :: Function outputStack locals
                   -> RuntimeContext Empty locals
                   -> RuntimeContext outputStack locals
executeFunction = undefined
