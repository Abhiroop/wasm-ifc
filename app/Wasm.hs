{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A type-safe embedded domain-specific language (DSL) for WebAssembly.
-- This module uses advanced Haskell type system features to ensure that
-- WebAssembly programs are stack-safe and type-correct at compile time.
module Wasm where

import GHC.TypeLits (Nat, type (+), type (-), CmpNat)
import GHC.TypeError (TypeError, ErrorMessage(..))
import Data.Type.Equality (type (==))
import Data.Kind (Type)
import Data.Int (Int32)

{-
=============================================================================
SCALAR VALUES AND TYPES
=============================================================================
-}

-- | WebAssembly value types.
-- Currently only supports 32-bit integers, but could be extended with:
-- I64, F32, F64, etc.
data WasmType = I32

-- | Singleton type for WasmType.
-- This is a "witness" type that lets us bring type-level information
-- (the WasmType kind) into term-level code. This is a common pattern
-- in dependently-typed Haskell programming.
data KnownWasmType (wasmType :: WasmType) where
    ForI32 :: KnownWasmType I32

-- | Type family that maps WebAssembly types to their Haskell representations.
-- This is how we connect the type-level WebAssembly types to actual runtime values.
type family RuntimeTypeOf (wasmType :: WasmType) :: Type where
    RuntimeTypeOf I32 = Int32

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

-- | Singleton type for slot indices.
-- This is another witness type that brings type-level natural numbers
-- into term-level code, allowing us to refer to specific local variable slots.
data KnownSlot (slotIndex :: SlotIndex) where
    SlotZero :: KnownSlot 0
    SlotOne  :: KnownSlot 1
    -- TODO: Add more slots or make this more general

-- | Type-level list representing the types of local variables.
-- Example: [I32, I32] means two local i32 variables.
type LocalsShape = [WasmType]

-- | Type-level comparison: is n less than m?
type family (n :: Nat) <? (m :: Nat) :: Bool where
    n <? m = CmpNat n m == 'LT

-- | Calculate the length of a locals context.
type family ContextLength (context :: LocalsShape) :: Nat where
    ContextLength '[] = 0
    ContextLength (_ ': rest) = 1 + ContextLength rest

-- | Helper for bounds-checked local variable access.
-- This provides nice error messages when trying to access out-of-bounds locals.
type family LocalAccessHelper (slotIndex :: SlotIndex) (context :: LocalsShape) (inBounds :: Bool) :: WasmType where
    LocalAccessHelper 0 (top ': _) 'True = top
    LocalAccessHelper n (_ ': rest) 'True = GetLocalType (n - 1) rest
    LocalAccessHelper n context 'False =
        TypeError ('Text "Local variable index out of bounds: "
                  ':<>: 'ShowType n
                  ':<>: 'Text " exceeds context length "
                  ':<>: 'ShowType (ContextLength context))

-- | Get the type of a local variable at a given slot.
-- This performs bounds checking and gives helpful error messages.
type family GetLocalType (slotIndex :: SlotIndex) (context :: LocalsShape) :: WasmType where
    GetLocalType n context = LocalAccessHelper n context (n <? ContextLength context)

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
data Instruction (inputStack :: StackShape) (outputStack :: StackShape) (locals :: LocalsShape) where

    -- Constants: push a literal value onto the stack
    I32Const :: Int32 -> Instruction inputStack (I32 :> inputStack) locals

    -- i32 arithmetic operators (all pop two values, push one result)
    I32Add :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals
    I32Sub :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals
    I32Mul :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals
    I32Div :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals
    -- TODO: Handle division by zero at type level if WASM spec allows,
    --       otherwise document that this fails at runtime

    -- i32 comparison operators (pop two values, push i32 boolean result)
    I32EqZ :: Instruction (I32 :> inputStack) (I32 :> inputStack) locals           -- test if zero
    I32Eq  :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals   -- equal
    I32LtS :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals   -- less than (signed)
    I32LtU :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals   -- less than (unsigned)
    I32LeS :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals   -- less or equal (signed)
    I32LeU :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals   -- less or equal (unsigned)
    I32GtS :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals   -- greater than (signed)
    I32GtU :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals   -- greater than (unsigned)
    I32GeS :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals   -- greater or equal (signed)
    I32GeU :: Instruction (I32 :> I32 :> inputStack) (I32 :> inputStack) locals   -- greater or equal (unsigned)

    -- Stack manipulation
    Drop :: Instruction (dropped :> inputStack) inputStack locals  -- remove top value from stack

    -- Local variable operations
    -- LocalGet: push the value of a local variable onto the stack
    LocalGet :: KnownSlot (slotIndex :: SlotIndex)
             -> Instruction inputStack (GetLocalType slotIndex locals :> inputStack) locals

    -- LocalSet: pop a value from stack and store it in a local variable
    LocalSet :: KnownSlot (slotIndex :: SlotIndex)
             -> Instruction (GetLocalType slotIndex locals :> inputStack) inputStack locals
    -- TODO: Handle uninitialized local variables according to WASM spec

    -- Control flow instructions
    -- Block: a sequence of instructions that can be exited early with 'br'
    -- The stack shape arithmetic (+>+) ensures the block result sits on top of the input stack
    Block :: Label
          -> KnownStackShape outputShape
          -> InstructionSequence inputStack (outputShape +>+ inputStack) locals
          -> Instruction inputStack (outputShape +>+ inputStack) locals

    -- Loop: a sequence of instructions that can be restarted with 'br'
    Loop  :: Label
          -> InstructionSequence inputStack inputStack locals
          -> Instruction inputStack inputStack locals

    -- If: conditional execution (pops i32 condition, executes one of two branches)
    If    :: InstructionSequence inputStack outputStack locals    -- then branch
          -> InstructionSequence inputStack outputStack locals    -- else branch
          -> Instruction (I32 :> inputStack) outputStack locals

    -- Br: unconditional branch to a label
    -- TODO: Make labels type-safe to prevent invalid references
    Br    :: Label -> Instruction inputStack outputStack locals

    -- BrIf: conditional branch (pops i32 condition)
    -- TODO: Make labels type-safe to prevent invalid references
    BrIf  :: Label -> Instruction (I32 :> inputStack) inputStack locals

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
data InstructionSequence (inputStack :: StackShape) (outputStack :: StackShape) (locals :: LocalsShape) where
    End  :: InstructionSequence inputStack inputStack locals                -- Base case: empty sequence (identity)
    (:|) :: Instruction initialStack intermediateStack locals               -- Inductive case: first instruction
         -> InstructionSequence intermediateStack finalStack locals                         -- rest of sequence
         -> InstructionSequence initialStack finalStack locals                              -- combined sequence

{-
=============================================================================
FUNCTIONS
=============================================================================
-}

-- | A complete WebAssembly function.
-- Functions start with an empty stack and produce the specified final stack shape.
-- The locals context represents the function's parameters and local variables.
data Function (resultStack :: StackShape) (locals :: LocalsShape) where
    Function :: InstructionSequence Empty resultStack locals -> Function resultStack locals

{-
=============================================================================
EXAMPLE FUNCTIONS
=============================================================================
-}

-- | Example 1: Add two integers
-- Takes two i32 parameters (slots 0 and 1), returns their sum
add2 :: Function (I32 :> Empty) (I32 ': I32 ': '[])
add2 = Function $
    -- Local slots: (0) first parameter, (1) second parameter
       LocalGet SlotZero    -- Push first parameter
    :| LocalGet SlotOne     -- Push second parameter
    :| I32Add               -- Add them (pops 2, pushes 1 result)
    :| End

-- | Example 2: Factorial function using iteration
-- Takes one i32 parameter, returns its factorial
factorial :: Function (I32 :> Empty) (I32 ': I32 ': '[])
factorial = Function $
    -- Local slots: (0) input parameter (also used as counter), (1) accumulator
    -- Initialize accumulator to 1
       I32Const 1
    :| LocalSet SlotOne
    -- Main computation block
    :| Block 0 NoReturn (
        -- Check if n <= 1 (base case)
           LocalGet SlotZero
        :| I32Const 1
        :| I32LeS
        :| BrIf 0              -- Exit block if n <= 1
        -- Iterative loop for factorial computation
        :| Loop 1 (
            -- accumulator *= n
               LocalGet SlotOne
            :| LocalGet SlotZero
            :| I32Mul
            :| LocalSet SlotOne
            -- n -= 1
            :| LocalGet SlotZero
            :| I32Const 1
            :| I32Sub
            :| LocalSet SlotZero
            -- Continue if n > 1
            :| LocalGet SlotZero
            :| I32Const 1
            :| I32GtS
            :| BrIf 1             -- Branch back to loop start
            :| End)
        :| End)
    -- Return the accumulated result
    :| LocalGet SlotOne
    :| End

-- | Example 3: Function that returns nothing (void function).
-- Demonstrates different return types - this one returns Empty stack.
printNumber :: Function Empty (I32 ': '[])
printNumber = Function $
    -- Just consume the parameter without returning anything
       LocalGet SlotZero
    :| Drop
    :| End

-- | Example 4: Function with more complex local variable patterns.
-- Takes one parameter, uses three local variables for intermediate calculations.
complexCalculation :: Function (I32 :> Empty) (I32 ': I32 ': I32 ': I32 ': '[])
complexCalculation = Function $
    -- Local slots: (0) input, (1) temp1, (2) temp2, (3) result
    -- temp1 = input * 2
       LocalGet SlotZero
    :| I32Const 2
    :| I32Mul
    :| LocalSet SlotOne
    -- temp2 = input + 10
    :| LocalGet SlotZero
    :| I32Const 10
    :| I32Add
    -- TODO: Need more slot witnesses for slots 2 and 3
    -- This is incomplete but shows the pattern
    :| End

-- | Example 5: Conditional logic with If instruction.
-- Returns the absolute value of the input.
absoluteValue :: Function (I32 :> Empty) (I32 ': '[])
absoluteValue = Function $
    -- Check if input is negative
       LocalGet SlotZero
    :| I32Const 0
    :| I32LtS              -- Is input < 0?
    :| If
        -- Then branch: negate the number (0 - input)
        (  I32Const 0
        :| LocalGet SlotZero
        :| I32Sub
        :| End)
        -- Else branch: return input as-is
        (  LocalGet SlotZero
        :| End)
    :| End

-- Bad example (fails at compile time)
--nestedControlFlow :: Function (I32 :> Empty) (I32 ': I32 ': '[])
--nestedControlFlow = Function $
--    -- Outer block
--       Block 0 (ReturnsOne ForI32) (
--           LocalGet SlotZero
--        :| I32Const 10
--        :| I32GtS
--        :| BrIf 0  -- Exit outer block if input > 10
--        -- Inner block
--        :| Block 1 NoReturn (
--               LocalGet SlotZero
--            :| I32Const 5
--            :| I32LtS
--            :| BrIf 1  -- Exit inner block if input < 5
--            -- If we're here, 5 <= input <= 10
--            :| LocalGet SlotZero
--            :| I32Const 2
--            :| I32Mul
--            :| LocalSet SlotOne
--            :| End)
--        -- Default case: return input unchanged
--        :| LocalGet SlotZero
--        :| End)
--    :| LocalGet SlotOne  -- Return the result
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
data Locals (localsShape :: LocalsShape) where
    NoLocals   :: Locals '[]
    ConsLocals :: RuntimeTypeOf wasmType -> Locals localsShape -> Locals (wasmType ': localsShape)

data RuntimeContext (stackShape :: StackShape) (localsShape :: LocalsShape) = RuntimeContext
    { stack  :: Stack stackShape,
      locals :: Locals localsShape
      -- TODO: labels, tables, etc.
    }

-- TODO
executeInstruction :: Instruction inputStack outputStack locals
                   -> RuntimeContext inputStack locals
                   -> RuntimeContext outputStack locals
executeInstruction = undefined

executeInstructionSequence :: InstructionSequence inputStack outputStack locals
                           -> RuntimeContext inputStack locals
                           -> RuntimeContext outputStack locals
executeInstructionSequence = undefined

executeFunction :: Function outputStack locals
                   -> RuntimeContext Empty locals
                   -> RuntimeContext outputStack locals
executeFunction = undefined
