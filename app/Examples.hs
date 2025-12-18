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
module Examples where

import Data.Int (Int32, Int64)
import Data.Word (Word32, Word64)
import Types --(Length, WasmType(I64, I32), WasmType, ValStackShape, type (:+>+), CheckTopVecEqual, BlockType (..), FuncName, FuncTypeAnn (..), Take, FuncTypeAnn (..), Reverse, KnownWasmType (ForI32), LabelStackShape, GetLabelType, GetLabelCreationValStackLength, SomeValStackShape(..), KnownValStackShape (KnownValVNil, KnownValCons), GetSpecificValVec, LabelShape(..))
import Utils
import WasmModule
import Wasm
import WasmInterpreter



{-
=============================================================================
EXECUTION EXAMPLES
=============================================================================
-}
-- data RuntimeContext (valuesShape :: ValStackShape) (localsShape :: LocalsShape) (wasmModule :: WasmModule shape) (labelsShape :: LabelStackShape) = RuntimeContext
--     { values :: ValueStack valuesShape,
--       locals :: Locals localsShape,
--       globals :: Globals (GetGlobals wasmModule), -- :: GlobalsShape (GetGlobalsShape shape)),
--       labels :: LabelStack labelsShape,
--       memories :: Memory (GetMems wasmModule)
--       -- TODO: tables, etc.
--     }
executeAddStep :: StepResult [I32, I32] '[I32] '[] (WasmModuleR '[] '[]) '[] '[]
executeAddStep = step (RuntimeContext {values = ConsValues 5 (ConsValues 10 NoValues), locals = NoLocals, WasmInterpreter.globals = WasmInterpreter.NoGlobals, labels = NoLabels, memories = NoMems} :: RuntimeContext (I32 ': I32 ': '[]) '[] (WasmModuleR '[] '[]) '[]) 
                (CSingle (I32Add :| End))

executeAddMany :: RuntimeContext @(WasmModuleShapeR Z Z) '[I32] '[] (WasmModuleR '[] '[]) '[]
executeAddMany = stepMany (RuntimeContext {values = ConsValues 10 (ConsValues 5 (ConsValues 10 NoValues)), locals = NoLocals, WasmInterpreter.globals = WasmInterpreter.NoGlobals, labels = NoLabels, memories = NoMems} :: RuntimeContext (I32 ': I32 ': I32 ': '[]) '[] ((WasmModuleR '[] '[]) :: WasmModule ( WasmModuleShapeR Z Z)) '[]) 
                (I32Div :| I32Add :| End)

executeDivMany :: RuntimeContext @(WasmModuleShapeR Z Z) '[I32] '[] (WasmModuleR '[] '[]) '[]
executeDivMany = stepMany (RuntimeContext {values = ConsValues 5 (ConsValues 10 NoValues), locals = NoLocals, WasmInterpreter.globals = WasmInterpreter.NoGlobals, labels = NoLabels, memories = NoMems} :: RuntimeContext (I32 ': I32 ': '[]) '[] ((WasmModuleR '[] '[]) :: WasmModule ( WasmModuleShapeR Z Z)) '[]) 
                (I32Div :| End)

-- Execution example for callExample
-- executeCallExample :: RuntimeContext @(WasmModuleShapeR Z Z) finalVal '[] (WasmModuleR '[] '[]) finalLab
-- executeCallExample = stepMany (RuntimeContext {values = NoValues, locals = NoLocals, WasmInterpreter.globals = WasmInterpreter.NoGlobals, labels = NoLabels, memories = NoMems} :: RuntimeContext '[] '[] ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z)) '[])
--                 (LocalGet SFZ :| LocalGet (SFS SFZ) :| Call "add2" (FFuncTypeAnn (I32 : (I32 : [])) (I32 : [])) :| End)

-- Execution example for memLoadSequence
-- executeMemLoadSequence = stepMany (RuntimeContext {values = NoValues, locals = NoLocals, WasmInterpreter.globals = WasmInterpreter.NoGlobals, labels = NoLabels, memories = NoMems} :: RuntimeContext '[] '[] ((WasmModuleR '[] ('[ fromIntegral 10::Int32, fromIntegral 20::Int32 ] ': '[])) :: WasmModule (WasmModuleShapeR Z (S Z))) '[])
--                 (LocalGet SFZ :| MemoryLoad @I64 SFZ (SMemArg 0 0) :| LocalGet (SFS SFZ) :| MemoryLoad @I64 SFZ (SMemArg 0 0) :| I64Add :| End)

-- Execution example for memstoresequence
-- executeMemStoreSequence = stepMany (RuntimeContext {values = NoValues, locals = NoLocals, WasmInterpreter.globals = WasmInterpreter.NoGlobals, labels = NoLabels, memories = NoMems} :: RuntimeContext '[] '[] ((WasmModuleR '[] ('[] ': '[])) :: WasmModule (WasmModuleShapeR Z (S Z))) '[])
--                 (LocalGet (SFS SFZ) :| LocalGet SFZ :| MemoryStore @I64 SFZ (SMemArg 0 0) :| End)


-- Execution example for branchExample


{-
=============================================================================
VALIDATION EXAMPLES
=============================================================================
-}

-- Example Call in Function
callExample :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function '[] (I32 ': '[]) (I32 ': I32 ': '[]) '[] wm
callExample = Function (FFuncTypeAnn [] (I32 : [])) $
       LocalGet SFZ    -- get first parameter
    :| LocalGet (SFS SFZ)  -- get second parameter
    :| Call "add2" (FFuncTypeAnn (I32 : (I32 : [])) (I32 : [])) -- call add2 function
    :| End

-- Example MemoryLoad
-- the locals are the two I32 integers that are used to compute the address of the memory load
-- memLoadSequence :: Function EmptyValStack (I64 :> EmptyValStack) (I32 ': I32 ': VNil) EmptyLabels ((WasmModuleR VNil ('[ 'SomeWasmType ( RInt32 (fromIntegral 10 :: Int32)), 'SomeWasmType ( RInt32 (fromIntegral 20 :: Int32))] ': VNil)) :: WasmModule ( WasmModuleShapeR Z (S Z)))

memLoadSequence :: Function '[] (I64 ': '[]) (I32 ': I32 ': '[]) '[] ((WasmModuleR '[] ('[ fromIntegral 10::Int32, fromIntegral 20::Int32 ] ': '[])) :: WasmModule ( WasmModuleShapeR Z (S Z)))
memLoadSequence = Function (FFuncTypeAnn [] (I64 : [])) $
       LocalGet SFZ
    :| MemoryLoad @I64 SFZ (SMemArg 0 0) 
    :| LocalGet (SFS SFZ)
    :| MemoryLoad @I64 SFZ (SMemArg 0 0)
    :| I64Add 
    :| End

-- Example MemoryStore
-- memstoresequence :: Function EmptyValStack EmptyValStack (I32 ': I64 ': VNil) EmptyLabels ((WasmModuleR VNil (MemoryTypeR (LimitsR (fromIntegral 0 Word64) Nothing) '[] ': VNil)) :: WasmModule ( WasmModuleShapeR Z (S Z)))
memstoresequence :: Function '[] '[] (I32 ': I64 ': '[]) '[] ((WasmModuleR '[] ('[] ': '[])) :: WasmModule ( WasmModuleShapeR Z (S Z)))
memstoresequence = Function (FFuncTypeAnn [] []) $
       LocalGet (SFS SFZ)  -- get the address
    :| LocalGet SFZ      -- get the value to store
    :| MemoryStore @I64 SFZ (SMemArg 0 0)
    :| End

-- Example GlobalGet and GlobalSet
-- have to force the WasmModuleShape so :: WasmModule (WasmModuleShapeR (S Z) Z) is necessary!!!
globalGetSetSequence :: InstructionSequence '[] (I32 ': '[]) locals ((WasmModuleR (GlobalTypeMW Var I32 ': '[]) '[]) :: WasmModule (WasmModuleShapeR (S Z) Z)) outputLabels   outputLabels
globalGetSetSequence = 
    GlobalGet SFZ        -- get global at index 0
    :| I32Const 10
    :| I32Add
    :| GlobalSet SFZ      -- set global at index 0
    :| GlobalGet SFZ      -- get global at index 0 again
    :| End

globalGetSet :: Function '[] (I32 ': '[]) '[] '[] ((WasmModuleR (GlobalTypeMW Var I32 ': '[]) '[]) :: WasmModule ( WasmModuleShapeR (S Z) Z))
globalGetSet = Function (FFuncTypeAnn [] [I32]) globalGetSetSequence
-- Execution example for globalGetSetSequence
executeGlobalGetSetSequence :: RuntimeContext @(WasmModuleShapeR (S Z) Z)    '[I32] '[] (WasmModuleR '[GlobalTypeMW Var I32] '[]) '[]
executeGlobalGetSetSequence = stepMany (RuntimeContext {values = NoValues, locals = NoLocals, WasmInterpreter.globals = WasmInterpreter.ConsGlobals 5 SVar NoGlobals, labels = NoLabels, memories = NoMems} :: RuntimeContext '[] '[] ((WasmModuleR (GlobalTypeMW Var I32 ': '[]) '[]) :: WasmModule (WasmModuleShapeR (S Z) Z)) '[])
                globalGetSetSequence


add1Sequence :: forall {shape :: WasmModuleShape} {inputStack :: ValStackShape} {locals :: LocalsShape} {wasmModule :: WasmModule shape} {inputLabels :: LabelStackShape}. InstructionSequence (I32 ': (I32 ': inputStack)) (I32 ': inputStack) locals wasmModule inputLabels inputLabels
add1Sequence = I32Add :| End

executeAdd1Sequence :: RuntimeContext @(WasmModuleShapeR Z Z) '[I32] '[] (WasmModuleR '[] '[]) '[]
executeAdd1Sequence = stepMany (RuntimeContext {values = ConsValues 5 (ConsValues 6 NoValues), locals = NoLocals, WasmInterpreter.globals = WasmInterpreter.NoGlobals, labels = NoLabels, memories = NoMems} :: RuntimeContext (I32 ': I32 ': '[]) '[] ((WasmModuleR '[] '[]) :: WasmModule ( WasmModuleShapeR Z Z)) '[]) add1Sequence


addSubSequence :: forall {shape :: WasmModuleShape} {inputStack :: ValStackShape} {locals :: LocalsShape} {wasmModule :: WasmModule shape} {inputLabels :: LabelStackShape}. InstructionSequence (I32 ': (I32 ': (I32 ': inputStack))) (I32 ': inputStack) locals wasmModule inputLabels inputLabels
addSubSequence = I32Add :| (I32Sub :| End)
executeAddSub :: RuntimeContext @(WasmModuleShapeR Z Z) '[I32] '[] (WasmModuleR '[] '[]) '[]
executeAddSub = stepMany (RuntimeContext {values = ConsValues 10 (ConsValues 5 (ConsValues 10 NoValues)), locals = NoLocals, WasmInterpreter.globals = WasmInterpreter.NoGlobals, labels = NoLabels, memories = NoMems} :: RuntimeContext (I32 ': I32 ': I32 ': '[]) '[] ((WasmModuleR '[] '[]) :: WasmModule ( WasmModuleShapeR Z Z)) '[])  addSubSequence

-- example function for Br instruction
branchExampleSeq :: forall {shape :: WasmModuleShape} {inputStack :: ValStackShape} {locals :: LocalsShape} {wasmModule :: WasmModule shape} {outputLabels :: LabelStackShape}.
    InstructionSequence   inputStack   ('[] :+>+ Take (Length inputStack) (Reverse inputStack))   locals   wasmModule   outputLabels   outputLabels
branchExampleSeq = Block (BTParamsResults KnownValVNil KnownValVNil) (
                    Br SFZ 
                    :| End)
                :| End
branchExample :: Function '[] '[] (I32 ': '[]) ('LabelShape '[] Z ': '[]) ((WasmModuleR '[] '[]) :: WasmModule ( WasmModuleShapeR Z Z))
branchExample = Function (FFuncTypeAnn [] []) branchExampleSeq
       

executeBranchExample :: RuntimeContext @(WasmModuleShapeR Z Z) '[] '[] (WasmModuleR '[] '[]) '[]
executeBranchExample = stepMany (RuntimeContext {values = NoValues, locals = NoLocals, WasmInterpreter.globals = WasmInterpreter.NoGlobals, labels = NoLabels, memories = NoMems} :: RuntimeContext '[] '[] ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z)) '[])
                branchExampleSeq

    -- example function for Br instruction
branchExample2Seq :: forall {shape :: WasmModuleShape} {inputStack :: ValStackShape} {locals :: LocalsShape} {wasmModule :: WasmModule shape} {outputLabels :: LabelStackShape}.
    InstructionSequence '[] '[] (I32 ': '[]) wasmModule ('LabelShape '[] Z ': '[]) ('LabelShape '[] Z ': '[])
branchExample2Seq = Block (BTParamsResults KnownValVNil KnownValVNil) (
        Br SFZ
        :| End)
    :| Br SFZ
    :| End
branchExample2 ::forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) =>  Function '[] '[] (I32 ': '[]) ('LabelShape '[] Z ': '[]) wm
branchExample2 = Function (FFuncTypeAnn [] []) branchExample2Seq


    -- example function for Br instruction
branchExample3 :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) =>  Function '[] (I32 ': '[]) (I32 ': '[]) '[] wm
branchExample3 = Function (FFuncTypeAnn [] []) $
       Block (BTParamsResults KnownValVNil (KnownValCons ForI32 KnownValVNil)) (
        Block (BTParamsResults KnownValVNil KnownValVNil) (
            Br SFZ
            :| End)
        :| I32Const 42
        :| Br SFZ
        :| End
        )
    :| End

-- example function for Br instruction

branchExample4Seq :: InstructionSequence '[] ('[I32] :+>+ Take (Length '[]) (I32 : Reverse '[])) locals wasmModule outputLabels outputLabels
branchExample4Seq = Block (BTParamsResults KnownValVNil (KnownValCons ForI32 KnownValVNil)) (
                    Block (BTParamsResults KnownValVNil KnownValVNil) (
                        I32Const 42
                        :| Br (SFS SFZ)
                        :| I32Const 7
                        :| End)
                    :| End
                    )
                :| End

branchExample4 :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function '[] (I32 ': '[]) (I32 ': '[]) '[] wm
branchExample4 = Function (FFuncTypeAnn [] []) branchExample4Seq
       
executeBranchExample4 :: RuntimeContext @(WasmModuleShapeR Z Z) '[I32] '[] (WasmModuleR '[] '[]) '[]
executeBranchExample4 = stepMany RuntimeContext {values = NoValues, locals = NoLocals, WasmInterpreter.globals = WasmInterpreter.NoGlobals, labels = NoLabels, memories = NoMems}
                branchExample4Seq


-- | Example 1: Add two integers
-- Takes two i32 parameters (slots 0 and 1), returns their sum
add2 :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function '[] (I32 ': '[]) (I32 ': I32 ': '[]) '[] wm -- Function resultStack locals (repr the function parameters)
add2 = Function (FFuncTypeAnn [] (I32 : [])) $
    -- Local slots: (0) first parameter, (1) second parameter
       LocalGet SFZ    -- Push first parameter
    :| LocalGet (SFS SFZ)     -- Push second parameter
    :| I32Add               -- Add them (pops 2, pushes 1 result)
    :| End

-- | Example 2: Factorial function using iteration
-- Takes one i32 parameter, returns its factorial
factorial :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function '[] (I32 ': '[]) (I32 ': I32 ': '[]) '[] wm
factorial = Function (FFuncTypeAnn [] (I32 : [])) $
    -- Local slots: (0) input parameter (also used as counter), (1) accumulator
    -- Initialize accumulator to 1
       I32Const 1
    :| LocalSet (SFS SFZ)
    -- :| I32Const 0
    -- Main computation block
    :| Block (BTParamsResults KnownValVNil KnownValVNil) (
        -- Check if n <= 1 (base case)
           LocalGet SFZ
        :| I32Const 1
        :| I32LeS
        :| BrIf SFZ             -- Exit block if n <= 1
        -- Iterative loop for factorial computation
        :| Loop (BTParamsResults KnownValVNil KnownValVNil) (
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
            :| BrIf (SFS SFZ)             -- Branch back to loop start
            :| End)
        :| End)
    -- Return the accumulated result
    :| LocalGet (SFS SFZ)
    :| End

-- | Example 3: Function that returns nothing (void function).
-- Demonstrates different return types - this one returns Empty stack.
printNumber :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function '[] '[] (I32 ': '[]) '[] wm
printNumber = Function (FFuncTypeAnn [] []) $
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
complexCalculation :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function '[] (I32 ': '[]) (I32 ': I32 ': I32 ': I32 ': '[]) '[] wm
complexCalculation = Function (FFuncTypeAnn [] (I32 : [])) $
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
absoluteValue :: forall (s :: WasmModuleShape) (wm :: WasmModule s) . (s ~ WasmModuleShapeR Z Z) => Function '[] (I32 ': '[]) (I32 ': '[]) '[] wm
absoluteValue = Function (FFuncTypeAnn [] (I32 : [])) $
    -- Check if input is negative
       LocalGet SFZ
    :| I32Const 0
    :| I32LtS              -- Is input < 0?
    :| If (BTParamsResults KnownValVNil KnownValVNil)
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

