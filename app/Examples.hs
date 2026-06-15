{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-
TODO Summary:
1. Line 39: tables, etc.
2. Line 196: BUG: in validation this instruction is not removed and therefore the types do not agree
-}

{- | A type-safe embedded domain-specific language (DSL) for WebAssembly.
This module uses advanced Haskell type system features to ensure that
WebAssembly programs are stack-safe and type-correct at compile time.
-}
module Examples where

import Data.Int (Int32, Int64)
import Types
import Utils
import Wasm
import WasmInterpreter
import WasmModule

{-
=============================================================================
EXECUTION EXAMPLES (Total 41 Examples)
=============================================================================
-}

{-
=============================================================================
BINARY OPERATION INSTRUCTIONS (6 Examples)
=============================================================================
-}

-- 1
executeAddStep :: RuntimeContext @WasmModuleShapeR '[I32 :~ High] '[] (WasmModuleR '[] '[]) '[]
executeAddStep =
    stepMany
        ( RuntimeContext
            { values = ConsValues 5 (ConsValues 10 NoValues)
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext (I32 :~ Low ': I32 :~ High ': '[]) '[] (WasmModuleR '[] '[]) '[]
        )
        ((I32Add :| End) :: InstructionSequence '[I32 :~ Low, I32 :~ High] '[I32 :~ High] '[] (WasmModuleR '[] '[]) '[] '[] '[Low] '[Low])

-- 2
executeAddMany ::
    RuntimeContext @WasmModuleShapeR '[I32 :~ Low] '[] (WasmModuleR '[] '[] :: WasmModule WasmModuleShapeR) '[]
executeAddMany =
    stepMany
        ( RuntimeContext
            { values = ConsValues 5 (ConsValues 10 (ConsValues 10 NoValues))
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                (I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': '[])
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        (I32Div :| I32Add :| End :: InstructionSequence '[I32 :~ Low, I32 :~ Low, I32 :~ Low] '[I32 :~ Low] '[] (WasmModuleR '[] '[]) '[] '[] '[Low] '[Low])

-- 3
executeDivMany ::
    RuntimeContext @WasmModuleShapeR '[I32 :~ Low] '[] (WasmModuleR '[] '[] :: WasmModule WasmModuleShapeR) '[]
executeDivMany =
    stepMany
        ( RuntimeContext
            { values = ConsValues 5 (ConsValues 10 NoValues)
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                (I32 :~ Low ': I32 :~ Low ': '[])
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        (I32Div :| End :: InstructionSequence '[I32 :~ Low, I32 :~ Low] '[I32 :~ Low] '[] (WasmModuleR '[] '[]) '[] '[] '[Low] '[Low])

-- 4
add1Sequence ::
    forall
        {shape :: WasmModuleShape}
        {inputStack :: ValStackShape}
        {locals :: LocalsShape}
        {wasmModule :: WasmModule WasmModuleShapeR}
        {inputLabels :: LabelStackShape}.
    InstructionSequence
        (I32 :~ Low ': (I32 :~ Low ': inputStack))
        (I32 :~ Low ': inputStack)
        locals
        wasmModule
        inputLabels
        inputLabels
        '[Low]
        '[Low]
add1Sequence = I32Add :| End

executeAdd1Sequence ::
    RuntimeContext @WasmModuleShapeR '[I32 :~ Low] '[] (WasmModuleR '[] '[]) '[]
executeAdd1Sequence =
    stepMany
        ( RuntimeContext
            { values = ConsValues 5 (ConsValues 6 NoValues)
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                (I32 :~ Low ': I32 :~ Low ': '[])
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        add1Sequence

-- 5
addSubSequence ::
    forall
        {shape :: WasmModuleShape}
        {inputStack :: ValStackShape}
        {locals :: LocalsShape}
        {wasmModule :: WasmModule WasmModuleShapeR}
        {inputLabels :: LabelStackShape}.
    InstructionSequence
        (I32 :~ Low ': (I32 :~ Low ': (I32 :~ Low ': inputStack)))
        (I32 :~ Low ': inputStack)
        locals
        wasmModule
        inputLabels
        inputLabels
        '[Low]
        '[Low]
addSubSequence = I32Add :| (I32Sub :| End)
executeAddSub ::
    RuntimeContext @WasmModuleShapeR '[I32 :~ Low] '[] (WasmModuleR '[] '[]) '[]
executeAddSub =
    stepMany
        ( RuntimeContext
            { values = ConsValues 10 (ConsValues 5 (ConsValues 10 NoValues))
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                (I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': '[])
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        addSubSequence

-- 6
{- | Example 1: Add two integers
Takes two i32 parameters (slots 0 and 1), returns their sum
-}
add2Seq ::
    InstructionSequence '[] '[I32 :~ Low] '[I32 :~ Low, I32 :~ Low] wasmModule outputLabels outputLabels '[Low] '[Low]
add2Seq =
    LocalGet SFZ -- Push first parameter
        :| LocalGet (SFS SFZ) -- Push second parameter
        :| I32Add -- Add them (pops 2, pushes 1 result)
        :| End

-- add2 ::
--     forall (s :: WasmModuleShape) (wm :: WasmModule s).
--     Function '[] (I32 :~ Low ': '[]) (I32 :~ Low ': I32 :~ Low ': '[]) '[] wm '[Low] '[Low] -- Function resultStack locals (repr the function parameters)
-- add2 =
--     Function
--         (FFuncTypeAnn [] [I32 :~ Low])
--         -- Local slots: (0) first parameter, (1) second parameter
--         add2Seq
executeAdd2 ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ Low]
        '[I32 :~ Low, I32 :~ Low]
        (WasmModuleR '[] '[])
        '[]
executeAdd2 =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals 5 (ConsLocals 2 NoLocals)
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[I32 :~ Low, I32 :~ Low]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        add2Seq


-- Example Call in Function
{-
callExample ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).
    InstructionSequence '[I32, I32] '[I32] '[] wm '[] '[] 
callExample =
        -- LocalSet SFZ -- get first parameter
        --     :| LocalSet (SFS SFZ) -- get second parameter
            Call "add" (FFuncTypeAnn (ConsLocalsShape ForI32 (ConsLocalsShape ForI32 NoLocalsShape)) (KnownValCons ForI32 KnownValVNil)) -- call add2 function
            :| End
executeCallExample ::
    RuntimeContext '[I32] '[] (WasmModuleR '[] '[] :: WasmModule shape) '[]
executeCallExample =
    stepMany
        ( RuntimeContext
            { values = ConsValues 5 (ConsValues 10 NoValues)
            , locals = NoLocals-- initialize locals for parameters, will be set by LocalSet instructions in callExample sequence
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            , funcs = Data.Map.fromList [("add", SomeFuncBody simpleAddSequence)]
            } ::
            RuntimeContext
                '[I32, I32]
                '[]
                (WasmModuleR '[] '[] :: WasmModule shape)
                '[]
        )
        callExample
        -}

{-
=============================================================================
MEMORY INSTRUCTIONS (5 Examples)
=============================================================================
    -}
-- Example MemoryLoad
-- the locals are the two I32 integers that are used to compute the address of the memory load
-- memLoadSequence :: Function EmptyValStack (I64 :> EmptyValStack) (I32 ': I32 ': VNil) EmptyLabels ((WasmModuleR VNil ('[ 'SomeWasmType ( RInt32 (fromIntegral 10 :: Int32)), 'SomeWasmType ( RInt32 (fromIntegral 20 :: Int32))] ': VNil)) :: WasmModule ( WasmModuleShapeR Z (S Z)))
createMemory :: Int -> MemoryArray
createMemory size = replicate size 0

currMem1 :: MemoryArray
-- currMem =  [10 :: Word8, 0, 0, 0, 20 :: Word8, 0, 0, 0] ++
currMem1 = createMemory 65536 -- 65528 -- create a memory with 1 page (64KiB)
currMem2 :: MemoryArray
currMem2 = store @I32 currMem1 0 (20 :: Int32)
currMem :: MemoryArray
currMem = store @I32 currMem2 4 (10 :: Int32)

-- 1
memLoadSequence ::
    InstructionSequence
        '[]
        '[I32 :~ Low]
        '[I64 :~ Low, I64 :~ Low]
        ( ( WasmModuleR
                '[]
                ( currMem ': '[]
                )
          ) ::
            WasmModule WasmModuleShapeR
        )
        '[]
        '[]
        '[Low]
        '[Low]
memLoadSequence =
    LocalGet SFZ
        :| MemoryLoad @I32 @Low SFZ (SMemArg 0 0)
        :| LocalGet (SFS SFZ)
        :| MemoryLoad @I32 @Low SFZ (SMemArg 0 0)
        :| I32Add
        :| End

-- memLoad ::
--     Function
--         '[]
--         (I32 :~ Low ': '[])
--         (I64 :~ Low ': I64 :~ Low ': '[])
--         '[]
--         ( ( WasmModuleR
--                 '[]
--                 ( currMem ': '[]
--                 )
--           ) ::
--             WasmModule WasmModuleShapeR
--         )
--         '[Low]
--         '[Low]
-- memLoad =
--     Function
--         (FFuncTypeAnn [] [I32 :~ Low])
--         memLoadSequence

executeMemLoad ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ Low]
        '[I64 :~ Low, I64 :~ Low]
        ( WasmModuleR
            '[]
            ( currMem ': '[] )
        :: WasmModule WasmModuleShapeR
        )
        '[]
executeMemLoad =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals (4 :: Int64) (ConsLocals (0 :: Int64) NoLocals)
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = WasmInterpreter.ConsMems currMem NoMems
            } ::
            RuntimeContext
                '[]
                '[I64 :~ Low, I64 :~ Low]
                ( ( WasmModuleR
                        '[]
                        ( currMem ': '[]
                        )
                  ) :: WasmModule WasmModuleShapeR
                )
                '[]
        )
        memLoadSequence

-- 2
memLoadSequence1 ::
    InstructionSequence
        '[]
        '[I32 :~ High, I32 :~ Low]
        '[I64 :~ Low, I64 :~ High]
        ( ( WasmModuleR
                '[]
                ( currMem ': '[] )
          ) ::
            WasmModule WasmModuleShapeR
        )
        '[]
        '[]
        '[Low]
        '[Low]
memLoadSequence1 =
    LocalGet SFZ
        :| MemoryLoad @I32 @Low SFZ (SMemArg 0 0)
        :| LocalGet (SFS SFZ)
        :| MemoryLoad @I32 @High SFZ (SMemArg 0 0)
        :| End

executeMemLoadSequence1 ::
    RuntimeContext
        @WasmModuleShapeR
        '[I32 :~ High, I32 :~ Low]
        '[I64 :~ Low, I64 :~ High]
        ( WasmModuleR
            '[]
            ( currMem ': '[] )
        )
        '[]
executeMemLoadSequence1 =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals 4 (ConsLocals 0 NoLocals)
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = WasmInterpreter.ConsMems currMem NoMems
            } ::
            RuntimeContext
                '[]
                '[I64 :~ Low, I64 :~ High]
                ( ( WasmModuleR
                        '[]
                        ( currMem ': '[] )
                  ) :: WasmModule WasmModuleShapeR
                )
                '[]
        )
        memLoadSequence1

-- 3
-- Example MemoryStore
-- memstoresequence :: Function EmptyValStack EmptyValStack (I32 ': I64 ': VNil) EmptyLabels ((WasmModuleR VNil (MemoryTypeR (LimitsR (fromIntegral 0 Word64) Nothing) '[] ': VNil)) :: WasmModule ( WasmModuleShapeR Z (S Z)))
memStoreSequence ::
    InstructionSequence
        '[]
        '[]
        '[I32 :~ Low, I64 :~ Low]
        ( (WasmModuleR '[] (storeMem ': '[])) ::
            WasmModule WasmModuleShapeR
        )
        '[]
        '[]
        '[Low]
        '[Low]
memStoreSequence =
    LocalGet SFZ -- get the value to store
        :| LocalGet (SFS SFZ) -- get the address
        :| MemoryStore @I32 SFZ (SMemArg 0 0)
        :| End

-- memStore ::
--     Function
--         '[]
--         '[]
--         '[I32 :~ Low, I64 :~ Low]
--         '[]
--         ((WasmModuleR '[] ('[] ': '[])) :: WasmModule WasmModuleShapeR)
--         '[Low]
--         '[Low]
-- memStore =
--     Function
--         (FFuncTypeAnn [] [])
--         memStoreSequence

storeMem :: MemoryArray
storeMem = createMemory 65536
executeMemStore ::
    RuntimeContext
        @WasmModuleShapeR
        '[]
        '[I32 :~ Low, I64 :~ Low]
        ( WasmModuleR
            '[]
            ( storeMem ': '[] )
            :: WasmModule WasmModuleShapeR
        )
        '[]
executeMemStore =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals 255 (ConsLocals 65531 NoLocals)
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = WasmInterpreter.ConsMems storeMem NoMems
            } ::
            RuntimeContext
                '[]
                '[I32 :~ Low, I64 :~ Low]
                ( ( WasmModuleR
                        '[]
                        ( storeMem ': '[]
                        )
                  ) :: WasmModule WasmModuleShapeR
                )
                '[]
        )
        memStoreSequence

 -- 4
memLoadStoreSequence ::
    InstructionSequence
        '[]
        '[I32 :~ Low]
        '[I32 :~ Low]
        ( ( WasmModuleR
                '[]
                ( storeMem
                    ': '[]
                )
          ) ::
            WasmModule WasmModuleShapeR
        )
        '[]
        '[]
        '[Low]
        '[Low]
memLoadStoreSequence =
    LocalGet SFZ -- get the value to store
        :| I64Const IsLow 0 -- get the address
        :| MemoryStore @I32 SFZ (SMemArg 0 0)
        :| I64Const IsLow 0
        :| MemoryLoad @I32 @Low SFZ (SMemArg 0 0)
        :| End

executeMemLoadStore ::
    RuntimeContext
        @WasmModuleShapeR
        '[I32 :~ Low]
        '[I32 :~ Low]
        ( WasmModuleR
            '[]
            ( storeMem
                ': '[]
            )
            :: WasmModule WasmModuleShapeR
        )
        '[]
executeMemLoadStore =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals (2147483647 :: Int32) NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = WasmInterpreter.ConsMems storeMem NoMems
            } ::
            RuntimeContext
                '[]
                '[I32 :~ Low]
                ( ( WasmModuleR
                        '[]
                        ( storeMem
                            ': '[]
                        )
                  ) :: WasmModule WasmModuleShapeR
                )
                '[]
        )
        memLoadStoreSequence

-- 5
memLoadStore64Sequence ::
    InstructionSequence
        '[]
        '[I64 :~ Low]
        '[I64 :~ Low]
        ( ( WasmModuleR
                '[]
                ( storeMem
                    ': '[]
                )
          ) ::
            WasmModule WasmModuleShapeR
        )
        '[]
        '[]
        '[Low]
        '[Low]
memLoadStore64Sequence =
    LocalGet SFZ -- get the value to store
        :| I64Const IsLow 0 -- get the address
        :| MemoryStore @I64 SFZ (SMemArg 0 0)
        :| I64Const IsLow 0
        :| MemoryLoad @I64 @Low SFZ (SMemArg 0 0)
        :| End

executeMemLoadStore64 ::
    RuntimeContext
        @WasmModuleShapeR
        '[I64 :~ Low]
        '[I64 :~ Low]
        ( WasmModuleR
            '[]
            ( storeMem
                ': '[]
            )
            :: WasmModule WasmModuleShapeR
        )
        '[]
executeMemLoadStore64 =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals (9223372036854775807 :: Int64) NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = WasmInterpreter.ConsMems storeMem NoMems
            } ::
            RuntimeContext
                '[]
                '[I64 :~ Low]
                ( ( WasmModuleR
                        '[]
                        ( storeMem
                            ': '[]
                        )
                  ) :: WasmModule WasmModuleShapeR
                )
                '[]
        )
        memLoadStore64Sequence

{-
=============================================================================
GLOBAL GET AND SET INSTRUCTIONS (2 Examples)
=============================================================================
-}
-- Example GlobalGet and GlobalSet
-- have to force the WasmModuleShape so :: WasmModule WasmModuleShapeR is necessary!!!

-- 1
globalGetSetSequence ::
    InstructionSequence
        '[]
        '[I32 :~ Low]
        locals
        ( (WasmModuleR (GlobalTypeMW Var (I32 :~ Low) ': '[]) '[]) ::
            WasmModule WasmModuleShapeR
        )
        outputLabels
        outputLabels
        '[Low]
        '[Low]
globalGetSetSequence =
    GlobalGet SFZ -- get global at index 0
        :| I32Const IsLow 10
        :| I32Add
        :| GlobalSet SFZ -- set global at index 0
        :| GlobalGet SFZ -- get global at index 0 again
        :| End

-- globalGetSet ::
--     Function
--         '[]
--         '[I32 :~ Low]
--         '[]
--         '[]
--         ( (WasmModuleR (GlobalTypeMW Var (I32 :~ Low) ': '[]) '[]) ::
--             WasmModule WasmModuleShapeR
--         )
--         '[Low]
--         '[Low]
-- globalGetSet = Function (FFuncTypeAnn [] [I32 :~ Low]) globalGetSetSequence

-- Execution example for globalGetSetSequence
executeGlobalGetSetSequence ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ Low]
        '[]
        (WasmModuleR '[GlobalTypeMW Var (I32 :~ Low)] '[])
        '[]
executeGlobalGetSetSequence =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.ConsGlobals 5 SVar NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[]
                ( (WasmModuleR (GlobalTypeMW Var (I32 :~ Low) ': '[]) '[]) :: WasmModule WasmModuleShapeR
                )
                '[]
        )
        globalGetSetSequence

-- 2
globalSetConstSeq ::
    InstructionSequence
        '[I32 :~ Low, I32 :~ Low]
        '[I32 :~ Low]
        locals
        ( (WasmModuleR '[GlobalTypeMW Const (I32 :~ Low), GlobalTypeMW Var (I32 :~ Low)] '[]) ::
            WasmModule WasmModuleShapeR
        )
        outputLabels
        outputLabels
        '[Low]
        '[Low]
globalSetConstSeq =
    GlobalSet (SFS SFZ)
        -- :| GlobalSet SFZ      -- set global at index 0 should fail if uncommented because of wrong mutability
        :| End
executeGlobalSetConstSequence ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ Low]
        '[]
        ( (WasmModuleR '[GlobalTypeMW Const (I32 :~ Low), GlobalTypeMW Var (I32 :~ Low)] '[]) :: WasmModule WasmModuleShapeR
        )
        '[]
executeGlobalSetConstSequence =
    stepMany
        ( RuntimeContext
            { values = ConsValues 5 (ConsValues 10 NoValues)
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.ConsGlobals 0 SConst (WasmInterpreter.ConsGlobals 5 SVar NoGlobals)
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[I32 :~ Low, I32 :~ Low]
                '[]
                ( (WasmModuleR '[GlobalTypeMW Const (I32 :~ Low), GlobalTypeMW Var (I32 :~ Low)] '[]) :: WasmModule WasmModuleShapeR
                )
                '[]
        )
        globalSetConstSeq

{-
=============================================================================
BRANCH INSTRUCTION (8 Examples)
=============================================================================
-}

-- 1
-- example function for Br instruction
branchExampleSeq ::
    forall
        {shape :: WasmModuleShape}
        {locals :: LocalsShape}
        {wasmModule :: WasmModule WasmModuleShapeR}
        {inputStack :: ValStackShape}
        {outputLabels :: LabelStackShape}.
    InstructionSequence
        -- inputStack
        -- ('[] +>+: Reverse (Take (Length inputStack) (Reverse inputStack)))
        inputStack
        inputStack
        locals
        wasmModule
        '[]
        '[]
        '[Low]
        '[Low]
branchExampleSeq =
    Block
        (BTParamsResults KnownValVNil KnownValVNil)
        (Br SFZ
            :| End
        )
        :| End
-- branchExample ::
--     Function
--         '[]
--         '[]
--         '[I32 :~ Low]
--         '[]
--         ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
--         '[Low]
--         '[Low]
-- branchExample = Function (FFuncTypeAnn [] []) branchExampleSeq

executeBranchExample ::
    RuntimeContext @WasmModuleShapeR        
        '[]
        '[]
        (WasmModuleR '[] '[] :: WasmModule WasmModuleShapeR)
        '[]
executeBranchExample =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        branchExampleSeq

-- 2
-- example function for Br instruction
branchExample2Seq ::
    forall {shape :: WasmModuleShape} {wasmModule :: WasmModule WasmModuleShapeR}.
    InstructionSequence
        '[]
        '[]
        '[]
        wasmModule
        '[ 'LabelShape '[] Z]
        '[ 'LabelShape '[] Z]
        '[Low, Low]
        '[Low, Low]
branchExample2Seq =
    Block
        (BTParamsResults KnownValVNil KnownValVNil)
        ( Br SFZ
            :| End
        )
        :| Br SFZ
        :| End
-- branchExample2 ::
--     -- forall (s :: WasmModuleShape) (wm :: WasmModule s).
--     Function @WasmModuleShapeR '[] '[] '[] '[ 'LabelShape '[] Z] wm '[Low, Low] [Low, Low]
-- branchExample2 = Function (FFuncTypeAnn [] []) branchExample2Seq

-- this does not make sense for execution since we assume the first control frame and in execution we cannot drop it!
-- Additionally, when we enter a program we expect there to be no labels on top of the stack
-- executeBranchExample2 :: RuntimeContext @(WasmModuleShapeR Z Z) '[] '[] (WasmModuleR '[] '[]) '[]
-- In validation we do not remove the label therefore have to type it like this! The above without a label should be more correct
-- executeBranchExample2 :: RuntimeContext @(WasmModuleShapeR Z Z) '[] '[] (WasmModuleR '[] '[]) '[ 'LabelShape '[] Z]
-- executeBranchExample2 = stepMany (RuntimeContext {values = NoValues, locals = NoLocals, WasmInterpreter.globals = WasmInterpreter.NoGlobals, labels = ConsLabels (Label SZ SZ (SomeInstrSeq End) :: Label ('LabelShape '[] 'Z) ) NoLabels, memories = NoMems} :: RuntimeContext '[] '[] ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z)) '[ 'LabelShape '[] Z])
--                 branchExample2Seq

-- 3
branchExample3Seq ::
    forall
        {shape :: WasmModuleShape}
        {locals :: LocalsShape}
        {wasmModule :: WasmModule WasmModuleShapeR}
        {outputLabels :: LabelStackShape}.
    InstructionSequence
        '[I32 :~ Low, I64 :~ Low]
        '[I32 :~ Low, I32 :~ Low, I64:~ Low]
        locals
        wasmModule
        '[]
        '[]
        '[Low]
        '[Low] -- example function for Br instruction
branchExample3Seq =
    Block
        (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) KnownValVNil))
        ( Block
            (BTParamsResults KnownValVNil KnownValVNil)
            ( Br SFZ
                :| End
            )
            :| I32Const IsLow 42
            :| Br SFZ
            :| End
        )
        :| End
-- branchExample3 ::
--     -- forall (s :: WasmModuleShape) (wm :: WasmModule s).
--     Function @WasmModuleShapeR '[I32 :~ Low, I64 :~ Low] (I32 :~ Low ': '[I32 :~ Low, I64 :~ Low]) (I32 :~ Low ': '[]) '[] wm '[Low] '[Low]
-- branchExample3 =
--     Function
--         (FFuncTypeAnn [] [])
--         branchExample3Seq
executeBranchExample3 ::
    RuntimeContext @WasmModuleShapeR '[I32 :~ Low, I32 :~ Low, I64 :~ Low]
        '[]
        (WasmModuleR '[] '[])
        '[]
executeBranchExample3 =
    stepMany
        (RuntimeContext
            { values = ConsValues (3 :: Int32) (ConsValues (2 :: Int64) NoValues)
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } :: RuntimeContext '[I32 :~ Low, I64 :~ Low] '[] ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR) '[])
        branchExample3Seq

-- example function for Br instruction
-- 4
branchExample4Seq ::
    InstructionSequence '[] '[I32 :~ Low] locals wasmModule '[] '[] '[Low] '[Low]
branchExample4Seq =
    Block
        (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) KnownValVNil))
        ( Block
            (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) KnownValVNil))
            ( I32Const IsLow 42
                :| Br (SFS SFZ)
                :| I32Const IsLow 7 -- this unreachable
                :| End
            )
            :| End
        )
        :| End

-- branchExample4 ::
--     forall (s :: WasmModuleShape) (wm :: WasmModule s).
--     Function '[] (I32 :~ Low ': '[]) (I32 :~ Low ': '[]) '[] wm '[Low] '[Low]

-- branchExample4 = Function (FFuncTypeAnn [] []) branchExample4Seq

executeBranchExample4 ::
    RuntimeContext @WasmModuleShapeR '[I32 :~ Low] '[] (WasmModuleR '[] '[]) '[]
executeBranchExample4 =
    stepMany
        RuntimeContext
            { values = NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            }
        branchExample4Seq

-- 5
branchExample5Seq ::
    InstructionSequence '[] '[I32 :~ Low] locals wasmModule '[] '[] '[Low] '[Low]
branchExample5Seq =
    Block
        (BTParamsResults KnownValVNil ( KnownValCons (IsLow, ForI32) KnownValVNil))
        ( Block
            (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) KnownValVNil))
            ( I32Const IsLow 42
                :| I32Const IsLow 7
                :| I32Const IsLow 3
                :| I32Add
                :| Br (SFS SFZ)
                :| End
            )
            :| End
        )
        :| End


executeBranchExample5 ::
    RuntimeContext @WasmModuleShapeR '[I32 :~ Low] '[] (WasmModuleR '[] '[]) '[]
executeBranchExample5 =
    stepMany
        RuntimeContext
            { values = NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems            }
        branchExample5Seq

-- DOES NOT COMPILE AND SHOULD NOT COMPILE!!
-- (SEE block-simple-br2-nested.wat)
-- branchExampleNestedSeq ::
--     InstructionSequence '[] '[I32 :~ Low, I32 :~ Low] locals wasmModule '[] '[] '[Low] '[Low]
-- branchExampleNestedSeq =
--     Block
--         (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) (KnownValCons (IsLow, ForI32) KnownValVNil)))
--         ( I32Const IsLow 42
--             :| I32Const IsLow 7
--             :| Block
--                 (BTParamsResults (KnownValCons (IsLow, ForI32) KnownValVNil) (KnownValCons (IsLow, ForI32) KnownValVNil))
--                 ( 
--                     I32Const IsLow 3
--                     :| I32Add
--                     :| Br (SFS SFZ)
--                     :| End
--                 )
--             :| End
--         )
--         :| End
-- executeBranchExampleNested ::
--     RuntimeContext '[I32 :~ Low, I32 :~ Low] '[] (WasmModuleR '[] '[]) '[]
-- executeBranchExampleNested =
--     stepMany
--         RuntimeContext
--             { values = NoValues
--             , locals = NoLocals
--             , WasmInterpreter.globals = WasmInterpreter.NoGlobals
--             , labels = NoLabels
--             , memories = NoMems
--             }
--         branchExampleNestedSeq

-- 6
branchThesisSeq ::
    InstructionSequence '[] '[I64 :~ Low, I32 :~ Low] locals wasmModule '[] '[] '[Low] '[Low]
branchThesisSeq =
    Block
        (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI64) (KnownValCons (IsLow, ForI32) KnownValVNil)))
        ( I32Const IsLow 10
             :| Block -- here we have problem that we expect 1 i32 on top at the end of the block but we have two
                (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI64) KnownValVNil))
                ( 
                    I32Const IsLow 20
                    :| I64Const IsLow 30
                    :| Br (SFS SFZ)
                    :| End -- here we expect that we have one i32 as defined in innerblock but we in fact have two i32
                            -- hence the first thing saing the we cannot match [I32] (which is the second one) with the empty list => so the firest i32 has already been matched
                )
            :| End
        )
        :| End

executeBranchThesisSeq ::
    RuntimeContext @WasmModuleShapeR '[I64 :~ Low, I32 :~ Low] '[] (WasmModuleR '[] '[]) '[]
executeBranchThesisSeq =
    stepMany
        (RuntimeContext            
            { values = NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } :: RuntimeContext
                '[]
                '[] ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR) '[]
        )
        branchThesisSeq


{-
(module
  (func $block-simple (result i32 i32)
    (block (result i32 i32)               ;; depth 2
      (i32.const 20)      
      (block (result i32)
          i32.const 6                 ;; depth 1
          (block (result i32)             ;; depth 0 (innermost)
                i32.const 4
                br 1                      ;; jump out of two enclosing blocks
                ;; unreachable
          )
          i32.add
          ;; skipped
      )
      ;; execution continues here after end of block with depth 1
      )
  )
)
-}
-- 7
branchThesisSeq2 ::
    InstructionSequence '[] '[I32 :~ Low, I32 :~ Low] locals wasmModule '[] '[] '[Low] '[Low]
branchThesisSeq2 = 
    Block
        (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) (KnownValCons (IsLow, ForI32) KnownValVNil)))
        ( I32Const IsLow 20
             :| Block
                (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) KnownValVNil))
                ( 
                    I32Const IsLow 6
                     :| Block
                        (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) KnownValVNil))
                        (
                            I32Const IsLow 4
                            :| Br (SFS SFZ)
                            :| End
                        )
                    :| I32Add
                    :| End
                )
            :| End
        )
        :| End
executeBranchThesisSeq2 ::
    RuntimeContext @WasmModuleShapeR '[I32 :~ Low, I32 :~ Low] '[] (WasmModuleR '[] '[]) '[]
executeBranchThesisSeq2 =
    stepMany
        (RuntimeContext            
        { values = NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } :: RuntimeContext
                '[]
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        branchThesisSeq2

-- 8
branchRandomAfterSequence ::
    InstructionSequence '[] '[I32 :~ High, I32 :~ Low] locals wasmModule '[] '[] '[Low] '[Low]
branchRandomAfterSequence = 
    Block
        (BTParamsResults KnownValVNil (KnownValCons (IsHigh, ForI32) (KnownValCons (IsLow, ForI32) KnownValVNil)))
        ( 
            I32Const IsLow 20
            :| I32Const IsHigh 10
            :| Br SFZ
            -- :| I32Add -- this does not work in IFC since we cannot definitely know what the output sec level is and therefore we have a problem also with what is expected from the next instr
            :| End
        )
    -- :| I32Add
    :| End
executeRandomAfterSequence ::
    RuntimeContext @WasmModuleShapeR '[I32 :~ High, I32 :~ Low] '[] (WasmModuleR '[] '[]) '[]
executeRandomAfterSequence =
    stepMany
        RuntimeContext
            { values = NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            }
        branchRandomAfterSequence

-- -- Does not compile and also SHOULD NOT compile
-- branchSimpleSeq :: 
--     InstructionSequence '[] '[I32 :~ Low, I32 :~ Low] locals wasmModule '[] '[] '[Low] '[Low]
-- branchSimpleSeq =
--     Block
--         (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) (KnownValCons (IsLow, ForI32) KnownValVNil)))
--         ( I32Const IsLow 10
--             :| Block
--                 (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) KnownValVNil))
--                 ( 
--                     I32Const IsLow 20
--                     :| Br (SFS SFZ)                    
--                     :| End
--                 )
--                 :| End
--         )
--         :| End

{-
=============================================================================
IF INSTRUCTION (8 Examples)
=============================================================================
-}

-- 1
ifCondSeq ::
    InstructionSequence
        '[I32 :~ High]
        '[I32 :~ High]
        '[]
        ( (WasmModuleR '[] '[]) ::
            WasmModule WasmModuleShapeR
        )
        outputLabels
        outputLabels
        '[Low]
        '[Low]
ifCondSeq =
    If
        (BTParamsResults KnownValVNil (KnownValCons (IsHigh, ForI32) KnownValVNil))
        ( I32Const IsLow 42
            :| I32Const IsLow 7
            :| I32Add
            :| End
        )
        ( I32Const IsLow 7
            :| I32Const IsLow 3
            :| I32Sub
            :| End
        )
        :| End
executeIfCond ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ High]
        '[]
        (WasmModuleR '[] '[])
        '[]
executeIfCond =
    stepMany
        ( RuntimeContext
            { values = ConsValues (0 :: Int32) NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[I32 :~ High]
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        ifCondSeq

-- 2
ifCondSeq2 ::
    InstructionSequence
        '[I32 :~ Low]
        '[I32 :~ Low]
        '[]
        ( (WasmModuleR '[] '[]) ::
            WasmModule WasmModuleShapeR
        )
        outputLabels
        outputLabels
        '[Low]
        '[Low]
ifCondSeq2 =
    If
        (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) KnownValVNil))
        ( I32Const IsLow 42
            :| I32Const IsLow 7
            :| I32Add
            :| End
        )
        ( I32Const IsLow 7
            :| I32Const IsLow 3
            :| I32Sub
            :| End
        )
        :| End
executeIfCond2 ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ Low]
        '[]
        (WasmModuleR '[] '[])
        '[]
executeIfCond2 =
    stepMany
        ( RuntimeContext
            { values = ConsValues (1 :: Int32) NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[I32 :~ Low]
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        ifCondSeq2

-- 3
ifCondSeqParentHigh ::
    InstructionSequence
        '[I32 :~ Low]
        '[I32 :~ High]
        '[]
        ( (WasmModuleR '[] '[]) ::
            WasmModule WasmModuleShapeR
        )
        outputLabels
        outputLabels
        '[High]
        '[High]
ifCondSeqParentHigh =
    If
        (BTParamsResults KnownValVNil (KnownValCons (IsHigh, ForI32) KnownValVNil))
        ( I32Const IsLow 42
            :| I32Const IsLow 7
            :| I32Add
            :| End
        )
        ( I32Const IsLow 7
            :| I32Const IsLow 3
            :| I32Sub
            :| End
        )
        :| End
executeifCondSeqParentHigh ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ High]
        '[]
        (WasmModuleR '[] '[])
        '[]
executeifCondSeqParentHigh =
    stepMany
        ( RuntimeContext
            { values = ConsValues (1 :: Int32) NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[I32 :~ Low]
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        ifCondSeqParentHigh

 -- 4
ifCondSeq3 ::
    InstructionSequence
        '[I32 :~ Low]
        '[I32 :~ High]
        '[]
        ( (WasmModuleR '[] '[]) ::
            WasmModule WasmModuleShapeR
        )
        outputLabels
        outputLabels
        '[Low]
        '[Low]
ifCondSeq3 =
    If
        (BTParamsResults KnownValVNil (KnownValCons (IsHigh, ForI32) KnownValVNil))
        ( I32Const IsHigh 42
            :| I32Const IsLow 7
            :| I32Add
            :| End
        )
        ( I32Const IsLow 7
            :| I32Const IsLow 3
            :| I32Sub
            :| End
        )
        :| End

executeIfCond3 ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ High]
        '[]
        (WasmModuleR '[] '[])
        '[]
executeIfCond3 =
    stepMany
        ( RuntimeContext
            { values = ConsValues (1 :: Int32) NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[I32 :~ Low]
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        ifCondSeq3
 -- 5
ifCondSeqGetLocalLow ::
    InstructionSequence
        '[I32 :~ High]
        '[I32 :~ High]
        '[I32 :~ Low]
        ( (WasmModuleR '[] '[]) ::
            WasmModule WasmModuleShapeR
        )
        outputLabels
        outputLabels
        '[Low]
        '[Low]
ifCondSeqGetLocalLow =
    If
        (BTParamsResults KnownValVNil (KnownValCons (IsHigh, ForI32) KnownValVNil))
        ( I32Const IsLow 42
            :| LocalGet SFZ
            :| I32Add
            :| End
        )
        ( I32Const IsLow 7
            :| I32Const IsLow 3
            :| I32Sub
            :| End
        )
        :| End
executeIfCondGetLocalLow ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ High]
        '[I32 :~ Low]
        (WasmModuleR '[] '[])
        '[]
executeIfCondGetLocalLow =
    stepMany
        ( RuntimeContext
            { values = ConsValues (1 :: Int32) NoValues
            , locals = ConsLocals (5 :: Int32) NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[I32 :~ High]
                '[I32 :~ Low]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        ifCondSeqGetLocalLow

-- 6
ifCondSeqGetLocalHigh ::
    InstructionSequence
        '[I32 :~ Low]
        '[I32 :~ High]
        '[I32 :~ High]
        ( (WasmModuleR '[] '[]) ::
            WasmModule WasmModuleShapeR
        )
        outputLabels
        outputLabels
        '[Low]
        '[Low]
ifCondSeqGetLocalHigh =
    If
        (BTParamsResults KnownValVNil (KnownValCons (IsHigh, ForI32) KnownValVNil))
        ( I32Const IsLow 42
            :| LocalGet SFZ
            :| I32Add
            :| End
        )
        ( I32Const IsLow 7
            :| I32Const IsLow 3
            :| I32Sub
            :| End
        )
        :| End
executeIfCondGetLocalHigh ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ High]
        '[I32 :~ High]
        (WasmModuleR '[] '[])
        '[]
executeIfCondGetLocalHigh =
    stepMany
        ( RuntimeContext
            { values = ConsValues (1 :: Int32) NoValues
            , locals = ConsLocals (5 :: Int32) NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[I32 :~ Low]
                '[I32 :~ High]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        ifCondSeqGetLocalHigh

-- 7
ifCondSeqSetLocalLow ::
    InstructionSequence
        '[I32 :~ Low]
        '[I32 :~ High]
        '[I32 :~ High]
        ( (WasmModuleR '[] '[]) ::
            WasmModule WasmModuleShapeR
        )
        outputLabels
        outputLabels
        '[Low]
        '[Low]
ifCondSeqSetLocalLow =
    If
        (BTParamsResults KnownValVNil (KnownValCons (IsHigh, ForI32) KnownValVNil))
        ( I32Const IsLow 42
            :| I32Const IsHigh 1
            :| I32Add
            :| LocalTee SFZ
            :| End
        )
        ( I32Const IsLow 7
            :| I32Const IsLow 3
            :| I32Sub
            :| End
        )
        :| End
executeIfCondSetLocalLow ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ High]
        '[I32 :~ High]
        (WasmModuleR '[] '[])
        '[]
executeIfCondSetLocalLow =
    stepMany
        ( RuntimeContext
            { values = ConsValues (1 :: Int32) NoValues
            , locals = ConsLocals (5 :: Int32) NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[I32 :~ Low]
                '[I32 :~ High]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        ifCondSeqSetLocalLow


-- 8
ifSeq :: 
    InstructionSequence '[] '[] '[I32 :~ High] wasmModule '[] '[] '[Low] '[Low]
ifSeq =
    Block
        (BTParamsResults KnownValVNil KnownValVNil)
        ( I32Const IsLow 0
            :| If 
                (BTParamsResults KnownValVNil (KnownValCons (IsHigh, ForI32) KnownValVNil))
                ( I32Const IsLow 2
                    :| I32Const IsLow 2
                    :| I32Add
                    :| End
                )
                ( I32Const IsHigh 1
                    :| I32Const IsLow 1
                    :| I32Add
                    :| End
                )
            :| LocalSet SFZ
            :| End
            )
        :| End

executeIfSeq ::
    RuntimeContext @WasmModuleShapeR
        '[]
        '[I32 :~ High]
        (WasmModuleR '[] '[])
        '[]
executeIfSeq =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals 1 NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[I32 :~ High]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        ifSeq



{-
=============================================================================
LOOP INSTRUCTION (3 Examples)
=============================================================================
-}

-- 1
loopSeq ::
    InstructionSequence
        '[]
        '[]
        '[I32 :~ Low]
        ( (WasmModuleR '[] '[]) ::
            WasmModule WasmModuleShapeR
        )
        '[]
        '[]
        '[Low]
        '[Low]
loopSeq =
    Block
        (BTParamsResults KnownValVNil  KnownValVNil)
        (
            Loop @Low
                (BTParamsResults KnownValVNil KnownValVNil)
                ( LocalGet SFZ
                    :| I32Const IsLow 7
                    :| I32Add
                    :| LocalTee SFZ  
                    :| I32Const IsLow 50 
                    :| I32LeS    
                    :| BrIf SFZ             
                    :| End
                )
                :| End
        )
        :| End
executeLoopSeq ::
    RuntimeContext @WasmModuleShapeR
        '[]
        '[I32 :~ Low]
        (WasmModuleR '[] '[])
        '[]
executeLoopSeq =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals 49 NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext                
                '[]
                '[I32 :~ Low]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        loopSeq


-- 2
loopSeqBrif ::
    InstructionSequence
        '[]
        '[]
        '[]
        ( (WasmModuleR '[] '[]) ::
            WasmModule WasmModuleShapeR
        )
        '[]
        '[]
        '[Low]
        '[Low]
loopSeqBrif =
    Block
        (BTParamsResults KnownValVNil KnownValVNil) -- (KnownValCons (IsLow, ForI32) KnownValVNil))
        (
            Loop @High
                (BTParamsResults KnownValVNil KnownValVNil) -- (KnownValCons (IsLow, ForI32) KnownValVNil))
                ( I32Const IsLow 42
                    :| I32Const IsLow 7
                    :| I32Add
                    :| I32Const IsHigh 50
                    :| I32GeS
                    :| BrIf SFZ                  
                    :| End
                )
                :| End
        )
        :| End
executeLoopSeqBrif ::
    RuntimeContext @WasmModuleShapeR
        '[]
        '[]
        (WasmModuleR '[] '[])
        '[]
executeLoopSeqBrif =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        loopSeqBrif


-- 3
loopSeqBrifSecWasm ::
    InstructionSequence
        '[]
        '[I32 :~ Low, I32 :~ High]
        '[]
        ( (WasmModuleR '[] '[]) ::
            WasmModule WasmModuleShapeR
        )
        '[]
        '[]
        '[Low]
        '[Low]
loopSeqBrifSecWasm =
    Block 
        (BTParamsResults KnownValVNil (KnownValCons (IsHigh, ForI32) KnownValVNil)) -- (KnownValCons (IsLow, ForI32) KnownValVNil))
        ( Block
            (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) KnownValVNil)) -- (KnownValCons (IsLow, ForI32) KnownValVNil))
            ( I32Const IsLow 0
                :| I32Const IsHigh 1
                :| BrIf (SFS SFZ)
                :| End
            )
            :| Drop
            :| I32Const IsHigh 0
            :| End 
        )
        :| I32Const IsLow 42
        :| End
executeLoopSeqBrifSecWasm ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ Low, I32 :~ High]
        '[]
        (WasmModuleR '[] '[])
        '[]
executeLoopSeqBrifSecWasm =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        loopSeqBrifSecWasm
            

{-
=============================================================================
BR_IF INSTRUCTION (2 Examples)
=============================================================================
-}

-- 1
brIfSeq ::
    InstructionSequence
        '[]
        '[I32 :~ Low]
        '[]
        ( (WasmModuleR '[] '[]) ::
            WasmModule WasmModuleShapeR
        )
        '[]
        '[]
        '[Low]
        '[Low]
brIfSeq =
    Block
        (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) KnownValVNil))
        ( I32Const IsLow 42
            :| I32Const IsLow 7
            :| I32Add
            :| I32Const IsLow 1
            :| BrIf SFZ
            :| I32Const IsLow 0
            :| I32Add
            :| End
        )
        :| End
executeBrIf :: 
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ Low]
        '[]
        (WasmModuleR '[] '[])
        '[]
executeBrIf =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        brIfSeq

-- 2
brIfSeqHigh ::
    InstructionSequence
        '[]
        '[I32 :~ High]
        '[]
        ( (WasmModuleR '[] '[]) ::
            WasmModule WasmModuleShapeR
        )
        '[]
        '[]
        '[Low]
        '[Low]
brIfSeqHigh =
    Block
        (BTParamsResults KnownValVNil (KnownValCons (IsHigh, ForI32) KnownValVNil))
        ( I32Const IsLow 42
            :| I32Const IsLow 7
            :| I32Add
            :| I32Const IsHigh 1
            :| BrIf SFZ
            :| I32Const IsLow 10
            :| I32Add
            :| End :: InstructionSequence '[] '[I32 :~ High] '[] (WasmModuleR '[] '[]) '[ 'LabelShape '[I32 :~ High] Z] '[ 'LabelShape '[I32 :~ High] Z] '[Low, Low] '[High, Low]
        )
        :| End
executeBrIfSeqHigh ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ High]
        '[]
        (WasmModuleR '[] '[])
        '[]
executeBrIfSeqHigh =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        brIfSeqHigh

-- shouldn't compile so this is good
-- localSetSeq ::
--     InstructionSequence '[] '[] '[I32 :~ Low] (WasmModuleR '[] '[]) '[]
--         '[]
--         '[High]
--         '[High]
-- localSetSeq =
--     I32Const IsLow 42
--         :| LocalSet SFZ
--         :| End


{-
=============================================================================
BR AND BR_IF INSTRUCTION TO ILLUSTRATE BR RUL OF SECWASM (3 Examples)
=============================================================================
-}

-- 1
brAndBrIfSeq ::
    InstructionSequence '[] '[I32 :~ High] '[] wasmModule '[] '[] '[Low] '[Low]
brAndBrIfSeq =
    Block
        (BTParamsResults KnownValVNil (KnownValCons (IsHigh, ForI32) KnownValVNil))
        ( 
        Block 
            (BTParamsResults KnownValVNil (KnownValCons (IsHigh, ForI32) KnownValVNil))
            ( I32Const IsHigh 42
                :| I32Const IsHigh 1
                :| BrIf SFZ
                :| Drop
                :| I32Const IsHigh 2
                :| Br (SFS SFZ)
                :| End
            )
            :| Drop
            :| I32Const IsHigh 7
            :| End
        )
        :| End
executeBrIfSeq ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ High]
        '[]
        (WasmModuleR '[] '[])
        '[]
executeBrIfSeq =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        brAndBrIfSeq

-- 2
brAndBrIfSeq2 ::
    InstructionSequence '[] '[] '[I32 :~ High] wasmModule '[] '[] '[Low] '[Low]
brAndBrIfSeq2 =
    Block
        (BTParamsResults KnownValVNil KnownValVNil)
        ( 
        Block 
            (BTParamsResults KnownValVNil KnownValVNil)
            ( I32Const IsHigh 1
                :| BrIf SFZ
                :| Br (SFS SFZ)
                :| End
            )
            :| I32Const IsLow 7
            :| LocalSet SFZ -- this only fails here with option two => also I think it should fail
            :| End
        )
        :| End
executeBrAndBrIfSeq2 ::
    RuntimeContext @WasmModuleShapeR
        '[]
        '[I32 :~ High]
        (WasmModuleR '[] '[])
        '[]
executeBrAndBrIfSeq2 =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals 1 NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext           
                '[]
                '[I32 :~ High]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        brAndBrIfSeq2

-- 3
brAndIfSeq :: 
    InstructionSequence '[] '[] '[I32 :~ High] wasmModule '[] '[] '[Low] '[Low]
brAndIfSeq =
    Block
        (BTParamsResults KnownValVNil KnownValVNil)
        ( I32Const IsHigh 0
            :| If 
                (BTParamsResults KnownValVNil KnownValVNil)
                ( Br (SFS SFZ)
                    :| End :: InstructionSequence '[] '[] '[I32 :~ High] wasmModule '[ 'LabelShape '[] 'Z ,'LabelShape '[] 'Z ] '[ 'LabelShape '[] 'Z ,'LabelShape '[] 'Z ] '[High, Low, Low] '[High, High, Low]
                )
                ( Br SFZ
                    :| End :: InstructionSequence '[] '[] '[I32 :~ High] wasmModule '[ 'LabelShape '[] 'Z ,'LabelShape '[] 'Z ] '[ 'LabelShape '[] 'Z ,'LabelShape '[] 'Z ] '[High, Low, Low] '[High, Low, Low]
                ) -- :: Instruction '[I32 :~ High] '[] '[I32 :~ Low] wasmModule '[ 'LabelShape '[] 'Z ] '[ 'LabelShape '[] 'Z ] '[Low, Low] '[High, Low])
            :| I32Const IsLow 7
            :| LocalSet SFZ -- this only fails here with option two => also I think it should fail
            :| End
            )
        :| End
executeBrAndIfSeq ::
    RuntimeContext @WasmModuleShapeR
        '[]
        '[I32 :~ High]
        (WasmModuleR '[] '[])
        '[]
executeBrAndIfSeq =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals 1 NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[I32 :~ High]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        brAndIfSeq


{-
=============================================================================
FACTORIAL FUNCTION (1 Example)
=============================================================================
-}

{- | Example 2: Factorial function using iteration
Takes one i32 parameter, returns its factorial
-}
factorialSeq ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s) (outputLabels :: LabelStackShape).
    InstructionSequence
        '[]
        (I32 :~ Low ': '[])
        (I32 :~ Low ': I32 :~ Low ': '[])
        wm
        '[]
        '[]
        '[Low]
        '[Low]
factorialSeq =
    -- Local slots: (0) input parameter (also used as counter), (1) accumulator
    -- Initialize accumulator to 1
    I32Const IsLow 1 -- Can be Low but when we get it from locals will be High since the slot is high
        :| LocalSet (SFS SFZ)
        -- :| I32Const 0
        -- Main computation block
        :| Block
            (BTParamsResults KnownValVNil KnownValVNil)
            ( -- Check if n <= 1 (base case)
              I32Const IsLow 1
                :| LocalGet SFZ
                :| I32LeS
                :| BrIf SFZ -- Exit block if n <= 1
                -- Iterative loop for factorial computation
                :| Loop @Low
                    (BTParamsResults KnownValVNil KnownValVNil)
                    ( -- accumulator *= n
                      LocalGet (SFS SFZ)
                        :| LocalGet SFZ
                        :| I32Mul
                        :| LocalSet (SFS SFZ)
                        -- n -= 1
                        :| LocalGet SFZ
                        :| I32Const IsLow 1
                        :| I32Sub
                        :| LocalSet SFZ
                        -- Continue if n > 1
                        :| I32Const IsLow 1
                        :| LocalGet SFZ
                        :| I32GtS
                        :| BrIf SFZ -- Branch back to loop start
                        :| End
                    )
                :| End
            )
        -- Return the accumulated result
        :| LocalGet (SFS SFZ)
        :| End

-- factorial ::
--     forall (s :: WasmModuleShape) (wm :: WasmModule s).
--     Function '[] (I32 :~ Low ': '[]) (I32 :~ Low ': I32 :~ Low ': '[]) '[] wm '[Low] '[Low]
-- factorial =
--     Function
--         (FFuncTypeAnn [] [I32 :~ Low])
--         factorialSeq
executeFactorial :: Int32 ->
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ Low]
        '[I32 :~ Low, I32 :~ Low]
        (WasmModuleR '[] '[])
        '[]
-- we put as input 4 so the expected result is 24
executeFactorial n =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals n (ConsLocals 0 NoLocals)
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[I32 :~ Low, I32 :~ Low]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        factorialSeq

{-
=============================================================================
RANDOM EXAMPLES (3 Examples)
=============================================================================
-}
 -- 1
{- | Example 3: Function that returns nothing (void function).
Demonstrates different return types - this one returns Empty stack.
-}
printNumberSeq ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s) (outputLabels :: LabelStackShape).
    InstructionSequence '[] '[I32 :~ Low] '[I32 :~ Low, I32 :~ Low] wm outputLabels outputLabels '[Low] '[Low]
printNumberSeq =
    -- Just consume the parameter without returning anything
    LocalGet SFZ
        :| LocalGet (SFS SFZ)
        :| I32Add -- just to do something with the parameters
        :| End

-- This cannot be executed for now.
-- printNumber ::
--     forall (s :: WasmModuleShape) (wm :: WasmModule s).
--     Function '[] '[I32 :~ Low] '[I32 :~ Low, I32 :~ Low] '[] wm '[Low] '[Low]
-- printNumber =
--     Function
--         (FFuncTypeAnn [I32 :~ Low, I32 :~ Low] [I32 :~ Low])
--         printNumberSeq


executePrintNumber ::
    RuntimeContext @WasmModuleShapeR '[I32 :~ Low] '[I32 :~ Low, I32 :~ Low] (WasmModuleR '[] '[]) '[]
executePrintNumber =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals 7 (ConsLocals 42 NoLocals)
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[I32 :~ Low, I32 :~ Low]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        printNumberSeq
 -- 2
{- | Example 4: Function with more complex local variable patterns.
Takes one parameter, uses three local variables for intermediate calculations.
-}
complexCalculationSeq ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s) (outputLabels :: LabelStackShape).
    InstructionSequence
        '[]
        '[I32 :~ Low]
        (I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': '[])
        wm
        outputLabels
        outputLabels
        '[Low]
        '[Low]
complexCalculationSeq =
    -- Local slots: (0) input, (1) temp1, (2) temp2, (3) result
    -- temp1 = input * 2
    LocalGet SFZ
        :| I32Const IsLow 2
        :| I32Mul
        :| LocalSet (SFS SFZ)
        -- temp2 = input + 10
        :| LocalGet SFZ
        :| I32Const IsLow 10
        :| I32Add
        :| LocalSet (SFS (SFS SFZ))
        -- result = temp1 + temp2
        :| LocalGet (SFS SFZ)
        :| LocalGet (SFS (SFS SFZ))
        :| I32Add
        :| LocalSet (SFS (SFS (SFS SFZ)))
        :| LocalGet (SFS (SFS (SFS SFZ))) -- return result on top of stack
        :| End

-- complexCalculation ::
--     forall (s :: WasmModuleShape) (wm :: WasmModule s).
--     Function '[] '[I32 :~ Low] (I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': '[]) '[] wm '[Low] '[Low]
-- complexCalculation =
--     Function
--         (FFuncTypeAnn [] [I32 :~ Low])
--         complexCalculationSeq

executeComplexCalculation ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ Low]
        (I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': '[])
        (WasmModuleR '[] '[])
        '[]
executeComplexCalculation =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals 5 (ConsLocals 0 (ConsLocals 0 (ConsLocals 0 NoLocals)))
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                (I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': '[])
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        complexCalculationSeq

-- 3
{- | Example 5: Conditional logic with If instruction.
Returns the absolute value of the input.
-}
absoluteValueSeq ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s) (outputLabels :: LabelStackShape).
    InstructionSequence '[] (I32 :~ Low ': '[]) (I32 :~ Low ': '[]) wm outputLabels outputLabels '[Low] '[Low]
absoluteValueSeq =
    -- Check if input is negative
    LocalGet SFZ
        :| I32Const IsLow 0
        :| I32LtS -- Is input < 0?
        :| If
            (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) KnownValVNil))
            -- Then branch: negate the number (0 - input)
            ( I32Const IsLow 0
                :| LocalGet SFZ
                :| I32Sub
                :| End
            )
            -- Else branch: return input as-is
            ( LocalGet SFZ
                :| End
            )
        :| End

-- absoluteValue ::
--     forall (s :: WasmModuleShape) (wm :: WasmModule s).
--     Function '[] (I32 :~ Low ': '[]) (I32 :~ Low ': '[]) '[] wm '[Low] '[Low]
-- absoluteValue =
--     Function
--         (FFuncTypeAnn [] [I32 :~ Low])
--         absoluteValueSeq
executeAbsoluteValue ::
    RuntimeContext @WasmModuleShapeR '[I32 :~ Low] '[I32 :~ Low] (WasmModuleR '[] '[]) '[]
executeAbsoluteValue =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals (-42) NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[I32 :~ Low]
                (WasmModuleR '[] '[] :: WasmModule WasmModuleShapeR)
                '[]
        )
        absoluteValueSeq

-- Bad example (fails at compile time)
-- nestedControlFlow :: Function (I32 :> Empty) (I32 ': I32 ': '[])
-- nestedControlFlow = Function $
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







{- Attempts at benchmarking -}

{- | Fibonacci function using iteration.
Local slots: (0) n (counter), (1) a = fib(i-1), (2) b = fib(i)
Init: a = 0, b = 1. Loop runs until n <= 1, then returns b.
fib(10) = 55
-}
fibSeq ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s) (outputLabels :: LabelStackShape).
    InstructionSequence
        '[]
        (I32 :~ Low ': '[])
        (I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': '[])
        wm
        '[]
        '[]
        '[Low]
        '[Low]
fibSeq =
    -- Local slots: (0) n, (1) a = 0, (2) b = 1
    I32Const IsLow 0
        :| LocalSet (SFS SFZ)           -- local[1] = a = 0
        :| I32Const IsLow 1
        :| LocalSet (SFS (SFS SFZ))     -- local[2] = b = 1
        -- Outer block for base-case early exit
        :| Block
            (BTParamsResults KnownValVNil KnownValVNil)
            ( LocalGet SFZ
                :| I32Const IsLow 1
                :| I32LeS               -- n <= 1?
                :| BrIf SFZ             -- skip loop entirely if n <= 1
                :| Loop @Low
                    (BTParamsResults KnownValVNil KnownValVNil)
                    ( -- Stack shuffle: need old b for both new a and the addition
                      -- Push b (becomes new a), then a, then b (for add)
                      LocalGet (SFS (SFS SFZ))     -- push b  (saved as new a)
                        :| LocalGet (SFS SFZ)       -- push a
                        :| LocalGet (SFS (SFS SFZ)) -- push b  (for a + b)
                        :| I32Add                   -- a + b; stack: [a+b, old_b]
                        :| LocalSet (SFS (SFS SFZ)) -- local[2] = b = a + b
                        :| LocalSet (SFS SFZ)       -- local[1] = a = old_b
                        -- Decrement n and store
                        :| LocalGet SFZ
                        :| I32Const IsLow 1
                        :| I32Sub
                        :| LocalTee SFZ             -- local[0] = n - 1, keep on stack
                        -- Continue loop if n > 1
                        :| I32Const IsLow 1
                        :| I32GtS                   -- (n-1) > 1?
                        :| BrIf SFZ                 -- branch back to loop start
                        :| End
                    )
                :| End
            )
        -- Return b
        :| LocalGet (SFS (SFS SFZ))
        :| End

-- fib ::
--     forall (s :: WasmModuleShape) (wm :: WasmModule s).
--     Function '[] (I32 :~ Low ': '[]) (I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': '[]) '[] wm '[Low] '[Low]
-- fib =
--     Function
--         (FFuncTypeAnn [] [I32 :~ Low])
--         fibSeq

executeFib ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ Low]
        '[I32 :~ Low, I32 :~ Low, I32 :~ Low]
        (WasmModuleR '[] '[])
        '[]
-- local[0] = 10, expected result: fib(10) = 55
executeFib =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals 10 (ConsLocals 0 (ConsLocals 0 NoLocals))
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[I32 :~ Low, I32 :~ Low, I32 :~ Low]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        fibSeq

-- Should return fib(2) = 1
executeFib2 ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ Low]
        '[I32 :~ Low, I32 :~ Low, I32 :~ Low]
        (WasmModuleR '[] '[])
        '[]
executeFib2 =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals 2 (ConsLocals 0 (ConsLocals 0 NoLocals))
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[I32 :~ Low, I32 :~ Low, I32 :~ Low]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        fibSeq

-- Should return fib(3) = 2
executeFib3 ::
    RuntimeContext @WasmModuleShapeR
        '[I32 :~ Low]
        '[I32 :~ Low, I32 :~ Low, I32 :~ Low]
        (WasmModuleR '[] '[])
        '[]
executeFib3 =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals 3 (ConsLocals 0 (ConsLocals 0 NoLocals))
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[I32 :~ Low, I32 :~ Low, I32 :~ Low]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        fibSeq