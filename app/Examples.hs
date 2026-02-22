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
EXECUTION EXAMPLES
=============================================================================
-}
-- data RuntimeContext (valuesShape :: ValStackShape) (localsShape :: LocalsShape) (wasmModule :: WasmModule shape) (labelsShape :: LabelStackShape) = RuntimeContext
--     { values :: ValueStack valuesShape,
--       locals :: Locals localsShape,
--       globals :: Globals (GetGlobals wasmModule),
--       labels :: LabelStack labelsShape,
--       memories :: Memory (GetMems wasmModule)
--       -- TODO: tables, etc.
--     }
executeAddStep :: RuntimeContext @WasmModuleShapeR '[I32] '[] (WasmModuleR '[] '[]) '[]
executeAddStep =
    stepMany
        ( RuntimeContext
            { values = ConsValues 5 (ConsValues 10 NoValues)
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext (I32 ': I32 ': '[]) '[] (WasmModuleR '[] '[]) '[]
        )
        (I32Add :| End)

executeAddMany ::
    RuntimeContext @WasmModuleShapeR '[I32] '[] (WasmModuleR '[] '[] :: WasmModule WasmModuleShapeR) '[]
executeAddMany =
    stepMany
        ( RuntimeContext
            { values = ConsValues 10 (ConsValues 5 (ConsValues 10 NoValues))
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                (I32 ': I32 ': I32 ': '[])
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        (I32Div :| I32Add :| End)

executeDivMany ::
    RuntimeContext @WasmModuleShapeR '[I32] '[] (WasmModuleR '[] '[] :: WasmModule WasmModuleShapeR) '[]
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
                (I32 ': I32 ': '[])
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
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

memLoadSequence ::
    InstructionSequence
        '[]
        '[I32]
        '[I64, I64]
        ( ( WasmModuleR
                '[]
                ( currMem
                    -- '[ fromIntegral 10 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 20::Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8]
                    ': '[]
                )
          ) ::
            WasmModule WasmModuleShapeR
        )
        '[]
        '[]
memLoadSequence =
    LocalGet SFZ
        :| MemoryLoad @I32 SFZ (SMemArg 0 0)
        :| LocalGet (SFS SFZ)
        :| MemoryLoad @I32 SFZ (SMemArg 0 0)
        :| I32Add
        :| End

memLoad ::
    Function
        '[]
        (I32 ': '[])
        (I64 ': I64 ': '[])
        '[]
        ( ( WasmModuleR
                '[]
                ( currMem
                    -- '[ fromIntegral 10 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 20::Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8]
                    ': '[]
                )
          ) ::
            WasmModule WasmModuleShapeR
        )
memLoad =
    Function
        (FFuncTypeAnn [] [I32])
        memLoadSequence

executeMemLoad ::
    RuntimeContext @WasmModuleShapeR
        '[I32]
        '[I64, I64]
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
                '[I64, I64]
                ( ( WasmModuleR
                        '[]
                        ( currMem
                            -- '[ fromIntegral 10 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 20::Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8]
                            ': '[]
                        )
                  ) :: WasmModule WasmModuleShapeR
                )
                '[]
        )
        memLoadSequence

memLoadSequence1 ::
    InstructionSequence
        '[]
        '[I32, I32]
        '[I64, I64]
        ( ( WasmModuleR
                '[]
                ( currMem ': '[] )
          ) ::
            WasmModule WasmModuleShapeR
        )
        '[]
        '[]
memLoadSequence1 =
    LocalGet SFZ
        :| MemoryLoad @I32 SFZ (SMemArg 0 0)
        :| LocalGet (SFS SFZ)
        :| MemoryLoad @I32 SFZ (SMemArg 0 0)
        :| End

executeMemLoadSequence1 ::
    RuntimeContext
        @WasmModuleShapeR
        '[I32, I32]
        '[I64, I64]
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
                '[I64, I64]
                ( ( WasmModuleR
                        '[]
                        ( currMem ': '[] )
                  ) :: WasmModule WasmModuleShapeR
                )
                '[]
        )
        memLoadSequence1

-- Example MemoryStore
-- memstoresequence :: Function EmptyValStack EmptyValStack (I32 ': I64 ': VNil) EmptyLabels ((WasmModuleR VNil (MemoryTypeR (LimitsR (fromIntegral 0 Word64) Nothing) '[] ': VNil)) :: WasmModule ( WasmModuleShapeR Z (S Z)))
memStoreSequence ::
    InstructionSequence
        '[]
        '[]
        '[I32, I64]
        ( (WasmModuleR '[] (storeMem ': '[])) ::
            WasmModule WasmModuleShapeR
        )
        '[]
        '[]
memStoreSequence =
    LocalGet SFZ -- get the value to store
        :| LocalGet (SFS SFZ) -- get the address
        :| MemoryStore @I32 SFZ (SMemArg 0 0)
        :| End

memStore ::
    Function
        '[]
        '[]
        '[I32, I64]
        '[]
        ((WasmModuleR '[] ('[] ': '[])) :: WasmModule WasmModuleShapeR)
memStore =
    Function
        (FFuncTypeAnn [] [])
        memStoreSequence

storeMem :: MemoryArray
storeMem = createMemory 65536
executeMemStore ::
    RuntimeContext
        @WasmModuleShapeR
        '[]
        '[I32, I64]
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
            , locals = ConsLocals 255 (ConsLocals 65532 NoLocals)
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = WasmInterpreter.ConsMems storeMem NoMems
            } ::
            RuntimeContext
                '[]
                '[I32, I64]
                ( ( WasmModuleR
                        '[]
                        ( storeMem ': '[]
                        )
                  ) :: WasmModule WasmModuleShapeR
                )
                '[]
        )
        memStoreSequence

memLoadStoreSequence ::
    InstructionSequence
        '[]
        '[I32]
        '[I32]
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
memLoadStoreSequence =
    LocalGet SFZ -- get the value to store
        :| I64Const 0 -- get the address
        :| MemoryStore @I32 SFZ (SMemArg 0 0)
        :| I64Const 0
        :| MemoryLoad @I32 SFZ (SMemArg 0 0)
        :| End

executeMemLoadStore ::
    RuntimeContext
        @WasmModuleShapeR
        '[I32]
        '[I32]
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
                '[I32]
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

memLoadStore64Sequence ::
    InstructionSequence
        '[]
        '[I64]
        '[I64]
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
memLoadStore64Sequence =
    LocalGet SFZ -- get the value to store
        :| I64Const 0 -- get the address
        :| MemoryStore @I64 SFZ (SMemArg 0 0)
        :| I64Const 0
        :| MemoryLoad @I64 SFZ (SMemArg 0 0)
        :| End

executeMemLoadStore64 ::
    RuntimeContext
        @WasmModuleShapeR
        '[I64]
        '[I64]
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
                '[I64]
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

-- Example GlobalGet and GlobalSet
-- have to force the WasmModuleShape so :: WasmModule (WasmModuleShapeR (S Z) Z) is necessary!!!
globalGetSetSequence ::
    InstructionSequence
        '[]
        (I32 ': '[])
        locals
        ( (WasmModuleR (GlobalTypeMW Var I32 ': '[]) '[]) ::
            WasmModule WasmModuleShapeR
        )
        outputLabels
        outputLabels
globalGetSetSequence =
    GlobalGet SFZ -- get global at index 0
        :| I32Const 10
        :| I32Add
        :| GlobalSet SFZ -- set global at index 0
        :| GlobalGet SFZ -- get global at index 0 again
        :| End

globalGetSet ::
    Function
        '[]
        (I32 ': '[])
        '[]
        '[]
        ( (WasmModuleR (GlobalTypeMW Var I32 ': '[]) '[]) ::
            WasmModule WasmModuleShapeR
        )
globalGetSet = Function (FFuncTypeAnn [] [I32]) globalGetSetSequence

-- Execution example for globalGetSetSequence
executeGlobalGetSetSequence ::
    RuntimeContext @WasmModuleShapeR
        '[I32]
        '[]
        (WasmModuleR '[GlobalTypeMW Var I32] '[])
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
                ( (WasmModuleR (GlobalTypeMW Var I32 ': '[]) '[]) :: WasmModule WasmModuleShapeR
                )
                '[]
        )
        globalGetSetSequence

globalSetConstSeq ::
    InstructionSequence
        (I32 ': '[])
        '[]
        locals
        ( (WasmModuleR '[GlobalTypeMW Const I32, GlobalTypeMW Var I32] '[]) ::
            WasmModule WasmModuleShapeR
        )
        outputLabels
        outputLabels
globalSetConstSeq =
    GlobalSet (SFS SFZ)
        -- :| GlobalSet SFZ      -- set global at index 0 should fail if uncommented
        :| End

add1Sequence ::
    forall
        {shape :: WasmModuleShape}
        {inputStack :: ValStackShape}
        {locals :: LocalsShape}
        {wasmModule :: WasmModule WasmModuleShapeR}
        {inputLabels :: LabelStackShape}.
    InstructionSequence
        (I32 ': (I32 ': inputStack))
        (I32 ': inputStack)
        locals
        wasmModule
        inputLabels
        inputLabels
add1Sequence = I32Add :| End

executeAdd1Sequence ::
    RuntimeContext @WasmModuleShapeR '[I32] '[] (WasmModuleR '[] '[]) '[]
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
                (I32 ': I32 ': '[])
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        add1Sequence

addSubSequence ::
    forall
        {shape :: WasmModuleShape}
        {inputStack :: ValStackShape}
        {locals :: LocalsShape}
        {wasmModule :: WasmModule WasmModuleShapeR}
        {inputLabels :: LabelStackShape}.
    InstructionSequence
        (I32 ': (I32 ': (I32 ': inputStack)))
        (I32 ': inputStack)
        locals
        wasmModule
        inputLabels
        inputLabels
addSubSequence = I32Add :| (I32Sub :| End)
executeAddSub ::
    RuntimeContext @WasmModuleShapeR '[I32] '[] (WasmModuleR '[] '[]) '[]
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
                (I32 ': I32 ': I32 ': '[])
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        addSubSequence

-- example function for Br instruction
branchExampleSeq ::
    forall
        {shape :: WasmModuleShape}
        {inputStack :: ValStackShape}
        {locals :: LocalsShape}
        {wasmModule :: WasmModule WasmModuleShapeR}
        {outputLabels :: LabelStackShape}.
    InstructionSequence
        -- inputStack
        -- ('[] +>+: Reverse (Take (Length inputStack) (Reverse inputStack)))
        '[]
        '[]
        locals
        wasmModule
        outputLabels
        outputLabels
branchExampleSeq =
    Block
        (BTParamsResults KnownValVNil KnownValVNil)
        ( Br SFZ
            :| End
        )
        :| End
branchExample ::
    Function
        '[]
        '[]
        (I32 ': '[])
        ('LabelShape '[] Z ': '[])
        ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)

branchExample = Function (FFuncTypeAnn [] []) branchExampleSeq

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

-- example function for Br instruction
branchExample2Seq ::
    forall {shape :: WasmModuleShape} {wasmModule :: WasmModule WasmModuleShapeR}.
    InstructionSequence
        '[]
        '[]
        '[]
        wasmModule
        ('LabelShape '[] Z ': '[])
        ('LabelShape '[] Z ': '[])
branchExample2Seq =
    Block
        (BTParamsResults KnownValVNil KnownValVNil)
        ( Br SFZ
            :| End
        )
        :| Br SFZ
        :| End
branchExample2 ::
    -- forall (s :: WasmModuleShape) (wm :: WasmModule s).
    Function @WasmModuleShapeR '[] '[] '[] ('LabelShape '[] Z ': '[]) wm
branchExample2 = Function (FFuncTypeAnn [] []) branchExample2Seq

-- this does not make sense for execution since we assume the first control frame and in execution we cannot drop it!
-- executeBranchExample2 :: RuntimeContext @(WasmModuleShapeR Z Z) '[] '[] (WasmModuleR '[] '[]) '[]
-- In validation we do not remove the label therefore have to type it like this! The above without a label should be more correct
-- executeBranchExample2 :: RuntimeContext @(WasmModuleShapeR Z Z) '[] '[] (WasmModuleR '[] '[]) '[ 'LabelShape '[] Z]
-- executeBranchExample2 = stepMany (RuntimeContext {values = NoValues, locals = NoLocals, WasmInterpreter.globals = WasmInterpreter.NoGlobals, labels = ConsLabels (Label SZ SZ (SomeInstrSeq End) :: Label ('LabelShape '[] 'Z) ) NoLabels, memories = NoMems} :: RuntimeContext '[] '[] ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z)) '[ 'LabelShape '[] Z])
--                 branchExample2Seq

branchExample3Seq ::
    forall
        {shape :: WasmModuleShape}
        {locals :: LocalsShape}
        {wasmModule :: WasmModule WasmModuleShapeR}
        {outputLabels :: LabelStackShape}.
    InstructionSequence
        '[I32, I64]
        '[I32, I32, I64]
        locals
        wasmModule
        outputLabels
        outputLabels -- example function for Br instruction
branchExample3Seq =
    Block
        (BTParamsResults KnownValVNil (KnownValCons ForI32 KnownValVNil))
        ( Block
            (BTParamsResults KnownValVNil KnownValVNil)
            ( Br SFZ
                :| End
            )
            :| I32Const 42
            :| Br SFZ
            :| End
        )
        :| End
branchExample3 ::
    -- forall (s :: WasmModuleShape) (wm :: WasmModule s).
    Function @WasmModuleShapeR '[I32, I64] (I32 ': '[I32, I64]) (I32 ': '[]) '[] wm
branchExample3 =
    Function
        (FFuncTypeAnn [] [])
        branchExample3Seq
executeBranchExample3 ::
    RuntimeContext @WasmModuleShapeR '[I32, I32, I64]
        '[]
        (WasmModuleR '[] '[])
        '[]
executeBranchExample3 =
    stepMany
        RuntimeContext
            { values = ConsValues (3 :: Int32) (ConsValues (2 :: Int64) NoValues)
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            }
        branchExample3Seq

-- example function for Br instruction

branchExample4Seq ::
    InstructionSequence '[] '[I32] locals wasmModule outputLabels outputLabels
branchExample4Seq =
    Block
        (BTParamsResults KnownValVNil (KnownValCons ForI32 KnownValVNil))
        ( Block
            (BTParamsResults KnownValVNil (KnownValCons ForI32 KnownValVNil))
            ( I32Const 42
                :| Br (SFS SFZ)
                -- :| I32Const 7 -- TODO BUG: in validation this instruction is not removed and therefore the types do not agree
                :| End
            )
            :| End
        )
        :| End

branchExample4 ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).Function '[] (I32 ': '[]) (I32 ': '[]) '[] wm

branchExample4 = Function (FFuncTypeAnn [] []) branchExample4Seq

executeBranchExample4 ::
    RuntimeContext @WasmModuleShapeR '[I32] '[] (WasmModuleR '[] '[]) '[]
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


branchExample5Seq ::
    InstructionSequence '[] '[I32] locals wasmModule '[] '[]
branchExample5Seq =
    Block
        (BTParamsResults KnownValVNil ( KnownValCons ForI32 KnownValVNil))
        ( Block
            (BTParamsResults KnownValVNil (KnownValCons ForI32 KnownValVNil))
            ( I32Const 42
                :| I32Const 7
                :| I32Const 3
                :| I32Add
                :| Br (SFS SFZ)
                :| End
            )
            :| End
        )
        :| End

executeBranchExample5 ::
    RuntimeContext @WasmModuleShapeR '[I32] '[] (WasmModuleR '[] '[]) '[]
executeBranchExample5 =
    stepMany
        RuntimeContext
            { values = NoValues
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            }
        branchExample5Seq

-- DOES NOT COMPILE AND SHOULD NOT COMPILE!!
-- (SEE block-simple-br2-nested.wat)
-- branchExampleNestedSeq ::
--     InstructionSequence '[] '[I32, I32] locals wasmModule '[] '[]
-- branchExampleNestedSeq =
--     Block
--         (BTParamsResults KnownValVNil (KnownValCons ForI32 (KnownValCons ForI32 KnownValVNil)))
--         ( I32Const 42
--             :| I32Const 7
--             :| Block
--                 (BTParamsResults (KnownValCons ForI32 KnownValVNil) (KnownValCons ForI32 KnownValVNil))
--                 ( 
--                     I32Const 3
--                     :| I32Add
--                     :| Br (SFS SFZ)
--                     :| End
--                 )
--             :| End
--         )
--         :| End
-- executeBranchExampleNested ::
--     RuntimeContext '[I32, I32] '[] (WasmModuleR '[] '[]) '[]
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

branchThesisSeq ::
    InstructionSequence '[] '[I64, I32] locals wasmModule '[] '[]
branchThesisSeq =
    Block
        (BTParamsResults KnownValVNil (KnownValCons ForI64 (KnownValCons ForI32 KnownValVNil)))
        ( I32Const 10
             :| Block -- here we have problem that we expect 1 i32 on top at the end of the block but we have two
                (BTParamsResults KnownValVNil (KnownValCons ForI64 KnownValVNil))
                ( 
                    I32Const 20
                    :| I64Const 30
                    :| Br (SFS SFZ)
                    :| End -- here we expect that we have one i32 as defined in innerblock but we in fact have two i32
                            -- hence the first thing saing the we cannot match [I32] (which is the second one) with the empty list => so the firest i32 has already been matched
                )
            :| End
        )
        :| End

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
branchThesisSeq2 ::
    InstructionSequence '[] '[I32, I32] locals wasmModule '[] '[]
branchThesisSeq2 = 
    Block
        (BTParamsResults KnownValVNil (KnownValCons ForI32 (KnownValCons ForI32 KnownValVNil)))
        ( I32Const 20
             :| Block
                (BTParamsResults KnownValVNil (KnownValCons ForI32 KnownValVNil))
                ( 
                    I32Const 6
                     :| Block
                        (BTParamsResults KnownValVNil (KnownValCons ForI32 KnownValVNil))
                        (
                            I32Const 4
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
    RuntimeContext @WasmModuleShapeR '[I32, I32] '[] (WasmModuleR '[] '[]) '[]
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

branchRandomAfterSequence ::
    InstructionSequence '[] '[I32] locals wasmModule '[] '[]
branchRandomAfterSequence =
    Block
        (BTParamsResults KnownValVNil (KnownValCons ForI32 (KnownValCons ForI32 KnownValVNil)))
        ( 
            I32Const 20
            :| I32Const 10
            :| Br SFZ
            :| I32Add -- this instruction is not removed in validation and therefore the types do not agree
            :| I32Add
            :| End
        )
    :| I32Add
    :| End
executeRandomAfterSequence ::
    RuntimeContext @WasmModuleShapeR '[I32] '[] (WasmModuleR '[] '[]) '[]
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

-- Does not compile and also SHOULD NOT compile
-- branchSimpleSeq :: 
--     InstructionSequence '[] '[I32, I32] locals wasmModule '[] '[]
-- branchSimpleSeq =
--     Block
--         (BTParamsResults KnownValVNil (KnownValCons ForI32 (KnownValCons ForI32 KnownValVNil)))
--         ( I32Const 10
--             :| Block
--                 (BTParamsResults KnownValVNil (KnownValCons ForI32 KnownValVNil))
--                 ( 
--                     I32Const 20
--                     :| Br (SFS SFZ)
--                     :| End
--                 )
--                 :| End
--         )
--         :| End

{- | Example 1: Add two integers
Takes two i32 parameters (slots 0 and 1), returns their sum
-}
add2Seq ::
    InstructionSequence '[] '[I32] '[I32, I32] wasmModule outputLabels outputLabels
add2Seq =
    LocalGet SFZ -- Push first parameter
        :| LocalGet (SFS SFZ) -- Push second parameter
        :| I32Add -- Add them (pops 2, pushes 1 result)
        :| End

add2 ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).
    Function '[] (I32 ': '[]) (I32 ': I32 ': '[]) '[] wm -- Function resultStack locals (repr the function parameters)
add2 =
    Function
        (FFuncTypeAnn [] [I32])
        -- Local slots: (0) first parameter, (1) second parameter
        add2Seq
executeAdd2 ::
    RuntimeContext @WasmModuleShapeR
        '[I32]
        '[I32, I32]
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
                '[I32, I32]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        add2Seq

-- Like this it doesn't compile either in wat2wasm not in our example
-- (module
--   (func $block-simple (result i32 i32)
--     (block (result i32 i32)
--       (i32.const 10)
--       (i32.const 20)
--       (block (param i32) (result i32)
--         (i32.const 10)
--         (i32.add)
--         (i32.const 1)
--         (br_if 1)
--       )
--     )
--   )
-- )
brIfSeq :: 
    InstructionSequence '[] '[I32, I32] '[] wasmModule outputLabels outputLabels
brIfSeq =
    Block
        (BTParamsResults KnownValVNil (KnownValCons ForI32 (KnownValCons ForI32 KnownValVNil)))
        ( I32Const 10
            :| I32Const 20
            :| Block
                (BTParamsResults (KnownValCons ForI32 KnownValVNil) (KnownValCons ForI32 KnownValVNil))
                (
                    I32Const 10
                    :| I32Add
                    :| I32Const 5
                    :| I32Const 1
                    :| BrIf (SFS SFZ)
                    :| Drop
                    :| End
                )
            :| End
        )
        :| End

{- | Example 2: Factorial function using iteration
Takes one i32 parameter, returns its factorial
-}
factorialSeq ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s) (outputLabels :: LabelStackShape).
    InstructionSequence
        '[]
        (I32 ': '[])
        (I32 ': I32 ': '[])
        wm
        outputLabels
        outputLabels
factorialSeq =
    -- Local slots: (0) input parameter (also used as counter), (1) accumulator
    -- Initialize accumulator to 1
    I32Const 1
        :| LocalSet (SFS SFZ)
        -- :| I32Const 0
        -- Main computation block
        :| Block
            (BTParamsResults KnownValVNil KnownValVNil)
            ( -- Check if n <= 1 (base case)
              I32Const 1
                :| LocalGet SFZ
                :| I32LeS
                :| BrIf SFZ -- Exit block if n <= 1
                -- Iterative loop for factorial computation
                :| Loop
                    (BTParamsResults KnownValVNil KnownValVNil)
                    ( -- accumulator *= n
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
                        :| I32Const 1
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

factorial ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).
    Function '[] (I32 ': '[]) (I32 ': I32 ': '[]) '[] wm
factorial =
    Function
        (FFuncTypeAnn [] [I32])
        factorialSeq
executeFactorial ::
    RuntimeContext @WasmModuleShapeR
        '[I32]
        '[I32, I32]
        (WasmModuleR '[] '[])
        '[]
-- we put as input 4 so the expected result is 24
executeFactorial =
    stepMany
        ( RuntimeContext
            { values = NoValues
            , locals = ConsLocals 4 (ConsLocals 0 NoLocals)
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext
                '[]
                '[I32, I32]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        factorialSeq

{- | Example 3: Function that returns nothing (void function).
Demonstrates different return types - this one returns Empty stack.
-}
printNumberSeq ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s) (outputLabels :: LabelStackShape).
    InstructionSequence '[] '[] '[I32, I32] wm outputLabels outputLabels
printNumberSeq =
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

printNumber ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).
    Function '[] '[] '[I32, I32] '[] wm
printNumber =
    Function
        (FFuncTypeAnn [] [])
        printNumberSeq
executePrintNumber ::
    RuntimeContext @WasmModuleShapeR '[] '[I32, I32] (WasmModuleR '[] '[]) '[]
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
                '[I32, I32]
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        printNumberSeq

{- | Example 4: Function with more complex local variable patterns.
Takes one parameter, uses three local variables for intermediate calculations.
-}
complexCalculationSeq ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s) (outputLabels :: LabelStackShape).
    InstructionSequence
        '[]
        '[I32]
        (I32 ': I32 ': I32 ': I32 ': '[])
        wm
        outputLabels
        outputLabels
complexCalculationSeq =
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
        :| LocalSet (SFS (SFS SFZ))
        -- result = temp1 + temp2
        :| LocalGet (SFS SFZ)
        :| LocalGet (SFS (SFS SFZ))
        :| I32Add
        :| LocalSet (SFS (SFS (SFS SFZ)))
        :| LocalGet (SFS (SFS (SFS SFZ))) -- return result on top of stack
        :| End

complexCalculation ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).
    Function '[] '[I32] (I32 ': I32 ': I32 ': I32 ': '[]) '[] wm
complexCalculation =
    Function
        (FFuncTypeAnn [] [I32])
        complexCalculationSeq

executeComplexCalculation ::
    RuntimeContext @WasmModuleShapeR
        '[I32]
        (I32 ': I32 ': I32 ': I32 ': '[])
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
                (I32 ': I32 ': I32 ': I32 ': '[])
                ((WasmModuleR '[] '[]) :: WasmModule WasmModuleShapeR)
                '[]
        )
        complexCalculationSeq

{- | Example 5: Conditional logic with If instruction.
Returns the absolute value of the input.
-}
absoluteValueSeq ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s) (outputLabels :: LabelStackShape).
    InstructionSequence '[] (I32 ': '[]) (I32 ': '[]) wm outputLabels outputLabels
absoluteValueSeq =
    -- Check if input is negative
    LocalGet SFZ
        :| I32Const 0
        :| I32LtS -- Is input < 0?
        :| If
            (BTParamsResults KnownValVNil (KnownValCons ForI32 KnownValVNil))
            -- Then branch: negate the number (0 - input)
            ( I32Const 0
                :| LocalGet SFZ
                :| I32Sub
                :| End
            )
            -- Else branch: return input as-is
            ( LocalGet SFZ
                :| End
            )
        :| End

absoluteValue ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).
    Function '[] (I32 ': '[]) (I32 ': '[]) '[] wm
absoluteValue =
    Function
        (FFuncTypeAnn [] [I32])
        absoluteValueSeq
executeAbsoluteValue ::
    RuntimeContext @WasmModuleShapeR '[I32] '[I32] (WasmModuleR '[] '[] :: WasmModule WasmModuleShapeR) '[]
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
                '[I32]
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
