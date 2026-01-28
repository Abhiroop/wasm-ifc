{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-
TODO Summary:
1. Line 39: tables, etc.
2. Line 196: BUG: in validation this instruction is not removed and therefore the types do not agree
-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

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
--       globals :: Globals (GetGlobals wasmModule), -- :: GlobalsShape (GetGlobalsShape shape)),
--       labels :: LabelStack labelsShape,
--       memories :: Memory (GetMems wasmModule)
--       -- TODO: tables, etc.
--     }
executeAddStep :: StepResult [I32 :~ Low, I32 :~ High] '[I32 :~ High] '[] (WasmModuleR '[] '[]) '[] '[] '[Low]
executeAddStep =
    step
        ( RuntimeContext
            { values = ConsValues 5 (ConsValues 10 NoValues)
            , locals = NoLocals
            , WasmInterpreter.globals = WasmInterpreter.NoGlobals
            , labels = NoLabels
            , memories = NoMems
            } ::
            RuntimeContext (I32 :~ Low ': I32 :~ High ': '[]) '[] (WasmModuleR '[] '[]) '[]
        )
        (CSingle (I32Add :| End))

executeAddMany ::
    RuntimeContext @(WasmModuleShapeR Z Z) '[I32 :~ Low] '[] (WasmModuleR '[] '[]) '[]
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
                (I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': '[])
                '[]
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        (I32Div :| I32Add :| End :: InstructionSequence '[I32 :~ Low, I32 :~ Low, I32 :~ Low] '[I32 :~ Low] '[] (WasmModuleR '[] '[]) '[] '[] '[Low])

executeDivMany ::
    RuntimeContext @(WasmModuleShapeR Z Z) '[I32 :~ Low] '[] (WasmModuleR '[] '[]) '[]
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
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        (I32Div :| End :: InstructionSequence '[I32 :~ Low, I32 :~ Low] '[I32 :~ Low] '[] (WasmModuleR '[] '[]) '[] '[] '[Low])

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
callExample ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).
    (s ~ WasmModuleShapeR Z Z) =>
    Function '[] (I32 :~ Low ': '[]) (I32 :~ Low ': I32 :~ Low ': '[]) '[] wm '[Low]
callExample =
    Function (FFuncTypeAnn [] [I32 :~ Low]) $
        LocalGet SFZ -- get first parameter
            :| LocalGet (SFS SFZ) -- get second parameter
            :| Call "add2" (FFuncTypeAnn  [I32 :~ Low, I32 :~ Low] [I32 :~ Low]) -- call add2 function
            :| End

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
{-
memLoadSequence ::
    InstructionSequence
        '[]
        '[I32 :~ Low]
        '[I64 :~ Low, I64 :~ Low]
        ( ( WasmModuleR
                '[]
                ( currMem
                    -- '[ fromIntegral 10 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 20::Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8]
                    ': '[]
                )
          ) ::
            WasmModule (WasmModuleShapeR Z (S (S Z)))
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
        (I32 :~ Low ': '[])
        (I64 :~ Low ': I64 :~ Low ': '[])
        '[]
        ( ( WasmModuleR
                '[]
                ( currMem
                    -- '[ fromIntegral 10 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 20::Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8]
                    ': '[]
                )
          ) ::
            WasmModule (WasmModuleShapeR Z (S (S Z)))
        )
memLoad =
    Function
        (FFuncTypeAnn [] [I32 :~ Low])
        memLoadSequence

executeMemLoad ::
    RuntimeContext @(WasmModuleShapeR Z (S (S Z)))
        '[I32 :~ Low]
        '[I64 :~ Low, I64 :~ Low]
        ( WasmModuleR
            '[]
            ( currMem
                -- '[ fromIntegral 10 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 20::Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8]
                ': '[]
            )
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
                        ( currMem
                            -- '[ fromIntegral 10 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 20::Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8]
                            ': '[]
                        )
                  ) ::
                    WasmModule (WasmModuleShapeR Z (S (S Z)))
                )
                '[]
        )
        memLoadSequence

memLoadSequence1 ::
    InstructionSequence
        '[]
        '[I32 :~ Low, I32 :~ Low]
        '[I64 :~ Low, I64 :~ Low]
        ( ( WasmModuleR
                '[]
                ( currMem
                    -- '[ fromIntegral 10 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 20::Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8]
                    ': '[]
                )
          ) ::
            WasmModule (WasmModuleShapeR Z (S (S Z)))
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
    RuntimeContext @(WasmModuleShapeR Z (S (S Z)))
        '[I32 :~ Low, I32 :~ Low]
        '[I64 :~ Low, I64 :~ Low]
        ( WasmModuleR
            '[]
            ( currMem
                -- '[ fromIntegral 10 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 20::Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8]
                ': '[]
            )
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
                '[I64 :~ Low, I64 :~ Low]
                ( ( WasmModuleR
                        '[]
                        ( currMem
                            -- '[ fromIntegral 10 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 20::Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8, fromIntegral 0 :: Word8]
                            ': '[]
                        )
                  ) ::
                    WasmModule (WasmModuleShapeR Z (S (S Z)))
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
        '[I32 :~ Low, I64 :~ Low]
        ( (WasmModuleR '[] (storeMem ': '[])) ::
            WasmModule (WasmModuleShapeR Z (S (S Z)))
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
        '[I32 :~ Low, I64 :~ Low]
        '[]
        ((WasmModuleR '[] ('[] ': '[])) :: WasmModule (WasmModuleShapeR Z (S (S Z))))
memStore =
    Function
        (FFuncTypeAnn [] [])
        memStoreSequence

storeMem :: MemoryArray
storeMem = createMemory 65536
executeMemStore ::
    RuntimeContext @(WasmModuleShapeR Z (S (S Z)))
        '[]
        '[I32 :~ Low, I64 :~ Low]
        ( WasmModuleR
            '[]
            ( storeMem
                ': '[]
            )
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
                '[I32 :~ Low, I64 :~ Low]
                ( ( WasmModuleR
                        '[]
                        ( storeMem
                            ': '[]
                        )
                  ) ::
                    WasmModule (WasmModuleShapeR Z (S (S Z)))
                )
                '[]
        )
        memStoreSequence

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
            WasmModule (WasmModuleShapeR Z (S (S Z)))
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
    RuntimeContext @(WasmModuleShapeR Z (S (S Z)))
        '[I32 :~ Low]
        '[I32 :~ Low]
        ( WasmModuleR
            '[]
            ( storeMem
                ': '[]
            )
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
                  ) ::
                    WasmModule (WasmModuleShapeR Z (S (S Z)))
                )
                '[]
        )
        memLoadStoreSequence

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
            WasmModule (WasmModuleShapeR Z (S (S Z)))
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
    RuntimeContext @(WasmModuleShapeR Z (S (S Z)))
        '[I64 :~ Low]
        '[I64 :~ Low]
        ( WasmModuleR
            '[]
            ( storeMem
                ': '[]
            )
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
                  ) ::
                    WasmModule (WasmModuleShapeR Z (S (S Z)))
                )
                '[]
        )
        memLoadStore64Sequence
-}
-- Example GlobalGet and GlobalSet
-- have to force the WasmModuleShape so :: WasmModule (WasmModuleShapeR (S Z) Z) is necessary!!!
globalGetSetSequence ::
    InstructionSequence
        '[]
        '[I32 :~ Low]
        locals
        ( (WasmModuleR (GlobalTypeMW Var (I32 :~ Low) ': '[]) '[]) ::
            WasmModule (WasmModuleShapeR (S Z) Z)
        )
        outputLabels
        outputLabels
        '[Low]
globalGetSetSequence =
    GlobalGet SFZ -- get global at index 0
        :| I32Const IsLow 10
        :| I32Add
        :| GlobalSet SFZ -- set global at index 0
        :| GlobalGet SFZ -- get global at index 0 again
        :| End

globalGetSet ::
    Function
        '[]
        '[I32 :~ Low]
        '[]
        '[]
        ( (WasmModuleR (GlobalTypeMW Var (I32 :~ Low) ': '[]) '[]) ::
            WasmModule (WasmModuleShapeR (S Z) Z)
        )
        '[Low]
globalGetSet = Function (FFuncTypeAnn [] [I32 :~ Low]) globalGetSetSequence

-- Execution example for globalGetSetSequence
executeGlobalGetSetSequence ::
    RuntimeContext @(WasmModuleShapeR (S Z) Z)
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
                ( (WasmModuleR (GlobalTypeMW Var (I32 :~ Low) ': '[]) '[]) ::
                    WasmModule (WasmModuleShapeR (S Z) Z)
                )
                '[]
        )
        globalGetSetSequence

globalSetConstSeq ::
    InstructionSequence
        '[I32 :~ Low]
        '[]
        locals
        ( (WasmModuleR '[GlobalTypeMW Const (I32 :~ Low), GlobalTypeMW Var (I32 :~ Low)] '[]) ::
            WasmModule (WasmModuleShapeR (S (S Z)) Z)
        )
        outputLabels
        outputLabels
        '[Low]
globalSetConstSeq =
    GlobalSet (SFS SFZ)
        -- :| GlobalSet SFZ      -- set global at index 0 should fail if uncommented
        :| End

add1Sequence ::
    forall
        {shape :: WasmModuleShape}
        {inputStack :: ValStackShape}
        {locals :: LocalsShape}
        {wasmModule :: WasmModule shape}
        {inputLabels :: LabelStackShape}.
    InstructionSequence
        (I32 :~ Low ': (I32 :~ Low ': inputStack))
        (I32 :~ Low ': inputStack)
        locals
        wasmModule
        inputLabels
        inputLabels
        '[Low]
add1Sequence = I32Add :| End

executeAdd1Sequence ::
    RuntimeContext @(WasmModuleShapeR Z Z) '[I32 :~ Low] '[] (WasmModuleR '[] '[]) '[]
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
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        add1Sequence

addSubSequence ::
    forall
        {shape :: WasmModuleShape}
        {inputStack :: ValStackShape}
        {locals :: LocalsShape}
        {wasmModule :: WasmModule shape}
        {inputLabels :: LabelStackShape}.
    InstructionSequence
        (I32 :~ Low ': (I32 :~ Low ': (I32 :~ Low ': inputStack)))
        (I32 :~ Low ': inputStack)
        locals
        wasmModule
        inputLabels
        inputLabels
        '[Low]
addSubSequence = I32Add :| (I32Sub :| End)
executeAddSub ::
    RuntimeContext @(WasmModuleShapeR Z Z) '[I32 :~ Low] '[] (WasmModuleR '[] '[]) '[]
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
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        addSubSequence

-- example function for Br instruction
branchExampleSeq ::
    forall
        {shape :: WasmModuleShape}
        {inputStack :: ValStackShape}
        {locals :: LocalsShape}
        {wasmModule :: WasmModule shape}.
    InstructionSequence
        inputStack
        ('[] +>+: Reverse (Take (Length inputStack) (Reverse inputStack)))
        locals
        wasmModule
        '[]
        '[]
        '[Low]
branchExampleSeq =
    Block
        (BTParamsResults KnownValVNil KnownValVNil)
        (Br SFZ
            :| End
        )
        :| End
branchExample ::
    Function
        '[]
        '[]
        '[I32 :~ Low]
        -- ('LabelShape '[] Z ': '[])
        '[]
        ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
        '[Low]
branchExample = Function (FFuncTypeAnn [] []) branchExampleSeq

executeBranchExample ::
    RuntimeContext @(WasmModuleShapeR Z Z) '[] '[] (WasmModuleR '[] '[]) '[]
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
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        branchExampleSeq

-- example function for Br instruction
branchExample2Seq ::
    forall {shape :: WasmModuleShape} {wasmModule :: WasmModule shape}.
    InstructionSequence
        '[]
        '[]
        '[]
        wasmModule
        '[ 'LabelShape '[] Z]
        '[ 'LabelShape '[] Z]
        '[Low, Low]
branchExample2Seq =
    Block
        (BTParamsResults KnownValVNil KnownValVNil)
        ( Br SFZ
            :| End
        )
        :| Br SFZ
        :| End
branchExample2 ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).
    (s ~ WasmModuleShapeR Z Z) =>
    Function '[] '[] '[] '[ 'LabelShape '[] Z] wm '[Low, Low]
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
        {wasmModule :: WasmModule shape}
        {outputLabels :: LabelStackShape}.
    InstructionSequence
        '[I32 :~ Low, I64 :~ Low]
        '[I32 :~ Low, I32 :~ Low, I64:~ Low]
        locals
        wasmModule
        '[]
        '[]
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
branchExample3 ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).
    (s ~ WasmModuleShapeR Z Z) =>
    Function '[I32 :~ Low, I64 :~ Low] (I32 :~ Low ': '[I32 :~ Low, I64 :~ Low]) (I32 :~ Low ': '[]) '[] wm '[Low]
branchExample3 =
    Function
        (FFuncTypeAnn [] [])
        branchExample3Seq
executeBranchExample3 ::
    RuntimeContext @(WasmModuleShapeR Z Z)
        '[I32 :~ Low, I32 :~ Low, I64 :~ Low]
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
    InstructionSequence '[] '[I32 :~ Low] locals wasmModule '[] '[] '[Low]
branchExample4Seq =
    Block
        (BTParamsResults KnownValVNil (KnownValCons (IsLow, ForI32) KnownValVNil))
        ( Block
            (BTParamsResults KnownValVNil KnownValVNil)
            ( I32Const IsLow 42
                :| Br (SFS SFZ)
                -- :| I32Const 7 -- TODO BUG: in validation this instruction is not removed and therefore the types do not agree
                :| End
            )
            :| End
        )
        :| End

branchExample4 ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).
    (s ~ WasmModuleShapeR Z Z) => Function '[] (I32 :~ Low ': '[]) (I32 :~ Low ': '[]) '[] wm '[Low]
branchExample4 = Function (FFuncTypeAnn [] []) branchExample4Seq

executeBranchExample4 ::
    RuntimeContext @(WasmModuleShapeR Z Z) '[I32 :~ Low] '[] (WasmModuleR '[] '[]) '[]
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

{-
EXAMPLE FOR IF WITH IFC
-}
ifCondSeq ::
    InstructionSequence
        '[I32 :~ High]
        '[I32 :~ High]
        '[]
        ( (WasmModuleR '[] '[]) ::
            WasmModule (WasmModuleShapeR Z Z)
        )
        outputLabels
        outputLabels
        '[Low]
ifCondSeq =
    If
        (BTParamsResults KnownValVNil KnownValVNil)
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
    RuntimeContext @(WasmModuleShapeR Z Z)
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
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        ifCondSeq


ifCondSeq2 ::
    InstructionSequence
        '[I32 :~ Low]
        '[I32 :~ Low]
        '[]
        ( (WasmModuleR '[] '[]) ::
            WasmModule (WasmModuleShapeR Z Z)
        )
        outputLabels
        outputLabels
        '[Low]
ifCondSeq2 =
    If
        (BTParamsResults KnownValVNil KnownValVNil)
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
    RuntimeContext @(WasmModuleShapeR Z Z)
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
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        ifCondSeq2

ifCondSeqParentHigh ::
    InstructionSequence
        '[I32 :~ Low]
        '[I32 :~ High]
        '[]
        ( (WasmModuleR '[] '[]) ::
            WasmModule (WasmModuleShapeR Z Z)
        )
        outputLabels
        outputLabels
        '[High]
ifCondSeqParentHigh =
    If
        (BTParamsResults KnownValVNil KnownValVNil)
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
    RuntimeContext @(WasmModuleShapeR Z Z)
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
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        ifCondSeqParentHigh


ifCondSeq3 ::
    InstructionSequence
        '[I32 :~ Low]
        '[I32 :~ High]
        '[]
        ( (WasmModuleR '[] '[]) ::
            WasmModule (WasmModuleShapeR Z Z)
        )
        outputLabels
        outputLabels
        '[Low]
ifCondSeq3 =
    If
        (BTParamsResults KnownValVNil KnownValVNil)
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
    RuntimeContext @(WasmModuleShapeR Z Z)
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
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        ifCondSeq3

ifCondSeqGetLocalLow ::
    InstructionSequence
        '[I32 :~ High]
        '[I32 :~ High]
        '[I32 :~ Low]
        ( (WasmModuleR '[] '[]) ::
            WasmModule (WasmModuleShapeR Z Z)
        )
        outputLabels
        outputLabels
        '[Low]
ifCondSeqGetLocalLow =
    If
        (BTParamsResults KnownValVNil KnownValVNil)
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
    RuntimeContext @(WasmModuleShapeR Z Z)
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
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        ifCondSeqGetLocalLow

ifCondSeqGetLocalHigh ::
    InstructionSequence
        '[I32 :~ Low]
        '[I32 :~ High]
        '[I32 :~ High]
        ( (WasmModuleR '[] '[]) ::
            WasmModule (WasmModuleShapeR Z Z)
        )
        outputLabels
        outputLabels
        '[Low]
ifCondSeqGetLocalHigh =
    If
        (BTParamsResults KnownValVNil KnownValVNil)
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
    RuntimeContext @(WasmModuleShapeR Z Z)
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
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        ifCondSeqGetLocalHigh

ifCondSeqSetLocalLow ::
    InstructionSequence
        '[I32 :~ Low]
        '[I32 :~ High]
        '[I32 :~ High]
        ( (WasmModuleR '[] '[]) ::
            WasmModule (WasmModuleShapeR Z Z)
        )
        outputLabels
        outputLabels
        '[Low]
ifCondSeqSetLocalLow =
    If
        (BTParamsResults KnownValVNil KnownValVNil)
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



{-
EXAMPLE FOR BRIF WITH TAINTED COND
-}



{- | Example 1: Add two integers
Takes two i32 parameters (slots 0 and 1), returns their sum
-}
add2Seq ::
    InstructionSequence '[] '[I32 :~ Low] '[I32 :~ Low, I32 :~ Low] wasmModule outputLabels outputLabels '[Low]
add2Seq =
    LocalGet SFZ -- Push first parameter
        :| LocalGet (SFS SFZ) -- Push second parameter
        :| I32Add -- Add them (pops 2, pushes 1 result)
        :| End

add2 ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).
    (s ~ WasmModuleShapeR Z Z) =>
    Function '[] (I32 :~ Low ': '[]) (I32 :~ Low ': I32 :~ Low ': '[]) '[] wm '[Low] -- Function resultStack locals (repr the function parameters)
add2 =
    Function
        (FFuncTypeAnn [] [I32 :~ Low])
        -- Local slots: (0) first parameter, (1) second parameter
        add2Seq
executeAdd2 ::
    RuntimeContext @(WasmModuleShapeR Z Z)
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
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        add2Seq

{- | Example 2: Factorial function using iteration
Takes one i32 parameter, returns its factorial
-}
factorialSeq ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s) (outputLabels :: LabelStackShape).
    (s ~ WasmModuleShapeR Z Z) =>
    InstructionSequence
        '[]
        (I32 :~ Low ': '[])
        (I32 :~ Low ': I32 :~ Low ': '[])
        wm
        '[]
        '[]
        '[Low]
factorialSeq =
    -- Local slots: (0) input parameter (also used as counter), (1) accumulator
    -- Initialize accumulator to 1
    I32Const IsLow 1
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
                :| Loop
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

factorial ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).
    (s ~ WasmModuleShapeR Z Z) =>
    Function '[] (I32 :~ Low ': '[]) (I32 :~ Low ': I32 :~ Low ': '[]) '[] wm '[Low]
factorial =
    Function
        (FFuncTypeAnn [] [I32 :~ Low])
        factorialSeq
executeFactorial ::
    RuntimeContext @(WasmModuleShapeR Z Z)
        '[I32 :~ Low]
        '[I32 :~ Low, I32 :~ Low]
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
                '[I32 :~ Low, I32 :~ Low]
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        factorialSeq

{- | Example 3: Function that returns nothing (void function).
Demonstrates different return types - this one returns Empty stack.
-}
printNumberSeq ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s) (outputLabels :: LabelStackShape).
    (s ~ WasmModuleShapeR Z Z) =>
    InstructionSequence '[] '[] '[I32 :~ Low, I32 :~ Low] wm outputLabels outputLabels '[Low]
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
    (s ~ WasmModuleShapeR Z Z) => Function '[] '[] '[I32 :~ Low, I32 :~ Low] '[] wm '[Low]
printNumber =
    Function
        (FFuncTypeAnn [] [])
        printNumberSeq
executePrintNumber ::
    RuntimeContext @(WasmModuleShapeR Z Z) '[] '[I32 :~ Low, I32 :~ Low] (WasmModuleR '[] '[]) '[]
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
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        printNumberSeq

{- | Example 4: Function with more complex local variable patterns.
Takes one parameter, uses three local variables for intermediate calculations.
-}
complexCalculationSeq ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s) (outputLabels :: LabelStackShape).
    (s ~ WasmModuleShapeR Z Z) =>
    InstructionSequence
        '[]
        '[I32 :~ Low]
        (I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': '[])
        wm
        outputLabels
        outputLabels
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

complexCalculation ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).
    (s ~ WasmModuleShapeR Z Z) =>
    Function '[] '[I32 :~ Low] (I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': I32 :~ Low ': '[]) '[] wm '[Low]
complexCalculation =
    Function
        (FFuncTypeAnn [] [I32 :~ Low])
        complexCalculationSeq

executeComplexCalculation ::
    RuntimeContext @(WasmModuleShapeR Z Z)
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
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
                '[]
        )
        complexCalculationSeq

{- | Example 5: Conditional logic with If instruction.
Returns the absolute value of the input.
-}
absoluteValueSeq ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s) (outputLabels :: LabelStackShape).
    (s ~ WasmModuleShapeR Z Z) =>
    InstructionSequence '[] (I32 :~ Low ': '[]) (I32 :~ Low ': '[]) wm outputLabels outputLabels '[Low]
absoluteValueSeq =
    -- Check if input is negative
    LocalGet SFZ
        :| I32Const IsLow 0
        :| I32LtS -- Is input < 0?
        :| If
            (BTParamsResults KnownValVNil KnownValVNil)
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

absoluteValue ::
    forall (s :: WasmModuleShape) (wm :: WasmModule s).
    (s ~ WasmModuleShapeR Z Z) => Function '[] (I32 :~ Low ': '[]) (I32 :~ Low ': '[]) '[] wm '[Low]
absoluteValue =
    Function
        (FFuncTypeAnn [] [I32 :~ Low])
        absoluteValueSeq
executeAbsoluteValue ::
    RuntimeContext @(WasmModuleShapeR Z Z) '[I32 :~ Low] '[I32 :~ Low] (WasmModuleR '[] '[]) '[]
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
                ((WasmModuleR '[] '[]) :: WasmModule (WasmModuleShapeR Z Z))
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
