{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-
TODO Summary:
1. Line 95: tables, etc.
2. Line 149: double check this
3. Line 248: double check the operand order
4. Line 249: double check the operand order
5. Line 270: double check the operand order
6. Line 271: double check the operand order
7. Line 315: How do we want to define the memory array?
8. Line 395: In future instead of inlining Br's code investigate how can we call `Br`
9. Line 437: double check the operand order
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
module WasmInterpreter where

import Data.Bits
import Data.Function (on)
import Data.Int (Int32, Int64)
import Data.Word (Word32, Word64, Word8)
-- (RuntimeTypeOf(..), ValStackShape(..), BlockType (..),  FuncTypeAnn (..), knownStackShapeLen, Take, Drop, FuncTypeAnn (..), Reverse, WasmType (I32), KnownWasmType (ForI32, ForI64), RuntimeWasmTypes(..), (:+>+), type (+>+:), KnownValStackShape(..), LabelStackShape, SomeValStackShape(..), GetSpecificValVec, GetLabelType, GetLabelCreationValStackLength)

-- HACK: ambiguous record fields

import Debug.Trace (traceShow)
import Types
import Unsafe.Coerce
import Utils
import Wasm
import WasmModule hiding (globals)
import Data.Char (GeneralCategory(Control))

{-
=============================================================================
INTERPRETER
=============================================================================
-}

reduceStackToLength ::
    forall n valuesShape.
    SNat n ->
    ValueStack valuesShape ->
    ValueStack (Reverse (Take n (Reverse valuesShape)))
    -- ValueStack ( (Take n (Reverse valuesShape)))
-- reduceStackToLength n = fst . takeStack n . reverseStack
reduceStackToLength n vals = reverseStack (fst (takeStack n (reverseStack vals)))

reverseStack :: ValueStack valuesShape -> ValueStack (Reverse valuesShape)
reverseStack NoValues = NoValues
reverseStack (ConsValues @wasmType secV rest) =
    concatStacks (reverseStack rest) (ConsValues @wasmType secV NoValues)

{- | Runtime representation of the WebAssembly stack.
This is the actual data structure that holds stack values during execution.
-}
data ValueStack (shape :: ValStackShape) where
    NoValues :: ValueStack '[]
    ConsValues :: RuntimeSecTypeOf top -> ValueStack shape -> ValueStack (top ': shape)

{- | Runtime representation of the WebAssembly locals.
This is the actual data structure that holds local values during execution.
-}
data Locals (localsShape :: LocalsShape) where
    NoLocals :: Locals '[]
    ConsLocals ::
        (KnownSecLevel l, RuntimeTypeOf wasmType) -> Locals localsShape -> Locals (wasmType :~ l ': localsShape)

data Globals (globalsShape :: GlobalsShape) where
    NoGlobals :: Globals '[]
    ConsGlobals ::
        (KnownSecLevel l,
        RuntimeTypeOf wasmType) ->
        KnownMutability m ->
        Globals globalsShape ->
        Globals (GlobalTypeMW m (wasmType :~ l) ': globalsShape)
data Memory (memsShape :: MemoriesShape) where
    NoMems :: Memory '[]
    ConsMems :: MemoryArray -> Memory memsShape -> Memory (memArray : memsShape)

data SomeInstrSeq where
    SomeInstrSeq ::
        InstructionSequence initialVal finalVal locals outLocals wasmModule outWasmModule initialLab finalLab ->
        SomeInstrSeq

-- HACK: no way of having record syntax with GADT features?
data Label (shape :: LabelShape) where
    --       height                 arity                 continuation
    Label ::
        SNat (Height shape) -> SNat (Arity shape) -> SomeInstrSeq -> Label shape

data LabelStack (shape :: LabelStackShape) where
    NoLabels :: LabelStack '[]
    ConsLabels ::
        Label topShape ->
        LabelStack restShape ->
        LabelStack (topShape ': restShape)

data SomeLabelStack = forall shape. SomeLabelStack (LabelStack shape)

data
    RuntimeContext
        (valuesShape :: ValStackShape)
        (localsShape :: LocalsShape)
        (wasmModule :: WasmModule shape)
        (labelsShape :: LabelStackShape) = RuntimeContext
    { values :: ValueStack valuesShape
    , locals :: Locals localsShape
    , globals :: Globals (GetGlobals wasmModule) -- :: GlobalsShape (GetGlobalsShape shape)),
    , labels :: LabelStack labelsShape
    , memories :: Memory (GetMems wasmModule)
    -- TODO: tables, etc.
    }

stackLength ::
    ValueStack (valuesShape :: ValStackShape) -> SNat (Length valuesShape)
stackLength NoValues = SZ
stackLength (ConsValues _ rest) = SS (stackLength rest)

takeStack ::
    () => SNat n -> ValueStack s -> (ValueStack (Take n s), ValueStack (Drop n s))
takeStack SZ stk = (NoValues, stk)
takeStack (SS n) (ConsValues secX xs) =
    let (taken, rest) = takeStack n xs
     in (ConsValues secX taken, rest)
takeStack (SS _) NoValues = error "takeStack: stack underflow"

concatStacks :: ValueStack s1 -> ValueStack s2 -> ValueStack (s1 +>+: s2)
concatStacks NoValues s2 = s2
concatStacks (ConsValues secX rest) s2 = ConsValues secX (concatStacks rest s2)

getAtLabel ::
    (l ~ Length labelStackShape) =>
    SFin n l ->
    LabelStack (labelStackShape :: LabelStackShape) ->
    Label (Index n labelStackShape)
getAtLabel SFZ (ConsLabels label _) = label
getAtLabel (SFS idx) (ConsLabels _ rest) = getAtLabel idx rest

dropLabels ::
    (l ~ Length shape) => SFin n l -> LabelStack shape -> LabelStack (Drop n shape)
dropLabels SFZ (ConsLabels label rest) = ConsLabels label rest
dropLabels (SFS n) (ConsLabels _ rest) = dropLabels n rest

-- function to get the value of a local variable at a given index
getLocal ::
    SFin i n -> Locals localsShape -> RuntimeSecTypeOf (Index i localsShape)
getLocal SFZ (ConsLocals (secLevel, val) _) = (secLevel, val)
getLocal (SFS idx) (ConsLocals _ rest) = getLocal idx rest
getLocal _ NoLocals = error "Index out of bounds in getLocal"

-- function to set the value of a local variable at a given index
setLocal :: -- ((KnownSecLevel l, w) ~ RuntimeSecTypeOf (Index i localsShape)) =>
    SFin i n ->
    (KnownSecLevel newSecLevel, RuntimeTypeOf (GetWasmType (Index i localsShape))) -> -- TODO: not sure whether here we also somehow need to set the sec level
    Locals localsShape ->
    Locals (SetSecLevelLocals i newSecLevel localsShape)
setLocal SFZ (newSecLevel, newVal) (ConsLocals _ rest) = ConsLocals (newSecLevel, newVal) rest
setLocal (SFS idx) (newSecLevel, newVal) (ConsLocals (secLevel, val) rest) = ConsLocals (secLevel, val) (setLocal idx (newSecLevel, newVal) rest)
setLocal _ _ NoLocals = error "Index out of bounds in setLocal"

-- function to get the value of a global variable at a given index
getGlobal ::
    SFin i n ->
    Globals globalsShape ->
    RuntimeSecTypeOf (GlobalTypeToWasmType (Index i globalsShape))
getGlobal SFZ (ConsGlobals val _ _) = val
getGlobal (SFS idx) (ConsGlobals _ _ rest) = getGlobal idx rest
getGlobal _ NoGlobals = error "Index out of bounds in getGlobal"

-- function to set the value of a global variable at a given index, mutability has to be var
setGlobal ::
    SFin i n ->
    -- RuntimeSecTypeOf (GlobalTypeToWasmType (Index i globalsShape)) ->
    (KnownSecLevel newSecLevel, RuntimeTypeOf (GetWasmType (GlobalTypeToWasmType (Index i globalsShape)))) ->
    Globals globalsShape ->
    Globals (SetSecLevelGlobals i newSecLevel globalsShape)
setGlobal SFZ newVal (ConsGlobals _ SVar rest) = ConsGlobals newVal SVar rest
setGlobal (SFS idx) newVal (ConsGlobals oldVal SVar rest) = ConsGlobals oldVal SVar (setGlobal idx newVal rest)
setGlobal _ _ (ConsGlobals _ SConst _) = error "Cannot set value of a constant global variable" -- TODO: double check this
setGlobal _ _ NoGlobals = error "Index out of bounds in setGlobalValue"

-- function to get the array of a memory at a given index
getMemoryArray :: SFin i n -> Memory memsShape -> MemoryArray
getMemoryArray SFZ (ConsMems memArray _) = memArray
getMemoryArray (SFS idx) (ConsMems _ rest) = getMemoryArray idx rest
getMemoryArray _ NoMems = error "Index out of bounds in getMemoryArray"

pushValue ::
    RuntimeSecTypeOf top ->
    RuntimeContext values locals wasmModule labels ->
    RuntimeContext (top ': values) locals wasmModule labels
pushValue secValue ctx = ctx{values = ConsValues secValue (values ctx)}

pushLabel ::
    Label top ->
    RuntimeContext values locals wasmModule labels ->
    RuntimeContext values locals wasmModule (top ': labels)
pushLabel label ctx = ctx{labels = ConsLabels label (labels ctx)}

data
    ControlStack
        (initialVal :: ValStackShape)
        (finalVal :: ValStackShape)
        (locals :: LocalsShape)
        (outLocals :: LocalsShape)
        (wasmModule :: WasmModule shape)
        (finalWasmModule :: WasmModule shape)
        (initialLab :: LabelStackShape)
        (finalLab :: LabelStackShape)
    where
    CSingle ::
        InstructionSequence initialVal finalVal locals outLocals wasmModule outWasmModule initialLab finalLab ->
        ControlStack initialVal finalVal locals outLocals wasmModule outWasmModule initialLab finalLab
    CCons :: -- TODO: maybe also have to have in and out locals here
        InstructionSequence initialVal middleVal locals middleLocals wasmModule middleWasmModule initialLab middleLab ->
        ControlStack middleVal finalVal middleLocals outLocals middleWasmModule finalWasmModule middleLab finalLab ->
        ControlStack initialVal finalVal locals outLocals wasmModule finalWasmModule initialLab finalLab

insertMemory ::
    SFin i n ->
    MemoryArray ->
    Memory memsShape ->
    Memory memsShape
insertMemory SFZ memArray (ConsMems _ memshape) = ConsMems memArray memshape
insertMemory (SFS idx) memArray (ConsMems mem rest) = ConsMems mem (insertMemory idx memArray rest)
insertMemory _ _ _ = error "Index out of bounds in insertMemory"

cprepend ::
    Instruction initialVal middleVal locals middleLocals wasmModule middleWasmModule initialLab middleLab ->
    ControlStack middleVal finalVal middleLocals outLocals middleWasmModule finalWasmModule middleLab finalLab ->
    ControlStack initialVal finalVal locals outLocals wasmModule finalWasmModule initialLab finalLab
cprepend instruction (CSingle current) = CSingle (instruction :| current)
cprepend instruction (CCons current parents) = CCons (instruction :| current) parents

appendInstructionSeq ::
    InstructionSequence initialVal middleVal locals middleLocals wasmModule middleWasmModule initialLab middleLab ->
    Instruction middleVal finalVal middleLocals finalLocals middleWasmModule finalWasmModule middleLab finalLab ->
    InstructionSequence initialVal finalVal locals finalLocals wasmModule finalWasmModule initialLab finalLab
appendInstructionSeq instrSeq instruction = case instrSeq of
    End -> instruction :| End
    (instr :| rest) -> instr :| appendInstructionSeq rest instruction

-- I think I need a cappend function since actually we want it as the last thing we do inside the body not the first thing we do outside the body
-- because if we have it as the first thing we might branch and leave but if we branch we do not want to leave!
cappend ::
    ControlStack initialVal middleVal locals middleLocals wasmModule middleWasmModule initialLab middleLab ->
    Instruction middleVal finalVal middleLocals finalLocals middleWasmModule finalWasmModule middleLab finalLab ->
    ControlStack initialVal finalVal locals finalLocals wasmModule finalWasmModule initialLab finalLab
cappend (CSingle current) instruction = CSingle (appendInstructionSeq current instruction)
cappend (CCons current parents) instruction = CCons current (cappend parents instruction)

data ControlStackWithSomeInitial locals wasmModule finalVal finalLab
    = forall initialVal initialLab initialLocals initialWasmModule.
        ControlStackWithSomeInitial
        (ControlStack initialVal finalVal initialLocals locals initialWasmModule wasmModule initialLab finalLab)

-- HACK: not using info in SFin
dropControlFrames ::
    SFin n l ->
    ControlStack initialVal finalVal locals outLocals wasmModule finalWasmModule initialLab finalLab ->
    ControlStackWithSomeInitial outLocals finalWasmModule finalVal finalLab
dropControlFrames SFZ frames = ControlStackWithSomeInitial frames
dropControlFrames (SFS n) (CCons _ rest) = dropControlFrames n rest
dropControlFrames _ (CSingle _) = error "Branch depth exceeds control stack"

data
    StepResult
        (initialVal :: ValStackShape)
        (finalVal :: ValStackShape)
        (locals :: LocalsShape)
        (outLocals :: LocalsShape)
        (wasmModule :: WasmModule shape)
        (finalWasmModule :: WasmModule shape)
        (initialLab :: LabelStackShape)
        (finalLab :: LabelStackShape)
    = forall middleVal middleLab middleLocals middleWasmModule.
        StepResult
        (RuntimeContext middleVal middleLocals middleWasmModule middleLab)
        (ControlStack middleVal finalVal middleLocals outLocals middleWasmModule finalWasmModule middleLab finalLab)

step ::
    RuntimeContext initialVal locals wasmModule initialLab ->
    ControlStack initialVal finalVal locals outLocals wasmModule finalWasmModule initialLab finalLab ->
    StepResult initialVal finalVal locals outLocals wasmModule finalWasmModule initialLab finalLab
step ctx (CSingle End) = StepResult ctx (CSingle End)
step ctx (CSingle (instruction :| rest)) = stepInternal ctx instruction (CSingle rest)
step ctx (CCons End parents) = StepResult ctx parents
step ctx (CCons (instruction :| rest) parents) = stepInternal ctx instruction (CCons rest parents)

stepInternal ::
    forall initialVal initialLocals initialWasmModule middleVal middleLocals middleWasmModule finalVal finalLocals finalWasmModule initialLab middleLab finalLab.
    RuntimeContext initialVal initialLocals initialWasmModule initialLab ->
    Instruction initialVal middleVal initialLocals middleLocals initialWasmModule middleWasmModule initialLab middleLab ->
    ControlStack middleVal finalVal middleLocals finalLocals middleWasmModule finalWasmModule middleLab finalLab ->
    StepResult initialVal finalVal initialLocals finalLocals initialWasmModule finalWasmModule initialLab finalLab
stepInternal ctx instruction nextControl = case instruction of
    I32Const value -> StepResult (pushValue (IsLow,value) ctx) nextControl
    I32Add -> stepBinaryOp (+) ctx nextControl
    I32Sub -> stepBinaryOp (-) ctx nextControl
    I32Mul -> stepBinaryOp (*) ctx nextControl
    I32Div -> stepBinaryOp div ctx nextControl
    I32RemU -> stepBinaryOp mod ctx nextControl -- TODO: double check the operand order
    I32RemS -> stepBinaryOp unsignedMod ctx nextControl -- TODO: double check the operand order
      where
        unsignedMod lhs rhs = fromIntegral $ (mod `on` (fromIntegral :: Int32 -> Word32)) lhs rhs
    I32EqZ -> stepUnaryOp (\x -> fromIntegral (fromEnum (x == 0))) ctx nextControl
    I32Eq -> stepBinaryOp (compareI32 (==)) ctx nextControl
    I32Neq -> stepBinaryOp (compareI32 (/=)) ctx nextControl
    I32LtS -> stepBinaryOp (compareI32 (<)) ctx nextControl
    I32LtU -> stepBinaryOp (compareU32 (<)) ctx nextControl
    I32LeS -> stepBinaryOp (compareI32 (<=)) ctx nextControl
    I32LeU -> stepBinaryOp (compareU32 (<=)) ctx nextControl
    I32GtS -> stepBinaryOp (compareI32 (>)) ctx nextControl
    I32GtU -> stepBinaryOp (compareU32 (>)) ctx nextControl
    I32GeS -> stepBinaryOp (compareI32 (>)) ctx nextControl
    I32GeU -> stepBinaryOp (compareU32 (>=)) ctx nextControl
    I64Const value -> StepResult (pushValue (IsLow,value) ctx) nextControl
    I64Add -> stepBinaryOp (+) ctx nextControl
    I64Sub -> stepBinaryOp (-) ctx nextControl
    I64Mul -> stepBinaryOp (*) ctx nextControl
    I64Div -> stepBinaryOp div ctx nextControl
    I64RemU -> stepBinaryOp mod ctx nextControl -- TODO: double check the operand order
    I64RemS -> stepBinaryOp unsignedMod ctx nextControl -- TODO: double check the operand order
      where
        unsignedMod lhs rhs = fromIntegral $ (mod `on` (fromIntegral :: Int64 -> Word64)) lhs rhs
    I64EqZ -> stepUnaryOp (\x -> fromIntegral (fromEnum (x == 0))) ctx nextControl
    I64Eq -> stepBinaryOp (compareI64 (==)) ctx nextControl
    I64Neq -> stepBinaryOp (compareI64 (/=)) ctx nextControl
    I64LtS -> stepBinaryOp (compareI64 (<)) ctx nextControl
    I64LtU -> stepBinaryOp (compareU64 (<)) ctx nextControl
    I64LeS -> stepBinaryOp (compareI64 (<=)) ctx nextControl
    I64LeU -> stepBinaryOp (compareU64 (<=)) ctx nextControl
    I64GtS -> stepBinaryOp (compareI64 (>)) ctx nextControl
    I64GtU -> stepBinaryOp (compareU64 (>)) ctx nextControl
    I64GeS -> stepBinaryOp (compareI64 (>)) ctx nextControl
    I64GeU -> stepBinaryOp (compareU64 (>=)) ctx nextControl
    Drop -> case values ctx of
        ConsValues _ rest ->
            let newCtx = ctx{values = rest}
             in StepResult newCtx nextControl
    LocalGet slot -> case getLocal slot (locals ctx) of
        val -> StepResult (pushValue val ctx) nextControl
    LocalSet slot -> case values ctx of
        ConsValues (secLevel, newVal) rest ->
            let newCtx =
                    ctx
                        { values = rest
                        , locals = setLocal slot (secLevel, newVal) (locals ctx)
                        }
             in StepResult newCtx nextControl
    LocalTee slot -> case values ctx of
        ConsValues (secLevel, val) _ ->
            let newCtx = ctx{locals = setLocal slot (secLevel, val) (locals ctx)}
             in StepResult newCtx nextControl
    GlobalGet slot -> case getGlobal slot (globals ctx) of
        val -> StepResult (pushValue val ctx) nextControl
    GlobalSet slot -> case values ctx of
        ConsValues (secLevel, val) rest ->
            let newCtx =
                    ctx
                        { values = rest
                        , globals = setGlobal slot (secLevel, val) (globals ctx) :: Globals (GetGlobals middleWasmModule)
                        , memories = memories ctx :: Memory (GetMems middleWasmModule)
                        }
             in StepResult newCtx nextControl
    -- Have memory array as a list of bytes and then we cast it when we load/store
    -- So F64 and I64 would read 8 bytes (8 consecutive elements) and cast them to the right type
    -- and F32 and I32 would read 4 bytes (4 consecutive elements) and cast them to the right type
    MemoryLoad @(wasmType :: WasmType) memidx (SMemArg alignment offset) -> case values ctx of
        ConsValues (secLevel, addr) rest ->
            let memoryArray = getMemoryArray memidx (memories ctx)
                addrAsWord64 = fromIntegral addr :: Word64
             in case (byteSize @wasmType) of
                    I32 ->
                        -- first check bounds of memory
                        if addrAsWord64 + offset + 4 >= (fromIntegral (length memoryArray) :: Word64)
                            then error "Memory access out of bounds in MemoryLoad I32"
                            else
                                let value = load @wasmType memoryArray (addrAsWord64 + offset)
                                 in StepResult (ctx{values = ConsValues (IsHigh, value) rest}) nextControl
                    I64 ->
                        if addrAsWord64 + offset + 8 >= (fromIntegral (length memoryArray) :: Word64)
                            then error "Memory access out of bounds in MemoryLoad I64"
                            else
                                let value = load @wasmType memoryArray (addrAsWord64 + offset)
                                 in StepResult (ctx{values = ConsValues (IsHigh, value) rest}) nextControl
    MemoryStore
        @(wasmType :: WasmType)
        (memidx :: SFin i n)
        (SMemArg alignment offset) -> case values ctx of
        ConsValues (secLevel, addr :: Int64) (ConsValues (secLevelVal, value :: RuntimeTypeOf wasmType) rest) ->
            let memoryArray = getMemoryArray memidx (memories ctx)
                addrAsWord64 = fromIntegral addr :: Word64
             in case (byteSize @wasmType) of
                    I32 ->
                        if addrAsWord64 + offset + 4 > (fromIntegral (length memoryArray) :: Word64)
                            then error "Memory access out of bounds in MemoryStore I32"
                            else
                                let newMemoryArray = store @wasmType memoryArray (addrAsWord64 + offset) value
                                    -- newMemories = ConsMems newMemoryArray (memories ctx)
                                    newCtx =
                                        ctx
                                            { values = rest
                                            , memories =
                                                insertMemory memidx newMemoryArray (memories ctx) :: Memory (GetMems initialWasmModule)
                                                -- memories = take memidx (memories ctx) ++ newMemoryArray ++ drop (SFS memidx) (memories ctx)
                                            }  ::
                                             RuntimeContext middleVal initialLocals initialWasmModule initialLab
                                 in StepResult newCtx nextControl
                    I64 ->
                        if addrAsWord64 + offset + 8 > (fromIntegral (length memoryArray) :: Word64)
                            then error "Memory access out of bounds in MemoryStore I64"
                            else
                                let newMemoryArray = store @wasmType memoryArray (addrAsWord64 + offset) value
                                    newCtx =
                                        ctx
                                            { values = rest
                                            , memories =
                                                insertMemory memidx newMemoryArray (memories ctx) :: Memory (GetMems initialWasmModule)
                                            } ::
                                            RuntimeContext middleVal initialLocals initialWasmModule initialLab
                                 in StepResult newCtx nextControl
    Block (BTParamsResults _ (res :: KnownValStackShape resStack)) body ->
        let newCtx =
                pushLabel
                    (Label (stackLength $ values ctx) (knownStackShapeLen res) (SomeInstrSeq End))
                    ctx
         in StepResult newCtx (CCons (appendInstructionSeq body Leave) nextControl)
    Loop
        blockType@(BTParamsResults (params :: KnownValStackShape paramsStack) _)
        body ->
        let loopCont = SomeInstrSeq (Loop blockType body :| End)
            newCtx =
                pushLabel
                    (Label (stackLength $ values ctx) (knownStackShapeLen params) loopCont)
                    ctx
         in StepResult newCtx (CCons (appendInstructionSeq body Leave) nextControl)
    If (BTParamsResults _ (res :: KnownValStackShape resStack)) thenBody elseBody ->
        case values ctx of
            ConsValues (secLevel, cond :: RuntimeTypeOf I32) restVal ->
                let newCtx =
                        ctx
                            { values = restVal
                            , labels =
                                ConsLabels
                                    (Label (stackLength restVal) (knownStackShapeLen res) (SomeInstrSeq End))
                                    (labels ctx)
                            }
                    -- TODO: need to merge the security levels here of the locals and globals and the stack?
                    -- TODO: also need to handle the condition thing...
                    body = if cond /= 0 then thenBody else elseBody
                 in StepResult newCtx (CCons (appendInstructionSeq body Leave) nextControl)
    -- The first drop is correct since we drop the label anyways with the leave instruction that we added in the block instruction
    -- For the controlFrames I have to drop depth frames +1 to get to the right instruction sequence
    Br depth ->
        case (dropLabels depth (labels ctx), dropControlFrames (SFS depth) nextControl) of
            ( ConsLabels (Label heightToPreserve arity someNext) (restLab :: LabelStack restLabShape)
                , ControlStackWithSomeInitial nextParents
                ) ->
                let (valuesToKeep, _) = takeStack arity (values ctx)
                    baseValues = reduceStackToLength heightToPreserve (values ctx)
                    finalValues = concatStacks valuesToKeep baseValues
                    nextCtx = ctx{values = finalValues, labels = restLab, globals = globals ctx, memories = memories ctx} :: RuntimeContext middleVal initialLocals middleWasmModule restLabShape
                 in case someNext of
                        SomeInstrSeq next -> StepResult nextCtx (cprepend (unsafeCoerce next) nextParents)
    -- TODO: In future instead of inlining Br's code investigate how can we call `Br`
    BrIf (depth :: SFin i n) ->
        case values ctx of
            ConsValues (secLevel, cond) rest ->
                if cond == 0
                    then case (dropLabels depth (labels ctx), dropControlFrames (SFS depth) nextControl) of
                        ( ConsLabels ((Label heightToPreserve arity someNext) :: Label  targetLabel) (restLab :: LabelStack restLabShape)
                            , ControlStackWithSomeInitial nextParents
                            ) ->
                            let (valuesToKeep, _) = takeStack arity rest
                                baseValues = reduceStackToLength heightToPreserve rest
                                finalValues = concatStacks valuesToKeep baseValues
                                nextCtx = ctx{values = finalValues, labels = restLab, globals = globals ctx, memories = memories ctx}  :: 
                                    RuntimeContext (Take (Arity targetLabel) middleVal +>+: Reverse (Take (Height targetLabel) (Reverse middleVal))) initialLocals middleWasmModule restLabShape
                             in case someNext of
                                    SomeInstrSeq next -> StepResult nextCtx (cprepend (unsafeCoerce next) nextParents)
                    else StepResult (ctx{values = rest}) nextControl
    Call _ _ -> undefined
    Leave ->
        case labels ctx of
            ConsLabels _ restLabels ->
                let newState = ctx{labels = restLabels}
                 in StepResult newState nextControl

unreachable :: a
unreachable = undefined

stepUnaryOp ::
    (RuntimeTypeOf typeIn -> RuntimeTypeOf typeOut) ->
    RuntimeContext (typeIn :~ l ': initialVal) locals wasmModule initialLab ->
    ControlStack
        (typeOut :~ l ': initialVal)
        finalVal
        locals
        finalLocals
        wasmModule
        finalWasmModule
        initialLab
        finalLab ->
    StepResult (typeIn :~ l ': initialVal) finalVal locals finalLocals wasmModule finalWasmModule initialLab finalLab
stepUnaryOp op ctx nextControl = case values ctx of
    ConsValues (_secLevel, val) rest ->
        let newCtx = ctx{values = ConsValues (_secLevel, op val) rest}
         in StepResult newCtx nextControl

-- TODO: double check the operand order
stepBinaryOp ::
    forall
        lRhs
        typeRhs
        lLhs
        typeLhs
        typeResult
        restStack
        locals
        finalLocals
        wasmModule
        finalWasmModule
        initialLab
        finalVal
        finalLab.
    (RuntimeTypeOf typeLhs -> RuntimeTypeOf typeRhs -> RuntimeTypeOf typeResult) ->
    RuntimeContext ((typeRhs :~ lRhs) ': (typeLhs :~ lLhs) ': restStack) locals wasmModule initialLab ->
    ControlStack
        ((typeResult :~ (lRhs :/\ lLhs)) ': restStack)
        finalVal
        locals
        finalLocals
        wasmModule
        finalWasmModule
        initialLab
        finalLab ->
    StepResult
        ((typeRhs :~ lRhs) ': (typeLhs :~ lLhs) ': restStack)
        finalVal
        locals
        finalLocals
        wasmModule
        finalWasmModule
        initialLab
        finalLab
stepBinaryOp op ctx nextControl = case values ctx of
    ConsValues (secRhs, valRhs) (ConsValues (secLhs, valLhs) restVal) ->
        let newCtx = ctx{values = ConsValues (combineSecLevels secRhs secLhs, op valLhs valRhs) restVal}
         in StepResult newCtx nextControl




compareI32 :: (Int32 -> Int32 -> Bool) -> Int32 -> Int32 -> Int32
compareI32 op x y = fromIntegral (fromEnum (op x y))

compareU32 :: (Word32 -> Word32 -> Bool) -> Int32 -> Int32 -> Int32
compareU32 op = compareI32 (op `on` fromIntegral)

compareI64 :: (Int64 -> Int64 -> Bool) -> Int64 -> Int64 -> Int64
compareI64 op x y = fromIntegral (fromEnum (op x y))

compareU64 :: (Word64 -> Word64 -> Bool) -> Int64 -> Int64 -> Int64
compareU64 op = compareI64 (op `on` fromIntegral)

-- executeInstructionSequence :: InstructionSequence inputStack outputStack locals wasmModule inputLabels outputLabels
--                           -> RuntimeContext inputStack locals wasmModule inputLabels
--                           -> RuntimeContext outputStack locals wasmModule outputLabels
--                        --    -> RuntimeContext inputStack locals wasmModule (LenLabelStackShape inputLabels)
--                        --    -> RuntimeContext outputStack locals wasmModule (LenLabelStackShape outputLabels)
-- executeInstructionSequence instrSeq prevCtxt@(RuntimeContext inputStack prevLocals prevWasmModule prevLabels prevMemory) = case instrSeq of
--    End -> RuntimeContext inputStack prevLocals prevWasmModule prevLabels prevMemory
--    (instr :| rest) ->
--        let intermediateContext = step prevCtxt instr
--        in executeInstructionSequence rest intermediateContext

stepMany ::
    forall
        {shape :: WasmModuleShape}
        {initialVal :: ValStackShape}
        {locals :: LocalsShape}
        {outLocals :: LocalsShape}
        {wasmModule :: WasmModule shape}
        {finalWasmModule :: WasmModule shape}
        {initialLab :: LabelStackShape}
        {finalVal :: ValStackShape}
        {finalLab :: LabelStackShape}.
    RuntimeContext initialVal locals wasmModule initialLab ->
    InstructionSequence initialVal finalVal locals outLocals wasmModule finalWasmModule initialLab finalLab ->
    RuntimeContext finalVal outLocals finalWasmModule finalLab
stepMany ctx program = stepManyHelper ctx (CSingle program)

stepManyHelper ::
    forall
        {shape :: WasmModuleShape}
        {initialVal :: ValStackShape}
        {locals :: LocalsShape}
        {outLocals :: LocalsShape}
        {wasmModule :: WasmModule shape}
        {finalWasmModule :: WasmModule shape}
        {initialLab :: LabelStackShape}
        {finalVal :: ValStackShape}
        {finalLab :: LabelStackShape}.
    RuntimeContext initialVal locals wasmModule initialLab ->
    ControlStack initialVal finalVal locals outLocals wasmModule finalWasmModule initialLab finalLab ->
    RuntimeContext finalVal outLocals finalWasmModule finalLab
stepManyHelper ctx control =
    let res = step ctx control
     in case res of
            StepResult newCtx (CSingle End) -> newCtx
            StepResult newCtx newControl -> stepManyHelper newCtx newControl

--
-- executeFunction :: Function inputStack outputStack locals labels wasmModule
--                   -> RuntimeContext inputStack locals globals labels
--                   -> RuntimeContext outputStack locals globals labels
--                --    -> RuntimeContext inputStack locals globals (LenLabelStackShape labels)
--                --    -> RuntimeContext outputStack locals globals (LenLabelStackShape labels)
-- executeFunction func@(Function (FFuncTypeAnn params res) instrSeq) prevCtxt = undefined
--    -- let newCtxt = executeInstructionSequence instrSeq (prevCtxt { stack = NoValues, locals = params }) :: RuntimeContext Empty --locals globals labels
--    -- in newCtxt { stack = concatStacks res (stack prevCtxt) }

-- =============================================================================
-- Initializations
-- =============================================================================



-- combineSecLevelVal1 :: ValueStack finalVal1 
--                  -> ValueStack finalVal2
--                  -> ValueStack (CombineValSecTypes finalVal1 finalVal2)
-- combineSecLevelVal1 NoValues NoValues = NoValues
-- combineSecLevelVal1 (ConsValues (secLevel1, val1) rest1) (ConsValues (secLevel2, _val2) rest2) = ConsValues (combineSecLevels secLevel1 secLevel2, val1) (combineSecLevelVals rest1 rest2)
--     --  in (ConsValues (combineSecLevels secLevel1 secLevel2, val1) res1, ConsValues (combineSecLevels secLevel1 secLevel2, val2) res2)
-- combineSecLevelVal1 _ _ = error "combineSecLevelVals: stacks have different shapes"

-- change the unsafe coerce depending on which example your testing to Int32 or Int64
instance Show (ValueStack shape) where
    show NoValues = "[]"
    show (ConsValues v rest) =
        show (unsafeCoerce v :: Int32) ++ " : " ++ show rest

instance Show (Locals shape) where
    show NoLocals = "[]"
    show (ConsLocals (_secLevel, v) rest) =
        show (unsafeCoerce v :: Int32) ++ " : " ++ show rest

instance Show (KnownMutability m) where
    show SConst = "const"
    show SVar = "var"

instance Show (Globals shape) where
    show NoGlobals = "[]"
    show (ConsGlobals (_secLevel, v) mut rest) =
        show (unsafeCoerce v :: Int32) ++ " (" ++ show mut ++ ") : " ++ show rest

printMemArray :: MemoryArray -> String
printMemArray memArray =
    "[" ++ concatMap (\b -> if b /= 0 then show b ++ "," else ".") memArray ++ "]"

instance Show (Memory shape) where
    show NoMems = ""
    show (ConsMems m rest) =
        "MemArray : " ++ printMemArray m ++ show rest

calcSNat :: SNat n -> Int
calcSNat SZ = 0
calcSNat (SS n) = 1 + calcSNat n

instance Show (SNat n) where
    show n = show (calcSNat n)

instance Show (Label shape) where
    show :: Label shape -> String
    show (Label lHeight arity _) =
        "Label { height = "
            ++ show lHeight
            ++ ", arity = "
            ++ show arity
            ++ ", continuation = <instr seq> }"

instance Show (LabelStack labelshape) where
    show NoLabels = "[]"
    show (ConsLabels label rest) =
        "Label : " ++ show label ++ " : " ++ show rest

instance Show (RuntimeContext valuesShape localsShape wasmModule labelsShape) where
    show ctxt =
        "RuntimeContext { values = "
            ++ show (values ctxt)
            ++ ",\n"
            ++ "locals = "
            ++ show (locals ctxt)
            ++ ",\n"
            ++ "globals = "
            ++ show (globals ctxt)
            ++ ",\n"
            ++ "labels = "
            ++ show (labels ctxt)
            ++ ",\n"
            ++ "memories = "
            ++ show (memories ctxt)
            ++ " }\n"
