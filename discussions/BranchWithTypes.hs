{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module BranchWithTypes where

import Data.Kind (Type)
import Unsafe.Coerce    --- !!! WARNING

data WasmType = I32

type family RuntimeTypeOf (wasmType :: WasmType) :: Type where
    RuntimeTypeOf I32 = Int

data ValueStack (shape :: [WasmType]) where
    NoValues :: ValueStack '[]
    PushValue :: (RuntimeTypeOf top) -> ValueStack shape -> ValueStack (top ': shape)

data Instr (values :: [WasmType]) (values' :: [WasmType]) where
    I32Const :: Int -> Instr values (I32 ': values)
    I32Add :: Instr (I32 ': I32 ': values) (I32 ': values)
    Block :: InstrSeq values values' -> Instr values values'
    Loop :: InstrSeq values values -> Instr values values
    Br :: Int -> Instr values values

data InstrSeq initial final where
    Halt :: InstrSeq initial initial
    (:|) :: Instr initial middle -> InstrSeq middle final -> InstrSeq initial final

data SomeInstrSeq where
    SomeInstrSeq :: InstrSeq initial final -> SomeInstrSeq

newtype Label = Label
    { continuation :: SomeInstrSeq }

data State (valuesShape :: [WasmType]) = State
    { values :: ValueStack valuesShape
    , labels :: [Label] 
    }

pushValue :: RuntimeTypeOf top -> State values -> State (top ': values)
pushValue value state = state { values = PushValue value (values state) }

pushLabel :: Label -> State values -> State values
pushLabel label state = state { labels = label : labels state }

-- Lean: inductive ControlStack : Shape -> Shape -> Type where
--   | single : InstrSeq i f -> ControlStack i f
--   | cons : InstrSeq i m -> ControlStack m f -> ControlStack i f
data ControlStack (initial :: [WasmType]) (final :: [WasmType]) where
    CSingle :: InstrSeq initial final -> ControlStack initial final
    CCons   :: InstrSeq initial middle -> ControlStack middle final -> ControlStack initial final

data SomeControlStack final = forall initial . SomeControlStack (ControlStack initial final)

popNFrames :: Int -> ControlStack initial final -> SomeControlStack final
popNFrames 0 control = SomeControlStack control
popNFrames n (CCons _ rest) = popNFrames (n-1) rest
popNFrames _ (CSingle _) = error "Branch depth exceeds control stack"

-- Lean: def step (init : State i) (stack : ControlStack i f) : 
--         (m : Shape) × State m × ControlStack m f
data StepResult (initial :: [WasmType]) (final :: [WasmType]) = forall middle .
    StepResult (State middle) (ControlStack middle final)

-- TODO
step :: forall initial final . State initial -> ControlStack initial final -> StepResult initial final
step state (CSingle Halt) = StepResult state (CSingle Halt)
step state (CSingle (instruction :| rest)) = stepInternal state instruction (CSingle rest)
step state (CCons Halt parents) = StepResult state parents
step state (CCons (instruction :| rest) parents) = stepInternal state instruction (CCons rest parents)

stepInternal :: forall initial middle final .
    State initial ->
    Instr initial middle ->
    ControlStack middle final ->
    StepResult initial final
stepInternal state instruction nextControl = case instruction of
    I32Const value -> 
        StepResult (pushValue value state) nextControl
    I32Add -> 
        case values state of
            PushValue rhs (PushValue lhs restValues) -> 
                let newState = state { values = PushValue (lhs + rhs) restValues } 
                in StepResult newState nextControl
    Block body ->
        let newState = pushLabel (Label (SomeInstrSeq Halt)) state
        in StepResult newState (CCons body nextControl)
    Loop body ->
        let newState = pushLabel (Label (SomeInstrSeq (Loop body :| Halt))) state
        in StepResult newState (CCons body nextControl)
    Br depth -> 
        case drop depth (labels state) of
            [] -> undefined
            targetLabel : restLabels ->
                case continuation targetLabel of
                    SomeInstrSeq next ->
                        case popNFrames depth nextControl of
                            SomeControlStack nextParents ->
                                let nextState = state { labels = restLabels }
                                in StepResult nextState (CCons (unsafeCoerce next) nextParents)