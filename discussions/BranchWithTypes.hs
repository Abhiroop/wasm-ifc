{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
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

data Label (initialVal :: [WasmType]) where
    Label :: InstrSeq initialVal initialLab finalVal finalLab -> Label initialVal

data LabelStack (shape :: [[WasmType]]) where
    NoLabels :: LabelStack '[]
    PushLabel :: Label topShape -> LabelStack restShape -> LabelStack (topShape ': restShape)

data SomeLabelStack = forall top rest. SomeLabelStack (Label top) (LabelStack rest)

popNLabels :: Int -> LabelStack shape -> SomeLabelStack
popNLabels 0 (PushLabel lab rest) = SomeLabelStack lab rest
popNLabels n (PushLabel _ rest) = popNLabels (n-1) rest
popNLabels _ NoLabels = error "Branch depth exceeds label stack"

data Instr (values :: [WasmType]) (labels :: [[WasmType]]) (values' :: [WasmType]) (labels' :: [[WasmType]]) where
    I32Const :: Int -> Instr values labels (I32 ': values) labels
    I32Add :: Instr (I32 ': I32 ': values) labels (I32 ': values) labels
    Block :: InstrSeq values (values ': labels) values' labels -> Instr values labels values' labels
    Loop :: InstrSeq values (values ': labels) values labels -> Instr values labels values labels
    Br :: Int -> Instr values labels values' labels'

data InstrSeq initialVal initialLab finalVal finalLab where
    Halt :: InstrSeq initialVal initialLab initialVal initialLab
    (:|) :: Instr initialVal initialLab middleVal middleLab 
            -> InstrSeq middleVal middleLab finalVal finalLab 
            -> InstrSeq initialVal initialLab finalVal finalLab

data State (valuesShape :: [WasmType]) (labelsShape :: [[WasmType]]) = State
    { values :: ValueStack valuesShape
    , labels :: LabelStack labelsShape
    }

pushValue :: RuntimeTypeOf top -> State values labels -> State (top ': values) labels
pushValue value state = state { values = PushValue value (values state) }

pushLabel :: Label top -> State values labels -> State values (top ': labels)
pushLabel label state = state { labels = PushLabel label (labels state) }

data ControlStack (initialVal :: [WasmType]) (initialLab :: [[WasmType]]) (finalVal :: [WasmType]) (finalLab :: [[WasmType]]) where
    CSingle :: InstrSeq initialVal initialLab finalVal finalLab -> ControlStack initialVal initialLab finalVal finalLab
    CCons   :: InstrSeq initialVal initialLab middleVal middleLab -> ControlStack middleVal middleLab finalVal finalLab -> ControlStack initialVal initialLab finalVal finalLab

data SomeControlStack finalVal finalLab = forall initialVal initialLab. 
    SomeControlStack (ControlStack initialVal initialLab finalVal finalLab)

popNFrames :: Int -> ControlStack initialVal initialLab finalVal finalLab -> SomeControlStack finalVal finalLab
popNFrames 0 control = SomeControlStack control
popNFrames n (CCons _ rest) = popNFrames (n-1) rest
popNFrames _ (CSingle _) = error "Branch depth exceeds control stack"

data StepResult (initialVal :: [WasmType]) (initialLab :: [[WasmType]]) (finalVal :: [WasmType]) (finalLab :: [[WasmType]]) = forall middleVal middleLab.
    StepResult (State middleVal middleLab) (ControlStack middleVal middleLab finalVal finalLab)

-- TODO
step :: forall initialVal initialLab finalVal finalLab. 
    State initialVal initialLab
    -> ControlStack initialVal initialLab finalVal finalLab
    -> StepResult initialVal initialLab finalVal finalLab
step state (CSingle Halt) = StepResult state (CSingle Halt)
step state (CSingle (instruction :| rest)) = stepInternal state instruction (CSingle rest)
step state (CCons Halt parents) = StepResult state parents
step state (CCons (instruction :| rest) parents) = stepInternal state instruction (CCons rest parents)

stepInternal :: forall initialVal initialLab middleVal middleLab finalVal finalLab.
    State initialVal initialLab
    -> Instr initialVal initialLab middleVal middleLab
    -> ControlStack middleVal middleLab finalVal finalLab
    -> StepResult initialVal initialLab finalVal finalLab
stepInternal state instruction nextControl = case instruction of
    I32Const value -> 
        StepResult (pushValue value state) nextControl
    I32Add -> 
        case values state of
            PushValue rhs (PushValue lhs restVal) -> 
                let newState = state { values = PushValue (lhs + rhs) restVal } 
                in StepResult newState nextControl
    Block body ->
        let newState = pushLabel (Label Halt) state
        in StepResult newState (CCons body nextControl)
    Loop body ->
        let newState = pushLabel (Label (Loop body :| Halt)) state
        in StepResult newState (CCons body nextControl)
    Br depth -> 
        case popNLabels depth (labels state) of
            SomeLabelStack targetLab restLab ->
                case targetLab of
                    Label next ->
                        case popNFrames depth nextControl of
                            SomeControlStack nextParents ->
                                let nextState = state { labels = restLab }
                                in StepResult nextState (CCons next nextParents)