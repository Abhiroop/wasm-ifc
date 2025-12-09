{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module BranchWithTypes where

import Data.Kind (Type)

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

data InstrSeq values values' where
    Halt :: InstrSeq values values
    (:|) :: Instr values values'' -> InstrSeq values'' values' -> InstrSeq values values'

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

data SomeState where
    SomeState :: State values -> SomeState

-- TODO
step :: State initial -> InstrSeq initial final -> [SomeInstrSeq] -> (SomeState, [SomeInstrSeq])
step state Halt parents = (SomeState state, parents)
step state (current :| rest) parents = case current of
    I32Const value ->
        (SomeState (pushValue value state), SomeInstrSeq rest : parents)

    I32Add ->
        undefined

    Block body ->
        let state' = pushLabel (Label $ SomeInstrSeq Halt) state
        in (SomeState state', SomeInstrSeq body : SomeInstrSeq rest : parents)

    Loop body ->
        let state' = pushLabel (Label $ SomeInstrSeq body) state
        in (SomeState state', SomeInstrSeq body : SomeInstrSeq rest : parents)

    Br depth ->
        let ((Label next) : restLabels) = drop depth (labels state)
            (_ : nextParents) = drop depth (SomeInstrSeq rest : parents)
            state' = state { labels = restLabels }
        in (SomeState state', if next == SomeInstrSeq Halt then nextParents else next : nextParents) 

run :: InstrSeq '[] final -> SomeState
run program = stepToCompletion (State NoValues []) program []
    where stepToCompletion :: State initial -> InstrSeq initial final ->  [SomeInstrSeq] -> SomeState
          stepToCompletion state current parents =
            let (state', parents') = step state current parents
            in if null parents' then state' else stepToCompletion state' (head parents') (tail parents')

test :: IO ()
test = do
    let program = 
               I32Const 5
            :| Block (I32Const 10 :| I32Add :| Br 0 :| I32Const 99)
            :| I32Const 20
            :| I32Add
    let result = run program
    print result
