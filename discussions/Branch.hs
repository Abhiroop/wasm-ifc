module Branch where

data Instr =
      I32Const Int
    | I32Add
    | Block InstrSeq
    | Loop InstrSeq
    | Br Int
    deriving (Show, Eq)

type InstrSeq = [Instr]

newtype Label = Label
    { continuation :: InstrSeq }
    deriving (Show)

data State = State
    { values :: [Int]
    , labels :: [Label] 
    }
    deriving (Show)

pushValue :: Int -> State -> State
pushValue value state = state { values = value : values state }

pushLabel :: Label -> State -> State
pushLabel label state = state { labels = label : labels state }

step :: State -> [InstrSeq] -> (State, [InstrSeq])
step state [] = (state, [])
step state ([] : parents) = (state, parents)
step state ((current : rest) : parents) = case current of
    I32Const value ->
        (pushValue value state, rest : parents)

    I32Add ->
        (state { values = (lhs + rhs) : restValues }, rest : parents)
        where (rhs : lhs : restValues) = values state

    Block body ->
        let state' = pushLabel (Label []) state
        in (state', body : rest : parents)

    Loop body ->
        let state' = pushLabel (Label [Loop body]) state
        in (state', body : rest : parents)

    Br depth ->
        let (targetLabel : restLabels) = drop depth (labels state)
            (_ : nextParents) = drop depth (rest : parents)
            state' = state { labels = restLabels }
            next = continuation targetLabel
        in (state', if null next then nextParents else next : nextParents)

run :: InstrSeq -> State
run program = stepToCompletion (State [] []) [program]
    where stepToCompletion state parents =
            let (state', parents') = step state parents
            in if null parents' then state' else stepToCompletion state' parents'

test :: IO ()
test = do
    let program = 
            [I32Const 5, 
             Block [I32Const 10, I32Add, Br 0, I32Const 99], 
             I32Const 20, 
             I32Add]
    let result = run program
    print result
