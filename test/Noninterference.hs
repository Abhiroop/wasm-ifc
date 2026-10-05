{- | The two-run noninterference property, tested over generated programs. No type can state
  noninterference, since it compares two runs, so it is tested here instead: a generated module
  that the elaborator accepts under a policy with a secret parameter, a secret global and a
  secret region of memory is run twice, with the same public input and different secrets, and
  when both runs finish they must agree on everything public: the result, the public global,
  and the memory bytes that both runs label public.

  The generator aims at what the lift-free rules decide differently from SecWasm's: values left
  on the stack across a secret branch, conditional branches out of several blocks, @br_table@,
  bounded loops, calls to an internal function whose labels inference chooses, and loads
  declared public that may read a secret byte (and then trap, which ends that pair of runs).
-}
module Noninterference (
    GeneratedModule (..),
    genModule,
    compileModule,
    policyText,
    Observation (..),
    observe,
    observeUnder,
    withPublicLoads,
    holdsValueAcrossBranch,
) where

import Data.Text (Text)
import Data.Word (Word32, Word8)
import Hedgehog (Gen)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

import Runtime.Instantiate (instantiate)
import Runtime.Module (Invocation (..), SomeModuleInst, Value (..), invokeExport, readGlobalExport, readMemoryLevels)
import Syntax.Functions (RawFunction (..))
import Syntax.Globals (RawGlobal (..))
import Syntax.Immediates
import Syntax.Indices
import Syntax.Instructions (RawInstr (..))
import Syntax.Module (Export (..), ExportDesc (..), RawMemory (..), RawModule (..))
import Syntax.Types
import Syntax.TypesIFC (SecLevel (..))
import Validation.Elaborate (elaborateModuleWith)
import Validation.Policy (parsePolicy)

-- | A statement: stack-neutral code.
data Stmt
    = SetLocal Word32 Expr
    | SetGlobal Word32 Expr
    | StoreAt Expr Expr
    | DropValue Expr
    | IfThen Expr [Stmt] [Stmt]
    | BlockOf [Stmt]
    | -- | a loop that runs its body a fixed number of times, counting in its own local
      LoopTimes Word32 Word32 [Stmt]
    | BranchIf Word32 Expr
    | BranchTable [Word32] Word32 Expr
    | -- | an unconditional branch, always the last statement of its sequence
      BranchOut Word32
    deriving stock (Show)

-- | An expression: code that pushes one i32.
data Expr
    = Literal Word32
    | GetLocal Word32
    | GetGlobal Word32
    | LoadAt SecLevel Expr
    | Binary BinaryOp Expr Expr
    | IfValue Expr Expr Expr
    | CallHelper Expr
    | -- | the value, left on the stack while the statements run in a block of their own
      Around Expr [Stmt]
    deriving stock (Show)

data BinaryOp = OpAdd | OpSub | OpMul | OpAnd | OpOr | OpXor | OpLtU
    deriving stock (Show)

{- | A module of two functions: an internal helper (function 0, @i32 -> i32@) and the exported
  @f@ (function 1, @i32 i32 -> i32@, the first parameter secret), with a public global (0), a
  secret global (1), and one page of memory whose bytes [32, 64) are a secret region.
-}
data GeneratedModule = GeneratedModule
    { helperBody :: ([Stmt], Expr)
    , mainBody :: ([Stmt], Expr)
    }
    deriving stock (Show)

-- | What the generator may do at a point of the program.
data Scope = Scope
    { readable :: [Word32]
    -- ^ the locals it may read
    , writable :: [Word32]
    -- ^ the locals it may write
    , counters :: [Word32]
    -- ^ the locals left for loop counters, one per nesting level
    , targets :: [Word32]
    -- ^ the labels a branch may name: blocks and @if@s without results
    , depth :: Word32
    -- ^ the number of enclosing labels
    , mayCall :: Bool
    }

-- | Enter a label: every target moves one further out; the new one is a target if it may be.
enter :: Bool -> Scope -> Scope
enter targetable scope =
    scope
        { targets = [0 | targetable] ++ map (+ 1) scope.targets
        , depth = scope.depth + 1
        }

genModule :: Gen GeneratedModule
genModule = do
    helper <- genBody (Scope [0, 1, 2] [0, 1, 2] [3, 4] [] 1 False)
    main <- genBody (Scope [0, 1, 2, 3] [0, 1, 2, 3] [4, 5] [] 1 True)
    pure (GeneratedModule helper main)
  where
    genBody scope = (,) <$> genStmts 3 scope <*> genExpr 3 scope

genStmts :: Int -> Scope -> Gen [Stmt]
genStmts size scope = do
    body <- Gen.list (Range.linear 0 3) (genStmt size scope)
    ending <- Gen.frequency [(6, pure []), (1, maybe [] (\t -> [BranchOut t]) <$> genTarget scope)]
    pure (body ++ ending)

genTarget :: Scope -> Gen (Maybe Word32)
genTarget scope = case scope.targets of
    [] -> pure Nothing
    ts -> Just <$> Gen.element ts

genStmt :: Int -> Scope -> Gen Stmt
genStmt size scope
    | size <= 0 = simple
    | otherwise =
        Gen.frequency
            ( [ (3, simple)
              , (2, IfThen <$> expr <*> genStmts (size - 1) (enter True scope) <*> genStmts (size - 1) (enter True scope))
              , (2, BlockOf <$> genStmts (size - 1) (enter True scope))
              ]
                ++ [(1, branchIf t) | t <- take 1 scope.targets]
                ++ [(1, branchTable) | not (null scope.targets)]
                ++ [ (1, LoopTimes counter <$> Gen.word32 (Range.linear 1 3) <*> genStmts (size - 1) (enter False scope {counters = more}))
                   | counter : more <- [scope.counters]
                   ]
            )
  where
    expr = genExpr (size - 1) scope
    simple =
        Gen.choice
            [ SetLocal <$> Gen.element scope.writable <*> expr
            , SetGlobal <$> Gen.element [0, 1] <*> expr
            , StoreAt <$> expr <*> expr
            , DropValue <$> expr
            ]
    branchIf _ = BranchIf <$> Gen.element scope.targets <*> expr
    branchTable = BranchTable <$> Gen.list (Range.linear 0 3) (Gen.element scope.targets) <*> Gen.element scope.targets <*> expr

genExpr :: Int -> Scope -> Gen Expr
genExpr size scope
    | size <= 0 = leaf
    | otherwise =
        Gen.frequency
            ( [ (4, leaf)
              , (3, Binary <$> Gen.element [OpAdd, OpSub, OpMul, OpAnd, OpOr, OpXor, OpLtU] <*> sub <*> sub)
              , (2, IfValue <$> sub <*> genExpr (size - 1) (enter False scope) <*> genExpr (size - 1) (enter False scope))
              , (1, LoadAt <$> Gen.element [Low, High] <*> sub)
              , (2, Around <$> sub <*> genStmts (size - 1) (enter True scope))
              ]
                ++ [(1, CallHelper <$> sub) | scope.mayCall]
            )
  where
    sub = genExpr (size - 1) scope
    leaf =
        Gen.choice
            [ Literal <$> Gen.word32 (Range.linear 0 64)
            , GetLocal <$> Gen.element scope.readable
            , GetGlobal <$> Gen.element [0, 1]
            ]

-- | The module, with the policy of 'policyText'.
compileModule :: GeneratedModule -> RawModule
compileModule generated =
    RawModule
        { types = [helperType, mainType]
        , imports = []
        , functions =
            [ RawFunction helperType [I32, I32, I32, I32] (body generated.helperBody)
            , RawFunction mainType [I32, I32, I32, I32] (secretIntoMemory ++ body generated.mainBody)
            ]
        , globals = [RawGlobal (GlobalType Mutable I32) [Const SI32 0], RawGlobal (GlobalType Mutable I32) [Const SI32 0]]
        , memories = [RawMemory (MemType AddrI32 (Limits 1 (Just 1)))]
        , tables = []
        , elementSegments = []
        , dataSegments = []
        , exports = [Export "f" (ExportFunc (FunctionIdx 1)), Export "public" (ExportGlobal (GlobalIdx 0))]
        , start = Nothing
        , customSections = []
        }
  where
    helperType = FuncType [I32] [I32]
    mainType = FuncType [I32, I32] [I32]
    body (stmts, result) = concatMap compileStmt stmts ++ compileExpr result
    -- the secret parameter, stored into the secret region, so the two runs' memories differ there
    secretIntoMemory = [Const SI32 32, LocalGet (LocalIdx 0), Store SI32 (MemArg 0 0)]

-- | The policy the generated modules are checked under.
policyText :: Text
policyText = "export f : H L -> L\nglobal 1 : H\nregion 32 64 : H\n"

compileStmt :: Stmt -> [RawInstr]
compileStmt stmt = case stmt of
    SetLocal i e -> compileExpr e ++ [LocalSet (LocalIdx i)]
    SetGlobal g e -> compileExpr e ++ [GlobalSet (GlobalIdx g)]
    StoreAt address value -> compileAddress address ++ compileExpr value ++ [Store SI32 (MemArg 0 0)]
    DropValue e -> compileExpr e ++ [Drop]
    IfThen c t e -> compileExpr c ++ [If noResult (concatMap compileStmt t) (concatMap compileStmt e)]
    BlockOf body -> [Block noResult (concatMap compileStmt body)]
    LoopTimes counter times body ->
        [ Const SI32 times
        , LocalSet (LocalIdx counter)
        , Loop noResult (concatMap compileStmt body ++ [LocalGet (LocalIdx counter), Const SI32 1, Sub SI32, LocalTee (LocalIdx counter), BrIf (LabelIdx 0)])
        ]
    BranchIf t e -> compileExpr e ++ [BrIf (LabelIdx t)]
    BranchTable ts d e -> compileExpr e ++ [BrTable (map LabelIdx ts) (LabelIdx d)]
    BranchOut t -> [Br (LabelIdx t)]
  where
    noResult = FuncType [] []

compileExpr :: Expr -> [RawInstr]
compileExpr expr = case expr of
    Literal n -> [Const SI32 n]
    GetLocal i -> [LocalGet (LocalIdx i)]
    GetGlobal g -> [GlobalGet (GlobalIdx g)]
    LoadAt level address -> compileAddress address ++ [Annotated level (Load SI32 (MemArg 0 0))]
    Binary op x y -> compileExpr x ++ compileExpr y ++ [binaryInstr op]
    IfValue c t e -> compileExpr c ++ [If (FuncType [] [I32]) (compileExpr t) (compileExpr e)]
    CallHelper e -> compileExpr e ++ [Call (FunctionIdx 0)]
    Around e stmts -> compileExpr e ++ [Block (FuncType [] []) (concatMap compileStmt stmts)]
  where
    binaryInstr OpAdd = Add SI32
    binaryInstr OpSub = Sub SI32
    binaryInstr OpMul = Mul SI32
    binaryInstr OpAnd = And SI32
    binaryInstr OpOr = Or SI32
    binaryInstr OpXor = Xor SI32
    binaryInstr OpLtU = Lt SI32 Unsigned

-- | An address in the first 64 bytes, aligned to four.
compileAddress :: Expr -> [RawInstr]
compileAddress address = compileExpr address ++ [Const SI32 60, And SI32]

{- | The module with every load declared public: under the empty policy it has no secret at
  all, so it is accepted however its locals are typed, and no load traps on a level.
-}
withPublicLoads :: GeneratedModule -> GeneratedModule
withPublicLoads generated = GeneratedModule (body generated.helperBody) (body generated.mainBody)
  where
    body (stmts, result) = (map stmt stmts, expr result)
    stmt s = case s of
        SetLocal i e -> SetLocal i (expr e)
        SetGlobal g e -> SetGlobal g (expr e)
        StoreAt a v -> StoreAt (expr a) (expr v)
        DropValue e -> DropValue (expr e)
        IfThen c t e -> IfThen (expr c) (map stmt t) (map stmt e)
        BlockOf b -> BlockOf (map stmt b)
        LoopTimes counter times b -> LoopTimes counter times (map stmt b)
        BranchIf t e -> BranchIf t (expr e)
        BranchTable ts d e -> BranchTable ts d (expr e)
        BranchOut t -> BranchOut t
    expr e = case e of
        LoadAt _ a -> LoadAt Low (expr a)
        Binary op x y -> Binary op (expr x) (expr y)
        IfValue c t f -> IfValue (expr c) (expr t) (expr f)
        CallHelper x -> CallHelper (expr x)
        Around x stmts -> Around (expr x) (map stmt stmts)
        other -> other

{- | Whether the module holds a value on the stack across a conditional branch out of a block:
  the shape in which the lift-free rules and SecWasm's differ.
-}
holdsValueAcrossBranch :: GeneratedModule -> Bool
holdsValueAcrossBranch generated = any bodyHolds [generated.helperBody, generated.mainBody]
  where
    bodyHolds (stmts, result) = any stmtHolds stmts || exprHolds result
    stmtHolds stmt = case stmt of
        SetLocal _ e -> exprHolds e
        SetGlobal _ e -> exprHolds e
        StoreAt a v -> exprHolds a || exprHolds v
        DropValue e -> exprHolds e
        IfThen c t e -> exprHolds c || any stmtHolds t || any stmtHolds e
        BlockOf body -> any stmtHolds body
        LoopTimes _ _ body -> any stmtHolds body
        BranchIf _ e -> exprHolds e
        BranchTable _ _ e -> exprHolds e
        BranchOut _ -> False
    exprHolds expr = case expr of
        Around e stmts -> any branches stmts || exprHolds e || any stmtHolds stmts
        LoadAt _ a -> exprHolds a
        Binary _ x y -> exprHolds x || exprHolds y
        IfValue c t e -> exprHolds c || exprHolds t || exprHolds e
        CallHelper e -> exprHolds e
        _ -> False
    branches stmt = case stmt of
        BranchIf {} -> True
        BranchTable {} -> True
        IfThen _ t e -> any branches t || any branches e
        BlockOf body -> any branches body
        LoopTimes _ _ body -> any branches body
        _ -> False

-- | What the attacker sees of a run that finished: the result, the public global, and memory.
data Observation = Observation
    { result :: [Value]
    , publicGlobal :: Value
    , memory :: [(Word8, SecLevel)]
    }
    deriving stock (Show)

{- | Validate the module under the policy of 'policyText', run @f@ on a secret and a public
  argument, and observe the run: 'Left' if the module is rejected, 'Right Nothing' if the run
  traps or calls out.
-}
observe :: RawModule -> Word32 -> Word32 -> Either String (Maybe Observation)
observe = observeUnder policyText

-- | 'observe' under a policy given as text.
observeUnder :: Text -> RawModule -> Word32 -> Word32 -> Either String (Maybe Observation)
observeUnder text m secret public = do
    policy <- either (Left . show) Right (parsePolicy text)
    validated <- either (Left . show) Right (elaborateModuleWith policy m)
    inst <- either (Left . show) Right (instantiate validated)
    pure $ case invokeExport inst "f" [I32Value secret, I32Value public] of
        Right (Returned after results) -> observed after results
        _ -> Nothing
  where
    observed :: SomeModuleInst -> [Value] -> Maybe Observation
    observed after results = Observation results <$> either (const Nothing) Just (readGlobalExport after "public") <*> readMemoryLevels after 0 64
