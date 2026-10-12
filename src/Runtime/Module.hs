{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

{- | Instantiated modules, and the boundary for invoking their exports from the outside world.
  Arguments and results cross it as tagged, term-level 'Value's — so the CLI and test harnesses
  need no type-level machinery — and are checked against the export's type on the way in.
  Lists of values are in declared order here; the stack the function sees has the last
  argument on top (see "Validation.Shape" on stack order).
-}
module Runtime.Module (
    SomeModuleInst (..),
    Value (..),
    valueType,
    renderValue,
    RunError (..),
    Invocation (..),
    SomeHostRequest (..),
    ForeignCall (..),
    foreignCall,
    ForeignTarget (..),
    targetNames,
    answerForeign,
    exportSignature,
    exportedGlobal,
    fromValue,
    exportedResultLevels,
    exportedGlobalLevel,
    readMemoryLevels,
    readTable,
    invokeExport,
    readGlobalExport,
    continueWith,

    -- * An instance among others
    Instance,
    instanceOf,
    instanceModule,
    Progress (..),
    enterFunction,
    resumeInstance,
    abandonCall,
    exportOf,
    functionType,
    GivenMemory (..),
    GivenTable (..),
    memoryAt,
    putMemoryAt,
    tableAt,
    putTableAt,
    globalAt,
    putGlobalAt,
) where

import Data.Bifunctor (first)
import Data.Maybe (fromMaybe)
import Data.Singletons (Sing, fromSing)
import Data.Singletons.Base.TH (SList (SCons, SNil))
import Data.Text (Text)
import Data.Word (Word32, Word64, Word8)

import Numeric (showHex)
import Runtime.Interpreter (Config, ForeignTarget (..), FuncSpaceInst, Halt (..), HostRequest (..), ModuleInst (..), Outcome (..), Store (..), Suspended, getFunc, moduleToStore, resumeWith, run, runFunction, runKeeping, startFunction, storeToModule)
import Runtime.MemInst (MemInst, levelOfRange, memoryPages, readBytes, retypeMemory)
import Runtime.Stack (GlobalSpaceInst (..), MemSpaceInst (..), TableInsts (..), TableSpaceInst (..), ValueStack (..), getGlobal)
import Runtime.TableInst (TableInst, readEntries, tableSize)
import Runtime.Trap (Trap)
import Syntax.Immediates (HostType, Reference, Vector128 (..), isNullReference, referent)
import Syntax.Indices (FunctionIdx (..), GlobalIdx (..))
import Syntax.Module (Export (..), ExportDesc (..))
import Syntax.Types
import Syntax.TypesIFC
import Validation.Reflect (SomeGlobalRef (..), declaredOrder, funcTypesSing, globalTypesSing, lookupFuncRef, lookupGlobalRef, stackOrder)
import Validation.Shape

{- | An instantiated module with its shape hidden: the shape's singleton, the instance, and
the exports (for resolving entry points).
-}
data SomeModuleInst where
    SomeModuleInst :: Sing (shape :: ModuleShape) -> ModuleInst shape -> [Export] -> SomeModuleInst

-- | A WebAssembly value with its type as a tag, for crossing the invocation boundary.
data Value
    = I32Value Word32
    | I64Value Word64
    | F32Value Float
    | F64Value Double
    | V128Value Vector128
    | FuncRefValue Reference
    | ExternRefValue Reference
    | ExnRefValue Reference
    deriving stock (Eq, Show)

valueType :: Value -> ValType
valueType (I32Value _) = I32
valueType (I64Value _) = I64
valueType (F32Value _) = F32
valueType (F64Value _) = F64
valueType (V128Value _) = V128
valueType (FuncRefValue _) = FuncRef
valueType (ExternRefValue _) = ExternRef
valueType (ExnRefValue _) = ExnRef

-- | Integers as unsigned decimals (the raw bits), floats as Haskell shows them, references by index.
renderValue :: Value -> String
renderValue (I32Value w) = show w
renderValue (I64Value w) = show w
renderValue (F32Value f) = show f
renderValue (F64Value d) = show d
renderValue (V128Value (Vector128 low high)) = "0x" ++ concatMap (\word -> let digits = showHex word "" in replicate (16 - length digits) '0' ++ digits) [high, low]
renderValue (FuncRefValue r) = maybe "null" (\index -> "func " ++ show index) (referent r)
renderValue (ExternRefValue r) = maybe "null" (\index -> "extern " ++ show index) (referent r)
renderValue (ExnRefValue r) = maybe "null" (\index -> "exception " ++ show index) (referent r)

{- | A call the module made out of itself: to a function it imports or to one of another
  instance that a reference names. The arguments are in declared order; the types are the ones
  the call expects of the function.
-}
data ForeignCall = ForeignCall
    { target :: ForeignTarget
    , expected :: FuncType
    , arguments :: [Value]
    }

-- | The call a suspended invocation waits on, if it is one to an embedder's function.
foreignCall :: SomeHostRequest -> Maybe ForeignCall
foreignCall (SomeHostRequest _ _ _ _ request) = case request of
    ForeignRequest target psS _ args rsS _ _ ->
        Just (ForeignCall target (FuncType (declaredOrder (unlabelledTypes psS)) (declaredOrder (unlabelledTypes rsS))) (declaredOrder (toValues psS args)))
    HostRequest {} -> Nothing

{- | Continue an invocation suspended on a call to an embedder's function, with that
  function's results in declared order; they must have the types the import declares.
-}
answerForeign :: SomeHostRequest -> [Value] -> Either RunError Invocation
answerForeign (SomeHostRequest shapeS funcs exports rsS request) results = case request of
    ForeignRequest target _ _ _ resultTypes store suspended -> do
        answered <- note (uncurry ForeignResultMismatch (targetNames target)) (if map valueType results == declaredOrder (unlabelledTypes resultTypes) then buildStack resultTypes (stackOrder results) else Nothing)
        continueWith shapeS funcs exports rsS (resumeWith store answered suspended)
    HostRequest {} -> Left (ForeignResultMismatch "" "")

-- | The names a call out of a module is reported under: those of the import, or none for a reference.
targetNames :: ForeignTarget -> (Text, Text)
targetNames (ImportedAs moduleName fieldName) = (moduleName, fieldName)
targetNames (ReferencedBy _) = ("", "a function reference")

data RunError
    = -- | no export of that name and kind (a function to invoke, a global to read)
      NoSuchExport Text
    | -- | a call to an embedder's function (module, name) that nothing answered
      ForeignCallUnanswered Text Text
    | -- | the answer to a call to an embedder's function has not the results it declares
      ForeignResultMismatch Text Text
    | -- | expected and actual number of arguments
      ArgumentCount Int Int
    | -- | the argument at this (zero-based) position should have the first type, has the second
      ArgumentType Int ValType ValType
    | Trapped Trap
    | -- | the function called into the host, and the caller had no host to offer
      HostCallNotServed
    | {- | an exception left a function that another module had called. A tag belongs to one
      module here, so the caller could catch it only by a clause for all exceptions, and the
      linker does not carry it over ("Runtime.Link").
      -}
      ExceptionAcrossModules
    deriving stock (Eq, Show)

{- | How an invocation ends, short of a trap: with its results and the module as the call left
  it, or suspended on a call into the host. The pure core stops there; a driver (see
  "Runtime.Wasi") performs the call and continues with 'continueWith'.
-}
data Invocation
    = Returned SomeModuleInst [Value]
    | CalledHost SomeHostRequest

{- | A pending host call together with everything needed to resume the module afterwards:
  its shape witness, its functions, its exports, and the result type of the invocation.
-}
data SomeHostRequest where
    SomeHostRequest ::
        Sing (shape :: ModuleShape) ->
        FuncSpaceInst shape (ModuleFuncs shape) ->
        [Export] ->
        Sing (rs :: [LabelledValType]) ->
        HostRequest shape rs ->
        SomeHostRequest

-- | The type of an exported function, parameters and results in declared order.
exportSignature :: SomeModuleInst -> Text -> Maybe FuncType
exportSignature (SomeModuleInst shapeS _ exports) name = do
    FunctionIdx idx <- exportedFuncIndex name exports
    SomeFuncRef _ psS rsS _ <- lookupFuncRef (funcTypesSing shapeS) idx
    pure (FuncType (declaredOrder (unlabelledTypes psS)) (declaredOrder (unlabelledTypes rsS)))

{- | Run an exported function on arguments given in declared order; results likewise. The
  module comes back with the globals and memories the call left behind, so a sequence of
  invocations shares state as the spec's instance does.
-}
invokeExport :: SomeModuleInst -> Text -> [Value] -> Either RunError Invocation
invokeExport (SomeModuleInst shapeS inst exports) name args = do
    FunctionIdx idx <- note (NoSuchExport name) (exportedFuncIndex name exports)
    SomeFuncRef _ psS rsS funcIx <- note (NoSuchExport name) (lookupFuncRef (funcTypesSing shapeS) idx)
    checkArguments (declaredOrder (unlabelledTypes psS)) args
    argStack <- note (ArgumentCount 0 0) (buildStack psS (stackOrder args))
    outcome <- first Trapped (runFunction rsS inst (getFunc funcIx inst.functions) argStack)
    pure $ case outcome of
        Completed inst' results -> Returned (SomeModuleInst shapeS inst' exports) (declaredOrder (toValues rsS results))
        NeedsHost request -> CalledHost (SomeHostRequest shapeS inst.functions exports rsS request)

{- | Continue a suspended invocation from the configuration the host's answer produced (see
  'Runtime.Interpreter.resumeWith'); it may finish, or call the host again.
-}
continueWith ::
    Sing (shape :: ModuleShape) ->
    FuncSpaceInst shape (ModuleFuncs shape) ->
    [Export] ->
    Sing (rs :: [LabelledValType]) ->
    Config shape rs ->
    Either RunError Invocation
continueWith shapeS funcs exports rsS config = do
    halt <- first Trapped (run funcs config)
    pure $ case halt of
        Finished store results ->
            Returned (SomeModuleInst shapeS (storeToModule funcs store) exports) (declaredOrder (toValues rsS results))
        AwaitingHost request -> CalledHost (SomeHostRequest shapeS funcs exports rsS request)

{- | The levels of an exported function's results, in declared order. Whoever invokes the
  export observes them, so a driver that enforces the policy delivers only public ones.
-}
exportedResultLevels :: SomeModuleInst -> Text -> Maybe [SecLevel]
exportedResultLevels (SomeModuleInst shapeS _ exports) name = do
    FunctionIdx idx <- exportedFuncIndex name exports
    SomeFuncRef _ _ rsS _ <- lookupFuncRef (funcTypesSing shapeS) idx
    pure (declaredOrder [level | _ :~ level <- fromSing rsS])

-- | The level of an exported global, which whoever reads it observes (see 'exportedResultLevels').
exportedGlobalLevel :: SomeModuleInst -> Text -> Maybe SecLevel
exportedGlobalLevel (SomeModuleInst shapeS _ exports) name = do
    GlobalIdx idx <- exportedGlobalIndex name exports
    SomeGlobalRef _ (_ :%~ level) _ <- lookupGlobalRef (globalTypesSing shapeS) idx
    pure (fromSing level)

{- | The bytes of memory 0 in a range, each with its level, or 'Nothing' if the module has no
  memory or the range is out of bounds: what an observer of the memory's public part sees
  once the module has run (the bytes labelled 'Low').
-}
readMemoryLevels :: SomeModuleInst -> Int -> Int -> Maybe [(Word8, SecLevel)]
readMemoryLevels (SomeModuleInst _ inst _) addr count = case inst.memories of
    MCons mem _ -> do
        bytes <- readBytes mem addr count
        pure (zip bytes [levelOfRange mem a 1 | a <- [addr .. addr + count - 1]])
    MNil -> Nothing

-- | The entries of a table, by its index: for tests that compare what two runs left in it.
readTable :: SomeModuleInst -> Word32 -> Maybe [Reference]
readTable (SomeModuleInst _ inst _) = entriesAt inst.tables.instances
  where
    entriesAt :: TableInsts ts -> Word32 -> Maybe [Reference]
    entriesAt TNil _ = Nothing
    entriesAt (TCons table _) 0 = readEntries 0 (tableSize table) table
    entriesAt (TCons _ rest) n = entriesAt rest (n - 1)

-- | Whether an exported global may be written, and its current value.
exportedGlobal :: SomeModuleInst -> Text -> Maybe (Mutability, Value)
exportedGlobal (SomeModuleInst shapeS inst exports) name = do
    GlobalIdx idx <- exportedGlobalIndex name exports
    SomeGlobalRef smut (st :%~ _) globalIx <- lookupGlobalRef (globalTypesSing shapeS) idx
    pure (fromSing smut, toValue st (getGlobal globalIx inst.globals))

-- | The current value of an exported global (the spec's @get@ action).
readGlobalExport :: SomeModuleInst -> Text -> Either RunError Value
readGlobalExport (SomeModuleInst shapeS inst exports) name = do
    GlobalIdx idx <- note (NoSuchExport name) (exportedGlobalIndex name exports)
    SomeGlobalRef _ (st :%~ _) globalIx <- note (NoSuchExport name) (lookupGlobalRef (globalTypesSing shapeS) idx)
    Right (toValue st (getGlobal globalIx inst.globals))

exportedFuncIndex :: Text -> [Export] -> Maybe FunctionIdx
exportedFuncIndex name exports =
    case [idx | Export n (ExportFunc idx) <- exports, n == name] of
        (idx : _) -> Just idx
        [] -> Nothing

exportedGlobalIndex :: Text -> [Export] -> Maybe GlobalIdx
exportedGlobalIndex name exports =
    case [idx | Export n (ExportGlobal idx) <- exports, n == name] of
        (idx : _) -> Just idx
        [] -> Nothing

-- | Arguments must match the parameters one to one, in declared order.
checkArguments :: [ValType] -> [Value] -> Either RunError ()
checkArguments params args
    | length params /= length args = Left (ArgumentCount (length params) (length args))
    | otherwise = mapM_ check (zip3 [0 ..] params args)
  where
    check (i, param, arg)
        | valueType arg == param = Right ()
        | otherwise = Left (ArgumentType i param (valueType arg))

{- | Build the typed argument stack from values already in stack order. Total once
  'checkArguments' has passed; the 'Nothing' is only the count/type mismatch it rules out.
-}

-- | The value types of a labelled stack: what the outside world, which knows no levels, sees.
unlabelledTypes :: Sing (s :: [LabelledValType]) -> [ValType]
unlabelledTypes = map unlabelled . fromSing

buildStack :: Sing (ps :: [LabelledValType]) -> [Value] -> Maybe (ValueStack ps)
buildStack SNil [] = Just VNil
buildStack (SCons (st :%~ _) rest) (v : vs) = (:#) <$> fromValue st v <*> buildStack rest vs
buildStack _ _ = Nothing

fromValue :: Sing (t :: ValType) -> Value -> Maybe (HostType t)
fromValue SI32 (I32Value w) = Just w
fromValue SI64 (I64Value w) = Just w
fromValue SF32 (F32Value f) = Just f
fromValue SF64 (F64Value d) = Just d
fromValue SV128 (V128Value v) = Just v
-- (A reference to a function names the instance it belongs to, so one from outside means the
-- same function here, or none; a call through one that names none traps. From outside, the
-- only reference to an exception is null: another names an exception in the module's store.)
fromValue SFuncRef (FuncRefValue r) = Just r
fromValue SExternRef (ExternRefValue r) = Just r
fromValue SExnRef (ExnRefValue r) | isNullReference r = Just r
fromValue _ _ = Nothing

toValues :: Sing (rs :: [LabelledValType]) -> ValueStack rs -> [Value]
toValues SNil VNil = []
toValues (SCons (st :%~ _) rest) (v :# vs) = toValue st v : toValues rest vs

toValue :: Sing (t :: ValType) -> HostType t -> Value
toValue SI32 = I32Value
toValue SI64 = I64Value
toValue SF32 = F32Value
toValue SF64 = F64Value
toValue SV128 = V128Value
toValue SFuncRef = FuncRefValue
toValue SExternRef = ExternRefValue
toValue SExnRef = ExnRefValue

note :: e -> Maybe a -> Either e a
note e = maybe (Left e) Right

{- * An instance among others

   What an embedder that links several modules needs of one of them: to enter it and be told
   when it calls out, to resume it when the call returns, and to read and replace the memories,
   tables and globals it shares with the others ("Runtime.Link").
-}

{- | An instance together with the calls out of it that have not returned, innermost first. A
  call out suspends the activation that made it; the instance may be entered again meanwhile
  (the function it called calls back), and that activation runs on the same state. The state
  is the instance's one store, which every activation continues from: what a nested one wrote
  is there when an outer one resumes, and what ran before a trap wrote stays written.
-}
data Instance where
    Instance :: Sing (shape :: ModuleShape) -> FuncSpaceInst shape (ModuleFuncs shape) -> [Export] -> Store shape -> [Pending shape] -> Instance

-- | An activation waiting for results of type @rs@, to finish a call whose own results are @res@.
data Pending (shape :: ModuleShape) where
    Pending :: Sing (res :: [LabelledValType]) -> Sing (rs :: [LabelledValType]) -> Suspended shape res rs -> Pending shape

instanceOf :: SomeModuleInst -> Instance
instanceOf (SomeModuleInst shapeS inst exports) = Instance shapeS inst.functions exports (moduleToStore inst) []

-- | The instance as it stands, for the readers of "Runtime.Module".
instanceModule :: Instance -> SomeModuleInst
instanceModule (Instance shapeS funcs exports store _) = SomeModuleInst shapeS (storeToModule funcs store) exports

-- | How far a call got: it returned, or it calls out and waits ('resumeInstance').
data Progress = Returns [Value] | Calls ForeignCall

{- | Call a function of the instance, by its index, with arguments in declared order. The
  instance comes back as the call left it, also when the call trapped.
-}
enterFunction :: Instance -> Word32 -> [Value] -> (Instance, Either RunError Progress)
enterFunction inst@(Instance shapeS funcs exports store pending) idx args = case lookupFuncRef (funcTypesSing shapeS) idx of
    Nothing -> (inst, Left (NoSuchExport "a function by its index"))
    Just (SomeFuncRef _ psS rsS funcIx) ->
        case checkArguments (declaredOrder (unlabelledTypes psS)) args >> note (ArgumentCount 0 0) (buildStack psS (stackOrder args)) of
            Left err -> (inst, Left err)
            Right argStack -> case startFunction rsS store (getFunc funcIx funcs) argStack of
                Left trap -> (inst, Left (Trapped trap))
                Right (Left request) -> suspendOn shapeS funcs exports pending rsS request
                Right (Right config) -> advance shapeS funcs exports pending rsS (runKeeping funcs config)

{- | Give the innermost waiting activation the results of its call, in declared order, and run
  it on from the instance's state as it is now.
-}
resumeInstance :: Instance -> [Value] -> (Instance, Either RunError Progress)
resumeInstance inst@(Instance shapeS funcs exports store pending) results = case pending of
    [] -> (inst, Left HostCallNotServed)
    Pending resS rsS suspended : outer ->
        case if map valueType results == declaredOrder (unlabelledTypes rsS) then buildStack rsS (stackOrder results) else Nothing of
            Nothing -> (Instance shapeS funcs exports store outer, Left (ForeignResultMismatch "" "a call out of the module"))
            Just answered -> advance shapeS funcs exports outer resS (runKeeping funcs (resumeWith store answered suspended))

-- | Drop the innermost waiting activation: its call trapped, and so does it.
abandonCall :: Instance -> Instance
abandonCall (Instance shapeS funcs exports store pending) = Instance shapeS funcs exports store (drop 1 pending)

advance ::
    Sing (shape :: ModuleShape) ->
    FuncSpaceInst shape (ModuleFuncs shape) ->
    [Export] ->
    [Pending shape] ->
    Sing (res :: [LabelledValType]) ->
    Either (Trap, Store shape) (Halt shape res) ->
    (Instance, Either RunError Progress)
advance shapeS funcs exports pending resS outcome = case outcome of
    Left (trap, store) -> (Instance shapeS funcs exports store pending, Left (Trapped trap))
    Right (Finished store results) -> (Instance shapeS funcs exports store pending, Right (Returns (declaredOrder (toValues resS results))))
    Right (AwaitingHost request) -> suspendOn shapeS funcs exports pending resS request

suspendOn ::
    Sing (shape :: ModuleShape) ->
    FuncSpaceInst shape (ModuleFuncs shape) ->
    [Export] ->
    [Pending shape] ->
    Sing (res :: [LabelledValType]) ->
    HostRequest shape res ->
    (Instance, Either RunError Progress)
suspendOn shapeS funcs exports pending resS request = case request of
    ForeignRequest target psS _ args rsS store suspended ->
        ( Instance shapeS funcs exports store (Pending resS rsS suspended : pending)
        , Right (Calls (ForeignCall target (FuncType (declaredOrder (unlabelledTypes psS)) (declaredOrder (unlabelledTypes rsS))) (declaredOrder (toValues psS args))))
        )
    -- (A module linked with others has no WASI host here.)
    HostRequest _ _ store _ _ -> (Instance shapeS funcs exports store pending, Left HostCallNotServed)

-- | What the instance exports under a name.
exportOf :: Instance -> Text -> Maybe ExportDesc
exportOf (Instance _ _ exports _ _) name = case [desc | Export n desc <- exports, n == name] of
    desc : _ -> Just desc
    [] -> Nothing

{- | The type of a function of the instance, by its index, in declared order, and the levels of
  its results: who calls it from outside observes them.
-}
functionType :: Instance -> Word32 -> Maybe (FuncType, [SecLevel])
functionType (Instance shapeS _ _ _ _) idx = do
    SomeFuncRef _ psS rsS _ <- lookupFuncRef (funcTypesSing shapeS) idx
    pure (FuncType (declaredOrder (unlabelledTypes psS)) (declaredOrder (unlabelledTypes rsS)), declaredOrder [level | _ :~ level <- fromSing rsS])

{- | A memory as one module gives it to another: its address type, its size now with the
  maximum it was declared with (what an import's limits are matched against), and the memory.
-}
data GivenMemory where
    GivenMemory :: AddrType -> Limits -> MemInst m -> GivenMemory

-- | A table as one module gives it to another, likewise, with the level of its entries.
data GivenTable = GivenTable
    { entries :: ValType
    , indices :: AddrType
    , level :: SecLevel
    , limits :: Limits
    , table :: TableInst
    }

-- | A memory of the instance, by its index.
memoryAt :: Instance -> Int -> Maybe GivenMemory
memoryAt (Instance shapeS _ _ store _) = case shapeS of
    SModuleShape _ _ msS _ _ _ _ -> go msS store.memories
  where
    go :: Sing (ms :: [MemShape]) -> MemSpaceInst ms -> Int -> Maybe GivenMemory
    go (SCons shape rest) (MCons mem more) n
        | n == 0 = case fromSing shape of
            MemShape addresses _ most -> Just (GivenMemory addresses (Limits (fromIntegral (memoryPages mem)) (fmap fromIntegral most)) mem)
        | otherwise = go rest more (n - 1)
    go SNil MNil _ = Nothing

-- | Replace a memory of the instance by one given (an index it has not leaves it as it is).
putMemoryAt :: Int -> GivenMemory -> Instance -> Instance
putMemoryAt index (GivenMemory _ _ given) (Instance shapeS funcs exports store pending) =
    Instance shapeS funcs exports Store {globals = store.globals, memories = go store.memories index, tables = store.tables, dataSegments = store.dataSegments} pending
  where
    go :: MemSpaceInst ms -> Int -> MemSpaceInst ms
    go (MCons mem more) n
        | n == 0 = MCons (retypeMemory given) more
        | otherwise = MCons mem (go more (n - 1))
    go MNil _ = MNil

-- | A table of the instance, by its index.
tableAt :: Instance -> Int -> Maybe GivenTable
tableAt (Instance shapeS _ _ store _) = case shapeS of
    SModuleShape _ _ _ tsS _ _ _ -> go tsS store.tables.instances
  where
    go :: Sing (ts :: [TableShape]) -> TableInsts ts -> Int -> Maybe GivenTable
    go (SCons shape rest) (TCons held more) n
        | n == 0 = case fromSing shape of
            TableShape entryType tableLevel indexType _ most -> Just (GivenTable entryType indexType tableLevel (Limits (fromIntegral (tableSize held)) (fmap fromIntegral most)) held)
        | otherwise = go rest more (n - 1)
    go SNil TNil _ = Nothing

-- | Replace a table of the instance.
putTableAt :: Int -> TableInst -> Instance -> Instance
putTableAt index given (Instance shapeS funcs exports store pending) =
    Instance shapeS funcs exports Store {globals = store.globals, memories = store.memories, tables = replaced, dataSegments = store.dataSegments} pending
  where
    replaced = TableSpaceInst store.tables.directory (go store.tables.instances index) store.tables.segments store.tables.caught
    go :: TableInsts ts -> Int -> TableInsts ts
    go (TCons held more) n
        | n == 0 = TCons given more
        | otherwise = TCons held (go more (n - 1))
    go TNil _ = TNil

-- | A global of the instance, by its index: whether it may be written, its level, its value now.
globalAt :: Instance -> Int -> Maybe (Mutability, SecLevel, Value)
globalAt (Instance shapeS _ _ store _) = go (globalTypesSing shapeS) store.globals
  where
    go :: Sing (gs :: [LabelledGlobalType]) -> GlobalSpaceInst gs -> Int -> Maybe (Mutability, SecLevel, Value)
    go (SCons (SGlobalType smut (st :%~ sl)) rest) (GCons value more) n
        | n == 0 = Just (fromSing smut, fromSing sl, toValue st value)
        | otherwise = go rest more (n - 1)
    go SNil GNil _ = Nothing

-- | Give a global of the instance a value (one of another type leaves it as it is).
putGlobalAt :: Int -> Value -> Instance -> Instance
putGlobalAt index given (Instance shapeS funcs exports store pending) =
    Instance shapeS funcs exports Store {globals = go (globalTypesSing shapeS) store.globals index, memories = store.memories, tables = store.tables, dataSegments = store.dataSegments} pending
  where
    go :: Sing (gs :: [LabelledGlobalType]) -> GlobalSpaceInst gs -> Int -> GlobalSpaceInst gs
    go (SCons (SGlobalType _ (st :%~ _)) rest) (GCons value more) n
        | n == 0 = GCons (fromMaybe value (fromValue st given)) more
        | otherwise = GCons value (go rest more (n - 1))
    go SNil GNil _ = GNil
