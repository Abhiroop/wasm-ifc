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
    exportSignature,
    exportedResultLevels,
    exportedGlobalLevel,
    readMemoryLevels,
    invokeExport,
    readGlobalExport,
    continueWith,
) where

import Data.Bifunctor (first)
import Data.Singletons (Sing, fromSing)
import Data.Singletons.Base.TH (SList (SCons, SNil))
import Data.Text (Text)
import Data.Word (Word32, Word64, Word8)

import Runtime.Interpreter (Config, FuncSpaceInst, Halt (..), HostRequest, ModuleInst (..), Outcome (..), getFunc, run, runFunction, storeToModule)
import Runtime.MemInst (levelOfRange, readBytes)
import Runtime.Stack (MemSpaceInst (..), ValueStack (..), getGlobal)
import Runtime.Trap (Trap)
import Syntax.Immediates (HostType)
import Syntax.Indices (FunctionIdx (..), GlobalIdx (..))
import Syntax.Module (Export (..), ExportDesc (..))
import Syntax.Types
import Syntax.TypesIFC
import Validation.Reflect (SomeGlobalRef (..), declaredOrder, funcTypesSing, globalTypesSing, lookupFuncRef, lookupGlobalRef, stackOrder)
import Validation.Shape (ModuleFuncs, ModuleShape, SomeFuncRef (..))

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
    deriving stock (Eq, Show)

valueType :: Value -> ValType
valueType (I32Value _) = I32
valueType (I64Value _) = I64
valueType (F32Value _) = F32
valueType (F64Value _) = F64

-- | Integers as unsigned decimals (the raw bits), floats as Haskell shows them.
renderValue :: Value -> String
renderValue (I32Value w) = show w
renderValue (I64Value w) = show w
renderValue (F32Value f) = show f
renderValue (F64Value d) = show d

data RunError
    = -- | no export of that name and kind (a function to invoke, a global to read)
      NoSuchExport Text
    | -- | expected and actual number of arguments
      ArgumentCount Int Int
    | -- | the argument at this (zero-based) position should have the first type, has the second
      ArgumentType Int ValType ValType
    | Trapped Trap
    | -- | the function called into the host, and the caller had no host to offer
      HostCallNotServed
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
fromValue _ _ = Nothing

toValues :: Sing (rs :: [LabelledValType]) -> ValueStack rs -> [Value]
toValues SNil VNil = []
toValues (SCons (st :%~ _) rest) (v :# vs) = toValue st v : toValues rest vs

toValue :: Sing (t :: ValType) -> HostType t -> Value
toValue SI32 = I32Value
toValue SI64 = I64Value
toValue SF32 = F32Value
toValue SF64 = F64Value

note :: e -> Maybe a -> Either e a
note e = maybe (Left e) Right
