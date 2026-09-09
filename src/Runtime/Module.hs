{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

{- | Instantiated modules, and the boundary for invoking their exports from the outside world.
  Arguments and results cross it as tagged, term-level 'Value's — so the CLI and test harnesses
  need no type-level machinery — and are checked against the export's type on the way in.
  Lists of values are in declared order here; the stack the function sees has the last
  argument on top (see "Validation.Shape" on stack order).
-}
module Runtime.Module (
    SomeModule (..),
    Value (..),
    valueType,
    renderValue,
    RunError (..),
    Invocation (..),
    SomeHostRequest (..),
    exportSignature,
    invokeExport,
    continueWith,
) where

import Data.Bifunctor (first)
import Data.Singletons (Sing, fromSing)
import Data.Singletons.Base.TH (SList (SCons, SNil))
import Data.Text (Text)
import Data.Word (Word32, Word64)

import Runtime.Interpreter (Config, FuncInsts, Halt (..), HostRequest, ModuleInst (..), Outcome (..), Store (..), getFunc, run, runFunction)
import Runtime.Stack (ValueStack (..))
import Runtime.Trap (Trap)
import Syntax.Immediates (HostType)
import Syntax.Indices (FunctionIdx (..))
import Syntax.Module (Export (..), ExportDesc (..))
import Syntax.Types
import Validation.Reflect (SomeFuncRef (..), declaredOrder, funcTypesSing, lookupFuncRef, stackOrder)
import Validation.Shape (ModuleFuncs, ModuleShape)

{- | A fully elaborated, well-typed module: its shape witness, its instances, and its exports
  (for resolving entry points).
-}
data SomeModule where
    SomeModule :: Sing (shape :: ModuleShape) -> ModuleInst shape -> [Export] -> SomeModule

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
    = NoSuchExport Text
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
    = Returned SomeModule [Value]
    | CalledHost SomeHostRequest

{- | A pending host call together with everything needed to resume the module afterwards:
  its shape witness, its functions, its exports, and the result type of the invocation.
-}
data SomeHostRequest where
    SomeHostRequest ::
        Sing (shape :: ModuleShape) ->
        FuncInsts shape (ModuleFuncs shape) ->
        [Export] ->
        Sing (rs :: [ValType]) ->
        HostRequest shape rs ->
        SomeHostRequest

-- | The type of an exported function, parameters and results in declared order.
exportSignature :: SomeModule -> Text -> Maybe FuncType
exportSignature (SomeModule shapeS _ exports) name = do
    FunctionIdx idx <- exportedFuncIndex name exports
    SomeFuncRef psS rsS _ <- lookupFuncRef (funcTypesSing shapeS) idx
    pure (FuncType (declaredOrder (fromSing psS)) (declaredOrder (fromSing rsS)))

{- | Run an exported function on arguments given in declared order; results likewise. The
  module comes back with the globals and memories the call left behind, so a sequence of
  invocations shares state as the spec's instance does.
-}
invokeExport :: SomeModule -> Text -> [Value] -> Either RunError Invocation
invokeExport (SomeModule shapeS inst exports) name args = do
    FunctionIdx idx <- note (NoSuchExport name) (exportedFuncIndex name exports)
    SomeFuncRef psS rsS funcIx <- note (NoSuchExport name) (lookupFuncRef (funcTypesSing shapeS) idx)
    checkArguments (declaredOrder (fromSing psS)) args
    argStack <- note (ArgumentCount 0 0) (buildStack psS (stackOrder args))
    outcome <- first Trapped (runFunction inst (getFunc funcIx inst.funcs) argStack)
    pure $ case outcome of
        Completed inst' results -> Returned (SomeModule shapeS inst' exports) (declaredOrder (toValues rsS results))
        NeedsHost request -> CalledHost (SomeHostRequest shapeS inst.funcs exports rsS request)

{- | Continue a suspended invocation from the configuration the host's answer produced (see
  'Runtime.Interpreter.resumeWith'); it may finish, or call the host again.
-}
continueWith ::
    Sing (shape :: ModuleShape) ->
    FuncInsts shape (ModuleFuncs shape) ->
    [Export] ->
    Sing (rs :: [ValType]) ->
    Config shape rs ->
    Either RunError Invocation
continueWith shapeS funcs exports rsS config = do
    halt <- first Trapped (run funcs config)
    pure $ case halt of
        Finished store results ->
            Returned (SomeModule shapeS (ModuleInst funcs store.globals store.mems) exports) (declaredOrder (toValues rsS results))
        AwaitingHost request -> CalledHost (SomeHostRequest shapeS funcs exports rsS request)

exportedFuncIndex :: Text -> [Export] -> Maybe FunctionIdx
exportedFuncIndex name exports =
    case [idx | Export n (ExportFunc idx) <- exports, n == name] of
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
buildStack :: Sing (ps :: [ValType]) -> [Value] -> Maybe (ValueStack ps)
buildStack SNil [] = Just VNil
buildStack (SCons st rest) (v : vs) = (:#) <$> fromValue st v <*> buildStack rest vs
buildStack _ _ = Nothing

fromValue :: Sing (t :: ValType) -> Value -> Maybe (HostType t)
fromValue SI32 (I32Value w) = Just w
fromValue SI64 (I64Value w) = Just w
fromValue SF32 (F32Value f) = Just f
fromValue SF64 (F64Value d) = Just d
fromValue _ _ = Nothing

toValues :: Sing (rs :: [ValType]) -> ValueStack rs -> [Value]
toValues SNil VNil = []
toValues (SCons st rest) (v :# vs) = toValue st v : toValues rest vs

toValue :: Sing (t :: ValType) -> HostType t -> Value
toValue SI32 = I32Value
toValue SI64 = I64Value
toValue SF32 = F32Value
toValue SF64 = F64Value

note :: e -> Maybe a -> Either e a
note e = maybe (Left e) Right
