{- | The official WebAssembly spec testsuite, run through wabt's @wast2json@: each @.wast@
  script becomes binary modules plus a JSON list of assertions, which this harness executes
  against the decoder, the elaborator and the interpreter.

  A module that needs a feature we do not implement (tables, reference types, imports, …)
  is skipped together with the assertions on it, and counted; every assertion on a module we
  do accept must pass. The suite is a git submodule under @test/spec/testsuite@, pinned to a
  commit @wast2json@ 1.0.27 can parse.
-}
module Main (main) where

import Control.Monad (foldM)
import Data.Aeson (FromJSON (..), withObject, (.:), (.:?))
import Data.Aeson qualified as Aeson
import Data.Bifunctor (first)
import Data.ByteString.Lazy qualified as BL
import Data.List (isInfixOf)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64, castFloatToWord32, castWord32ToFloat, castWord64ToDouble)
import System.Directory (createDirectoryIfMissing, doesFileExist, findExecutable, getTemporaryDirectory)
import System.Exit (ExitCode (..))
import System.FilePath ((<.>), (</>))
import System.Process (readProcessWithExitCode)
import Test.Hspec
import Text.Read (readMaybe)

import Codec.Wasm (decodeModule)
import Runtime.Instantiate (InstantiationError (..), instantiate)
import Runtime.Module (Invocation (..), RunError (..), SomeModuleInst, Value (..), invokeExport, valueType)
import Runtime.Trap (Trap (..))
import Syntax.Types (ValType (..))
import Validation.Elaborate (elaborateModule)

{- | Assertions we know we cannot meet, by script and line, with the reason. They are reported
  as skipped, not failed, so a regression elsewhere still shows.
-}
knownGaps :: Map.Map String [(Int, String)]
knownGaps =
    Map.fromList
        [ ("elem", [(l, "the table is shared with another module through an import") | l <- [574, 575, 587, 588, 589]])
        ]

-- | The scripts we run: those exercising the instruction subset and the binary format.
scripts :: [String]
scripts =
    [ "address"
    , "align"
    , "binary"
    , "binary-leb128"
    , "block"
    , "br"
    , "br_if"
    , "br_table"
    , "bulk"
    , "call"
    , "call_indirect"
    , "comments"
    , "const"
    , "conversions"
    , "custom"
    , "data"
    , "elem"
    , "endianness"
    , "exports"
    , "f32"
    , "f32_bitwise"
    , "f32_cmp"
    , "f64"
    , "f64_bitwise"
    , "f64_cmp"
    , "fac"
    , "float_exprs"
    , "float_literals"
    , "float_memory"
    , "float_misc"
    , "forward"
    , "func"
    , "func_ptrs"
    , "global"
    , "i32"
    , "i64"
    , "if"
    , "imports"
    , "int_exprs"
    , "int_literals"
    , "labels"
    , "left-to-right"
    , "load"
    , "local_get"
    , "local_set"
    , "local_tee"
    , "loop"
    , "memory"
    , "memory_copy"
    , "memory_fill"
    , "memory_grow"
    , "memory_init"
    , "memory_redundancy"
    , "memory_size"
    , "memory_trap"
    , "names"
    , "nop"
    , "return"
    , "select"
    , "stack"
    , "start"
    , "store"
    , "switch"
    , "table"
    , "traps"
    , "type"
    , "unreachable"
    , "unreached-invalid"
    , "unreached-valid"
    , "unwind"
    ]

suiteDir :: FilePath
suiteDir = "test/spec/testsuite"

main :: IO ()
main = hspec $ do
    wast2json <- runIO (findExecutable "wast2json")
    checkedOut <- runIO (doesFileExist (suiteDir </> "i32.wast"))
    describe "WebAssembly spec testsuite" $
        mapM_ (scriptSpec wast2json checkedOut) scripts

scriptSpec :: Maybe FilePath -> Bool -> String -> Spec
scriptSpec wast2json checkedOut name = it name $ case wast2json of
    Nothing -> pendingWith "wast2json (wabt) is not installed"
    Just tool
        | not checkedOut -> pendingWith "test/spec/testsuite is not checked out (git submodule update --init)"
        | otherwise -> do
            outDir <- (</> ("wasm-ifc-spec" </> name)) <$> getTemporaryDirectory
            createDirectoryIfMissing True outDir
            let jsonPath = outDir </> name <.> "json"
            (code, _, err) <- readProcessWithExitCode tool [suiteDir </> name <.> "wast", "-o", jsonPath] ""
            case code of
                ExitFailure _ -> pendingWith ("wast2json cannot parse this script: " ++ take 200 err)
                ExitSuccess -> do
                    decoded <- Aeson.eitherDecode <$> BL.readFile jsonPath
                    script <- either fail pure (decoded :: Either String Script)
                    outcomes <- runScript name outDir script.commands
                    report name outcomes

-- *** The script format (as wast2json writes it) ***

newtype Script = Script {commands :: [Command]}

instance FromJSON Script where
    parseJSON = withObject "script" $ \o -> Script <$> o .: "commands"

-- | One command; the optional fields are present depending on the kind.
data Command = Command
    { line :: Int
    , kind :: Text
    , filename :: Maybe FilePath
    , name :: Maybe Text
    , moduleType :: Maybe Text
    , action :: Maybe Action
    , expected :: [Literal]
    , trapText :: Maybe Text
    }

instance FromJSON Command where
    parseJSON = withObject "command" $ \o ->
        Command
            <$> o .: "line"
            <*> o .: "type"
            <*> o .:? "filename"
            <*> o .:? "name"
            <*> o .:? "module_type"
            <*> o .:? "action"
            <*> (fromMaybe [] <$> o .:? "expected")
            <*> o .:? "text"

data Action = Action
    { actionKind :: Text
    , actionModule :: Maybe Text
    , field :: Text
    , args :: [Literal]
    }

instance FromJSON Action where
    parseJSON = withObject "action" $ \o ->
        Action <$> o .: "type" <*> o .:? "module" <*> o .: "field" <*> (fromMaybe [] <$> o .:? "args")

-- | A typed literal: the value is the bit pattern as a decimal string, or a NaN class.
data Literal = Literal {litType :: Text, litValue :: Maybe Text}

instance FromJSON Literal where
    parseJSON = withObject "literal" $ \o -> Literal <$> o .: "type" <*> o .:? "value"

-- *** Running ***

data Outcome = Passed | Failed String | Skipped String

-- | A module the script refers to: usable, or unavailable for a stated reason.
data Loaded = Loaded SomeModuleInst | Unavailable String

-- | Which stage rejected a module, and why.
data Rejection
    = AtDecode String
    | AtValidation String
    | AtInstantiation InstantiationError

-- | A rejection for a feature outside the implemented subset, which the suite skips.
isUnsupported :: Rejection -> Bool
isUnsupported rejection = case rejection of
    AtDecode err -> any (`isInfixOf` err) ["unsupported", "not supported", "unknown valtype", "unknown limits flag"]
    AtValidation _ -> False
    AtInstantiation (UnsupportedImport _ _) -> True
    AtInstantiation _ -> False

describeRejection :: Rejection -> String
describeRejection rejection = case rejection of
    AtDecode err -> "decode error: " ++ err
    AtValidation err -> "validation error: " ++ err
    AtInstantiation (UnsupportedImport modName field) -> "unsupported import: " ++ T.unpack modName ++ "." ++ T.unpack field
    AtInstantiation err -> "instantiation error: " ++ show err

-- | The instance a @module@ command yields, unavailable if any stage rejected it.
toLoaded :: Either Rejection SomeModuleInst -> Loaded
toLoaded = either (Unavailable . describeRejection) Loaded

{- | The script's instances: the named ones, the anonymous latest one, and which of them the
  last @module@ command made current. Invocations update the instance they ran on, since
  module state persists across a script.
-}
data State = State
    { anonymous :: Loaded
    , named :: Map.Map Text Loaded
    , current :: Maybe Text
    }

runScript :: String -> FilePath -> [Command] -> IO [(Int, Outcome)]
runScript name dir = fmap (reverse . snd) . foldM step (State (Unavailable "no module yet") Map.empty Nothing, [])
  where
    gaps = Map.findWithDefault [] name knownGaps
    step (state, acc) cmd = do
        (state', outcome) <- runCommand dir state cmd
        let outcome' = case lookup cmd.line gaps of
                Just reason -> Skipped ("known gap: " ++ reason)
                Nothing -> outcome
        pure (state', (cmd.line, outcome') : acc)

runCommand :: FilePath -> State -> Command -> IO (State, Outcome)
runCommand dir state cmd = case cmd.kind of
    "module" -> do
        result <- loadModule (dir </> fromMaybe "" cmd.filename)
        let loaded = toLoaded result
            outcome = case result of
                Right _ -> Passed
                Left rejection
                    | isUnsupported rejection -> Skipped (describeRejection rejection)
                    | otherwise -> Failed ("valid module rejected: " ++ describeRejection rejection)
            state' = case cmd.name of
                Just n -> state {named = Map.insert n loaded state.named, current = Just n}
                Nothing -> state {anonymous = loaded, current = Nothing}
        pure (state', outcome)
    "assert_return" -> pure (withAction (\m act -> assertReturn m act cmd.expected))
    "assert_trap" -> pure (withAction (\m act -> assertTrap m act cmd.trapText))
    "action" -> pure (withAction (\m act -> either (\e -> (m, Failed (show e))) (\(m', _) -> (m', Passed)) (invoke m act)))
    "assert_malformed" -> rejectedBy malformed
    "assert_invalid" -> rejectedBy invalid
    "assert_unlinkable" -> rejectedBy unlinkable
    "assert_uninstantiable" -> rejectedBy uninstantiable
    other -> pure (state, Skipped ("command " ++ T.unpack other))
  where
    -- Run a check on the instance an action names, and store the instance it hands back.
    withAction check = case cmd.action of
        Nothing -> (state, Failed "command without an action")
        Just act -> case lookupInstance (act.actionModule) of
            Unavailable reason -> (state, Skipped reason)
            Loaded m -> let (m', outcome) = check m act in (storeInstance (act.actionModule) (Loaded m'), outcome)
    lookupInstance which = case which of
        Just n -> namedInstance n
        Nothing -> maybe state.anonymous namedInstance state.current
    namedInstance n = Map.findWithDefault (Unavailable "unknown module") n state.named
    storeInstance which loaded = case which of
        Just n -> state {named = Map.insert n loaded state.named}
        Nothing -> case state.current of
            Just n -> state {named = Map.insert n loaded state.named}
            Nothing -> state {anonymous = loaded}
    -- What each assertion expects of the rejection: the stage, and for instantiation the kind.
    malformed rejection = case rejection of
        AtDecode _ -> True
        _ -> False
    invalid rejection = case rejection of
        AtInstantiation _ -> False
        _ -> True
    unlinkable rejection = case rejection of
        AtInstantiation (UnsupportedImport _ _) -> True
        AtInstantiation (ImportTypeMismatch _) -> True
        _ -> False
    uninstantiable rejection = case rejection of
        AtInstantiation (StartFunctionTrapped _) -> True
        AtInstantiation (DataSegmentOutOfBounds _) -> True
        AtInstantiation (ElementSegmentOutOfBounds _) -> True
        _ -> False
    -- The module must be rejected, and by the stage the assertion names: a module the
    -- decoder cannot handle at all is a gap, not a verdict, unless decoding is the stage.
    rejectedBy expected
        | cmd.moduleType /= Just "binary" = pure (state, Skipped "text-format module")
        | otherwise = do
            result <- loadModule (dir </> fromMaybe "" cmd.filename)
            pure . (,) state $ case result of
                Left rejection
                    | expected rejection -> Passed
                    | isUnsupported rejection -> Skipped (describeRejection rejection)
                    | otherwise -> Failed ("rejected at the wrong stage: " ++ describeRejection rejection)
                Right _ -> Failed ("accepted a module the spec rejects: " ++ maybe "" T.unpack cmd.trapText)

loadModule :: FilePath -> IO (Either Rejection SomeModuleInst)
loadModule path = do
    bytes <- BL.readFile path
    pure $ do
        raw <- first AtDecode (decodeModule bytes)
        validated <- first (AtValidation . show) (elaborateModule raw)
        first AtInstantiation (instantiate validated)

invoke :: SomeModuleInst -> Action -> Either RunError (SomeModuleInst, [Value])
invoke m act = case traverse literalValue act.args of
    Nothing -> Left (NoSuchExport "(non-numeric argument)")
    Just values -> case invokeExport m act.field values of
        Left err -> Left err
        Right (Returned m' results) -> Right (m', results)
        Right (CalledHost _) -> Left HostCallNotServed

-- | Each check hands back the instance to continue with (unchanged when the call failed).
assertReturn :: SomeModuleInst -> Action -> [Literal] -> (SomeModuleInst, Outcome)
assertReturn m act expectations
    | act.actionKind /= "invoke" = (m, Skipped ("action " ++ T.unpack act.actionKind))
    | any (\a -> a.litType `notElem` numericTypes) act.args = (m, Skipped "non-numeric argument")
    | otherwise = case invoke m act of
        Left err -> (m, Failed ("invoke " ++ T.unpack act.field ++ ": " ++ show err))
        Right (m', results)
            | length results /= length expectations -> (m', Failed ("expected " ++ show (length expectations) ++ " result(s), got " ++ show results))
            | and (zipWith matches expectations results) -> (m', Passed)
            | otherwise -> (m', Failed ("invoke " ++ T.unpack act.field ++ " " ++ show (map render act.args) ++ ": expected " ++ show (map render expectations) ++ ", got " ++ show results))
  where
    render l = T.unpack l.litType ++ ":" ++ maybe "?" T.unpack l.litValue

assertTrap :: SomeModuleInst -> Action -> Maybe Text -> (SomeModuleInst, Outcome)
assertTrap m act expectedText = case invoke m act of
    Left (Trapped trap)
        | Just (trapText trap) == expectedText -> (m, Passed)
        | otherwise -> (m, Failed ("trapped with " ++ show trap ++ ", expected " ++ maybe "?" T.unpack expectedText))
    Left err -> (m, Failed ("invoke " ++ T.unpack act.field ++ ": " ++ show err))
    Right (m', results) -> (m', Failed ("expected a trap (" ++ maybe "?" T.unpack expectedText ++ "), got " ++ show results))

-- | The spec's wording for each trap, as the scripts assert it.
trapText :: Trap -> Text
trapText IntegerDivideByZero = "integer divide by zero"
trapText IntegerOverflow = "integer overflow"
trapText OutOfBoundsMemoryAccess = "out of bounds memory access"
trapText InvalidConversionToInteger = "invalid conversion to integer"
trapText UnreachableExecuted = "unreachable"
trapText UndefinedElement = "undefined element"
trapText UninitializedElement = "uninitialized element"
trapText IndirectCallTypeMismatch = "indirect call type mismatch"

numericTypes :: [Text]
numericTypes = ["i32", "i64", "f32", "f64"]

-- | A literal's value from its bit pattern.
literalValue :: Literal -> Maybe Value
literalValue lit = do
    bits <- readMaybe . T.unpack =<< lit.litValue :: Maybe Integer
    case lit.litType of
        "i32" -> Just (I32Value (fromInteger bits))
        "i64" -> Just (I64Value (fromInteger bits))
        "f32" -> Just (F32Value (castWord32ToFloat (fromInteger bits)))
        "f64" -> Just (F64Value (castWord64ToDouble (fromInteger bits)))
        _ -> Nothing

-- | Does a result match an expectation? Bit-exact, except that a NaN class matches any NaN.
matches :: Literal -> Value -> Bool
matches lit actual
    | typeName (valueType actual) /= lit.litType = False
    | otherwise = case lit.litValue of
        Just "nan:canonical" -> isNaNValue actual
        Just "nan:arithmetic" -> isNaNValue actual
        Just v -> readMaybe (T.unpack v) == Just (valueBits actual)
        Nothing -> False
  where
    typeName I32 = "i32"
    typeName I64 = "i64"
    typeName F32 = "f32"
    typeName F64 = "f64"

isNaNValue :: Value -> Bool
isNaNValue (F32Value f) = isNaN f
isNaNValue (F64Value d) = isNaN d
isNaNValue _ = False

valueBits :: Value -> Integer
valueBits (I32Value w) = fromIntegral w
valueBits (I64Value w) = fromIntegral w
valueBits (F32Value f) = fromIntegral (castFloatToWord32 f)
valueBits (F64Value d) = fromIntegral (castDoubleToWord64 d :: Word64)

-- *** Reporting ***

report :: String -> [(Int, Outcome)] -> Expectation
report name outcomes = do
    putStrLn ("    " ++ name ++ ": " ++ show passed ++ " passed, " ++ show (length failures) ++ " failed, " ++ show skipped ++ " skipped")
    case failures of
        [] -> pure ()
        _ -> expectationFailure (unlines (take 12 [name ++ ".wast:" ++ show l ++ ": " ++ msg | (l, msg) <- failures]))
  where
    passed = length [() | (_, Passed) <- outcomes]
    skipped = length [() | (_, Skipped _) <- outcomes]
    failures = [(l, msg) | (l, Failed msg) <- outcomes]
