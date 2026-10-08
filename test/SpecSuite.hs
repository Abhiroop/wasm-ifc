{- | The official WebAssembly spec testsuite, at the WebAssembly 3.0 release: each @.wast@
  script becomes binary modules plus a JSON list of assertions (through @wasm-tools
  json-from-wast@, or wabt's @wast2json@ for the scripts it can parse), which this harness
  executes against the decoder, the elaborator and the interpreter.

  Every script at the top of the suite is run. A module that uses a feature we do not
  implement is skipped together with the assertions on it, and counted under the features it
  uses, which @wasm-tools validate@ tells us ('neededFeatures'); every assertion on a module
  within the supported subset must pass. The suite is a git submodule under
  @test/spec/testsuite@; @scripts/spec-report.py@ tabulates a run by feature.
-}
module Main (main) where

import Control.Monad (foldM, forM_)
import Data.Aeson (FromJSON (..), withObject, (.:), (.:?), (.=))
import Data.Aeson qualified as Aeson
import Data.Aeson.Types (parseMaybe)
import Data.Bifunctor (first)
import Data.ByteString.Lazy qualified as BL
import Data.List (isInfixOf, isPrefixOf, sort, sortOn)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64, castFloatToWord32, castWord32ToFloat, castWord64ToDouble)
import System.Directory (createDirectoryIfMissing, doesFileExist, findExecutable, getTemporaryDirectory, listDirectory)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath (dropExtension, takeExtension, (<.>), (</>))
import System.Process (readProcessWithExitCode)
import Test.Hspec
import Text.Read (readMaybe)

import Codec.Wasm (decodeModule)
import Runtime.Instantiate (InstantiationError (..), instantiate)
import Runtime.Module (Invocation (..), RunError (..), SomeModuleInst, Value (..), invokeExport, readGlobalExport, valueType)
import Runtime.Trap (Trap (..))
import Syntax.Types (ValType (..))
import Validation.Elaborate (elaborateModuleWith)
import Validation.Policy (Policy (..), Restrictions (..), emptyPolicy)

suiteDir :: FilePath
suiteDir = "test/spec/testsuite"

{- | The program that turns a script into JSON and binary modules: @wasm-tools json-from-wast@
  if it is installed, since it reads every script of the WebAssembly 3.0 suite, and otherwise
  wabt's @wast2json@, which cannot parse the scripts that use the newest text syntax.
-}
data Converter = WasmTools FilePath | Wast2Json FilePath

findConverter :: IO (Maybe Converter)
findConverter = do
    wasmTools <- findExecutable "wasm-tools"
    wast2json <- findExecutable "wast2json"
    pure (maybe (Wast2Json <$> wast2json) (Just . WasmTools) wasmTools)

convert :: Converter -> FilePath -> FilePath -> FilePath -> IO (ExitCode, String)
convert converter wast jsonPath outDir = do
    (code, _, err) <- case converter of
        WasmTools tool -> readProcessWithExitCode tool ["json-from-wast", wast, "-o", jsonPath, "--wasm-dir", outDir] ""
        Wast2Json tool -> readProcessWithExitCode tool [wast, "-o", jsonPath] ""
    pure (code, err)

{- | Every script at the top of the suite is run, whatever it exercises: what the interpreter
  does not support shows up as skipped assertions, with the reason, not as a script left out.
  With @WASM_IFC_SPEC_REPORT@ set to a file, one JSON line per script is appended to it.
-}
main :: IO ()
main = hspec $ do
    converter <- runIO findConverter
    checkedOut <- runIO (doesFileExist (suiteDir </> "i32.wast"))
    scripts <- runIO (if checkedOut then sort . map dropExtension . filter ((== ".wast") . takeExtension) <$> listDirectory suiteDir else pure [])
    describe "WebAssembly spec testsuite" $
        if checkedOut
            then mapM_ (scriptSpec converter) scripts
            else it "is checked out" (pendingWith "test/spec/testsuite is not checked out (git submodule update --init)")

scriptSpec :: Maybe Converter -> String -> Spec
scriptSpec converter name = it name $ case converter of
    Nothing -> pendingWith "neither wasm-tools nor wast2json (wabt) is installed"
    Just tool -> do
        outDir <- (</> ("wasm-ifc-spec" </> name)) <$> getTemporaryDirectory
        createDirectoryIfMissing True outDir
        let jsonPath = outDir </> name <.> "json"
        (code, err) <- convert tool (suiteDir </> name <.> "wast") jsonPath outDir
        case code of
            ExitFailure _ -> case tool of
                WasmTools _ -> expectationFailure ("wasm-tools could not convert this script: " ++ take 200 err)
                Wast2Json _ -> pendingWith ("wast2json cannot parse this script: " ++ take 200 err)
            ExitSuccess -> do
                decoded <- Aeson.eitherDecode <$> BL.readFile jsonPath
                script <- either fail pure (decoded :: Either String Script)
                outcomes <- runScript outDir script.commands
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

-- (A vector literal's value is a list of lanes and an alternative has none: neither is read.)
instance FromJSON Literal where
    parseJSON = withObject "literal" $ \o -> do
        value <- o .:? "value"
        pure . Literal (fromMaybe "?" (parseMaybe (.: "type") o)) $ case value of
            Just (Aeson.String text) -> Just text
            _ -> Nothing

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
    , registered :: Bool
    -- ^ whether the script has registered a module for others to import from
    }

runScript :: FilePath -> [Command] -> IO [(Int, Outcome)]
runScript dir = fmap (reverse . snd) . foldM step (State (Unavailable "no module yet") Map.empty Nothing False, [])
  where
    step (state, acc) cmd = do
        (state', outcome) <- runCommand dir state cmd
        pure (state', (cmd.line, outcome) : acc)

runCommand :: FilePath -> State -> Command -> IO (State, Outcome)
runCommand dir state cmd = case cmd.kind of
    "module" -> do
        let path = dir </> fromMaybe "" cmd.filename
        result <-
            if cmd.moduleType `elem` [Just "binary", Nothing]
                then loadModule path
                else pure (Left (AtDecode "unsupported: text-format module"))
        -- A valid module we reject is a gap, not a failure, if it needs a feature we lack.
        missing <- case result of
            Left _ | cmd.moduleType `elem` [Just "binary", Nothing] -> neededFeatures path
            _ -> pure Nothing
        -- A module we could not load may have imported a table, memory or global of a
        -- registered module and changed it, which linking between modules would have done
        -- here; what the script asserts about the modules loaded before it is then unknown.
        let unlinked = state.registered && either (const True) (const False) result
            stale loadedBefore = case loadedBefore of
                Loaded _ | unlinked -> Unavailable "its state may depend on a module that could not be linked"
                other -> other
            loaded = case missing of
                Just features | Left _ <- result -> Unavailable ("needs " ++ features)
                _ -> toLoaded result
            outcome = case (result, missing) of
                (Right _, _) -> Passed
                (Left _, Just feature) -> Skipped ("needs " ++ feature)
                (Left rejection, Nothing)
                    | isUnsupported rejection -> Skipped (describeRejection rejection)
                    | otherwise -> Failed ("valid module rejected: " ++ describeRejection rejection)
            earlier = state {anonymous = stale state.anonymous, named = Map.map stale state.named}
            state' = case cmd.name of
                Just n -> earlier {named = Map.insert n loaded earlier.named, current = Just n}
                Nothing -> earlier {anonymous = loaded, current = Nothing}
        pure (state', outcome)
    "assert_return" -> pure (withAction (\m act -> assertReturn m act cmd.expected))
    "assert_trap" -> pure (withAction (\m act -> assertTrap m act cmd.trapText))
    "assert_exhaustion" -> pure (withAction (\m act -> assertTrap m act cmd.trapText))
    "action" -> pure (withAction (\m act -> either (\e -> (m, Failed (show e))) (\(m', _) -> (m', Passed)) (invoke m act)))
    "assert_malformed" -> rejectedBy malformed
    "assert_invalid" -> rejectedBy invalid
    "assert_unlinkable" -> rejectedBy unlinkable
    "assert_uninstantiable" -> rejectedBy uninstantiable
    "register" -> pure (state {registered = True}, Skipped "command register")
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
            let path = dir </> fromMaybe "" cmd.filename
            result <- loadModule path
            -- A module that uses a feature we lack is a gap whatever we answer: the decoder
            -- turns it away before the stage the assertion names is reached.
            missing <- neededFeatures path
            -- Such a module may have written into a registered module's table or memory
            -- before it failed, which persists; without linking we cannot say what.
            let stale loadedBefore = case loadedBefore of
                    Loaded _ | state.registered -> Unavailable "its state may depend on a module that could not be linked"
                    other -> other
            pure . (,) state {anonymous = stale state.anonymous, named = Map.map stale state.named} $ case result of
                _ | Just features <- missing -> Skipped ("needs " ++ features)
                Left rejection
                    | expected rejection -> Passed
                    | isUnsupported rejection -> Skipped (describeRejection rejection)
                    | otherwise -> Failed ("rejected at the wrong stage: " ++ describeRejection rejection)
                Right _ -> Failed ("accepted a module the spec rejects: " ++ maybe "" T.unpack cmd.trapText)

{- | The features of WebAssembly this interpreter implements, as @wasm-tools validate@ names
  them: WebAssembly 1.0 with the mutable-global, sign-extension, saturating-conversion,
  multi-value and bulk-memory extensions. (@gc-types@ enables no instruction: it lets
  @wasm-tools@ mention reference types at all once another feature introduces them.)
-}
supportedFeatures :: String
supportedFeatures = "-all,mutable-global,saturating-float-to-int,sign-extension,multi-value,bulk-memory,floats,gc-types"

{- | The features of WebAssembly 3.0 beyond 'supportedFeatures', each with the flags that
  enable it in @wasm-tools@ together with the features it builds on.
-}
furtherFeatures :: [(String, String)]
furtherFeatures =
    [ ("vector instructions", "simd")
    , ("reference types", "reference-types")
    , ("64-bit memories and tables", "memory64")
    , ("multiple memories", "multi-memory")
    , ("tail calls", "tail-call")
    , ("extended constant expressions", "extended-const")
    , ("typed function references", "reference-types,function-references")
    , ("garbage collection", "reference-types,function-references,gc")
    , ("exceptions", "reference-types,exceptions")
    ]

{- | The features a module uses beyond 'supportedFeatures', or 'Nothing' if it uses none (or if
  @wasm-tools@ is not installed to say). @wasm-tools@ gives its verdict on the module with
  all of WebAssembly 3.0 enabled; the features the module uses are the smallest set, of one or two of
  'furtherFeatures', with which it gives that same verdict. The comparison of verdicts, not
  of validity, is for the modules the suite expects to be rejected.
-}
neededFeatures :: FilePath -> IO (Maybe String)
neededFeatures path = do
    tool <- findExecutable "wasm-tools"
    case tool of
        Nothing -> pure Nothing
        Just wasmTools -> do
            let verdict flags = do
                    (code, _, err) <- readProcessWithExitCode wasmTools ["validate", "--features=" ++ flags, path] ""
                    -- (Without its log lines, which carry the time of day.)
                    pure (if code == ExitSuccess then "" else unlines (filter (not . isPrefixOf "[") (lines err)))
            target <- verdict "wasm3"
            subset <- verdict supportedFeatures
            if subset == target
                then pure Nothing
                else do
                    let matching candidates = case candidates of
                            [] -> pure Nothing
                            (names, flags) : rest -> do
                                answer <- verdict (supportedFeatures ++ "," ++ flags)
                                if answer == target then pure (Just names) else matching rest
                        pairs = [(a ++ " + " ++ b, fa ++ "," ++ fb) | (i, (a, fa)) <- zip [0 :: Int ..] furtherFeatures, (b, fb) <- drop (i + 1) furtherFeatures]
                    found <- matching (furtherFeatures ++ pairs)
                    pure (Just (fromMaybe "three or more features" found))

{- | Decode, validate and instantiate a module. With @WASM_IFC_SECWASM_RESTRICTIONS@ set in the
  environment, validation applies SecWasm's restrictions ("Validation.Policy").
-}
loadModule :: FilePath -> IO (Either Rejection SomeModuleInst)
loadModule path = do
    bytes <- BL.readFile path
    restricted <- lookupEnv "WASM_IFC_SECWASM_RESTRICTIONS"
    let policy = case restricted of
            Nothing -> emptyPolicy
            Just _ -> emptyPolicy {restrictions = SecWasmRestrictions}
    pure $ do
        raw <- first AtDecode (decodeModule bytes)
        validated <- first (AtValidation . show) (elaborateModuleWith policy raw)
        first AtInstantiation (instantiate validated)

-- | Perform an action: @invoke@ an exported function, or @get@ an exported global.
invoke :: SomeModuleInst -> Action -> Either RunError (SomeModuleInst, [Value])
invoke m act
    | act.actionKind == "get" = (\value -> (m, [value])) <$> readGlobalExport m act.field
    | otherwise = case traverse literalValue act.args of
        Nothing -> Left (NoSuchExport "(non-numeric argument)")
        Just values -> case invokeExport m act.field values of
            Left err -> Left err
            Right (Returned m' results) -> Right (m', results)
            Right (CalledHost _) -> Left HostCallNotServed

-- | The actions the harness performs; anything else is skipped, not failed.
knownAction :: Action -> Bool
knownAction act = act.actionKind `elem` ["invoke", "get"]

-- | Each check hands back the instance to continue with (unchanged when the call failed).
assertReturn :: SomeModuleInst -> Action -> [Literal] -> (SomeModuleInst, Outcome)
assertReturn m act expectations
    | not (knownAction act) = (m, Skipped ("action " ++ T.unpack act.actionKind))
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
assertTrap m act expectedText
    | not (knownAction act) = (m, Skipped ("action " ++ T.unpack act.actionKind))
    | otherwise = case invoke m act of
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
trapText CallStackExhausted = "call stack exhausted"
trapText InformationFlowViolation = "information flow violation"
trapText IndirectCallBelowBound = "indirect call below bound"
trapText (SecretRead _) = "secret read"
trapText GlobalNotRestored = "global not restored"

numericTypes :: [Text]
numericTypes = ["i32", "i64", "f32", "f64"]

-- | A literal's value from its bit pattern.
literalValue :: Literal -> Maybe Value
literalValue lit = do
    -- (wabt writes a bit pattern as an unsigned decimal, wasm-tools as a signed one.)
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
        Just v -> fmap (`mod` width) (readMaybe (T.unpack v)) == Just (valueBits actual)
        Nothing -> False
  where
    typeName I32 = "i32"
    typeName I64 = "i64"
    typeName F32 = "f32"
    typeName F64 = "f64"
    width = case valueType actual of
        I32 -> 2 ^ (32 :: Int)
        F32 -> 2 ^ (32 :: Int)
        I64 -> 2 ^ (64 :: Int)
        F64 -> 2 ^ (64 :: Int)

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

-- | One line per script, and the commonest reasons for skipping, so a gap shows up as a count.
report :: String -> [(Int, Outcome)] -> Expectation
report name outcomes = do
    putStrLn ("    " ++ name ++ ": " ++ show passed ++ " passed, " ++ show (length failures) ++ " failed, " ++ show (length skipped) ++ " skipped")
    reportFile <- lookupEnv "WASM_IFC_SPEC_REPORT"
    forM_ reportFile $ \file ->
        BL.appendFile file (Aeson.encode (Aeson.object ["script" .= name, "passed" .= passed, "failed" .= length failures, "skipped" .= length skipped, "reasons" .= skipReasons, "failures" .= take 5 (map snd failures)]) <> "\n")
    mapM_ (\(reason, n) -> putStrLn ("        " ++ show n ++ "x " ++ reason)) (take 4 skipReasons)
    case failures of
        [] -> pure ()
        _ -> expectationFailure (unlines (take 12 [name ++ ".wast:" ++ show l ++ ": " ++ msg | (l, msg) <- failures]))
  where
    passed = length [() | (_, Passed) <- outcomes]
    skipped = [reason | (_, Skipped reason) <- outcomes]
    failures = [(l, msg) | (l, Failed msg) <- outcomes]
    skipReasons = sortOn (negate . snd) (Map.toList (Map.fromListWith (+) [(reason, 1 :: Int) | reason <- skipped]))
