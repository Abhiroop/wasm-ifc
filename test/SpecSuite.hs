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
import Data.Maybe (fromMaybe, isJust)
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
import Runtime.Instantiate (InstantiationError (..))
import Runtime.Link (World, callExport, emptyWorld, instantiateIn, register, unaliased, viewInstance)
import Runtime.Module (RunError (..), Value (..), readGlobalExport, valueType)
import Runtime.Trap (Trap (..))
import Runtime.Vector (fromLanes, lanes)
import Syntax.Functions (RawFunction (..))
import Syntax.Globals (RawGlobal (..))
import Syntax.Immediates (Reference (..), Vector128 (..), isNullReference, nullReference, referenceTo)
import Syntax.Indices (FunctionIdx (..), GlobalIdx (..), MemoryIdx (..), TableIdx (..))
import Syntax.Instructions (RawInstr (..))
import Syntax.Module (Export (..), ExportDesc (..), RawMemory (..), RawModule (..), RawTable (..), importsNoState, noAliases)
import Syntax.Types (AddrType (..), FuncTypeOf (..), GlobalTypeOf (..), Limits (..), MemType (..), Mutability (..), SValType (..), ValType (..))
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
    -- (WASM_IFC_SPEC_ONLY, a prefix, restricts a run to the scripts whose names start with it.)
    only <- runIO (lookupEnv "WASM_IFC_SPEC_ONLY")
    scripts <- runIO (if checkedOut then filter (maybe (const True) isPrefixOf only) . sort . map dropExtension . filter ((== ".wast") . takeExtension) <$> listDirectory suiteDir else pure [])
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
    , registerAs :: Maybe Text
    , instanceName :: Maybe Text
    -- ^ of a @module_instance@: the name of the instance it makes
    , definition :: Maybe Text
    -- ^ of a @module_instance@: the name of the definition it instantiates
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
            <*> o .:? "as"
            <*> o .:? "instance"
            <*> o .:? "module"

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
data Literal = Literal
    { litType :: Text
    , litValue :: Maybe Text
    , laneType :: Maybe Text
    -- ^ of a vector: how its lanes are written (@i8@ … @f64@)
    , laneValues :: [Text]
    -- ^ of a vector: its lanes, lane 0 first, each written like a scalar of the lane type
    , alternatives :: [Literal]
    -- ^ of an @either@: the values of which a result must be one
    }

instance FromJSON Literal where
    parseJSON = withObject "literal" $ \o -> do
        value <- o .:? "value"
        written <- o .:? "lane_type"
        choices <- fromMaybe [] <$> o .:? "values"
        pure $ case value of
            Just (Aeson.String text) -> Literal (kind o) (Just text) written [] choices
            Just (Aeson.Array texts) -> Literal (kind o) Nothing written [text | Aeson.String text <- foldr (:) [] texts] choices
            _ -> Literal (kind o) Nothing written [] choices
      where
        kind o = fromMaybe "?" (parseMaybe (.: "type") o)

-- *** Running ***

data Outcome = Passed | Failed String | Skipped String

-- | A module the script refers to: an instance of the script's world, or unavailable for a stated reason.
data Loaded = Loaded Int | Unavailable String

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
    AtInstantiation (ImportedTwice _ _) -> True
    -- (A start function that calls into a host: the world of a script has none.)
    AtInstantiation StartFunctionNeedsHost -> True
    AtInstantiation _ -> False

describeRejection :: Rejection -> String
describeRejection rejection = case rejection of
    AtDecode err -> "decode error: " ++ err
    AtValidation err -> "validation error: " ++ err
    AtInstantiation (UnsupportedImport modName field) -> "unsupported import: " ++ T.unpack modName ++ "." ++ T.unpack field
    AtInstantiation (ImportedTwice modName field) -> "the same object imported twice: " ++ T.unpack modName ++ "." ++ T.unpack field
    AtInstantiation err -> "instantiation error: " ++ show err

-- | The instance a @module@ command yields, unavailable if any stage rejected it.
toLoaded :: Either Rejection Int -> Loaded
toLoaded = either (Unavailable . describeRejection) Loaded

{- | The script's instances: the world they are linked in, the named ones, the anonymous latest
  one, and which of them the last @module@ command made current. A module a script registers
  is importable under that name ('Runtime.Link.register'), and what it shares with those that
  import it is shared.
-}
data State = State
    { world :: World
    , instances :: Map.Map Int Loaded
    -- ^ every module the script has loaded, in order
    , named :: Map.Map Text Int
    , latest :: Maybe Int
    -- ^ the module the last @module@ command loaded, which an action without a name means
    , registers :: Bool
    -- ^ whether the script has registered a module for import
    , definitions :: Map.Map Text FilePath
    -- ^ the modules the script has defined without instantiating them, by name
    }

runScript :: FilePath -> [Command] -> IO [(Int, Outcome)]
runScript dir = fmap (reverse . snd) . foldM step (State withSpectest Map.empty Map.empty Nothing False Map.empty, [])
  where
    step (state, acc) cmd = do
        (state', outcome) <- runCommand dir state cmd
        pure (state', (cmd.line, outcome) : acc)

{- | A world with the suite's @spectest@ module in it: its printing functions, which do
  nothing, its four globals, its memory and its two tables. It is a module like any other, so
  the modules of a script that import its memory or its table share them.
-}
withSpectest :: World
withSpectest = case elaborateModuleWith emptyPolicy spectest of
    Left invalid -> error ("the spectest module is invalid: " ++ show invalid)
    Right validated -> case instantiateIn emptyWorld validated of
        (world, Right x, _) -> register "spectest" x world
        (_, Left failure, _) -> error ("the spectest module does not instantiate: " ++ show failure)
  where
    prints = [("print", []), ("print_i32", [I32]), ("print_i64", [I64]), ("print_f32", [F32]), ("print_f64", [F64]), ("print_i32_f32", [I32, F32]), ("print_f64_f64", [F64, F64])]
    globals =
        [ ("global_i32", I32, [Const SI32 666])
        , ("global_i64", I64, [Const SI64 666])
        , ("global_f32", F32, [Const SF32 666.6])
        , ("global_f64", F64, [Const SF64 666.6])
        ]
    spectest =
        RawModule
            { types = [FuncType params [] | (_, params) <- prints]
            , imports = []
            , functions = [RawFunction (FuncType params []) [] [] | (_, params) <- prints]
            , globals = [RawGlobal (GlobalType Immutable t) initialiser | (_, t, initialiser) <- globals]
            , memories = [RawMemory (MemType AddrI32 (Limits 1 (Just 2)))]
            , tables = [RawTable FuncRef AddrI32 (Limits 10 (Just 20)), RawTable FuncRef AddrI64 (Limits 10 (Just 20))]
            , elementSegments = []
            , dataSegments = []
            , exports =
                [Export name (ExportFunc (FunctionIdx i)) | (i, (name, _)) <- zip [0 ..] prints]
                    ++ [Export name (ExportGlobal (GlobalIdx i)) | (i, (name, _, _)) <- zip [0 ..] globals]
                    ++ [Export "memory" (ExportMem (MemoryIdx 0)), Export "table" (ExportTable (TableIdx 0)), Export "table64" (ExportTable (TableIdx 1))]
            , start = Nothing
            , customSections = []
            , stateImports = importsNoState
            , tags = []
            , tagImports = []
            , aliases = noAliases
            , tableInitialisers = []
            , written = Nothing
            }

runCommand :: FilePath -> State -> Command -> IO (State, Outcome)
runCommand dir state cmd = case cmd.kind of
    "module" -> do
        let path = dir </> fromMaybe "" cmd.filename
        (world', result) <-
            if cmd.moduleType `elem` [Just "binary", Nothing]
                then loadModule state.world path
                else pure (state.world, Left (AtDecode "unsupported: text-format module"))
        -- A valid module we reject is a gap, not a failure, if it needs a feature we lack.
        missing <- case result of
            Left _ | cmd.moduleType `elem` [Just "binary", Nothing] -> neededFeatures path
            _ -> pure Nothing
        -- A module we could not load may have imported a table, memory or global of a
        -- registered module and changed it, which linking between modules would have done
        -- here; what the script asserts about the modules loaded before it is then unknown.
        let unlinked = state.registers && either (const True) (const False) result && isJust missing
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
            index = Map.size state.instances
            state' =
                state
                    { world = world'
                    , instances = Map.insert index loaded (Map.map stale state.instances)
                    , named = maybe state.named (\n -> Map.insert n index state.named) cmd.name
                    , latest = Just index
                    }
        pure (state', outcome)
    -- A definition is a module that is checked now and instantiated later, any number of times.
    "module_definition" -> do
        let path = dir </> fromMaybe "" cmd.filename
        bytes <- BL.readFile path
        missing <- neededFeatures path
        pure $ case first AtDecode (decodeModule bytes) >>= first (AtValidation . show) . elaborateModuleWith emptyPolicy of
            Right _ -> (state {definitions = Map.insert (fromMaybe "" cmd.name) path state.definitions}, Passed)
            Left rejection
                | Just feature <- missing -> (state, Skipped ("needs " ++ feature))
                | isUnsupported rejection -> (state, Skipped (describeRejection rejection))
                | otherwise -> (state, Failed ("valid module rejected: " ++ describeRejection rejection))
    "module_instance" -> case cmd.definition >>= (`Map.lookup` state.definitions) of
        Just path -> runCommand "" state cmd {kind = "module", filename = Just path, name = cmd.instanceName, moduleType = Just "binary"}
        Nothing -> pure (state, Skipped "an instance of a module that is not defined")
    "assert_return" -> pure (withAction (\current i act -> assertReturn current i act cmd.expected))
    "assert_trap" -> pure (withAction (\current i act -> assertTrap current i act cmd.trapText))
    -- (An exception that leaves the function invoked: the run ends with it.)
    "assert_exception" -> pure (withAction (\current i act -> assertTrap current i act (Just (trapText UncaughtException))))
    "assert_exhaustion" -> pure (withAction (\current i act -> assertTrap current i act cmd.trapText))
    "action" -> pure (withAction (\current i act -> either (Failed . show) (const Passed) <$> invoke current i act))
    "assert_malformed" -> rejectedBy malformed
    "assert_invalid" -> rejectedBy invalid
    "assert_unlinkable" -> rejectedBy unlinkable
    "assert_uninstantiable" -> rejectedBy uninstantiable
    "register" -> pure $ case (cmd.registerAs, instanceNamed cmd.name) of
        (Just importedAs, Just i) | Just (Loaded x) <- Map.lookup i state.instances -> (state {world = register importedAs x state.world, registers = True}, Passed)
        (Just _, Just i) | Just (Unavailable reason) <- Map.lookup i state.instances -> (state {registers = True}, Skipped reason)
        _ -> (state, Skipped "command register")
    other -> pure (state, Skipped ("command " ++ T.unpack other))
  where
    -- Run a check on the instance an action names; the check hands back the script's state.
    withAction check = case cmd.action of
        Nothing -> (state, Failed "command without an action")
        Just act -> case instanceNamed act.actionModule >>= \i -> (,) i <$> Map.lookup i state.instances of
            Just (_, Loaded x) -> check state x act
            Just (_, Unavailable reason) -> (state, Skipped reason)
            Nothing -> (state, Skipped "unknown module")
    instanceNamed which = maybe state.latest (`Map.lookup` state.named) which
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
            (world', result) <- loadModule state.world path
            -- A module that uses a feature we lack is a gap whatever we answer: the decoder
            -- turns it away before the stage the assertion names is reached.
            missing <- neededFeatures path
            -- Such a module may have written into a registered module's table or memory
            -- before it failed, which persists; if we could not load it we cannot say what.
            let stale loadedBefore = case loadedBefore of
                    Loaded _ | state.registers, isJust missing -> Unavailable "its state may depend on a module that could not be linked"
                    other -> other
            pure . (,) state {world = world', instances = Map.map stale state.instances} $ case result of
                _ | Just features <- missing -> Skipped ("needs " ++ features)
                Left rejection
                    | expected rejection -> Passed
                    | isUnsupported rejection -> Skipped (describeRejection rejection)
                    | otherwise -> Failed ("rejected at the wrong stage: " ++ describeRejection rejection)
                Right _ -> Failed ("accepted a module the spec rejects: " ++ maybe "" T.unpack cmd.trapText)

{- | The features of WebAssembly this interpreter implements, as @wasm-tools validate@ names
  them: WebAssembly 2.0 without vector instructions, which is 1.0 with the mutable-global,
  sign-extension, saturating-conversion, multi-value, bulk-memory and reference-types
  extensions. (@gc-types@ enables no instruction: it lets @wasm-tools@ accept @externref@.)
-}
supportedFeatures :: String
supportedFeatures = "-all,mutable-global,saturating-float-to-int,sign-extension,multi-value,bulk-memory,reference-types,function-references,simd,relaxed-simd,multi-memory,memory64,tail-call,extended-const,exceptions,floats,gc-types"

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
    , ("garbage collection", "gc")
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
loadModule :: World -> FilePath -> IO (World, Either Rejection Int)
loadModule world path = do
    bytes <- BL.readFile path
    restricted <- lookupEnv "WASM_IFC_SECWASM_RESTRICTIONS"
    let policy = case restricted of
            Nothing -> emptyPolicy
            Just _ -> emptyPolicy {restrictions = SecWasmRestrictions}
    -- (A module that imports one object of the world twice is made to use it under one index.)
    pure $ case first AtDecode (decodeModule bytes) >>= first (AtValidation . show) . elaborateModuleWith policy . unaliased world of
        Left rejection -> (world, Left rejection)
        -- (An instance that failed while it was being initialised stays in the world, with
        -- what it had written.)
        Right validated -> case instantiateIn world validated of
            (world', result, _) -> (world', first AtInstantiation result)

-- | Perform an action on an instance of the world: @invoke@ an exported function, or @get@ an exported global.
invoke :: State -> Int -> Action -> (State, Either RunError [Value])
invoke state x act
    | act.actionKind == "get" = (state, maybe (Left (NoSuchExport act.field)) (\m -> (: []) <$> readGlobalExport m act.field) (viewInstance state.world x))
    | otherwise = case traverse literalValue act.args of
        Nothing -> (state, Left (NoSuchExport "(non-numeric argument)"))
        Just values -> case callExport state.world x act.field values of
            (world', result) -> (state {world = world'}, result)

-- | The actions the harness performs; anything else is skipped, not failed.
knownAction :: Action -> Bool
knownAction act = act.actionKind `elem` ["invoke", "get"]

-- | Each check hands back the script's state later the action.
assertReturn :: State -> Int -> Action -> [Literal] -> (State, Outcome)
assertReturn state i act expectations
    | not (knownAction act) = (state, Skipped ("action " ++ T.unpack act.actionKind))
    | any (\a -> a.litType `notElem` numericTypes) act.args = (state, Skipped "non-numeric argument")
    | otherwise = case invoke state i act of
        (later, Left err) -> (later, Failed ("invoke " ++ T.unpack act.field ++ ": " ++ show err))
        (later, Right results)
            | length results /= length expectations -> (later, Failed ("expected " ++ show (length expectations) ++ " result(s), got " ++ show results))
            | and (zipWith matches expectations results) -> (later, Passed)
            | otherwise -> (later, Failed ("invoke " ++ T.unpack act.field ++ " " ++ show (map render act.args) ++ ": expected " ++ show (map render expectations) ++ ", got " ++ show results))
  where
    render l = T.unpack l.litType ++ ":" ++ maybe "?" T.unpack l.litValue

assertTrap :: State -> Int -> Action -> Maybe Text -> (State, Outcome)
assertTrap state i act expectedText
    | not (knownAction act) = (state, Skipped ("action " ++ T.unpack act.actionKind))
    | otherwise = case invoke state i act of
        (later, Left (Trapped trap))
            -- (The suite's text may say more than ours, as in "uninitialized element 2".)
            | maybe False (trapText trap `T.isPrefixOf`) expectedText -> (later, Passed)
            | otherwise -> (later, Failed ("trapped with " ++ show trap ++ ", expected " ++ maybe "?" T.unpack expectedText))
        (later, Left err) -> (later, Failed ("invoke " ++ T.unpack act.field ++ ": " ++ show err))
        (later, Right results) -> (later, Failed ("expected a trap (" ++ maybe "?" T.unpack expectedText ++ "), got " ++ show results))

-- | The spec's wording for each trap, as the scripts assert it.
trapText :: Trap -> Text
trapText IntegerDivideByZero = "integer divide by zero"
trapText IntegerOverflow = "integer overflow"
trapText OutOfBoundsMemoryAccess = "out of bounds memory access"
trapText InvalidConversionToInteger = "invalid conversion to integer"
trapText UnreachableExecuted = "unreachable"
trapText OutOfBoundsTableAccess = "out of bounds table access"
trapText UncaughtException = "uncaught exception"
trapText NullExceptionReference = "null exception reference"
trapText NullReference = "null reference"
trapText NullFunctionReference = "null function reference"
trapText UndefinedElement = "undefined element"
trapText UninitializedElement = "uninitialized element"
trapText IndirectCallTypeMismatch = "indirect call type mismatch"
trapText CallStackExhausted = "call stack exhausted"
trapText InformationFlowViolation = "information flow violation"
trapText IndirectCallBelowBound = "indirect call below bound"
trapText (SecretRead _) = "secret read"
trapText GlobalNotRestored = "global not restored"

numericTypes :: [Text]
numericTypes = ["i32", "i64", "f32", "f64", "v128", "funcref", "externref", "exnref"]

-- | A literal's value from its bit pattern.
literalValue :: Literal -> Maybe Value
literalValue lit = case (lit.litType, lit.litValue) of
    ("funcref", Just "null") -> Just (FuncRefValue nullReference)
    ("externref", Just "null") -> Just (ExternRefValue nullReference)
    ("exnref", Just "null") -> Just (ExnRefValue nullReference)
    ("externref", Just number) -> ExternRefValue . referenceTo <$> readMaybe (T.unpack number)
    ("v128", _) -> do
        bits <- laneWidth =<< lit.laneType
        numbers <- traverse (readMaybe . T.unpack) lit.laneValues :: Maybe [Integer]
        Just (V128Value (fromLanes bits (map (fromInteger . (`mod` 2 ^ bits)) numbers)))
    _ -> numericLiteral lit

-- | The width in bits of a vector literal's lanes.
laneWidth :: Text -> Maybe Int
laneWidth written = lookup written [("i8", 8), ("i16", 16), ("i32", 32), ("i64", 64), ("f32", 32), ("f64", 64)]

numericLiteral :: Literal -> Maybe Value
numericLiteral lit = do
    -- (wabt writes a bit pattern as an unsigned decimal, wasm-tools as a signed one.)
    bits <- readMaybe . T.unpack =<< lit.litValue :: Maybe Integer
    case lit.litType of
        "i32" -> Just (I32Value (fromInteger bits))
        "i64" -> Just (I64Value (fromInteger bits))
        "f32" -> Just (F32Value (castWord32ToFloat (fromInteger bits)))
        "f64" -> Just (F64Value (castWord64ToDouble (fromInteger bits)))
        _ -> Nothing

{- | Does a result match an expectation? Bit-exact, except that a NaN class matches any NaN.
  A reference type with no value expects any reference of that type that is not null, and
  @refnull@ a null reference of any type.
-}
matches :: Literal -> Value -> Bool
matches lit actual
    | lit.litType == "either" = any (`matches` actual) lit.alternatives
    -- A vector is compared lane by lane, each lane like a scalar of the lane type.
    | V128Value vector <- actual = case (lit.litType, lit.laneType >>= laneWidth) of
        ("v128", Just bits) ->
            let actualLanes = lanes bits vector
                laneMatches expected lane
                    | expected `elem` ["nan:canonical", "nan:arithmetic"] = if bits == 32 then isNaN (castWord32ToFloat (fromIntegral lane)) else isNaN (castWord64ToDouble lane)
                    | otherwise = fmap (`mod` 2 ^ bits) (readMaybe (T.unpack expected)) == Just (toInteger lane)
             in length lit.laneValues == length actualLanes && and (zipWith laneMatches lit.laneValues actualLanes)
        _ -> False
    | Just reference <- referenceOf actual = case (lit.litType, lit.litValue) of
        ("refnull", _) -> isNullReference reference
        (expected, _) | expected /= typeName (valueType actual) -> False
        (_, Nothing) -> not (isNullReference reference)
        (_, Just "null") -> isNullReference reference
        (_, Just number) -> fmap referenceTo (readMaybe (T.unpack number)) == Just reference
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
    typeName V128 = "v128"
    typeName FuncRef = "funcref"
    typeName ExternRef = "externref"
    typeName ExnRef = "exnref"
    referenceOf value = case value of
        FuncRefValue reference -> Just reference
        ExternRefValue reference -> Just reference
        ExnRefValue reference -> Just reference
        _ -> Nothing
    width = case valueType actual of
        I64 -> 2 ^ (64 :: Int)
        F64 -> 2 ^ (64 :: Int)
        _ -> 2 ^ (32 :: Int)

isNaNValue :: Value -> Bool
isNaNValue (F32Value f) = isNaN f
isNaNValue (F64Value d) = isNaN d
isNaNValue _ = False

valueBits :: Value -> Integer
valueBits (I32Value w) = fromIntegral w
valueBits (I64Value w) = fromIntegral w
valueBits (F32Value f) = fromIntegral (castFloatToWord32 f)
valueBits (F64Value d) = fromIntegral (castDoubleToWord64 d :: Word64)
valueBits (V128Value (Vector128 low _)) = fromIntegral low
valueBits (FuncRefValue (Reference word)) = fromIntegral word
valueBits (ExternRefValue (Reference word)) = fromIntegral word
valueBits (ExnRefValue (Reference word)) = fromIntegral word

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
