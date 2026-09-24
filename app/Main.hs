module Main where

import Control.Exception (IOException, try)
import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.Bits ((.|.))
import Data.ByteString.Lazy qualified as BL
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Float (castWord32ToFloat, castWord64ToDouble)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), die, exitSuccess, exitWith)
import Text.Read (readMaybe)

import Codec.Wasm (decodeModule)
import Data.Map.Strict qualified as Map
import Data.Text.IO qualified as TIO
import Runtime.Instantiate (instantiate)
import Runtime.Module (RunError (..), SomeModuleInst, Value (..), exportSignature, readGlobalExport, renderValue)
import Runtime.Wasi (Completion (..), DescriptorLevels (..), Preopen (..), WasiConfig (..), runWithWasi)
import Syntax.Module (SomeModule)
import Syntax.Types (FuncTypeOf (..), ValType (..))
import Syntax.TypesIFC (SecLevel (..))
import System.FilePath (takeFileName)
import Validation.Elaborate (elaborateModuleWith)
import Validation.Policy (Policy (..), emptyPolicy, modulePolicy, parsePolicy)

main :: IO ()
main = do
    args <- getArgs
    case args of
        ("check" : rest) -> case parseOptions rest of
            Right (options, [path]) -> withValidated options path (\_ _ -> putStrLn "ok")
            _ -> die usage
        ("get" : rest) -> case parseOptions rest of
            Right (options, [path, name]) -> withModule options path $ \_ wasmModule ->
                either (die . describeRunError) (putStrLn . renderValue) (readGlobalExport wasmModule (T.pack name))
            _ -> die usage
        ("invoke" : rest) -> case parseOptions rest of
            Right (options, path : name : rawArgs) ->
                withModule options path $ \policy wasmModule ->
                    case parseArguments wasmModule (T.pack name) (map T.pack rawArgs) of
                        Left err -> die err
                        Right values -> runUnderWasi (configFor options policy path []) wasmModule (T.pack name) values (mapM_ (putStrLn . renderValue))
            _ -> die usage
        ("run" : rest) -> case parseOptions rest of
            Right (options, path : programArgs) ->
                withModule options path $ \policy wasmModule -> case exportSignature wasmModule "_start" of
                    Nothing -> die "the module has no _start export"
                    Just (FuncType [] []) -> runUnderWasi (configFor options policy path programArgs) wasmModule "_start" [] (\_ -> pure ())
                    Just _ -> die "_start must take no parameters and return nothing"
            _ -> die usage
        _ -> die usage

usage :: String
usage =
    unlines
        [ "Usage:"
        , "  wasm-ifc check  [options] <file.wasm>                    decode and validate (no instantiation)"
        , "  wasm-ifc invoke [options] <file.wasm> <export> [args...] run an exported function"
        , "  wasm-ifc get    [options] <file.wasm> <global>           print an exported global"
        , "  wasm-ifc run    [options] <file.wasm> [program args...]  run a WASI program (its _start export)"
        , ""
        , "Options:  --policy FILE         the module's security policy (levels of its interface, memory"
        , "                                accesses and regions); merged with the module's own ifc section"
        , "          --dir HOST[::GUEST]   preopen a host directory under the guest name (default: the same)"
        , "          --env NAME=VALUE      an environment variable for the program"
        , ""
        , "Arguments to invoke are typed by the export: integers (decimal or 0x…) for i32/i64;"
        , "decimals, inf, -inf, nan, -nan or a bit pattern nan:0x… for f32/f64. WASI Preview 1"
        , "host calls are served; proc_exit's code becomes the exit code."
        ]

-- | The @--dir@ and @--env@ options before the module path.
data Options = Options
    { dirs :: [Preopen]
    , vars :: [(Text, Text)]
    , policyFile :: Maybe FilePath
    }

parseOptions :: [String] -> Either String (Options, [String])
parseOptions = go (Options [] [] Nothing)
  where
    go options ("--policy" : file : rest) = go options {policyFile = Just file} rest
    go options ("--dir" : spec : rest) =
        let (host, guest) = case T.splitOn "::" (T.pack spec) of
                [h, g] -> (T.unpack h, g)
                _ -> (spec, T.pack spec)
         in go options {dirs = options.dirs ++ [Preopen guest host]} rest
    go options ("--env" : spec : rest) = case T.breakOn "=" (T.pack spec) of
        (name, value) | not (T.null value) -> go options {vars = options.vars ++ [(name, T.drop 1 value)]} rest
        _ -> Left ("--env expects NAME=VALUE, got " ++ spec)
    go options rest = Right (options, rest)

configFor :: Options -> Policy -> FilePath -> [String] -> WasiConfig
configFor options policy path programArgs =
    WasiConfig
        { arguments = map T.pack (takeFileName path : programArgs)
        , environment = options.vars
        , preopens = options.dirs
        , descriptorLevels =
            DescriptorLevels
                { standardInput = stream "stdin"
                , standardOutput = stream "stdout"
                , standardError = stream "stderr"
                , preopenLevels = policy.preopenLevels
                }
        }
  where
    stream name = Map.findWithDefault Low name policy.streamLevels

-- | Invoke an export with the WASI host serving its calls; hand the results to the printer.
runUnderWasi :: WasiConfig -> SomeModuleInst -> Text -> [Value] -> ([Value] -> IO ()) -> IO ()
runUnderWasi cfg wasmModule name args printResults = do
    completion <- runWithWasi cfg wasmModule name args
    case completion of
        Left err -> die (describeRunError err)
        Right (Ran _ results) -> printResults results
        Right (Exited 0) -> exitSuccess
        Right (Exited code) -> exitWith (ExitFailure code)

{- | Decode and validate a module from disk, then hand it to the action. All the fallible
  work is a pure @Either String@; IO is only reading the file and printing. Any failure is
  reported and exits non-zero (via 'die').
-}
withValidated :: Options -> FilePath -> (Policy -> SomeModule -> IO ()) -> IO ()
withValidated options path action = do
    policy <- case options.policyFile of
        Nothing -> pure emptyPolicy
        Just file -> do
            policyText <- try (TIO.readFile file) :: IO (Either IOException Text)
            case policyText of
                Left ioErr -> die ("Cannot read " ++ file ++ ": " ++ show ioErr)
                Right text -> either (\e -> die ("Policy error: " ++ show e)) pure (parsePolicy text)
    readResult <- try (BL.readFile path) :: IO (Either IOException BL.ByteString)
    case readResult of
        Left ioErr -> die ("Cannot read " ++ path ++ ": " ++ show ioErr)
        Right bytes -> case pipeline policy bytes of
            Left err -> die err
            Right (inForce, validated) -> action inForce validated
  where
    -- The policy in force is the given one merged with the module's own section; the WASI
    -- host reads the descriptor levels off it.
    pipeline policy bytes = do
        raw <- first ("Decode error: " ++) (decodeModule bytes)
        inForce <- first (\e -> "Policy error: " ++ show e) (modulePolicy policy raw)
        validated <- first (\e -> "Validation error: " ++ show e) (elaborateModuleWith policy raw)
        Right (inForce, validated)

-- | 'withValidated', then instantiate: the module ready to have an export invoked.
withModule :: Options -> FilePath -> (Policy -> SomeModuleInst -> IO ()) -> IO ()
withModule options path action = withValidated options path $ \policy validated ->
    case instantiate validated of
        Left err -> die ("Instantiation error: " ++ show err)
        Right wasmModule -> action policy wasmModule

-- | Parse the textual arguments at the export's parameter types.
parseArguments :: SomeModuleInst -> Text -> [Text] -> Either String [Value]
parseArguments wasmModule name rawArgs = do
    FuncType params _ <- maybe (Left ("no exported function named " ++ T.unpack name)) Right (exportSignature wasmModule name)
    unless (length params == length rawArgs) $
        Left ("expected " ++ show (length params) ++ " argument(s), got " ++ show (length rawArgs))
    traverse parseArgument (zip params rawArgs)
  where
    parseArgument (valType, raw) =
        maybe (Left ("cannot read " ++ T.unpack raw ++ " as " ++ show valType)) Right (parseValue valType raw)

describeRunError :: RunError -> String
describeRunError err = case err of
    NoSuchExport name -> "no exported function named " ++ T.unpack name
    ArgumentCount expectedCount actualCount ->
        "expected " ++ show expectedCount ++ " argument(s), got " ++ show actualCount
    ArgumentType position expectedType actualType ->
        "argument " ++ show position ++ " should be " ++ show expectedType ++ ", got " ++ show actualType
    Trapped trap -> "trap: " ++ show trap
    HostCallNotServed -> "the function called into the host, which this path cannot serve"

{- | Read one argument at a value type. Integers wrap to the type's width (so @-1@ is a valid
  i32); floats accept decimals, the infinities, NaN, and a NaN with an explicit payload
  (@nan:0x…@, the spec's text-format notation).
-}
parseValue :: ValType -> Text -> Maybe Value
parseValue valType raw = case valType of
    I32 -> I32Value . fromInteger <$> readInteger
    I64 -> I64Value . fromInteger <$> readInteger
    F32 -> F32Value <$> readFloat (castWord32ToFloat . fromInteger) 0x7F800000
    F64 -> F64Value <$> readFloat (castWord64ToDouble . fromInteger) 0x7FF0000000000000
  where
    text = T.unpack raw
    readInteger = readMaybe text :: Maybe Integer
    -- The canonical NaN is @abs (0 / 0)@ rather than a bit-cast of its literal bits: GHC 9.12
    -- panics when constant-folding 'castWord32ToFloat' applied to a literal.
    readFloat :: (RealFloat a, Read a) => (Integer -> a) -> Integer -> Maybe a
    readFloat fromBits exponentBits = case text of
        "inf" -> Just (1 / 0)
        "-inf" -> Just (negate (1 / 0))
        "nan" -> Just (abs (0 / 0))
        "-nan" -> Just (negate (abs (0 / 0)))
        _ | Just payload <- T.stripPrefix "nan:" raw -> fromBits . (.|. exponentBits) <$> readMaybe (T.unpack payload)
        _ -> readMaybe text
