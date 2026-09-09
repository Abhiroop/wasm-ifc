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
import Runtime.Module (RunError (..), SomeModule, Value (..), exportSignature, renderValue)
import Runtime.Wasi (Completion (..), runWithWasi)
import Syntax.Types (FuncType (..), ValType (..))
import Validation.Elaborate (elaborateModule)

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["check", path] -> withModule path (\_ -> putStrLn "ok")
        ("invoke" : path : name : rawArgs) ->
            withModule path $ \wasmModule ->
                case parseArguments wasmModule (T.pack name) (map T.pack rawArgs) of
                    Left err -> die err
                    Right values -> runUnderWasi wasmModule (T.pack name) values (mapM_ (putStrLn . renderValue))
        ["run", path] ->
            withModule path $ \wasmModule -> case exportSignature wasmModule "_start" of
                Nothing -> die "the module has no _start export"
                Just (FuncType [] []) -> runUnderWasi wasmModule "_start" [] (\_ -> pure ())
                Just _ -> die "_start must take no parameters and return nothing"
        _ -> die usage

usage :: String
usage =
    unlines
        [ "Usage:"
        , "  wasm-ifc check  <file.wasm>                    decode and validate"
        , "  wasm-ifc invoke <file.wasm> <export> [args...] run an exported function"
        , "  wasm-ifc run    <file.wasm>                    run a WASI program (its _start export)"
        , ""
        , "Arguments are typed by the export: integers (decimal or 0x…) for i32/i64; decimals,"
        , "inf, -inf, nan, -nan or a bit pattern nan:0x… for f32/f64. Host calls (fd_write to"
        , "the standard streams, proc_exit) are served; proc_exit's code becomes the exit code."
        ]

-- | Invoke an export with the WASI host serving its calls; hand the results to the printer.
runUnderWasi :: SomeModule -> Text -> [Value] -> ([Value] -> IO ()) -> IO ()
runUnderWasi wasmModule name args printResults = do
    completion <- runWithWasi wasmModule name args
    case completion of
        Left err -> die (describeRunError err)
        Right (Ran _ results) -> printResults results
        Right (Exited 0) -> exitSuccess
        Right (Exited code) -> exitWith (ExitFailure code)

{- | Decode and elaborate a module from disk, then hand it to the action. All the fallible
  work is a pure @Either String@; IO is only reading the file and printing. Any failure is
  reported and exits non-zero (via 'die').
-}
withModule :: FilePath -> (SomeModule -> IO ()) -> IO ()
withModule path action = do
    readResult <- try (BL.readFile path) :: IO (Either IOException BL.ByteString)
    case readResult of
        Left ioErr -> die ("Cannot read " ++ path ++ ": " ++ show ioErr)
        Right bytes -> case pipeline bytes of
            Left err -> die err
            Right wasmModule -> action wasmModule
  where
    pipeline bytes = do
        raw <- first ("Decode error: " ++) (decodeModule bytes)
        first (\e -> "Elaboration error: " ++ show e) (elaborateModule raw)

-- | Parse the textual arguments at the export's parameter types.
parseArguments :: SomeModule -> Text -> [Text] -> Either String [Value]
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
