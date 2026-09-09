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
import System.Exit (die)
import Text.Read (readMaybe)

import Codec.Wasm (decodeModule)
import Runtime.Module (RunError (..), SomeModule, Value (..), exportSignature, invokeExport, renderValue)
import Syntax.Types (FuncType (..), ValType (..))
import Validation.Elaborate (elaborateModule)

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["check", path] -> withModule path (\_ -> putStrLn "ok")
        ("invoke" : path : name : rawArgs) ->
            withModule path $ \wasmModule ->
                case invokeWithText wasmModule (T.pack name) (map T.pack rawArgs) of
                    Left err -> die err
                    Right results -> mapM_ (putStrLn . renderValue) results
        _ -> die usage

usage :: String
usage =
    unlines
        [ "Usage:"
        , "  wasm-ifc check  <file.wasm>                    decode and validate"
        , "  wasm-ifc invoke <file.wasm> <export> [args...] run an exported function"
        , ""
        , "Arguments are typed by the export: integers (decimal or 0x…) for i32/i64; decimals,"
        , "inf, -inf, nan, -nan or a bit pattern nan:0x… for f32/f64."
        ]

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

-- | Parse the textual arguments at the export's parameter types, then invoke it.
invokeWithText :: SomeModule -> Text -> [Text] -> Either String [Value]
invokeWithText wasmModule name rawArgs = do
    FuncType params _ <- maybe (Left ("no exported function named " ++ T.unpack name)) Right (exportSignature wasmModule name)
    unless (length params == length rawArgs) $
        Left ("expected " ++ show (length params) ++ " argument(s), got " ++ show (length rawArgs))
    args <- traverse parseArgument (zip params rawArgs)
    first describeRunError (invokeExport wasmModule name args)
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
