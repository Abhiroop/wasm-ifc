module Main where

import Control.Exception (IOException, try)
import Data.Bifunctor (first)
import Data.ByteString.Lazy qualified as BL
import Data.Text qualified as T
import System.Environment (getArgs)
import System.Exit (die)
import Text.Read (readMaybe)

import Codec.Wasm (decodeModule)
import Validation.Elaborate (elaborateModule, runModuleFunction)

main :: IO ()
main = do
    args <- getArgs
    case args of
        (path : funcName : rawArgs) -> run path funcName rawArgs
        _ -> die "Usage: wasm-ifc <file.wasm> <function> [int args...]"

{- | The pipeline: decode the binary, elaborate (validate + recover types for) the whole
  module, then run the named export through the intrinsically-typed interpreter. All the
  fallible work is a pure @Either String@; IO is only reading the file and printing. Any
  failure is reported and exits non-zero (via 'die').
-}
run :: FilePath -> String -> [String] -> IO ()
run path funcName rawArgs = do
    readResult <- try (BL.readFile path) :: IO (Either IOException BL.ByteString)
    case readResult of
        Left ioErr -> die ("Cannot read " ++ path ++ ": " ++ show ioErr)
        Right bytes -> case pipeline bytes of
            Left err -> die err
            Right output -> mapM_ putStrLn output
  where
    pipeline bytes = do
        wasmModule <- first ("Decode error: " ++) (decodeModule bytes)
        someModule <- first (\e -> "Elaboration error: " ++ show e) (elaborateModule wasmModule)
        args <- maybe (Left "arguments must be integers") Right (traverse readMaybe rawArgs)
        first ("Run error: " ++) (runModuleFunction someModule (T.pack funcName) args)
