module Main where

import qualified Data.ByteString.Lazy as BL
import qualified Data.Text as T
import System.Environment (getArgs)

import Codec.Wasm      (decodeModule)
import Validation.Elaborate (elaborateModule, runModuleFunction)

main :: IO ()
main = do
    args <- getArgs
    case args of
        (path : funcName : rawArgs) -> run path funcName rawArgs
        _ -> putStrLn "Usage: wasm-ifc <file.wasm> <function> [args...]"

-- | The pipeline: decode the binary, elaborate (validate + recover types for) the whole
--   module, then run the named export through the intrinsically-typed interpreter.
run :: FilePath -> String -> [String] -> IO ()
run path funcName rawArgs = do
    bytes <- BL.readFile path
    case decodeModule bytes of
        Left err -> putStrLn ("Decode error: " ++ err)
        Right wasmModule -> case elaborateModule wasmModule of
            Left elabErr     -> putStrLn ("Elaboration error: " ++ show elabErr)
            Right someModule -> case runModuleFunction someModule (T.pack funcName) (map read rawArgs) of
                Left err     -> putStrLn ("Run error: " ++ err)
                Right result -> mapM_ putStrLn result
