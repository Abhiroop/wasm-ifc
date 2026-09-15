{- | A driver for the Hackage @wasm@ package's interpreter (TODO.md §I, comparator C3), with the
  command line of ours, so bench/run.py can time it with @--binary haskell-wasm=PATH@.

  > haskell-wasm-driver invoke <module.wasm> <export>

  That interpreter is untyped Haskell of a different design from ours: it runs in IO over
  mutable vectors. It is the comparison with an untyped Haskell interpreter written
  independently, where the erased machine (bench/erased) is the one written to differ from ours
  in nothing but the types.
-}
module Main (main) where

import qualified Data.ByteString.Lazy as BL
import qualified Data.Text.Lazy as TL
import Language.Wasm (decodeLazy)
import Language.Wasm.Interpreter (Value (..), emptyImports, emptyStore, instantiate, invokeExport)
import Language.Wasm.Validate (validate)
import System.Environment (getArgs)
import System.Exit (die)

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["invoke", path, name] -> do
            bytes <- BL.readFile path
            parsed <- either (die . ("decode error: " ++)) pure (decodeLazy bytes)
            valid <- either (die . ("validation error: " ++) . show) pure (validate parsed)
            (instantiated, store) <- instantiate emptyStore emptyImports valid
            inst <- either (die . ("instantiation error: " ++)) pure instantiated
            outcome <- invokeExport store inst (TL.pack name) []
            maybe (die "trapped") (mapM_ (putStrLn . render)) outcome
        _ -> die "usage: haskell-wasm-driver invoke <module.wasm> <export>"
  where
    render value = case value of
        VI32 w -> show w
        VI64 w -> show w
        VF32 f -> show f
        VF64 d -> show d
