{-# OPTIONS_GHC -fno-full-laziness #-}

{- | Front-end cost (TODO.md §I, E5): how long decoding, validation and instantiation take per
  module, against the module's size.

  > wasm-ifc-phases <module.wasm>...

  prints a CSV row per module: its path, bytes, functions, instructions, and the median
  milliseconds of each phase over as many repetitions as fill a tenth of a second.

  What each phase is timed to. Decoding: to a fully built raw module, forced by a traversal that
  walks every list and every instruction in it, less the time of the same traversal over the
  already-built module (so what remains is building it). Validation: to 'elaborateModule''s decision, which is
  when every check has run. Instantiation: likewise, to its 'Either'. A validated module may
  still hold a thunk or two that its first run forces; that is rounding next to the checks.

  Full laziness is off for this module, and each repetition applies the phase afresh through a
  NOINLINE application: otherwise GHC may float the phase out of the timing loop and compute it
  once, and every repetition after the first would time nothing.
-}
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Data.ByteString.Lazy qualified as BL
import Data.List (sort)
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)
import System.Environment (getArgs)
import System.IO (hPutStrLn, stderr)
import Text.Printf (printf)

import Codec.Wasm (decodeModule)
import Runtime.Instantiate (instantiate)
import Syntax.Functions (RawFunction (..))
import Syntax.Instructions (RawInstr (..))
import Syntax.Module (RawModule (..))
import Validation.Elaborate (elaborateModule)

main :: IO ()
main = do
    paths <- getArgs
    putStrLn "module,bytes,functions,instructions,decode_ms,validate_ms,instantiate_ms"
    forM_ paths $ \path -> do
        bytes <- BL.readFile path
        size <- evaluate (BL.length bytes)
        case decodeModule bytes of
            Left err -> hPutStrLn stderr (path ++ ": decode error: " ++ err)
            Right raw -> do
                _ <- evaluate (traversed raw)
                case elaborateModule raw of
                    Left err -> hPutStrLn stderr (path ++ ": validation error: " ++ show err)
                    Right validated -> do
                        decodeAndForce <- medianNanos (\b -> either (const False) traversed (decodeModule b)) bytes
                        traversal <- medianNanos traversed raw
                        validate <- medianNanos (either (const False) (const True) . elaborateModule) raw
                        instantiated <- medianNanos (either (const False) (const True) . instantiate) validated
                        printf
                            "%s,%d,%d,%d,%.3f,%.3f,%.3f\n"
                            path
                            size
                            (length raw.functions)
                            (sum [instructions f.body | f <- raw.functions])
                            (max 0 (decodeAndForce - traversal) / 1e6)
                            (validate / 1e6)
                            (instantiated / 1e6)

-- | The median nanoseconds of @f x@ forced to a Boolean, over enough runs to fill 100 ms (5 to 1000).
medianNanos :: (a -> Bool) -> a -> IO Double
medianNanos f x = go [] 0
  where
    go :: [Word64] -> Word64 -> IO Double
    go samples spent
        | n >= 5 && (spent >= 100_000_000 || n >= 1000) = pure (median samples)
        | otherwise = do
            start <- getMonotonicTimeNSec
            _ <- evaluate (apply f x)
            end <- getMonotonicTimeNSec
            go (end - start : samples) (spent + end - start)
      where
        n = length samples
    median samples = let sorted = sort samples in fromIntegral (sorted !! (length sorted `div` 2))

{-# NOINLINE apply #-}
apply :: (a -> b) -> a -> b
apply f x = f x

-- | Walk every list of a raw module and every instruction in every body; always 'True'.
traversed :: RawModule -> Bool
traversed m =
    sum
        [ length m.types
        , length m.imports
        , sum [instructions f.body + length f.locals | f <- m.functions]
        , length m.globals
        , length m.memories
        , length m.tables
        , length m.elementSegments
        , length m.dataSegments
        , length m.exports
        ]
        >= 0

instructions :: [RawInstr] -> Int
instructions = sum . map one
  where
    one instr = case instr of
        Block _ body -> 1 + instructions body
        Loop _ body -> 1 + instructions body
        If _ thenArm elseArm -> 1 + instructions thenArm + instructions elseArm
        _ -> 1
