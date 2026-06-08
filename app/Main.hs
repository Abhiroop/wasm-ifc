{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
module Main where

import Data.Int
import Control.Exception
import Control.Monad
import System.Environment (getArgs)
import Examples
import WasmInterpreter


{-# NOINLINE mkExec #-}
mkExec :: Int32 -> Int32
mkExec n = let (ConsValues v _) = values $ executeFactorial n in v

main :: IO ()
main = do
    args <- getArgs
    case args of
        [nStr, repStr] -> do
            let n   = read nStr
                rep = read repStr
            -- list <- replicateM rep $ do evaluate (mkExec n)
            -- s <- evaluate (sum list)
            -- print s
            res <- loop n rep 0
            print res
        _ -> putStrLn "Usage: cabal run my-exe -- <n> <rep>"

-- Attempt 2

loop :: Int32 -> Int -> Int64 -> IO Int64
loop !_ 0 !acc = return acc
loop n k !acc = do
    v <- evaluate (mkExec n)
    let acc' = acc + fromIntegral v
    acc' `seq` loop (n + 1) (k - 1) acc'