{-# LANGUAGE BangPatterns #-}

{- | How much is there to win by storing locals in a vector instead of a linked list?

  `locals-N` and `globals-N` in the kernel sweep grow with the index because 'setLocal' and
  'storeSetGlobal' rebuild the spine of a linked list on every store. Replacing that spine
  with a flat vector is a large, invasive change to the core (the container is heterogeneous,
  so every access has to carry the value type's singleton), so this stands the two
  representations side by side first and says what the ceiling is.

  Both models do what the interpreter does: read the local at index @d@, write it back. The
  list model mirrors 'Runtime.Stack.LocalSpaceInst' exactly — strict fields, O(index) read,
  rebuild-the-prefix write — with the value type erased to 'Word64', which is what a vector
  would store anyway.

  Read its numbers as the ceiling for a design that resolves the position /once/ — an 'Int'
  known before the loop, which is what these loops use. The prototype that kept walking the
  'Elem' witness on every access (@bench/prototypes/e2-vector-locals.patch@) ran 1.2–1.5×
  /slower/ than the list inside the interpreter, at index 64 too; see E2 in TODO.md §I.

  Compile and run (it is a measurement device, not library code, so it is built ad hoc):

  > cabal exec -- ghc -O2 -outputdir /tmp/idx -o /tmp/idx/bench bench/micro/IndexedUpdate.hs
  > /tmp/idx/bench
-}
module Main (main) where

import Control.Monad (forM_)
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector.Unboxed.Mutable as MV
import Data.Word (Word64)
import System.CPUTime (getCPUTime)
import Text.Printf (printf)

-- | The current representation: a strict cons list, read and rebuilt by unary index.
data Cells = Nil | Cons !Word64 !Cells

getCell :: Int -> Cells -> Word64
getCell _ Nil = 0
getCell 0 (Cons x _) = x
getCell n (Cons _ rest) = getCell (n - 1) rest

setCell :: Int -> Word64 -> Cells -> Cells
setCell _ _ Nil = Nil
setCell 0 v (Cons _ rest) = Cons v rest
setCell n v (Cons x rest) = Cons x (setCell (n - 1) v rest)

cellsOf :: Int -> Cells
cellsOf n = foldr Cons Nil (replicate n 0)

-- | One iteration is what the `locals-N` kernel does: read index @d@, write index @d@.
listLoop :: Int -> Int -> Cells -> Word64
listLoop 0 d cells = getCell d cells
listLoop k d !cells = listLoop (k - 1) d (setCell d (getCell d cells + fromIntegral k) cells)

-- | A flat vector, updated by copying the whole thing (@//@ builds the new vector).
copyLoop :: Int -> Int -> UV.Vector Word64 -> Word64
copyLoop 0 d v = UV.unsafeIndex v d
copyLoop k d !v = copyLoop (k - 1) d (v UV.// [(d, UV.unsafeIndex v d + fromIntegral k)])

-- | The same, writing through a mutable copy instead of an update list.
modifyLoop :: Int -> Int -> UV.Vector Word64 -> Word64
modifyLoop 0 d v = UV.unsafeIndex v d
modifyLoop k d !v =
    let x = UV.unsafeIndex v d + fromIntegral k
     in modifyLoop (k - 1) d (UV.modify (\mv -> MV.unsafeWrite mv d x) v)

iterations :: Int
iterations = 1_000_000

timed :: Word64 -> IO Double
timed result = do
    start <- getCPUTime
    seen <- pure $! result
    end <- seen `seq` getCPUTime
    pure (fromIntegral (end - start) / 1e3 / fromIntegral iterations)

main :: IO ()
main = do
    printf "one read + one write at index d, %d iterations, nanoseconds each\n\n" iterations
    printf "%5s %10s %10s %10s %10s\n" "d" "list" "vector//" "vecModify" "best win"
    forM_ [2, 4, 16, 64, 256] $ \d -> do
        let size = d + 1
        list <- timed (listLoop iterations d (cellsOf size))
        copy <- timed (copyLoop iterations d (UV.replicate size 0))
        modif <- timed (modifyLoop iterations d (UV.replicate size 0))
        printf "%5d %10.1f %10.1f %10.1f %9.2fx\n" d list copy modif (list / min copy modif)
