{-# LANGUAGE DataKinds #-}

{- | The @cabal test@ suite. It exercises the pipeline in Haskell, without needing
  @wat2wasm@: elaboration and running are driven from 'RawModule' values built by hand, so
  we can check acceptance, rejection, traps and algebraic laws directly. (The end-to-end
  check on real @.wasm@ files lives in @samples/check.sh@.)
-}
module Main (main) where

import Control.Monad (void)
import Data.Either (isLeft)
import Data.List (isInfixOf)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Hspec
import Test.Hspec.Hedgehog (forAll, hedgehog, (===))

import Runtime.Bytes (bytesOfWord32, bytesOfWord64, word32OfBytes, word64OfBytes)
import Runtime.Examples (runFactorial, runIncrement, runSquare)
import Runtime.Numeric (intDiv32)
import Syntax.Functions (RawFunction (..))
import Syntax.Indices
import Syntax.Instructions
import Syntax.Module
import Syntax.Types
import Validation.Elaborate (ElabError, elaborateModule, runModuleFunction)

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    describe "hand-written intrinsically-typed examples" $ do
        it "factorial 5  = 120" $ runFactorial 5 `shouldBe` Right 120
        it "factorial 10 = 3628800" $ runFactorial 10 `shouldBe` Right 3628800
        it "factorial 0  = 1" $ runFactorial 0 `shouldBe` Right 1
        it "square 9     = 81" $ runSquare 9 `shouldBe` Right 81
        it "increment 41 = 42" $ runIncrement 41 `shouldBe` Right 42

    describe "elaborate + run (built from RawModule)" $ do
        it "adds two i32 parameters" $
            elabRun
                [I32, I32]
                [I32]
                []
                [LocalGet (LocalIdx 0), LocalGet (LocalIdx 1), Add SI32]
                [3, 4]
                `shouldBe` Right ["7"]
        it "signed division works" $
            elabRun
                [I32, I32]
                [I32]
                []
                [LocalGet (LocalIdx 0), LocalGet (LocalIdx 1), Div SI32 Signed]
                [20, 5]
                `shouldBe` Right ["4"]
        it "traps on divide-by-zero (a trap the types cannot rule out)" $
            elabRun
                [I32, I32]
                [I32]
                []
                [LocalGet (LocalIdx 0), LocalGet (LocalIdx 1), Div SI32 Signed]
                [7, 0]
                `shouldSatisfy` trapContaining "IntegerDivideByZero"

    describe "elaborator rejects ill-typed / malformed modules" $ do
        it "stack underflow (add with no operands)" $
            elabError [] [I32] [] [Add SI32] `shouldSatisfy` isLeft
        it "result type mismatch (empty body, i32 result declared)" $
            elabError [] [I32] [] [] `shouldSatisfy` isLeft
        it "local index out of range" $
            elabError [] [I32] [] [LocalGet (LocalIdx 9)] `shouldSatisfy` isLeft
        it "operand type mismatch (adds f32 where i32 expected)" $
            elabError [I32] [I32] [] [LocalGet (LocalIdx 0), Const SF32 1.0, Add SI32]
                `shouldSatisfy` isLeft

    describe "algebraic laws (properties)" $ do
        it "word32 -> bytes -> word32 round-trips" $ hedgehog $ do
            w <- forAll (Gen.word32 Range.linearBounded)
            word32OfBytes (bytesOfWord32 w) === w
        it "word64 -> bytes -> word64 round-trips" $ hedgehog $ do
            w <- forAll (Gen.word64 Range.linearBounded)
            word64OfBytes (bytesOfWord64 w) === w
        it "unsigned i32 division matches host div (divisor /= 0)" $ hedgehog $ do
            x <- forAll (Gen.word32 Range.linearBounded)
            y <- forAll (Gen.filter (/= 0) (Gen.word32 Range.linearBounded))
            intDiv32 Unsigned x y === Right (x `div` y)

-- | Build a single-function module exporting @f@, elaborate it, and run @f@ on integer args.
elabRun :: [ValType] -> [ValType] -> [ValType] -> [RawInstr] -> [Integer] -> Either String [String]
elabRun params results locals body args =
    case elaborateModule (singleFunctionModule params results locals body) of
        Left err -> Left (show err)
        Right sm -> runModuleFunction sm "f" args

-- | Elaborate a single-function module and discard the result — for rejection tests.
elabError :: [ValType] -> [ValType] -> [ValType] -> [RawInstr] -> Either ElabError ()
elabError params results locals body =
    void (elaborateModule (singleFunctionModule params results locals body))

singleFunctionModule :: [ValType] -> [ValType] -> [ValType] -> [RawInstr] -> RawModule
singleFunctionModule params results locals body =
    RawModule
        { moduleTypes = [ft]
        , moduleFuncs = [RawFunction ft locals body]
        , moduleGlobals = []
        , moduleMemories = []
        , moduleExports = [Export "f" (ExportFunc (FunctionIdx 0))]
        , moduleStart = Nothing
        }
  where
    ft = FuncType params results

trapContaining :: String -> Either String [String] -> Bool
trapContaining needle = either (needle `isInfixOf`) (const False)
