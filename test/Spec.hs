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
import Data.Word (Word32)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Hspec
import Test.Hspec.Hedgehog (forAll, hedgehog, (===))

import Runtime.Bytes (bytesOfWord32, bytesOfWord64, word32OfBytes, word64OfBytes)
import Runtime.Convert (convertVal)
import Runtime.Examples (runFactorial, runIncrement, runSquare)
import Runtime.Numeric (intDiv32)
import Runtime.Trap (Trap (..))
import Syntax.Functions (RawFunction (..))
import Syntax.Indices
import Syntax.Instructions
import Syntax.Memories (RawMemory (..))
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
        it "eqz on a float (an integer-only instruction)" $
            elabError [F32] [I32] [] [LocalGet (LocalIdx 0), Eqz SF32] `shouldSatisfy` isLeft
        it "4-byte narrow load of an i32 (not narrower than the value)" $
            elabErrorWithMemory [I32] [I32] [] [LocalGet (LocalIdx 0), LoadN SI32 4 Signed (MemArg 0 0)]
                `shouldSatisfy` isLeft
        it "over-aligned load (2^align exceeds the access width)" $
            elabErrorWithMemory [I32] [I32] [] [LocalGet (LocalIdx 0), Load SI32 (MemArg 3 0)]
                `shouldSatisfy` isLeft

    describe "elaborator refines witnesses (accepts what the spec allows)" $ do
        it "float comparison drops the (meaningless) signedness" $
            elabRun
                [F32, F32]
                [I32]
                []
                [LocalGet (LocalIdx 0), LocalGet (LocalIdx 1), Lt SF32 Signed]
                [1, 2]
                `shouldBe` Right ["1"]
        it "maximal legal alignment on an i64 load (2^3 = 8 bytes)" $
            elabRunWithMemory
                [I32]
                [I64]
                []
                [LocalGet (LocalIdx 0), Load SI64 (MemArg 3 0)]
                [0]
                `shouldBe` Right ["0"]

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
        it "i64.extend_i32_u then i32.wrap_i64 is the identity" $ hedgehog $ do
            w <- forAll (Gen.word32 Range.linearBounded)
            (convertVal I32WrapI64 =<< convertVal (I64ExtendI32 Unsigned) w) === Right w
        it "i64.extend_i32_s then i32.wrap_i64 is the identity" $ hedgehog $ do
            w <- forAll (Gen.word32 Range.linearBounded)
            (convertVal I32WrapI64 =<< convertVal (I64ExtendI32 Signed) w) === Right w
        it "f32.reinterpret_i32 then i32.reinterpret_f32 is the identity on the bits" $ hedgehog $ do
            w <- forAll (Gen.word32 Range.linearBounded)
            (convertVal I32ReinterpretF32 =<< convertVal F32ReinterpretI32 w) === Right w
        it "f64.promote_f32 then f32.demote_f64 is the identity on finite floats" $ hedgehog $ do
            f <- forAll (Gen.float (Range.linearFracFrom 0 (-1e30) 1e30))
            (convertVal F32DemoteF64 =<< convertVal F64PromoteF32 f) === Right f
        it "f64.convert_i32_s then i32.trunc_f64_s is the identity" $ hedgehog $ do
            w <- forAll (Gen.word32 Range.linearBounded)
            (convertVal (I32TruncF64 Signed) =<< convertVal (F64ConvertI32 Signed) w) === Right w

    describe "conversion corner cases" $ do
        it "f32.demote_f64 keeps NaN a NaN" $
            fmap isNaN (convertVal F32DemoteF64 (0 / 0 :: Double)) `shouldBe` Right True
        it "f32.demote_f64 keeps infinity infinite" $
            fmap isInfinite (convertVal F32DemoteF64 (1 / 0 :: Double)) `shouldBe` Right True
        it "i32.trunc_f32_u traps on NaN" $
            convertVal (I32TruncF32 Unsigned) (0 / 0 :: Float) `shouldBe` Left InvalidConversionToInteger
        it "i32.trunc_f32_u traps on 2^32" $
            convertVal (I32TruncF32 Unsigned) (4294967296 :: Float) `shouldBe` Left IntegerOverflow
        it "i32.trunc_f64_s truncates toward zero" $
            convertVal (I32TruncF64 Signed) (-3.9 :: Double) `shouldBe` Right (fromSigned32Test (-3))

-- | Build a single-function module exporting @f@, elaborate it, and run @f@ on integer args.
elabRun :: [ValType] -> [ValType] -> [ValType] -> [RawInstr] -> [Integer] -> Either String [String]
elabRun = elabRunIn []

-- | 'elabRun' for a module that also declares one (one-page) memory.
elabRunWithMemory :: [ValType] -> [ValType] -> [ValType] -> [RawInstr] -> [Integer] -> Either String [String]
elabRunWithMemory = elabRunIn [onePageMemory]

elabRunIn :: [RawMemory] -> [ValType] -> [ValType] -> [ValType] -> [RawInstr] -> [Integer] -> Either String [String]
elabRunIn memories params results locals body args =
    case elaborateModule (singleFunctionModule memories params results locals body) of
        Left err -> Left (show err)
        Right sm -> runModuleFunction sm "f" args

-- | Elaborate a single-function module and discard the result — for rejection tests.
elabError :: [ValType] -> [ValType] -> [ValType] -> [RawInstr] -> Either ElabError ()
elabError = elabErrorIn []

-- | 'elabError' for a module that also declares one memory (so memory instructions elaborate).
elabErrorWithMemory :: [ValType] -> [ValType] -> [ValType] -> [RawInstr] -> Either ElabError ()
elabErrorWithMemory = elabErrorIn [onePageMemory]

elabErrorIn :: [RawMemory] -> [ValType] -> [ValType] -> [ValType] -> [RawInstr] -> Either ElabError ()
elabErrorIn memories params results locals body =
    void (elaborateModule (singleFunctionModule memories params results locals body))

singleFunctionModule :: [RawMemory] -> [ValType] -> [ValType] -> [ValType] -> [RawInstr] -> RawModule
singleFunctionModule memories params results locals body =
    RawModule
        { moduleTypes = [ft]
        , moduleFuncs = [RawFunction ft locals body]
        , moduleGlobals = []
        , moduleMemories = memories
        , moduleExports = [Export "f" (ExportFunc (FunctionIdx 0))]
        , moduleStart = Nothing
        }
  where
    ft = FuncType params results

onePageMemory :: RawMemory
onePageMemory = RawMemory (MemType AddrI32 (Limits 1 Nothing))

-- | An i32 written as a signed literal (the stack holds raw bits).
fromSigned32Test :: Int -> Word32
fromSigned32Test = fromIntegral

trapContaining :: String -> Either String [String] -> Bool
trapContaining needle = either (needle `isInfixOf`) (const False)
