{-# LANGUAGE DataKinds #-}

{- | The @cabal test@ suite. It exercises the pipeline in Haskell, without needing
  @wat2wasm@: elaboration and running are driven from 'RawModule' values built by hand, so
  we can check acceptance, rejection, traps and algebraic laws directly. (The end-to-end
  check on real @.wasm@ files lives in @samples/check.sh@.)
-}
module Main (main) where

import Control.Monad (void)
import Data.ByteString.Lazy qualified as BL
import Data.Either (isLeft, isRight)
import Data.List (isInfixOf)
import Data.Word (Word32, Word8)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Hspec
import Test.Hspec.Hedgehog (forAll, hedgehog, (===))

import Codec.Wasm (decodeModule)
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
        it "select keeps the first operand when the condition is non-zero" $
            elabRun [I32, I32, I32] [I32] [] [LocalGet (LocalIdx 0), LocalGet (LocalIdx 1), LocalGet (LocalIdx 2), Select] [1, 2, 1]
                `shouldBe` Right ["1"]
        it "select keeps the second operand when the condition is zero" $
            elabRun [I32, I32, I32] [I32] [] [LocalGet (LocalIdx 0), LocalGet (LocalIdx 1), LocalGet (LocalIdx 2), Select] [1, 2, 0]
                `shouldBe` Right ["2"]
        it "traps on unreachable" $
            elabRun [] [I32] [] [Unreachable] [] `shouldSatisfy` trapContaining "UnreachableExecuted"
        it "traps on an invalid float-to-int conversion (NaN)" $
            elabRun [] [I32] [] [Const SF32 (0 / 0), Convert (I32TruncF32 Signed)] []
                `shouldSatisfy` trapContaining "InvalidConversionToInteger"
        it "traps on an out-of-bounds load" $
            elabRunWithMemory [I32] [I32] [] [LocalGet (LocalIdx 0), Load SI32 (MemArg 0 0)] [70000]
                `shouldSatisfy` trapContaining "OutOfBoundsMemoryAccess"

    describe "memory.grow (the old size on success, -1 when it cannot grow)" $ do
        it "grows within the declared maximum" $
            elabRunIn [memoryWithMax 1 2] [] [I32] [] [Const SI32 1, MemoryGrow] [] `shouldBe` Right ["1"]
        it "refuses to grow past the declared maximum" $
            elabRunIn [memoryWithMax 1 2] [] [I32] [] [Const SI32 2, MemoryGrow] [] `shouldBe` Right ["4294967295"]
        it "refuses to grow past 65536 pages" $
            elabRunWithMemory [] [I32] [] [Const SI32 70000, MemoryGrow] [] `shouldBe` Right ["4294967295"]
        it "memory.size reflects a successful grow" $
            elabRunWithMemory [] [I32] [] [Const SI32 3, MemoryGrow, Drop, MemorySize] [] `shouldBe` Right ["4"]

    describe "float rounding corner cases" $ do
        it "ceil keeps NaN" $
            elabRun [] [F32] [] [Const SF32 (0 / 0), Ceil SF32] [] `shouldBe` Right ["NaN"]
        it "floor keeps infinity" $
            elabRun [] [F64] [] [Const SF64 (1 / 0), Floor SF64] [] `shouldBe` Right ["Infinity"]
        it "ceil of -0.5 is negative zero" $
            elabRun [] [F32] [] [Const SF32 (-0.5), Ceil SF32] [] `shouldBe` Right ["-0.0"]
        it "trunc of -0.3 is negative zero" $
            elabRun [] [F64] [] [Const SF64 (-0.3), FloatTrunc SF64] [] `shouldBe` Right ["-0.0"]
        it "nearest rounds ties to even" $
            elabRun [] [F32] [] [Const SF32 2.5, Nearest SF32] [] `shouldBe` Right ["2.0"]
        it "nearest of -0.5 is negative zero" $
            elabRun [] [F32] [] [Const SF32 (-0.5), Nearest SF32] [] `shouldBe` Right ["-0.0"]

    describe "dead code after an unconditional transfer" $ do
        it "is typed under the polymorphic stack (an add with nothing pushed is fine)" $
            elabError [] [I32] [] [Const SI32 1, Return, Add SI32] `shouldSatisfy` isRight
        it "is still checked where operand types are known (f32 fed to i32.add)" $
            elabError [] [I32] [] [Const SI32 1, Return, Const SF32 1.0, Add SI32] `shouldSatisfy` isLeft
        it "may not branch to a label that does not exist" $
            elabError [] [I32] [] [Const SI32 1, Return, Br (LabelIdx 5)] `shouldSatisfy` isLeft

    describe "decoder (hand-assembled binaries)" $ do
        it "accepts a minimal module with one empty function" $
            decodeSections [typeSection, funcSection [0], codeSection [[0x0B]]] `shouldBe` Right 1
        it "rejects a bad magic number" $
            decodeBytes [0x00, 0x61, 0x73, 0x6E, 0x01, 0x00, 0x00, 0x00] `shouldSatisfy` isLeft
        it "rejects an unsupported version" $
            decodeBytes [0x00, 0x61, 0x73, 0x6D, 0x02, 0x00, 0x00, 0x00] `shouldSatisfy` isLeft
        it "rejects function and code sections of different lengths" $
            decodeSections [typeSection, funcSection [0], codeSection []]
                `shouldSatisfy` decodeErrorContaining "different lengths"
        it "rejects a function type index out of range" $
            decodeSections [typeSection, funcSection [7], codeSection [[0x0B]]]
                `shouldSatisfy` decodeErrorContaining "function type index out of range"
        it "rejects a block type index out of range" $
            decodeSections [typeSection, funcSection [0], codeSection [[0x02, 0x05, 0x0B, 0x0B]]]
                `shouldSatisfy` decodeErrorContaining "block type index out of range"
        it "rejects an unknown opcode" $
            decodeSections [typeSection, funcSection [0], codeSection [[0xFF, 0x0B]]]
                `shouldSatisfy` decodeErrorContaining "unsupported opcode"

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

memoryWithMax :: Word32 -> Word32 -> RawMemory
memoryWithMax lo hi = RawMemory (MemType AddrI32 (Limits lo (Just hi)))

{- *** Hand-assembled binaries ***

   Just enough of the binary format to reach the decoder's error paths without @wat2wasm@:
   a header, and sections whose payloads are short enough for one-byte LEB128 sizes.
-}

-- | Decode raw bytes, reduced to the number of functions ('RawModule' has no 'Show').
decodeBytes :: [Word8] -> Either String Int
decodeBytes bytes = fmap (length . (.moduleFuncs)) (decodeModule (BL.pack bytes))

decodeSections :: [[Word8]] -> Either String Int
decodeSections sections = decodeBytes (wasmHeader ++ concat sections)

wasmHeader :: [Word8]
wasmHeader = [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00]

-- | A section: its id, its byte size, its payload.
section :: Word8 -> [Word8] -> [Word8]
section sectionId payload = sectionId : fromIntegral (length payload) : payload

-- | A length-prefixed vector.
vec :: [[Word8]] -> [Word8]
vec items = fromIntegral (length items) : concat items

-- | The type section with a single type, @() -> ()@.
typeSection :: [Word8]
typeSection = section 1 (vec [[0x60, 0x00, 0x00]])

-- | The function section: one type index per function.
funcSection :: [Word8] -> [Word8]
funcSection typeIndices = section 3 (vec [[i] | i <- typeIndices])

-- | The code section: one body per function, declaring no locals (each body must end in 0x0B).
codeSection :: [[Word8]] -> [Word8]
codeSection bodies = section 10 (vec [entry body | body <- bodies])
  where
    entry body = let content = 0x00 : body in fromIntegral (length content) : content

decodeErrorContaining :: String -> Either String Int -> Bool
decodeErrorContaining needle = either (needle `isInfixOf`) (const False)

-- | An i32 written as a signed literal (the stack holds raw bits).
fromSigned32Test :: Int -> Word32
fromSigned32Test = fromIntegral

trapContaining :: String -> Either String [String] -> Bool
trapContaining needle = either (needle `isInfixOf`) (const False)
