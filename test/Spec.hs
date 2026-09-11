{-# LANGUAGE DataKinds #-}

{- | The @cabal test@ suite. It exercises the pipeline in Haskell, without needing
  @wat2wasm@: elaboration and running are driven from 'RawModule' values built by hand, so
  we can check acceptance, rejection, traps and algebraic laws directly. (The end-to-end
  check on real @.wasm@ files lives in @samples/check.sh@.)
-}
module Main (main) where

import Control.Monad (void)
import Data.Bifunctor (first)
import Data.Bits (xor, (.&.), (.|.))
import Data.ByteString.Lazy qualified as BL
import Data.Either (isLeft, isRight)
import Data.List (isInfixOf)
import Data.Text (Text)
import Data.Word (Word32, Word8)
import Hedgehog (Gen)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Hspec
import Test.Hspec.Hedgehog (forAll, hedgehog, (===))

import Codec.Wasm (decodeModule)
import Examples (labelledSumLength, runFactorial, runIncrement, runSpinFor, runSquare)
import Runtime.Bytes (bytesOfWord32, bytesOfWord64, word32OfBytes, word64OfBytes)
import Runtime.Convert (convertVal)
import Runtime.Host (WasiFunc (..))
import Runtime.Instantiate (InstantiationError (..), instantiate)
import Runtime.Interpreter (HostRequest (..), callDepthBound, resumeWith)
import Runtime.Module (Invocation (..), RunError (..), SomeHostRequest (..), SomeModuleInst, Value (..), continueWith, exportSignature, invokeExport, readGlobalExport, renderValue)
import Runtime.Numeric (intDiv32)
import Runtime.Stack (ValueStack (..))
import Runtime.Trap (Trap (..))
import Runtime.Wasi (Completion (..), WasiConfig (..), runWithWasi)
import Syntax.Functions (RawFunction (..))
import Syntax.Globals (RawGlobal (..))
import Syntax.Immediates
import Syntax.Indices
import Syntax.Instructions
import Syntax.Module (DataMode (..), Export (..), ExportDesc (..), ImportDesc (..), RawDataSegment (..), RawElementSegment (..), RawImport (..), RawMemory (..), RawModule (..), RawTable (..))
import Syntax.Types
import Validation.Elaborate (ElabError (..), IndexSpace (..), elaborateModule)

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    describe "hand-written intrinsically-typed examples (test/Examples.hs)" $ do
        it "factorial 5  = 120" $ runFactorial 5 `shouldBe` Right 120
        it "factorial 10 = 3628800" $ runFactorial 10 `shouldBe` Right 3628800
        it "factorial 0  = 1" $ runFactorial 0 `shouldBe` Right 1
        it "square 9     = 81" $ runSquare 9 `shouldBe` Right 81
        it "an endless loop is still running when the step budget is spent" $ runSpinFor 1000 `shouldBe` Right True
        it "increment 41 = 42" $ runIncrement 41 `shouldBe` Right 42
        it "a secret plus a public value is typed secret (the first labelled program)" $ labelledSumLength `shouldBe` 3

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
        it "typed select names the operand type" $
            elabRun [I32, I32, I32] [I32] [] [LocalGet (LocalIdx 0), LocalGet (LocalIdx 1), LocalGet (LocalIdx 2), SelectTyped [I32]] [1, 2, 1]
                `shouldBe` Right ["1"]
        it "typed select rejects an annotation the operands do not have" $
            elabError [] [I32] [] [Const SI32 1, Const SI32 2, Const SI32 0, SelectTyped [I64]]
                `shouldBe` Left (OperandMismatch "select" I64 I32)
        it "typed select needs exactly one type" $
            elabError [] [I32] [] [Const SI32 1, Const SI32 2, Const SI32 0, SelectTyped []]
                `shouldBe` Left (InvalidSelectArity 0)
        it "traps on unreachable" $
            elabRun [] [I32] [] [Unreachable] [] `shouldSatisfy` trapContaining "UnreachableExecuted"
        it "traps on an invalid float-to-int conversion (NaN)" $
            elabRun [] [I32] [] [Const SF32 (0 / 0), Convert (I32TruncF32 Signed)] []
                `shouldSatisfy` trapContaining "InvalidConversionToInteger"
        it "traps on an out-of-bounds load" $
            elabRunWithMemory [I32] [I32] [] [LocalGet (LocalIdx 0), Load SI32 (MemArg 0 0)] [70000]
                `shouldSatisfy` trapContaining "OutOfBoundsMemoryAccess"
        it "traps when a runaway recursion exhausts the call stack" $
            elabRun [] [] [] [Call (FunctionIdx 0)] [] `shouldSatisfy` trapContaining "CallStackExhausted"
        it "allows recursion exactly up to the call-depth bound" $ do
            -- @f n@ recurses to @f 0@ and counts back up, so a call with @n@ nests @n + 1@ activations.
            let countdown = [LocalGet (LocalIdx 0), LocalGet (LocalIdx 0), Eqz SI32, BrIf (LabelIdx 0), Const SI32 1, Sub SI32, Call (FunctionIdx 0), Const SI32 1, Add SI32]
                deepest = fromIntegral callDepthBound - 1
            elabRun [I32] [I32] [] countdown [deepest] `shouldBe` Right [show deepest]
            elabRun [I32] [I32] [] countdown [deepest + 1] `shouldSatisfy` trapContaining "CallStackExhausted"

    describe "indirect calls" $ do
        it "go through the table entry, typed" $
            elabRunModule (tableModule [Const SI32 0, CallIndirect (TypeIdx 0)]) [] `shouldBe` Right ["42"]
        it "trap on an uninitialised entry" $
            elabRunModule (tableModule [Const SI32 1, CallIndirect (TypeIdx 0)]) [] `shouldSatisfy` trapContaining "UninitializedElement"
        it "trap on an index past the table" $
            elabRunModule (tableModule [Const SI32 3, CallIndirect (TypeIdx 0)]) [] `shouldSatisfy` trapContaining "UndefinedElement"
        it "trap when the entry's function has another type" $
            elabRunModule (tableModule [Const SI32 2, CallIndirect (TypeIdx 0)]) [] `shouldSatisfy` trapContaining "IndirectCallTypeMismatch"
        it "need a table in the module" $
            void (elaborateModule (singleFunctionModule [] [] [I32] [] [Const SI32 0, CallIndirect (TypeIdx 0)]))
                `shouldBe` Left (NoTable "call_indirect")
        it "reject an element segment that does not fit" $
            void (load ((tableModule [Const SI32 0]) {elementSegments = [RawElementSegment [Const SI32 2] [FunctionIdx 0, FunctionIdx 0]]}))
                `shouldBe` Left (Uninstantiable (ElementSegmentOutOfBounds 0))
        it "reject an element segment in a module without a table at validation" $
            void (elaborateModule ((singleFunctionModule [] [] [] [] []) {elementSegments = [RawElementSegment [Const SI32 0] [FunctionIdx 0]]}))
                `shouldBe` Left (NoTable "elem")

    describe "WASI imports" $ do
        it "resolve to typed host functions; proc_exit ends the run with its code" $ do
            completion <- runWithWasi noHost (either (error . show) id (load (wasiModule procExitImport [Const SI32 3, Call (FunctionIdx 0)] []))) "f" []
            fmap describeCompletion completion `shouldBe` Right "exited 3"
        it "fd_write on an unknown descriptor reports errno 8 (badf) and the module continues" $ do
            completion <- runWithWasi noHost (either (error . show) id (load (wasiModule fdWriteImport [Const SI32 7, Const SI32 0, Const SI32 0, Const SI32 8, Call (FunctionIdx 0)] [I32]))) "f" []
            fmap describeCompletion completion `shouldBe` Right "returned [I32Value 8]"
        it "suspend the pure invocation, which a pure driver can answer itself" $
            case load (wasiModule fdWriteImport [Const SI32 1, Const SI32 0, Const SI32 0, Const SI32 8, Call (FunctionIdx 0)] [I32]) of
                Left err -> expectationFailure (show err)
                Right sm -> case invokeExport sm "f" [] of
                    Right (CalledHost (SomeHostRequest shapeS funcs exports rsS (HostRequest FdWrite _ store suspended))) ->
                        case continueWith shapeS funcs exports rsS (resumeWith store (99 :# VNil) suspended) of
                            Right (Returned _ results) -> results `shouldBe` [I32Value 99]
                            _ -> expectationFailure "expected the module to return the fake errno"
                    _ -> expectationFailure "expected a suspended fd_write call"
        it "args_sizes_get reports the argument count and buffer size" $ do
            let cfg = WasiConfig ["prog", "xy"] [] []
                body = [Const SI32 0, Const SI32 4, Call (FunctionIdx 0), Drop, Const SI32 0, Load SI32 (MemArg 0 0), Const SI32 4, Load SI32 (MemArg 0 0), Add SI32]
            completion <- runWithWasi cfg (either (error . show) id (load (wasiModule (wasiImport "args_sizes_get" (FuncType [I32, I32] [I32])) body [I32]))) "f" []
            fmap describeCompletion completion `shouldBe` Right "returned [I32Value 10]"
        it "must be declared at the host function's type" $
            void (load (wasiModule (RawImport "wasi_snapshot_preview1" "proc_exit" (ImportFunc (FuncType [I64] []))) [] []))
                `shouldBe` Left (Uninstantiable (ImportTypeMismatch "proc_exit"))
        it "must be provided by this host" $
            void (load (wasiModule (RawImport "spectest" "print" (ImportFunc (FuncType [] []))) [] []))
                `shouldBe` Left (Uninstantiable (UnsupportedImport "spectest" "print"))
        it "need a memory in the module" $
            void (load ((wasiModule procExitImport [] []) {memories = []}))
                `shouldBe` Left (Uninstantiable WasiNeedsMemory)
        it "are valid whether or not this host provides them: linking is instantiation's job" $
            void (elaborateModule (wasiModule (RawImport "spectest" "print" (ImportFunc (FuncType [] []))) [] []))
                `shouldBe` Right ()

    describe "module-level validation" $ do
        it "rejects a memory whose minimum exceeds its maximum" $
            void (elaborateModule (singleFunctionModule [memoryWithMax 2 1] [] [] [] []))
                `shouldBe` Left (InvalidMemoryLimits (Limits 2 (Just 1)))
        it "rejects a memory beyond 65536 pages" $
            void (elaborateModule (singleFunctionModule [memoryWithMax 1 70000] [] [] [] []))
                `shouldBe` Left (InvalidMemoryLimits (Limits 1 (Just 70000)))
        it "rejects two memories" $
            void (elaborateModule (singleFunctionModule [onePageMemory, onePageMemory] [] [] [] []))
                `shouldBe` Left TooManyMemories
        it "exposes an exported global's current value (the spec's get action)" $
            readExportedGlobal ((startModule [Const SI32 5, GlobalSet (GlobalIdx 0)]) {exports = [Export "g" (ExportGlobal (GlobalIdx 0))]}) "g"
                `shouldBe` Right "5"
        it "reading a function export as a global is NoSuchExport" $
            readExportedGlobal (startModule []) "f" `shouldBe` Left (show (NoSuchExport "f"))
        it "rejects duplicate export names" $
            void (elaborateModule ((singleFunctionModule [] [] [] [] []) {exports = [Export "f" (ExportFunc (FunctionIdx 0)), Export "f" (ExportFunc (FunctionIdx 0))]}))
                `shouldBe` Left (DuplicateExport "f")
        it "rejects an export of a function that does not exist" $
            void (elaborateModule ((singleFunctionModule [] [] [] [] []) {exports = [Export "g" (ExportFunc (FunctionIdx 7))]}))
                `shouldSatisfy` isLeft
        it "runs the start function at instantiation (it bumps a global the export reads)" $
            elabRunModule (startModule [Const SI32 1, GlobalSet (GlobalIdx 0)]) [] `shouldBe` Right ["1"]
        it "rejects a start function with parameters" $
            void (elaborateModule (twoFunctions (FuncType [I32] []) [] (FuncType [] [I32]) [Const SI32 0]) {start = Just (FunctionIdx 0)})
                `shouldBe` Left InvalidStartFunction
        it "fails instantiation when the start function traps" $
            void (load (startModule [Unreachable]))
                `shouldBe` Left (Uninstantiable (StartFunctionTrapped UnreachableExecuted))
        it "validates a start function that would trap: only instantiation runs it" $
            void (elaborateModule (startModule [Unreachable])) `shouldBe` Right ()

    describe "data segments" $ do
        it "are copied into memory at instantiation" $
            elabRunModule (withData [RawDataSegment (Active [Const SI32 8]) "hi"] (singleFunctionModule [onePageMemory] [] [I32] [] [Const SI32 9, LoadN SI32 1 Unsigned (MemArg 0 0)])) []
                `shouldBe` Right ["105"]
        it "must fit in the memory" $
            void (load (withData [RawDataSegment (Active [Const SI32 65535]) "hi"] (singleFunctionModule [onePageMemory] [] [I32] [] [Const SI32 0])))
                `shouldBe` Left (Uninstantiable (DataSegmentOutOfBounds 0))
        it "need a memory to land in, which validation checks" $
            void (elaborateModule (withData [RawDataSegment (Active [Const SI32 0]) "hi"] (singleFunctionModule [] [] [I32] [] [Const SI32 0])))
                `shouldBe` Left (NoMemory "data")
        it "need a constant offset, which validation checks" $
            void (elaborateModule (withData [RawDataSegment (Active [Const SI32 0, Const SI32 0]) "hi"] (singleFunctionModule [onePageMemory] [] [I32] [] [Const SI32 0])))
                `shouldBe` Left (InvalidDataSegmentOffset 0)

    describe "bulk memory" $ do
        it "memory.fill then memory.copy" $
            elabRunWithMemory [] [I32] [] [Const SI32 0, Const SI32 7, Const SI32 4, MemoryFill, Const SI32 100, Const SI32 0, Const SI32 4, MemoryCopy, Const SI32 103, LoadN SI32 1 Unsigned (MemArg 0 0)] []
                `shouldBe` Right ["7"]
        it "memory.copy traps when a range is out of bounds, writing nothing" $
            elabRunWithMemory [] [I32] [] [Const SI32 65530, Const SI32 0, Const SI32 10, MemoryCopy, Const SI32 0] []
                `shouldSatisfy` trapContaining "OutOfBoundsMemoryAccess"
        it "memory.fill with a huge count traps without allocating" $
            elabRunWithMemory [] [I32] [] [Const SI32 1, Const SI32 0xAA, Const SI32 0xFFFFFFFF, MemoryFill, Const SI32 0] []
                `shouldSatisfy` trapContaining "OutOfBoundsMemoryAccess"
        it "memory.init copies from a passive segment" $
            elabRunModule (withData [RawDataSegment Passive "xyz"] (singleFunctionModule [onePageMemory] [] [I32] [] [Const SI32 10, Const SI32 1, Const SI32 2, MemoryInit (DataIdx 0), Const SI32 10, LoadN SI32 1 Unsigned (MemArg 0 0)])) []
                `shouldBe` Right ["121"]
        it "memory.init traps after data.drop (except for zero bytes)" $
            elabRunModule (withData [RawDataSegment Passive "xyz"] (singleFunctionModule [onePageMemory] [] [I32] [] [DataDrop (DataIdx 0), Const SI32 0, Const SI32 0, Const SI32 0, MemoryInit (DataIdx 0), Const SI32 10, Const SI32 0, Const SI32 1, MemoryInit (DataIdx 0), Const SI32 0])) []
                `shouldSatisfy` trapContaining "OutOfBoundsMemoryAccess"
        it "memory.init must name an existing segment" $
            void (elaborateModule (singleFunctionModule [onePageMemory] [] [] [] [Const SI32 0, Const SI32 0, Const SI32 0, MemoryInit (DataIdx 3)]))
                `shouldBe` Left (IndexOutOfRange DataSegments 3)

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
        it "must end with the block's result type (an extra value is an error)" $
            elabError [] [] [] [Unreachable, Const SI32 0] `shouldSatisfy` isLeft
        it "may not select between two known but different types" $
            elabError [] [I32] [] [Unreachable, Const SI64 0, Const SI32 0, Select] `shouldSatisfy` isLeft
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
        it "rejects an over-long integer encoding (a 6-byte u32)" $
            decodeSections [section 1 [0x80, 0x80, 0x80, 0x80, 0x80, 0x00]]
                `shouldSatisfy` decodeErrorContaining "too long"
        it "rejects an integer with its unused high bits set" $
            decodeSections [section 1 [0xFF, 0xFF, 0xFF, 0xFF, 0x7F]]
                `shouldSatisfy` decodeErrorContaining "too large"
        it "rejects an unknown section id" $
            decodeSections [section 13 []] `shouldSatisfy` decodeErrorContaining "malformed section id"
        it "rejects sections out of order" $
            decodeSections [funcSection [0], typeSection] `shouldSatisfy` decodeErrorContaining "out of order"
        it "rejects a custom section without a name" $
            decodeSections [section 0 []] `shouldSatisfy` isLeft
        it "rejects a code entry whose declared size disagrees with its content" $
            decodeSections [typeSection, funcSection [0], section 10 (vec [[0x03, 0x00, 0x0B]])]
                `shouldSatisfy` isLeft
        it "rejects a data count that disagrees with the data section" $
            decodeSections [typeSection, funcSection [0], section 12 [0x01], codeSection [[0x0B]]]
                `shouldSatisfy` decodeErrorContaining "inconsistent"
        it "rejects an unknown opcode" $
            decodeSections [typeSection, funcSection [0], codeSection [[0xFF, 0x0B]]]
                `shouldSatisfy` decodeErrorContaining "unsupported opcode"

    describe "calls between functions" $ do
        it "pass arguments in order (a - b through a call)" $
            elabRunModule (twoFunctions (FuncType [I32, I32] [I32]) [LocalGet (LocalIdx 0), LocalGet (LocalIdx 1), Sub SI32] (FuncType [I32, I32] [I32]) [LocalGet (LocalIdx 0), LocalGet (LocalIdx 1), Call (FunctionIdx 0)]) [10, 3]
                `shouldBe` Right ["7"]
        it "accept parameters of different types" $
            elabRunModule (twoFunctions (FuncType [I32, I64] [I64]) [LocalGet (LocalIdx 1)] (FuncType [I32, I64] [I64]) [LocalGet (LocalIdx 0), LocalGet (LocalIdx 1), Call (FunctionIdx 0)]) [5, 9]
                `shouldBe` Right ["9"]
        it "return several results in order (1 - 2 after a two-result call)" $
            elabRunModule (twoFunctions (FuncType [] [I32, I32]) [Const SI32 1, Const SI32 2] (FuncType [] [I32]) [Call (FunctionIdx 0), Sub SI32]) []
                `shouldBe` Right ["4294967295"]
        it "render several results in declared order" $
            elabRun [] [I32, I64] [] [Const SI32 1, Const SI64 2] [] `shouldBe` Right ["1", "2"]

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

    describe "generated well-typed programs (i32 arithmetic with if/else over two parameters)" $ do
        it "elaborate, run, and agree with a reference evaluator" $ hedgehog $ do
            program <- forAll (genProgram 4)
            a <- forAll (Gen.word32 Range.linearBounded)
            b <- forAll (Gen.word32 Range.linearBounded)
            elabRun [I32, I32] [I32] [] (compileProgram program) [toInteger a, toInteger b]
                === Right [show (evalProgram a b program)]

    describe "conversion corner cases" $ do
        it "f32.demote_f64 keeps NaN a NaN" $
            fmap isNaN (convertVal F32DemoteF64 (0 / 0 :: Double)) `shouldBe` Right True
        it "f32.demote_f64 keeps infinity infinite" $
            fmap isInfinite (convertVal F32DemoteF64 (1 / 0 :: Double)) `shouldBe` Right True
        it "i32.trunc_f32_u traps on NaN" $
            convertVal (I32TruncF32 Unsigned) (0 / 0 :: Float) `shouldBe` Left InvalidConversionToInteger
        it "i32.trunc_f32_u traps on infinity with an integer overflow" $
            convertVal (I32TruncF32 Unsigned) (1 / 0 :: Float) `shouldBe` Left IntegerOverflow
        it "i32.trunc_f32_u traps on 2^32" $
            convertVal (I32TruncF32 Unsigned) (4294967296 :: Float) `shouldBe` Left IntegerOverflow
        it "i32.trunc_sat_f32_u saturates: NaN to 0, negative to 0, huge to the maximum" $
            map (convertVal (I32TruncSatF32 Unsigned)) [0 / 0, -1, 1e10 :: Float] `shouldBe` [Right 0, Right 0, Right 4294967295]
        it "i32.trunc_sat_f64_s saturates at the signed bounds" $
            map (convertVal (I32TruncSatF64 Signed)) [-1e10, 1e10 :: Double] `shouldBe` [Right 2147483648, Right 2147483647]
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
    case load (singleFunctionModule memories params results locals body) of
        Left err -> Left (show err)
        Right sm -> invokeWithIntegers sm args

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
    moduleOf memories [RawFunction (FuncType params results) locals body] (FunctionIdx 0)

-- | Two functions, the second (function 1) exported as @f@ and free to call function 0.
twoFunctions :: FuncType -> [RawInstr] -> FuncType -> [RawInstr] -> RawModule
twoFunctions calleeType callee mainType mainBody =
    moduleOf [] [RawFunction calleeType [] callee, RawFunction mainType [] mainBody] (FunctionIdx 1)

-- | A module of the given functions (no globals), exporting one of them as @f@.
moduleOf :: [RawMemory] -> [RawFunction] -> FunctionIdx -> RawModule
moduleOf memories funcs exported =
    RawModule
        { types = [f.signature | f <- funcs]
        , imports = []
        , functions = funcs
        , globals = []
        , memories = memories
        , tables = []
        , elementSegments = []
        , dataSegments = []
        , exports = [Export "f" (ExportFunc exported)]
        , start = Nothing
        }

{- | Validate and instantiate a module and run its export @f@ on integer arguments.
| Load a module and read one of its exported globals, collapsing any error to text.
-}
readExportedGlobal :: RawModule -> Text -> Either String String
readExportedGlobal m name = case load m of
    Left err -> Left (show err)
    Right inst -> either (Left . show) (Right . renderValue) (readGlobalExport inst name)

elabRunModule :: RawModule -> [Integer] -> Either String [String]
elabRunModule m args = case load m of
    Left err -> Left (show err)
    Right sm -> invokeWithIntegers sm args

-- | Why a module could not be loaded: which stage rejected it, and why.
data LoadError = Invalid ElabError | Uninstantiable InstantiationError
    deriving stock (Eq, Show)

-- | Validate, then instantiate.
load :: RawModule -> Either LoadError SomeModuleInst
load m = do
    validated <- first Invalid (elaborateModule m)
    first Uninstantiable (instantiate validated)

-- | Invoke export @f@ on integer literals, typed by its parameters; render the results.
invokeWithIntegers :: SomeModuleInst -> [Integer] -> Either String [String]
invokeWithIntegers sm args = do
    FuncType params _ <- maybe (Left "no export f") Right (exportSignature sm "f")
    let values = zipWith integerValue params args
    case invokeExport sm "f" values of
        Left err -> Left (show err)
        Right (Returned _ results) -> Right (map renderValue results)
        Right (CalledHost _) -> Left "called into the host"
  where
    integerValue I32 n = I32Value (fromInteger n)
    integerValue I64 n = I64Value (fromInteger n)
    integerValue F32 n = F32Value (fromInteger n)
    integerValue F64 n = F64Value (fromInteger n)

onePageMemory :: RawMemory
onePageMemory = RawMemory (MemType AddrI32 (Limits 1 Nothing))

{- | A three-entry table: entry 0 is function 0 (@() -> i32@, returning 42), entry 1 is left
  uninitialised, entry 2 is function 1 (@i32 -> i32@). The export @f@ is function 2 with the given
  body, of type @() -> i32@; type index 0 is @() -> i32@.
-}
tableModule :: [RawInstr] -> RawModule
tableModule body =
    (moduleOf [] [RawFunction (FuncType [] [I32]) [] [Const SI32 42], RawFunction (FuncType [I32] [I32]) [] [LocalGet (LocalIdx 0)], RawFunction (FuncType [] [I32]) [] body] (FunctionIdx 2))
        { tables = [RawTable (Limits 3 Nothing)]
        , elementSegments = [RawElementSegment [Const SI32 0] [FunctionIdx 0], RawElementSegment [Const SI32 2] [FunctionIdx 1]]
        }

procExitImport, fdWriteImport :: RawImport
procExitImport = wasiImport "proc_exit" (FuncType [I32] [])
fdWriteImport = wasiImport "fd_write" (FuncType [I32, I32, I32, I32] [I32])

wasiImport :: Text -> FuncType -> RawImport
wasiImport name ft = RawImport "wasi_snapshot_preview1" name (ImportFunc ft)

{- | One import (function 0), one page of memory, and the export @f@ (function 1) with the
  given body and result type.
-}
wasiModule :: RawImport -> [RawInstr] -> [ValType] -> RawModule
wasiModule imported body results =
    (moduleOf [onePageMemory] [RawFunction (FuncType [] results) [] body] (FunctionIdx 1))
        { imports = [imported]
        , types = [importType imported, FuncType [] results]
        }
  where
    importType (RawImport _ _ (ImportFunc ft)) = ft

noHost :: WasiConfig
noHost = WasiConfig [] [] []

describeCompletion :: Completion -> String
describeCompletion (Ran _ results) = "returned " ++ show results
describeCompletion (Exited code) = "exited " ++ show code

{- | Function 0 is the start function with the given body; the export @f@ (function 1) reads
  the module's one mutable i32 global, initially 0.
-}
startModule :: [RawInstr] -> RawModule
startModule startBody =
    (twoFunctions (FuncType [] []) startBody (FuncType [] [I32]) [GlobalGet (GlobalIdx 0)])
        { globals = [RawGlobal (GlobalType Mutable I32) [Const SI32 0]]
        , start = Just (FunctionIdx 0)
        }

withData :: [RawDataSegment] -> RawModule -> RawModule
withData segments m = m {dataSegments = segments}

memoryWithMax :: Word32 -> Word32 -> RawMemory
memoryWithMax lo hi = RawMemory (MemType AddrI32 (Limits lo (Just hi)))

{- *** Hand-assembled binaries ***

   Just enough of the binary format to reach the decoder's error paths without @wat2wasm@:
   a header, and sections whose payloads are short enough for one-byte LEB128 sizes.
-}

-- | Decode raw bytes, reduced to the number of functions ('RawModule' has no 'Show').
decodeBytes :: [Word8] -> Either String Int
decodeBytes bytes = fmap (length . (.functions)) (decodeModule (BL.pack bytes))

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

{- *** Generated programs ***

   A small expression language over two i32 parameters, compiled to WebAssembly and evaluated
   by a reference in Haskell (with the same wrap-around arithmetic), so a property can check
   that whatever the generator builds elaborates and computes the same value.
-}

data Program
    = Literal Word32
    | Param Word32
    | Binary BinaryOp Program Program
    | IfElse Program Program Program
    deriving stock (Show)

data BinaryOp = OpAdd | OpSub | OpMul | OpAnd | OpOr | OpXor
    deriving stock (Show)

genProgram :: Int -> Gen Program
genProgram depth
    | depth <= 0 = leaf
    | otherwise =
        Gen.choice
            [ leaf
            , Binary <$> Gen.element [OpAdd, OpSub, OpMul, OpAnd, OpOr, OpXor] <*> sub <*> sub
            , IfElse <$> sub <*> sub <*> sub
            ]
  where
    leaf = Gen.choice [Literal <$> Gen.word32 Range.linearBounded, Param <$> Gen.element [0, 1]]
    sub = genProgram (depth - 1)

compileProgram :: Program -> [RawInstr]
compileProgram program = case program of
    Literal n -> [Const SI32 n]
    Param i -> [LocalGet (LocalIdx i)]
    Binary op x y -> compileProgram x ++ compileProgram y ++ [binaryInstr op]
    IfElse c t e -> compileProgram c ++ [If (FuncType [] [I32]) (compileProgram t) (compileProgram e)]
  where
    binaryInstr OpAdd = Add SI32
    binaryInstr OpSub = Sub SI32
    binaryInstr OpMul = Mul SI32
    binaryInstr OpAnd = And SI32
    binaryInstr OpOr = Or SI32
    binaryInstr OpXor = Xor SI32

evalProgram :: Word32 -> Word32 -> Program -> Word32
evalProgram a b program = case program of
    Literal n -> n
    Param 0 -> a
    Param _ -> b
    Binary op x y -> binary op (evalProgram a b x) (evalProgram a b y)
    IfElse c t e -> evalProgram a b (if evalProgram a b c /= 0 then t else e)
  where
    binary OpAdd = (+)
    binary OpSub = (-)
    binary OpMul = (*)
    binary OpAnd = (.&.)
    binary OpOr = (.|.)
    binary OpXor = xor

-- | An i32 written as a signed literal (the stack holds raw bits).
fromSigned32Test :: Int -> Word32
fromSigned32Test = fromIntegral

trapContaining :: String -> Either String [String] -> Bool
trapContaining needle = either (needle `isInfixOf`) (const False)
