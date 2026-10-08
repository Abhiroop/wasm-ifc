{-# LANGUAGE DataKinds #-}

{- | The @cabal test@ suite. It exercises the pipeline in Haskell, without needing
  @wat2wasm@: elaboration and running are driven from 'RawModule' values built by hand, so
  we can check acceptance, rejection, traps and algebraic laws directly. (The end-to-end
  check on real @.wasm@ files lives in @samples/check.sh@.)
-}
module Main (main) where

import Control.Monad (forM_, void)
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
import System.Environment (lookupEnv)
import Test.Hspec
import Test.Hspec.Hedgehog (annotate, classify, failure, forAll, hedgehog, label, modifyMaxSuccess, (===))

import Codec.Wasm (decodeModule)
import Data.Map.Strict qualified as Map
import Examples (labelledSumLength, leakLength, runFactorial, runIncrement, runSpinFor, runSquare, secretStoreLength)
import Noninterference (Observation (..), compileModule, genModule, holdsValueAcrossBranch, observe, observeUnder, withPublicLoads)
import Runtime.Bytes (bytesOfWord32, bytesOfWord64, word32OfBytes, word64OfBytes)
import Runtime.Convert (convertVal)
import Runtime.Host (WasiFunc (..))
import Runtime.Instantiate (InstantiationError (..), instantiate)
import Runtime.Interpreter (HostRequest (..), callDepthBound, resumeWith)
import Runtime.Module (Invocation (..), RunError (..), SomeHostRequest (..), SomeModuleInst, Value (..), continueWith, exportSignature, invokeExport, readGlobalExport, renderValue)
import Runtime.Numeric (intDiv32)
import Runtime.Stack (ValueStack (..), retagStack)
import Runtime.Trap (Trap (..))
import Runtime.Wasi (Completion (..), DescriptorLevels (..), Preopen (..), WasiConfig (..), publicDescriptors, runWithWasi)
import Syntax.Functions (RawFunction (..))
import Syntax.Globals (RawGlobal (..))
import Syntax.Immediates
import Syntax.Indices
import Syntax.Instructions
import Syntax.Module (DataMode (..), ElemMode (..), Export (..), ExportDesc (..), ImportDesc (..), RawDataSegment (..), RawElementSegment (..), RawImport (..), RawMemory (..), RawModule (..), RawTable (..))
import Syntax.Types
import Syntax.TypesIFC (LabelledFuncType (..), LabelledValType (..), SecLevel (..))
import Validation.Elaborate (ElabError (..), IndexSpace (..), Inferred (..), elaborateModule, elaborateModuleInferring, elaborateModuleWith)
import Validation.LocalWebs (mergeModuleWebs, splitModuleLocals)
import Validation.Policy (FunctionLevels (..), Policy (..), PolicyError (..), mergePolicies, parsePolicy)

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
        it "a public write under a secret condition needs a proof that does not exist" $ leakLength `shouldBe` 1
        it "a secret stored into memory declares its bytes secret, statically" $ secretStoreLength `shouldBe` 3

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

    describe "information flow through memory (SecWasm's run-time check)" $ do
        let secretStore = [Const SI32 0, Const SI32 7, Annotated High (Store SI32 (MemArg 0 0))]
            publicStore = [Const SI32 0, Const SI32 9, Store SI32 (MemArg 0 0)]
            loadPublic = [Const SI32 0, Load SI32 (MemArg 0 0)]
            loadSecret = [Const SI32 0, Annotated High (Load SI32 (MemArg 0 0))]
        it "a load expecting public bytes traps on a byte a secret store wrote" $
            elabRunWithMemory [] [I32] [] (secretStore ++ loadPublic) [] `shouldSatisfy` trapContaining "SecretRead (AccessAt 0 1)"
        it "a load declared secret yields a secret, which a public function cannot return" $
            elabRunWithMemory [] [I32] [] (secretStore ++ loadSecret) [] `shouldSatisfy` isLeft
        it "a secret that was loaded stays secret when stored again (the store's level is inferred)" $
            -- A secret can only be observed publicly through a declassification, so the
            -- evidence is the trap on the public read of the copy.
            elabRunWithMemory [] [I32] [] (secretStore ++ [Const SI32 8] ++ loadSecret ++ [Store SI32 (MemArg 0 0), Const SI32 8, Load SI32 (MemArg 0 0)]) []
                `shouldSatisfy` trapContaining "SecretRead (AccessAt 0 3)"
        it "a public store over secret bytes makes them public again" $
            elabRunWithMemory [] [I32] [] (secretStore ++ publicStore ++ loadPublic) [] `shouldBe` Right ["9"]
        it "a narrow load sees the level of every byte it covers" $
            elabRunWithMemory [] [I32] [] (secretStore ++ [Const SI32 2, LoadN SI32 1 Unsigned (MemArg 0 0)]) []
                `shouldSatisfy` trapContaining "SecretRead (AccessAt 0 1)"
        it "memory.copy carries the bytes' levels with them" $
            elabRunWithMemory [] [I32] [] (secretStore ++ [Const SI32 16, Const SI32 0, Const SI32 4, MemoryCopy, Const SI32 16, Load SI32 (MemArg 0 0)]) []
                `shouldSatisfy` trapContaining "SecretRead (AccessAt 0 1)"
        it "a store may declare a level the value flows into, not one it does not" $ do
            elabErrorWithMemory [] [] [] [Const SI32 0, Const SI32 1, Annotated High (Store SI32 (MemArg 0 0))] `shouldSatisfy` isRight
            elabErrorWithMemory [] [] [] (secretStore ++ loadSecret ++ [Const SI32 4, Store SI32 (MemArg 0 0)]) `shouldSatisfy` isRight
            elabErrorWithMemory [] [] [] (secretStore ++ [Const SI32 4] ++ loadSecret ++ [Annotated Low (Store SI32 (MemArg 0 0))])
                `shouldBe` Left (IllegalFlow "store" High Low)
        it "relabelling goes up freely and never down without declassification" $ do
            elabError [] [I32] [] [Const SI32 1, Relabel High, Relabel Low] `shouldBe` Left (IllegalFlow "relabel" High Low)
            elabError [] [I32] [] [Const SI32 1, Relabel High, Declassify Low] `shouldBe` Left DeclassifyNotAllowed
        it "an annotation belongs on a memory access only" $
            elabError [] [] [] [Annotated High Nop] `shouldBe` Left AnnotationMisplaced

    describe "security policies (Validation.Policy)" $ do
        let policy text = either (error . show) id (parsePolicy text)
            withMemory = singleFunctionModule [onePageMemory]
        it "parses every kind of statement" $ do
            let parsed = policy "func 3 : H L -> H\nexport check : H -> L ; a comment\nimport env.read : L L -> H\nglobal 0 : H\nexport global key : H\nload 3 5 : H\nstore 3 2 : L\nregion 0x1000 0x1400 : H\nload-default : H\nload-default func 3 : L\nload-default export check : H\nallow-declassify\n"
            Map.lookup 3 parsed.functionsByIndex `shouldBe` Just (FunctionLevels [High, Low] [High] Low)
            Map.lookup ("env", "read") parsed.importedFunctions `shouldBe` Just (FunctionLevels [Low, Low] [High] Low)
            Map.lookup (3, 5) parsed.loads `shouldBe` Just High
            parsed.regions `shouldBe` [(0x1000, 0x1400, High)]
            parsed.loadDefault `shouldBe` Just High
            parsed.declassifyAllowed `shouldBe` True
        it "rejects a line that is not a statement, and reads the arrow's level" $ do
            parsePolicy "global zero : H" `shouldSatisfy` isLeft
            fmap (Map.lookup "f" . (.exportedFunctions)) (parsePolicy "export f : H -{H}-> H") `shouldBe` Right (Just (FunctionLevels [High] [High] High))
        it "a function's results must be at least its bound" $
            elabRunWithPolicy "export f : -{H}-> L" (singleFunctionModule [] [] [I32] [] [Const SI32 1]) [] `shouldSatisfy` errorContaining "PolicyResultsBelowBound"
        it "a call inside a secret branch needs a callee bound at secret" $ do
            let caller = [LocalGet (LocalIdx 0), If (FuncType [] []) [Call (FunctionIdx 0)] [], Const SI32 0]
                program = twoFunctions (FuncType [] []) [Nop] (FuncType [I32] [I32]) caller
            elabRunWithPolicy "func 0 : -{H}->\nexport f : H -> L" program [1] `shouldBe` Right ["0"]
            elabRunWithPolicy "func 0 : ->\nexport f : H -> L" program [1] `shouldSatisfy` errorContaining "IllegalFlow \"call\" High Low"
        it "a function bound at secret writes only to secret places" $
            elabRunWithPolicy "func 0 : -{H}->\nexport f : -> L" (twoFunctions (FuncType [] []) [Const SI32 0, Const SI32 1, Store SI32 (MemArg 0 0)] (FuncType [] [I32]) [Call (FunctionIdx 0), Const SI32 0, Load SI32 (MemArg 0 0)]) {memories = [onePageMemory]} []
                `shouldSatisfy` trapContaining "SecretRead (AccessAt 1 0)"
        it "two sources may speak about the same item only if they agree" $ do
            mergePolicies (policy "global 0 : H") (policy "global 0 : L") `shouldBe` Left (PolicyConflict "global 0")
            fmap (.globalsByIndex) (mergePolicies (policy "global 0 : H") (policy "global 0 : H\nload-default : H")) `shouldBe` Right (Map.fromList [(0, High)])
        it "regions that overlap must agree" $ do
            elabRunWithPolicy "region 0 8 : H\nregion 4 12 : L" (withMemory [] [] [] []) [] `shouldSatisfy` errorContaining "PolicyConflict \"region\""
            elabRunWithPolicy "region 0 8 : H\nregion 4 12 : H" (withMemory [] [] [] []) [] `shouldBe` Right []
        it "an import from the host keeps a public bound and public parameters" $ do
            elabRunWithPolicy "import wasi_snapshot_preview1.fd_write : H L L L -> L" (wasiModule fdWriteImport [Const SI32 0] [I32]) []
                `shouldSatisfy` errorContaining "PolicyImportNotPublic \"wasi_snapshot_preview1.fd_write\""
            elabRunWithPolicy "import wasi_snapshot_preview1.fd_write : L L L L -{H}-> H" (wasiModule fdWriteImport [Const SI32 0] [I32]) []
                `shouldSatisfy` errorContaining "PolicyImportNotPublic"
        it "an import's results may be declared secret; the host stays public" $ do
            elabRunWithPolicy "import wasi_snapshot_preview1.fd_write : L L L L -> H" (wasiModule fdWriteImport [Const SI32 1, Const SI32 0, Const SI32 0, Const SI32 8, Call (FunctionIdx 0)] [I32]) []
                `shouldSatisfy` errorContaining "IllegalFlow \"result\""
            elabRunWithPolicy "import wasi_snapshot_preview1.fd_write : L L L L -> H" (wasiModule fdWriteImport [Const SI32 1, Const SI32 0, Const SI32 0, Const SI32 8, Call (FunctionIdx 0), Drop, Const SI32 0] [I32]) []
                `shouldSatisfy` errorContaining "called into the host"
        it "a declaration must name something the module has" $
            elabRunWithPolicy "export g : -> " (singleFunctionModule [] [] [] [] []) [] `shouldSatisfy` errorContaining "PolicyUnknown \"export g\""
        it "a secret parameter cannot be returned by a public function" $
            elabRunWithPolicy "export f : H -> L" (singleFunctionModule [] [I32] [I32] [] [LocalGet (LocalIdx 0)]) [1]
                `shouldSatisfy` errorContaining "IllegalFlow \"result\" High Low"
        it "a local written under a secret decision is secret, so a public function cannot return it" $
            elabRunWithPolicy "export f : H -> L" (singleFunctionModule [] [I32] [I32] [I32] [LocalGet (LocalIdx 0), If (FuncType [] []) [Const SI32 1, LocalSet (LocalIdx 1)] [], LocalGet (LocalIdx 1)]) [1]
                `shouldSatisfy` errorContaining "IllegalFlow \"result\" High Low"
        it "a secret parameter may be dropped" $
            elabRunWithPolicy "export f : H -> L" (singleFunctionModule [] [I32] [I32] [] [LocalGet (LocalIdx 0), Drop, Const SI32 1]) [1] `shouldBe` Right ["1"]
        it "a function's store default declares its stores secret" $
            elabRunWithPolicy "store-default func 0 : H" (withMemory [] [I32] [] [Const SI32 0, Const SI32 7, Store SI32 (MemArg 0 0), Const SI32 0, Load SI32 (MemArg 0 0)]) []
                `shouldSatisfy` trapContaining "SecretRead (AccessAt 0 1)"
        it "a store declared secret by position makes a later public read trap" $
            elabRunWithPolicy "store 0 0 : H" (withMemory [] [I32] [] [Const SI32 0, Const SI32 7, Store SI32 (MemArg 0 0), Const SI32 0, Load SI32 (MemArg 0 0)]) []
                `shouldSatisfy` trapContaining "SecretRead (AccessAt 0 1)"
        it "a region's bytes are secret from instantiation on, whatever a data segment wrote there" $ do
            let withSegment = withData [RawDataSegment (Active [Const SI32 0]) "\7\0\0\0"]
            elabRunWithPolicy "region 0 4 : H" (withSegment (withMemory [I32] [I32] [] [LocalGet (LocalIdx 0), Load SI32 (MemArg 0 0)])) [0]
                `shouldSatisfy` trapContaining "SecretRead (AccessAt 0 0)"
            elabRunWithPolicy "region 0 4 : H" (withSegment (withMemory [I32] [I32] [] [LocalGet (LocalIdx 0), Load SI32 (MemArg 0 0)])) [4] `shouldBe` Right ["0"]
        it "a load at a constant address in a region is declared at the region's level" $ do
            let withSegment = withData [RawDataSegment (Active [Const SI32 0]) "\7\0\0\0"]
                constantLoad = withSegment (withMemory [] [I32] [] [Const SI32 2, Load SI32 (MemArg 0 0)])
            elabRunWithPolicy "region 0 4 : H" constantLoad [] `shouldSatisfy` errorContaining "IllegalFlow \"result\""
            elabRunWithPolicy "region 0 4 : H\nexport f : -> H" constantLoad [] `shouldBe` Right ["0"]
        it "a region must lie in the memory as instantiated" $
            elabRunWithPolicy "region 65530 65540 : H" (withMemory [] [] [] []) [] `shouldSatisfy` errorContaining "RegionOutOfBounds"
        it "a public store over a region's bytes makes them public" $
            elabRunWithPolicy "region 0 4 : H" (withMemory [I32] [I32] [] [Const SI32 0, Const SI32 7, Store SI32 (MemArg 0 0), LocalGet (LocalIdx 0), Load SI32 (MemArg 0 0)]) [0]
                `shouldBe` Right ["7"]
        it "a public result is relabelled where a secret one is declared" $
            elabRunWithPolicy "export f : -> H" (singleFunctionModule [] [] [I32] [] [Const SI32 1]) [] `shouldBe` Right ["1"]
        it "a block may produce a secret result, and arms at different levels meet at the higher" $ do
            elabRunWithPolicy "export f : H -> H" (singleFunctionModule [] [I32] [I32] [] [LocalGet (LocalIdx 0), If (FuncType [] [I32]) [Const SI32 1] [Const SI32 0]]) [1] `shouldBe` Right ["1"]
            elabRunWithPolicy "export f : H -> H" (singleFunctionModule [] [I32] [I32] [] [Const SI32 1, If (FuncType [] [I32]) [LocalGet (LocalIdx 0)] [Const SI32 0]]) [7] `shouldBe` Right ["7"]
        it "a public argument may be passed where a secret parameter is declared" $
            elabRunWithPolicy "func 0 : H -> H\nexport f : -> H" (twoFunctions (FuncType [I32] [I32]) [LocalGet (LocalIdx 0)] (FuncType [] [I32]) [Const SI32 5, Call (FunctionIdx 0)]) [] `shouldBe` Right ["5"]
        it "a loop whose back edge carries a secret raises its parameter" $
            elabRunWithPolicy "export f : H -> H" (singleFunctionModule [] [I32] [I32] [] [Const SI32 0, Loop (FuncType [I32] [I32]) [Drop, LocalGet (LocalIdx 0), Const SI32 0, BrIf (LabelIdx 0)]]) [3] `shouldBe` Right ["3"]
        it "the load default makes every unannotated load secret" $
            elabRunWithPolicy "load-default : H" (withMemory [] [I32] [] [Const SI32 0, Load SI32 (MemArg 0 0)]) [] `shouldSatisfy` errorContaining "IllegalFlow \"result\""
        it "a module without functions assembles (the index space is empty, not wrapped around)" $
            void (elaborateModule (singleFunctionModule [] [] [] [] []) {functions = [], exports = []}) `shouldSatisfy` isRight
        it "declares the levels of the standard streams and preopens for the host" $ do
            let parsed = policy "stdout : H\npreopen /data : H"
            Map.lookup "stdout" parsed.streamLevels `shouldBe` Just High
            Map.lookup "/data" parsed.preopenLevels `shouldBe` Just High
        it "the module's own ifc section carries a policy" $ do
            let declassifying = (singleFunctionModule [] [] [I32] [] [Const SI32 1, Relabel High, Declassify Low]) {customSections = [("ifc", "allow-declassify")]}
            elabRunModule declassifying [] `shouldBe` Right ["1"]
            elabRunModule (declassifying {customSections = []}) [] `shouldSatisfy` errorContaining "DeclassifyNotAllowed"

    describe "inference of the labels of locals and internal functions" $ do
        let inferred text m = either (Left . show) Right (parsePolicy text) >>= \policy -> either (Left . show) (Right . snd) (elaborateModuleInferring policy m)
            secretThroughLocal = singleFunctionModule [] [I32] [I32] [I32] [LocalGet (LocalIdx 0), LocalSet (LocalIdx 1), LocalGet (LocalIdx 1)]
            helper = twoFunctions (FuncType [I32] [I32]) [LocalGet (LocalIdx 0)] (FuncType [I32] [I32]) [LocalGet (LocalIdx 0), Call (FunctionIdx 0)]
        it "a local that holds a secret is secret" $ do
            elabRunWithPolicy "export f : H -> H" secretThroughLocal [5] `shouldBe` Right ["5"]
            fmap (.raisedLocals) (inferred "export f : H -> H" secretThroughLocal) `shouldBe` Right [(0, 0)]
        it "a local that never holds a secret stays public" $
            fmap (.raisedLocals) (inferred "export f : L -> L" secretThroughLocal) `shouldBe` Right []
        it "an internal function that receives a secret takes it, and returns a secret" $ do
            elabRunWithPolicy "export f : H -> H" helper [5] `shouldBe` Right ["5"]
            fmap (.raisedFunctions) (inferred "export f : H -> H" helper) `shouldBe` Right [(0, LabelledFuncType Low [I32 :~ High] [I32 :~ High])]
        it "an internal function called under a secret pc is bound at secret" $ do
            let caller = [LocalGet (LocalIdx 0), If (FuncType [] []) [Call (FunctionIdx 0)] [], Const SI32 0]
                program = twoFunctions (FuncType [] []) [Nop] (FuncType [I32] [I32]) caller
            fmap (.raisedFunctions) (inferred "export f : H -> L" program) `shouldBe` Right [(0, LabelledFuncType High [] [])]
        it "a local reused for a secret and then for a public value is split, so the public use stays public" $ do
            let reused = singleFunctionModule [] [I32, I32] [I32] [I32] [LocalGet (LocalIdx 0), LocalSet (LocalIdx 2), LocalGet (LocalIdx 2), Drop, LocalGet (LocalIdx 1), LocalSet (LocalIdx 2), LocalGet (LocalIdx 2)]
            elabRunWithPolicy "export f : H L -> L" reused [7, 9] `shouldBe` Right ["9"]
            fmap (.raisedLocals) (inferred "export f : H L -> L" reused) `shouldBe` Right [(0, 0)]
        it "the webs of a local meet where its definitions reach a common use" $ do
            let joined = singleFunctionModule [] [I32, I32] [I32] [I32] [LocalGet (LocalIdx 1), LocalSet (LocalIdx 2), LocalGet (LocalIdx 0), If (FuncType [] []) [LocalGet (LocalIdx 0), LocalSet (LocalIdx 2)] [], LocalGet (LocalIdx 2)]
            elabRunWithPolicy "export f : H L -> L" joined [7, 9] `shouldSatisfy` errorContaining "IllegalFlow \"result\" High Low"
            elabRunWithPolicy "export f : H L -> H" joined [0, 9] `shouldBe` Right ["9"]
        it "the interface is not inferred: an export, a declared function, a table entry stay as declared" $ do
            elabRunWithPolicy "export f : H -> L" secretThroughLocal [5] `shouldSatisfy` errorContaining "IllegalFlow \"result\" High Low"
            elabRunWithPolicy "func 0 : L -> L\nexport f : H -> H" helper [5] `shouldSatisfy` errorContaining "IllegalFlow \"call\" High Low"
            elabRunWithPolicy "export f : H -> H" (helper {tables = [RawTable FuncRef (Limits 1 Nothing)], elementSegments = [activeElements [Const SI32 0] [FunctionIdx 0]]}) [5]
                `shouldSatisfy` errorContaining "IllegalFlow \"call\" High Low"

    describe "br_table raises the pc down to its deepest target" $ do
        let noResult = FuncType [] []
            -- a function with a secret parameter and a public global, returning that global
            withSecret body = (singleFunctionModule [] [I32] [I32] [] (body ++ [GlobalGet (GlobalIdx 0)])) {globals = [RawGlobal (GlobalType Mutable I32) [Const SI32 0]]}
            publicWrite = [Const SI32 1, GlobalSet (GlobalIdx 0)]
        it "a public write after the blocks the table may leave is accepted" $
            elabRunWithPolicy "export f : H -> L" (withSecret (Block noResult [LocalGet (LocalIdx 0), BrTable [LabelIdx 0] (LabelIdx 0)] : publicWrite)) [3]
                `shouldBe` Right ["1"]
        it "a public write inside a block the table may leave is rejected" $
            elabRunWithPolicy "export f : H -> L" (withSecret [Block noResult (Block noResult [LocalGet (LocalIdx 0), BrTable [LabelIdx 0] (LabelIdx 1)] : publicWrite)]) [3]
                `shouldSatisfy` errorContaining "IllegalFlow \"global.set\" High Low"
        it "SecWasm's printed rule leaks here, since the default target is deeper than the table is long" $
            elabRunWithPolicy
                "export f : H -> L"
                (withSecret [Block noResult (Block noResult [Block noResult [Block noResult [LocalGet (LocalIdx 0), BrTable [LabelIdx 0] (LabelIdx 3)]]] : publicWrite)])
                [3]
                `shouldSatisfy` errorContaining "IllegalFlow \"global.set\" High Low"

    describe "preserved globals (a public global that code under a secret pc may change and must restore)" $ do
        let stackPointer m = m {globals = [RawGlobal (GlobalType Mutable I32) [Const SI32 1000]]}
            lower = [GlobalGet (GlobalIdx 0), Const SI32 16, Sub SI32, GlobalSet (GlobalIdx 0)]
            raise = [GlobalGet (GlobalIdx 0), Const SI32 16, Add SI32, GlobalSet (GlobalIdx 0)]
            noResult = FuncType [] []
            preserving = ("preserved global 0\n" <>)
            -- f(secret): if (secret) helper(); return the global, where helper lowers and raises it
            helperInBranch = stackPointer (twoFunctions noResult (lower ++ raise) (FuncType [I32] [I32]) [LocalGet (LocalIdx 0), If noResult [Call (FunctionIdx 0)] [], GlobalGet (GlobalIdx 0)])
            -- f(secret): if (secret) lower the global; return it
            notRestored = stackPointer (singleFunctionModule [] [I32] [I32] [] [LocalGet (LocalIdx 0), If noResult lower [], GlobalGet (GlobalIdx 0)])
            -- g(secret) lowers the global, returns early if secret (after `beforeReturn`), and raises it at its end
            earlyReturn beforeReturn =
                stackPointer
                    ( twoFunctions
                        (FuncType [I32] [I32])
                        (lower ++ [LocalGet (LocalIdx 0), If noResult (beforeReturn ++ [Const SI32 1, Return]) []] ++ raise ++ [Const SI32 0])
                        (FuncType [I32] [I32])
                        [LocalGet (LocalIdx 0), Call (FunctionIdx 0), Drop, GlobalGet (GlobalIdx 0)]
                    )
            -- the invoked function itself returns early under a secret pc without raising the global
            entryNotRestored = stackPointer (singleFunctionModule [] [I32] [] [] (lower ++ [LocalGet (LocalIdx 0), If noResult [Return] []] ++ raise))
        it "a function that lowers and raises the global may be called under a secret pc" $ do
            elabRunWithPolicy (preserving "export f : H -> L") helperInBranch [1] `shouldBe` Right ["1000"]
            elabRunWithPolicy (preserving "export f : H -> L") helperInBranch [0] `shouldBe` Right ["1000"]
            elabRunWithPolicy "export f : H -> L" helperInBranch [1] `shouldSatisfy` errorContaining "IllegalFlow \"global.set\" High Low"
        it "a conditional on a secret that leaves the global changed traps where it ends" $ do
            elabRunWithPolicy (preserving "export f : H -> L") notRestored [1] `shouldSatisfy` trapContaining "GlobalNotRestored"
            elabRunWithPolicy (preserving "export f : H -> L") notRestored [0] `shouldBe` Right ["1000"]
        it "a function that returns early under a secret pc is compared with the value at its call" $ do
            elabRunWithPolicy (preserving "export f : H -> L") (earlyReturn raise) [1] `shouldBe` Right ["1000"]
            elabRunWithPolicy (preserving "export f : H -> L") (earlyReturn raise) [0] `shouldBe` Right ["1000"]
            elabRunWithPolicy (preserving "export f : H -> L") (earlyReturn []) [1] `shouldSatisfy` trapContaining "GlobalNotRestored"
            elabRunWithPolicy (preserving "export f : H -> L") (earlyReturn []) [0] `shouldBe` Right ["1000"]
        it "the invoked function is held to the same" $ do
            elabRunWithPolicy (preserving "export f : H ->") entryNotRestored [1] `shouldSatisfy` trapContaining "GlobalNotRestored"
            elabRunWithPolicy (preserving "export f : H ->") entryNotRestored [0] `shouldBe` Right []
        it "under a public pc the ordinary rule holds: a secret value may not be written" $
            elabRunWithPolicy (preserving "export f : H -> L") (stackPointer (singleFunctionModule [] [I32] [I32] [] [LocalGet (LocalIdx 0), GlobalSet (GlobalIdx 0), Const SI32 0])) [1]
                `shouldSatisfy` errorContaining "IllegalFlow \"global.set\" High Low"
        it "a preserved global is a mutable public global the module has" $ do
            let immutable = (singleFunctionModule [] [] [] [] []) {globals = [RawGlobal (GlobalType Immutable I32) [Const SI32 0]]}
            elabRunWithPolicy "preserved global 0" immutable [] `shouldSatisfy` errorContaining "PolicyPreservedNotMutable 0"
            elabRunWithPolicy "preserved global 0\nglobal 0 : H" (stackPointer (singleFunctionModule [] [] [] [] [])) [] `shouldSatisfy` errorContaining "PolicyConflict \"preserved global 0\""
            elabRunWithPolicy "preserved global 3" (stackPointer (singleFunctionModule [] [] [] [] [])) [] `shouldSatisfy` errorContaining "PolicyUnknown \"global 3\""

    describe "SecWasm's restrictions (secwasm-restrictions)" $ do
        let restricted = ("secwasm-restrictions\n" <>)
            -- (block (result i32) (i32.const 7) (local.get $c) (br_if 0) <rest>)
            afterCoercion rest = singleFunctionModule [] [I32, I32] [I32] [I32] [Block (FuncType [] [I32]) ([Const SI32 7, LocalGet (LocalIdx 0), BrIf (LabelIdx 0)] ++ rest)]
            -- a value that a br_if coerced up, written to a public global when the branch is not taken
            coercedThenWritten = (afterCoercion [GlobalSet (GlobalIdx 0), LocalGet (LocalIdx 1), Br (LabelIdx 0)]) {globals = [RawGlobal (GlobalType Mutable I32) [Const SI32 0]]}
            -- a public argument pushed before a secret branch, passed to a public parameter after it
            argumentBeforeBranch = twoFunctions (FuncType [I32] []) [Nop] (FuncType [I32] []) [Const SI32 7, Block (FuncType [I32] []) [LocalGet (LocalIdx 0), BrIf (LabelIdx 0), Call (FunctionIdx 0)]]
        it "without them, a br_if that is not taken leaves the carried value at its own level" $ do
            elabRunWithPolicy "export f : L H -> H" coercedThenWritten [0, 5] `shouldBe` Right ["5"]
            elabRunWithPolicy "export f : L H -> H" coercedThenWritten [1, 5] `shouldBe` Right ["7"]
        it "with them, the value takes the target's type on both paths" $ do
            elabRunWithPolicy (restricted "export f : L H -> H") coercedThenWritten [0, 5] `shouldSatisfy` errorContaining "IllegalFlow \"global.set\" High Low"
            elabRunWithPolicy (restricted "export f : L H -> H") (afterCoercion [LocalGet (LocalIdx 1), Add SI32]) [0, 5] `shouldBe` Right ["12"]
            elabRunWithPolicy (restricted "export f : L H -> H") (afterCoercion [LocalGet (LocalIdx 1), Add SI32]) [1, 5] `shouldBe` Right ["7"]
        it "without them, a block's result may stay below the pc its body ends with; with them, it may not" $ do
            -- (block (block (result i32) (i32.const 0) (local.get $c) (br_if 0) <write the constant to a public global>
            --                            (local.get $yH) (br_if 1)) (drop))
            let resultBelowEndPc =
                    (singleFunctionModule [] [I32, I32] [] [I32] [Block (FuncType [] []) [Block (FuncType [] [I32]) [Const SI32 0, LocalGet (LocalIdx 0), BrIf (LabelIdx 0), LocalTee (LocalIdx 2), LocalGet (LocalIdx 2), GlobalSet (GlobalIdx 0), LocalGet (LocalIdx 1), BrIf (LabelIdx 1)], Drop]])
                        { globals = [RawGlobal (GlobalType Mutable I32) [Const SI32 0]]
                        }
            elabRunWithPolicy "export f : L H ->" resultBelowEndPc [0, 1] `shouldBe` Right []
            elabRunWithPolicy (restricted "export f : L H ->") resultBelowEndPc [0, 1] `shouldSatisfy` errorContaining "IllegalFlow \"global.set\" High Low"
        it "without them, a call may take an argument below the pc; with them, it may not" $ do
            elabRunWithPolicy "func 0 : L -{H}->\nexport f : H ->" argumentBeforeBranch [0] `shouldBe` Right []
            elabRunWithPolicy (restricted "func 0 : L -{H}->\nexport f : H ->") argumentBeforeBranch [0] `shouldSatisfy` errorContaining "IllegalFlow \"call\" High Low"

    describe "the ifc import namespace (annotations as calls)" $ do
        let ghost name ft = RawImport "ifc" name (ImportFunc ft)
            loadSecret = ghost "load_secret_i32" (FuncType [I32] [I32])
            storeSecret = ghost "store_secret_i32" (FuncType [I32, I32] [])
            declassify = ghost "declassify_i32" (FuncType [I32] [I32])
            withGhosts imports = ghostModule imports [I32]
        it "a store through the ghost is a secret store: a plain load then traps" $
            elabRunModule (withGhosts [storeSecret] [Const SI32 0, Const SI32 7, Call (FunctionIdx 0), Const SI32 0, Load SI32 (MemArg 0 0)]) []
                `shouldSatisfy` trapContaining "SecretRead (AccessAt 1 0)"
        it "a public load through the ghost traps on a secret byte, naming the ghost call" $
            elabRunModule (withGhosts [storeSecret, ghost "load_public_i32" (FuncType [I32] [I32])] [Const SI32 0, Const SI32 7, Call (FunctionIdx 0), Const SI32 0, Call (FunctionIdx 1)]) []
                `shouldSatisfy` trapContaining "SecretRead (GhostCallAt 2 1)"
        it "a load through the ghost is secret, so it needs declassification to come out" $ do
            elabRunModule (withGhosts [storeSecret, loadSecret] [Const SI32 0, Const SI32 7, Call (FunctionIdx 0), Const SI32 0, Call (FunctionIdx 1)]) []
                `shouldSatisfy` errorContaining "IllegalFlow \"result\""
            elabRunModule ((withGhosts [storeSecret, loadSecret, declassify] [Const SI32 0, Const SI32 7, Call (FunctionIdx 0), Const SI32 0, Call (FunctionIdx 1), Call (FunctionIdx 2)]) {customSections = [("ifc", "allow-declassify")]}) []
                `shouldBe` Right ["7"]
        it "a ghost must have the type its name says" $
            elabRunModule (withGhosts [ghost "load_secret_i32" (FuncType [I32] [I64])] [Const SI32 1]) [] `shouldSatisfy` errorContaining "PolicyGhostType"
        it "a ghost may not be exported" $
            elabRunModule ((withGhosts [declassify] [Const SI32 1]) {exports = [Export "f" (ExportFunc (FunctionIdx 0))]}) [] `shouldSatisfy` errorContaining "PolicyGhostReferenced"

    describe "indirect calls" $ do
        -- function 0 (type 0, [] -> [i32]) sits in slot 0 of the table; function 1, exported, calls through it
        let throughTable mainType mainBody =
                (moduleOf [] [RawFunction (FuncType [] [I32]) [] [Const SI32 42], RawFunction mainType [] mainBody] (FunctionIdx 1))
                    { tables = [RawTable FuncRef (Limits 1 Nothing)]
                    , elementSegments = [activeElements [Const SI32 0] [FunctionIdx 0]]
                    }
            underSecret = throughTable (FuncType [I32] [I32]) [LocalGet (LocalIdx 0), If (FuncType [] [I32]) [Const SI32 0, CallIndirect (TableIdx 0) (TypeIdx 0)] [Const SI32 1]]
            atPublicPc = throughTable (FuncType [] [I32]) [Const SI32 0, CallIndirect (TableIdx 0) (TypeIdx 0)]
        it "take the type the policy declares for the type-section entry, bound included" $ do
            elabRunWithPolicy "func 0 : -{H}-> H\ntype 0 : -{H}-> H\nexport f : H -> H" underSecret [1] `shouldBe` Right ["42"]
            elabRunWithPolicy "func 0 : -{H}-> H\nexport f : H -> H" underSecret [1] `shouldSatisfy` errorContaining "IllegalFlow \"call_indirect\" High Low"
        it "check at run time that the expected bound flows into the callee's" $ do
            elabRunWithPolicy "func 0 : -{H}-> H\ntype 0 : -> H\nexport f : -> H" atPublicPc [] `shouldBe` Right ["42"]
            elabRunWithPolicy "func 0 : -> H\ntype 0 : -{H}-> H\nexport f : -> H" atPublicPc [] `shouldSatisfy` trapContaining "IndirectCallBelowBound"
        it "a type declaration must name an entry the type section has" $
            elabRunWithPolicy "type 5 : -> L" atPublicPc [] `shouldSatisfy` errorContaining "PolicyUnknown \"type 5\""
        it "go through the table entry, typed" $
            elabRunModule (tableModule [Const SI32 0, CallIndirect (TableIdx 0) (TypeIdx 0)]) [] `shouldBe` Right ["42"]
        it "trap on an uninitialised entry" $
            elabRunModule (tableModule [Const SI32 1, CallIndirect (TableIdx 0) (TypeIdx 0)]) [] `shouldSatisfy` trapContaining "UninitializedElement"
        it "trap on an index past the table" $
            elabRunModule (tableModule [Const SI32 3, CallIndirect (TableIdx 0) (TypeIdx 0)]) [] `shouldSatisfy` trapContaining "UndefinedElement"
        it "trap when the entry's function has another type" $
            elabRunModule (tableModule [Const SI32 2, CallIndirect (TableIdx 0) (TypeIdx 0)]) [] `shouldSatisfy` trapContaining "IndirectCallTypeMismatch"
        it "need a table in the module" $
            first unplaced (void (elaborateModule (singleFunctionModule [] [] [I32] [] [Const SI32 0, CallIndirect (TableIdx 0) (TypeIdx 0)])))
                `shouldBe` Left (IndexOutOfRange Tables 0)
        it "reject an element segment that does not fit" $
            void (load ((tableModule [Const SI32 0]) {elementSegments = [activeElements [Const SI32 2] [FunctionIdx 0, FunctionIdx 0]]}))
                `shouldBe` Left (Uninstantiable (ElementSegmentOutOfBounds 0))
        it "reject an element segment in a module without a table at validation" $
            void (elaborateModule ((singleFunctionModule [] [] [] [] []) {elementSegments = [activeElements [Const SI32 0] [FunctionIdx 0]]}))
                `shouldBe` Left (IndexOutOfRange Tables 0)

    describe "references and tables" $ do
        -- function 0 (type 0, [] -> [i32]) sits in slot 0 of a table of two; function 1, exported, takes an i32
        let tabled results body =
                (moduleOf [] [RawFunction (FuncType [] [I32]) [] [Const SI32 42], RawFunction (FuncType [I32] results) [] body] (FunctionIdx 1))
                    { tables = [RawTable FuncRef (Limits 2 (Just 4))]
                    , elementSegments = [activeElements [Const SI32 0] [FunctionIdx 0]]
                    }
            setThenCall = tabled [I32] [Const SI32 1, RefFunc (FunctionIdx 0), TableSet (TableIdx 0), Const SI32 1, CallIndirect (TableIdx 0) (TypeIdx 0)]
            writeIfArgument = tabled [] [LocalGet (LocalIdx 0), If (FuncType [] []) [Const SI32 1, RefFunc (FunctionIdx 0), TableSet (TableIdx 0)] []]
            isSlotOneNull = tabled [I32] [Const SI32 1, TableGet (TableIdx 0), RefIsNull]
            size = tabled [I32] [TableSize (TableIdx 0)]
            growByArgument = tabled [I32] [RefNull FuncRef, LocalGet (LocalIdx 0), TableGrow (TableIdx 0)]
            callSlotZero = tabled [I32] [Const SI32 0, CallIndirect (TableIdx 0) (TypeIdx 0)]
        it "a function written to a table is the one an indirect call finds there" $
            elabRunModule setThenCall [0] `shouldBe` Right ["42"]
        it "table instructions trap past the end of the table, and growing stops at the maximum" $ do
            elabRunModule (tabled [I32] [LocalGet (LocalIdx 0), TableGet (TableIdx 0), RefIsNull]) [2] `shouldSatisfy` trapContaining "OutOfBoundsTableAccess"
            elabRunModule growByArgument [2] `shouldBe` Right ["2"]
            elabRunModule growByArgument [3] `shouldBe` Right ["4294967295"]
        it "a write under a secret pc needs a secret table" $ do
            elabRunWithPolicy "export f : H ->" writeIfArgument [1] `shouldSatisfy` errorContaining "IllegalFlow \"table.set\" High Low"
            elabRunWithPolicy "table 0 : H\nexport f : H ->" writeIfArgument [1] `shouldBe` Right []
        it "what is read from a secret table is secret, its size included" $ do
            elabRunWithPolicy "table 0 : H\nexport f : L -> L" isSlotOneNull [0] `shouldSatisfy` errorContaining "IllegalFlow"
            elabRunWithPolicy "table 0 : H\nexport f : L -> H" isSlotOneNull [0] `shouldBe` Right ["1"]
            elabRunWithPolicy "table 0 : H\nexport f : L -> L" size [0] `shouldSatisfy` errorContaining "IllegalFlow"
            elabRunWithPolicy "table 0 : H\nexport f : L -> H" size [0] `shouldBe` Right ["2"]
        it "growing a table by a secret count is a write to it" $ do
            elabRunWithPolicy "export f : H -> H" growByArgument [1] `shouldSatisfy` errorContaining "IllegalFlow \"table.grow\" High Low"
            elabRunWithPolicy "table 0 : H\nexport f : H -> H" growByArgument [1] `shouldBe` Right ["2"]
        it "a call through a secret table is a call from a secret context" $ do
            elabRunWithPolicy "table 0 : H\nexport f : L -> H" callSlotZero [0] `shouldSatisfy` errorContaining "IllegalFlow \"call_indirect\" High Low"
            elabRunWithPolicy "func 0 : -{H}-> H\ntype 0 : -{H}-> H\ntable 0 : H\nexport f : L -> H" callSlotZero [0] `shouldBe` Right ["42"]
        it "ref.func names only a function the module declares outside its code" $
            elabRunModule (moduleOf [] [RawFunction (FuncType [] []) [] [], RawFunction (FuncType [] []) [] [RefFunc (FunctionIdx 0), Drop]] (FunctionIdx 1)) []
                `shouldSatisfy` errorContaining "UndeclaredFunctionReference 0"
        it "a policy may only label a table that exists" $
            elabRunWithPolicy "table 1 : H" size [0] `shouldSatisfy` errorContaining "PolicyUnknown"

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
                    Right (CalledHost (SomeHostRequest shapeS funcs exports rsS (HostRequest FdWrite _ store resultsAgree suspended))) ->
                        case continueWith shapeS funcs exports rsS (resumeWith store (retagStack resultsAgree (99 :# VNil)) suspended) of
                            Right (Returned _ results) -> results `shouldBe` [I32Value 99]
                            _ -> expectationFailure "expected the module to return the fake errno"
                    _ -> expectationFailure "expected a suspended fd_write call"
        it "writing secret bytes to a public descriptor traps; to a secret one it goes through" $ do
            -- An iovec at 8 pointing at 4 secret bytes at 0; fd 1 is stdout.
            let body = [Const SI32 0, Const SI32 7, Annotated High (Store SI32 (MemArg 0 0)), Const SI32 8, Const SI32 0, Store SI32 (MemArg 0 0), Const SI32 12, Const SI32 4, Store SI32 (MemArg 0 0), Const SI32 1, Const SI32 8, Const SI32 1, Const SI32 16, Call (FunctionIdx 0)]
                program = either (error . show) id (load (wasiModule fdWriteImport body [I32]))
            leaked <- runWithWasi noHost program "f" []
            fmap describeCompletion leaked `shouldBe` Left (Trapped InformationFlowViolation)
            allowed <- runWithWasi noHost {descriptorLevels = publicDescriptors {standardOutput = High}} program "f" []
            fmap describeCompletion allowed `shouldBe` Right "returned [I32Value 0]"
        it "an iovec array with a secret byte cannot direct a write to a public descriptor" $ do
            -- The data at 0 is public; the iovec at 8 has a secret pointer field.
            let body = [Const SI32 8, Const SI32 0, Annotated High (Store SI32 (MemArg 0 0)), Const SI32 12, Const SI32 4, Store SI32 (MemArg 0 0), Const SI32 1, Const SI32 8, Const SI32 1, Const SI32 16, Call (FunctionIdx 0)]
                program = either (error . show) id (load (wasiModule fdWriteImport body [I32]))
            leaked <- runWithWasi noHost program "f" []
            fmap describeCompletion leaked `shouldBe` Left (Trapped InformationFlowViolation)
            allowed <- runWithWasi noHost {descriptorLevels = publicDescriptors {standardOutput = High}} program "f" []
            fmap describeCompletion allowed `shouldBe` Right "returned [I32Value 0]"
        it "the byte count of a read from a secret descriptor is secret" $ do
            -- fd_read of no bytes from stdin (fd 0), then a public load of the count it stored at 16.
            let body = [Const SI32 8, Const SI32 0, Store SI32 (MemArg 0 0), Const SI32 12, Const SI32 0, Store SI32 (MemArg 0 0), Const SI32 0, Const SI32 8, Const SI32 1, Const SI32 16, Call (FunctionIdx 0), Drop, Const SI32 16, Load SI32 (MemArg 0 0)]
                program = either (error . show) id (load (wasiModule (wasiImport "fd_read" (FuncType [I32, I32, I32, I32] [I32])) body [I32]))
            secret <- runWithWasi noHost {descriptorLevels = publicDescriptors {standardInput = High}} program "f" []
            fmap describeCompletion secret `shouldBe` Left (Trapped (SecretRead (AccessAt 1 2)))
            public <- runWithWasi noHost program "f" []
            fmap describeCompletion public `shouldBe` Right "returned [I32Value 0]"
        it "a path must be public" $ do
            -- path_open in the preopened directory (fd 3) of the one-byte path at 0.
            let pathOpen = wasiImport "path_open" (FuncType [I32, I32, I32, I32, I32, I64, I64, I32, I32] [I32])
                open storePath = storePath ++ [Const SI32 3, Const SI32 0, Const SI32 0, Const SI32 1, Const SI32 0, Const SI64 0, Const SI64 0, Const SI32 0, Const SI32 16, Call (FunctionIdx 0)]
                program storePath = either (error . show) id (load (wasiModule pathOpen (open storePath) [I32]))
                cfg = WasiConfig [] [] [Preopen "/" "test"] publicDescriptors
                name = [Const SI32 0, Const SI32 0x7A]
            secret <- runWithWasi cfg (program (name ++ [Annotated High (StoreN SI32 1 (MemArg 0 0))])) "f" []
            fmap describeCompletion secret `shouldBe` Left (Trapped InformationFlowViolation)
            public <- runWithWasi cfg (program (name ++ [StoreN SI32 1 (MemArg 0 0)])) "f" []
            fmap describeCompletion public `shouldBe` Right "returned [I32Value 44]"
        it "args_sizes_get reports the argument count and buffer size" $ do
            let cfg = WasiConfig ["prog", "xy"] [] [] publicDescriptors
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
            first unplaced (void (elaborateModule (singleFunctionModule [onePageMemory] [] [] [] [Const SI32 0, Const SI32 0, Const SI32 0, MemoryInit (DataIdx 3)])))
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
        it "names the function and the instruction, counted in code order, where an error arose" $
            void (elaborateModule (twoFunctions (FuncType [] []) [Nop] (FuncType [] []) [Nop, Block (FuncType [] []) [Nop], If (FuncType [] []) [Nop] [Nop, Const SI32 1, Add SI32]]))
                `shouldBe` Left (InFunction 1 (AtInstruction 3 (StackUnderflow "if")))
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

    describe "noninterference over generated programs (test/Noninterference.hs)" $ do
        -- A leak can be rare among the generated programs: a mutant that skips the load check
        -- first failed after 1,666 cases, and one that skips the comparison of the preserved
        -- global after 5,057, so this runs many more than the default hundred;
        -- WASM_IFC_NI_CASES sets the count for a longer campaign.
        cases <- runIO (maybe 10000 read <$> lookupEnv "WASM_IFC_NI_CASES")
        modifyMaxSuccess (const cases) $
            it "two runs that differ only in their secrets, and both finish, agree on everything public" $
                hedgehog $ do
                    generated <- forAll genModule
                    public <- forAll (Gen.word32 (Range.linear 0 64))
                    secret <- forAll (Gen.word32 Range.linearBounded)
                    otherSecret <- forAll (Gen.word32 Range.linearBounded)
                    let m = compileModule generated
                    case (observe m secret public, observe m otherSecret public) of
                        (Right (Just oneRun), Right (Just otherRun)) -> do
                            label "accepted, both runs finished"
                            classify "accepted, finished, holding a value across a conditional branch" (holdsValueAcrossBranch generated)
                            oneRun.result === otherRun.result
                            oneRun.publicGlobal === otherRun.publicGlobal
                            oneRun.preservedGlobal === otherRun.preservedGlobal
                            oneRun.publicTable === otherRun.publicTable
                            [(a, i) | (i, (a, Low), (_, Low)) <- zip3 [0 :: Int ..] oneRun.memory otherRun.memory]
                                === [(b, i) | (i, (_, Low), (b, Low)) <- zip3 [0 :: Int ..] oneRun.memory otherRun.memory]
                        (Right _, Right _) -> label "accepted, a run trapped"
                        _ -> label "rejected"
    describe "splitting locals into webs (Validation.LocalWebs) over generated programs" $ do
        cases <- runIO (maybe 2000 read <$> lookupEnv "WASM_IFC_NI_CASES")
        modifyMaxSuccess (const cases) $
            it "a module behaves the same with its locals split, split and merged again, and as written" $
                hedgehog $ do
                    generated <- forAll genModule
                    a <- forAll (Gen.word32 Range.linearBounded)
                    b <- forAll (Gen.word32 (Range.linear 0 64))
                    -- No secrets at all, so every form is accepted and only the behaviour is compared.
                    -- The validator does not split under such a policy, so the test splits and
                    -- merges itself; the merge groups the webs of a local under alternating
                    -- levels, since any grouping must be faithful, not only the one inference picks.
                    let m = compileModule (withPublicLoads generated)
                        (split, origins) = splitModuleLocals m
                        alternating = [zipWith const (cycle [Low, High]) f.locals | f <- split.functions]
                        params = [map (const Low) ps | RawFunction (FuncType ps _) _ _ <- split.functions]
                        (merged, _) = mergeModuleWebs origins params alternating split
                        run form = observeUnder "no-local-splitting\n" form a b
                        asWritten = run m
                    forM_ [run split, run merged] $ \other -> case (other, asWritten) of
                        (Right (Just one), Right (Just reference)) -> do
                            label "both runs finished"
                            one.result === reference.result
                            one.publicGlobal === reference.publicGlobal
                            one.memory === reference.memory
                        (Right Nothing, Right Nothing) -> label "both runs trapped"
                        _ -> do
                            annotate (show (void other) ++ " / " ++ show (void asWritten))
                            failure
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
    first unplaced (void (elaborateModule (singleFunctionModule memories params results locals body)))

-- | An error without the function and instruction it arose at: the rule alone.
unplaced :: ElabError -> ElabError
unplaced err = case err of
    InFunction _ inner -> unplaced inner
    AtInstruction _ inner -> unplaced inner
    _ -> err

singleFunctionModule :: [RawMemory] -> [ValType] -> [ValType] -> [ValType] -> [RawInstr] -> RawModule
singleFunctionModule memories params results locals body =
    moduleOf memories [RawFunction (FuncType params results) locals body] (FunctionIdx 0)

-- | Two functions, the second (function 1) exported as @f@ and free to call function 0.
twoFunctions :: FuncType -> [RawInstr] -> FuncType -> [RawInstr] -> RawModule
twoFunctions calleeType callee mainType mainBody =
    moduleOf [] [RawFunction calleeType [] callee, RawFunction mainType [] mainBody] (FunctionIdx 1)

{- | A module with a memory, the given imports first in the function index space, and one
  function of type @[] -> results@ with the given body, exported as @f@.
-}
ghostModule :: [RawImport] -> [ValType] -> [RawInstr] -> RawModule
ghostModule imports results body =
    (moduleOf [onePageMemory] [RawFunction (FuncType [] results) [] body] (FunctionIdx (fromIntegral (length imports))))
        { imports = imports
        , types = [ft | RawImport _ _ (ImportFunc ft) <- imports] ++ [FuncType [] results]
        }

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
        , customSections = []
        }

{- | Validate and instantiate a module and run its export @f@ on integer arguments.
| Load a module and read one of its exported globals, collapsing any error to text.
-}
readExportedGlobal :: RawModule -> Text -> Either String String
readExportedGlobal m name = case load m of
    Left err -> Left (show err)
    Right inst -> either (Left . show) (Right . renderValue) (readGlobalExport inst name)

-- | 'elabRunModule' under a policy given as text.
elabRunWithPolicy :: Text -> RawModule -> [Integer] -> Either String [String]
elabRunWithPolicy text m args = do
    policy <- first show (parsePolicy text)
    validated <- first show (elaborateModuleWith policy m)
    inst <- first show (instantiate validated)
    invokeWithIntegers inst args

errorContaining :: String -> Either String [String] -> Bool
errorContaining needle = either (needle `isInfixOf`) (const False)

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
    integerValue FuncRef _ = FuncRefValue nullReference
    integerValue ExternRef n = ExternRefValue (referenceTo (fromInteger n))

onePageMemory :: RawMemory
onePageMemory = RawMemory (MemType AddrI32 (Limits 1 Nothing))

{- | A three-entry table: entry 0 is function 0 (@() -> i32@, returning 42), entry 1 is left
  uninitialised, entry 2 is function 1 (@i32 -> i32@). The export @f@ is function 2 with the given
  body, of type @() -> i32@; type index 0 is @() -> i32@.
-}
tableModule :: [RawInstr] -> RawModule
tableModule body =
    (moduleOf [] [RawFunction (FuncType [] [I32]) [] [Const SI32 42], RawFunction (FuncType [I32] [I32]) [] [LocalGet (LocalIdx 0)], RawFunction (FuncType [] [I32]) [] body] (FunctionIdx 2))
        { tables = [RawTable FuncRef (Limits 3 Nothing)]
        , elementSegments = [activeElements [Const SI32 0] [FunctionIdx 0], activeElements [Const SI32 2] [FunctionIdx 1]]
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
noHost = WasiConfig [] [] [] publicDescriptors

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
        , customSections = []
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

-- | An active element segment for table 0: these functions, from a constant offset.
activeElements :: RawExpr -> [FunctionIdx] -> RawElementSegment
activeElements offset functions = RawElementSegment (ElemActive (TableIdx 0) offset) FuncRef [[RefFunc f] | f <- functions]
