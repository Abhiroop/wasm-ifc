{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
-- GHC's coverage checker spuriously flags the single-equation 'factorial' binding as a
-- redundant pattern match — a known false positive for GADT values whose field types pass
-- through a type family (here 'HostType'). The program is well-typed and runs, so we silence
-- just this warning here.
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

{- | Hand-written intrinsically-typed programs. That these /compile/ is the guarantee:
  the type checker has verified they are stack- and type-correct WebAssembly. Running
  them (see @test/@) is just a sanity check on the interpreter.
-}
module Examples (
    runFactorial,
    runSquare,
    runIncrement,
    runSpinFor,
    labelledSumLength,
) where

import Data.Word (Word32)

import Data.Singletons.Base.TH (SList (SCons, SNil))
import Runtime.Interpreter
import Runtime.Stack
import Syntax.Functions (Function (..), FunctionBody)
import Syntax.Immediates (NumWithSign (..), Signedness (..))
import Syntax.Instructions
import Syntax.InstructionsIFC qualified as IFC
import Syntax.Types (
    FuncType (..),
    GlobalType (..),
    IsInt (..),
    IsNum (..),
    Mutability (..),
    SValType (..),
    ValType (..),
 )
import Syntax.TypesIFC (LValType (..), SecLevel (..))
import Validation.Shape (Elem (..), ModuleShape (..))

{- | The single i32 a completed run produced. (These modules import nothing, so a call into
the host cannot arise; the case is still spelled out because the type admits it.)
-}
completedI32 :: Outcome mod '[ 'I32] -> Either String Word32
completedI32 (Completed _ (x :# VNil)) = Right x
completedI32 (NeedsHost _) = Left "the example called into the host"

{- *** factorial *** -

   Iterative factorial, mirroring test/wat/factorial.wat. Parameter @n@ (local 0) and a
   declared accumulator (local 1). It type-checks, so the loop, the two labels, and every
   stack effect line up; a single misplaced instruction would not compile.
-}

factorial :: FuncInst shape ('FuncType '[ 'I32] '[ 'I32])
factorial =
    WasmFunc . Function (SCons SI32 SNil) $
        ( IConst I32IsNum 1
            :. ILocalSet acc
            :. block_
                ( loop_
                    ( ILocalGet n
                        :. IConst I32IsNum 1
                        :. ILe (IntsHaveSign I32IsInt Signed)
                        :. brIf_ toDone
                        :. ILocalGet acc
                        :. ILocalGet n
                        :. IMul I32IsNum
                        :. ILocalSet acc
                        :. ILocalGet n
                        :. IConst I32IsNum 1
                        :. ISub I32IsNum
                        :. ILocalSet n
                        :. br_ toContinue
                        :. INil
                    )
                    :. INil
                )
            :. ILocalGet acc
            :. INil
        )
  where
    n, acc :: Elem 'I32 '[ 'I32, 'I32]
    n = Here
    acc = There Here
    -- Inside the loop the labels are: 0 = loop, 1 = block, 2 = function.
    toContinue, toDone :: Elem '[] '[ '[], '[], '[ 'I32]]
    toContinue = Here -- branch to the loop header (restarts it)
    toDone = There Here -- branch out of the block (exits the loop)

{- *** a loop that never ends *** -

   @loop (br 0)@: the branch re-enters the loop forever. 'run' would not return; 'runFor'
   reports the spent budget, which is how termination becomes a testable property.
-}

spinForever :: FunctionBody shape '[] '[]
spinForever = loop_ (br_ Here :. INil) :. INil

-- | Whether the loop is still running after the given number of steps (it always is).
runSpinFor :: Int -> Either String Bool
runSpinFor fuel = case runFor fuel FsNil (Config (moduleToStore emptyMod) LNil VNil spinForever EntryBoundary) of
    Left trap -> Left (show trap)
    Right (OutOfFuel _) -> Right True
    Right (Halted _) -> Right False
  where
    emptyMod :: ModuleInst ('ModuleShape '[] '[] '[] '[] '[])
    emptyMod = ModuleInst FsNil GNil MNil TNil DNil

runFactorial :: Word32 -> Either String Word32
runFactorial input =
    either (Left . show) completedI32 (runFunction emptyModule factorial (input :# VNil))
  where
    emptyModule :: ModuleInst ('ModuleShape '[] '[] '[] '[] '[])
    emptyModule = ModuleInst FsNil GNil MNil TNil DNil

{- *** call *** -

   @square x = mul x x@, exercising a typed 'call' into another function in the module.
-}

type CallCtx = 'ModuleShape '[ 'FuncType '[ 'I32, 'I32] '[ 'I32]] '[] '[] '[] '[]

multiply :: FuncInst CallCtx ('FuncType '[ 'I32, 'I32] '[ 'I32])
multiply = WasmFunc . Function SNil $ (ILocalGet Here :. ILocalGet (There Here) :. IMul I32IsNum :. INil)

square :: FuncInst CallCtx ('FuncType '[ 'I32] '[ 'I32])
square = WasmFunc . Function SNil $ (ILocalGet Here :. ILocalGet Here :. call toMultiply :. INil)
  where
    -- function index 0 in the module signature
    toMultiply :: Elem ('FuncType '[ 'I32, 'I32] '[ 'I32]) '[ 'FuncType '[ 'I32, 'I32] '[ 'I32]]
    toMultiply = Here

runSquare :: Word32 -> Either String Word32
runSquare input = either (Left . show) completedI32 (runFunction callModule square (input :# VNil))
  where
    callModule :: ModuleInst CallCtx
    callModule = ModuleInst (FsCons multiply FsNil) GNil MNil TNil DNil

{- *** global *** -

   Reads, increments and writes back a mutable global, returning the new value. @global.set@
   on the (only) global type-checks only because it is declared 'Mutable.
-}

type GlobalCtx = 'ModuleShape '[] '[ 'GlobalType 'Mutable 'I32] '[] '[] '[]

increment :: FuncInst GlobalCtx ('FuncType '[] '[ 'I32])
increment =
    WasmFunc . Function SNil $
        ( IGlobalGet Here
            :. IConst I32IsNum 1
            :. IAdd I32IsNum
            :. IGlobalSet Here
            :. IGlobalGet Here
            :. INil
        )

runIncrement :: Word32 -> Either String Word32
runIncrement initial = either (Left . show) completedI32 (runFunction globalModule increment VNil)
  where
    globalModule :: ModuleInst GlobalCtx
    globalModule = ModuleInst FsNil (GCons initial GNil) MNil TNil DNil

{- *** an ill-typed program (does NOT compile) ***

   Uncommenting the body below is a compile error — @i32.add@ needs two operands but only
   one is on the stack after a single @local.get@. The type checker reports the stack
   underflow statically; there is no way to even construct this program. This is the
   payoff of intrinsic typing. GHC says, verbatim:

       • Couldn't match type: '[ 'I32]
                        with: '[]
         In the first argument of ‘(:.)’, namely ‘IAdd I32IsNum’

   broken :: FuncInst shape ('FuncType '[ 'I32 ] '[ 'I32 ])
   broken = WasmFunc . Function SNil $ (ILocalGet Here :. IAdd I32IsNum :. INil)
-}

{- | The first labelled program, for "Syntax.InstructionsIFC": a secret plus a public value.
  Its type is the assertion: the sum is 'High because the join reduces, and the program
  compiles only because a free-labelled constant can be pinned to either level. Nothing runs
  it yet.
  TODO(ifc P2): the examples to write as the TODOs land, each a type-level assertion like this
  one: the leaky @if@ (a secret condition, a public @local.set@ in a branch) that must /not/
  compile once the pc exists (keep it as a commented ill-typed program with its error, as the
  early phases did for @broken@); @select@ on a secret condition typing secret after the
  'ISelect' fix; a store of a public value into a secret local through the flow witness. When
  the P0 structure decision lands, these become runnable through 'runFunction' too.
-}
secretPlusPublic :: IFC.Expr shape ret locals labels '[] (('I32 ':~ 'High) ': '[])
secretPlusPublic = secret IFC.:. public IFC.:. IFC.IAdd I32IsNum IFC.:. IFC.INil
  where
    secret :: IFC.Instr shape ret locals labels s (('I32 ':~ 'High) ': s)
    secret = IFC.IConst I32IsNum 42
    public :: IFC.Instr shape ret locals labels s (('I32 ':~ 'Low) ': s)
    public = IFC.IConst I32IsNum 1

-- | The instruction count of 'secretPlusPublic': the one thing a labelled program can do so far.
labelledSumLength :: Int
labelledSumLength = count secretPlusPublic
  where
    count :: IFC.Expr shape ret locals labels s s' -> Int
    count IFC.INil = 0
    count (_ IFC.:. rest) = 1 + count rest
