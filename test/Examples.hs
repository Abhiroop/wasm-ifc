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
import Syntax.Types (
    FuncTypeOf (..),
    GlobalTypeOf (..),
    IsInt (..),
    IsNum (..),
    Mutability (..),
    SValType (..),
    ValType (..),
 )
import Syntax.TypesIFC (DynamicCheck (..), LValType (..), SLValType (..), SSecLevel (..), SecLevel (..))
import Validation.Ref (LocalRef, resolveLocal)
import Validation.Shape (Elem (..), ModuleShape (..))

{- | The single i32 a completed run produced. (These modules import nothing, so a call into
the host cannot arise; the case is still spelled out because the type admits it.)
-}

-- | A public i32: the labelled type nearly every example here works with.
type PublicI32 = 'I32 ':~ 'Low

-- | A secret i32.
type SecretI32 = 'I32 ':~ 'High

-- | The singleton of 'PublicI32'.
publicI32 :: SLValType PublicI32
publicI32 = SI32 :%~ SLow

{- | The constant one, public. A constant's level is free in its type (see 'IConst'), so an
  example has to say which level it means wherever nothing else decides it.
-}
one :: Instr mod frame labels 'NoDynamicCheck s (PublicI32 ': s)
one = IConst I32IsNum 1

completedI32 :: Outcome mod '[PublicI32] -> Either String Word32
completedI32 (Completed _ (x :# VNil)) = Right x
completedI32 (NeedsHost _) = Left "the example called into the host"

{- *** factorial *** -

   Iterative factorial, mirroring test/wat/factorial.wat. Parameter @n@ (local 0) and a
   declared accumulator (local 1). It type-checks, so the loop, the two labels, and every
   stack effect line up; a single misplaced instruction would not compile.
-}

factorial :: FuncInst shape ('FuncType '[PublicI32] '[PublicI32])
factorial =
    WasmFunc . Function (SCons publicI32 SNil) (SCons publicI32 SNil) $
        ( one
            :. ILocalSet acc
            :. block_
                ( loop_
                    ( ILocalGet n
                        :. one
                        :. ILe (IntsHaveSign I32IsInt Signed)
                        :. brIf_ toDone
                        :. ILocalGet acc
                        :. ILocalGet n
                        :. IMul I32IsNum
                        :. ILocalSet acc
                        :. ILocalGet n
                        :. one
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
    n, acc :: LocalRef PublicI32 '[PublicI32, PublicI32]
    n = resolveLocal publicI32 Here
    acc = resolveLocal publicI32 (There Here)
    -- Inside the loop the labels are: 0 = loop, 1 = block, 2 = function.
    toContinue, toDone :: Elem '[] '[ '[], '[], '[PublicI32]]
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
runSpinFor fuel = case runFor fuel FsNil (Config (moduleToStore emptyMod) noLocals VNil spinForever EntryBoundary) of
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

type CallCtx = 'ModuleShape '[ 'FuncType '[PublicI32, PublicI32] '[PublicI32]] '[] '[] '[] '[]

multiply :: FuncInst CallCtx ('FuncType '[PublicI32, PublicI32] '[PublicI32])
multiply = WasmFunc . Function (SCons publicI32 (SCons publicI32 SNil)) SNil $ (ILocalGet (resolveLocal publicI32 Here) :. ILocalGet (resolveLocal publicI32 (There Here)) :. IMul I32IsNum :. INil)

square :: FuncInst CallCtx ('FuncType '[PublicI32] '[PublicI32])
square = WasmFunc . Function (SCons publicI32 SNil) SNil $ (ILocalGet (resolveLocal publicI32 Here) :. ILocalGet (resolveLocal publicI32 Here) :. call toMultiply :. INil)
  where
    -- function index 0 in the module signature
    toMultiply :: Elem ('FuncType '[PublicI32, PublicI32] '[PublicI32]) '[ 'FuncType '[PublicI32, PublicI32] '[PublicI32]]
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

type GlobalCtx = 'ModuleShape '[] '[ 'GlobalType 'Mutable PublicI32] '[] '[] '[]

increment :: FuncInst GlobalCtx ('FuncType '[] '[PublicI32])
increment =
    WasmFunc . Function SNil SNil $
        ( IGlobalGet Here
            :. one
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
   broken = WasmFunc . Function (SCons publicI32 SNil) SNil $ (ILocalGet (resolveLocal publicI32 Here) :. IAdd I32IsNum :. INil)
-}

{- | A secret plus a public value. The type is the assertion: the sum is 'High, because a
  result is as secret as its most secret operand. Writing 'Low in the signature instead is a
  compile error. The test only counts the instructions, since the levels exist in types alone.

  TODO(ifc P2): examples to add as the checks land. A secret @if@ around a public @local.set@
  should not compile once the program counter label exists; keep it here as a commented
  program with the error GHC gives, as @broken@ above does for an ill-typed stack. A public
  value stored into a secret local should compile once the writes take a flow witness.
-}
secretPlusPublic :: Expr mod frame labels '[] '[SecretI32]
secretPlusPublic = secret :. one :. IAdd I32IsNum :. INil
  where
    secret :: Instr mod frame labels 'NoDynamicCheck s (SecretI32 ': s)
    secret = IConst I32IsNum 42

-- | The instruction count of 'secretPlusPublic'.
labelledSumLength :: Int
labelledSumLength = count secretPlusPublic
  where
    count :: Expr mod frame labels s s' -> Int
    count INil = 0
    count (_ :. rest) = 1 + count rest
