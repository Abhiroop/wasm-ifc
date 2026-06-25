{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- GHC's coverage checker spuriously flags the single-equation 'factorial' binding as a
-- redundant pattern match — a known false positive for GADT values whose field types pass
-- through a type family (here 'RuntimeHostType'). The program is well-typed and runs, so
-- we silence just this warning here.
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

-- | Hand-written intrinsically-typed programs. That these /compile/ is the guarantee:
--   the type checker has verified they are stack- and type-correct WebAssembly. Running
--   them (see @test/@) is just a sanity check on the interpreter.
module Runtime.Examples
    ( runFactorial
    , runSquare
    , runIncrement
    ) where

import Data.Word (Word32)

import Runtime.Trap   (Trap)
import Syntax.Types   (FuncType (..), GlobalType (..), Mutability (..), NumType (..),
                       SNumType (..), Signedness (..), ValType (..))
import Validation.Shape  (Elem (..), ModuleShape (..))
import Syntax.Instructions
import Runtime.Interpreter
import Runtime.Stack

-- A shorthand for the only value type these examples use.
type I32 = 'Num 'I32

extractI32 :: ValueStack '[I32] -> Word32
extractI32 (x :# VNil) = x

{- *** factorial *** -

   Iterative factorial, mirroring test/wat/factorial.wat. Parameter @n@ (local 0) and a
   declared accumulator (local 1). It type-checks, so the loop, the two labels, and every
   stack effect line up; a single misplaced instruction would not compile. -}

factorial :: FuncInst shape ('FuncType '[I32] '[I32])
factorial = FuncInst (0 :& LNil)
    ( IConst SI32 1
   :. ILocalSet acc
   :. block_
        ( loop_
            (  ILocalGet n :. IConst SI32 1 :. ILe SI32 Signed :. brIf_ toDone
            :. ILocalGet acc :. ILocalGet n :. IMul SI32 :. ILocalSet acc
            :. ILocalGet n :. IConst SI32 1 :. ISub SI32 :. ILocalSet n
            :. br_ toContinue
            :. INil )
       :. INil )
   :. ILocalGet acc
   :. INil )
  where
    n, acc :: Elem I32 '[I32, I32]
    n   = Here
    acc = There Here
    -- Inside the loop the labels are: 0 = loop, 1 = block, 2 = function.
    toContinue, toDone :: Elem '[] '[ '[], '[], '[I32] ]
    toContinue = Here          -- branch to the loop header (restarts it)
    toDone     = There Here    -- branch out of the block (exits the loop)

runFactorial :: Word32 -> Either Trap Word32
runFactorial input =
    extractI32 <$> runFunction emptyModule factorial (input :# VNil)
  where
    emptyModule :: ModuleInst ('ModuleShape '[] '[] '[])
    emptyModule = ModuleInst FsNil GNil MNil

{- *** call *** -

   @square x = mul x x@, exercising a typed 'call' into another function in the module. -}

type CallCtx = 'ModuleShape '[ 'FuncType '[I32, I32] '[I32] ] '[] '[]

multiply :: FuncInst CallCtx ('FuncType '[I32, I32] '[I32])
multiply = FuncInst LNil (ILocalGet Here :. ILocalGet (There Here) :. IMul SI32 :. INil)

square :: FuncInst CallCtx ('FuncType '[I32] '[I32])
square = FuncInst LNil (ILocalGet Here :. ILocalGet Here :. call toMultiply :. INil)
  where
    -- function index 0 in the module signature
    toMultiply :: Elem ('FuncType '[I32, I32] '[I32]) '[ 'FuncType '[I32, I32] '[I32] ]
    toMultiply = Here

runSquare :: Word32 -> Either Trap Word32
runSquare input = extractI32 <$> runFunction callModule square (input :# VNil)
  where
    callModule :: ModuleInst CallCtx
    callModule = ModuleInst (FsCons multiply FsNil) GNil MNil

{- *** global *** -

   Reads, increments and writes back a mutable global, returning the new value. @global.set@
   on the (only) global type-checks only because it is declared 'Mutable. -}

type GlobalCtx = 'ModuleShape '[] '[ 'GlobalType 'Mutable I32 ] '[]

increment :: FuncInst GlobalCtx ('FuncType '[] '[I32])
increment = FuncInst LNil
    ( IGlobalGet Here :. IConst SI32 1 :. IAdd SI32 :. IGlobalSet Here
   :. IGlobalGet Here :. INil )

runIncrement :: Word32 -> Either Trap Word32
runIncrement initial = extractI32 <$> runFunction globalModule increment VNil
  where
    globalModule :: ModuleInst GlobalCtx
    globalModule = ModuleInst FsNil (GCons initial GNil) MNil

{- *** an ill-typed program (does NOT compile) ***

   Uncommenting the body below is a compile error — @i32.add@ needs two operands but only
   one is on the stack after a single @local.get@. The type checker reports the stack
   underflow statically; there is no way to even construct this program. This is the
   payoff of intrinsic typing. GHC says, verbatim:

       • Couldn't match type: '[ 'Num 'I32]
                        with: '[]
         In the first argument of ‘(:.)’, namely ‘IAdd SI32’

   broken :: FuncInst shape ('FuncType '[I32] '[I32])
   broken = FuncInst LNil (ILocalGet Here :. IAdd SI32 :. INil)
-}
