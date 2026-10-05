{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}

{- | The evidence the machine has to present before it may step past an instruction whose
  rule has a premise only the machine can decide ('Syntax.TypesIFC.DynamicCheck').

  The point is that leaving such a check out of the interpreter is a type error, not a bug
  that a test has to find. An instruction names its premise in its @check@ index, the step
  that runs it returns a result carrying a 'CheckPassed' at that index
  ('Runtime.Interpreter.StepResult'), and the evidence for the two checks can only be built
  from values that the checks themselves hand out:

    * for a load, a 'Runtime.MemInst.CheckedRead' at the load's level, which only
      'Runtime.MemInst.loadChecked' produces, after comparing the labels of the bytes it read
      with that level; the word the load pushes comes out of the same value;
    * for an indirect call, a 'Runtime.TableInst.CheckedCallee' at the expected type, which
      only 'Runtime.TableInst.lookupChecked' produces, after comparing the table entry's type
      with it; the function the call enters comes out of the same value.

  So the trusted code is those two functions. The interpreter reads memory and the table
  through nothing else. Nothing reads the evidence afterwards; the driver drops it.
-}
module Runtime.Obligation (
    CheckPassed (..),
) where

import Data.Kind (Type)

import Runtime.MemInst (CheckedRead)
import Runtime.TableInst (CheckedCallee)
import Syntax.TypesIFC (DynamicCheck (..))

type CheckPassed :: DynamicCheck -> Type
data CheckPassed check where
    -- | The rule has no premise of this kind.
    NothingToCheck :: CheckPassed 'NoDynamicCheck
    -- | The bytes the load read are labelled at most the level it declares.
    BytesWereBelow :: !(CheckedRead level) -> CheckPassed ('BytesBelow level)
    {- | The function the indirect call found has the expected labelled parameters and results,
    and the expected bound flows into its bound.
    -}
    CalleeWasWithin :: !(CheckedCallee bound ps rs fts) -> CheckPassed ('CalleeWithin bound)
