{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}

{- | The evidence the machine has to present before it may step past an instruction whose
  rule has a premise only the machine can decide ('Syntax.TypesIFC.DynamicCheck').

  The point is that leaving such a check out of the interpreter is a type error rather than a
  bug. An instruction names its premise in its @check@ index, the step that runs it has to
  return a result carrying a 'CheckPassed' at that index, and the only way to build one for a
  load is to have read the bytes through 'Runtime.MemInst.loadChecked' and compared their
  labels with the instruction's through 'Syntax.TypesIFC.decideFlow'. Nothing reads the
  evidence afterwards; the driver drops it, and GHC drops the allocation with it.
-}
module Runtime.Obligation (
    CheckPassed (..),
) where

import Data.Kind (Type)

import Runtime.MemInst (LabelsOfRead)
import Syntax.TypesIFC (DynamicCheck (..), FlowsInto)

type CheckPassed :: DynamicCheck -> Type
data CheckPassed check where
    -- | The rule has no dynamic premise.
    NothingToCheck :: CheckPassed 'NoDynamicCheck
    {- | The bytes a load read had labels joining to @b@, and @b@ flows into the level @lm@
    written in the load. The first field can only come from the read itself, so this cannot
    be claimed about bytes that were not read.
    -}
    BytesWereBelow :: !(LabelsOfRead b) -> !(FlowsInto b lm) -> CheckPassed ('BytesBelow lm)
