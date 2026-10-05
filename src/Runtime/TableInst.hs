{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}

{- | A table of function references, indexed by the module's function types. Every initialised
  entry is a 'SomeFuncRef': a proof that it names a function of the module, together with that
  function's type — so an indirect call can be checked against it with @decideEquality@ and can
  never dereference a dangling index. Uninitialised entries are simply absent. Only @funcref@
  tables exist here, and no instruction changes a table after instantiation.

  'lookupChecked' is the one way the interpreter reads an entry, and half of the trusted code
  behind SecWasm's run-time checks (the other half is 'Runtime.MemInst.loadChecked'): it hands
  out the function only as a 'CheckedCallee' at the type it compared the entry's with, and
  that value is the evidence an indirect call's step has to present ("Runtime.Obligation").
-}
module Runtime.TableInst (
    TableInst,
    allocTable,
    tableSize,
    CheckedCallee,
    enteredCallee,
    lookupChecked,
    tableEntryUnchecked,
    setTableEntries,
) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Kind (Type)
import Data.Word (Word32)

import Data.Singletons (Sing)
import Data.Singletons.Decide (decideEquality)
import Data.Type.Equality ((:~:) (Refl))
import Runtime.Trap (Trap (..))
import Syntax.Types (Limits (..))
import Syntax.TypesIFC (FlowsInto, LabelledFuncType (..), LabelledValType, SLabelledFuncType (..), SecLevel, decideFlow)
import Validation.Shape (Elem, SomeFuncRef (..))

type TableInst :: [LabelledFuncType] -> Type
data TableInst fts = TableInst
    { limits :: !Limits
    , entries :: !(IntMap (SomeFuncRef fts))
    -- ^ by index; an absent entry is uninitialised
    }

-- | A table at its declared minimum size, with every entry uninitialised.
allocTable :: Limits -> TableInst fts
allocTable declared = TableInst declared IntMap.empty

-- | The current size; without @table.grow@ it is the declared minimum.
tableSize :: TableInst fts -> Word32
tableSize table = table.limits.min

{- | A function found in the table whose labelled parameters and results are the ones an
  indirect call expects, and whose bound @lt@ the expected bound @lf@ flows into (SecWasm's
  @ℓf ⊑ ℓt@). The constructor stays in this module and 'lookupChecked' is its only use, so a
  value of this type exists only if a table entry was compared with the expected type: it is
  both the function the call enters and the evidence that the call's check passed. The proof
  and the function share @lt@, so the proof is about that function.
-}
type CheckedCallee :: SecLevel -> [LabelledValType] -> [LabelledValType] -> [LabelledFuncType] -> Type
data CheckedCallee lf ps rs fts where
    CheckedCallee :: FlowsInto lf lt -> Elem ('LabelledFuncType lt ps rs) fts -> CheckedCallee lf ps rs fts

-- | The function of a checked callee, at whatever bound it has.
{-# INLINE enteredCallee #-}
enteredCallee :: CheckedCallee lf ps rs fts -> (forall lt. Elem ('LabelledFuncType lt ps rs) fts -> result) -> result
enteredCallee (CheckedCallee _ ix) k = k ix

{- | An indirect call's table lookup with its run-time checks (E-CALL-INDIRECT): the entry at
  @index@, if it is a function with the expected labelled parameters and results and a bound
  that the expected bound flows into. An index past the table, an uninitialised entry, another
  type and a lower bound are the four traps.
-}
{-# INLINE lookupChecked #-}
lookupChecked :: TableInst fts -> Word32 -> Sing ('LabelledFuncType lf ps rs) -> Either Trap (CheckedCallee lf ps rs fts)
lookupChecked table index (SLabelledFuncType expectedBound expectedParams expectedResults) = case tableEntryUnchecked table index of
    Left trap -> Left trap
    Right (SomeFuncRef boundS paramsS resultsS ix) ->
        case (decideEquality paramsS expectedParams, decideEquality resultsS expectedResults) of
            (Just Refl, Just Refl) -> case decideFlow expectedBound boundS of
                Just flows -> Right (CheckedCallee flows ix)
                Nothing -> Left IndirectCallBelowBound
            _ -> Left IndirectCallTypeMismatch

{- | The function an entry refers to, whatever its type. An index past the table is the spec's
  "undefined element" trap; an entry never initialised is "uninitialized element". Not for the
  interpreter, which reads through 'lookupChecked': this is for code outside the labelled
  machine (the benchmarks' erased copy).
-}
tableEntryUnchecked :: TableInst fts -> Word32 -> Either Trap (SomeFuncRef fts)
tableEntryUnchecked table index
    | index >= tableSize table = Left UndefinedElement
    | otherwise = maybe (Left UninitializedElement) Right (IntMap.lookup (fromIntegral index) table.entries)

-- | Initialise consecutive entries from an offset (an element segment); 'Nothing' if they do not fit.
setTableEntries :: Word32 -> [SomeFuncRef fts] -> TableInst fts -> Maybe (TableInst fts)
setTableEntries offset refs table
    | toInteger offset + toInteger (length refs) > toInteger (tableSize table) = Nothing
    | otherwise = Just table {entries = foldr (uncurry IntMap.insert) table.entries (zip [fromIntegral offset ..] refs)}
