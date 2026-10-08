{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}

{- | A table: references of one type, by index, with the table's current size. An entry is a
  'Reference' as the value stack holds it, null until something is written there, so the
  table instructions move entries between a table and the stack unchanged, whatever the
  reference type; the shape of the table says which type it is.

  An indirect call needs the function behind an entry. A 'FunctionDirectory' gives, for a
  reference to a function of the module, that function's witness and type ('SomeFuncRef'); it
  is built once from the module's shape. 'lookupChecked' is the one way the interpreter reads
  an entry for a call, and half of the trusted code behind SecWasm's run-time checks (the other
  half is 'Runtime.MemInst.loadChecked'): it hands out the function only as a 'CheckedCallee' at
  the type it compared the entry's with, and that value is the evidence an indirect call's step
  has to present ("Runtime.Obligation").
-}
module Runtime.TableInst (
    TableInst,
    allocTable,
    tableSize,
    getEntry,
    setEntry,
    growTable,
    fillEntries,
    writeEntries,
    readEntries,
    FunctionDirectory,
    functionDirectory,
    CheckedCallee,
    enteredCallee,
    lookupChecked,
    tableEntryUnchecked,
) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Kind (Type)
import Data.Vector qualified as V
import Data.Word (Word32)

import Data.Singletons (Sing)
import Data.Singletons.Decide (decideEquality)
import Data.Type.Equality ((:~:) (Refl))
import Runtime.Trap (Trap (..))
import Syntax.Immediates (Reference, isNullReference, nullReference, referent)
import Syntax.Types (Limits (..))
import Syntax.TypesIFC (FlowsInto, LabelledFuncType (..), LabelledValType, SLabelledFuncType (..), SecLevel, decideFlow)
import Validation.Shape (Elem, SomeFuncRef (..))

data TableInst = TableInst
    { size :: !Word32
    , maxSize :: !(Maybe Word32)
    , entries :: !(IntMap Reference)
    -- ^ by index, below the size; an absent entry is null
    }

-- | A table at its declared minimum size, with every entry null.
allocTable :: Limits -> TableInst
allocTable declared = TableInst declared.min declared.max IntMap.empty

tableSize :: TableInst -> Word32
tableSize table = table.size

-- | The entry at an index, or 'Nothing' past the end of the table.
getEntry :: TableInst -> Word32 -> Maybe Reference
getEntry table index
    | index >= table.size = Nothing
    | otherwise = Just (IntMap.findWithDefault nullReference (fromIntegral index) table.entries)

setEntry :: Word32 -> Reference -> TableInst -> Maybe TableInst
setEntry index reference table
    | index >= table.size = Nothing
    | otherwise = Just (put index reference table)

-- (Null entries are not stored, so a table that is mostly empty stays small.)
put :: Word32 -> Reference -> TableInst -> TableInst
put index reference table
    | isNullReference reference = table {entries = IntMap.delete (fromIntegral index) table.entries}
    | otherwise = table {entries = IntMap.insert (fromIntegral index) reference table.entries}

{- | Grow a table by a number of entries, each the given reference; 'Nothing' if that would
  pass its declared maximum or the largest size an index can reach.
-}
growTable :: Word32 -> Reference -> TableInst -> Maybe TableInst
growTable count reference table
    | grown > maybe 0xFFFFFFFF toInteger table.maxSize = Nothing
    | otherwise = Just (foldr (`put` reference) table {size = fromInteger grown} (indicesFrom table.size count))
  where
    grown = toInteger table.size + toInteger count

-- | Write one reference to consecutive entries; 'Nothing' if they do not all exist.
fillEntries :: Word32 -> Word32 -> Reference -> TableInst -> Maybe TableInst
fillEntries from count reference table
    | toInteger from + toInteger count > toInteger table.size = Nothing
    | otherwise = Just (foldr (`put` reference) table (indicesFrom from count))

-- | Write references to consecutive entries from an index; 'Nothing' if they do not fit.
writeEntries :: Word32 -> [Reference] -> TableInst -> Maybe TableInst
writeEntries from references table
    | toInteger from + toInteger (length references) > toInteger table.size = Nothing
    | otherwise = Just (foldr (uncurry put) table (zip [from ..] references))

-- | Consecutive entries from an index; 'Nothing' if they do not all exist.
readEntries :: Word32 -> Word32 -> TableInst -> Maybe [Reference]
readEntries from count table
    | toInteger from + toInteger count > toInteger table.size = Nothing
    | otherwise = Just [IntMap.findWithDefault nullReference (fromIntegral index) table.entries | index <- indicesFrom from count]

indicesFrom :: Word32 -> Word32 -> [Word32]
indicesFrom from count = if count == 0 then [] else [from .. from + (count - 1)]

{- | The functions of a module by their index: what a reference to a function refers to. A
  reference that a module's code or element segments made names one of them
  ('Validation.Ref.FunctionRef'); for any other number 'referencedFunction' has no answer.
-}
type FunctionDirectory :: [LabelledFuncType] -> Type
newtype FunctionDirectory fts = FunctionDirectory (V.Vector (SomeFuncRef fts))

functionDirectory :: [SomeFuncRef fts] -> FunctionDirectory fts
functionDirectory = FunctionDirectory . V.fromList

referencedFunction :: FunctionDirectory fts -> Reference -> Maybe (SomeFuncRef fts)
referencedFunction (FunctionDirectory functions) reference = referent reference >>= \index -> functions V.!? fromIntegral index

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
  that the expected bound flows into. An index past the table, a null entry, another type and
  a lower bound are the four traps.
-}
{-# INLINE lookupChecked #-}
lookupChecked :: FunctionDirectory fts -> TableInst -> Word32 -> Sing ('LabelledFuncType lf ps rs) -> Either Trap (CheckedCallee lf ps rs fts)
lookupChecked directory table index (SLabelledFuncType expectedBound expectedParams expectedResults) = case tableEntryUnchecked directory table index of
    Left trap -> Left trap
    Right (SomeFuncRef boundS paramsS resultsS ix) ->
        case (decideEquality paramsS expectedParams, decideEquality resultsS expectedResults) of
            (Just Refl, Just Refl) -> case decideFlow expectedBound boundS of
                Just flows -> Right (CheckedCallee flows ix)
                Nothing -> Left IndirectCallBelowBound
            _ -> Left IndirectCallTypeMismatch

{- | The function an entry refers to, whatever its type. An index past the table is the spec's
  "undefined element" trap; a null entry is "uninitialized element". Not for the interpreter,
  which reads through 'lookupChecked': this is for code outside the labelled machine (the
  benchmarks' erased copy).
-}
tableEntryUnchecked :: FunctionDirectory fts -> TableInst -> Word32 -> Either Trap (SomeFuncRef fts)
tableEntryUnchecked directory table index = case getEntry table index of
    Nothing -> Left UndefinedElement
    Just reference -> maybe (Left UninitializedElement) Right (referencedFunction directory reference)
