{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}

{- | A table of function references, indexed by the module's function types. Every initialised
  entry is a 'SomeFuncRef': a proof that it names a function of the module, together with that
  function's type — so an indirect call can be checked against it with @decideEquality@ and can
  never dereference a dangling index. Uninitialised entries are simply absent. Only @funcref@
  tables exist here, and no instruction changes a table after instantiation.
-}
module Runtime.TableInst (
    TableInst,
    allocTable,
    tableSize,
    tableLookup,
    setTableEntries,
) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Kind (Type)
import Data.Word (Word32)

import Runtime.Trap (Trap (..))
import Syntax.Types (FuncType, Limits (..))
import Validation.Shape (SomeFuncRef)

type TableInst :: [FuncType] -> Type
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

{- | The function an entry refers to. An index past the table is the spec's "undefined
  element" trap; an entry never initialised is "uninitialized element".
-}
tableLookup :: TableInst fts -> Word32 -> Either Trap (SomeFuncRef fts)
tableLookup table index
    | index >= tableSize table = Left UndefinedElement
    | otherwise = maybe (Left UninitializedElement) Right (IntMap.lookup (fromIntegral index) table.entries)

-- | Initialise consecutive entries from an offset (an element segment); 'Nothing' if they do not fit.
setTableEntries :: Word32 -> [SomeFuncRef fts] -> TableInst fts -> Maybe (TableInst fts)
setTableEntries offset refs table
    | toInteger offset + toInteger (length refs) > toInteger (tableSize table) = Nothing
    | otherwise = Just table {entries = foldr (uncurry IntMap.insert) table.entries (zip [fromIntegral offset ..] refs)}
