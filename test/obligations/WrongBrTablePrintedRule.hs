module WrongBrTablePrintedRule where

import Syntax.Instructions
import Syntax.Types
import Syntax.TypesIFC
import Validation.Shape

-- The same table as SecWasm's printed rule types it: the rule raises as many entries as the
-- table has targets, two, whatever their depths, so the entries of the two outer blocks stay
-- public although the table may leave them.
-- Wrong: the target at depth 3 lies outside a reach of two labels.
table :: Instr m f '[ '[], '[], '[], '[]] ('Low ': 'Low ': 'Low ': 'Low ': pcs) ('High ': 'High ': 'Low ': 'Low ': pcs) 'NoDynamicCheck (('I32 ':~ 'High) ': s) anyOut
table = IBrTable NothingCarried NoValuesFlow ANil (ReachesThere ReachesHere) [Here] (There (There (There Here)))
