module GoodBrTable where

import Syntax.Instructions
import Syntax.Types
import Syntax.TypesIFC
import Validation.Shape

-- The table of the paper's first finding, inside four blocks without results: two targets, the
-- labels at depths 0 and 3, chosen by a secret index. Its reach is its deepest target, so it
-- raises the entries of all four blocks, and both targets lie within the reach.
table :: Instr m f '[ '[], '[], '[], '[]] ('Low ': 'Low ': 'Low ': 'Low ': pcs) ('High ': 'High ': 'High ': 'High ': pcs) 'NoDynamicCheck (('I32 ':~ 'High) ': s) anyOut
table = IBrTable NothingCarried NoValuesFlow ANil (ReachesThere (ReachesThere (ReachesThere ReachesHere))) [Here] (There (There (There Here)))
