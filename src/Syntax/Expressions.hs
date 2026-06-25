-- | An expression is a flat list of (tree-structured) instructions — a function body or a
--   global's initializer.
module Syntax.Expressions where

import Syntax.Instructions

type RawExpr = [RawInstr]
