{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

{- | Functions, in their two forms: 'RawFunction' as decoded (the binary's function and code
  sections merged), and 'Function' as validated — its body an intrinsically-typed 'Expr'
  against its signature. A module's 'FunctionSpace' is its function index space: every
  function in index order, imported ones included (an import has a type and a name, and is
  linked to a host function only when the module is instantiated).
-}
module Syntax.Functions (
    RawFunction (..),
    FunctionBody,
    Function (..),
    FunctionSpace (..),
) where

import Data.Singletons (Sing)
import Data.Text (Text)

import Syntax.Instructions (Expr, RawExpr)
import Syntax.Types
import Syntax.TypesIFC (LabelledFuncType (..), LabelledValType)
import Validation.Shape (FrameShape (..), ModuleShape, ReverseOnto)

-- *** As decoded ***

data RawFunction = RawFunction
    { signature :: FuncType
    , locals :: [ValType]
    , body :: RawExpr
    }

-- *** As validated ***

{- | The type an 'Expr' must have to be a function body: from the empty operand stack it
  produces the function's results @rs@; its frame binds @locals@ and return type @rs@; and it
  runs under exactly one enclosing label — the function's own result — which is what @return@
  and falling off the end both target. Its pc stack starts at the function's bound, the most
  secret context it may be called from ('Syntax.TypesIFC.LabelledFuncType'); where the stack
  ends up does not matter to anyone, since the caller carries on with its own.
-}
type FunctionBody mod locals rs bound pcOut = Expr mod ('FrameShape locals rs) '[rs] '[bound] pcOut '[] rs

{- | A function as validated: the types of its parameters and of the locals it declares, and
  its body. The frame's locals are the parameters — reversed, since the argument segment lists
  the last one first and local 0 is the first parameter — followed by the declared locals.
  Both singletons are kept because a call packs its arguments into the callee's locals, and
  packing a value takes its type.
-}
data Function (mod :: ModuleShape) (ft :: LabelledFuncType) where
    Function ::
        Sing (ps :: [LabelledValType]) ->
        Sing (declared :: [LabelledValType]) ->
        FunctionBody mod (ReverseOnto ps declared) rs bound pcOut ->
        Function mod ('LabelledFuncType bound ps rs)

-- | A module's function index space: one entry per function type in the shape.
data FunctionSpace (mod :: ModuleShape) (fts :: [LabelledFuncType]) where
    NoFunctions :: FunctionSpace mod '[]
    Defined :: Function mod ft -> FunctionSpace mod fts -> FunctionSpace mod (ft ': fts)
    -- | an import: the module and name it comes from; its type is the entry's
    Imported :: Text -> Text -> FunctionSpace mod fts -> FunctionSpace mod (ft ': fts)
