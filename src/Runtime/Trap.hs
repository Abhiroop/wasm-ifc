{- | WebAssembly traps: the runtime errors the spec defines.

A trap is a /defined/ outcome, not a stuck state: the type-soundness statement for the
typed interpreter is that every well-typed configuration either steps, finishes, or
traps. So these are produced as ordinary values, never via @error@. Ill-typed programs,
by contrast, cannot be represented at all (elaboration rejects them), so there is no
"type mismatch" trap.
-}
module Runtime.Trap (
    Trap (..),
) where

import Syntax.Immediates (AccessSite)

data Trap
    = IntegerDivideByZero
    | IntegerOverflow
    | OutOfBoundsMemoryAccess
    | InvalidConversionToInteger
    | UnreachableExecuted
    | -- | @call_indirect@ with an index past the table
      UndefinedElement
    | -- | @call_indirect@ through an entry never initialised
      UninitializedElement
    | -- | @call_indirect@ through a function of another type than expected
      IndirectCallTypeMismatch
    | {- | a load read a byte more secret than the level the instruction declares: one of
      SecWasm's two run-time information-flow checks (the others are static). The site is the
      load's, as a policy would declare it.
      -}
      SecretRead AccessSite
    | {- | a host call was handed a byte more secret than the descriptor it writes to, or the
      module entered an @ifc@ ghost import (which the policy stage rewrites away)
      -}
      InformationFlowViolation
    | {- | @call_indirect@ through a function whose bound is below the one the instruction
      expects, so the callee may not run in the context the call allows: SecWasm's other
      run-time check
      -}
      IndirectCallBelowBound
    | {- | a @call@ or @call_indirect@ that would nest activations past the interpreter's bound
      ('callDepthBound' in "Runtime.Interpreter")
      -}
      CallStackExhausted
    deriving stock (Eq, Show)
