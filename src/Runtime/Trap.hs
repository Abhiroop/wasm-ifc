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

import Data.Text (Text)
import Syntax.Immediates (AccessSite)

data Trap
    = IntegerDivideByZero
    | IntegerOverflow
    | OutOfBoundsMemoryAccess
    | -- | a table instruction with an index past the table, or past the element segment
      OutOfBoundsTableAccess
    | InvalidConversionToInteger
    | UnreachableExecuted
    | -- | an exception left the function that was invoked: not a trap of the spec's, but how a run ends then
      UncaughtException
    | -- | @throw_ref@ of a null reference
      NullExceptionReference
    | -- | @ref.as_non_null@ of a null reference
      NullReference
    | -- | @call_ref@ of a null reference
      NullFunctionReference
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
    | {- | the module entered an @ifc@ ghost import (which the policy stage rewrites away), or a
      call out of the module would have carried a secret
      -}
      InformationFlowViolation
    | {- | a host call would have let a secret reach what is public: a byte more secret than the
      descriptor it is for, or in a path or a list of buffers, which are public; a file moved
      or linked between directories of different levels; or a failure that a secret decides
      and the call's public status would report. The call does nothing. It is named as the
      module imports it (@fd_write@).
      -}
      SecretToHost Text
    | {- | @call_indirect@ through a function whose bound is below the one the instruction
      expects, so the callee may not run in the context the call allows: SecWasm's other
      run-time check
      -}
      IndirectCallBelowBound
    | {- | a preserved global ('Syntax.Types.Preserved') does not hold, where the code in which a
      secret decided the control flow ends, the value it held where that code began
      -}
      GlobalNotRestored
    | {- | a @call@ or @call_indirect@ that would nest activations past the interpreter's bound
      ('callDepthBound' in "Runtime.Interpreter")
      -}
      CallStackExhausted
    deriving stock (Eq, Show)
