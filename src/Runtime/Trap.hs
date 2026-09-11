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
    | {- TODO(ifc P1): SecWasm's dynamic checks trap (§4.2: "failure to satisfy the additional
         security checks also leads to a trap", rules E-*-TRAP in the technical report). Add one
         constructor for it, say @InformationFlowViolation@, raised by the load check
         (@⨆ ℓ of the bytes read ⋢ ℓ@ of the instruction) and by the host boundary's sink check;
         it is a defined outcome like every other trap, and TINI puts it outside the theorem. -}

      {- | a @call@ or @call_indirect@ that would nest activations past the interpreter's bound
      ('callDepthBound' in "Runtime.Interpreter")
      -}
      CallStackExhausted
    deriving stock (Eq, Show)
