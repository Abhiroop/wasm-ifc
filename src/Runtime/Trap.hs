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
         security checks also leads to a trap", rules E-*-TRAP in the technical report), but the
         IFC layer's memory has no dynamic label check to fail: a load's label is settled
         statically by the span its 'Syntax.TypesIFC.SpanAt' proof names, and an access that
         misses that span is an ordinary 'OutOfBoundsMemoryAccess' (a tighter bound than the
         memory's, raised the same way). What may still want a constructor of its own — say
         @InformationFlowViolation@ — is the host boundary's sink check, the one place where a
         label is compared at run time (see "Runtime.Host"). Either way it is a defined outcome
         like every other trap, and TINI puts it outside the theorem. -}

      {- | a @call@ or @call_indirect@ that would nest activations past the interpreter's bound
      ('callDepthBound' in "Runtime.Interpreter")
      -}
      CallStackExhausted
    deriving stock (Eq, Show)
