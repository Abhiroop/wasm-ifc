-- | WebAssembly traps: the runtime errors the spec defines.
--
-- A trap is a /defined/ outcome, not a stuck state: the type-soundness statement for the
-- typed interpreter is that every well-typed configuration either steps, finishes, or
-- traps. So these are produced as ordinary values, never via @error@. Ill-typed programs,
-- by contrast, cannot be represented at all (elaboration rejects them), so there is no
-- "type mismatch" trap.
module Runtime.Trap
    ( Trap (..)
    ) where

data Trap
    = IntegerDivideByZero
    | IntegerOverflow
    | OutOfBoundsMemoryAccess
    | InvalidConversionToInteger
    | UnreachableExecuted
    deriving (Eq, Show)
