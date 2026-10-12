# Noninterference for the lift-free rules, in Lean

A Lean 4 development that proves termination-insensitive noninterference for the labelled
typing rules of this repository on a core of WebAssembly: blocks, loops and conditionals with
parameters and results, `br`, `br_if` and `br_table`, calls of the module's functions
(recursion included), local and global variables, and arithmetic on one value type. It has no `sorry`, and its theorems depend on Lean's three
standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

```
cd lean && lake build        # Lean 4.35.0, no dependencies; elan reads lean-toolchain
```

## What is proved

| Theorem | File | Statement |
|---|---|---|
| `rise` | `Basic.lean` | A typed sequence ends with a pc stack that is entrywise at least the one it started with (the paper's `lem:rise`). |
| `confine` | `Confinement.lean` | A typed sequence that starts under a secret pc leaves the public variables unchanged, and if it leaves by a branch, the target's type is all secret and the pcs of the blocks it leaves are secret. |
| `loop_alone` | `Confinement.lean` | The same for a loop whose body is typed under a secret pc, from any iteration on. |
| `ni` | `Noninterference.lean` | Two runs of a typed sequence from stacks and states that agree where public end in related outcomes (`OutRel`). |
| `tini` | `Noninterference.lean` | For a function of a well-typed module: two calls with arguments that agree where the parameters are public, from global variables that agree where public, if both return, return results that agree where the result type is public and leave global variables that agree where public. |

`Examples.lean` has a program that the rules type, with two runs of it, a program with an
implicit flow together with a proof that no typing of it exists, and a well-typed module of two
functions.

## The rules

`Typed C Λ e Π st Π' st'` in `Defs.lean` is the paper's judgment
`Λ ⊢ e : Π | st ⇒ Π' | st'` (appendix B, "The Rules"), with the rules of the typed instruction
type `Syntax.Instructions.Instr` for the instructions above:

- A branch raises the pcs of the blocks it may leave, and the label of no value (no lift).
- A `br_if` that is not taken leaves the values it would have carried at their own labels.
- `br_table` raises the pcs down to a depth that no target exceeds (the repaired rule).
- The results of a block, a loop and a conditional are at least the pc at which the body
  starts (the paper's Property (E), a witness of `IBlock`, `ILoop` and `IIf`).
- A call needs the caller's pc to flow into the callee's bound, and the arguments to flow into
  the parameters. The arguments need not be at least the pc (SecWasm's lift raised them).
- A module is well typed if every function body is typed as the paper's rule for functions
  says. That a function's results be at least its bound, which that rule also asks, is not
  used by the proof and is not part of `WellTyped`.
- The code after `br`, `br_table` and `unreachable` is not typed.

## How the proof goes

When two runs take different paths, one of them is on its way out of a block and the pcs of
the blocks it leaves are secret. From then on the relation between the two runs (`OutRel`)
says nothing about their stacks. The run that stays behind runs on under a secret pc, so
`confine` applies to it alone. The two runs meet again at the end of a block that one of them
left by a branch. A branch under a secret pc, or on a secret condition, goes to a label whose
type is all secret, so the block's results are secret in both runs and need not agree. Property
(E) gives the same where the runs took the two arms of a conditional on a secret, and where one
run iterates a loop longer than the other.

A block's body runs on the block's parameters alone (see below), so a value that a block has
abandoned never has to be related to anything. The relation "up to abandoned entries" of the
paper's appendix B.4 has no counterpart here.

## What differs from the paper's statement

- **The judgment is ours, not SecWasm's.** The rules are the W-rules, with a pc stack and the
  current block's segment, and not SecWasm's rules over a stack-of-stacks. The theorem is
  therefore noninterference for the typed instruction type directly, on this core, without
  the erasure and the typing inclusion (`lem:inclusion`).
- **The semantics is block-local.** `Eval` is big-step with the outcome "branch to label `i`",
  as SecWasm's, but a block's body is evaluated on the block's parameters, and what lies below
  them on the stack is put back under the body's results. SecWasm evaluates on one stack that
  holds the labels. On validated code the two agree, because a body never reaches below its
  parameters; this agreement is not proved here.
- **The core is small.** One value type; two levels; no memory, no indirect calls and no
  `return` (a branch to the function's label leaves the function, and the semantics of a call
  treats it so); no `local.tee`; `unreachable` is the only trap. The proof for memory needs
  the labels of the bytes in the relation between states, and a second relation for what one
  run under a secret pc does to them, since a store there may make a public byte secret; it
  is not here.
- **Parameters are numbered from the top of the stack.** Local `i` of a callee is the `i`-th
  argument counted from the top, where WebAssembly counts from the bottom. The order plays no
  part in the proofs.
