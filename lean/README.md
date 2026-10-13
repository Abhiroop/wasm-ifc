# Noninterference for the lift-free rules, in Lean

A Lean 4 development that proves termination-insensitive noninterference for the labelled
typing rules of this repository on a core of WebAssembly: blocks, loops and conditionals with
parameters and results, `br`, `br_if`, `br_table` and `return`, direct calls, indirect calls,
calls through a reference and tail calls, direct and indirect, of the module's functions (recursion included), a bounded memory whose bytes carry a level, with loads and stores of several bytes, data segments (`memory.init`, `data.drop`),
SecWasm's run-time check on loads, `memory.size`, `memory.grow`, `memory.fill` and
`memory.copy`, a second memory with `memory.copy` between the two, a function table with a level, a size and a limit (`table.get`, `table.set`, `table.fill`, `table.copy`, `table.size`, `table.grow`), a host that reads from and writes to
descriptors of channels with levels and opens files in directories (`path_open`), local and global
variables with `local.tee`, exceptions (`throw`, `throw_ref` and `try_table` with its four kinds
of clause, so references to exceptions), preserved globals with
their run-time comparison, and arithmetic on one value type. It has no `sorry`, and its
theorems depend on Lean's three standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`).

```
cd lean && lake build        # Lean 4.35.0, no dependencies; elan reads lean-toolchain
```

**To check the statement without reading the proofs, read `STATEMENTS.md`**: it lists the
definitions and the theorem with their lines, each typing rule beside the constructor of the
implementation and the rule of the paper it stands for, and what is assumed.

## What is proved

| Theorem | File | Statement |
|---|---|---|
| `rise` | `Basic.lean` | A typed sequence ends with a pc stack that is entrywise at least the one it started with (the paper's `lem:rise`). |
| `confine` | `Confinement.lean` | A typed sequence that starts under a secret pc leaves the public variables unchanged, except the preserved globals, and changes no public memory cell except to make it secret (`Conf`). If it leaves by a branch, the label's type is all secret and the pcs of the blocks it leaves are secret (`Info`). |
| `pres_after`, `pres_after_call` | `Basic.lean` | Where two runs come out of a block, a loop, a conditional or a call, they agree on the preserved globals unless the pc there is secret. |
| `ni` | `Noninterference.lean` | Two runs of a typed sequence from stacks and states that agree where public, and on the preserved globals unless the pc is secret, end in related outcomes (`OutRel`). |
| `noninterference` | `Statement.lean` | The theorem in the paper's terms: two calls of a function from low-equivalent states (`LowEq`, the paper's definition of the attacker), if both end, end alike and in low-equivalent states. It is `tini` with the two relations of the proof put together. |
| `refinement` | `Machine.lean` | A run of the small-step machine from the call of a function to its end is a derivation of the big-step semantics with the same end (the paper's `lem:refinement`). No typing is assumed. |
| `machine_noninterference` | `Machine.lean` | `noninterference` for two runs of the machine. |
| `tini` | `Noninterference.lean` | For a function of a well-typed module: two calls with arguments that agree where the parameters are public, from states that agree where public, if both end, either both return or both end by the same exception with the same values, and they leave states that agree where public. If they return, their results agree where the result type is public, and they agree on the preserved globals too if both pass the comparison made at the function's return. |
| `leak_not_typed`, `leak_runs_differ` | `Findings.lean` | The paper's leak through `br_table` has no typing by these rules, and it has two runs, from states that differ in a secret local only, after which a public global differs. |
| `call_after_secret_branch_typed`, `write_after_public_branch_typed` | `Findings.lean` | The paper's two secure programs that SecWasm's rules for `call` and `br_if` reject are typed. |
| `SecWasm.printed_rule_accepts_leak`, `SecWasm.repaired_rule_rejects_leak`, `SecWasm.printed_rule_unsound` | `SecWasmPrinted.lean` | SecWasm's rules as printed, for the five instructions of the leak, type it; with the lift of `br_table` down to the deepest target they do not. |

`Machine.lean` has a small-step machine written after the implementation's `step`: a
configuration with a state, the operands of the current block, the rest of the block and a
control stack of labels and call boundaries, and one transition for each instruction.
`STATEMENTS.md` puts its parts beside those of `src/Runtime/Interpreter.hs`; that the two are
the same machine is what remains by reading. `Examples.lean` has two runs of it: an exception
caught in the function that throws it, and one that leaves a tail call's callee and is not
caught by the `try_table` around the tail call.

`Examples.lean` also has a `try_table` that catches what its body throws, with its typing and
its run, and a throw under a secret pc with a proof that no typing of it exists. Besides, it
has a program that the rules type, with two runs of it, a program with an
implicit flow and a store of a secret into a public cell, each with a proof that no typing of
it exists, a well-typed module of two functions, and a conditional on a secret that moves a
preserved global and puts it back: it is typed if it compares the global, a run of it passes
the comparison, and without the comparison no typing of it exists.

## The rules

`Typed C Λ e Π st Π' st'` in `Defs.lean` is the paper's judgment
`Λ ⊢ e : Π | st ⇒ Π' | st'` (appendix B, "The Rules"), with the rules of the typed instruction
type `Syntax.Instructions.Instr` for the instructions above:

- A branch raises the pcs of the blocks it may leave, and the label of no value (no lift).
- A `br_if` that is not taken leaves the values it would have carried at their own labels.
- `br_table` raises the pcs down to a depth that no target exceeds (the repaired rule).
- The results of a block, a loop and a conditional are at least the pc at which the body
  starts (the paper's Property (E), a witness of `IBlock`, `ILoop` and `IIf`).
- A load declares a level, and its result is at least that level, the address's and the pc. A
  store declares the level it gives the bytes it writes, which is at least the pc, the
  address's and the value's. A load and a store name how many bytes they access. At run time
  a load traps unless the level of every byte it reads flows into the declared one, which is
  the check on the join of their labels.
- `memory.init` is typed as `memory.fill`, and `data.drop` has no premise, under any pc. A
  run under a secret pc may therefore drop a segment that the other run keeps. The only
  instruction that reads a segment then traps in the run that dropped it, unless it asks for
  no byte, so two runs that both go on have read the same bytes (`seg_payload`).
- A call needs the caller's pc to flow into the callee's bound, and the arguments to flow into
  the parameters. The arguments need not be at least the pc (SecWasm's lift raised them).
- The function table has one level (`Ctx.table`). What `table.get` reads is as secret as the
  table, the index and the pc. `table.set` needs the pc, the index and the reference to flow
  into the table's level.
- An indirect call needs the pc, the level of the table index and the level of the table to
  flow into the bound of the expected type, and that type to be well formed: its results are
  at least its bound. At run
  time it traps unless the table entry names a function with the expected parameters and
  results whose bound is at least the expected one, as in the implementation and the paper.
- A call through a reference (`call_ref`) is an indirect call without the table: the pc and
  the level of the reference flow into the bound of the expected type. `br_on_null` has no
  rule of its own. It is the three instructions the elaborator writes for it, a copy of the
  reference (`dup`), a test (`unop`) and a conditional, each of which has its rule here.
- An exception is thrown only under a public pc and carries public values, and a `try_table`
  is typed only under a public pc. A clause's branch raises no pc.
- `memory.fill` labels the cells it writes at a level that is at least the pc's and those of
  its three operands. `memory.copy` makes no check: each cell it copies keeps its own level,
  raised by one that is at least the pc's and those of the count and the two addresses.
- A host call is made under a public pc with public arguments. The host's descriptors have
  levels, which are part of the state. A write to a descriptor traps unless every cell it
  takes flows into the descriptor's level; a read stores what it read, and how much, at the
  descriptor's level. The attacker sees what was written to a public descriptor and what is
  left to read from one (`IoRel`).
- The size of the memory is public: `memory.size` gives a value at the pc, and `memory.grow`
  is typed only under a public pc with a public amount.
- A module is well typed if every function body is typed as the paper's rule for functions
  says. That a function's results be at least its bound, which that rule also asks, is not
  part of `WellTyped`: the proof uses it in one place, an indirect call on a secret index,
  where two different functions run and their results must be secret. The rule for the
  indirect call asks it there.
- `return` is the branch to the outermost label, and raises every pc. A tail call is typed as
  the call followed by that branch, with the callee's results flowing into the function's.
- A global may be declared preserved (`Ctx.preserved`), as the policy does for the stack
  pointer of compiled C. A write to it needs no premise on the pc, and the value written is at
  most as secret as the pc: under a public pc this is the ordinary rule, and under a secret pc
  anything may be written. A read is the ordinary one.
- A block, a loop and a conditional name the globals they compare (`keep`). Either the pc does
  not drop where the construct ends, or every preserved global is among them (`Restores`). At
  run time the construct goes on only if those globals hold what they held at its start. The
  same holds of a function and of a call: either the function's body ends under a public pc,
  or the call compares every preserved global with its value at the call.
- The code after `br`, `br_table`, `return` and `unreachable` is not typed.

## How the proof goes

When two runs take different paths, one of them is on its way out of a block and the pcs of
the blocks it leaves are secret. From then on the relation between the two runs (`OutRel`)
says nothing about their stacks. The run that stays behind runs on under a secret pc, so
`confine` applies to it alone. The two runs meet again at the end of a block that one of them
left by a branch. A branch under a secret pc, or on a secret condition, goes to a label whose
type is all secret, so the block's results are secret in both runs and need not agree. Property
(E) gives the same where the runs took the two arms of a conditional on a secret, and where one
run iterates a loop longer than the other.

The preserved globals are apart from the other public variables. Two runs agree on them only
where the pc is public (`PresOr`), and a run under a secret pc may write them (`Conf` does not
constrain them). Where the pc drops again, at the end of a block, a loop, a conditional or a
call, both runs have passed the construct's comparison, so each holds what it held at the
construct's start; the pc there was public, since it is at most the pc after the construct, so
the two runs agreed then and agree now (`pres_after`, `pres_after_call`). A branch further out
skips the comparison of the blocks it leaves, and raises their pcs, so the pc has not dropped
until the branch lands.

Whether a run throws, and what, is public. A run under a secret pc does not end by an
exception (`confine`, where `Info` of such an outcome is false), so two runs that have gone
apart do not throw until they meet again, and two runs in step throw together, under a public
pc, where they agree on the preserved globals. An exception leaves blocks and calls without
their comparisons of the preserved globals. Nothing is lost: the state does not change on the
way to the clause, and the two runs agreed where the exception was thrown (`Sync.exn`). The
same clause catches it in both runs, with the same values (`caught_rel`).

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
- **A loop runs its iterations as a block runs its body.** The semantics has an instruction
  that no program contains, `iter`, for the iterations of a loop's body: the body again while
  it branches to the loop's label. A loop evaluates it once, as a block evaluates its body,
  and then compares the globals it names with the state at its start. So the comparison is
  with the values at the loop's first entry, as in the implementation, which records them
  once. Comparing with the values at the start of the last iteration would not be sound: one
  iteration could write a preserved global and the next one leave it.
- **The comparison names its globals.** The implementation compares every preserved global of
  the module, which a typed construct cannot leave out. Here a construct lists the globals it
  compares, and the rule asks that the list cover the preserved ones where the pc drops.
- **The host is two calls.** One reads and one writes, with the checks and the labels of the
  implementation's rule for the host boundary. WASI's other calls, its error codes, and
  results on the stack are not modelled.
- **The core is small.** One value type; two levels; the semantics of a tail call does not model that it
  runs in constant space. A tag
  is the number of public values its exceptions carry, a clause catches by tag or catches
  everything, and there is no reference to an exception (`exnref`, `throw_ref`, and the
  clauses that hand one out). The function table has no bound and no size, a reference in it is a number (zero for null), and
the table's instructions trap beyond its size. A value is a natural number, of which a store writes the low bytes. A load
  or a store outside the memory traps, a load also by the level check, and `unreachable` is
  the other trap. `memory.grow` fails only if the memory would exceed its limit, which is
  part of the state and the same in both runs; the implementation's may also fail for want of
  host memory, which the proof does not model.
- **Two relations between states.** `StRel` relates the states of two runs and is not
  transitive, because a cell that is secret in the middle state says nothing. `Conf` relates a
  state to a later one of the same run under a secret pc, in which a public cell may have
  become secret. This is SecWasm's Definition 6 with the paper's convention (C5).
- **Parameters are numbered from the top of the stack.** Local `i` of a callee is the `i`-th
  argument counted from the top, where WebAssembly counts from the bottom. The order plays no
  part in the proofs.
