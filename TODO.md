# wasm-ifc — backlog

What is still open. Finished work lives in the git history and, for the design, in `README.md`
and in the comments beside the code. The order of work follows the paper track's plan
(`paper/PLAN.md` on the `paper` branch); what has been delivered to it is in `HANDOFF.md`.

Priorities: **P1** is needed for the claims the project makes, **P2** for real programs or the
paper, **P3** is desirable. Items marked **decision** wait on Daniel. Open design points in the
code are `TODO(ifc Pn)` comments beside what they concern (`grep -rn 'TODO(ifc' src test`); they
are summarised here, not repeated.

## Where things stand (2026-10-08)

- WebAssembly: the spec testsuite, at the WebAssembly 3.0 release (all 257 scripts), passes for
  the supported subset (30,693 assertions, none failing, 34,509 skipped, counted by feature
  below); the wasi-testsuite passes 72 of 72. Both also with SecWasm's restrictions on.
- Information flow: SecWasm's static rules in the single instruction type, with the repairs of
  the paper's findings (`br_table` raises down to its deepest target); inference of stores,
  block results, loop parameters, local variables (split into webs first) and internal
  functions; SecWasm's two restrictions behind `secwasm-restrictions`; labelled types for
  `call_indirect` with the run-time bound check `ℓf ⊑ ℓt`; public host imports and the complete
  host boundary rule (every byte a call takes is checked against its descriptor, every byte it
  stores carries the descriptor's level); secret regions labelled at instantiation; load traps
  that name their site. References and tables (ours, SecWasm has neither): a table has one
  level from the policy, like a global.
- Evidence: a two-run noninterference property test (100,000 cases, no counterexample); case
  studies with secrets in `casestudies/` (the password checker, SecWasm's examples, WANILLA's
  suite as an oracle, the wasi-testsuite's C programs, PolyBench).

## Information flow

- [ ] **P2** Error codes at the host boundary are as the host reports them. They depend on the
  descriptor table, the operands and the names in a directory, which the paper's model treats
  as public, and also on whether an operation on a secret file fails (a failed read or write),
  which the model does not cover. `fd_fdstat_get` reports a descriptor's type, flags and rights
  as public, as part of the descriptor table.
- [ ] **P2** The error check after a read: the byte count of a read from a secret descriptor is
  secret, so C's check of `read`'s result raises the pc of what follows, and the password
  checker of `casestudies/` through libc is rejected (`casestudies/README.md`). The checker
  itself now asks the host directly, where the status and the count are two values. Declaring
  a secret channel's length public was considered and declined (the length is sensitive).
- [ ] **P3** Typed obligations cover the two checks of the pure machine (`Runtime/Obligation.hs`).
  The host driver's checks (`Runtime/Wasi.hs`: bytes handed to a descriptor) are plain code,
  with no evidence type.
- [ ] **P2** Host calls under a secret pc. An import has the bound `Low`, so output decided by
  a secret is rejected even on a secret channel: this is what still rejects `printf` of a
  secret and an `assert` on a secret, now that the stack pointer can be declared preserved
  (`casestudies/README.md`). The general rule is the usual one for output, pc ⊔ data ⊑ channel,
  with the channel looked up at run time; it is of use to compiled C only together with a
  version of each libc wrapper per calling context. **decision**, after the deadline.
- [ ] **P3** Inference is monomorphic: one label per parameter joins every call site's (a
  precision loss against WANILLA, `casestudies/README.md`).
- [ ] **P3** A noninterference proof (Lean, delta 6). `Formalisation/` holds earlier Agda and
  Lean models of the untyped core only.

## WebAssembly coverage

The supported subset is WebAssembly 2.0 without vector instructions and with imports of
functions only. What the 3.0 suite skips
(`WASM_IFC_SPEC_REPORT=f cabal test wasm-ifc-spec; ./scripts/spec-report.py f`), by the features
a skipped module uses according to `wasm-tools`, in assertions:

| Skipped | Features the module uses beyond the subset |
|---:|---|
| 25,355 | vector instructions |
| 3,107 | none: imports of tables, memories and globals; functions imported from another module of the script |
| 2,280 | 64-bit memories and tables |
| 834 | multiple memories |
| 821 | garbage collection |
| 424 | typed function references |
| 88 | tail calls with typed function references (34 with tail calls alone) |
| 79 | extended constant expressions |
| 61 | exceptions (98 more with another feature) |
| 1,245 | none: malformed modules given as text, which the harness does not run |

Of the 3,107, 2,616 are `table_copy.wast` and `table_init.wast` (and their 64-bit twins), whose
modules import functions from a module the script registers. `return_call.wast` needs typed
function references.

- [ ] **P2** Imports of globals, memories and tables, and linking between modules in the spec
  runner (`register`, the `spectest` module); `global.get` of an imported global in
  initialisers.
- [ ] **P3** A reference to a function is a word, the function's index, which the table
  resolves in the module's directory of functions (`Runtime/TableInst.hs`). The typed
  instructions and element segments only make references to functions that exist
  (`Validation.Ref.FunctionRef`), but the word on the stack carries no proof of it, so the
  resolution answers "no function" for any other word and no type rules that case out. With
  linking the word would have to name a function of the store.
- [ ] **P3** Tail calls; extended constant expressions; multiple memories; 64-bit memories.
- [ ] **P3** Vector instructions; exceptions; typed function references; garbage collection.

## Performance

- [ ] **P2** The cost of the labels was measured on 2026-10-06 on a loaded machine
  (`BENCHMARKS.md`): the ratios stand with their spread, the absolute times do not. Re-run on a
  quiet machine, `PRE=<wasm-ifc built at 0fcf4b4> ./bench/sweep-labels.sh`, after
  `./bench/tools/fetch.sh wasm3` (WAMR's release binary does not run on EL9: build it from
  source or drop it from the table), and replace the section's timings.
- [ ] **P2** With secrets in memory the interpreter takes 1.7 to 1.8 times the time and
  allocates 2.1 to 2.2 times as much (`BENCHMARKS.md`): a store under a secret label copies a
  chunk of the label map as well as a chunk of bytes. Keeping a byte and its label in one
  chunk, or the label map coarser where a whole chunk is secret, would be the first things to
  try.
- [ ] **P3** `call_indirect`: avoid the allocation of the level-aware type check (number table
  entries' types at instantiation), then re-record `bench/allocation.txt`.
- [ ] **P3** The front end under a policy that names a secret: splitting, inference and the
  merge take three times the time of plain validation on CoreMark (0.09 s against 0.03 s). The
  reaching-definitions pass keeps a set of definitions per local at every point.
- [ ] **P3** Memory in `ST` against persistent chunks, now that bytes carry levels
  (`BENCHMARKS.md`, E6).
- [ ] **P3** `bench/erased` is the twin of the typed core without labels (it is kept compiling,
  not in lockstep): against it the typed core of 0fcf4b4 is at 1.00 and the labelled build at
  1.05 on the loaded machine. A twin of the labelled machine would separate typing from labels
  at the current commit; settle whether the paper needs one.

## Repository

- [ ] **decision** The cabal `author`, `maintainer` and `synopsis`.
- [ ] **decision** Keep or remove `app.old/` (the original prototype), `exercises/` (a scratch
  file), and the template `Formalisation/wasmifc/README.md`.

## Decisions on record

- One instruction type for WebAssembly and information flow; the plain interpreter is the
  instance where everything is public.
- SecWasm's memory: a level per byte, changed by stores, checked on loads at run time. The
  alternative of declared spans with static labels (branch `refactor-pcc`) was tried and not
  adopted, because compiled code keeps secrets and public data in one heap and stack.
- A stack of pc labels, one per enclosing block, as in SecWasm and the `ifc` branch.
- The policy: everything SecWasm annotates is expressible; stores are inferred; loads take a
  site, a region, a function default or a module default; the interface is declared or public.
- Host functions are public: their bound is `Low` and their parameters public; the policy may
  declare their results secret; descriptors carry levels per stream and per preopened directory.
- Inference by re-elaboration (2026-09-30): the typed rules are the only copy of the rules; a
  failure names the labels that would repair it, and the elaborator raises them until the
  module is accepted or no named label can rise.
- Locals are split into webs before typing (2026-09-30), which makes a local's label
  flow-sensitive at the granularity of its live ranges without changing the typing rules.
