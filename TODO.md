# wasm-ifc — backlog

What is still open. Finished work lives in the git history and, for the design, in `README.md`
and in the comments beside the code. The order of work follows the paper track's plan
(`paper/PLAN.md` on the `paper` branch); what has been delivered to it is in `HANDOFF.md`.

Priorities: **P1** is needed for the claims the project makes, **P2** for real programs or the
paper, **P3** is desirable. Items marked **decision** wait on Daniel. Open design points in the
code are `TODO(ifc Pn)` comments beside what they concern (`grep -rn 'TODO(ifc' src test`); they
are summarised here, not repeated.

## Where things stand (2026-09-30)

- WebAssembly: the spec testsuite passes for the supported subset (23,306 assertions, none
  failing, 960 skipped as unsupported features); the wasi-testsuite passes 72 of 72. Both also
  with SecWasm's restrictions on.
- Information flow: SecWasm's static rules in the single instruction type, with the repairs of
  the paper's findings (`br_table` raises down to its deepest target); inference of stores,
  block results, loop parameters, local variables (split into webs first) and internal
  functions; SecWasm's two restrictions behind `secwasm-restrictions`; labelled types for
  `call_indirect` with the run-time bound check `ℓf ⊑ ℓt`; public host imports and the complete
  host boundary rule (every byte a call takes is checked against its descriptor, every byte it
  stores carries the descriptor's level); secret regions labelled at instantiation; load traps
  that name their site.
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
  checker of `casestudies/` is rejected (`casestudies/README.md`). **decision**, together with
  the shadow-stack pointer below.
- [ ] **P3** Typed obligations cover the two checks of the pure machine (`Runtime/Obligation.hs`).
  The host driver's checks (`Runtime/Wasi.hs`: bytes handed to a descriptor) are plain code,
  with no evidence type.
- [ ] **P2** The shadow-stack pointer (`__stack_pointer`, global 0 of every wasi-sdk binary) is
  a public global that every non-leaf C function writes in its prologue, so no such function
  can be called under a secret pc, although the pointer is always restored. This is what
  rejects `printf` on secret data and an `assert` on secret data (`casestudies/README.md`).
  A sound treatment needs a rule for balanced save and restore. **decision**
- [ ] **P3** Inference is monomorphic: one label per parameter joins every call site's (a
  precision loss against WANILLA, `casestudies/README.md`).
- [ ] **P3** A noninterference proof (Lean, delta 6). `Formalisation/` holds earlier Agda and
  Lean models of the untyped core only.

## WebAssembly coverage

- [ ] **P2** `global.get` of an imported immutable global in initialisers, once globals can be
  imported.
- [ ] **P3** Imports of globals, memories and tables, and linking between modules.
- [ ] **P3** The `table.*` instructions, `elem.drop`, passive and declarative element segments.
- [ ] **P3** Multiple memories; reference and SIMD types; tail calls; exceptions; exported
  memories in the spec runner.

## Performance

- [ ] **P2** IFC's own cost: an interleaved timing sweep of this build against the pre-IFC one,
  with and without secrets in memory (`bench/README.md`).
- [ ] **P3** `call_indirect`: avoid the allocation of the level-aware type check (number table
  entries' types at instantiation), then re-record `bench/allocation.txt`.
- [ ] **P3** Memory in `ST` against persistent chunks, now that bytes carry levels
  (`BENCHMARKS.md`, E6).
- [ ] **P3** Retake the tables on native Linux before quoting them.

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
