# wasm-ifc — backlog

What is still open. Finished work lives in the git history and, for the design, in `README.md`
and in the comments beside the code.

Priorities: **P1** is needed for the claims the project makes, **P2** for real programs or the
paper, **P3** is desirable. Items marked **decision** wait on Daniel. Open design points in the
code are `TODO(ifc Pn)` comments beside what they concern (`grep -rn 'TODO(ifc' src test`); they
are summarised here, not repeated.

## Where things stand (2026-09-28)

- WebAssembly: the spec testsuite passes for the supported subset (23,306 assertions, none
  failing, 960 skipped as unsupported features); the wasi-testsuite passes 72 of 72.
- Information flow: SecWasm's static rules in the single instruction type (labelled values, a
  pc stack with the branch raise, flow witnesses on writes, branches, returns and calls, the
  bound on function types), subtyping as `SegmentFlows` witnesses, inferred block results,
  per-byte memory levels with the run-time load check, the policy (custom section, `--policy`
  file, `ifc` ghost imports), and levels at the host boundary.
- Performance: allocation per step at the pre-IFC reference (`bench/tripwire.py`), except
  `call_indirect` at +2.8 %.

## Information flow

- [ ] **P2** Inference of the levels of undeclared internal functions. Two ways, written up in
  `Validation/Policy.hs`: re-run the typed elaboration raising a level on each failure, or a
  separate level-flow analysis. **decision**
- [ ] **P2** The two-run noninterference property test over the program generator
  (`test/Spec.hs`); compare only runs that both finish.
- [ ] **P2** Port or drop the branch `ifc-obligations`: it makes the load check a typed
  obligation of `step`, so an interpreter that forgets it does not compile. It predates the pc
  stack, memory levels and the policy, adds an index to `Instr`, and measured 0.7 to 4.3 %
  more allocation. **decision**
- [ ] **P3** A noninterference proof. Ours differs from SecWasm's in one place: stack values are
  not lifted on a branch, because every sink checks the pc (the argument is at `IBlock`).
  `Formalisation/` holds earlier Agda and Lean models.

## WebAssembly coverage

- [ ] **P2** `global.get` of an imported immutable global in initialisers, once globals can be
  imported.
- [ ] **P3** Imports of globals, memories and tables, and linking between modules.
- [ ] **P3** The `table.*` instructions, `elem.drop`, passive and declarative element segments.
- [ ] **P3** Multiple memories; reference and SIMD types; exported memories in the spec runner.

## Performance (paused while IFC lands)

- [ ] **P2** IFC's own cost: an interleaved timing sweep of this build against the pre-IFC one
  (`bench/README.md`).
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
- Host functions are public; the policy types the import; descriptors carry levels per stream
  and per preopened directory.
