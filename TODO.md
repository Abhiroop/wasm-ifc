# wasm-ifc — backlog

What is still open. Finished work lives in the git history and, for the design, in `README.md`
and in the comments beside the code. The order of work follows the paper track's plan
(`paper/PLAN.md` on the `paper` branch); what has been delivered to it is in `HANDOFF.md`.

Priorities: **P1** is needed for the claims the project makes, **P2** for real programs or the
paper, **P3** is desirable. Items marked **decision** wait on Daniel. Open design points in the
code are `TODO(ifc Pn)` comments beside what they concern (`grep -rn 'TODO(ifc' src test`); they
are summarised here, not repeated.

## Where things stand (2026-10-13)

- WebAssembly: the spec testsuite, at the WebAssembly 3.0 release (all 257 scripts), passes for
  the supported subset (63,080 assertions, none failing, 2,122 skipped, counted by reason
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
  suite as an oracle, the wasi-testsuite's C programs, PolyBench, a service on a secret socket).

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
- [ ] **P3** The noninterference proof in Lean (`lean/`, delta 6) covers a core: control flow
  with `return`, direct and indirect calls, calls through a reference and tail calls, a
  memory with levels, local and global variables,
  preserved globals, `memory.size`, `memory.grow`, `memory.fill` and `memory.copy`, exceptions.
  The memory is of bytes, with data segments. Not in it: a table's size and growth, references to exceptions, the
  host's calls other than a read and a write, more than one value
  type. Its semantics evaluates a block's body on the block's parameters alone; that this
  agrees with the flat stack is not proved. `Formalisation/` holds earlier Agda and Lean
  models of the untyped core only.

## WebAssembly coverage

The supported subset is WebAssembly 3.0 without garbage collection: 2.0, plus several memories
per module, 64-bit memories and tables, tail calls, extended constant expressions, the relaxed
vector instructions, typed function references and exceptions. What the 3.0 suite skips
(`WASM_IFC_SPEC_REPORT=f cabal test wasm-ifc-spec; ./scripts/spec-report.py f`), in
assertions:

| Skipped | Why |
|---:|---|
| 877 | the module uses garbage collection |
| 1,245 | the module is malformed text, which the harness does not run (it runs binaries) |

Every other assertion of the suite passes (63,080).

- [ ] **P3** A module that imports one memory, table or writable global twice is linked only
  after `Runtime.Link.unaliased` has rewritten it, which an embedder must call before
  validation (the spec runner does). A policy that names a global or a table by index still
  names the index as written, which the rewriting leaves in place and unused.
- [ ] **P3** `Runtime.Link` has no WASI host: a module linked with others that calls a WASI
  function fails with `HostCallNotServed`. The CLI runs one module.
- [ ] **P3** `Runtime.Module.invokeExport` and the CLI give back no instance after a trap, so
  what the call wrote before trapping is lost to whoever would go on with the instance. The
  linker keeps it (`Runtime.Module.enterFunction`), and so does the spec runner now.
- [ ] **P3** A reference to a function is a word, the function's instance and index, which the table
  resolves in the module's directory of functions (`Runtime/TableInst.hs`). The typed
  instructions and element segments only make references to functions that exist
  (`Validation.Ref.FunctionRef`), but the word on the stack carries no proof of it, so the
  resolution answers "no function" for any other word and no type rules that case out. With
  linking the word would have to name a function of the store.
- [ ] **P3** A policy's regions are of memory 0 only; the other memories of a module have
  their byte labels but no declared regions.
- [ ] **P3** A 64-bit memory or table holds at most 2^32 - 1 pages or entries here (a memory of
  256 TiB); a module that declares a larger minimum does not instantiate, and growing past it
  fails as the spec allows.
- [ ] **P3** A tail call whose callee returns at lower levels than its caller declares leaves an
  instruction (`IRelabelTop`) before what the caller returns to; a long chain of such calls
  between functions of different result levels grows that continuation. A function that calls
  itself in tail position, or one of the same result levels, does not.
- [ ] **P3** The store keeps every exception that a clause caught by reference, for the
  `exnref` that names it, and never frees one.
- [ ] **P3** The typed program does not know whether a reference may be null, nor the function
  type behind one: `Validation.References` checks both on the module as written, and the typed
  instructions check again at run time. To have them in the types, a value type would carry a
  nullability and a function type, with subtyping in every rule that compares two types.
- [ ] **P3** `br_on_null` and `br_on_non_null` are elaborated as a null test and a conditional,
  so what they leave on the stack is at least as secret as the reference they tested. A rule
  of their own, like the one for `br_if`, would leave the other values at their own labels.
- [ ] **P3** Garbage collection.
- [ ] **P3** The vector instructions work on lists of lanes (`Runtime/Vector.hs`), which is
  simple and slow; nothing measures them. A vector is two words on the stack and in a frame.

## Performance

What two profiles of instructions executed found, and what was done about it, is in
`BENCHMARKS.md` ("Performance work of 2026-10-13" and its second round, which ends with
what each open point below would give). Open:

- [ ] **P1** The times in `BENCHMARKS.md` and in the paper are of c2a3f4b. The second round
  (1d633f3) took 28 % of the instructions away and was not timed: a sweep on a quiet machine
  (`bench/sweep-labels.sh`, about two hours) has to replace them.
- [ ] **P2** A store copies its 1 KiB chunk of bytes and inserts it in the chunk map: 600
  instructions, against 250 for a load. A store in place gave 16 to 20 % fewer cycles on
  three memory-bound programs in an experiment (not committed). Memory in `ST`, or as a
  mutable array behind a pure interface, is the next step; the machine is then a function
  of a configuration only if each configuration is used once, and it changes how instances
  hand a shared memory over (`Runtime.Link`) and how the two-run tests keep two states.
  **decision**
- [ ] **P2** A call finds its function, and `global.get` its global, by walking a list as
  long as the index (`getFunc`, `getGlobal`): 189 instructions per step on `funcs-64` against
  106 on `funcs-2`. An array indexed by the witness's position makes it constant; a function
  read from it has the type its witness says by how the array is built, which GHC cannot
  check without a comparison of types at each call.
- [ ] **P3** GHC's LLVM backend for the interpreter's module: untried, since `opt` and `llc`
  are not installed (GHC 9.12 takes LLVM 13 to 19). The native code generator moves values
  between registers and the C stack around the dispatch.
- [ ] **P3** The allocation area: `-A1m` looked 10 to 15 % better than the default in a noisy
  run. Needs a quiet machine and an executable linked with `-rtsopts`.
- [ ] **P3** A call computes the size of the callee's frame from the singletons of its types
  (`Runtime.Stack.wordsIn`, 4 % of `fib`), and a return appends the results to the caller's
  stack cell by cell (`appendStack`, 7 %). The frame size can be kept in `Function`.
- [ ] **P3** `br_table` turns its target into a label of the whole context at run time
  (`Validation.Shape.withinReach`, 1 to 2 % of the `br-table` kernel): the proof that the
  target is within the raise is walked on every execution.
- [ ] **P3** `relabelStack` rebuilds a segment whose levels do rise, value by value. It is the
  identity on the words. A coercion would make it free, at the price of one trusted line in
  the machine; with `SegmentAsItIs` covering the segments whose levels do not change, nothing
  measured asks for it.
- [ ] **P3** The front end under a policy that names a secret takes three to four times the
  time of plain validation (0.035 s against 0.010 s on a PolyBench kernel): the locals are
  split into webs, the module is elaborated until the labels settle (a function's own locals
  settle without the rest, since 2026-10-13), and once more with the webs merged.
- [ ] **P3** `bench/erased` is the twin of the typed core without labels. It has the general
  optimizations of the interpreter (2026-10-13) and none of the features added since the
  labels, so it bounds the cost of typing and labels together from below.
- [ ] **P3** wabt's interpreter is about twice as fast on the kernels, and wasm3, WAMR and
  wasmi 20 to 80 times on programs (`BENCHMARKS.md`). The paper's "within 20 % of wabt" was
  measured on another processor against wabt 1.0.27 and does not hold here.

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
