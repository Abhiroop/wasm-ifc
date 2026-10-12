# Hand-off to the paper track

What the implementer track delivered against `paper/PLAN.md` (branch `paper`), item by item,
with the names the paper can cite and the data behind each claim. Numbers are from 2026-09-30
on this machine (Linux, GHC 9.12.2); commits are on `implement`.

## Phase 0

**1. The restrictions of `int:relax`, behind a flag** (b0cae86)
- Flag: the policy statement `secwasm-restrictions`; on the command line
  `--secwasm-restrictions`; for the suites `WASM_IFC_SECWASM_RESTRICTIONS=1`. Off by default.
- In the types: `ICall` and `ICallIndirect` carry `ArgumentsAtCallPc pc ps`
  (`ArgumentsAtAnyLevel` | `ArgumentsAtLeastPc (AllAtLeast pc ps)`); `IBrIf` carries
  `FallThrough rs s full out` (`KeepsLevels`, output `full` | `TakesTargetType`, output
  `rs ++ s`, and the fall-through path relabels the carried values).
- With the flag on: spec suite 23,306 passed, 0 failed, 960 skipped; wasi-testsuite 72 of 72.
- Unit tests: programs A and B of `int:relax` are accepted without the flag and rejected with it.

**2. Import labels and exported results** (ce3b226)
- The policy stage rejects a host import with a bound other than L or a secret parameter
  (`PolicyImportNotPublic`); its results may be secret.
- Linking states the rule in `HostFunc`'s type: the import's bound is `'Low` and its arguments
  flow into the host's public parameters (`SegmentFlows ps hostParams`); otherwise
  `ImportNotPublic`.
- The CLI's `invoke` refuses an export whose results the policy declares secret, and `get` a
  secret global (the embedder is the observer). The unit test "an import may be declared at
  levels of the policy's choosing" is now "an import's results may be declared secret".

**3. Labelled types for indirect calls, ⊑ at run time** (13b97a3)
- Policy statement `type N : ... -{l}-> ...` labels entry N of the type section.
- Run-time check: labelled parameters and results equal, and the expected bound flows into the
  callee's (`decideFlow expectedBound boundS`); a failure traps with `IndirectCallBelowBound`
  (a type mismatch still traps with `IndirectCallTypeMismatch`).

**4. `br_table` raises to its deepest target** (ea6e058)
- Witness `TableReach l labels pcs pcs' reach` (`Validation.Shape`): it raises the pc entries
  of the labels down to the deepest target, and the targets are `Elem`s into that prefix, so a
  target deeper than the raise cannot be represented. SecWasm's printed leak is a unit test and
  a case study, and is rejected.

**5. Regions labelled at instantiation; load traps name their site** (ec3f976)
- Instantiation labels the bytes of each secret region after placing the data segments
  (`Module.secretRegions`, `MemInst.labelRange`); a region outside the memory fails with
  `RegionOutOfBounds`. The constant-address peephole now covers every byte of the load and
  applies to loads only.
- The load check traps with `SecretRead site`, where `site` is `AccessAt function position`
  (the policy's `load F N`) or `GhostCallAt function call`; the CLI prints the declaration that
  would make the load secret. `InformationFlowViolation` remains for host writes.

**5b. A witness for Property (E), and (E⁺) as the third restriction**
- `IBlock`, `ILoop` and `IIf` carry `AllAtLeast` for the pc their body starts with (`pc`,
  `pcLoop`, `Join pc lv`), so Property (E) holds for every typed program, not only for the
  elaborator's output.
- `IBlock` and `IIf` also carry `ResultsAtEndPc pcEnd rs` (`ResultsAtAnyLevel` |
  `ResultsAtLeastEndPc (AllAtLeast pcEnd rs)`), with `pcEnd` the top pc entry the body ends
  with (`pcBody`, `Join pcThen pcElse`): Property (E⁺), imposed under `secwasm-restrictions`.
  Program C of `app:findings` is a unit test: accepted without the flag, rejected with it.
- With the flag on (three restrictions): spec suite 23,306 passed, 0 failed, 960 skipped;
  wasi-testsuite 72 of 72.

**5c.** `casestudies/secwasm/finding5-br-table-values-below`: the block of §4.2, verdict "runs".

## Phase 1

**6. Inference of locals and internal functions** (8500ebe, d9cb140, 624a05a)
- Re-elaboration, as the plan recommends. A flow that fails only because an inferred label is
  too low fails with `LevelTooLow [Raise] err`, where `Raise` is `RaiseLocal`, `RaiseParam`,
  `RaiseResult` or `RaiseBound`; `elaborateModuleInferring` raises what every failing function
  names and elaborates again, until the module is accepted or no named label can rise. Raising
  a bound raises the results. Inferred: every local, and the parameters, results and bound of
  every internal function (not imported, exported, declared, in a table, or the start function).
- **Local splitting** (d9cb140, `Validation.LocalWebs`): before typing, every local is split
  into its webs (reaching definitions over the structured control flow). This was needed
  because LLVM reuses locals across variables at every optimisation level: in the password
  checker, the descriptor of the secret file and bytes of the password shared a local, and no
  build was typable. The renaming preserves every value, so it needs no change to the rules;
  the spec suite and the wasi-testsuite run through it. This is flow-sensitivity of locals at
  the granularity of live ranges, which PLAN.md lists as out of scope: the paper should decide
  how to present it (one box, as PLAN.md suggests, or as part of inference).
- Block results, loop parameters and a loop's pc are retried at secret only for a failure
  that concerns them (`BlockTooLow` with `OwnResults`, `LabelsAt` or `LoopPc`): the end of the
  block's body, a branch that carries values to its label, or the loop's back edge. Before,
  every enclosing block retried on any flow error, which cost time exponential in the nesting
  depth for each failure (delta 12's "nested retries"); one wasi-testsuite program did not
  finish validating in a minute and now takes a second.
- Diagnostics: errors carry `InFunction f (AtInstruction n err)` (instructions counted in code
  order, as `wasm2wat` lists them); `elaborateModuleTraced` and the CLI's `explain` report what
  inference raised, per attempt.

**7. Two-run noninterference property test** (65bb6a2)
- Generator: `test/Noninterference.hs`. Modules of an internal helper (`i32 -> i32`) and an
  exported `f : i32⟨H⟩ i32⟨L⟩ -> i32⟨L⟩`, a public and a secret global, one page of memory with
  a secret region [32, 64). Statements: local, global and memory writes, `if`, blocks, bounded
  loops (1–3 iterations), `br_if`, `br_table`, `br`; expressions: constants, locals, globals,
  loads declared L or H, binary operators, `if` with a result, calls to the helper, and a value
  held on the stack while statements run in a block (the lift shape). Statement nesting 3,
  expression depth 3, up to 3 statements per sequence.
- Property: when both runs (same public input, different secrets) finish, the result, the
  public global and the memory bytes both runs label public agree.
- 100,000 cases (`WASM_IFC_NI_CASES=100000`, 20 s): 34 % accepted and both runs finished,
  1 % accepted with a trap, 65 % rejected; 3 % are accepted programs that hold a value across a
  conditional branch. **No counterexample.** A mutant that skips the load check is caught after
  1,666 cases; the suite runs 2,000.

**8. Case studies with secrets** (`casestudies/`, README there; results in
`casestudies/results/`)
- **(a) The overview's password checker** (`password/`). The plainly written C program is
  rejected: the compiler moves the verdict's `write` into the blocks of branches on the hash,
  so the host is called under a secret pc. A branch-free version runs under a four-line policy
  (three channels, `load-default func 11 : H`); inference raises six locals and `write`. Its
  two leaks (the verdict or the hash in the log) trap at `fd_write` on the public log.
  C globals are in linear memory, so the overview's `global 0 : H` is a region or a load
  declaration in a real binary.
- **(b) SecWasm's examples and the findings** (`secwasm/`): Figure 2a, Examples 1–8 and the
  counterexamples of `int:secwasm` (items 1–4, 6, 7) as modules; all seventeen end as expected.
- **(c) WANILLA** (`wanilla/oracle.py`, artifact downloaded, not copied): of 312 active
  specifications, all 63 expressible leaks are rejected statically; 152 of 196 expressible
  noninterferent ones are accepted; 44 precision losses (at `result` 21, `return` 11,
  `memory.grow` 5, `call_indirect` 4, `call` 2, `local.tee` 1); 53 not expressible (memory,
  table and import queries 33, memory or global imports 8, imported functions 3, globals
  relabelled on exit 2, integrity 3, unnamed 4). WANILLA lists results top of stack first.
- **(d) The wasi-testsuite's C programs** with their files secret, stdout secret and public:
  8 of 14 run in both configurations (none of them loads a byte the host labelled secret); 6
  are rejected (`fdopendir-with-access`, `lseek`, `pread-with-access`, `pwrite-with-access`,
  `pwrite-with-append`, `stat-dev-ino`), because an `assert` on what a call reported about a
  secret file (data, a byte count, a position, an attribute) runs code under a secret pc that
  writes `__stack_pointer`, or returns a secret where a public result is declared. Before the
  boundary rule was complete (item 11), 10 ran and 4 were rejected.
- **(d) PolyBench** (ten kernels, MINI), data secret where `main` writes it
  (`store-default func main : H`, a new statement), loads of `main` secret: with the printing
  compiled out, all ten type and run with two policy lines and no further declaration, also
  under SecWasm's restrictions. Printing the results with `fprintf` is rejected in every
  kernel: `printf_core` branches on the value, and the functions it calls then run under a
  secret pc and write `__stack_pointer`.
- **(e) Lift shapes**: no program of (a)–(d) is accepted by the lift-free rules and rejected
  with `secwasm-restrictions` (`run.py`'s `lift_shape` is false throughout).

**9. The cost of the labels; the suites on the labelled build** (`BENCHMARKS.md`, "The cost of
the labels (2026-10-06, d2839ff)"; `bench/results/2026-10-06-d2839ff*.json`; driver
`bench/sweep-labels.sh`)
- **Caveat that governs every timing below:** the machine (bare-metal Ryzen 5 3600, Linux,
  GHC 9.12.2) was loaded by unrelated jobs during the sweeps (load average 3 to 32 on 12
  threads, recorded per sweep). The repetitions are interleaved, so the ratios are usable with
  their spread; the absolute times and ns per step are not quiet-machine figures. Allocation
  is deterministic and exact. A quiet re-run is open (`TODO.md`).
- **Without secrets, labelled build against the typed core of 0fcf4b4:** CPU-time ratio 1.05
  on 24 kernels (0.96 to 1.26; the block-entering kernels `labels-*` 1.09 to 1.26, `br-table`
  1.16, `call-indirect` 1.12), 1.03 on 10 programs at the small sizes, 0.98 on 11 at the
  medium sizes; the spread over repetitions is 1 to 2 % in the median and up to 13 %.
  Allocation: within +0.4 to +2.8 % on seven of the tripwire's nine workloads, −15.5 % on
  `fib` and −6.2 % on `call-indirect`.
- **With secrets in memory** (ten PolyBench kernels without printing, their data declared
  secret by two policy lines, against the same binary without a policy): 1.76 times the time
  at the small sizes and 1.69 at the medium sizes (per kernel 1.5 to 2.3), and 2.23 and 2.11
  times the allocation (1.8 to 2.9), 79 to 323 bytes more per step. The two time ratios come
  from sweeps under very different load and agree. The cost is the label map written by every
  secret store.
- **Typed against erased** (kernels): the erased machine (`bench/erased`) is the twin of the
  typed core without labels. The typed core of 0fcf4b4 is at 1.00 of it here (0.85 to 1.18),
  which is parity as in the paper's table (0.95 to 0.97 on the other machine); the labelled
  build is at 1.05 of it, the same 5 % as against the build before the labels.
- **Placement:** Hackage `wasm` 3.8 times slower than ours on the kernels; wabt 1.0.42 1.9
  times faster (ahead on all 24); on the programs at the medium sizes wasmi 73 times faster,
  Pulley 15, Winch 233 (8 programs), Cranelift 495 (4). **WAMR could not be run** on this
  machine (its release binary needs a newer libstdc++), and **wasm3 was not in the sweep**.
- **ns per machine step** of the labelled build on the programs: 33.8 (small) and 38.4
  (medium), geometric means, under load and on a slower processor than the paper's 16.1 and
  15.9; upper bounds only.
- **Suites** (at 720256f, same `src`/`app`/`test` as d2839ff): spec 23,306 passed, 0 failed,
  960 skipped over 70 scripts; wasi-testsuite 72 of 72. Skips by reason: text-format modules
  368, reference types 333, imports of tables, memories and globals 154, passive, declarative
  or other-table element segments 43, `table.*` instructions 21, harness imports 13, a shared
  table 5, and 23 the runner's output does not attribute.

## Phase 2

**10. Typed obligations on the main line** (delta 7)
- Index: `data DynamicCheck = NoDynamicCheck | BytesBelow SecLevel | CalleeWithin SecLevel`
  (`Syntax.TypesIFC`), the sixth index of `Instr`, after the two pc stacks:
  `Instr mod frame labels pcIn pcOut check stackIn stackOut`. `ILoad` and `ILoadN` have
  `'BytesBelow level`, `ICallIndirect` has `'CalleeWithin bound`, every other constructor
  `'NoDynamicCheck`. `Expr` has no such index; `(:.)` hides it.
- Evidence (`Runtime.Obligation`): `data CheckPassed (check :: DynamicCheck)` with
  `NothingToCheck :: CheckPassed 'NoDynamicCheck`,
  `BytesWereBelow :: CheckedRead level -> CheckPassed ('BytesBelow level)` and
  `CalleeWasWithin :: CheckedCallee bound ps rs fts -> CheckPassed ('CalleeWithin bound)`.
- The design is **"the value only with its evidence"**, for both checks, which differs from
  §7's listing (`LabelsOfRead b`, `FlowsInto b lm`, `enterCall`) and closes its stated gap:
  - `Runtime.MemInst.loadChecked :: MemInst m -> Sing level -> Int -> Int -> Either LoadFailure
    (CheckedRead level)` reads the word, joins its bytes' labels and compares the join with
    `level` (skipped when `level` is `High`). `CheckedRead` is abstract; `checkedWord` gives the
    word. The interpreter imports no other read of memory, so every word a load pushes comes
    out of a `CheckedRead` at some level, and the evidence must be one at the load's level.
    (`loadWordUnchecked` remains exported for `bench/erased`.)
  - `Runtime.TableInst.lookupChecked :: TableInst fts -> Word32 -> Sing ('LabelledFuncType lf
    ps rs) -> Either Trap (CheckedCallee lf ps rs fts)` compares the entry's labelled
    parameters and results with the expected ones and decides `lf ⊑ lt`. `CheckedCallee` is
    abstract and holds `FlowsInto lf lt` and `Elem ('LabelledFuncType lt ps rs) fts` at the
    same `lt`; `enteredCallee` gives the function. The interpreter imports no other lookup, so
    the callee an indirect call enters is the one that was checked.
  - Trusted code: `loadChecked` and `lookupChecked`. What still rests on inspection: that a
    load's case pushes the word of the read it presents (it could make a second checked read
    at another level and push that word), and that each check is the intended one.
- The machine: `stepInstr :: … -> Instr mod frame labels pcIn pcOut check stackIn stackOut -> …
  -> Either Trap (StepResult check mod res)`, with `Stepped :: !(CheckPassed check) -> !(Config
  mod res) -> StepResult check mod res`, `HostCall :: !(CheckPassed check) -> HostRequest mod res
  -> StepResult check mod res` (an indirect call may enter a host function) and `Done` at
  `'NoDynamicCheck`. The evidence is strict, so it cannot be left undefined. `step` returns
  `SomeStepResult`, which hides the index; the drivers `run` and `runFor` call `stepInstr`
  themselves and drop the evidence.
- "Must not compile": `test/obligations-must-not-compile.sh` (in `scripts/gate.sh`) type-checks
  `test/obligations/Good.hs` and requires GHC to reject four wrong steps: continuing with
  `NothingToCheck` ("Couldn't match type ‘NoDynamicCheck’ with ‘BytesBelow level’"); reading at
  another level ("Expected: Sing level, Actual: SSecLevel High"); forging the evidence (the
  constructor `CheckedRead` is not in scope); and continuing past an indirect call unchecked
  ("Couldn't match type ‘NoDynamicCheck’ with ‘CalleeWithin bound’"). The paper's third wrong
  version (`LowFlowsAnywhere`) has no counterpart, since the evidence holds no flow proof.
- Cost, on this machine (Ryzen 5 3600, native Linux), `bench/tripwire.py`'s nine workloads,
  against the same code without the index (9f53c0a with `enterCall` inlined, as it is now):
  allocation +0.7 % to +2.0 % on eight and +4.4 % on `call-indirect` (0.2 to 2.7 bytes per
  step); CPU time ratio 0.97 as a geometric mean over seven workloads (five interleaved runs
  each, medians; individual ratios 0.90 to 1.03), which is parity. Inlining `enterCall`, done
  in the same commit, lowers allocation against 9f53c0a itself by 16 % on `fib` and 9 % on
  `call-indirect`. Passing the evidence as an argument of `stepped`, `stepBin` and `stepUn`
  matters: with the helpers fixed at `'NoDynamicCheck`, allocation rose by 9 to 74 %.

**11. The complete WASI boundary rule** (delta 2)
- Taken from memory, checked against the descriptor's level (`InformationFlowViolation` if a
  byte is more secret): the data of `fd_write`/`fd_pwrite` (`gather`, as before), the iovec
  arrays of `fd_read`, `fd_pread`, `fd_write`, `fd_pwrite` (`peekIovecs`), and the contents of
  `path_symlink` against the directory's level. Paths of every `path_*` call (`peekPath`) and
  the subscriptions of `poll_oneoff` must be public.
- Stored, at the descriptor's level: the data and the byte counts of reads and writes
  (`pokeWord32At`), the positions of `fd_seek` and `fd_tell`, the `filestat` of
  `fd_filestat_get` and `path_filestat_get` (the directory's level), the entries and the size
  of `fd_readdir`, the target of `path_readlink`.
- Public: arguments, environment, clocks, random bytes, `prestat` data, the new descriptor of
  `path_open`, poll events, and `fdstat` (a descriptor's type, flags and rights, which belong to
  the descriptor table).
- Error codes are unchanged, and are as the host reports them: they depend on the descriptor
  table, the operands, and the names in a directory (public in the model of `def:swpp`), and
  also on whether an operation on a secret file fails, which the model does not cover. The
  paper should keep that limit stated.
- Sockets still return `ENOTSOCK`, `proc_raise` `ENOSYS`. (Sockets: served since 2026-10-12, see
  "WASI sockets" below.)
- Unit tests: a secret iovec array to a public descriptor traps; the count of a read from a
  secret descriptor is secret; a secret path traps. Spec suite and wasi-testsuite unchanged.

**Local splitting, checked differentially** (3614d3c): the policy statement
`no-local-splitting` types the locals as written; a property runs generated modules both ways
on the same inputs and requires the same result, public global and memory (2,000 cases).

**Merging split locals; the allocation reference** (95a0f15)
- Splitting every local into its webs made frames several times larger, and a write to a local
  copies the frame: at 9f53c0a CoreMark allocated 73 % more than on 15 September, 2mm 36 % more,
  seidel-2d 10 % more, all from d9cb140 (the splitting). Now, once inference has settled the
  labels, the webs of one local at the same label share a local again (`mergeWebs` in
  `Validation.LocalWebs`), and the module is elaborated once more under those labels; a split
  local needs at most one slot per label. A module whose policy names no secret is not split.
- For the paper's description of splitting: any grouping of the webs of one local preserves
  behaviour (the definition a use read last is in the use's own web), so the merge needs no
  argument beyond the one for the splitting. The differential property runs each generated
  module as written, split, and split and merged under alternating levels (2,000 cases).
- The counts of secret locals in `casestudies/results/` from this commit on are counts of
  merged locals, so they are lower than in the earlier files (the password checker: 2, was 6).
- `bench/allocation.txt` is re-recorded at 95a0f15 for the labelled build without a policy:
  against 15 September, CoreMark +1.2 %, 2mm +0.4 %, seidel-2d +0.4 %, `memory-random` +2.8 %
  (the load evidence), `fib` −15.5 % and `call-indirect` −6.2 % (`enterCall` inlined); the full
  table is in `BENCHMARKS.md`, "Allocation at the labelled build". With a secret in the policy,
  CoreMark is at +2.7 % in all, and validation takes 0.09 s where it takes 0.03 s without one.

## Preserved globals (Daniel's decision of 2026-10-05; not in PLAN.md)

- **Policy:** `preserved global N`. The global must be mutable and public; it gets the
  mutability `Preserved` in the module's shape (`Syntax.Types.Mutability`).
- **Static rule:** `IGlobalSetPreserved :: FlowsInto lv pc -> Elem ('GlobalType 'Preserved
  (t ':~ 'Low)) … -> Instr …`: the pc premise of `global.set` is dropped and the value may be as
  secret as the pc (under a public pc this is the ordinary rule). Reads are unchanged.
- **Run-time rule:** a block, loop, conditional or call in which the pc may end up secret must
  leave every preserved global as it found it. Where it has to is a witness: `IBlock`, `ILoop`
  and `IIf` carry `Restores pcEnd pcsAfter gs` (`PcDoesNotDrop (FlowsInto pcEnd pcAfter)` |
  `PreservedRestored (PreservedOf gs)`), and `Function` carries `ReturnsWith pcOut gs`
  (`ReturnsUnderPublicPc` | `RestoresOnReturn (PreservedOf gs)`); `PreservedOf gs` enumerates
  every global of the module, so none can be left out. The machine records the values at the
  construct's start (`Runtime.Stack.recordPreserved`) and puts an `IRequireRestored` in front
  of what follows it; a mismatch traps with `GlobalNotRestored`. The invoked function is held
  to the same as a callee. The reference for a block is the value at its entry, and for a
  call the value at the call, which is what makes an early return after a secret check pass.
- **Not a typed obligation:** `IRequireRestored` has the check `NoDynamicCheck`; that the
  machine inserts it is by inspection of three clauses of `stepInstr` and `enterCall`.
- **Cost:** without a `preserved` statement nothing is recorded or compared, and the
  allocation tripwire is at the reference on all nine workloads.
- **Tests:** six unit tests (a helper under a secret pc; a conditional that does not restore;
  an early return, restored and not; the invoked function; the ordinary rule under a public
  pc; policy errors). The two-run noninterference generator writes a preserved global, raw
  and bracketed: 100,000 cases, no counterexample (38 % accepted and finished, 2 % trapped,
  59 % rejected); a mutant whose comparison always succeeds fails after 5,057 cases, so the
  suite now runs 10,000.
- **Case studies:** `casestudies/frames/` (a non-leaf helper called if a secret byte is odd)
  runs with `preserved global 0` and is rejected without it, at the helper's prologue. A leaf
  function does not move the pointer, so only non-leaf functions are concerned. PolyBench with
  `fprintf` gets past every prologue and is rejected later, at the indirect call through
  which `vfprintf` writes its buffer out (function 63, instruction 126, `call_indirect`): a
  host call under a secret pc.
- **For the paper:** Daniel's view is that this can be an assumption of the theorem ("a module
  restores a preserved global before the end of every secret region"), explicit in the policy
  and checked by the implementation; the paper track decides.

## Findings that bear on the paper's claims

1. **The shadow-stack pointer.** `__stack_pointer` is a public global that every non-leaf C
   function writes in its prologue and restores in its epilogue. SecWasm's rules forbid the
   write under a secret pc, so no such function can be called in a secret context. With the
   global declared preserved (above) this is lifted. What then still rejects `printf` of a
   secret and `assert` on a secret is the host call under a secret pc (TODO.md).
2. **Branches on secrets before output.** The compiler moves output into the blocks of earlier
   branches; typable programs are written branch-free where they handle secrets (constant-time
   style). The password checker shows both versions.
3. **Local reuse** (item 6 above), fixed by splitting.
4. **Error checks after reads** (§6.7 "Statuses and errors"). Since the boundary rule is
   complete (item 11), the byte count of a read from a secret file is secret, and the
   branch-free password checker is no longer typable as written: `if (count < 0) return 1;`
   raises the pc of the rest of `main`, and the next call, `open`, is rejected at its write of
   `__stack_pointer`. Under the four-line policy the run traps in libc's `read`, at the load of
   the count (`load 12 3`); with that load declared the module is rejected statically. The
   earlier result (it ran; the leaks trapped at the log) is from before the rule was complete
   (`casestudies/results/2026-09-30-624a05a.json`) and should not be cited for the final system.
   **Resolved for the checker without giving up the length (af3f83a):** `password.c` now calls
   `__wasi_fd_read` and `__wasi_fd_write` directly for its secret input and output. The host
   reports the status (public) and the byte count (secret) as two values, so checking the
   status is a public branch; libc's `read` merges them. It runs under the four-line policy and
   its leaking variants trap at the log. The version through libc is `password-libc.c`, with
   its rejection. Daniel's position (2026-10-05): the length of a secret is sensitive, so a
   policy does not get a way to declare it public.

## Not done yet

- Item 9, remainder: the timing sweeps again on a quiet machine, with wasm3 and, if a
  runnable build is found, WAMR (`PRE=… ./bench/sweep-labels.sh`).
- Items 12–14: Lean (a first step, see "Lean" below); the rest of WebAssembly 3.0 (done but for typed function
  references and garbage collection, see "Where coverage stands"); WASI sockets (done).

## The 3.0 suite (item 13, first step, 2026-10-08)

No feature was added. The spec suite is now the WebAssembly 3.0 release (submodule at b464a4c,
2026-09-15; it was a commit of 2021), all 257 scripts at its top level are run, and a skipped
assertion is counted under the features its module uses, which `wasm-tools validate` reports.

- **Result:** 27,891 assertions passed, 0 failed, 37,311 skipped; the same with SecWasm's
  restrictions on. 38 scripts run with nothing skipped, 154 with nothing passed (57 of them
  for vector instructions).
- **Supported subset**, as `wasm-tools` names it: WebAssembly 1.0 with mutable-global,
  sign-extension, saturating-float-to-int, multi-value and the memory half of bulk-memory.
  That is less than WebAssembly 2.0, which also has reference types, the table instructions
  and vector instructions.
- **Skips by feature:** the table in `TODO.md`. Two thirds are vector instructions.
- **The counts changed meaning.** An assertion that a module is malformed or invalid now counts
  as passed only if the module stays within the subset; before, rejecting it for any reason
  counted. The old 23,306 and 960 are not comparable with the new numbers.
- **One decoder change:** an alignment field of 64 or more in a memory access is now rejected
  when decoding (64 to 127 announce a memory index, which is unsupported; 128 and above are
  malformed), where it used to fail validation as a misaligned access.
- **Tools:** the runner needs `wasm-tools` (1.261); wabt's `wast2json` cannot parse 44 of the
  257 scripts.

## Reference types and tables (item 13, second step, 2026-10-08)

The interpreter now covers WebAssembly 2.0 without vector instructions and without imports of
tables, memories and globals (only functions are imported): `funcref` and
`externref` as value types, `ref.null`, `ref.is_null`, `ref.func`, typed `select` on
references, several tables per module, `table.get`, `table.set`, `table.size`, `table.grow`,
`table.fill`, `table.copy`, `table.init`, `elem.drop`, passive and declarative element
segments, segments given as expressions, and `call_indirect` through any table.

- **Spec suite:** 30,693 assertions passed, 0 failed, 34,509 skipped (27,891 and 37,311
  before), the same with SecWasm's restrictions on; 44 scripts run with nothing skipped. The
  skips by feature are in `TODO.md`. `table_copy.wast` and `table_init.wast` still skip 2,616
  assertions, because their modules import functions from another module of the script
  (linking, not done).
- **The rules** (ours: SecWasm has no reference types and no instruction that writes a table).
  A table has one static level `lt` from the policy (`table N : H`, public otherwise), as
  Section 5's "Beyond the Calculus" and the "Tables and references" row of Appendix A say. The
  typed constructors are in `src/Syntax/Instructions.hs`:
  - `table.get`: the result is labelled pc ⊔ index ⊔ lt.
  - `table.set`: pc ⊔ index ⊔ value ⊑ lt.
  - `table.size`: the result is labelled pc ⊔ lt. The size of a table is part of its contents.
  - `table.grow`: pc ⊔ count ⊔ value ⊑ lt, and the result is labelled pc ⊔ lt.
  - `table.fill`: pc ⊔ count ⊔ value ⊔ index ⊑ lt.
  - `table.copy`: pc ⊔ the three operands ⊔ the source table's level ⊑ the destination's.
  - `table.init`: pc ⊔ the three operands ⊑ lt. An element segment is public.
  - `elem.drop`: no premise, like `data.drop`: whether a later `table.init` traps is not an
    output.
  - `ref.null` and `ref.func` are constants, typed like `const`; `ref.is_null` is as secret as
    its operand; `select` on references is the rule of `select`.
  - `call_indirect`: pc ⊔ index ⊔ lt ⊑ the expected bound (lt is new). The run-time check on
    the callee is unchanged.
  The paper states the static level and the two call rules. The rules for `table.size`,
  `table.grow`, `table.fill`, `table.copy`, `table.init` and `elem.drop` are this
  implementation's reading of "like a global" and are for the paper track to confirm.
- **Not in the calculus, not proved.** No dynamic check was added: tables have no run-time
  labels.
- **Inference:** a function whose reference the module takes (in an element segment or a
  global's initial value) keeps its declared type, like an exported one.
- **Tests:** eight unit examples (`test/Spec.hs`, "references and tables"); the generator of
  the noninterference property now writes, grows, copies, reads and calls through a public and
  a secret table, and compares the public table of the two runs. 100,000 cases, no
  counterexample (30 % accepted and finished, 6 % accepted with a trap, 64 % rejected). A
  mutant whose `table.get` forgets the table's level fails after 7,470 cases; the first
  version of the generator did not find it in 30,000, until the entry written was made to
  depend on the parity of the secret.
- **Representation:** a reference is one word (null, or an index); `TODO.md` records what the
  types do not rule out there.
- **Cost:** the allocation tripwire is unchanged (`bench/tripwire.py`); no timing was run.

## Functions imported from other modules (item 13, third step, 2026-10-09)

- **What:** a module may import functions of whoever embeds it (`Runtime.Instantiate.instantiateWith`
  takes their types). A call to one suspends the machine with the arguments
  (`ForeignRequest`), and the embedder answers with the results (`Runtime.Module.foreignCall`,
  `answerForeign`), which are checked against the declared result types. The spec runner uses
  this to link the modules of a script: it keeps every instance, serves a call to a function
  of a registered module by running that function in its own instance, and serves the
  printing functions of the suite's `spectest` module by returning nothing.
- **Spec suite:** 33,439 passed, 0 failed, 31,763 skipped (30,693 and 34,509 before), the same
  with SecWasm's restrictions on. `table_copy.wast` and `table_init.wast` now run.
- **Information flow:** such an import is typed like a host function: the policy must give it
  the bound `Low` and public parameters (checked when the policy is assembled and again at
  linking), and may label its results. The policy of the module that is called plays no part:
  from the importer's side it is the host. Two modules with two policies are not composed.
- **Not done:** imports of tables, memories and globals. The accurate coverage claim is
  "WebAssembly 2.0 without vector instructions and without imports of tables, memories and
  globals"; 358 assertions of the suite still need them or depend on state shared between
  modules.

## GHC's error for SecWasm's printed `br_table` rule (plan, new item of 2026-10-03)

`test/obligations/WrongBrTablePrintedRule.hs` writes the table of the first finding
(`br_table 0 3` on a secret index, inside four blocks without results) the way the printed
rule types it: the raise covers as many labels as the table has targets, two, and the target
at depth 3 lies outside it. `GoodBrTable.hs` is the same table with the raise down to its
deepest target. `test/obligations-must-not-compile.sh` (in the gate) checks that the first is
rejected and the second accepted.

```haskell
table :: Instr m f '[ '[], '[], '[], '[]] ('Low ': 'Low ': 'Low ': 'Low ': pcs)
                   ('High ': 'High ': 'Low ': 'Low ': pcs) 'NoDynamicCheck (('I32 ':~ 'High) ': s) anyOut
table = IBrTable NothingCarried NoValuesFlow ANil (ReachesThere ReachesHere) [Here] (There (There (There Here)))
```

GHC 9.12.2 answers:

```
WrongBrTablePrintedRule.hs:13:100: error: [GHC-83865]
    • Couldn't match type: y0 : '[] : xs10
                     with: '[]
      Expected: Elem '[] '[]
        Actual: Elem '[] (y0 : '[] : xs10)
    • In the first argument of ‘There’, namely ‘(There Here)’
      In the first argument of ‘There’, namely ‘(There (There Here))’
      In the sixth argument of ‘IBrTable’, namely
        ‘(There (There (There Here)))’
```

That is: the default target is a position in the list of labels the table raises (`reach`,
here two labels), and position 3 walks past its end.

- **How the finding was found: not through this error.** The repository's history has no
  transcription of the printed rule for GHC to reject. The first typed `IBrTable` (e705545,
  20 September) tracked no pc at all; the next raised every entry; `TableReach`, which makes
  the mismatch a type error, came with ea6e058 on 30 September, after the paper's corrected
  example (25 September). So the text can say that the printed rule cannot be written with
  the witness, and show the error, but not that GHC caught the bug.

## What the toolchains emit by default (item 13a, 2026-10-12)

For `wasm32-wasip1`, clang 23.1.0 of wasi-sdk 34 (`clang -dM -E`) and rustc 1.99.0
(`rustc --print cfg`) enable the same features by default: mutable globals, sign extension,
saturating conversions, multiple values, bulk memory and reference types. Neither enables
vector instructions, tail calls, exceptions, multiple or 64-bit memories, extended constant
expressions or garbage collection. Every feature the two toolchains use by default is
implemented since e87e76a.

## Several memories per module (item 13, 2026-10-12)

- **What:** a module may declare any number of memories; every memory instruction, and an
  active data segment, names the one it works on, and `memory.copy` may copy from one to
  another. The typed instructions take a reference to their memory (`Validation.Ref.MemoryRef`)
  where they used to ask that the module has one.
- **Spec suite:** 34,141 passed, 0 failed, 31,061 skipped (33,439 and 31,763 before), the same
  with SecWasm's restrictions on; 72 scripts run with nothing skipped.
- **Information flow:** as the paper's "Beyond the Calculus" says, each memory has its own
  byte labels; the rules of loads, stores and the bulk instructions are unchanged, and a byte
  copied from one memory to another keeps its label, joined with the pc and the operands'. A
  policy's `region` lines are of memory 0. Two unit examples (`test/Spec.hs`, "module-level
  validation").
- **Cost:** the allocation tripwire improved on the workloads that use memory (2 to 3 % less
  than the reference): the word a load reads is no longer returned in an allocated `Just`.
  The saved binary of the timing sweep (505ee9c) is from before this change.

## 64-bit memories and tables (item 13, 2026-10-12)

- **What:** a memory or a table may have 64-bit addresses (the 3.0 feature the spec calls
  memory64, which covers tables too). The operands that address it are then `i64`: the address
  of a load or store, the index of a table instruction or of `call_indirect`, the counts of
  the bulk instructions, the result of `memory.size`, `table.size` and the two `grow`s, and
  the constant offset of a data or element segment. A copy between a 32-bit and a 64-bit
  memory or table takes each address at its own type. In the typed AST the operand's type is
  computed from the memory's or the table's shape (`AddrVal at`).
- **Spec suite:** 36,367 passed, 0 failed, 28,835 skipped (34,141 and 31,061 before), the same
  with SecWasm's restrictions on; 93 scripts run with nothing skipped.
- **Information flow:** no new rule. An address is an operand like before, whatever its width.
- **Limit of the implementation:** a 64-bit memory or table holds at most 2^32 - 1 pages or
  entries; `TODO.md` says what happens beyond.
- **Cost:** the allocation tripwire is unchanged by this step.

## Tail calls (item 13, 2026-10-12)

- **What:** `return_call` and `return_call_indirect`. The machine replaces the caller's frame
  by the callee's, so a chain of tail calls runs at constant depth (a unit example runs
  100,000 of them, ten times the bound on nested calls).
- **Rule, as the paper has it:** a tail call is typed as the call followed by a `return`. The
  typed constructors (`IReturnCall`, `IReturnCallIndirect`) carry the premises of the call
  (pc ⊑ the callee's bound, the arguments flow into its parameters; for the indirect one, the
  index and the table join the pc, and the run-time check on the callee is the usual one) and
  those of the return (pc ⊑ the levels of the function's results, and the callee's results
  flow into them). After it the pc is raised as after a `return`.
- **Spec suite:** 36,401 passed, 0 failed, 28,801 skipped. The gain is small (34 assertions):
  the main modules of `return_call.wast` and `return_call_indirect.wast` each contain one
  function whose type has a typed function reference, which is not supported, so they are
  skipped whole. Five unit examples cover the rule and the constant depth (`test/Spec.hs`,
  "tail calls").

## Imported state and constant expressions (item 13, 2026-10-12)

- **Imports of globals, memories and tables, by value.** An embedder
  (`Runtime.Instantiate.Embedder`) provides, by the two names of an import: a global's value
  and whether it may be written, or the type of a memory or a table. The module gets the value,
  or a new empty memory or table of that type, and owns it: nothing it writes reaches the
  embedder. The provided type must match the import's as the spec says (the global's type and
  mutability; the limits of a memory or table within the declared ones). For an immutable
  global this is the spec's meaning exactly. For the rest it is the spec's meaning as long as
  nobody else sees the same object, which is why **state shared between two modules is still
  not supported**: the spec runner provides the suite's `spectest` module and a registered
  module's immutable globals, and skips 301 assertions that need a registered module's memory,
  table or mutable global.
- **Constant expressions.** The initial value of a global and the offset of a data or element
  segment may read an imported immutable global and add, subtract and multiply integers
  (WebAssembly 3.0's extended constant expressions); an element may be the value of an
  imported global. They are kept as expressions (`Syntax.Globals.ConstExpr`) and evaluated when
  the module is instantiated, since only then is the imported value known.
- **Information flow.** An imported global has the level the policy declares for its index
  (`global N : H`), like any global; the embedder is trusted to give a value of that level, as
  it is for the results of a function it provides. New static checks, at validation: what a
  global's initialiser reads must flow into the global's level; the offset of a data or element
  segment, and an element, must read nothing secret (where the bytes of a segment land is
  public). An imported memory starts public, an imported table has its declared level. Five
  unit examples (`test/Spec.hs`, "state an embedder provides").
- **Spec suite:** 36,726 passed, 0 failed, 28,476 skipped (36,401 and 28,801 before); 98
  scripts run with nothing skipped.

## Vector instructions (item 13, 2026-10-12)

- **What:** the `v128` value type and all the vector instructions of WebAssembly 2.0
  (fixed-width SIMD): constants, lane operations, the integer and floating-point operations of
  every shape, comparisons, shifts, conversions, and the loads and stores of whole vectors and
  of single lanes. With them every instruction of WebAssembly 2.0 is implemented.
- **Rules:** none new. An operation is typed like a numeric one (the result is as secret as
  the operands and the pc); a vector load or store is typed like a load or store, declares a
  level, counts as a memory access for the policy's `load F N`, and is checked at run time like
  every load, each half of a whole vector on its own (`BothWereBelow`).
- **How:** the operations that do not touch memory are one family indexed by operand and
  result types (`Syntax.Vector.VectorOp`), so the typed instruction has one constructor per
  number of operands (`IVector0` to `IVector3`); their meaning is given lane by lane in
  `Runtime/Vector.hs`. A vector local takes two words of a frame.
- **Spec suite:** 62,081 passed, 0 failed, 3,121 skipped (36,726 and 28,476 before), the same
  with SecWasm's restrictions on; all 59 scripts for vectors pass, and 130 of the 257 scripts
  run with nothing skipped. Four unit examples (`test/Spec.hs`, "vectors").
- **Cost:** the allocation tripwire is unchanged; no workload of the benchmarks uses vectors.

## Exceptions (item 13c, 2026-10-12)

- **What:** exception tags, `throw`, `throw_ref`, `try_table` with its four kinds of clause,
  and the `exnref` type (WebAssembly 3.0's exceptions; the earlier `try`/`catch` instructions
  are not in 3.0).
- **The rule, as decided on 2026-09-30 and as section 5 states it:** `throw` requires a public
  pc and public operands (`IThrow` is typed at pc `Low`, with a witness that the tag's values
  are public); `throw_ref` requires a public pc and a public reference. No function type has a
  label for exceptional exits: a function whose body may throw has bound `Low`.
- **One thing the text leaves open, decided here:** a `try_table` is typed only under a public
  pc (`ITryTable` is at pc `Low`). Its clauses are then branches taken under a public pc, with
  the public values of the exception, so they raise nothing. Under a secret pc no exception can
  arrive anyway (nothing reachable from there may throw), so the clauses would be dead; typing
  them there would need the branch rule's raise for no gain. A `try_table` under a secret pc
  is rejected (`IllegalFlow "try_table" High Low`). **For the paper track to confirm.**
- **Run time:** an exception unwinds the control stack, through calls, to the nearest clause
  that catches it; one that nothing catches ends the run (`UncaughtException`).
- **Preserved globals:** an exception skips no comparison that the rule for preserved globals
  needs. A construct compares them where the pc drops on the way out of it. A `throw` is typed
  at a public pc, the pc of an enclosing construct is never above that of what it encloses,
  and a caller's pc flows into the bound of its callee, which is public here. So every
  construct and every call the exception leaves is left under a public pc, and whatever ran
  under a secret pc before the throw had ended, and was compared, by then. The clause's branch
  goes through the same code as a `br`, so the construct it lands behind compares as usual.
  This is my argument, not a proof; the paper track should check it against section 6.6.
- **Spec suite:** 62,137 passed, 0 failed, 3,065 skipped (62,081 and 3,121 before);
  `throw.wast` and `throw_ref.wast` pass in full. (The main module of `try_table.wast` imports
  a tag; it passes since tags are imported, see "State shared between modules".) Four unit
  examples (`test/Spec.hs`, "exceptions").

## Lean: noninterference on a core with control flow, calls and memory (item 12, 2026-10-12)

- **Where:** `lean/` (Lean 4.35.0, no dependencies; `cd lean && lake build`). 2,015 lines in
  five files; `lean/README.md` states what is proved and what differs from the paper.
- **What is proved** (`WasmIfc.tini`, from `WasmIfc.ni`): termination-insensitive
  noninterference for a function of a well-typed module, under the lift-free rules, on a core
  with blocks, loops and conditionals (with parameters and results), `br`, `br_if`, the
  repaired `br_table`, direct and indirect calls (recursion included), `load` and `store` on a
  memory whose cells
  carry a level, with the run-time check of loads, local and global variables and arithmetic. Also `WasmIfc.rise`, the paper's `lem:rise`. **No `sorry`; the theorems
  depend on `propext`, `Classical.choice` and `Quot.sound` only** (`#print axioms`).
- **Against the plan's steps (a) to (f):** (a) in part. The rules are the W-rules themselves,
  so for this core there is no erasure and no inclusion to prove, and the theorem is the main
  theorem's statement for the typed program. Not covered: `return` (it is a
  branch to the function's label), `local.tee`, `memory.grow`, a bounded memory of bytes, more
  than one value type, more than two levels, bulk memory, WASI, the features of 3.0, and
  the correspondence with SecWasm's flat-stack semantics (the Lean semantics evaluates a
  block's body on the block's parameters alone). (b) to (f): not done.
- **The lift-free invariant holds on this core**, which is what step (a) was to find out.
  Two observations for appendix B.4:
  1. With a block-local semantics the relation "up to abandoned entries" is not needed. After
     two runs diverge, the proof relates their states and says nothing of their stacks, until
     they meet at the end of a block whose result type is all secret.
  2. **The proof uses Property (E) in two places:** where two runs took different arms of a
     conditional on a secret and both reach its end, and where one run iterates a loop longer
     than the other. Without (E) a block with parameters under a secret pc may pass a public
     parameter through as a public result, and the proof would have to track which values
     were moved and which computed (the `tk` box of step 7). With (E) it does not.
  3. **The case of `call` needs neither the lift nor well-formed function types.** The
     arguments keep their own labels below the parameters', and the premise that a function's
     results be at least its bound is not used: where two runs of a callee diverge, one of them
     returns early under a secret pc, and the rule for the branch makes the result type secret.
     **`call_indirect` on a secret index does need it**: two different functions run, and
     their results agree only because the expected type's results are at least its bound,
     which the pc and the index have raised. The Lean rule for the indirect call carries that
     premise. The implementation checks it in the policy stage for every function type
     (`PolicyResultsBelowBound`), as the paper says.
- **Toolchain:** elan and Lean are installed under `~/.elan` (3 GB, user space).

## WASI sockets (item 14, 2026-10-12)

- **What:** the four socket calls of WASI Preview 1 (`sock_accept`, `sock_recv`, `sock_send`,
  `sock_shutdown`) on sockets the host listens on. `wasm-ifc run --listen HOST:PORT` gives the
  module a listening TCP socket as the descriptor after the preopened directories (the
  interface has no call that makes a socket, so this is all it allows). `fd_read`, `fd_write`,
  `fd_close`, `fd_fdstat_get`, `fd_fdstat_set_flags` (non-blocking) and `poll_oneoff` work on
  them. New dependency: the `network` package.
- **The rule:** the policy line `listen HOST:PORT : H` gives a listening socket a level, like
  `preopen` gives one to a directory, and **a connection inherits the level of the socket it
  was accepted from**. Then the boundary rule of item 11 applies unchanged: what `sock_send`
  takes from memory (the data and the iovec array) must flow into the connection's level; what
  `sock_recv` stores (the data, the count, the flags) carries it. The new descriptor of
  `sock_accept` is public, like that of `path_open`, and so are the error codes.
- **One addition to item 11's rule, for the paper track to confirm:** the events of
  `poll_oneoff` and their count were public, since only the subscriptions decided them. With a
  subscription to read from a socket they say whether the socket was ready, so they are now
  stored at the join of the levels of the sockets subscribed to (public if there is none).
- **Not covered, as before:** when a peer connects or sends is visible in how long a call
  waits, and in whether a non-blocking call reports `EAGAIN`. Both are outside a
  termination-insensitive statement; the second is an instance of "error codes are as the host
  reports them" (item 11).
- **Not provided:** `MSG_PEEK` and `MSG_WAITALL` of `sock_recv` (`ENOTSUP`); UDP; outgoing
  connections (Preview 1 has no `connect`).
- **Evidence:** six unit examples (`test/Spec.hs`, "WASI imports": a connection is served; it
  inherits its socket's level, so its data goes back to it and not to stdout; the count of a
  receive is secret; calls on what is no connection fail, and a non-blocking accept does not
  wait; a poll on a secret socket reports at its level; the policy line parses). A C echo
  server built with wasi-sdk 34 runs through libc's `poll`, `accept`, `recv`, `send` and
  `shutdown` (checked by hand, not in the gate). **Case study `casestudies/service/`:** the
  password checker as a service on a secret socket, 2 policy lines; it runs for a weak and a
  strong password, both leaking variants trap at the report, and with the socket public the
  leaking variant runs (`./casestudies/run.py service`, 5 of 5 as expected; see
  `casestudies/README.md` for the two functions the coarse `load-default func` forces on the
  program).
- A run now closes what the host still holds open when it ends (files, sockets).

## A load no longer boxes its word (2026-10-12)

- `Runtime.MemInst.loadChecked` now takes what to do with a failure and with the word, where
  it returned an `Either`. The word then reaches the code after the load in one place and
  unboxed; before, GHC shared that code between the ways of reading a word and passed the
  word boxed, 16 bytes on every load (32 once exceptions had made the interpreter larger).
  The evidence a load presents is unchanged: `CheckedRead` is still built in that function
  only, and the two obligation tests that use it are adapted.
- **Cost:** allocation on the tripwire's memory workloads, against the reference of 95a0f15:
  `memory-random` −7.3 %, `coremark-100` −6.9 %, `pb-2mm-small` −5.3 %, `pb-seidel-2d-small`
  −4.9 %; the five others unchanged. No timing was run (the machine is loaded).
- The frozen binaries for the clean benchmark are of db01cdc, before this change. If the
  benchmark has not started when this is read, freeze the binaries again.

## State shared between modules (2026-10-12)

- **What:** `Runtime.Link`, a world of instances. A module imports functions, memories, tables
  and globals from the modules registered in it, and a memory, a table or a writable global
  that two modules both see is one object. This removes the restriction that cut across
  versions ("imports are by value").
- **How, without a shared mutable store:** the interpreter is still pure and an instance still
  owns its state. Only one instance runs at a time, and control passes between instances at
  two points, a call out of a module and its return. An instance takes what it imports from
  the instance that defines it when control comes to it, and gives it back when control
  leaves, by a call, a return or a trap. A memory and a table are persistent structures, so
  this costs nothing. In C terms: no two modules hold a pointer to the same buffer; the buffer
  is passed along with the control, and nobody else can run in between.
- **What had to change for it:**
  - A reference to a function names its instance (the high bits of the word), so a shared
    table holds functions of several modules. An indirect call through an entry of another
    instance leaves the module like a call of an import, and the linker compares the
    function's type with the expected one (`ElsewhereCallee`, `CalleeWasElsewhere`).
  - An instance keeps one state for all its activations (`Runtime.Module.Instance`), so a
    module that is called back while a call out of it waits resumes from what the nested
    activation left.
  - A trap keeps what was written before it (`runKeeping`), and so does an active segment
    that does not fit: the segments before it stay written, in the importing module's own
    and in the imported memories and tables, as the specification has it. Element segments
    are now placed before data segments, the specification's order.
  - The suite's `spectest` module is an ordinary module of the script's world.
- **Information flow at the boundary:**
  - Calls between modules carry public values: an import is typed at public parameters and a
    public bound (as before), and a function whose results its own policy declares secret is
    not given to other modules, by name or by reference.
  - A global is imported at the level it has where it is defined (exactly, if it can be
    written; at that level or above, if not), and a table at exactly its level. Before, an
    imported global took whatever level the importer's policy gave it, which could lower a
    secret one; `ImportLevelMismatch` now refuses that.
  - The bytes of a shared memory keep their levels, so a secret byte one module stored traps
    a public load in another.
  **For the paper track:** none of this is in section 5 or 6. The rule is short ("an import
  has the level of what is imported; calls between modules are public").
- **One limit, refused by name:** a module that imports the same memory, table or writable
  global twice is not linked (`ImportedTwice`): inside one instance two indices are two
  objects. 10 assertions.
- **Exceptions across modules (added 2026-10-12, later the same day):** a tag is imported and
  exported, and has one name among all the instances (`tagNames`); a module's own tag is named
  after its instance, and an imported one has the name of the tag it imports. An exception is
  its tag's name with the values it carries at their types. One that leaves a function another
  module called is thrown again in the caller, where the call was (`throwInto`), so a clause
  for the tag, or for all exceptions, catches it there. Nothing changes in the rule: a throw
  and a catch are under a public pc with public values, and a call between modules is under a
  public pc. `try_table.wast` now passes in full (65 assertions).
- **Spec suite:** 62,399 passed, 0 failed, 2,803 skipped (62,137 and 3,065 before; 62,476 and
  2,726 once the relaxed vector instructions were in). Every skip
  for an unsupported import and for state that may depend on an unlinked module is gone (292),
  and so are the three for a start function that calls an import. Seven unit examples
  (`test/Spec.hs`, "modules linked in a world").

## Typed function references (2026-10-12)

- **What:** the reference types `(ref null? ht)` for the heap types `func`, `extern`, `exn`,
  their bottoms and the module's function types; `call_ref`, `return_call_ref`,
  `ref.as_non_null`, `br_on_null`, `br_on_non_null`; a `ref.func` at its function's type; the
  rule that a local without a default value is written before it is read; the matching of
  imports by these types.
- **How, and what it means for the paper's claim about types.** Two layers:
  1. **The typed program knows a reference by its kind alone**, as before: `funcref`,
     `externref`, `exnref`. A reference to a function type is a `funcref` there. The typed
     instruction set gains a call and a tail call through a reference (`ICallRef`,
     `IReturnCallRef`: the indirect calls without the table, with the same run-time check of
     the callee against the expected type, and a trap on null), `IRefAsNonNull` (a trap on
     null) and `IDuplicate`. The two branches on null are elaborated as what they abbreviate,
     a null test and a conditional with a branch.
  2. **What a module writes beyond the kind is checked by `Validation.References`**, a
     conventional validator (a stack of types, a stack of frames) over the types as written,
     with subtyping, the equivalence of function types and the initialisation of locals. It
     runs before elaboration and decides nothing about security.
  So nullability and the function type behind a reference are **not in the types of the typed
  program**; they are run-time checks there, as for `call_indirect`. A module the validator
  wrongly accepted would trap where the specification promises it cannot; no illegal state is
  representable. The paper's claim "intrinsically typed" should carry this one qualification.
- **The information-flow rule:** `call_ref` is `call_indirect` without the table: the level of
  the reference joins the pc in the premise on the callee's bound, the expected labelled type
  is the policy's for the type index, and the machine compares the callee's bound with it.
  `ref.as_non_null` is typed like a division: it may trap on a secret, and the rule does not
  restrict that. `br_on_null` and `br_on_non_null` get the rules of the test and the
  conditional they are elaborated as, which is sound and slightly coarser than a rule of their
  own would be: the values they leave are at least as secret as the reference tested.
  **For the paper track:** none of this is in section 6.6.
- A table may be declared with an initial value for its entries, which a table of references
  that cannot be null needs: a constant expression of the entries' type, which reads nothing
  more secret than the table.
- **Spec suite:** 62,990 passed, 0 failed, 2,212 skipped (62,476 and 2,726 before): every skip
  for typed function references is gone.
- **Cost:** the allocation tripwire is at the reference. (Commit 17e697a allocated 3.6 % more
  on `call-indirect`, because the comparison of a callee with the expected type had become a
  call of its own; the next commit inlines it again.) Five unit examples (`test/Spec.hs`,
  "typed function references").

## Where coverage stands (2026-10-12, for the paper's claim)

Supported, with the 3.0 suite passing on all of it: **WebAssembly 3.0 without garbage
collection**, that is every instruction and type of WebAssembly 2.0, linking between modules
included, and of what 3.0 adds, several memories, 64-bit memories and tables, tail calls,
extended constant expressions, the relaxed vector instructions, typed function references and
exceptions. Three qualifications:

- exceptions are thrown and caught under a public pc only (a rule, not a gap in coverage);
- a module that imports the same memory, table or writable global twice is not linked (10
  assertions of the suite), refused by name;
- nullability and the function type behind a reference are checked by a validator beside the
  typed program, not by its types (see "Typed function references").

The relaxed vector instructions (2026-10-12) let an implementation choose among a few results.
Ours are those of the 2.0 instruction each one relaxes (`relaxed_swizzle` is `swizzle`,
`relaxed_laneselect` is `bitselect`, and so on), a product rounded before the sum for
`relaxed_madd`, and saturating sums for the two dot products. Their rule is the rule of every
vector operation. All seven scripts of the suite pass in full (77 assertions).

Not supported: garbage collection, as decided.

Every feature that clang 23 (wasi-sdk 34) and rustc 1.99 enable by default for
`wasm32-wasip1` is supported. The suite's 2,159 skipped assertions are: 1,245 malformed modules
given as text, which the harness does not run; 877 on modules that use garbage collection; 27
for a script command the harness lacks; 10 for an object imported twice. Counts are in
`TODO.md`.
