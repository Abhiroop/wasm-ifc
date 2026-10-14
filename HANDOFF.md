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
  This was my argument; since 2026-10-13 it is proved in Lean on the core (see "Lean" below).
- **Spec suite:** 62,137 passed, 0 failed, 3,065 skipped (62,081 and 3,121 before);
  `throw.wast` and `throw_ref.wast` pass in full. (The main module of `try_table.wast` imports
  a tag; it passes since tags are imported, see "State shared between modules".) Four unit
  examples (`test/Spec.hs`, "exceptions").

## Lean: noninterference on a core with control flow, calls and memory (item 12, 2026-10-12)

- **Where:** `lean/` (Lean 4.35.0, no dependencies; `cd lean && lake build`). 5,566 lines in
  seven files; `lean/README.md` states what is proved and what differs from the paper.
- **What is proved** (`WasmIfc.tini`, from `WasmIfc.ni`): termination-insensitive
  noninterference for a function of a well-typed module, under the lift-free rules, on a core
  with blocks, loops and conditionals (with parameters and results), `br`, `br_if`, the
  repaired `br_table`, direct and indirect calls (recursion included), `load` and `store` on a
  memory whose cells
  carry a level, with the run-time check of loads, local and global variables and arithmetic. Also `WasmIfc.rise`, the paper's `lem:rise`. **No `sorry`; the theorems
  depend on `propext`, `Classical.choice` and `Quot.sound` only** (`#print axioms`).
- **Against the plan's steps (a) to (f):** (a) in part. The rules are the W-rules themselves,
  so for this core there is no erasure and no inclusion to prove, and the theorem is the main
  theorem's statement for the typed program. Not covered: a memory of bytes, more
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
- **Preserved globals, `return` and `local.tee` (added 2026-10-13).** The core now has the
  rule for a preserved global and its run-time comparison, so the plan's item "preserved
  globals in the proofs" has a proof case and is no longer an assumption of the theorem.
  No `sorry`, the same three axioms.
  - *What is modelled.* `Ctx.preserved` says which globals are preserved. A write to one has
    the rule of `IGlobalSetPreserved` (no premise on the pc; the value at most as secret as
    the pc). A block, a loop and a conditional carry the premise `Restores pcEnd after keep`,
    with the same `pcEnd` and `after` as the witnesses of `IBlock`, `ILoop` and `IIf`; a
    function carries what `ReturnsWith` says. The semantics goes on after a construct, or a
    call, only if the compared globals hold what they held at its start, or at the call.
  - *What is proved.* `tini` as before, for states that also agree on the preserved globals:
    the two runs agree on them again at the return, if both pass the comparison made there
    (a run that fails it traps). Inside, the two runs agree on the preserved globals wherever
    the pc is public (`PresOr`).
  - *The argument*, which the appendix can use. In C terms, take
    `if (secret) { sp -= 16; f(); sp += 16; }`. Inside the conditional the pc is secret, and the
    two runs may hold different values of `sp`; the proof says nothing of `sp` there. After the
    conditional the pc is public again, so it drops, and the rule makes the conditional compare
    `sp` with its value before the `if`. Both runs passed that comparison, or one trapped. The
    pc before the `if` was public, so the two runs agreed on `sp` there, and therefore they
    agree after it.
  - *Finding 1: the pc before the construct is public whenever the comparison is needed.* The
    pc after a construct is at least the pc before it (`rise`), so where the pc after it is
    public the pc before it was too. This is what makes "its value at the construct's start"
    a value the two runs share. No extra premise is needed for it.
  - *Finding 2: a loop must compare with the values at its first entry.* The implementation
    does (it records once, in `restoring`). Comparing with the start of the last iteration
    would be unsound: the first iteration writes the global under a secret pc, the second
    leaves it alone and ends the loop, and the comparison passes with two different values.
    To state the right comparison in a big-step semantics, a loop now evaluates the
    iterations of its body as one unit (`iter`, an instruction no program contains). The
    proof for a loop became the proof for a block around that unit, and the separate lemma
    for a loop that runs alone (`loop_alone`) is gone.
  - *Finding 3: a call on a secret table index needs the callee's comparison.* Two different
    functions run, each under a secret pc from its start, so each ends under a secret pc and
    the rule for functions makes each compare the preserved globals at its return. Without
    that premise the caller, whose pc may be public, would go on with globals the two runs
    disagree on.
  - *The memory is bounded now* (the same day): a load or a store outside it traps,
    `memory.size` gives a public value, and `memory.grow` is typed as `IMemGrow` is, only
    under a public pc with a public amount. 2,516 lines. One thing the proof does not model:
    the implementation's `memory.grow` may also fail when the host has no memory left, which
    is outside the program's state. In the proof it fails only by the memory's declared limit.
  - *Exceptions* (the same day; 2,911 lines). The core has `throw` and `try_table`, with the
    rules of `IThrow` and `ITryTable`: an exception is thrown only under a public pc with
    public values, a `try_table` is typed only under a public pc, and a clause's branch raises
    no pc. The proof settles the two points that were open:
    1. *Typing them under a public pc only is sound.* Whether a run throws, and what, is
       public: a run under a secret pc does not end by an exception, so two runs throw
       together or not at all, the same tag with the same values, and the same clause catches
       it. `tini` now says: if both calls end, either both return or both end by the same
       exception with the same values.
    2. *An exception cannot harmfully skip a comparison of the preserved globals.* It does
       skip the comparisons of the blocks and calls it leaves. But it is thrown under a public
       pc, where the two runs agree on the preserved globals, and nothing changes the state
       between the throw and the clause. In C terms: `longjmp` out of the middle of a function
       skips its epilogue, but it can only be called where no secret has decided the control
       flow, and there the stack pointer is the same in both runs.
    Not modelled: references to exceptions (`exnref`, `throw_ref`, `catch_ref`).
  - *The statement in the paper's terms, and a reading guide* (2026-10-13, the plan's second
    list, items 1 and 2). `lean/STATEMENTS.md` is for a reviewer who checks definitions and
    the statement only: where each is, what to be convinced of, each typing rule beside its
    `Instr` constructor and the paper's rule, what is assumed, what is outside the core.
    `lean/guide.py` writes it, with the line numbers. Two changes to the statement:
    - **The indirect call compares bounds by the order.** It goes on if the callee has the
      expected parameters and results and its bound is at least the expected one, as
      `compared` does in the implementation and as the paper says, where the core asked for
      equal types. The same for a call through a reference.
    - **`WasmIfc.noninterference` (`Statement.lean`) is the theorem with the paper's
      attacker.** `LowEq` is `def:attacker` clause by clause: public locals, every public
      global, the bytes public in both, the memory's size, the descriptors' levels, and for
      every public descriptor the output written and the input left. Its conclusion has what
      the attacker observes: the results, the final public globals, the bytes written to
      public descriptors. A call from outside is `Invoke`, which includes the comparison of
      preserved globals that the machine makes for the invoked function, so the conclusion is
      unconditional. Two clauses of the paper's definition have no counterpart: stack
      positions (a call from outside starts on an empty stack) and the names of files in
      directories (the core's host has none). One hypothesis is new and explicit: a preserved
      global is public, which the policy ensures.
    3,945 lines; `noninterference` depends on the three standard axioms.
  - *A machine and refinement* (the plan's list of 2026-10-14, item 2).
    `lean/WasmIfc/Machine.lean` has a small-step machine for the whole core, shaped like
    `Runtime.Interpreter.step`: a state, the current block's operands, the rest of the block,
    and a control stack of labels and call boundaries (`Frame`); `Step` is one transition and
    `Runs` a run to its end. `refinement`: a run from `Config.entry f a s` to an end `e` is
    `Invoke F f a s e`. It needs no typing, and holds for every instruction of the core, so
    nothing of the paper's `lem:refinement` is left on paper for the core.
    `machine_noninterference` is `noninterference` for two runs of the machine. Both have no
    `sorry`; `refinement` depends on `propext` and `Quot.sound`, the other on the three
    standard axioms. Section 6 of `lean/STATEMENTS.md` puts each part of the Lean machine
    beside the Haskell one with both lines; that correspondence is the paper's Assumption (M),
    and it lists four known differences (the bound on the depth of calls, the suspension at
    host calls, the coercions between segments, the reference a clause gets for an
    exception thrown again).
    - **The proof found an error in the Lean semantics, now fixed** (`e75d54a`). `Eval` ran a
      tail call as a call inside the function, so a `try_table` around a `return_call`
      caught an exception of the callee. The Haskell machine drops the function's labels and
      their clauses at the tail call (`tailCall`), as WebAssembly says, and the exception
      passes. `Eval` now has an outcome of its own for such an exception (`Out.tailExn`),
      which the function's blocks pass and which is an exception again for the function's
      caller. `ni` has the case; the theorem's statement is unchanged, but `Invoke.threw` is
      now stated with `Out.thrown`. The implementation was right; no Haskell changed.
  - *References to exceptions* (the list of 2026-10-14, item 4): `throw_ref`, and clauses that
    catch by reference (`catch_ref`, `catch_all_ref`), with the rule of `IThrowRef` and of the
    two handlers. The state keeps the exceptions that references are to. Two runs keep the same
    ones, since a clause catches only under a public pc, and this is a clause of `StRel` and
    of `LowEq`, with the condition that a kept exception carries as many values as its tag
    says (`ExnOk`). **For the paper:** this is an assumption on the two initial states that
    `def:attacker` does not have; it holds of a new instance, which keeps no exception.
  - *Opening a file in a directory* (the list of 2026-10-14, item 4): `hostOpen`, which is the
    paper's Host-Open (appendix B) operand for operand. The state has a descriptor table from
    descriptors to channels, the names of the files in each directory, and the channel of each
    file; the two host calls that were there go through the table. The name's bytes must be
    public or the call traps; the file is opened if the directory has the name or `O_CREAT`
    is set, as the least free descriptor from 3 on, which is stored as a public value; a new
    file starts empty; otherwise the status is an error code. `LowEq` has the two clauses of
    `def:attacker` that it lacked: the same descriptor table and the same names in every
    directory. The proof does not use that a file has its directory's level, which the paper
    states of the policy: two runs open the same channel whatever its level.
  - *A second memory* (the list of 2026-10-14, item 4): of a fixed size, with `memory.copy`
    from the memory to it and back (`copyTo`, `copyFrom`), typed as `IMemCopy` is whatever its
    two memories. Its bytes have levels as the first one's, and `LowEq` has the clause for it.
  - **Not done of that item: a second value type.** A type stack in Lean is a list of levels
    (`STy`), and each of the 60 rules and every lemma on stacks is written on it; value types
    would be a second component of every entry. The rules' premises on levels do not mention
    the value types, and the semantics is on untyped numbers, so the proof would be the same
    with the types carried along. For the paper: the Lean rules are the level part of the
    paper's rules, and that a value has its type is WebAssembly's validation, which is not
    restated in Lean.
  - *More of the table, and the indirect tail call* (the same list, item 6): `table.fill`,
    `table.copy` and `return_call_indirect`, with the rules of `ITableFill`, `ITableCopy` and
    `IReturnCallIndirect`. Then `table.size` and `table.grow` (the list of 2026-10-14, item 4),
    with the rules of `ITableSize` and `ITableGrow`: the table has a size and a limit, which
    two runs agree on when the table is public, and its instructions and the indirect calls
    trap beyond the size.
  - *A memory of bytes and data segments* (2026-10-13, the plan's item 5). A load and a store
    name a number of bytes. A load of several bytes checks the level of each, which is the
    check on the join of their labels that the paper states, and the proof of the case is that
    each byte passed the check in both runs, so each is public in both and they agree.
    `memory.init` and `data.drop` are in the core with the rules of `IMemInit` and
    `IDataDrop`. **A finding:** `IDataDrop` has no premise on the pc, so under a secret pc one
    run may drop a segment that the other keeps. This is sound, but only because traps are
    not observed: `memory.init` on a dropped segment traps unless it asks for no byte, so
    where both runs go on they have copied the same bytes. If the paper ever states a
    termination-sensitive property, `data.drop` needs the pc to be public.
  - *A call through a reference* (2026-10-13, after the benchmark): `call_ref` with the rule
    of `ICallRef`, and the two instructions `br_on_null` is elaborated to besides the
    conditional. This is the proof on the core of the rule for `call_ref`, and it shows the
    coarser typing of `br_on_null` sound, since that typing is a composition of rules that
    are each in the proof.
  - *The host boundary* (the same day; 3,459 lines): descriptors with levels, a read and a
    write. A write traps unless every cell it takes flows into the descriptor's level, and a
    read stores its data and its count at that level, as the implementation does. The
    attacker of `tini` now also sees what was written to a public descriptor and what is left
    to read from one, which is the paper's `def:attacker` for channels. A run under a secret
    pc makes no host call, since a host call is typed under a public pc only.
  - *A table with a level* (the same day): the function table has one level, as
    a table has in the implementation, with `table.get`, `table.set` and the indirect call
    typed as `ITableGet`, `ITableSet` and `ICallIndirect` are. This is a proof of the table
    rules on the core, which were ours and had none. Two runs agree on the table only if it
    is public; a call through a secret table is handled as a call on a secret index is.
  - *Bulk memory* (the same day): `memory.fill` and `memory.copy`, with the
    rules of `IMemFill` and `IMemCopy`. A copy makes no run-time check, and the proof confirms
    that it needs none: each copied cell keeps its own level, so a cell that was secret in one
    run is secret where it lands, and is not compared.
  - *Tail calls* (the same day): `return_call`, with the rule of `IReturnCall`
    (the call, then the `return` of what the callee returns). The callee's comparison of the
    preserved globals is made where the tail call is, as in the machine (`tailCall`), and the
    caller's own stays with whoever called it. Not in the core: the indirect forms.

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
- **An object imported twice (2026-10-12, later the same day):** inside one instance two
  indices are two objects, so a module that imports the same memory, table or writable global
  under two indices cannot be instantiated as it is written (`ImportedTwice`). It does not
  have to be: a use of the second index is a use of the first. `Runtime.Link.unaliased`
  rewrites every such use before validation and declares the second index unused
  (`Validation.Aliases`); the elaborator checks that it is unused before it believes it; the
  linker then gives that index its object once and leaves it alone. In C terms: two pointer
  variables that are known to hold the same address are replaced by one. 20 assertions of the
  suite (`instance.wast`, `imports1`, `imports2`, `data0`, `data1`). The spec runner also
  performs `module_definition` and `module_instance` now (17 assertions).
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

## The paper's numbers, checked (the plan's items 1 to 4b, 2026-10-13, at 67e5597)

Checked against `08-evaluation.tex`, the abstract and the end of the introduction as they
were at Overleaf 5063c84. `REPRODUCE.md` has the command behind each number.

### Numbers that do not match

1. **WANILLA (table `tab:eval`, section "Comparison", introduction).** The paper has 63 of 63
   leaks, 152 of 196 secure specifications, 53 not expressible. Those are of 5 October. The
   same translation at 67e5597 gives **67 of 67, 156 of 200, 45 not expressible**: eight
   specifications import a memory or a global, which the decoder then refused. The 44
   rejected secure ones and their breakdown (21, 11, 5, 4, 2, 1) are unchanged.
   With two more kinds of query translated (see "WANILLA again" below) it is **73 of 73,
   163 of 211, 28 not expressible**, and 48 rejected: the 44, and 4 at a store.
2. **"Rejects every leaking program of an independent benchmark" (abstract).** It rejects
   every leak among the specifications it can express. Of those it cannot, 20 are leaks under
   the paper's translation and 14 under the wider one.
3. **"Policies of two to four lines" (abstract, introduction).** True of the password checker
   (4), the service (2) and PolyBench (2). The program with a stack frame of section
   "C programs" runs under 5 lines (the four of the checker and `preserved global 0`).
4. **The naive checker (section "A password checker").** The paper says the call that writes
   the verdict happens under a secret pc. What the elaborator reports is in `open`, the call
   that opens the log: `InFunction 24 (AtInstruction 4 (IllegalFlow "global.set" High Low))`.
   Function 24 is `open`, and instruction 4 is the write of the stack pointer in its
   prologue. Inference raised `open`'s bound to secret because `main` calls it under a secret
   pc, and the first public write of `open` is then the failure. With `preserved global 0`
   added, the rejection moves to `sbrk`: `InFunction 36 (AtInstruction 23 (IllegalFlow
   "memory.grow" High Low))`.
5. **"clang 23 (wasi-sdk 34) and rustc 1.99" (section "Conformance").** That sentence is about
   the features the toolchains enable by default, and it holds. The binaries of the WASI
   suite that we run were built by others, with **clang 22.1.0 (wasi-sdk) for the 14 C
   programs and rustc 1.96.0 for the 46 Rust programs** (their `producers` sections); the 12
   AssemblyScript binaries name no producer. Our own C programs are built with clang 23.1.0.
6. **"Within a factor of two of WABT" (abstract, introduction, section "Other
   interpreters").** True of the geometric mean, 1.5. By kernel the ratio goes from 0.85 to
   7.7: WABT is 7.7 times as fast on `labels-64`, 4.5 on `globals-64` and 3.0 on `labels-16`.

### Numbers that match

63,080, 2,122, 877, 1,245 and 257; 72 programs as 14, 46 and 12; 100,000 programs with 36 %
accepted (30 % finish, 6 % trap; 64 % rejected); 1,666 and 5,057 (not run again, from the
entries of their day); 18 examples, of which two trap and five of SecWasm's are rejected, and
the leaking program of the findings; four policy lines and three locals for the checker; two
lines for the service; 8 of 14 C programs in both configurations and 6 rejected; 10 of 10
PolyBench kernels under two lines, all rejected with their printing, at function 64 and, with
the pointer preserved, at the indirect call of function 63; no accepted program needs the
absence of the lift (49 programs, all accepted under the restrictions too); 24 kernels; the
spread (at most 1.3 %); 1.04 with 0.88 to 1.25; 2 %, and 11 to 20 % at blocks; 8 % and 4 %
with secrets; 4.5, 1.5, 11, 35, 46 and 53.

Not measured again: the 0.97 of the typed obligations over seven workloads (50011b8, before
this night's optimizations) and the 0.97 of the typed core against its erased copy (the laptop,
18 September).

### The versions of the benchmark

From `environment.versions` of `bench/results/2026-10-13-c2a3f4b-t2-medium.json`: Wasmtime
48.0.1 (Pulley, Winch and Cranelift), WAMR `iwasm` 2.4.5, wasm3 0.9.1-beta.1, wasmi 2.0.0;
WABT `wasm-interp` 1.0.42 and the Hackage `wasm` 1.1.1 on the kernels.

### The overview's example, from the real binary (item 3)

The policy, `casestudies/password/checker.policy`:

```
dir /secrets : H               ; files opened here are secret: the password
dir /log : L                   ; the log shared with the developer is public
stdout : H                     ; only the user sees the verdict
load-default func 11 : H       ; main (__original_main) reads the password's bytes
```

The checker, with `/secrets/password` holding `letmein`:

```
$ wasm-ifc run --policy checker.policy --dir secrets::/secrets --dir log::/log password.wasm
weak
$ cat log/runs.log
checked 4
```

A leaking variant (`-DLEAK_CONTROL` logs the verdict, `-DLEAK_MEMORY` the hash; both print the
same):

```
$ wasm-ifc run --policy checker.policy --dir secrets::/secrets --dir log::/log password-leak-control.wasm
weak
trap: fd_write was handed a byte more secret than its descriptor; nothing was written
$ cat log/runs.log
$
```

The verdict still reaches the secret standard output, and the log stays empty. Until today
this trap read `trap: InformationFlowViolation`; it names the call since 67e5597.

The naive checker:

```
$ wasm-ifc check --policy checker.policy password-naive.wasm
Validation error: InFunction 24 (AtInstruction 4 (IllegalFlow "global.set" High Low))
```

and `wasm-ifc explain` adds what inference had raised by then: 12 locals of `main`, and the
bounds of functions 13 and 24 (`open`) to secret. Item 4 above says what this error means.

### WANILLA again (item 2)

- **Case studies:** re-recorded in `casestudies/results/2026-10-13-67e5597.json`. All 90
  outcomes are those of 5 October.
- **Imports of a memory or a global** are decoded now: 8 specifications moved from "not
  expressible" to 4 leaks caught and 4 secure accepted.
- **Memory.** A specification whose attacker observes the memory's data at the end is
  expressible by declaring every store public: a store of a secret is then rejected, every
  byte stays public, and our attacker sees what WANILLA's sees. 13 specifications: 3 leaks
  caught, 6 accepted, 4 rejected at a store that writes a value WANILLA proves independent of
  the secret. Six ask about areas of the memory, which a policy cannot say statically.
- **Imports.** What flows into an imported function with public parameters, results and
  context is our default for an import. 4 specifications: 3 leaks caught, 1 accepted. Eleven
  give an import a secret parameter, result or context, or let it write the module's state.
- **Tables.** A policy can label a table now, but only two specifications mention one, and
  both also give an import a secret context. So tables make nothing more expressible.
- **The four losses at indirect calls.** I declared the expected type and the functions in
  the table with a secret bound (`type 1 : -{H}-> H`, `func 1 : -{H}-> H`, by hand; the
  comparison's script does not do it). One of the four is then accepted
  (`basic/call_indirect`, parameter and result secret). The other three stay rejected for
  another reason: one returns a public result that both callees compute as the same constant,
  and two call functions that write a public global, which WANILLA's specification does not
  observe at the end. So the sentence "because our translation leaves the expected types of
  indirect calls public" explains one loss of the four.

### What SecWasm's rules reject in compiled code (item 4b)

`./scripts/secwasm-shapes.py` types each function as validation does and counts four shapes.
Each cell is instructions, then modules that have at least one. Every module was analysed, and
the script found exactly the four shapes in the four hand-written programs of the findings,
one each.

| Binaries | Modules | Functions | `br_table` with more targets than blocks | `br_table` with values below | `unreachable` where the stack is not the block's result | branch to the function body |
|---|---:|---:|---:|---:|---:|---:|
| C, clang 22.1 (WASI suite) | 14 | 831 | 15; 14 | 0; 0 | 19; 8 | 0; 0 |
| Rust, rustc 1.96 (WASI suite) | 46 | 15,320 | 230; 46 | 0; 0 | 354; 46 | 0; 0 |
| AssemblyScript (WASI suite) | 12 | 337 | 0; 0 | 0; 0 | 12; 10 | 0; 0 |
| C, clang 23.1 (our case studies) | 33 | 1,587 | 10; 10 | 0; 0 | 60; 30 | 0; 0 |
| C, clang 23.1 (CoreMark, PolyBench) | 62 | 4,376 | 62; 62 | 0; 0 | 124; 62 | 0; 0 |

What this supports:

- **Every binary of clang and of rustc in the WASI suite has a `br_table` that SecWasm's
  premise rejects**: 60 of 60, and so has every build of CoreMark and PolyBench. Of the 913
  tables in the suite's C and Rust binaries, 245 have more targets than enclosing blocks.
  Of our own small case studies 10 of 33 have one, and AssemblyScript's binaries have none.
- **`unreachable` where T-Unreachable fails** is in 64 of the suite's 72 binaries, from all
  three compilers (8 of 14 C, 46 of 46 Rust, 10 of 12 AssemblyScript).
- **A `br_table` with values below the carried ones occurs in no compiled binary**, and
  neither does a branch to the function body. Section 4.2's "compilers emit programs of the
  first two kinds" is right if the second kind is read as `unreachable`; the example with
  `br_table` under that heading is ours, not a compiler's.
- The C binaries share wasi-libc, so their counts are not independent: most of the 15 tables
  of the 14 C programs are the same functions of the library.

Directories: `test/wasi/testsuite/tests/{c,rust,assemblyscript}/testsuite/wasm32-wasip1`,
`casestudies/build/{password,frames,service,polybench}`, `bench/wasm-t2`. Data:
`bench/results/2026-10-13-secwasm-shapes.json`.

## An anonymized artifact (the plan's second list, item 4, 2026-10-13)

`./scripts/artifact.sh [OUT]` writes an anonymized copy of the tree to `OUT/wasm-ifc/` and
`OUT/wasm-ifc-artifact.tar.gz` (default `../wasm-ifc-artifact`). Nothing is published.

- **What it is:** the files of `HEAD`, without history, so without commit messages and
  trailers. About 350 files, 4.6 MB unpacked, 680 KB packed; the script prints the numbers. `REPRODUCE.md` is at its
  top, with the two test suites fetched by `git clone` at their pinned commits, since a copy
  without history has no submodules.
- **What is removed:** `CLAUDE.md`, `paper/`, `.gitmodules` (it had the paper's remote), and
  the script itself, which names what it removes.
- **What is rewritten:** the licence's copyright line and the package's `author` and
  `maintainer`; the two first names where a document has them ("an author"); e-mail
  addresses; absolute paths under a home directory, which the recorded benchmark results
  had (30 files in all). The archive's entries have no user name and one fixed date.
- **How it is checked:** the script searches every file of the copy, binaries included, for
  the names, the addresses, the user's name and home paths, and fails if one is left. The
  copy builds from the archive with `-Werror`, and its 239 unit tests pass.
- **What is not anonymous in it, to decide:** the repository's name `wasm-ifc` and the
  documents' talk of "the paper", its sections and its plan (`HANDOFF.md`, `TODO.md`). If the
  artifact should not carry the hand-off, delete `HANDOFF.md` from the copy; `REPRODUCE.md`
  points to five of its sections for details that the commands' output also gives.

## A Rust program with secrets (the plan's second list, item 5, 2026-10-13)

The password checker is ported to Rust (`casestudies/password-rust/`), built by the installed
`rustc` 1.99.0 for `wasm32-wasip1` with the standard library, at `-C opt-level=2`. It took
about half an hour, and nothing in the interpreter changed.

- **It runs under a policy**: the verdict on the secret standard output, `checked 4` in the
  public log; also under SecWasm's restrictions. Inference raises three locals of `main`.
- **The policy has 9 lines, not 4.** The checker's one line for the loads of `main`
  (`load-default func`) is too coarse for this binary: Rust keeps the file descriptor in
  memory, so the default makes it secret, and the call of `fd_read` is rejected for a secret
  argument. Declaring the six loads that the traps name instead works. So "at most five
  lines" holds of the C programs; with the Rust one the range is two to nine.
- **Both leaking variants are stopped, earlier than in C.** Logging the verdict by a branch is
  rejected statically, at an indirect call under a secret pc (the string's growth calls the
  allocator through a function pointer). Logging the hash traps at a load in the formatting
  code that reads a secret byte without a declaration. In C both reached `fd_write` and
  trapped there.
- **What it shows for the abstract's claim**: one program with secrets from `rustc`, 715
  functions with the standard library, typed and run. `casestudies/run.py` runs it if it has
  been built, and the results file of this commit has its three rows.

## Performance and the clean benchmark (item 9, 2026-10-13)

`BENCHMARKS.md`, last section, has the tables; `bench/results/2026-10-13-c2a3f4b*` the data.
The machine was quiet (load about 1 of 12 threads, spread 0.6 % on the kernels and 0.2 % on
the medium programs), so the times may be quoted, for this machine: an AMD Ryzen 5 3600.

- **What changed first.** A profile by instructions executed found eight costs, and they are
  removed (`BENCHMARKS.md` lists each with its cause). The interpreter at c2a3f4b is 14 %
  faster on the kernels than the typed core of 18 September and 15 % faster on the medium
  programs, and with secrets in memory it costs 8 % where it cost 70 %.
- **The placeholders of section 9.5.** The labels against the typed core need a baseline with
  the same general optimizations, or the comparison credits the labels with a speed-up. That
  baseline is `pre-ifc-opt` (0fcf4b4 with `bench/pre-ifc-opt.patch`). Against it:
  - X, the kernels under no policy: **2 %** (1.02 as a geometric mean of 24, 0.78 to 1.20; 3 %
    without the one kernel the patch slows down). It is 11 to 20 % where blocks are entered
    and left, and nothing on locals, globals and memory.
  - Y, the programs under no policy: **no cost that can be measured.** The labelled build is
    at 0.91 (small) and 0.88 (medium), since memory was made faster after 18 September.
  - Z, the programs with secrets in memory: **8 %** over the same build without a policy at
    the medium sizes (1.04 to 1.23), 13 % at the small sizes, where a constant 0.03 s of
    inference weighs more. Allocation: 4 % and 10 % more.
- **Intrinsic typing.** The typed and labelled machine against its erased twin, both with the
  general optimizations: 1.04 on the kernels (0.88 to 1.25). The paper's 0.97 is of the typed
  core of 18 September against the twin of that day. The twin has no labels, so 1.04 is typing
  and labels together.
- **Other interpreters, which the paper's paragraph must change.** `wasm-interp` 1.0.42 is 1.5
  times as fast as the labelled build on the kernels, not 1.2 (that was 1.0.27 on the laptop).
  The Hackage `wasm` 1.1.1 is 4.5 times slower. On the medium programs: Pulley 11 times as
  fast, WAMR 35, wasm3 46, wasmi 53 (the paper has 16, 9, 45, 49 from the laptop). The
  labelled build needs 16 to 26 ns per step on the programs (the paper says 11 to 24).
- **What I did not do.** One trusted line would make giving a stack new levels free
  (`relabelStack` as a coercion). Nothing measured asks for it now, and it would qualify "the
  machine is its own soundness argument", so it is left for Daniel to decide (`TODO.md`). The
  memory is still persistent: a store copies 1 KiB and inserts it in a map, which is the
  largest cost left in a memory-bound program.

## A second round on performance, by instructions executed (2026-10-13, 1d633f3)

`BENCHMARKS.md`, last section, has the tables. The machine was busy, so nothing was timed:
every number is a count of instructions executed per machine step, which does not depend on
the load. **The times in the paper's evaluation are those of c2a3f4b and are now too high
for the labelled build**; a sweep on a quiet machine (about two hours, `bench/sweep-labels.sh`)
has to replace them, and I did not start one.

- **What changed.** The labelled build executes 0.72 times the instructions on the 24
  kernels (0.61 to 0.92) and 0.72 times on the 11 small programs (0.69 to 0.76). Five
  changes, each with its cause in `BENCHMARKS.md`: strict fields in the typed instructions
  and their witnesses, the six most frequent instructions declared first, loads and stores
  of a word without a loop over its bytes, frames of locals kept in groups of eight words so
  that a `local.set` copies one group, and a driver loop that does not pass the functions.
- **For the paper: a typed instruction cannot hold an undefined witness any more.** The
  fields of `Instr`, `Expr` and the witnesses (`FlowsInto`, `Elem`, `BranchTarget`, ...) are
  strict. Before, `ILocalSet undefined undefined ref` was a value of the instruction type,
  and the machine would have run it, since it never looks at those two proofs. Now building
  it fails. The paper's claim that an ill-typed program is not representable needed this to
  be literally true in Haskell, where every type has an undefined value. The example in
  `test/Examples.hs` that leaves a hole for a proof that does not exist now fails when the
  program is built, and the test expects that. GHC's coverage check also uses the strictness:
  five clauses for targets that no witness can name were redundant and are removed.
- **The erased twin** has the same changes, so the ratio of the typed machine to it can be
  measured again in the next sweep. By instructions it is 1.00 to 1.11 on eleven kernels.
- **The allocation reference** is recorded anew: up to 3 % less on the programs, 6 % more on
  kernels that have two or three locals.
- **A third round** (78c3f93, the same day, also by instructions) took the steps that need no
  decision: the chunks of a memory in a radix tree in place of the `IntMap`
  (`Runtime.Chunks`), chunks of 256 bytes, a load that tests for "no secret" without a
  call and reads its word in one piece, a store strict in its word, and the first case of a
  branch and of a stack split in line. The programs execute 0.81 times the instructions of
  the second round (0.75 to 0.89) and the kernels 0.93. From 48ac063, the day's start, that
  is 0.58 on the programs and 0.67 on the kernels, and about half the cycles on the programs
  as far as a busy machine shows. GHC's LLVM backend was tried (LLVM 19 is installed now,
  `opt-19` and `llc-19`) and is slower than the native one here, by 2 to 36 % in cycles.
- **What is left**, with what each would take, is at the end of the third round's section of
  `BENCHMARKS.md`. The large one is still the memory: a store in place gave 16 to 20 % fewer
  cycles on three memory-bound programs in an experiment that is not committed, and it needs
  Daniel's decision, since the machine then is a function of a configuration only if each
  configuration is used once. The second is that a call finds its function by walking a list
  as long as the function's index.

## The findings in Lean, evidence for Lemma 1, and the guide (the plan's block of 2026-10-14, at bc768cc)

The four items of the block and the two small ones before it are done. `lake build` is green
without `sorry`. `lean/WasmIfc/*.lean` has 5,996 lines (it had 5,566). Nothing that the paper
cites was renamed or restated: the two new files import the old ones and nothing imports
them. The gate passes, the suite passes in both configurations, and the case studies give
their recorded results (numbers at the end of this section).

### Item 1: the three programs of the findings (`lean/WasmIfc/Findings.lean`, 206 lines)

| Lean name | Statement | Axioms |
|---|---|---|
| `leak` | Program (a): four blocks without parameters or results, `local.get 0; br_table [0] 3` in the innermost, `const 1; global.set 0` after the third block inside the fourth. | |
| `leak_not_typed` | `∀ Ls st P' st', ¬ Typed leakCtx Ls leak [L] st P' st'`: no typing from a public pc, for any labels around the program, any segment before it, and any pc stack and segment after it. | `propext` |
| `leak_runs_differ` | For every `ls`, `s`, `t` with `s.loc 0 = 0` and `t.loc 0 ≠ 0`: `Eval [] 8 ls leak [] s (.normal [] (s.setGlob 0 1))` and `Eval [] 6 ls leak [] t (.normal [] t)`. | `propext`, `Quot.sound` |
| `leak_runs_globals` | If `s.glob 0 = t.glob 0`, the first final state has 1 in global 0 and the second has what `s` had. | `propext` |
| `call_after_secret_branch_typed` | `Typed callCtx [[]] callAfterSecretBranch [L] [] [L] []` for program (b), `const 7; block (param L) [local.get 0; br_if 0; call 0]`. | `propext` |
| `write_after_public_branch_typed` | `Typed branchCtx [[]] writeAfterPublicBranch [L] [] [L] [H]` for program (c), `block (result H) [const 7; local.get 0; br_if 0; local.set 1; local.get 2; br 0]`. | `propext` |

The contexts are as the plan says. In `leakCtx`, local 0 is secret and global 0 is public and
not preserved. In `callCtx`, local 0 is secret and function 0 has the type `[L] -{H}-> []`. In
`branchCtx`, locals 0 and 1 are public and local 2 is secret. Three remarks for the text:

- `leak_runs_differ` asks nothing of the two states but the value of the secret local, so it
  holds in particular for two states that differ there only. The numbers 8 and 6 are the sizes
  of the two derivations.
- (b) and (c) are typed under one label, the function's, with no results (`[[]]`). The result
  of (c) is the pc stack `[L]` and the segment `[H]`.
- `leak_not_typed` is about SecWasm+. That the repaired rule of SecWasm rejects the program
  is `repaired_rule_rejects_leak` of item 4.

### Item 4: the printed rule in Lean (`lean/WasmIfc/SecWasmPrinted.lean`, 224 lines, namespace `WasmIfc.SecWasm`)

It took under the four hours. `SecWasm.Typed lifted C Ls e γ γ'` is SecWasm's judgment on a
stack of stacks (`List (STy × Lab)`, an entry being a labelled type stack and a pc), with
T-Const, T-Get-Local, T-Set-Global, T-Block and T-Br-Table, each composed with T-Seq. I wrote
the rules from Fig. 13 of the full version (pages 34 and 35, read as images) and compared
them with `paper/reference/secwasm-printed-rules-checker.py`. The parameter `lifted` is how
many entries below the current one T-Br-Table lifts, given the targets: `printed` is their
number `m` (the printed `γ'[0 : m - 1]`), and `repaired` is the deepest target (as T-Br-If
lifts `γ'[0 : i - 1]` for its target `i`).

| Lean name | Statement | Axioms |
|---|---|---|
| `SecWasm.printed_rule_accepts_leak` | `Typed printed leakCtx [] leak [([], L)] [([], L)]`: the printed rules type the leak as a function body (T-Func's premise, with a public bound and no results). | `propext` |
| `SecWasm.write_under_public_pc` | In any typing by these rules, with any `lifted`, the `global.set 0` of the leak is under a public pc (this is T-Set-Global for a public global). | `propext` |
| `SecWasm.repaired_rule_rejects_leak` | `∀ γ', ¬ Typed repaired leakCtx [] leak [([], L)] γ'`. | `propext` |
| `SecWasm.printed_rule_rejects_shallow_leak` | The printed rules reject the same leak two blocks deep (`br_table [0] 1`, the write after the first block inside the second). A check that the encoding does not accept everything: the printed rule is wrong only for a target deeper than the number of targets. | `propext` |
| `SecWasm.printed_rule_unsound` | The finding in one statement: for `s`, `t` with `s.loc 0 = 0`, `t.loc 0 ≠ 0`, `s.glob 0 = t.glob 0` and `s.glob 0 ≠ 1`, the printed rules type `leak`, and there are final states `s'`, `t'` of `Eval` from `s` and from `t` with `s'.glob 0 ≠ t'.glob 0`. | `propext`, `Quot.sound` |

Three choices of the encoding, in case the paper describes it:

- `br_table ts d` has the targets `ts` and then the default `d`, so the `m` of the printed
  rule is `ts.length + 1`, which is 2 for the leak. The premises `m ≥ 1` and `|γ| ≥ m` are
  premises of the Lean rule. For the repaired rule the second one reads `k ≤ |γ|` with the
  deepest target `k`. The reference checker asks `|γ| > k` there. The Lean premise is the
  weaker one, so the theorem that the repaired rule rejects the leak is the stronger one.
- `γ ⊑ γ'` is `Below`, the order of Definition 14 entry by entry. The proof of rejection goes
  through every `γ'` that the rule may choose.
- The code after a `br_table` is typed from the rule's output, as T-Seq does. `WasmIfc.Typed`
  does not type that code. In the leak nothing follows the `br_table` in its block.

### Item 3: the reading guide (`lean/STATEMENTS.md`, `lean/guide.py`)

- The column "Paper's rule" has the names T+-Block and so on, from the three figures of the
  appendix. Where the paper prints no rule and says in the text which rule an instruction
  follows, the column says "as" that rule. The three host instructions are under T+-Call,
  since the paper types a call of a host import by its rule for calls.
- Section 4 names the five evaluation rules of the paper's figure: E+-Load is `load`, E+-Br
  is `br`, E+-Block is `blockCont`, E+-Block-Exit is `blockExit`, E+-Call is `call`; and the
  paper's `lands`, `exits`, `kept` are `Out.lands`, `Out.exits`, `Kept`.
- The section on differences no longer mentions an erasure or a typing inclusion. What is
  left: `refinement` and `machine_noninterference` also cover a run that ends by an exception,
  which the paper's `lem:refinement` and `thm:tini` do not state; and the two links outside
  Lean, by reading (a Haskell typed instruction is a derivation of `Typed`; `step` makes the
  transitions of `Step`).
- Section 7 is new and lists the theorems of items 1 and 4 with their lines.

**The paper's clauses (i) to (viii) against `LowEq`.** Every clause of the paper is a clause
of `LowEq` (the table is in the guide's section 5). `LowEq` has two clauses that the paper's
definition lacks:

1. *The public local variables agree* (`∀ i, C.locals i = L → s.loc i = t.loc i`). These are
   the locals of whoever makes the call. The callee gets a frame made of its arguments, and
   the final state has the caller's locals as they were, so the clause is assumed of the
   initial states and holds of the final ones for that reason alone. The paper can leave it
   out without changing what the theorem says of a program, but as stated in Lean it is a
   hypothesis.
2. *`ExnOk C s`*: every exception that the first state keeps for a reference carries as many
   values as its tag says. It is a condition on one state. A new instance keeps no exception,
   so it holds there, and the theorem gives it back for the final state.

Two remarks on wording. Clauses (ii) and (iii) say "the memory", and the core has two: the
second memory's public bytes and its size are clauses of `LowEq` as well. Clause (v) covers
`fdt`, `chan`, `names` and also `file`, the function that gives a file of a directory its
channel.

### Item 2: evidence for the proof of Lemma 1

All three points are now checked by a script in the gate, `scripts/step-inventory.py`, except
the last, which is by reading with the divisions covered by the script.

**How.** The script builds the library without optimization into `dist-recursion/` with
`-ddump-ds` and reads the desugared Core of every module. It computes the definitions that
`Runtime.Interpreter.step` can reach, by name, through the imports of each module, and takes
two inventories over them. Each is compared with a list in `test/` in which every entry has
its reason. A definition that is found and not listed fails the gate, and so does an entry
that is no longer found. `step` reaches 278 definitions, in `Runtime.Interpreter`, `Stack`,
`MemInst`, `Chunks`, `TableInst`, `Numeric`, `Vector`, `Convert`, and besides in
`Syntax.TypesIFC`, `Syntax.Immediates`, `Validation.Shape` and `Validation.Reflect`.

**Recursion (mechanical).** `step` and `stepInstr` are in no recursive group. 56 of the 278
definitions are recursive: the `Rec` groups of the top level and the `letrec`s inside
definitions, which GHC forms by dependency analysis. `test/recursion-allowed.txt` has each
with what it descends on. By kind:

| Descends on | Number | Which |
|---|---:|---|
| a witness or a singleton (`Elem`, `Append`, `SegmentFlows`, `PreservedGlobals`, `TableReach`, `Sing`) | 30 | `getFunc`, `getGlobal`, `setGlobal`, `splitValues`, `relabelByValue`, `stillRestored`, `withArguments`, `appendIs`, `withinReach` and the like |
| the control stack | 7 | `unwindFrom`, `unwindTo`, `returnUnwind`, `tailCall`, `throwException` and its local `offer` (which also descends on a handler's list of clauses), `activationDepth` |
| a count of bytes or words, or a list of them | 9 | in `MemInst`: `runsByChunk`, `setLevelsFrom`, `levelWhereSecrets` and four local loops; in `Vector`: `pairs` and a comprehension |
| a tree: the chunks of a memory, or a frame of more than 64 words | 6 | `chunkAt`'s `descend`, `withChunk`'s `put` and `below`; `frameSlot`, `slotOfLargeFrame`, `withFrameSlot` |
| an operand stack | 1 | `appendValues` |
| a size that grows a bounded number of times | 2 | `withChunk` raises the tree's root while the key has bits above it, at most 13 times for a key below 2^56; `zeroFrame`'s `eightOf` multiplies the frame by 8 until it holds the locals, at most 5 times for the decoder's bound of 50,000 locals |
| nothing: a recursive value | 1 | in `throwException`, the dictionary of the singletons library's equality on lists of types, which refers to itself for the tail of a list. The comparison it serves descends on the types of a tag. |

So the sentence of the paper's proof, "descends on a witness, on a stack, or on a count of
bytes", needs two more cases: a tree (of chunks, or of a frame), and the two functions that
enlarge a structure a bounded number of times. The paper side's text scan found about forty
recursive definitions in four files. The exact number that a step reaches is 56, in eight
modules.

**Partial functions (mechanical).** The script looks, in the same 278 definitions, for the
functions of other packages that can raise an exception or read outside an array. No
definition calls `error`, `undefined`, `head`, `tail`, `fromJust`, an indexing that raises
(`!`), `toEnum`, `throw`, a record selector that can fail, or an unsafe coercion. It found
one hole, which is now closed:

- `Runtime.Vector` indexed a list of lanes with `!!` at four places. Two of them
  (`extractLane`, `laneBitsAt`) took the index from the instruction's lane immediate, a byte
  that validation bounds and the instruction's type does not. A typed instruction with a lane
  index past the last lane would have raised a Haskell exception in a step. The lookup is now
  total (`laneAt`, 0 past the last lane), and `!!` is on the list of names that fail the gate.

113 uses remain, each in `test/partial-allowed.txt` with its reason: 36 are the fall-through
that GHC's desugarer leaves under a match on a GADT (`patError`), which no value reaches
since the exhaustiveness checker accepts each match and an incomplete one is an error of the
build; 35 are divisions, remainders and powers, with a constant or a guarded divisor and an
exponent that is not negative; 24 are shifts and bit tests, whose counts are not negative
(they are on the list because GHC's shifts raise on a negative count); and 18 are unchecked
primitives of arrays and shifts in the tree of chunks, in frames, and in the read and the
write of a word, each within a bound that the entry states. `fromIntegral` wraps and raises
nothing, and the runtime modules have no `Natural`.

**Traps (by reading; the divisions are in the list above).** Each operation for which
WebAssembly prescribes a trap returns `Left` and raises nothing:

- Division by zero and the overflow of signed division: `Runtime.Numeric.intDiv32`,
  `intDiv64`, `intRem32`, `intRem64` return `Left IntegerDivideByZero` and `Left
  IntegerOverflow` in clauses before the division. The remainder of the least integer by -1
  is answered 0 before `rem` is called.
- A float that is no number or out of range: `Runtime.Convert.truncToI32` and `truncToI64`
  return `Left InvalidConversionToInteger` and `Left IntegerOverflow`. They compare the
  truncation as an unbounded integer with the range before they convert it.
- An access outside a memory: `Runtime.MemInst.loadChecked` compares with the size first and
  answers a failure through its continuation, which the interpreter turns into `Left
  OutOfBoundsMemoryAccess` (`loadTrap`); `storeWordAt` and the bulk operations return
  `Nothing`. The tables do the same (`Runtime.TableInst`).
- `unreachable` is `Left UnreachableExecuted`, and a call beyond the bound on the depth of
  calls is `Left CallStackExhausted`.

**What the script does not show.** Reachability is by name, so a local variable named like a
definition adds an edge, which only makes the lists longer. Functions of other packages
(base, containers, vector, primitive) are not followed: that they terminate and raise only
what their documentation says is an assumption, and the names that the script treats as
partial are a list in the script. Exhaustion of memory or of the Haskell stack is outside.
These belong with the assumptions on GHC in the paper's appendix on type safety.

### The two small items

- `dir PATH : LEVEL` is the policy statement for a directory's level, and `preopen` is a
  synonym. `dir` is in `--help`, `README.md`, the case studies' policies and their README,
  and the documentation of `Validation.Policy`. A unit test checks that the two spellings
  parse to the same policy. The recorded result files are unchanged.
- The guide's rule names: item 3 above.

### Commits and verification

| Commit | What |
|---|---|
| `8991e09` | items 1, 3 and 4: `Findings.lean`, `SecWasmPrinted.lean`, the guide |
| `44a7bf5` | the statement `dir` |
| `bc768cc` | item 2: `scripts/step-inventory.py`, the two lists, the gate's stage, `laneAt` |

At `bc768cc`: the gate passes (240 unit tests, 72 WASI programs, 257 scripts, lint, 7
obligation checks, the step inventory, the samples); the suite gives 63,080 passed, 0 failed
and 2,122 skipped in both configurations; the 93 case studies give their recorded results;
the allocation of the nine reference workloads is unchanged. A clean `lake build` takes 57 s.
The axioms of the three cited theorems are as before: `noninterference` and
`machine_noninterference` depend on `propext`, `Classical.choice` and `Quot.sound`, and
`refinement` on `propext` and `Quot.sound`.

For the paper's numbers: the Lean development has 5,996 lines (the paper quotes 5,566), the
unit suite has 240 tests, and the obligations script still makes seven checks.

## Closing the gaps of the Lean core (the plan's items 5 to 9 of 2026-10-14)

One entry per item, each with its commit, the line count of `lean/WasmIfc/*.lean` after it,
and what changed in the statements that the paper cites. After every item `lake build` is
green without `sorry`, and the axioms of `noninterference`, `refinement` and
`machine_noninterference` are as before.

### Item 5: operations that trap (`169e993`, 6,074 lines)

The core has two new instructions, `partialBinop f` and `partialUnop f`, whose `f` is a
partial function (`Nat → Nat → Option Nat`, `Nat → Option Nat`). They stand for `IDiv`, `IRem`
and the conversions that trap. They are typed exactly as `binop` and `unop`. Their evaluation
rules have one premise more, that `f` is defined on the operands (`f b a = some v`), so a
division by zero has no evaluation, which is how the core says "traps".

**What changed in the statements.**

- `Instr`: two constructors more, `partialBinop` and `partialUnop`.
- `Typed`: two rules more, `partialBinop` and `partialUnop`, with the premises and the
  conclusion of `binop` and `unop`. In the paper's terms they are T+-Binop for a division.
- `Eval`: two rules more, with the premise that the operation is defined.
- `Machine.Basic` (and so `Step`): two basic steps more, with the same premise.
- No theorem's statement changed. `State`, `LowEq`, `WellTyped`, `Invoke`, `Config`, `Runs`
  are as they were. `rise`, `confine`, `ni`, `noninterference`, `refinement` and
  `machine_noninterference` now cover the two instructions.

For the paper: the proof case is that of the total operation. If both runs get past the
instruction, the function was defined in both, and where the result's label is public the
operands agree, so the results do. Whether the operation traps may depend on a secret
operand, and the theorem says nothing of a run that traps, as for the load check.
`Examples.lean` has 6 divided by 2, which runs, 6 divided by 0, which has no evaluation, and
the typing of a division of a secret.

### Item 6: any number of tables (`7030d7b`, 6,274 lines)

Every instruction on a table takes a table index, and so do `call_indirect` and
`return_call_indirect`. Each table has its own level, entries, size and limit. `table.copy` is
between two tables. `table.init` and `elem.drop` are new, with element segments in the state.

**What changed in the statements.**

- `Instr`: `tableGet x`, `tableSet x`, `tableFill x`, `tableSize x`, `tableGrow x` take the
  table `x`; `tableCopy xd xs` takes the table copied to and the one copied from;
  `callIndirect x ps b rs` and `retCallIndirect x ps b rs` take the table first. New:
  `tableInit x k` (table `x`, element segment `k`) and `elemDrop k`.
- `Ctx`: `table` is `Nat → Lab`, a level per table (it was one `Lab`).
- `Typed`: the rules of the table instructions and of the two indirect calls read `C.table x`
  where they read `C.table`. The premise of `tableCopy` is now
  `pc ⊔ ℓn ⊔ ℓsrc ⊔ ℓdst ⊔ C.table xs ⊑ C.table xd`: the level of the table copied from
  flows into the level of the table copied to, as `ITableCopy` asks (`lfrom`). New rules:
  `tableInit`, with the premise of `tableFill` (`pc ⊔ ℓn ⊔ ℓsrc ⊔ ℓdst ⊑ C.table x`; a segment
  is public), and `elemDrop`, without a premise under any pc, as `dataDrop`.
- `State`: `tbl`, `tsize` and `tcap` are indexed by the table (`tbl : Nat → Nat → Option Nat`,
  `tsize`, `tcap : Nat → Nat`). New field `elems : Nat → List (Option Nat)`, the element
  segments, of which a dropped one is empty.
- `State.sameTable s t x` is for one table `x` (it was `s.sameTable t`).
- `Eval`: the table rules name their table, and each bound is that of its table (in
  `tableCopy`, the range written is within `xd` and the range read within `xs`). New rules
  `tableInit` (a trap unless the range is within the table and within the segment) and
  `elemDrop`.
- `LowEq`: the clause on the table is now `∀ x, C.table x = L → s.sameTable t x`, for every
  public table. One clause more, after the one on data segments:
  `∀ k, s.elems k = t.elems k ∨ s.elems k = [] ∨ t.elems k = []`.
- `StRel` and `Conf`, the relations of the proof, change in the same two ways.
- `Machine`: `Basic` has the table steps with their indices and the two new ones;
  `Step.callIndirect` and `Step.retCallIndirect` look the entry up in their table.
- The theorems are stated as before, word for word. They say more through `LowEq` and `Typed`.

For the paper. Its definition of low equivalence should read "every table whose label is
public" in clause (iv), and "every data segment and element segment" in clause (vii). Its
figure has T+-Table-Get, T+-Table-Set, T+-Table-Size and T+-Table-Grow with the label of
"the table", which is now the label of the instruction's table, so the rules stand. The text
says that `table.copy` is typed like T+-Table-Set with three operands. Between two tables
the premise has a fifth label, that of the table copied from; with one table it is the
premise as printed. The text does not say how `table.init` and `elem.drop` are typed: as
`table.fill` and as `data.drop`. `Examples.lean` has a context with a public and a secret
table: a copy from the public one to the secret one is typed, the copy back has no typing,
and a `table.init` followed by `elem.drop` runs.

### Item 7: any number of memories (`1eb1b37`, 6,134 lines)

Every instruction on a memory takes a memory index, and `memory.copy` takes two. Each memory
has its own bytes, levels, size and limit. The second memory of a fixed size that the core
had, with its two copy instructions, is gone: it is the case of two indices. The line count
went down because one lemma on copies replaces three.

**What changed in the statements.**

- `Instr`: `load m w lm`, `store m w lm`, `memSize m`, `memGrow m`, `fill m lm` and
  `memInit m k lm` take the memory `m`; `copy md ms lm` takes the memory copied to and the one
  copied from. Removed: `copyTo` and `copyFrom`.
- `Typed`: the same rules with the index. No premise changed, because a memory has no static
  level: the levels are per byte, at run time. The rule of `copy` is the same within a memory
  and between two. Removed: the rules `copyTo` and `copyFrom`.
- `State`: `mem : Nat → Nat → Nat` and `lab : Nat → Nat → Lab` are indexed by the memory, and
  so are `size` and `cap` (`Nat → Nat`). Removed: `mem2`, `lab2`, `size2`.
- `Eval`: each rule reads and writes its memory, within that memory's size. In `copy` the
  range written is within `md` and the range read within `ms`. `memGrow m` grows the memory
  `m` up to its own limit. The three host calls read and write memory 0, which is WASI's.
- `LowEq`: the clause on bytes is `∀ m a, s.lab m a = L → t.lab m a = L → s.mem m a = t.mem m a`,
  for every memory. `s.size = t.size` and `s.cap = t.cap` are now equalities of functions: the
  size and the limit of every memory. Removed: the two clauses on the second memory.
- `StRel` and `Conf` change in the same way, and the relation `Limits` loses its part on the
  second memory.
- `Machine`: `Basic` has the memory steps with their indices; the steps for `copyTo` and
  `copyFrom` are removed.
- The theorems are stated as before.

For the paper. Clauses (ii) and (iii) of its definition of low equivalence should say "of
every memory". Its rules T+-Load, T+-Store, T+-Memory-Grow, T+-Memory-Fill and
T+-Memory-Copy stand as printed, with a memory index on the instruction. The appendix says
that the core has "two memories of labeled bytes": it has any number. `Examples.lean` stores
a secret byte in memory 0 and copies it to memory 1 with the level `L` declared: the program
is typed, it runs, and the byte of memory 1 is secret afterwards, since the level moved with
the value.

### Item 8, first: findings in the host (`Runtime.Wasi`), reported before the Lean model

Going through the 46 functions for their shapes, I found that the host does not keep what the
paper assumes of it. Two of the findings are leaks that I reproduced with compiled C under
the policy of the paper's own example (`dir /secrets : H`, `dir /log : L`, `stdout : L`): the
secret file's contents were printed on the public stream, and nothing trapped.

**Leaks (reproduced).**

1. *A rename moves a secret file into a public directory.* `path_rename` checks nothing about
   the two directories' levels. `rename("/secrets/pw", "/log/x")`, then `open("/log/x")`: the
   new descriptor has the level of `/log`, so `read` delivers the password as public bytes.
   `path_link` does the same with a hard link, in both directions: a public file linked into a
   secret directory takes secret writes that the public name then reads.
2. *A symbolic link leads out of its directory.* `symlink("../secrets/pw", "/log/l")`, then
   `open("/log/l")`: the host hands the path to the operating system, which follows the link
   into `/secrets`, and the descriptor has the level of `/log`. This is also an escape from
   the directory that `--dir` grants: only the path's text is checked against `..`, not what
   links on the way resolve to. A link that is already in a granted directory does the same.

Behind both is one missing invariant: a file must be reachable at one level only. The same
invariant fails, without any call, if two granted directories with different levels contain
one another (`--dir /data` public and `--dir /data/keys` secret: `keys/k` opens as public
through the first).

**A public status that depends on a secret.** The paper assumes that the status of a host
call depends only on its operands and on the public part of the state. Four places break it:

3. *The buffers' list of a read or a write.* `peekIovecs` lets the bytes of the iovec array
   be as secret as the descriptor. A pointer in it that is out of bounds makes the call return
   `EFAULT`, a public status, so one bit of a secret pointer shows (`fd_read`, `fd_pread`,
   `sock_recv`, `fd_write`, `fd_pwrite`, `sock_send`).
4. *A socket that does not block.* With `O_NONBLOCK`, `sock_accept`, `sock_recv` and `fd_read`
   return `EAGAIN` when nothing has arrived. On a secret socket that is a fact about the
   secret channel, and `poll_oneoff` labels the same fact with the socket's level. For
   `sock_accept` the descriptor table depends on it too.
5. *A seek relative to the end or to the position.* `fd_seek` returns `EINVAL` if the new
   position would be negative, which depends on the size or the position of the file, and the
   host labels both with the descriptor's level elsewhere (`fd_filestat_get`, `fd_tell`).
6. *The contents of a symbolic link.* `path_symlink` lets them be as secret as the directory,
   and its own status depends on them (empty, a leading `/`, bytes that are not UTF-8). The
   calls that follow a link (`path_open`, `path_filestat_get`, `path_filestat_set_times`,
   `path_link`) then succeed or fail by what the link names, and `path_open` changes the
   descriptor table by it.

**What the statuses do depend on, as the paper says.** Whether a name exists in a directory,
and whether it is a file, a directory or a link, decides the status of every `path_` call, in
a secret directory too. The paper states this ("the label of a directory protects the
contents of its files but not their names"). `fd_readdir` nevertheless delivers the names at
the directory's level, which is more careful than the assumption and not consistent with it.

**Not about flows.** An iovec array of length 0 and a `poll_oneoff` with no subscription run
into `EFAULT` (the count is an unsigned number from which 1 is subtracted), where the first
should succeed and the second return `EINVAL`.

All of these are fixed: the next entry says how.

### Item 8: the host, fixed (`0fe52a1`) and modelled (`8418282`, 6,494 lines)

**The fixes in `Runtime.Wasi`.** Each finding of the entry above is closed by the system's
one answer: what would leak traps (`SecretToHost`, named after the call) or is refused.

| Finding | Now |
|---|---|
| 1. rename or hard link between directories | `path_rename` and `path_link` trap unless the two directories have one level (`requireSameLevel`), in both directions: a file moved into a secret directory could still be read through a descriptor opened before, at the public level. |
| 2. a link that leads out of its directory | Every path is confined (`confine`): the host resolves the links on the way itself and returns `ENOTCAPABLE` if the result is not inside the directory the path was resolved in. A link in the last component is followed by the host, step by step under the same rule, and never by the operating system. This also closes the escape from the granted directory. |
| nested directories of different levels | The host refuses to start (`newHost`), and the command line reports it. |
| 3. the list of buffers | The iovec array may still be as secret as the descriptor: the password checker prints its verdict on the secret stream through a pointer and a length that the secret decides. But if the array has a secret byte, a failure of the part of the call that uses the buffers traps and is no status (`usingBuffers`). |
| 4. a socket that does not block | On a secret socket that has nothing, `sock_accept`, `sock_recv` and `fd_read` trap in place of `EAGAIN` (`unlessWouldBlock`). |
| 5. a seek from the end or the position | On a secret file, a failure of such a seek traps (the case of `FdSeek`). |
| 6. the contents of a link | They are a path and so public bytes (`path_symlink` reads them with `peekPath`). |
| lengths of 0 | An iovec array of length 0 is no buffer, and `poll_oneoff` without a subscription returns `EINVAL`. |

Only a secret descriptor or directory sees a change of behaviour, besides the confinement of
paths, so a run without a policy is as before: the WASI suite passes 72 of 72. The unit suite
has four new tests (a rename between levels, a link that leads out, nested directories, a
fault that a secret iovec array decides): 244 tests. The two
programs that leaked now end with a trap (`rename`) and with a failed `open` (`symlink`).
The gate passes, the suite gives 63,080 passed and 0 failed in both configurations, and the
93 case studies give their recorded results.

What the host still assumes is in `TODO.md` ("What the host still assumes"): the operating
system's own failures on a secret file or connection, no hard link between granted
directories of different levels made outside the run, and no change to a link between the
check of a path and its use.

**For the paper.**

- The sentence "the evaluation rules assume that the status of a host primitive depends only
  on its operands and on the public part of the state" was false of the implementation in
  four places and is true now, up to the three assumptions above. In Lean it is no assumption
  any more: it is the type of `hostStatus`.
- "The label of a directory protects the contents of its files but not their names" needs one
  more thing said: a file has one level because it is in one directory, which the host now
  enforces (confined paths, no move between levels, no nesting of levels). Before this, the
  claim was not true of a program that renames.
- The trusted computing base has this code in it: `confine`, `requireSameLevel` and the check
  in `newHost` are plain Haskell with no evidence type, as the other checks of the host
  driver (`tab:trust` should list them with the driver).
- A trap of the host is now also "a status that a secret would decide". The case studies do
  not meet it.

**The Lean model.** The core has six host primitives, one for each shape of rule. `hostRead`,
`hostWrite` and `hostOpen` were there. New: `hostGet` (public data from no descriptor),
`hostCtl` (changes to the descriptor table, a directory or a position) and `hostPoll`
(`poll_oneoff`). `lean/STATEMENTS.md`, section 8, has the shape of each of the 46 functions
with the line of its case in `Runtime.Wasi` and what there makes it so: 8 read, 3 write, 2
make a descriptor, 10 give public data, 21 change the table, a directory or a position, 1
polls, and `proc_exit` has no rule.

**What changed in the statements.**

- `Instr`: three constructors more, `hostGet`, `hostCtl`, `hostPoll`.
- `Typed`: `hostRead` and `hostWrite` now leave a public value, the status, on the stack
  (they left nothing). New rules `hostGet`, `hostCtl`, `hostPoll`, of the same form as the
  others: a public pc, public operands, a public status.
- New definitions in `Defs.lean`: `hostStatus`, an opaque function of the call, its operands,
  the descriptor table, the names, the files' channels, the channels' levels and the size of
  the first memory; `State.status`; `ctlFdt`, `ctlNames`, `ctlFile` and `reposition`, opaque
  functions for what `hostCtl` makes of the table, the directories and a position, with
  `State.control`; `State.polled`, `State.pollLevel`, `pollEvents` and `State.events` for a
  poll. `State` has no new field.
- `Eval`: `hostRead` and `hostWrite` have the premise that the status is 0 and push it. Each
  host primitive but `hostOpen` has a second rule, for any other status, which leaves the
  state as it was and pushes the status (`hostReadFail` and so on). `hostOpen` is unchanged:
  its two rules already give its status from the names. New rules `hostGet`, `hostCtl`,
  `hostPoll` and their failing ones.
- `Machine.Basic`: the same steps.
- `LowEq`, `StRel`, `Conf`, and the statements of the theorems: unchanged.
- New lemmas that carry the argument: `StRel.status` (two runs give a call the same status;
  the one place where the proof uses that a status depends on nothing secret),
  `StRel.control`, `StRel.events`.

How the noninterference proof goes for the new cases: the operands are public, so they are
the same in both runs, and so is the status, hence both runs succeed or both fail. For
`hostGet` the source is a public channel, which has the same left to read in both runs. For
`hostCtl` the new table and directories are functions of equal things, and a position moves
on a channel that is either public, with the same contents in both runs, or secret, where
nothing is compared. For `hostPoll` the level is the same in both runs, and if it is public
every channel polled is public, so the reports agree.

What the model leaves out, said in the guide: a failure of the operating system on a secret
file; `proc_exit`, which has no rule, so that a run that exits is as one that traps and the
theorem says nothing of it (that the exit code is public follows from the typing of the call,
which is under a public pc with a public operand, but it is not proved); the count that
`fd_write` stores; and that `fd_seek` stores the new position besides moving it.

### Item 9: value types, and with them 64-bit memories (`a2ab617`, 7,066 lines)

**How it is done, which is not how the plan put it.** The plan asked for the stack type of
`Typed` to become a list of labelled value types. I added the value types as a layer on top
and left `Typed` as it is. `ValueTypes.lean` (572 lines) has a second judgment, `ValueTyped`,
with labelled value types over the same instructions, and the lemma `ValueTyped.erase`: a
derivation with value types is, with the types forgotten, a derivation of `Typed`. The
theorems for a module typed with value types then follow from the existing ones in one line
each. The reason is that the semantics does not look at types (a value is a number, an
operation a function on numbers), so a change of `Typed` itself would have touched every
proof case to carry a type along that no proof uses. The layer says the same thing, "the
proofs do not change in content", as a lemma. The file imports the rest and nothing imports
it, so the commit can be read and reverted on its own, as the plan asked.

**What changed in the statements: nothing that the paper cites.** `Typed`, `WellTyped`,
`Eval`, `State`, `LowEq`, `Step`, `Runs` and the three theorems are as after item 8. New, all
in `ValueTypes.lean`:

| Lean name | What it is | Axioms |
|---|---|---|
| `VTy`, `LTy`, `VSTy`, `labelsOf` | the value types (`i32`, `i64`, `f32`, `f64`, `v128`, `funcref`, `exnref`), a labelled type `t⟨ℓ⟩` as a pair, a stack type as a list of them, and its labels | |
| `VFuncTy`, `VCtx`, `VCtx.erase` | function types and the context with value types; the context has an address type for each memory and each table, `i32` or `i64` | |
| `ValueTyped` | the judgment `Λ ⊢ e : Π | st ⇒ Π' | st'` with `st` of labelled value types: one rule for each rule of `Typed` (but `iter`, which no program contains), with the operand types of `Syntax.Instructions` | |
| `ValueTyped.erase` | `ValueTyped C Ls e P st P' st' → Typed C.erase (Ls.map labelsOf) e P (labelsOf st) P' (labelsOf st')` | `propext` |
| `VFunc`, `WellValueTyped`, `WellValueTyped.erase` | functions and well-typed modules with value types, and that such a module is `WellTyped` | `propext`, `Quot.sound` |
| `value_typed_noninterference` | `noninterference` for a module that is `WellValueTyped`: the hypotheses and the conclusion read the function's type through `labelsOf` and the context through `VCtx.erase` | the three standard ones |
| `value_typed_machine_noninterference` | the same for two runs of the machine | the three standard ones |

**What the rules with value types say beyond the labels.** An address has its memory's
address type, and so have `memory.size`'s result and `memory.grow`'s operand and result; the
same for a table. The count of a copy between two memories or tables is `i32` unless both are
64-bit (`minAddr`, the `MinAddr` of `Syntax.Instructions`). A condition (`select`, `if`,
`br_if`, `br_table`) and every operand and result of a host call are `i32`. A table holds
`funcref`s, and `throw_ref` takes an `exnref`. The two operands of an operation on two values
have one type; its result may have another (a comparison gives `i32`, a conversion another
type), because the core's `binop` and `unop` are any functions and carry no type. A tag
carries a list of value types, and a clause's label has those types, with `exnref` on top
for a clause by reference.

**For the paper.**

- The sentence that the core "has a single value type, so it treats the numeric and vector
  instructions alike" can become: the proofs are on labels, and a judgment with labelled value
  types `t⟨ℓ⟩`, with address types for 64-bit memories and tables, erases to it
  (`ValueTyped.erase`). If the paper's table of notation should show `t⟨ℓ⟩`, it would cite
  `ValueTyped` and `WellValueTyped` in `ValueTypes.lean` for the judgment and the well-typed
  module, and `value_typed_noninterference` for the theorem. Say if you would rather have
  the names `Typed` and `noninterference` on the value-typed ones: that is a renaming, which
  I did not do since the statements are under review.
- Two things remain outside, and the guide says so: an instruction of the core carries no
  value type (an operation is any function on numbers), and a value is a natural number with
  no range, so the wrapping of a 32-bit address is not modelled. With these, "64-bit
  memories" means that the typing distinguishes the address types, and the semantics has no
  width.

### After items 5 to 9: what the core leaves out

The paper's sentence was that the core "leaves out 64-bit memories, linking, and most WASI
calls". After these items it leaves out: linking of several modules; the pass that splits
locals into webs and the inference of labels, which happen before typing; declassification;
the numeric and vector instructions one by one, and the ranges of the value types;
`proc_exit` and the operating system's failures on a secret file. The first two are the ones
the plan set aside as new proofs. `lean/STATEMENTS.md`, "Outside the core", has the list.
The development has 7,066 lines in ten files, no `sorry`, and its theorems depend on
`propext`, `Classical.choice` and `Quot.sound` only. A clean `lake build` takes about a
minute and a half.

### The two proofs set aside: how I would state them

The plan asked for half a page on linking and on the splitting of locals, and to stop there.

**Linking.** The core's module is one list of functions with one state. A world of modules
(`Runtime.Link`) is several instances that import functions, memories, tables and globals
from one another, where an imported object lives in the instance that defines it and is
handed over when control passes. I would not add worlds to the semantics. I would state that
a world is one module of the core:

- *Flattening.* A function `flatten` from a world to a context and a list of functions: the
  function spaces are laid end to end, every instruction's indices (functions, globals,
  memories, tables, tags, segments) are shifted by where its module's spaces start, and an
  import's index is replaced by the index of the export it is linked to.
- *Typing is kept.* If every module of the world is `WellTyped` in its own context, and every
  import is linked to an export of the same type (a function type with its bound, a global's
  level, a table's level, a tag's arity; `Runtime.Instantiate` checks this), then the
  flattened module is `WellTyped` in the flattened context. The lemma behind it is that
  `Typed` is stable under a renaming of indices that the context respects. This is routine.
- *The machine is the same.* A run of the world from an export is a run of the flattened
  module from the same function, with the state of the flattened module being the homes'
  objects. This is the new proof: it has to show that pulling an imported object when control
  comes to an instance and pushing it back when control leaves gives every instruction the
  object as its last writer left it. In Lean it would be a refinement like `refinement`, from
  a machine with a current instance and a table of homes to `Step`.

`noninterference` for a world is then the theorem for the flattened module. The cost is in
the third point, and it is about `Runtime.Link`, not about flows.

**The splitting of locals into webs.** The interpreter runs the elaborated program, which is
the program after the split, and the theorems are about that program. So the split does not
enter noninterference. What is missing is that the elaborated program computes what the
binary says, which is conformance, and for the split a statement of its own:

- Let `split f` be the function with its locals renamed by `Validation.LocalWebs`, and let
  `web p x` be the local that a use of `x` at the position `p` is renamed to.
- *Invariant.* Two states are related at a position `p` if they agree on everything but the
  locals, and `s.loc x = s'.loc (web p x)` for every local `x` that some definition reaches
  at `p`.
- *Statement.* If `Eval F n ls e σ s o` for a body `e` and the states are related at its
  start, then `Eval F' n ls (split e) σ s' o'` with outcomes that carry the same values and
  states related at the end, and conversely. The values of the stack, the globals, the
  memories and the host are the same, so the two programs are indistinguishable from outside.

The proof needs the reaching-definitions analysis to be sound (a use reads a local that only
the definitions reaching it write), over structured control flow with a loop iterated to a
fixed point, and the merging of webs after inference (`mergeWebs`) to be a coarser renaming
of the same kind. It is a compiler-correctness proof for one pass. Today the evidence is the
suite: all 63,080 assertions run through the elaborator with the split on.

### The paper's names on the judgment with value types (`7e24625`, 7,099 lines; Daniel: "Take the names that are on the paper")

| Paper's name | Now | File | Axioms |
|---|---|---|---|
| `Typed`, `WellTyped` | the judgment with labelled value types `t⟨ℓ⟩`, and a module typed by it | `ValueTypes.lean` | |
| `rise` | `lem:rise` for `Typed` | `ValueTypes.lean` | `propext` |
| `noninterference` | the theorem for a `WellTyped` module | `ValueTypes.lean` | the three standard ones |
| `machine_noninterference` | the same for two runs of the machine | `ValueTypes.lean` | the three standard ones |
| `leak_not_typed`, `call_after_secret_branch_typed`, `write_after_public_branch_typed` | about `Typed`, in contexts with value types (`leakTypedCtx` and so on) | `Findings.lean` | `propext` |
| `Eval`, `Out`, `Invoke`, `Ended`, `StkRel`, `LowEq`, `Config`, `Step`, `Runs`, `refinement`, `Step.sem`, `Runs.sem` | unchanged | as before | as before |
| `confine`, `ni`, `tini` | unchanged: lemmas of the proof, about the label part | as before | as before |

The label part, on which every proof is, has new names: `LTyped`, `WellLTyped`,
`rise_labels`, `noninterference_labels`, `machine_noninterference_labels`,
`leak_not_typed_labels` and the like. `Typed.erase` and `WellTyped.erase` connect the two.

For the paper's table of notation: the judgment and the well-typed module (`Typed`,
`WellTyped`) and `noninterference` are now in `ValueTypes.lean`, and `machine_noninterference`
too. `Defs.lean` has the label part and the semantics, `Statement.lean` low equivalence and
`Invoke`. The appendix's sentence that the Lean rules "are the label part of the rules" can
become: the Lean judgment has the value types, and the proofs are on its label part, which
`Typed.erase` connects. `lean/STATEMENTS.md` says which name is which at its start.

### The host refuses instead of trapping (`3f86d62`; Daniel: the traps "sound a bit hacky", "there has to be a better standard answer")

This supersedes the traps in the table of "Item 8: the host, fixed and modelled". Those traps
depended on what happened in a run (no data yet on a non-blocking secret socket), so a
program could pass its tests and stop in use. Now the host refuses an operation whose outcome
would tell a secret before it makes it, with an ordinary status that depends only on the
operands and on the levels of the descriptors, which are public. This is the capability
discipline that WASI has already (`ENOTCAPABLE`), extended to levels.

| Case | Status now | Why it tells nothing |
|---|---|---|
| a secret socket made non-blocking (`fd_fdstat_set_flags`, `sock_accept` with the flag) | `ENOTSUP`, in every run; reads on a secret socket wait, and a poll reports at the socket's level | it depends on the socket's level |
| a seek back from the end or the position of a secret file | `ENOTSUP`, whether or not it would land before the start | it depends on the operands and the file's level |
| a rename or a hard link between directories of different levels | `EXDEV`, as between two file systems; a program falls back to a copy, which the checks of reads and writes govern | it depends on the directories' levels |
| a buffer out of bounds through a secret pointer in the list of a read or a write | the trap for an access out of bounds of the memory, as a `store` to a bad address | WebAssembly's own trap; a trap is outside a termination-insensitive theorem |

The one trap left at the host boundary is SecWasm's check that no secret byte goes where it
may not (a public descriptor, a path). The unit suite has 245 tests (one new: a secret socket
is not made non-blocking); the gate, both configurations of the suite (63,080 passed, 0
failed) and the 93 case studies pass. The program that renamed the password into the public
directory now gets `EXDEV` and stops by itself. The Lean model has these statuses already,
since `hostStatus` takes the channels' levels.

For the paper: the rule to state is "the host refuses what would tell a secret, with a status
that depends on the descriptors' levels"; the only traps are the flow check and the access out
of bounds. A more precise design, for the future work: a status declared secret in the policy
(an import can already be declared with a secret result) would let the host answer as WASI
says, with the type system treating the answer as a secret, checked at run time as a load is
(`TODO.md`).

## Audit: does the Lean model the paper faithfully? (2026-10-14, Lean at 7e24625, paper at Overleaf 9ee893e)

Read rule by rule against appendix B's three figures and the sixteen rules cited from SecWasm,
the evaluation figure, Definition `def:attacker`, Theorems `lem:swp-ni`, `lem:refinement` and
`thm:tini`, and the host paragraph of Section 3.6. Verdict: every rule and every statement that
the paper marks with the Lean badge is in the Lean in the paper's form, with the differences
below. None affects soundness; four need a sentence in the paper, and one is a choice.

**A. Where the paper and the Lean state a rule differently.**

1. *The premise `ℓ ⊑ τ2` of T+-Func is not in `WellTyped`.* The Lean puts it where the proof
   uses it: `callIndirect`, `retCallIndirect` and `callRef` have the premise `AllGe b rs`, that
   the results of the expected type are at least its bound. In the paper, T+-Call-Indirect and
   T+-Call-Ref have no such premise, and T+-Func has `ℓ ⊑ τ2` for every declared function. The
   two systems agree on every program whose indirect calls can proceed: in the paper's, a
   function that the run-time check accepts at an expected type `τ1 -ℓf-> τ2` has bound at
   least `ℓf` and results `τ2`, so by its own T+-Func `ℓf ⊑ τ2`. A paper-typed program with an
   expected type that violates it (`[] -H-> [L]`) has no Lean typing, and its call traps in
   every run. The implementation checks the premise for every type of the module (type
   section included), so for it the two agree. For the paper: either add to T+-Call-Indirect
   and T+-Call-Ref the side condition that the expected type is well formed (`ℓf ⊑ τ2`), which
   is what the policy stage checks, or say in the appendix that the Lean carries the premise
   there and not in T+-Func.
2. *T+-Br-Table's `d = max_j i_j`.* The Lean rule has `∀ t ∈ targets, t ≤ k` and raises down to
   `k`: any depth at or beyond the deepest target. The Haskell type is the same
   (`TableReach` of any depth, the targets as `Elem`s within it); the elaborator always takes
   the deepest target. A derivation with `k` beyond the deepest target raises more pcs and is
   proved sound. So the paper's rule is the instance the elaborator builds, and the Lean rule
   is the type. No change needed; if the paper wants `d = max` in Lean, that is a one-line
   change to the premise (`k = max`), which I have not made since the statements are under
   review.
3. *The witness on preserved globals of T+-Loop.* The text of appendix B.2 says of a block, a
   loop, an if and a try_table that "the pc `p` with which the body ends flows to the pc in
   force after the construct". For a loop, the Lean (`Restores C pcL P1 keep`) and the Haskell
   (`Restores pcLoop pcs'`) use the loop's pc `pc_L`, which is at least `p`. The text should
   say `pc_L` for the loop.
4. *`clauses(c*, Λ)`.* The caption of the third figure says a clause's label has a type that
   "consists of the public values of the clause's tag". The Lean (`ClauseOk`) and the Haskell
   (`Handler`, with a `SegmentFlows` to the target) ask only that the label take as many
   values as the tag carries (one more for a clause by reference): the values are public and
   flow into any label. "whose type takes the public values of the clause's tag" is the exact
   wording.
5. *Rules the paper does not print and the Lean has:* `tableCopy` between two tables with the
   source table's level in the premise, `tableInit`, `elemDrop`, the three host primitives
   `hostGet`, `hostCtl`, `hostPoll`, and `iter` and `dup`, which no program contains (`iter`
   is how a loop runs; `dup` is what `br_on_null` elaborates to). All reported in the entries
   of items 6 and 8 above. T+-Relabel on one value is the case of `relabel` (the Lean has only
   `relabel_results`) with the other labels unchanged.

**B. Where the semantics and the statements differ in form.**

6. *The outcome grammar.* The paper's `o ::= end | br_i | exn_t`. The Lean has a fourth
   outcome, `tailExn`, for an exception that leaves the callee of a tail call: the function
   that made the tail call is gone, so its own `try_table`s do not see the exception, and it
   is an ordinary exception for the caller. The refinement proof found that without it `Eval`
   let a `try_table` around a tail call catch the callee's exception, which the machine does
   not do. The paper's grammar and the caption of `fig:eval` (`exits`) should name it, or the
   text should say that an exception that leaves a tail call is not offered to the function's
   handlers.
7. *`⟨f(a), s⟩ ⇓ ret(r, s')` and the initial configuration.* Section 3.2 defines the call's
   evaluation without the comparison of the function's preserved globals at its return, and
   Section 4.3 says the initial configuration's control stack `Entry` is empty. The Lean
   `Invoke` has `Kept f.keep s t`, `Config.entry` runs the body over a boundary that carries
   the comparison, and the Haskell `startFunction` does the same ("the entry function is held
   to what every callee is"). E+-Call in `fig:eval` relies on the same `ret`. One clause in
   each place: the call returns only if the globals the function compares hold what they held
   at the call.
8. *The state.* Section 3.2 lists the globals, the memories, "the table", the descriptors, the
   data segments and the exceptions. The Lean state has any number of tables, the element
   segments, and the local variables (which the paper keeps outside the state, as the `F` of a
   configuration), plus the names of the files in each directory and the channel of each
   file, which the paper's clause (v) covers. Say "the tables" and "the data and element
   segments".
9. *Descriptor labels are not inherited in the model.* Section 3.6 says a descriptor inherits
   the label of the directory in which the file is opened. In the Lean, a file is a channel
   with a level fixed for the run (`State.file`, `State.chan`), and `hostOpen` gives the new
   descriptor the file's channel; nothing relates that level to the directory's. The model is
   the more abstract one, and the theorem holds for any assignment of levels to files that does
   not change during the run. The inheritance of Section 3.6, with the three checks of the
   host (confined paths, `EXDEV` between levels, no nesting of levels), is what makes the
   level of a file fixed and equal to its directory's. The last row of `tab:trust` ("no file
   is linked into two directories with different labels") is this assumption; it could say
   "each file has one label for the run, that of its directory, which the host's checks on
   paths, renames, links and nested directories ensure".
10. *`lem:refinement` and `thm:tini`* are stated for a run that returns. `refinement` and
    `machine_noninterference` also cover a run that ends by an exception (the second case of
    `lem:swp-ni`). The paper may say so or leave it.
11. *`lem:rise`* has the hypothesis `|Π| = |Π'|`; the Lean `rise` has none and proves the
    lengths equal (`SFlows` relates lists of one length).

**C. Verified as matching, nothing to change.** The sixteen rules from SecWasm (`const`,
`unop`, `binop`, `drop`, `select`, the locals and globals, `load`, `store`, `memory.size`,
`memory.grow` with its public pc and argument, `nop`, and T-Seq built into every rule);
T+-Block, T+-If, T+-Br, T+-Br-If, T+-Return (the outermost label is the function's result
type), T+-Unreachable, T+-Call, T+-Return-Call, `return_call_indirect`, T+-Throw,
T+-Throw-Ref, T+-Try-Table (body under `L :: L :: Π_r`, a clause's branch raises nothing),
T+-Memory-Fill, T+-Memory-Copy, `memory.init`, `data.drop`, the four table rules,
T+-Set-Global-Preserved (`ℓ ⊑ pc`; the global's public label is the theorem's hypothesis),
the witness on preserved globals of block, if and try_table (`Restores`) and of a function's
return (`WellTyped`'s disjunction, the Haskell's `ReturnsWith`); the five rules of
`fig:eval`; the run-time checks of a load and an indirect call as premises; `select`'s and
`binop`'s operand order; the host rules of Section 3.6 (what a read stores is at the
descriptor's level, a write checks every byte, paths and the other inputs are public, a poll
reports at the join); the eight clauses of `def:attacker`, in order, with the two extra
hypotheses that appendix B.4 already names; the attacker's three observations in the
conclusion; and the statement of `lem:swp-ni` word for word.

**D. What the Lean leaves out, for the appendix's "Scope".** A value is a natural number
with no range, so the wrapping of a 32-bit address or sum is not modelled, and an operation
is any function on numbers, so the numeric instructions are not modelled one by one; the
run-time check of an indirect call compares the labels of the expected type, not its value
types; `proc_exit`; the operating system's failures on a secret file; linking; the pass that
splits locals and the inference of labels; the initial labelling of memory from the policy's
regions (the initial state is any state).

**E. The paper's description of the Lean is behind the code.** Not a question of the Lean's
faithfulness, but the reviewer will compare. "approximately 6,100 lines" (7,099); "with a
single value type" and "It leaves out 64-bit memories, linking, and most WASI calls"
(Section 7.2 and appendix B.4): the value types with address types and the six host shapes
are in, linking is not; "at 48ac063" (7e24625); `tab:lean`'s files after the renaming of this
morning: `Typed` and `WellTyped` are in `ValueTypes.lean`, and so are `noninterference` and
`machine_noninterference` (`Defs.lean` has `LTyped` and `WellLTyped`, `Statement.lean`
`noninterference_labels`, `Machine.lean` `machine_noninterference_labels`); `tab:trust`'s row
"The features outside the mechanized core (value types, 64-bit memories, linking, other WASI
calls)" is now "linking, and the ranges of the value types"; appendix B.4's "host calls that
read, write, and open files" is now six shapes with every WASI function assigned to one
(`lean/STATEMENTS.md`, section 8).

### After the audit: the Lean changed (`9c32712`, 7,123 lines) and the paper edited (Daniel: "Fix and extend the Lean formalization and then update the paper to match")

**What changed in the statements.**

- `WellTyped` and `WellLTyped` have the premise of T+-Func that the function's results are at
  least its bound (`AllGe f.ty.bound f.ty.results`). The rules `callIndirect`,
  `retCallIndirect` and `callRef` no longer ask it of the expected type: they have the
  premises the paper prints and nothing more. The proof gets the secrecy of the results from
  the callee's own type where two runs call different functions. Item 1 of the audit is
  closed: the two systems now have the same rules.
- `Eval.hostOpen` and `Basic.hostOpen` have one premise more: the channel of the file opened
  has the level of the directory's channel (`s.chan (s.file c name) = s.chan c`). A descriptor
  inherits the level of the directory its file is opened in, as Section 3.6 says. Item 9 of
  the audit is closed; the host's checks on paths, renames, links and nested directories are
  what keep the premise true, and `tab:trust` says so.
- `proc_exit` is in the core as `hostExit`: typed under a public pc with a public code and the
  output stack free, like `unreachable`, and without an evaluation rule or a machine step. A
  run that exits has no outcome, as a run that traps. The guide's table of the 46 functions
  gives every one a primitive.
- Nothing else moved. The axioms of `noninterference`, `machine_noninterference` and
  `refinement` are as before.

**The paper, edited on the `paper` branch (submodule `paper/current`, branch
`prose-rewrite`, committed and not pushed).** Each edit is what the audit asked for, in the
paper's own words:

| File | Change |
|---|---|
| `03-findings.tex` | the state has "the tables" and "the data and element segments"; the outcome grammar has the fourth outcome $\mathsf{exn}^{\mathrm{tail}}$ with one sentence on it; $\langle f(a), s\rangle \Downarrow \mathsf{ret}(r, s')$ includes the function's comparison of preserved globals; T+-Br-Table's premise is $\max_j i_j \le d$ in `fig:swp-rules` and the text says the elaborator takes the deepest target |
| `04-core.tex` | the initial configuration's `Entry` holds the invoked function's comparison |
| `07-metatheory.tex` | the mechanization paragraph: 7,100 lines, any number of memories and tables, the value types with address types, a host primitive per shape; only linking is left out; the verify box names 9c32712 |
| `B-proofs.tex` | T+-Br-Table's premise as above; the witness on preserved globals says $p$, or $\pc_L$ for a loop; the caption of `fig:wrules3` says the tag's values flow into the clause's label, with the reference in front for a clause by reference; the "Scope" paragraph of appendix B.4 rewritten (seven host primitives, the status as a definition, value types by erasure, what is left out); `tab:lean` points `Typed`, `WellTyped`, `rise`, `noninterference`, `machine_noninterference` at `ValueTypes.lean`; the step-inventory box notes the counts are unchanged (the draft no longer has the figure of evaluation rules, so its caption's `exits` needed no change) |
| `A-deviations.tex` | `tab:trust`: the row on features outside the core is "linking, the ranges of the value types"; the host row says each file has one label for the run, that of its directory, kept by the host's checks |

Not changed in the paper, and open for the paper track: Section 3.6's description of the host
says "A link or a rename requires its two directories to have equal labels", which is now a
status (`EXDEV`) and no trap, and nothing there says that a secret socket is not made
non-blocking; the "Runs that trap" paragraph could say that the host's refusals are statuses,
not traps. The audit's items 10 and 11 (the exception case of `refinement`, `rise` without a
length hypothesis) were left as they were.

## Where coverage stands (2026-10-12, for the paper's claim)

Supported, with the 3.0 suite passing on all of it: **WebAssembly 3.0 without garbage
collection**, that is every instruction and type of WebAssembly 2.0, linking between modules
included, and of what 3.0 adds, several memories, 64-bit memories and tables, tail calls,
extended constant expressions, the relaxed vector instructions, typed function references and
exceptions. Two qualifications:

- exceptions are thrown and caught under a public pc only (a rule, not a gap in coverage);
- nullability and the function type behind a reference are checked by a validator beside the
  typed program, not by its types (see "Typed function references").

The relaxed vector instructions (2026-10-12) let an implementation choose among a few results.
Ours are those of the 2.0 instruction each one relaxes (`relaxed_swizzle` is `swizzle`,
`relaxed_laneselect` is `bitselect`, and so on), a product rounded before the sum for
`relaxed_madd`, and saturating sums for the two dot products. Their rule is the rule of every
vector operation. All seven scripts of the suite pass in full (77 assertions).

Not supported: garbage collection, as decided.

Every feature that clang 23 (wasi-sdk 34) and rustc 1.99 enable by default for
`wasm32-wasip1` is supported. **The suite: 63,080 assertions pass, none fails, 2,122 are
skipped: 877 on modules that use garbage collection, and 1,245 malformed modules given as
text, which the harness does not run.** Nothing else is skipped: 174 of the 257 scripts run
without a skipped assertion.
