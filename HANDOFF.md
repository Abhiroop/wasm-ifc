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
- Sockets still return `ENOTSOCK`, `proc_raise` `ENOSYS`.
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

## Findings that bear on the paper's claims

1. **The shadow-stack pointer.** `__stack_pointer` is a public global that every non-leaf C
   function writes in its prologue and restores in its epilogue. SecWasm's rules forbid the
   write under a secret pc, so no such function can be called in a secret context: this is
   what rejects `printf` of a secret and `assert` on a secret. A sound treatment needs a rule
   for balanced save and restore, or a secret stack pointer with its cost. Open (TODO.md).
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

## Not done yet

- Item 9: the cost of the labels (timing sweep, native Linux, suites at the submission commit).
- Items 12–14: Lean; the rest of WebAssembly 3.0; WASI sockets.
