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
  10 of 14 run in both configurations (none of them loads the secret files' bytes); 4 are
  rejected, because an `assert` on data read from the secret file calls `__assert_fail` under a
  secret pc, whose prologue writes `__stack_pointer`.
- **(d) PolyBench** (ten kernels, MINI), data secret where `main` writes it
  (`store-default func main : H`, a new statement), loads of `main` secret: with the printing
  compiled out, all ten type and run with two policy lines and no further declaration, also
  under SecWasm's restrictions. Printing the results with `fprintf` is rejected in every
  kernel: `printf_core` branches on the value, and the functions it calls then run under a
  secret pc and write `__stack_pointer`.
- **(e) Lift shapes**: no program of (a)–(d) is accepted by the lift-free rules and rejected
  with `secwasm-restrictions` (`run.py`'s `lift_shape` is false throughout).

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
4. **Error checks after reads** (§6.7 "Statuses and errors") did not arise in the password
   checker because the driver still writes byte counts as public (delta 2 is open); they will,
   once it labels them with the descriptor's label.

## Not done yet

- Item 9: the cost of the labels (timing sweep, native Linux, suites at the submission commit).
- Items 10–11: typed obligations on the main line; the complete WASI boundary rule.
- Items 12–14: Lean; the rest of WebAssembly 3.0; WASI sockets.
