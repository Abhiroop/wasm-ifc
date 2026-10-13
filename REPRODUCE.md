# Reproducing the evaluation

For each table and number of the paper's evaluation, the command that produces it, where the
result is recorded in this repository, and how long the command takes on the machine of the
paper (AMD Ryzen 5 3600, 12 threads, Linux 5.14, GHC 9.12.2). Commands run from the
repository's root. The numbers in the paper are those of commit `67e5597` for the suites and
the case studies and of `c2a3f4b` for the timings; the interpreter's source is the same at
both but for the message of one trap.

## Setting up

```sh
git submodule update --init                 # the two official test suites
cabal build all --enable-tests --enable-benchmarks
./bench/tools/fetch.sh                      # wasi-sdk 34, wabt, wasm-tools and the other runtimes, into ~/.local/wasm-bench-tools
./bench/build.sh && ./bench/c/build.sh && ./bench/c/build-silent.sh     # the kernels, CoreMark and PolyBench
for study in password service frames polybench secwasm; do ./casestudies/$study/build.sh; done
rustup target add wasm32-wasip1 && ./casestudies/password-rust/build.sh     # the checker in Rust, optional
```

The first build takes about 15 minutes. `wasm-tools` 1.261 or later must be on the `PATH` for
the specification suite, and `wat2wasm` (wabt) for the examples written as text.

## Conformance (RQ1)

| Claim | Command | Recorded in | Time |
|---|---|---|---|
| 63,080 assertions of the WebAssembly 3.0 suite pass, none fails, 2,122 are skipped, from 257 scripts | `WASM_IFC_SPEC_REPORT=spec.jsonl cabal test wasm-ifc-spec` | the test's last line | 2 min |
| the 2,122 skipped: 877 garbage collection, 1,245 malformed text | `./scripts/spec-report.py spec.jsonl` | `TODO.md`, "WebAssembly coverage" | 1 s |
| the same with SecWasm's restrictions on | `WASM_IFC_SECWASM_RESTRICTIONS=1 cabal test wasm-ifc-spec` | | 2 min |
| 72 of 72 programs of the WASI suite: 14 C, 46 Rust, 12 AssemblyScript | `cabal test wasm-ifc-wasi` | the test's last line | 20 s |
| which compilers built the suite's binaries | `wasm-tools print FILE \| grep -A4 @producers` on a binary of each directory | `HANDOFF.md`, "The paper's numbers" | 1 s |
| everything at once: format, `-Werror` build, the three suites, lint, the samples | `./scripts/gate.sh` | | about 10 min |

## Errors that the types rule out (RQ2)

| Claim | Command | Recorded in | Time |
|---|---|---|---|
| 100,000 generated programs, 36 % accepted, no interference | `WASM_IFC_NI_CASES=100000 cabal test wasm-ifc-test --test-show-details=direct --test-options='--match "two runs"'` | the test's output: the accepted are the first three classes | 50 s |
| a wrong step of the machine does not compile (the load check and the indirect call's check) | `./test/obligations-must-not-compile.sh` | its output, seven checks | 1 min |
| GHC rejects SecWasm's printed rule for `br_table` | the same script | `HANDOFF.md`, "GHC's error for SecWasm's printed `br_table` rule" | |
| mutants found after 1,666 and 5,057 programs | by hand: the mutations and the seeds are in `HANDOFF.md` ("Phase 1", "Preserved globals") | `HANDOFF.md` | |

## Programs with secrets (RQ3)

| Claim | Command | Recorded in | Time |
|---|---|---|---|
| every row of the section: SecWasm's 11 examples and the 7 programs of the findings, the password checker and its variants, the service, the 14 C programs of the WASI suite under two policies, the 10 PolyBench kernels in three builds, the program with a stack frame | `./casestudies/run.py` | `casestudies/results/2026-10-13-67e5597.json` (per program: policy lines, outcome with rule and site, labels inferred, whether SecWasm's restrictions accept it) | 100 s |
| the checker's run, the traps of its leaking variants and the rejection of the naive one, as a user sees them | the commands of `HANDOFF.md`, "The overview's example" | there | 1 s |
| no accepted program needs the absence of the lift | the field `secwasm_restrictions` of the same file | | |

## Comparison with WANILLA (RQ4)

| Claim | Command | Recorded in | Time |
|---|---|---|---|
| the verdict for each of the 312 specifications, under both translations | `casestudies/wanilla/oracle.py [ARTIFACT]`, after unpacking WANILLA's artifact (https://researchdata.tuwien.ac.at/records/hc4rp-xp328) into `~/.local/wasm-bench-tools/src/wanilla` | `casestudies/results/2026-10-13-309c9a4-wanilla.json`: `counts` is 73 leaks caught, 163 secure accepted, 48 secure rejected, 28 not expressible; `verdict_narrow` is the translation without the queries on imports and memory data | 2 s |
| where the 48 rejected secure specifications stop (21, 11, 5, 4, 4, 2, 1) | the command's third line of output | `precision_losses_at` of the same file | |

## Run-time cost (RQ5)

The timings need a quiet machine: the sweep records the load average beside each part
(`bench/results/2026-10-13-c2a3f4b.progress`).

| Claim | Command | Recorded in | Time |
|---|---|---|---|
| every timing of the section | `PRE=<the build of 0fcf4b4> PREOPT=<0fcf4b4 with bench/pre-ifc-opt.patch> ./bench/sweep-labels.sh` | `bench/results/2026-10-13-c2a3f4b*.json` | 1 h 52 min |
| the section's tables and geometric means | `./bench/sweep-report.py bench/results/2026-10-13-c2a3f4b` | `BENCHMARKS.md`, "Performance work of 2026-10-13" | 1 s |
| typing and labels against the erased copy (1.04) | the row "labelled / erased" of the kernels | the same | |
| labels against the typed core built with the same optimizations (2 %; 11 to 20 % at blocks) | the row "labelled / pre-ifc-opt" | the same | |
| secrets in memory (8 % time, 4 % allocation) | the table "With secrets in memory, medium" | the same | |
| WABT, the Hackage interpreter, Pulley, WAMR, wasm3, wasmi | the kernels' rows for wabt and `haskell-wasm`, the medium programs' for the others | the same; versions in `environment.versions` of the results files | |
| allocation per machine step did not grow | `./bench/tripwire.py` | `bench/allocation.txt` | 5 s |

The two earlier builds: check out `0fcf4b4` in a second worktree, `cabal build exe:wasm-ifc`,
and copy the binary; then `git apply bench/pre-ifc-opt.patch` there and build again.

## What compilers emit (section 4.2)

| Claim | Command | Recorded in | Time |
|---|---|---|---|
| how often the binaries of each compiler contain an instruction that SecWasm's printed rules reject | `./scripts/secwasm-shapes.py LABEL=DIR...` (the directories are in `HANDOFF.md`, "What SecWasm's rules reject in compiled code") | `bench/results/2026-10-13-secwasm-shapes.json` | 25 s |

## The Lean proof

| Claim | Command | Time |
|---|---|---|
| noninterference on the core, without `sorry` | `cd lean && lake build` (Lean 4.35.0, which `elan` installs from `lean-toolchain`) | 30 s |
| the axioms it depends on | `#print axioms WasmIfc.tini` in a file run with `lake env lean` | 10 s |
