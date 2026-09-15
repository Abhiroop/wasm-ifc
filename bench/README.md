## bench — how fast is the intrinsically typed interpreter?

The experiments behind `TODO.md` §I. The question is not "are we fast" but **where the time
goes**: to the typing discipline (the witnesses that survive erasure), to our representation
choices (linked-list stacks, immutable pages, lazy fields), or to the host language (GHC and
its collector). Only the first would be an argument against intrinsic typing, and the
infrastructure here exists to tell the three apart.

| Path | Contents |
|------|----------|
| `gen.py`     | generates the micro-kernels; edit this, never `wat/*.wat` |
| `wat/`       | the generated kernels |
| `wasm/`      | the compiled kernels (committed, so a run needs no `wat2wasm`) |
| `build.sh`   | `gen.py` + `wat2wasm` |
| `run.py`     | times every workload on every runtime it can find; writes `results/*.json` |
| `report.py`  | results → the markdown tables, or two result files against each other |
| `smoke.sh`   | one run of every kernel on our interpreter, checksums checked |
| `results/`   | committed measurements, one file per run, with the environment that produced it |
| `micro/`     | stand-alone measurement devices, built ad hoc and not part of the package |
| `prototypes/` | designs measured and rejected, kept as patches that still apply |
| `tools/fetch.sh` | installs pinned, checksummed toolchains, runtimes and third-party sources into `~/.local/wasm-bench-tools` |
| `c/build.sh` | builds the real-program tier (CoreMark, ten PolyBench kernels) into `wasm-t2/`, which is not committed |
| `erased/`    | the erased machine (E1): the interpreter with its types forgotten; frozen at `15e5ace` (see below) |
| `phases/`    | front-end timing per module (E5); `cabal build bench:wasm-ifc-phases --enable-benchmarks` |
| `drivers/haskell-wasm/` | the Hackage `wasm` interpreter behind our command line (E3); `build.sh` prints its path |
| `steps.py`   | records machine-step counts once per module in `results/steps.json` |
| `tripwire.py` | bytes allocated by nine workloads against `allocation.txt`: deterministic, under a minute |

### The kernels

Every kernel is one self-contained module exporting a zero-argument `run` that returns an
i32 checksum. Zero arguments because wabt's `wasm-interp` cannot pass any; a checksum because
every runtime must agree on it, which makes the benchmark a differential test as well.

`empty` is the per-runtime start-up baseline and is subtracted from every other number.
`fib` is call-bound, `loop-arith`/`loop-arith64` are pure dispatch, `float` is f64 arithmetic,
`memory-stream`/`memory-random` are sequential and scattered memory, `call-indirect` and
`br-table` are the indirect control transfers. The four sweeps — `locals-N`, `funcs-N`,
`globals-N`, `labels-N` for N in 2, 4, 16, 64 — put the hot local, callee, global and branch
target at index N. Those sweeps are the experiment that matters most: a cost that grows with
N is the unary index (`Elem`, and the control-stack depth) being walked at run time, which is
the one overhead intrinsic typing actually imposes here.

### Running

```sh
./bench/tools/fetch.sh                 # toolchain, other runtimes, CoreMark and PolyBench sources
./bench/build.sh                       # regenerate and compile the kernels (t1)
./bench/c/build.sh                     # compile the real programs (t2)
./bench/run.py                         # t1 on everything available
./bench/run.py --tier t2 -w coremark-100 -w 'pb-*-small'
./bench/run.py --tier t2 --verify -w 'pb-*-small-dump'
./bench/report.py                      # tables from the newest results
./bench/report.py before.json after.json
./bench/report.py results.json --versus erased --steps bench/results/steps.json
```

`run.py` finds the runtimes itself and skips what is missing: ours (via `cabal list-bin`),
wasmtime in its three tiers (Cranelift, Winch, and the Pulley interpreter), wabt's
`wasm-interp`, wasm3, WAMR's `iwasm` pinned to its interpreter, and wasmi. Repetitions are
interleaved across runtimes, and `--binary NAME=PATH` times another build of ours inside the
same sweep; the method note in `TODO.md` §I says why both matter on this machine. Set
`BENCH_CPU=2` to pin with `taskset`; it is off by default because on this hybrid CPU under
WSL2 it makes runs slower without steadying them.

### Machine steps

Time per step is the unit that lets runtimes be compared on programs sized for different
speeds. A step is one transition of our small-step machine, and `--ticky PATH` records each
workload's count from a build of ours with GHC's ticky-ticky counters, which count entries
into `step`. The count on `empty` is exactly 2, and on `locals-2` exactly 13 per iteration,
as counted by hand. Build it once, outside the normal build directory:

```sh
cabal build exe:wasm-ifc --builddir=/tmp/ticky --ghc-options='-ticky -rtsopts'
./bench/run.py --ticky "$(cabal list-bin exe:wasm-ifc --builddir=/tmp/ticky)"
```

### What these kernels can and cannot compare

They are sized for an interpreter, so a compiling runtime finishes one inside the spread of
its own start-up: `report.py` prints those cells as `<0.05` and takes them out of every ratio
rather than quoting a number that is really scheduler noise. The honest comparison here is
against other **interpreters** — wabt's, and Pulley. Placing us against the JIT tiers needs
workloads that run long enough for everyone, which is what the real-program tier (CoreMark,
PolyBench) in `TODO.md` §I is for.

Benchmarks never gate: `smoke.sh` is a manual check, and timings are taken deliberately, not
on every commit. Each file in `results/` names the commit and the machine it came from.

### Checking for regressions

Timings need a quiet machine and interleaving, so they are for milestones. Between milestones,
run `./bench/tripwire.py` after any change to `step`, the stack or memory. It counts the bytes
each of nine workloads allocates, which is deterministic and has moved with every regression
found so far, and fails when one grows by more than 2 % over `allocation.txt`. A change meant to
move allocation re-records the reference with `--record` in the same commit.

At a milestone, save the built binary; time the next milestone against it in one sweep:

```sh
./bench/run.py --binary before=/path/to/saved/wasm-ifc -r before -r wasm-ifc
./bench/run.py --binary before=/path/to/saved/wasm-ifc -r before -r wasm-ifc --tier t2 -w coremark-100 -w 'pb-*-small'
```

The erased machine is frozen at `15e5ace`, where it answered E1 (typed / erased 0.95). It is not
kept in lockstep while IFC reshapes the instructions and `step`, and it will stop compiling once
they change; to rerun E1, build `bench/erased` from that commit.

The findings, with their method and threats, are in `BENCHMARKS.md` at the repository root.
