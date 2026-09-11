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
| `tools/fetch.sh` | installs pinned, checksummed toolchains into `~/.local/wasm-bench-tools` (wasi-sdk so far) |

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
./bench/build.sh                       # regenerate and compile the kernels
./bench/run.py                         # everything available, ~10 minutes
./bench/run.py -r wasm-ifc -w fib      # one runtime, one workload
./bench/report.py                      # tables from the newest results
./bench/report.py before.json after.json
```

`run.py` finds the runtimes itself and skips what is missing: ours (via `cabal list-bin`),
wasmtime in its three tiers (Cranelift, Winch, and the Pulley interpreter), wabt's
`wasm-interp`, and wasm3. Set `BENCH_CPU=2` to pin with `taskset`; it is off by default
because on this hybrid CPU under WSL2 it makes runs slower without steadying them.

### What these kernels can and cannot compare

They are sized for an interpreter, so a compiling runtime finishes one inside the spread of
its own start-up: `report.py` prints those cells as `<0.05` and takes them out of every ratio
rather than quoting a number that is really scheduler noise. The honest comparison here is
against other **interpreters** — wabt's, and Pulley. Placing us against the JIT tiers needs
workloads that run long enough for everyone, which is what the real-program tier (CoreMark,
PolyBench) in `TODO.md` §I is for.

Benchmarks never gate: `smoke.sh` is a manual check, and timings are taken deliberately, not
on every commit. Each file in `results/` names the commit and the machine it came from.
