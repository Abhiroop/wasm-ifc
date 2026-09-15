# Is an intrinsically typed interpreter necessarily slow?

Measurements behind that question for wasm-ifc, taken 2026-09-11 to 2026-09-15 (plan and
running log: `TODO.md` §I; tools: `bench/`). The interpreter's instructions are indexed by the
stack, locals, labels and module they run in, and its small-step `step` is total over the
well-typed configurations it can represent — the machine is its own type-soundness argument.
The question is whether that design has to cost speed. The experiments were built to charge
every cost to one of three causes: **the typing** (whatever of it survives erasure), **our
representation choices** (lists, persistent memory, laziness), or **the host language** (GHC
and its collector).

## The answer

**No — the typing itself costs nothing measurable.** Compared with an erased twin that is the
same machine with its types removed and nothing else changed, the typed interpreter is 3–5 %
*faster* (geometric mean over 24 kernels, before and after E2b; it makes no run-time tag checks
the twin must). Where
it had been slower — by about 20 % at GHC's default `-O1` — the cause was traced to the byte
in GHC's final STG: the optimiser left a configuration record allocated per step in the typed
driver. Types have no run-time representation, but they did change the optimiser's decisions,
and `-O2` on one module undoes that.

Placed among other interpreters, measured per machine step:

| against | relative to ours | notes |
|---|---|---|
| Hackage `wasm` 1.1.1 (untyped Haskell, IO, mutable vectors) | ours 4.6× faster | kernels |
| wabt `wasm-interp` (plain C++) | 1.3× faster than ours | kernels; wabt has no WASI here |
| WAMR `iwasm --interp` | 23× faster | real programs, per step |
| wasmtime Pulley | 36× faster | real programs, per step |
| wasm3, wasmi | 102×, 111× faster | real programs, per step |
| wasmtime Winch (baseline JIT) | ~320× faster | real programs, per step |
| wasmtime Cranelift (optimising JIT) | ~640× faster | real programs, partly under the floor |

These ratios predate E2b and the 1 KiB memory chunks, which since made ours about 2.1× faster on
the real programs. The remaining distance to the optimised interpreters is representation, and it is largest on
memory-heavy real programs (19–58 ns per step, against 6–14 on the kernels): persistent,
copy-on-write memory and boxed values under a garbage collector — costs of keeping `step` a
pure function, not of its types. The front end, which includes full type elaboration of every
function, takes a median 6 ms per module and 43 ms for the largest (2.2 MB), linearly in size.

## Method

- **Machine**: Intel i7-12700H laptop under WSL2 (Linux 6.18), GHC 9.12.2. Not native Linux;
  see *Threats*.
- **Runtimes**: ours at each commit, and the erased twin; wabt 1.0.27 `wasm-interp`; wasm3
  0.9.1-beta.1; WAMR 2.4.5 `iwasm --interp`; wasmi 2.0.0; wasmtime 48.0.1 as Pulley (interpreter),
  Winch and Cranelift; Hackage `wasm` 1.1.1. All installed pinned and checksummed by
  `bench/tools/fetch.sh`.
- **Workloads**: 25 micro-kernels (`bench/gen.py`; each isolates one cost — dispatch, calls,
  indexed locals/globals/labels at depths 2–64, memory); CoreMark and ten PolyBench/C kernels
  compiled with wasi-sdk 34 (`bench/c/build.sh`); 129 modules for the front end, including
  the WASI testsuite's C, Rust and AssemblyScript programs.
- **Timing**: CPU seconds, median of 3–7 repetitions after a warm-up, each runtime's start-up
  (an empty module) subtracted; repetitions interleaved round-robin across runtimes, and builds
  of ours compared inside a single sweep (`run.py --binary`). Times under 50 ms are reported as
  a bound and take part in no ratio.
- **The unit**: nanoseconds per *machine step* — one transition of our small-step machine. The
  count belongs to the program and its input, so it normalises every runtime alike; it is
  taken from GHC's ticky-ticky entry count for `step` (checked by hand: `empty` is 2 steps,
  `locals-2` 13 per iteration).
- **Correctness**: every kernel returns the same checksum on every runtime (recorded in
  `bench/checksums.txt`); all 20 PolyBench array dumps (mini, small) agree across seven runtimes;
  CoreMark's CRCs agree. Every interpreter change passed the unit tests, the spec testsuite
  (70 files, 0 failing) and the WASI testsuite (72/72) before it was timed.

Four measurement mistakes were caught along the way, each now guarded against: on this laptop a
fifteen-minute sweep runs everything ~2.5× slower than a two-minute one (a "speed-up" of
1.4–2.0× once came from that alone — hence interleaving); CoreMark's POSIX port calibrates its
own iteration count unless it is compiled in; ticky's report runs wide columns together; and a
`find` on a symlinked directory had silently built PolyBench without its kernels.

## E0 — laziness, not types (2026-09-11)

The first interpreter pushed `op a b` unevaluated onto a lazy stack, so a program retained every
value it had computed: `fib 30` peaked at 163 MB residency with 48 % of its time in GC. Strict
fields throughout the running state took that to 44 KB and 0 % and made the kernels 2.2–30×
faster (`bench/results/2026-09-11-*`).

## E1 — the typed machine against its erased twin

`bench/erased/Main.hs` runs the program the elaborator produced with the types forgotten: `Elem`
and `Append` witnesses become unary naturals (so indices are still walked), numeric witnesses
become the opcode's value type, values carry tags that every operation checks; stack, locals,
globals, configuration and control stack are strict exactly where the typed machine's are, and
its step mirrors the typed one clause for clause, calling the typed machine's own arithmetic.

| stage | typed time / erased time (geometric mean, 24 kernels) |
|---|---|
| before E6 (`-O1`) | 1.18 |
| step inlined into the driver (`-O1`) | 1.22 |
| `-O2` for the interpreter module | **0.97** |
| E2b: locals resolved at elaboration (twin mirrored) | **0.95** |

How the gap was found and closed (`bench/results/2026-09-15-e1-allocation.txt`, ticky reports,
final STG):

1. The erased machine allocated 13–37 % less. Ticky: its `step` has one caller and GHC inlines
   it, so the `Right (Stepped (Config …))` a step returns is never built; the typed `step` is
   exported and used twice, too large to inline, so every step built that result for `run` to
   discard. `INLINE step` halved the typed machine's allocation.
2. A gap remained: 104 bytes per `i32.add` step against 40. The STG shows both machines box the
   result and cons it (40 bytes); the erased driver then tail-calls itself with the
   configuration's fields unboxed, while the typed one builds a `Config` and a `Stepped` (64
   bytes) to jump to a join point that takes them apart.
3. Two explanations were tested and refuted. Looping over the fields by hand changed nothing.
   The existential type variables in the typed `Config` are not the cause: the erased machine
   given a phantom existential (`-DEXISTENTIAL_CONFIG`) allocates exactly as before.
4. GHC's `-O2` passes (SpecConstr) remove the `Config` and `Stepped`. On the interpreter module
   alone this matches a whole-program `-O2` byte for byte, and reverses the gap: the typed
   machine now allocates less than the erased one (e.g. `loop-arith` 456 against 608 MB).

The erased machine's tag checks are therefore worth at most the 3 % the typed machine now leads
by, which is why the plan's untagged variant of the twin was not built.

## E2 and E2b — locals in a vector

Locals as a flat vector of packed words, still reached by walking the `Elem` witness, ran
1.2–1.5× slower than the cons list on every kernel, deepest local included; the micro-benchmark
promising 1.6–6.5× had indexed by a precomputed `Int`. Reverted; the prototype is
`bench/prototypes/e2-vector-locals.patch`. A design that resolves positions at elaboration
remains possible but moves one property out of the types (TODO.md §I, E2b).

**E2b (approved and done, 2026-09-15): resolve the position at elaboration.** The local
instructions now carry a `Validation.Ref.LocalRef` — the local's position and type, computed
once from its witness by the only function that builds one, with the constructor hidden — and a
frame is a flat vector of packed words that an access indexes directly. It wins where E2 lost:
**1.43× on the real programs** (geometric mean; `pb-nussinov` 2.09×, `pb-3mm` 1.73×, CoreMark
1.47×) and 2.6× on the deepest-local kernel, while over all 25 kernels it is neutral (1.00×),
since the call-heavy ones lose 13–19 %: each call now builds a vector frame, and each local read
boxes a fresh value. The erased twin mirrors it (positions and value types at the access,
packed frames, a tag check on each write); typed / erased is 0.95 afterwards
(`bench/results/2026-09-15-e2b-e1.json`, `…-candidates-t2.json`). With it, our cost on the real
programs falls from ~37 to ~26 ns per step, and with 1 KiB memory chunks after it (§E6) to ~18,
which narrows every ratio in the E4 table by about 2.1×.

## E3 — an independent untyped Haskell interpreter

The Hackage `wasm` package (IO, mutable vectors, no intrinsic typing) is 1.6–12.4× slower than
ours per kernel, **4.6× in geometric mean**: untyped Haskell is not, by itself, faster.

## E4 — positioning

**Kernels**, per machine step (full table in the appendix): ours 5.7–13.6 ns on everything but
the deep-index and memory kernels (24–28 ns); the erased twin level with ours; wabt 6.6–11.6 ns,
1.3× ahead in geometric mean. The faster interpreters finish these kernels under the 50 ms
floor, so they are placed by the real programs.

**Real programs.** Ours was timed at the small sizes, where a run takes it seconds, and the fast
runtimes at the medium sizes, where a run takes them seconds; the two are compared per step on
the same ten programs. The pairing matters: at the small sizes the fast runtimes' start-up of
10–15 ms is a large share of their time, which had made WAMR look 5.5× ahead where it is 23×.

| runtime | ns per step | ahead of ours |
|---|---|---|
| ours (small sizes) | 37.1 | — |
| WAMR `iwasm --interp` | 1.60 | 23× |
| wasmtime Pulley | 1.03 | 36× |
| wasm3 | 0.37 | 102× |
| wasmi | 0.33 | 111× |
| wasmtime Winch (5 programs above the floor) | 0.11 | 324× |
| wasmtime Cranelift (4 programs above the floor) | 0.05 | 638× |

Our cost per step triples from the kernels to the programs, and the programs are where memory is
used: every store copies a 4 KiB chunk, and every value is boxed under a collector. Those are
costs of keeping `step` a pure function over persistent state, not of its types; the typed and
erased machines are level throughout.

## E5 — the front end

Decoding, validation with full elaboration to the typed AST, and instantiation, on 129 modules
(`bench/results/2026-09-15-e5-phases.csv`): median 6.2 ms per module, 43 ms at worst; for the
largest (2.2 MB, 42,775 instructions) 14 ms decoding, 19 ms validating, 1.2 ms instantiating.
About 85 ms per 100,000 instructions, correlation 0.90 with instruction count; decoding and
validation take roughly half each. (55 further files in the WASI testsuite are Preview 3
components, not core modules, and are rejected at decoding by design.)

## E6 — which change bought what

| stage | kernels, over previous | real programs, over previous |
|---|---|---|
| memory in 4 KiB chunks, word loads/stores | 1.09× | **4.07×** |
| `step` inlined | 1.42× | 1.15× |
| `-O2` on the interpreter module | 1.26× | 1.08× |
| **all three** | ~1.95× | ~5.1× |
| later, after E2b: chunks of 1 KiB instead of 4 KiB | 1.07× | **1.46×** |

CoreMark went from 8.4 s to 1.8 s, PolyBench `floyd-warshall` (small) from 25.8 s to 4.1 s, the
streaming-memory kernel from 5.4 s to 0.66 s. Each change passed the full suites before timing.

## Threats to validity and what remains

- **Laptop under WSL2.** Interleaving removes most drift, but absolute numbers should be retaken
  on native Linux on a desktop CPU before they are quoted as absolute.
- **Per-step comparisons across input sizes** (small for the slow interpreters, medium for the
  fast ones) assume cost per step does not depend on size; larger inputs stress caches more.
- **Coverage of the fast tiers.** On the kernels they finish under the 50 ms floor; on the
  programs they are compared at medium sizes per step, which assumes a step costs the same at
  both sizes (larger inputs stress caches more). CoreMark's step count moves by a few dozen steps
  between runs, because it formats timings that differ: 2 parts in 100 million.
- **The paired E4 comparison combines two sweeps** (ours in one, the fast runtimes in another),
  where every other comparison here is interleaved inside one; its ratios are good to the
  run-to-run spread of long sweeps on this machine, not to the 2 % of an interleaved A/B.
- **Open design decision**: the memory representation — the largest remaining cost on real
  programs, bounded by keeping `step` pure (TODO.md §I, "E6 next", with measured candidates).

## Reproducing

```sh
./bench/tools/fetch.sh && ./bench/build.sh && ./bench/c/build.sh
cabal build exe:wasm-ifc --builddir=/tmp/ticky --ghc-options='-ticky -rtsopts'
cabal build bench:wasm-ifc-erased bench:wasm-ifc-phases --enable-benchmarks --builddir=/tmp/bench
./bench/drivers/haskell-wasm/build.sh
./bench/run.py --binary erased="$(cabal list-bin bench:wasm-ifc-erased --enable-benchmarks --builddir=/tmp/bench)" \
               --ticky "$(cabal list-bin exe:wasm-ifc --builddir=/tmp/ticky)"
./bench/run.py --tier t2 -w coremark-100 -w 'pb-*-small'
./bench/report.py --versus erased
```

## Appendix — full tables

Generated from `bench/results/2026-09-15-45a93c6-t1-stages.json`,
`…-45a93c6-t2-stages.json`, `…-addf1ee-t2-compilers.json`, `steps.json` and the E5 CSV.

#### E6, kernels: CPU seconds by stage

| workload                                | e1    | e6a-memory | e6b-inline | e6d-O2 | first/last |
|-----------------------------------------|-------|------------|------------|--------|------------|
| br-table                                | 0.202 | 0.221      | 0.152      | 0.106  | 1.9x       |
| call-indirect                           | 0.222 | 0.195      | 0.160      | 0.143  | 1.5x       |
| fib                                     | 0.502 | 0.491      | 0.341      | 0.308  | 1.6x       |
| float                                   | 0.105 | 0.105      | 0.073      | 0.055  | 1.9x       |
| funcs-16                                | 0.131 | 0.140      | 0.099      | 0.080  | 1.6x       |
| funcs-2                                 | 0.123 | 0.138      | 0.094      | 0.077  | 1.6x       |
| funcs-4                                 | 0.158 | 0.148      | 0.108      | 0.086  | 1.8x       |
| funcs-64                                | 0.169 | 0.168      | 0.131      | 0.113  | 1.5x       |
| globals-16                              | 0.140 | 0.140      | 0.103      | 0.076  | 1.8x       |
| globals-2                               | 0.109 | 0.107      | 0.074      | 0.053  | 2.1x       |
| globals-4                               | 0.117 | 0.114      | 0.079      | 0.055  | 2.1x       |
| globals-64                              | 0.261 | 0.261      | 0.215      | 0.205  | 1.3x       |
| labels-16                               | 0.238 | 0.242      | 0.159      | 0.123  | 1.9x       |
| labels-2                                | 0.107 | 0.107      | 0.071      | 0.051  | 2.1x       |
| labels-4                                | 0.119 | 0.119      | 0.083      | 0.061  | 1.9x       |
| labels-64                               | 0.761 | 0.707      | 0.448      | 0.389  | 2.0x       |
| locals-16                               | 0.209 | 0.213      | 0.156      | 0.137  | 1.5x       |
| locals-2                                | 0.179 | 0.185      | 0.117      | 0.088  | 2.0x       |
| locals-4                                | 0.193 | 0.191      | 0.128      | 0.097  | 2.0x       |
| locals-64                               | 0.409 | 0.409      | 0.352      | 0.317  | 1.3x       |
| loop-arith                              | 0.193 | 0.192      | 0.121      | 0.082  | 2.3x       |
| loop-arith64                            | 0.201 | 0.193      | 0.120      | 0.087  | 2.3x       |
| memory-random                           | 0.646 | 0.437      | 0.282      | 0.300  | 2.2x       |
| memory-stream                           | 5.428 | 1.181      | 0.897      | 0.655  | 8.3x       |
| **geometric mean, stage over previous** |       | 1.09x      | 1.42x      | 1.26x  |            |

#### E6, real programs (small): CPU seconds by stage

| workload                                | e1     | e6a-memory | e6b-inline | e6d-O2 | first/last |
|-----------------------------------------|--------|------------|------------|--------|------------|
| coremark-100                            | 8.388  | 2.136      | 2.167      | 1.800  | 4.7x       |
| pb-2mm-small                            | 1.674  | 0.456      | 0.378      | 0.388  | 4.3x       |
| pb-3mm-small                            | 2.936  | 0.729      | 0.598      | 0.525  | 5.6x       |
| pb-atax-small                           | 0.188  | 0.047      | 0.045      | 0.039  | —          |
| pb-correlation-small                    | 1.739  | 0.395      | 0.356      | 0.337  | 5.2x       |
| pb-floyd-warshall-small                 | 25.818 | 5.000      | 4.901      | 4.081  | 6.3x       |
| pb-gemm-small                           | 1.443  | 0.298      | 0.251      | 0.258  | 5.6x       |
| pb-jacobi-2d-small                      | 2.905  | 0.641      | 0.492      | 0.472  | 6.2x       |
| pb-lu-small                             | 9.278  | 2.045      | 1.594      | 1.526  | 6.1x       |
| pb-nussinov-small                       | 5.512  | 1.920      | 1.896      | 1.540  | 3.6x       |
| pb-seidel-2d-small                      | 4.085  | 1.242      | 1.027      | 1.080  | 3.8x       |
| **geometric mean, stage over previous** |        | 4.07x      | 1.15x      | 1.08x  |            |

#### E1: typed time / erased time, at each stage (below 1: typed is faster)

| workload           | memory (E6a) | + inline (E6b) | + -O2 (E6d) |
|--------------------|--------------|----------------|-------------|
| br-table           | 1.20         | 1.21           | 0.94        |
| call-indirect      | 1.06         | 1.00           | 1.11        |
| fib                | 1.19         | 1.09           | 1.04        |
| float              | 1.08         | 1.36           | 1.03        |
| funcs-16           | 1.18         | 1.16           | 0.94        |
| funcs-2            | 1.25         | 1.30           | 1.07        |
| funcs-4            | 1.21         | 1.30           | 1.03        |
| funcs-64           | 1.11         | 1.14           | 0.97        |
| globals-16         | 1.13         | 1.22           | 0.81        |
| globals-2          | 1.09         | 1.29           | 0.93        |
| globals-4          | 1.06         | 1.32           | 0.88        |
| globals-64         | 1.11         | 1.03           | 0.99        |
| labels-16          | 1.29         | 1.13           | 0.99        |
| labels-2           | 1.38         | 1.33           | 0.97        |
| labels-4           | 1.16         | 1.24           | 0.96        |
| labels-64          | 1.48         | 1.00           | 1.03        |
| locals-16          | 1.15         | 1.32           | 1.01        |
| locals-2           | 1.19         | 1.37           | 0.98        |
| locals-4           | 1.14         | 1.39           | 0.96        |
| locals-64          | 1.10         | 1.09           | 0.99        |
| loop-arith         | 1.17         | 1.36           | 0.91        |
| loop-arith64       | 1.21         | 1.27           | 0.88        |
| memory-random      | 1.32         | 1.21           | 1.16        |
| memory-stream      | 1.19         | 1.35           | 0.88        |
| **geometric mean** | 1.18         | 1.22           | 0.97        |

#### E4, kernels: nanoseconds per machine step

| workload                                     | steps | e6d-O2 | erased-e6d | haskell-wasm | wabt-interp | wamr-interp | wasm3 | wasmi | wasmtime-pulley |
|----------------------------------------------|-------|--------|------------|--------------|-------------|-------------|-------|-------|-----------------|
| br-table                                     | 11.5M | 9.2    | 9.8        | 48.0         | 7.1         | <4.3        | <4.3  | <4.3  | <4.3            |
| call-indirect                                | 10.5M | 13.6   | 12.3       | 55.5         | 11.6        | <4.8        | <4.8  | <4.8  | <4.8            |
| fib                                          | 29.6M | 10.4   | 10.0       | 40.8         | 8.6         | 1.8         | <1.7  | <1.7  | <1.7            |
| float                                        | 8.5M  | 6.5    | 6.3        | 53.6         | 7.2         | <5.9        | <5.9  | <5.9  | <5.9            |
| funcs-16                                     | 9.0M  | 8.9    | 9.5        | 43.2         | 8.1         | <5.6        | <5.6  | <5.6  | <5.6            |
| funcs-2                                      | 9.0M  | 8.6    | 8.0        | 49.5         | 8.1         | <5.6        | <5.6  | <5.6  | <5.6            |
| funcs-4                                      | 9.0M  | 9.6    | 9.3        | 53.9         | 9.1         | <5.6        | <5.6  | <5.6  | <5.6            |
| funcs-64                                     | 9.0M  | 12.5   | 12.9       | 41.8         | 7.6         | <5.6        | <5.6  | <5.6  | <5.6            |
| globals-16                                   | 8.5M  | 8.9    | 11.0       | 43.1         | 9.2         | <5.9        | <5.9  | <5.9  | <5.9            |
| globals-2                                    | 8.5M  | 6.2    | 6.7        | 39.5         | 7.7         | <5.9        | <5.9  | <5.9  | <5.9            |
| globals-4                                    | 8.5M  | 6.5    | 7.4        | 38.4         | 7.7         | <5.9        | <5.9  | <5.9  | <5.9            |
| globals-64                                   | 8.5M  | 24.1   | 24.4       | 38.5         | 7.6         | <5.9        | <5.9  | <5.9  | <5.9            |
| labels-16                                    | 15.0M | 8.2    | 8.3        | 26.6         | <3.3        | <3.3        | <3.3  | <3.3  | <3.3            |
| labels-2                                     | 8.0M  | 6.4    | 6.6        | 34.9         | <6.2        | <6.2        | <6.2  | <6.2  | <6.2            |
| labels-4                                     | 9.0M  | 6.8    | 7.0        | 33.1         | <5.6        | <5.6        | <5.6  | <5.6  | <5.6            |
| labels-64                                    | 39.0M | 10.0   | 9.7        | 27.8         | 1.3         | 1.9         | <1.3  | <1.3  | <1.3            |
| locals-16                                    | 13.0M | 10.5   | 10.4       | 37.0         | 6.6         | <3.8        | <3.8  | <3.8  | <3.8            |
| locals-2                                     | 13.0M | 6.7    | 6.9        | 47.1         | 7.4         | <3.8        | <3.8  | <3.8  | <3.8            |
| locals-4                                     | 13.0M | 7.4    | 7.8        | 55.1         | 7.2         | <3.8        | <3.8  | <3.8  | <3.8            |
| locals-64                                    | 13.0M | 24.3   | 24.6       | 47.9         | 6.6         | <3.8        | <3.8  | <3.8  | <3.8            |
| loop-arith                                   | 14.5M | 5.7    | 6.2        | 70.6         | 8.5         | <3.4        | <3.4  | <3.4  | <3.4            |
| loop-arith64                                 | 13.5M | 6.5    | 7.3        | 75.7         | 9.7         | <3.7        | <3.7  | <3.7  | <3.7            |
| memory-random                                | 24.9M | 12.0   | 10.4       | 44.6         | 7.7         | <2.0        | <2.0  | <2.0  | <2.0            |
| memory-stream                                | 23.0M | 28.5   | 32.5       | 51.2         | 11.2        | 2.3         | <2.2  | <2.2  | <2.2            |
| **geometric mean: times faster than e6d-O2** |       |        | 1.0x       | 0.2x         | 1.3x        | 7.3x        | —     | —     | —               |

#### E4, real programs at small sizes: nanoseconds per machine step

| workload                                     | steps  | e6d-O2 | wamr-interp | wasm3 | wasmi | wasmtime-pulley |
|----------------------------------------------|--------|--------|-------------|-------|-------|-----------------|
| coremark-100                                 | 60.7M  | 29.6   | 4.4         | <0.8  | <0.8  | 0.8             |
| pb-2mm-small                                 | 6.8M   | 56.7   | 17.3        | <7.3  | <7.3  | <7.3            |
| pb-3mm-small                                 | 11.3M  | 46.3   | 9.9         | <4.4  | <4.4  | <4.4            |
| pb-atax-small                                | 0.8M   | <61.6  | 109.6       | <61.6 | <61.6 | <61.6           |
| pb-correlation-small                         | 6.9M   | 48.9   | 19.8        | <7.2  | <7.2  | <7.2            |
| pb-floyd-warshall-small                      | 142.8M | 28.6   | 2.1         | 0.4   | <0.4  | 0.5             |
| pb-gemm-small                                | 7.5M   | 34.6   | 12.2        | <6.7  | <6.7  | <6.7            |
| pb-jacobi-2d-small                           | 25.2M  | 18.7   | 4.2         | <2.0  | <2.0  | <2.0            |
| pb-lu-small                                  | 45.3M  | 33.7   | 3.6         | <1.1  | <1.1  | 1.5             |
| pb-nussinov-small                            | 26.5M  | 58.1   | 5.6         | <1.9  | <1.9  | <1.9            |
| pb-seidel-2d-small                           | 30.0M  | 36.0   | 6.3         | <1.7  | <1.7  | 2.4             |
| **geometric mean: times faster than e6d-O2** |        |        | 5.5x        | 73.0x | —     | 28.5x           |

#### E4, real programs at medium sizes (the compilers' tier; ours not run): nanoseconds per machine step

| workload                                              | steps    | wasmtime-pulley | wamr-interp | wasm3 | wasmi | wasmtime-winch | wasmtime-cranelift |
|-------------------------------------------------------|----------|-----------------|-------------|-------|-------|----------------|--------------------|
| coremark-4000                                         | 2,425.0M | 0.7             | 1.9         | 0.5   | 0.4   | 0.1            | 0.1                |
| pb-2mm-medium                                         | 305.4M   | 1.3             | 1.6         | 0.3   | 0.3   | <0.2           | <0.2               |
| pb-3mm-medium                                         | 473.5M   | 1.2             | 1.6         | 0.3   | 0.3   | 0.1            | <0.1               |
| pb-atax-medium                                        | 8.9M     | <5.6            | 11.7        | <5.6  | <5.6  | <5.6           | <5.6               |
| pb-correlation-medium                                 | 151.2M   | 1.3             | 2.1         | 0.3   | <0.3  | <0.3           | <0.3               |
| pb-floyd-warshall-medium                              | 3,021.5M | 0.4             | 1.4         | 0.4   | 0.3   | 0.1            | 0.0                |
| pb-gemm-medium                                        | 225.9M   | 1.5             | 1.6         | 0.4   | 0.3   | <0.2           | <0.2               |
| pb-jacobi-2d-medium                                   | 495.3M   | 1.5             | 1.4         | 0.4   | 0.4   | <0.1           | <0.1               |
| pb-lu-medium                                          | 1,773.6M | 1.3             | 1.4         | 0.4   | 0.3   | 0.1            | 0.0                |
| pb-nussinov-medium                                    | 551.0M   | 0.4             | 1.6         | 0.3   | 0.3   | <0.1           | <0.1               |
| pb-seidel-2d-medium                                   | 844.1M   | 1.5             | 1.7         | 0.4   | 0.3   | 0.2            | 0.1                |
| **geometric mean: times faster than wasmtime-pulley** |          |                 | 0.6x        | 2.8x  | 3.1x  | 9.1x           | 18.1x              |

#### E4, paired: ours at small sizes against each runtime at medium sizes, per step

ours, geometric mean over the programs: 37.1 ns per step

| runtime            | programs | ns per step | times faster than ours |
|--------------------|----------|-------------|------------------------|
| wamr-interp        | 10       | 1.60        | 23x                    |
| wasmtime-pulley    | 10       | 1.03        | 36x                    |
| wasm3              | 10       | 0.37        | 102x                   |
| wasmi              | 9        | 0.33        | 111x                   |
| wasmtime-winch     | 5        | 0.11        | 324x                   |
| wasmtime-cranelift | 4        | 0.05        | 638x                   |

#### E3: Hackage wasm / typed (E6d), kernels

| workload      | haskell-wasm s | ours s | ratio |
|---------------|----------------|--------|-------|
| br-table      | 0.552          | 0.106  | 5.2x  |
| call-indirect | 0.583          | 0.143  | 4.1x  |
| fib           | 1.207          | 0.308  | 3.9x  |
| float         | 0.456          | 0.055  | 8.3x  |
| funcs-16      | 0.389          | 0.080  | 4.8x  |
| funcs-2       | 0.446          | 0.077  | 5.8x  |
| funcs-4       | 0.485          | 0.086  | 5.6x  |
| funcs-64      | 0.376          | 0.113  | 3.3x  |
| globals-16    | 0.366          | 0.076  | 4.8x  |
| globals-2     | 0.336          | 0.053  | 6.4x  |
| globals-4     | 0.327          | 0.055  | 5.9x  |
| globals-64    | 0.327          | 0.205  | 1.6x  |
| labels-16     | 0.400          | 0.123  | 3.2x  |
| labels-2      | 0.279          | 0.051  | 5.5x  |
| labels-4      | 0.298          | 0.061  | 4.9x  |
| labels-64     | 1.084          | 0.389  | 2.8x  |
| locals-16     | 0.481          | 0.137  | 3.5x  |
| locals-2      | 0.612          | 0.088  | 7.0x  |
| locals-4      | 0.716          | 0.097  | 7.4x  |
| locals-64     | 0.623          | 0.317  | 2.0x  |
| loop-arith    | 1.023          | 0.082  | 12.4x |
| loop-arith64  | 1.022          | 0.087  | 11.7x |
| memory-random | 1.111          | 0.300  | 3.7x  |
| memory-stream | 1.177          | 0.655  | 1.8x  |
geometric mean: 4.62x

#### E5: front end

129 modules; 96 with at least 1,000 instructions.
Largest: fd_readdir.wasm, 2.20 MB, 42,775 instructions: decode 14.1 ms, validate 18.8 ms, instantiate 1.16 ms.
Slowest total: 43.3 ms. Median total: 6.17 ms.
Fit through the origin, modules with 1,000+ instructions: 84.5 ms per 100,000 instructions; correlation 0.898.
Share of the front end, median over those: decode 45%, validate 52%.
