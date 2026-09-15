#!/usr/bin/env bash
# Build the real-program tier (T2) with wasi-sdk into bench/wasm-t2/. The modules are not
# committed: the sources are third-party, fetched by bench/tools/fetch.sh.
#
#   ./bench/tools/fetch.sh wasi-sdk coremark polybench
#   ./bench/c/build.sh
#
# Each PolyBench kernel is built twice per dataset size: plain, for timing (it prints nothing,
# so the time measured is the kernel's), and `-dump`, which prints the result arrays so that
# the runtimes' answers can be compared — formatting thousands of doubles would otherwise
# dominate the time being measured.
set -euo pipefail
cd "$(dirname "$0")/../.."
TOOLS=${WASM_BENCH_TOOLS:-$HOME/.local/wasm-bench-tools}
CC=("$TOOLS/wasi-sdk/bin/clang" --target=wasm32-wasip1 -O2)
OUT=bench/wasm-t2
mkdir -p "$OUT"

CM=$TOOLS/src/coremark
# SEED_VOLATILE compiles the seeds and the iteration count in. The POSIX port's default reads
# them from the command line, and without arguments CoreMark calibrates itself to run for ten
# seconds — a different number of iterations, and so different CRCs, on every runtime and run.
for iterations in 100 4000; do
    "${CC[@]}" -w -I"$CM" -I"$CM/posix" -DSEED_METHOD=SEED_VOLATILE -DPERFORMANCE_RUN=1 -DITERATIONS=$iterations -DFLAGS_STR='"-O2"' \
        "$CM"/core_{list_join,main,matrix,state,util}.c "$CM/posix/core_portme.c" -o "$OUT/coremark-$iterations.wasm"
done

PB=$TOOLS/src/polybench
KERNELS=(2mm 3mm atax gemm jacobi-2d seidel-2d floyd-warshall nussinov correlation lu)
for kernel in "${KERNELS[@]}"; do
    # The trailing slash matters: src/polybench is a symlink, and find does not descend into a
    # symlinked starting point, so without it every kernel's source came back empty.
    src=$(find "$PB/" -name "$kernel.c" -not -path '*/utilities/*' | head -1)
    [ -n "$src" ] || { echo "no PolyBench source for $kernel" >&2; exit 1; }
    for size in MINI SMALL MEDIUM; do
        # polybench.c includes <sys/resource.h>, which WASI only has as an emulation.
        common=(-w -D_WASI_EMULATED_PROCESS_CLOCKS -I"$PB/utilities" -I"$(dirname "$src")" -D"${size}_DATASET"
            "$src" "$PB/utilities/polybench.c" -lm -lwasi-emulated-process-clocks)
        "${CC[@]}" "${common[@]}" -o "$OUT/pb-$kernel-${size,,}.wasm"
        "${CC[@]}" -DPOLYBENCH_DUMP_ARRAYS "${common[@]}" -o "$OUT/pb-$kernel-${size,,}-dump.wasm"
    done
done
echo "built $(ls "$OUT"/*.wasm | wc -l) modules in $OUT"
