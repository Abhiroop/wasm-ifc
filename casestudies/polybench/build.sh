#!/usr/bin/env bash
# Build ten PolyBench/C kernels (./bench/tools/fetch.sh wasi-sdk polybench) at the MINI size into
# casestudies/build/polybench/: <kernel>.wasm prints its result arrays with fprintf, and
# <kernel>-silent.wasm has the printing compiled out (a copy of the source whose
# polybench_prevent_dce, the run-time guard around the printing, expands to nothing), so only the
# kernel handles the data.
set -euo pipefail
cd "$(dirname "$0")/../.."
TOOLS=${WASM_BENCH_TOOLS:-$HOME/.local/wasm-bench-tools}
CC=("$TOOLS/wasi-sdk/bin/clang" --target=wasm32-wasip1 -O2 -w)
PB=$TOOLS/src/polybench
OUT=casestudies/build/polybench
mkdir -p "$OUT"
for kernel in 2mm 3mm atax gemm jacobi-2d seidel-2d floyd-warshall nussinov correlation lu; do
    src=$(find "$PB/" -name "$kernel.c" -not -path '*/utilities/*' | head -1)
    "${CC[@]}" -D_WASI_EMULATED_PROCESS_CLOCKS -DMINI_DATASET -DPOLYBENCH_DUMP_ARRAYS -I"$PB/utilities" -I"$(dirname "$src")" \
        "$src" "$PB/utilities/polybench.c" -lm -lwasi-emulated-process-clocks -o "$OUT/$kernel.wasm"
    sed 's/polybench_prevent_dce(/SILENT(/' "$src" > "$OUT/$kernel-silent.c"
    "${CC[@]}" -D_WASI_EMULATED_PROCESS_CLOCKS -DMINI_DATASET '-DSILENT(x)=' -I"$PB/utilities" -I"$(dirname "$src")" \
        "$OUT/$kernel-silent.c" "$PB/utilities/polybench.c" -lm -lwasi-emulated-process-clocks -o "$OUT/$kernel-silent.wasm"
done
