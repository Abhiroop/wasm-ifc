#!/usr/bin/env bash
# Build the ten PolyBench kernels with their printing compiled out, at the SMALL and MEDIUM
# sizes, into bench/wasm-t2-silent/ (not committed). They are the workloads of bench/secrets.py:
# under a policy that declares a kernel's data secret, a kernel that prints its arrays is
# rejected (casestudies/README.md), so the cost of the labels with secrets in memory is
# measured on kernels that only compute.
#
# The printing goes the way casestudies/polybench/build.sh removes it for the MINI size: a copy
# of the source whose polybench_prevent_dce, the run-time guard around the printing, expands to
# nothing.
#
#   ./bench/tools/fetch.sh wasi-sdk polybench
#   ./bench/c/build-silent.sh
set -euo pipefail
cd "$(dirname "$0")/../.."
TOOLS=${WASM_BENCH_TOOLS:-$HOME/.local/wasm-bench-tools}
CC=("$TOOLS/wasi-sdk/bin/clang" --target=wasm32-wasip1 -O2 -w)
PB=$TOOLS/src/polybench
OUT=bench/wasm-t2-silent
mkdir -p "$OUT"
for kernel in 2mm 3mm atax gemm jacobi-2d seidel-2d floyd-warshall nussinov correlation lu; do
    src=$(find "$PB/" -name "$kernel.c" -not -path '*/utilities/*' | head -1)
    [ -n "$src" ] || { echo "no PolyBench source for $kernel" >&2; exit 1; }
    sed 's/polybench_prevent_dce(/SILENT(/' "$src" > "$OUT/$kernel-silent.c"
    for size in SMALL MEDIUM; do
        "${CC[@]}" -D_WASI_EMULATED_PROCESS_CLOCKS "-D${size}_DATASET" '-DSILENT(x)=' -I"$PB/utilities" -I"$(dirname "$src")" \
            "$OUT/$kernel-silent.c" "$PB/utilities/polybench.c" -lm -lwasi-emulated-process-clocks -o "$OUT/pb-$kernel-${size,,}-silent.wasm"
    done
done
echo "built $(ls "$OUT"/*.wasm | wc -l) modules in $OUT"
