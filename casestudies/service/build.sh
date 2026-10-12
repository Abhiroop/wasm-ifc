#!/usr/bin/env bash
# Build the password service's variants with wasi-sdk (./bench/tools/fetch.sh wasi-sdk) into
# casestudies/build/service/: the service, and the same with each of the two leaks.
set -euo pipefail
cd "$(dirname "$0")"
CC=${WASI_SDK:-${WASM_BENCH_TOOLS:-$HOME/.local/wasm-bench-tools}/wasi-sdk}/bin/clang
OUT=../build/service
mkdir -p "$OUT"
"$CC" --target=wasm32-wasip1 -O2 service.c -o "$OUT/service.wasm"
"$CC" --target=wasm32-wasip1 -O2 -DLEAK_CONTROL service.c -o "$OUT/service-leak-control.wasm"
"$CC" --target=wasm32-wasip1 -O2 -DLEAK_MEMORY service.c -o "$OUT/service-leak-memory.wasm"
