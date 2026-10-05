#!/usr/bin/env bash
# Build frames.c with wasi-sdk (./bench/tools/fetch.sh wasi-sdk) into casestudies/build/frames/.
set -euo pipefail
cd "$(dirname "$0")"
CC=${WASI_SDK:-${WASM_BENCH_TOOLS:-$HOME/.local/wasm-bench-tools}/wasi-sdk}/bin/clang
OUT=../build/frames
mkdir -p "$OUT"
"$CC" --target=wasm32-wasip1 -O2 frames.c -o "$OUT/frames.wasm"
