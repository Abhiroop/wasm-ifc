#!/usr/bin/env bash
# Build the password checker's variants with wasi-sdk (./bench/tools/fetch.sh wasi-sdk) into
# casestudies/build/password/: the checker, the same through libc's read and write, and the
# naive one, each plain and with the two leaks.
set -euo pipefail
cd "$(dirname "$0")"
CC=${WASI_SDK:-${WASM_BENCH_TOOLS:-$HOME/.local/wasm-bench-tools}/wasi-sdk}/bin/clang
OUT=../build/password
mkdir -p "$OUT"
for source in password password-libc password-naive; do
    "$CC" --target=wasm32-wasip1 -O2 "$source.c" -o "$OUT/$source.wasm"
    "$CC" --target=wasm32-wasip1 -O2 -DLEAK_CONTROL "$source.c" -o "$OUT/$source-leak-control.wasm"
    "$CC" --target=wasm32-wasip1 -O2 -DLEAK_MEMORY "$source.c" -o "$OUT/$source-leak-memory.wasm"
done
