#!/usr/bin/env bash
# Build the Rust password checker and its two leaking variants into casestudies/build/password-rust/
# with the installed rustc (rustup target add wasm32-wasip1).
set -euo pipefail
cd "$(dirname "$0")"
OUT=../build/password-rust
mkdir -p "$OUT"
build() { rustc --edition 2021 --target wasm32-wasip1 -C opt-level=2 "$@"; }
build password.rs -o "$OUT/password.wasm"
build --cfg 'feature="leak_control"' password.rs -o "$OUT/password-leak-control.wasm"
build --cfg 'feature="leak_memory"' password.rs -o "$OUT/password-leak-memory.wasm"
