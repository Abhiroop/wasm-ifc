#!/usr/bin/env bash
# Assemble SecWasm's examples and the counterexamples to its printed rules (wabt's wat2wasm)
# into casestudies/build/secwasm/.
set -euo pipefail
cd "$(dirname "$0")"
OUT=../build/secwasm
mkdir -p "$OUT"
for wat in *.wat; do wat2wasm "$wat" -o "$OUT/${wat%.wat}.wasm"; done
