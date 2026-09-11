#!/usr/bin/env bash
# Regenerate the benchmark kernels and compile them to bench/wasm/.
#
#   ./bench/build.sh
set -euo pipefail
cd "$(dirname "$0")/.."
./bench/gen.py
mkdir -p bench/wasm
for wat in bench/wat/*.wat; do
    wat2wasm "$wat" -o "bench/wasm/$(basename "${wat%.wat}").wasm"
done
echo "built $(ls bench/wasm/*.wasm | wc -l) modules in bench/wasm"
