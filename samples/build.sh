#!/usr/bin/env bash
# Compile every .wat sample to .wasm (next to it). Requires wat2wasm (wabt).
set -euo pipefail
cd "$(dirname "$0")/wat"
for f in *.wat; do
    wat2wasm "$f" -o "${f%.wat}.wasm" && echo "compiled $f"
done
