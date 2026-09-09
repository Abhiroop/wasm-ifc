#!/usr/bin/env bash
# Every sample must be accepted by both wabt's wasm-validate and our own `check`: a
# disagreement is a validator bug on one side. (The spec testsuite's assert_invalid cases cover
# the rejecting direction.)
set -uo pipefail
cd "$(dirname "$0")/.."

BIN=$(cabal list-bin wasm-ifc 2>/dev/null)
./samples/build.sh >/dev/null

fail=0
for f in samples/wat/*.wasm samples/wasi/*.wasm; do
    if ! wasm-validate "$f" >/dev/null 2>&1; then echo "wasm-validate rejects $f"; fail=1; fi
    if ! "$BIN" check "$f" >/dev/null 2>&1; then echo "wasm-ifc rejects $f"; fail=1; fi
done
if [ "$fail" -eq 0 ]; then echo "all samples validate on both sides"; fi
exit "$fail"
