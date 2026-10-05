#!/usr/bin/env bash
# The typed obligations (Runtime.Obligation) make an interpreter that leaves out one of
# SecWasm's run-time checks a type error. This script checks that claim against the library as
# built: test/obligations/Good.hs, the correct step of a load, must type-check, and each
# Wrong*.hs, a step that omits the check, compares with another level, forges the evidence, or
# enters an indirect call's callee unchecked, must be rejected with an error that names what
# expected.txt says. Run after `cabal build`.
set -uo pipefail
cd "$(dirname "$0")/obligations" || exit 2
check () { cabal exec -v0 -- ghc -fno-code -v0 -XGHC2024 -package wasm-ifc -package singletons "$1.hs" 2>&1; }
fail=0
if out=$(check Good); then echo "ok   Good type-checks"; else echo "FAIL Good does not type-check"; echo "$out" | head -20; fail=1; fi
while read -r name needle; do
    if out=$(check "$name"); then echo "FAIL $name type-checks"; fail=1
    elif grep -q "$needle" <<<"$out"; then echo "ok   $name is rejected ($needle)"
    else echo "FAIL $name is rejected for another reason"; echo "$out" | head -20; fail=1
    fi
done < expected.txt
exit $fail
