#!/usr/bin/env bash
# The typed obligations (Runtime.Obligation) make an interpreter that leaves out one of
# SecWasm's run-time checks a type error. This script checks that claim against the library as
# built: test/obligations/Good.hs, the correct step of a load, must type-check, and each
# Wrong*.hs, a step that omits the check, compares with another level, forges the evidence, or
# enters an indirect call's callee unchecked, must be rejected with an error that names what
# expected.txt says. Run after `cabal build`.
#
# The same check for a typing rule: GoodBrTable.hs is the `br_table` of the paper's first
# finding as the repaired rule types it, and WrongBrTablePrintedRule.hs is the same table as
# SecWasm's printed rule types it, raising as many entries as it has targets. The second must
# be rejected: a target cannot lie deeper than the raise, because one witness gives both.
set -uo pipefail
cd "$(dirname "$0")/obligations" || exit 2
check () { cabal exec -v0 -- ghc -fno-code -v0 -XGHC2024 -package wasm-ifc -package singletons "$1.hs" 2>&1; }
fail=0
for good in Good GoodBrTable; do
    if out=$(check "$good"); then echo "ok   $good type-checks"; else echo "FAIL $good does not type-check"; echo "$out" | head -20; fail=1; fi
done
while read -r name needle; do
    if out=$(check "$name"); then echo "FAIL $name type-checks"; fail=1
    elif grep -q "$needle" <<<"$out"; then echo "ok   $name is rejected ($needle)"
    else echo "FAIL $name is rejected for another reason"; echo "$out" | head -20; fail=1
    fi
done < expected.txt
exit $fail
