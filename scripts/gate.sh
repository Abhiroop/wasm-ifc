#!/usr/bin/env bash
# Local gate: format, -Werror build, tests, lint, samples, cross-validate. One line per stage;
# on failure it prints the first lines of the offending output and exits non-zero.
#
#   ./scripts/gate.sh                      # everything (spec + wasi suites are slow)
#   SUITES=wasm-ifc-test ./scripts/gate.sh # the fast core loop: unit tests only
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2
LOG=$(mktemp)
fourmolu -i $(git ls-files -m -o --exclude-standard 'src/*.hs' 'app/*.hs' 'test/*.hs' 2>/dev/null) >/dev/null 2>&1
if ! cabal build all --ghc-options=-Werror >"$LOG" 2>&1; then echo "BUILD FAILED"; grep -n -A12 -iE "error" "$LOG" | head -60; exit 1; fi
echo "build ok"
if ! cabal test ${SUITES:-} >"$LOG" 2>&1; then echo "TESTS FAILED"; grep -E "Failure|expected|but got|examples" "$LOG" | head -40; exit 1; fi
grep -E "examples, 0 failures" "$LOG"
if ! fourmolu --mode check src app test >"$LOG" 2>&1; then echo "FOURMOLU FAILED"; head -20 "$LOG"; exit 1; fi
H=$(hlint src app test 2>&1); if [ "$H" != "No hints" ]; then echo "HLINT: $H" | head -30; exit 1; fi
echo "lint ok"
if ! ./samples/check.sh >"$LOG" 2>&1; then echo "SAMPLES FAILED"; grep -E "FAIL|passed" "$LOG" | head -20; exit 1; fi
tail -1 "$LOG"
if ! ./samples/validate.sh >"$LOG" 2>&1; then echo "VALIDATE FAILED"; head -20 "$LOG"; exit 1; fi
tail -1 "$LOG"
