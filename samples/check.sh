#!/usr/bin/env bash
# Run each sample through the typed pipeline (decode -> elaborate -> typed interpreter) and
# check it against the expected result.
#
# The expected values are independently known-correct (standard sequences and arithmetic),
# so they are the oracle now that the untyped interpreter — which used to serve as a
# differential reference — has been removed. If a CLI runtime that can invoke an export with
# arguments is available (e.g. `wasmtime --invoke`), it would make a good external oracle to
# layer on top; wabt's `wasm-interp` only runs exports with zero arguments.
#
#   ./samples/check.sh            # build samples + run all checks
set -uo pipefail
cd "$(dirname "$0")/.."

BIN=$(cabal list-bin wasm-ifc 2>/dev/null)
./samples/build.sh >/dev/null

pass=0; fail=0

# check <wasm> <func> <expected> [args...]
check () {
    local file=$1 func=$2 expected=$3; shift 3
    local out; out=$("$BIN" "samples/wat/$file" "$func" "$@")
    local label; label=$(printf '%-22s %-10s %s' "$file" "$func" "$*")
    if [ "$out" = "$expected" ]
        then printf 'ok   %s = %s\n' "$label" "$out"; pass=$((pass+1))
        else printf 'FAIL %s : got %q expected %q\n' "$label" "$out" "$expected"; fail=$((fail+1))
    fi
}

# checkTrap <wasm> <func> <trap-substring> [args...]
# A genuine runtime trap that the typed layer's stack typing cannot rule out (division by
# zero, out-of-bounds access) — the interpreter must report it, not crash.
checkTrap () {
    local file=$1 func=$2 needle=$3; shift 3
    local out; out=$("$BIN" "samples/wat/$file" "$func" "$@")
    local label; label=$(printf '%-22s %-10s %s' "$file" "$func" "$*")
    if [[ "$out" == *"$needle"* ]]
        then printf 'ok   %s -> trap (%s)\n' "$label" "$needle"; pass=$((pass+1))
        else printf 'FAIL %s : got %q (want trap %q)\n' "$label" "$out" "$needle"; fail=$((fail+1))
    fi
}

check factorial.wasm fac      3628800 10
check factorial.wasm fac      120     5
check recfac.wasm    fac      720     6
check fib.wasm       fib      55      10
check fib.wasm       fib      6765    20
check gcd.wasm       gcd      21      252 105
check gcd.wasm       gcd      1       17 5
check arraysum.wasm  arraysum 45      10
check arraysum.wasm  arraysum 4950    100
check bits.wasm      popcnt   3       7
check bits.wasm      popcnt   8       255
check bits.wasm      combine  13330   18 52
check evenodd.wasm   isEven   1       10
check evenodd.wasm   isOdd    0       10
check evenodd.wasm   isEven   0       7
check call.wasm      square   81      9
check counter.wasm   bump     1105    5
check memory.wasm    roundtrip 42     21
check absval.wasm    abs      42      -42
check nested_br.wasm nested   4
check hypot.wasm     hypot    5.0     3 4
check bigmul.wasm    bigmul   1000000000000 1000000 1000000
check widen.wasm     widen    5       5
check power.wasm     power    1024    2 10
check power.wasm     power    243     3 5
check collatz.wasm   collatz  111     27
check collatz.wasm   collatz  8       6
check memreverse.wasm memreverse 9    10

checkTrap divs.wasm divs IntegerDivideByZero       7 0
checkTrap oob.wasm  oob  OutOfBoundsMemoryAccess    1000000

echo "-----"
echo "passed: $pass   failed: $fail"
[ "$fail" -eq 0 ]
