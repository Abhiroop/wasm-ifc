#!/usr/bin/env bash
# Run each sample through the typed pipeline (decode -> elaborate -> typed interpreter) and
# check it against the expected result.
#
# The expected values are independently known-correct (standard sequences and arithmetic).
# When wasmtime is installed it also serves as a differential oracle: every integer-valued
# check with non-negative arguments is run through `wasmtime run --invoke` as well, and the
# two runtimes must agree (modulo the sign of an i32, which wasmtime prints signed); every
# trap check must trap there too.
#
#   ./samples/check.sh            # build samples + run all checks
set -uo pipefail
cd "$(dirname "$0")/.."

BIN=$(cabal list-bin wasm-ifc 2>/dev/null)
WASMTIME=$(command -v wasmtime || command -v "$HOME/.wasmtime/bin/wasmtime" || true)
./samples/build.sh >/dev/null

pass=0; fail=0; oracle=0

# oracle <wasm> <func> <our output> [args...]: compare against wasmtime where it applies.
oracle () {
    local file=$1 func=$2 ours=$3; shift 3
    [ -n "$WASMTIME" ] || return 0
    case "$ours $*" in *.*|*-*) return 0 ;; esac   # floats and negative arguments: not covered
    local theirs; theirs=$("$WASMTIME" run --invoke "$func" "samples/wat/$file" "$@" 2>/dev/null)
    if [ "$theirs" = "$ours" ] || { [[ "$theirs" =~ ^-?[0-9]+$ ]] && [ $(( (ours - theirs) % 4294967296 )) -eq 0 ]; }
        then oracle=$((oracle+1))
        else printf 'FAIL %-22s %-10s %s : wasmtime says %q, we say %q\n' "$file" "$func" "$*" "$theirs" "$ours"; fail=$((fail+1))
    fi
}

# oracleTrap <wasm> <func> [args...]: wasmtime must trap (exit non-zero) as well.
oracleTrap () {
    local file=$1 func=$2; shift 2
    [ -n "$WASMTIME" ] || return 0
    if "$WASMTIME" run --invoke "$func" "samples/wat/$file" "$@" >/dev/null 2>&1
        then printf 'FAIL %-22s %-10s %s : wasmtime does not trap\n' "$file" "$func" "$*"; fail=$((fail+1))
        else oracle=$((oracle+1))
    fi
}

# check <wasm> <func> <expected> [args...]
check () {
    local file=$1 func=$2 expected=$3; shift 3
    local out; out=$("$BIN" invoke "samples/wat/$file" "$func" "$@" 2>&1)
    local label; label=$(printf '%-22s %-10s %s' "$file" "$func" "$*")
    if [ "$out" = "$expected" ]
        then printf 'ok   %s = %s\n' "$label" "$out"; pass=$((pass+1)); oracle "$file" "$func" "$out" "$@"
        else printf 'FAIL %s : got %q expected %q\n' "$label" "$out" "$expected"; fail=$((fail+1))
    fi
}

# checkTrap <wasm> <func> <trap-substring> [args...]
# A genuine runtime trap that the typed layer's stack typing cannot rule out (division by
# zero, out-of-bounds access) — the interpreter must report it, not crash.
checkTrap () {
    local file=$1 func=$2 needle=$3; shift 3
    local out; out=$("$BIN" invoke "samples/wat/$file" "$func" "$@" 2>&1)
    local label; label=$(printf '%-22s %-10s %s' "$file" "$func" "$*")
    if [[ "$out" == *"$needle"* ]]
        then printf 'ok   %s -> trap (%s)\n' "$label" "$needle"; pass=$((pass+1)); oracleTrap "$file" "$func" "$@"
        else printf 'FAIL %s : got %q (want trap %q)\n' "$label" "$out" "$needle"; fail=$((fail+1))
    fi
}

# checkRun <wasm in samples/wasi> <expected stdout> <expected exit code>
# A WASI program: its _start export runs under the host; stdout and the exit code are checked.
checkRun () {
    local file=$1 expectedOut=$2 expectedCode=$3
    local out; out=$("$BIN" run "samples/wasi/$file" 2>/dev/null); local code=$?
    local label; label=$(printf '%-22s %-10s' "$file" "run")
    if [ "$out" = "$expectedOut" ] && [ "$code" -eq "$expectedCode" ]
        then printf 'ok   %s -> %q, exit %s\n' "$label" "$out" "$code"; pass=$((pass+1))
        else printf 'FAIL %s : got %q exit %s, expected %q exit %s\n' "$label" "$out" "$code" "$expectedOut" "$expectedCode"; fail=$((fail+1))
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
check args.wasm      callsub  7       10 3
check args.wasm      mixed    9       5 9
check args.wasm      multi    4294967295
check counter.wasm   bump     1105    5
check memory.wasm    roundtrip 42     21
check absval.wasm    abs      42      -42
check nested_br.wasm nested   4
check hypot.wasm     hypot    5.0     3 4
check floats.wasm    faddmul  21.0    3 4
check floats.wasm    f32div   2.5     5 2
check bigmul.wasm    bigmul   1000000000000 1000000 1000000
check widen.wasm     widen    5       5
check power.wasm     power    1024    2 10
check power.wasm     power    243     3 5
check collatz.wasm   collatz  111     27
check collatz.wasm   collatz  8       6
check memreverse.wasm memreverse 9    10

checkTrap divs.wasm divs IntegerDivideByZero       7 0
checkRun hello.wasm "Hello, world!" 0
checkRun exit.wasm  ""              7
checkTrap oob.wasm  oob  OutOfBoundsMemoryAccess    1000000

echo "-----"
if [ -n "$WASMTIME" ]; then echo "wasmtime agreed on $oracle checks"; else echo "(wasmtime not installed: no differential oracle)"; fi
echo "passed: $pass   failed: $fail"
[ "$fail" -eq 0 ]
