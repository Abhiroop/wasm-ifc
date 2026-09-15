#!/usr/bin/env bash
# Run benchmark kernels once on our interpreter and check their checksums. A correctness
# check on the kernels — that they still decode, validate and run to the value every runtime
# agreed on — not a measurement.
#
# This is a manual tool, not a gate stage: a full pass takes minutes (the kernels are sized
# to be slow on purpose) and adds no coverage that the spec suite does not already give.
# Run it after editing bench/gen.py or anything the interpreter's hot path touches.
#
#   ./bench/smoke.sh              # every kernel
#   ./bench/smoke.sh fib float    # just these
set -uo pipefail
cd "$(dirname "$0")/.."

# WASM_IFC_BIN checks another build, such as the erased machine: it must give the same answers.
BIN=${WASM_IFC_BIN:-$(cabal list-bin wasm-ifc 2>/dev/null)} || { echo "cannot find wasm-ifc"; exit 2; }
pass=0; fail=0; started=$SECONDS

while read -r name expected; do
    case "$name" in '#'*|'') continue ;; esac
    if [ $# -gt 0 ]; then
        case " $* " in *" $name "*) ;; *) continue ;; esac
    fi
    got=$("$BIN" invoke "bench/wasm/$name.wasm" run 2>&1)
    if [ "$got" = "$expected" ]
        then printf 'ok   %-16s %s\n' "$name" "$got"; pass=$((pass+1))
        else printf 'FAIL %-16s got %q expected %q\n' "$name" "$got" "$expected"; fail=$((fail+1))
    fi
done < bench/checksums.txt

echo "kernels: $pass ok, $fail failed, $((SECONDS-started))s"
[ "$fail" -eq 0 ]
