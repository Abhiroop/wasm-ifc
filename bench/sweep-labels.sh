#!/usr/bin/env bash
# The timed sweeps behind "the cost of the labels" (BENCHMARKS.md), one after the other so that
# none competes with another: the labelled build against a build from before the labels and
# against its erased copy on the kernels, against the other runtimes on the programs, and with
# secrets in memory (bench/secrets.py). Run it on a quiet machine: a timing is only as good as
# the load it was taken under, which is recorded beside each sweep in <prefix>.progress.
#
#   PRE=/path/to/pre-ifc/wasm-ifc ./bench/sweep-labels.sh [PREFIX]
#
# PRE is a binary of the interpreter built from a commit before the labels (the paper's is
# 0fcf4b4: check it out in a worktree, `cabal build exe:wasm-ifc`, copy the binary). PREFIX
# defaults to bench/results/<date>-<commit>. HASKELL_WASM, if set, is the driver of the Hackage
# interpreter (bench/drivers/haskell-wasm/build.sh prints its path). The other runtimes are
# whichever bench/run.py finds (bench/tools/fetch.sh installs them). MEDIUM=0 skips the two
# medium-size sweeps, which take about two hours.
#
# Needs: bench/build.sh, bench/c/build.sh and bench/c/build-silent.sh run once, and
# `cabal build exe:wasm-ifc bench:wasm-ifc-erased --enable-benchmarks`.
set -uo pipefail
cd "$(dirname "$0")/.."
: "${PRE:?set PRE to a wasm-ifc binary built before the labels}"
PREFIX=${1:-bench/results/$(date +%F)-$(git rev-parse --short HEAD)}
ERASED=$(cabal list-bin bench:wasm-ifc-erased --enable-benchmarks)
PROGRESS=$PREFIX.progress
stamp() { echo "$(date +%H:%M:%S) $1 (load $(cut -d' ' -f1-3 /proc/loadavg))" | tee -a "$PROGRESS"; }
others=(--binary pre-ifc="$PRE" --binary erased="$ERASED")
if [ -n "${HASKELL_WASM:-}" ]; then others+=(--binary haskell-wasm="$HASKELL_WASM"); fi
# On the programs: ours, the build before the labels, and the runtimes that are not ours.
programs=(-r wasm-ifc -r pre-ifc -r wasmi -r wasm3 -r wamr-interp -r wasmtime-pulley -r wasmtime-winch -r wasmtime-cranelift)

stamp "kernels start"
python3 bench/run.py "${others[@]}" --reps 7 -o "$PREFIX.json" > "$PREFIX.kernels.log" 2>&1
stamp "kernels exit $?"
python3 bench/run.py --tier t2 --binary pre-ifc="$PRE" "${programs[@]}" -w coremark-100 -w 'pb-*-small' --reps 7 -o "$PREFIX-t2-small.json" > "$PREFIX.t2-small.log" 2>&1
stamp "programs small exit $?"
python3 bench/secrets.py --size small --reps 7 --plain pre-ifc="$PRE" -o "$PREFIX-secrets-small.json" > "$PREFIX.secrets-small.log" 2>&1
stamp "secrets small exit $?"
if [ "${MEDIUM:-1}" != 0 ]; then
    python3 bench/run.py --tier t2 --binary pre-ifc="$PRE" "${programs[@]}" -w coremark-4000 -w 'pb-*-medium' --reps 3 --timeout 1800 -o "$PREFIX-t2-medium.json" > "$PREFIX.t2-medium.log" 2>&1
    stamp "programs medium exit $?"
    python3 bench/secrets.py --size medium --reps 3 -o "$PREFIX-secrets-medium.json" > "$PREFIX.secrets-medium.log" 2>&1
    stamp "secrets medium exit $?"
fi
