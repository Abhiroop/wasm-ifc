#!/usr/bin/env python3
"""A quick check that a change has not made the interpreter allocate more per machine step.

Allocation is deterministic, so unlike a timing it needs no quiet machine and no repetitions,
and it moves with every regression this project's benchmarks have found: a laziness leak (E0),
a `step` no longer inlined and a configuration record built on every step (E1), memory copied
on every store (E6). A run takes well under a minute. It does not replace timing: at a larger
milestone, time the new build against a saved binary of the previous one inside a single sweep
(`run.py --binary before=PATH -r before -r wasm-ifc`), since only an interleaved sweep can be
trusted on this machine.

  ./bench/tripwire.py              # compare the current build with bench/allocation.txt
  ./bench/tripwire.py --record     # make the current build the reference
  WASM_IFC_BIN=/path/to/wasm-ifc ./bench/tripwire.py

Exits non-zero when a workload allocates more than --tolerance (default 2 %) above its
reference. CoreMark's step count moves by a few dozen steps between runs, because it formats
timings, which is far inside that.
"""

from __future__ import annotations

import argparse, json, os, re, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REFERENCE = ROOT / "bench" / "allocation.txt"
STEPS = ROOT / "bench" / "results" / "steps.json"
# One workload per cost that has regressed before: calls, dispatch, locals, indirect calls,
# blocks, scattered memory, and three real programs, which weigh memory the way code does.
WORKLOADS = [
    ("t1", "fib"), ("t1", "loop-arith"), ("t1", "locals-16"), ("t1", "call-indirect"),
    ("t1", "labels-16"), ("t1", "memory-random"),
    ("t2", "coremark-100"), ("t2", "pb-2mm-small"), ("t2", "pb-seidel-2d-small"),
]


def allocated(binary: str, tier: str, name: str) -> int:
    module = ROOT / "bench" / ("wasm" if tier == "t1" else "wasm-t2") / f"{name}.wasm"
    argv = [binary, "invoke", str(module), "run"] if tier == "t1" else [binary, "run", str(module)]
    done = subprocess.run(argv + ["+RTS", "-s", "-RTS"], capture_output=True, text=True, timeout=600)
    match = re.search(r"([\d,]+) bytes allocated", done.stderr)
    if done.returncode != 0 or not match:
        raise SystemExit(f"{name}: no allocation figure (exit {done.returncode})")
    return int(match.group(1).replace(",", ""))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--record", action="store_true", help="write the current build's figures as the reference")
    ap.add_argument("--tolerance", type=float, default=0.02, help="allowed growth before failing (fraction)")
    args = ap.parse_args()

    binary = os.environ.get("WASM_IFC_BIN") or subprocess.run(
        ["cabal", "list-bin", "wasm-ifc"], cwd=ROOT, capture_output=True, text=True
    ).stdout.strip()
    missing = [n for t, n in WORKLOADS if not (ROOT / "bench" / ("wasm" if t == "t1" else "wasm-t2") / f"{n}.wasm").exists()]
    if missing:
        print(f"missing modules {missing}: run bench/build.sh and bench/c/build.sh", file=sys.stderr)
        return 2
    steps = json.loads(STEPS.read_text()) if STEPS.exists() else {}
    now = {name: allocated(binary, tier, name) for tier, name in WORKLOADS}

    if args.record:
        commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
        dirty = subprocess.run(["git", "status", "--porcelain", "--", "src", "app"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
        REFERENCE.write_text(
            "# Bytes allocated by each tripwire workload; written by bench/tripwire.py --record.\n"
            f"# build: {commit}{'-dirty' if dirty else ''}, {time.strftime('%Y-%m-%d')}\n"
            + "".join(f"{name} {now[name]}\n" for _, name in WORKLOADS)
        )
        print(f"recorded {len(now)} workloads in {REFERENCE.relative_to(ROOT)}")
        return 0

    if not REFERENCE.exists():
        print(f"no reference yet: run {Path(__file__).name} --record", file=sys.stderr)
        return 2
    reference = dict(line.split() for line in REFERENCE.read_text().splitlines() if line and not line.startswith("#"))
    print(f"{'workload':20s} {'reference MB':>13s} {'now MB':>9s} {'change':>8s} {'bytes/step':>11s}")
    failed = []
    for tier, name in WORKLOADS:
        ref, cur = int(reference[name]), now[name]
        change = cur / ref - 1
        count = steps.get(tier, {}).get(name)
        per_step = f"{cur / count:11.1f}" if count else f"{'—':>11s}"
        flag = "  <-- grew" if change > args.tolerance else ""
        print(f"{name:20s} {ref / 1e6:13.1f} {cur / 1e6:9.1f} {change:+8.1%} {per_step}{flag}")
        if change > args.tolerance:
            failed.append(name)
    print(f"\n{'allocation grew on: ' + ', '.join(failed) if failed else 'no workload allocates more than the reference'}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
