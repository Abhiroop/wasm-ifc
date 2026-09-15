#!/usr/bin/env python3
"""Count the machine steps of workloads once, and keep the counts.

A step count belongs to a program and its input, not to a runtime or a run, so it only ever
needs taking once per module — and taking it is slow for big inputs (it runs our interpreter
with GHC's ticky-ticky counters). This records counts in bench/results/steps.json, merged by
module, and `report.py --steps` uses them for results that were timed without `--ticky`.

  ./bench/steps.py --ticky "$(cabal list-bin exe:wasm-ifc --builddir=/tmp/ticky)" --tier t2 -w 'pb-*-medium'
"""

from __future__ import annotations

import argparse, fnmatch, importlib.util, json, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("bench_run", HERE / "run.py")
bench_run = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bench_run)

STEPS = HERE / "results" / "steps.json"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ticky", required=True, metavar="PATH", help="a ticky-instrumented build of ours")
    ap.add_argument("--tier", choices=sorted(bench_run.TIERS), default="t1")
    ap.add_argument("-w", "--workload", action="append", help="glob patterns over module names")
    ap.add_argument("--timeout", type=float, default=7200.0)
    args = ap.parse_args()

    counts = json.loads(STEPS.read_text()) if STEPS.exists() else {}
    tier = counts.setdefault(args.tier, {})
    modules = [m for m in sorted(bench_run.TIERS[args.tier].glob("*.wasm")) if not m.stem.endswith("-dump")]
    modules = [m for m in modules if not args.workload or any(fnmatch.fnmatch(m.stem, p) for p in args.workload)]
    for module in modules:
        if module.stem in tier:
            print(f"{module.stem:24s} {tier[module.stem]:>16,} (already counted)")
            continue
        count = bench_run.count_steps(args.ticky, args.tier, module, args.timeout)
        if count is None:
            print(f"{module.stem:24s} could not be counted", file=sys.stderr)
            continue
        tier[module.stem] = count
        STEPS.write_text(json.dumps(counts, indent=2, sort_keys=True) + "\n")
        print(f"{module.stem:24s} {count:>16,}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
