#!/usr/bin/env python3
"""Turn bench/results/*.json into the tables that go in the write-up.

  ./bench/report.py                          # the newest result file
  ./bench/report.py results.json --versus erased
  ./bench/report.py a.json b.json            # b against a, workload by workload
  ./bench/report.py compilers.json --steps bench/results/steps.json
"""

from __future__ import annotations

import argparse, json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "bench" / "results"
# The empty-module kernel, whose time is process start-up rather than interpretation.
BASELINE = "empty"
# Below this, a net time is start-up subtraction noise rather than a measurement: the kernels
# are sized for an interpreter, so a JIT finishes them inside the spread of its own start-up.
# Such cells are shown as an upper bound and take part in no ratio.
FLOOR_S = 0.05


def load(path: Path, counted: dict[str, dict[str, int]] | None = None) -> tuple[dict, dict[tuple[str, str], dict]]:
    """A results file's rows, with step counts filled in from `counted` where the run had none."""
    blob = json.loads(path.read_text())
    rows = {(r["workload"], r["runtime"]): r for r in blob["measurements"] if r.get("ok")}
    tier = (counted or {}).get(blob["environment"].get("tier", "t1"), {})
    for (workload, _), row in rows.items():
        if not row.get("steps") and workload in tier:
            row["steps"] = tier[workload]
    return blob["environment"], rows


def net(rows: dict[tuple[str, str], dict], workload: str, runtime: str) -> float | None:
    """CPU seconds of the interpretation itself: the run, less the runtime's own start-up."""
    row = rows.get((workload, runtime))
    if row is None:
        return None
    start_up = rows.get((BASELINE, runtime))
    return max(row["cpu_s"] - (start_up["cpu_s"] if start_up else 0.0), 0.0)


def steps(rows: dict[tuple[str, str], dict], workload: str) -> int | None:
    return next((r["steps"] for (w, _), r in rows.items() if w == workload and r.get("steps")), None)


def cell(rows: dict[tuple[str, str], dict], workload: str, runtime: str) -> str:
    seconds = net(rows, workload, runtime)
    if seconds is None:
        return "—"
    return f"<{FLOOR_S}" if seconds < FLOOR_S else f"{seconds:.4f}"


def per_step(rows: dict[tuple[str, str], dict], workload: str, runtime: str) -> str:
    seconds, count = net(rows, workload, runtime), steps(rows, workload)
    if seconds is None or not count:
        return "—"
    return f"<{FLOOR_S / count * 1e9:.1f}" if seconds < FLOOR_S else f"{seconds / count * 1e9:.1f}"


def axes(rows: dict[tuple[str, str], dict], first: str) -> tuple[list[str], list[str]]:
    workloads = sorted({w for w, _ in rows if w != BASELINE})
    runtimes = sorted({r for _, r in rows}, key=lambda r: (r != first, r))
    return workloads, runtimes


def table(header: list[str], body: list[list[str]]) -> str:
    widths = [max(len(str(row[i])) for row in [header, *body]) for i in range(len(header))]
    line = lambda cells: "| " + " | ".join(str(c).ljust(w) for c, w in zip(cells, widths)) + " |"
    rule = "|" + "|".join("-" * (w + 2) for w in widths) + "|"
    return "\n".join([line(header), rule, *(line(r) for r in body)])


def one(path: Path, versus: str, counted: dict[str, dict[str, int]] | None) -> None:
    env, rows = load(path, counted)
    workloads, runtimes = axes(rows, versus)
    reps = rows[next(iter(rows))]["reps"]
    print(f"### {path.name}\n")
    print(f"{env['commit']} · {env['cpu']} · {env['ghc']} · {env['date']}")
    print(f"CPU seconds, median of {reps}, each runtime's start-up (the `{BASELINE}` kernel) subtracted\n")
    print(table(["workload", *runtimes], [[w, *[cell(rows, w, r) for r in runtimes]] for w in workloads]))
    if any(steps(rows, w) for w in workloads):
        print("\nNanoseconds per machine step (the step count is the program's, the same for every runtime):\n")
        print(table(["workload", "steps", *runtimes], [[w, f"{steps(rows, w) or 0:,}", *[per_step(rows, w, r) for r in runtimes]] for w in workloads]))
    others = [r for r in runtimes if r != versus]
    if others and any((w, versus) in rows for w in workloads):
        print(f"\nTime relative to `{versus}` (above 1: slower than it; blank where either is under the {FLOOR_S}s floor):\n")

        def ratio(w: str, r: str) -> str:
            base, theirs = net(rows, w, versus), net(rows, w, r)
            if base is None or theirs is None or base < FLOOR_S or theirs < FLOOR_S:
                return "—"
            return f"{theirs / base:.2f}"

        print(table(["workload", *others], [[w, *[ratio(w, r) for r in others]] for w in workloads]))


def compare(before: Path, after: Path) -> None:
    _, old = load(before)
    env, new = load(after)
    workloads, runtimes = axes(new, "wasm-ifc")
    print(f"### {after.name} against {before.name}\n")
    print(f"{env['commit']} · CPU seconds, start-up subtracted; speed-up = before / after\n")
    body = []
    for w in workloads:
        row = [w]
        for r in runtimes:
            was, now = net(old, w, r), net(new, w, r)
            row.append(f"{was:.4f} -> {now:.4f} ({was / now:.2f}x)" if was and now else "—")
        body.append(row)
    print(table(["workload", *runtimes], body))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="*", type=Path)
    ap.add_argument("--versus", default="wasm-ifc", help="the runtime every ratio is taken against")
    ap.add_argument("--steps", type=Path, help="step counts recorded by bench/steps.py, for runs timed without --ticky")
    args = ap.parse_args()
    counted = json.loads(args.steps.read_text()) if args.steps else None
    files = args.files or sorted(RESULTS.glob("*.json"))[-1:]
    if not files:
        print(f"no results in {RESULTS}", file=sys.stderr)
        return 2
    if len(files) == 2:
        compare(*files)
    else:
        for path in files:
            one(path, args.versus, counted)
    return 0


if __name__ == "__main__":
    sys.exit(main())
