#!/usr/bin/env python3
"""Turn bench/results/*.json into the tables that go in the write-up.

  ./bench/report.py                       # the newest result file
  ./bench/report.py a.json b.json         # b against a, workload by workload
"""

from __future__ import annotations

import argparse, json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "bench" / "results"
# The reference runtime every ratio is taken against, and the empty-module kernel whose time
# is process start-up rather than interpretation.
OURS = "wasm-ifc"
BASELINE = "empty"
# Below this, a net time is start-up subtraction noise rather than a measurement: the kernels
# are sized for an interpreter, so a JIT finishes them inside the spread of its own start-up.
# Such cells are shown as an upper bound and take part in no ratio.
FLOOR_S = 0.05


def load(path: Path) -> tuple[dict, dict[tuple[str, str], dict]]:
    blob = json.loads(path.read_text())
    rows = {(r["workload"], r["runtime"]): r for r in blob["measurements"] if r.get("ok")}
    return blob["environment"], rows


def net(rows: dict[tuple[str, str], dict], workload: str, runtime: str) -> float | None:
    """CPU seconds of the interpretation itself: the run, less the runtime's own start-up."""
    row = rows.get((workload, runtime))
    if row is None:
        return None
    start_up = rows.get((BASELINE, runtime))
    return max(row["cpu_s"] - (start_up["cpu_s"] if start_up else 0.0), 0.0)


def cell(rows: dict[tuple[str, str], dict], workload: str, runtime: str) -> str:
    seconds = net(rows, workload, runtime)
    if seconds is None:
        return "—"
    return f"<{FLOOR_S}" if seconds < FLOOR_S else f"{seconds:.4f}"


def axes(rows: dict[tuple[str, str], dict]) -> tuple[list[str], list[str]]:
    workloads = sorted({w for w, _ in rows if w != BASELINE})
    runtimes = sorted({r for _, r in rows}, key=lambda r: (r != OURS, r))
    return workloads, runtimes


def table(header: list[str], body: list[list[str]]) -> str:
    widths = [max(len(str(row[i])) for row in [header, *body]) for i in range(len(header))]
    line = lambda cells: "| " + " | ".join(str(c).ljust(w) for c, w in zip(cells, widths)) + " |"
    rule = "|" + "|".join("-" * (w + 2) for w in widths) + "|"
    return "\n".join([line(header), rule, *(line(r) for r in body)])


def one(path: Path) -> None:
    env, rows = load(path)
    workloads, runtimes = axes(rows)
    print(f"### {path.name}\n")
    print(f"{env['commit']} · {env['cpu']} · {env['ghc']} · {env['date']}")
    print(f"start-up subtracted per runtime (the `{BASELINE}` kernel); CPU seconds, median of {rows[next(iter(rows))]['reps']}\n")
    print(table(["workload", *runtimes], [[w, *[cell(rows, w, r) for r in runtimes]] for w in workloads]))
    others = [r for r in runtimes if r != OURS]
    if others:
        print(f"\nHow many times faster than `{OURS}`; blank where their time is under the {FLOOR_S}s floor:\n")
        def ratio(w: str, r: str) -> str:
            mine, theirs = net(rows, w, OURS), net(rows, w, r)
            if not mine or not theirs or theirs < FLOOR_S:
                return "—"
            return f"{mine / theirs:.0f}x"
        print(table(["workload", *others], [[w, *[ratio(w, r) for r in others]] for w in workloads]))


def compare(before: Path, after: Path) -> None:
    _, old = load(before)
    env, new = load(after)
    workloads, runtimes = axes(new)
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
    args = ap.parse_args()
    files = args.files or sorted(RESULTS.glob("*.json"))[-1:]
    if not files:
        print(f"no results in {RESULTS}", file=sys.stderr)
        return 2
    if len(files) == 2:
        compare(*files)
    else:
        for path in files:
            one(path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
