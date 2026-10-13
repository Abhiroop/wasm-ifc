#!/usr/bin/env python3
"""The tables of a sweep taken by bench/sweep-labels.sh, as Markdown.

  ./bench/sweep-report.py bench/results/2026-10-13-c2a3f4b

Reads <prefix>.json (the kernels), <prefix>-t2-small.json and <prefix>-t2-medium.json (the
programs), and <prefix>-secrets-small.json and <prefix>-secrets-medium.json, whichever exist.
A kernel's time is net of its runtime's start-up (the `empty` kernel); a program's is not.
Cells under 50 ms take part in no ratio. Ratios are of CPU seconds, medians over the
repetitions; a summary line gives the geometric mean and the range.
"""

from __future__ import annotations

import json, math, sys
from pathlib import Path

FLOOR_S = 0.05
STEPS = Path(__file__).resolve().parent / "results" / "steps.json"


def rows(path: Path) -> dict[tuple[str, str], dict]:
    return {(r["workload"], r["runtime"]): r for r in json.loads(path.read_text())["measurements"] if r.get("ok")}


def gmean(xs: list[float]) -> float:
    return math.exp(sum(math.log(x) for x in xs) / len(xs))


def summary(name: str, xs: list[float]) -> str:
    if not xs:
        return f"- {name}: no workload above the floor"
    return f"- {name}: {gmean(xs):.2f} (geometric mean of {len(xs)}; {min(xs):.2f} to {max(xs):.2f})"


def spread(table: dict, runtime: str) -> str:
    rel = sorted(r["wall_mad_s"] / r["wall_s"] for (_, rt), r in table.items() if rt == runtime and r["wall_s"] > FLOOR_S)
    return f"{100 * rel[len(rel) // 2]:.1f} % (median), {100 * rel[-1]:.1f} % (max)" if rel else "-"


def kernels(path: Path) -> None:
    table = rows(path)
    steps = json.loads(STEPS.read_text()).get("t1", {}) if STEPS.exists() else {}

    def net(workload: str, runtime: str) -> float | None:
        row, base = table.get((workload, runtime)), table.get(("empty", runtime))
        return None if row is None else row["cpu_s"] - (base["cpu_s"] if base else 0.0)

    columns = [("pre-ifc", "before the labels"), ("pre-ifc-opt", "the same, optimized"), ("wasm-ifc", "labelled"), ("erased", "erased")]
    columns = [(rt, title) for rt, title in columns if any(r == rt for _, r in table)]
    against = [rt for rt, _ in columns if rt != "wasm-ifc"] + [rt for rt in ("wabt-interp", "haskell-wasm") if any(r == rt for _, r in table)]
    print("### Kernels\n")
    print("| Kernel | " + " | ".join(f"{title} (s)" for _, title in columns) + " | " + " | ".join(f"labelled / {rt}" for rt in against) + " | ns per step |")
    print("|---|" + "---:|" * (len(columns) + len(against) + 1))
    ratios: dict[str, list[float]] = {rt: [] for rt in against}
    for workload in sorted({w for w, _ in table if w != "empty"}):
        ours = net(workload, "wasm-ifc")
        if ours is None:
            continue
        cells = [f"{net(workload, rt):.3f}" if net(workload, rt) is not None else "-" for rt, _ in columns]
        for rt in against:
            other = net(workload, rt)
            if other is not None and other > FLOOR_S and ours > FLOOR_S:
                ratios[rt].append(ours / other)
                cells.append(f"{ours / other:.2f}")
            else:
                cells.append("-")
        count = steps.get(workload)
        cells.append(f"{1e9 * ours / count:.1f}" if count else "-")
        print(f"| {workload} | " + " | ".join(cells) + " |")
    print()
    for rt in against:
        print(summary(f"labelled / {rt}", ratios[rt]))
    print(f"- spread of the labelled build over the repetitions (relative MAD of wall time): {spread(table, 'wasm-ifc')}\n")


def programs(path: Path, size: str) -> None:
    table = rows(path)
    steps = json.loads(STEPS.read_text()).get("t2", {}) if STEPS.exists() else {}
    ours_first = ["pre-ifc", "pre-ifc-opt"]
    others = [rt for rt in sorted({r for _, r in table}) if rt not in ("wasm-ifc", *ours_first)]
    present = [rt for rt in ours_first if any(r == rt for _, r in table)]
    print(f"### Programs, {size}\n")
    print("| Program | labelled (s) | " + " | ".join(f"labelled / {rt}" for rt in present) + " | ns per step | " + " | ".join(others) + " |")
    print("|---|---:|" + "---:|" * (len(present) + 1 + len(others)))
    ratios: dict[str, list[float]] = {rt: [] for rt in present + others}
    per_step = []
    for workload in sorted({w for w, _ in table}):
        row = table.get((workload, "wasm-ifc"))
        if row is None:
            continue
        ours = row["cpu_s"]
        cells = [f"{ours:.3f}"]
        for rt in present:
            other = table.get((workload, rt), {}).get("cpu_s")
            if other and other > FLOOR_S and ours > FLOOR_S:
                ratios[rt].append(ours / other)
                cells.append(f"{ours / other:.2f}")
            else:
                cells.append("-")
        count = steps.get(workload)
        cells.append(f"{1e9 * ours / count:.1f}" if count else "-")
        if count and ours > FLOOR_S:
            per_step.append(1e9 * ours / count)
        for rt in others:
            other = table.get((workload, rt), {}).get("cpu_s")
            if other and other > FLOOR_S and ours > FLOOR_S:
                ratios[rt].append(ours / other)
                cells.append(f"{ours / other:.0f}×")
            else:
                cells.append("-")
        print(f"| {workload} | " + " | ".join(cells) + " |")
    print()
    for rt in present:
        print(summary(f"labelled / {rt}", ratios[rt]))
    for rt in others:
        print(summary(f"how many times faster {rt} is", ratios[rt]))
    if per_step:
        print(f"- nanoseconds per machine step of the labelled build: {gmean(per_step):.1f} (geometric mean; {min(per_step):.1f} to {max(per_step):.1f})")
    print(f"- spread of the labelled build over the repetitions: {spread(table, 'wasm-ifc')}\n")


def secrets(path: Path, size: str) -> None:
    table = rows(path)
    print(f"### With secrets in memory, {size}\n")
    print("| Kernel | no policy (s) | data secret (s) | ratio | no policy (MB) | data secret (MB) | ratio |")
    print("|---|---:|---:|---:|---:|---:|---:|")
    times, allocations = [], []
    for workload in sorted({w for w, _ in table}):
        plain, secret = table.get((workload, "wasm-ifc")), table.get((workload, "wasm-ifc+secret"))
        if plain is None or secret is None:
            continue
        above = plain["cpu_s"] > FLOOR_S
        if above:
            times.append(secret["cpu_s"] / plain["cpu_s"])
        allocations.append(secret["allocated"] / plain["allocated"])
        ratio = f"{secret['cpu_s'] / plain['cpu_s']:.2f}" if above else "-"
        print(
            f"| {workload.removeprefix('pb-').removesuffix('-silent')} | {plain['cpu_s']:.3f} | {secret['cpu_s']:.3f} | {ratio} | "
            f"{plain['allocated'] / 1e6:.1f} | {secret['allocated'] / 1e6:.1f} | {secret['allocated'] / plain['allocated']:.2f} |"
        )
    print()
    print(summary("time, data secret / no policy", times))
    print(summary("allocation, data secret / no policy", allocations))
    print()


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    prefix = sys.argv[1]
    found = False
    for suffix, show in ((".json", kernels), ("-t2-small.json", lambda p: programs(p, "small")), ("-t2-medium.json", lambda p: programs(p, "medium")), ("-secrets-small.json", lambda p: secrets(p, "small")), ("-secrets-medium.json", lambda p: secrets(p, "medium"))):
        path = Path(prefix + suffix)
        if path.exists():
            found = True
            show(path)
    progress = Path(prefix + ".progress")
    if progress.exists():
        print("### Load while the sweep ran\n\n```\n" + progress.read_text().rstrip() + "\n```")
    return 0 if found else 1


if __name__ == "__main__":
    sys.exit(main())
