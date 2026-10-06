#!/usr/bin/env python3
"""What the labels cost when secrets are really in memory.

Each PolyBench kernel of bench/wasm-t2-silent/ (bench/c/build-silent.sh: the kernels with their
printing compiled out) is run twice by the same binary: without a policy, where every byte is
public and the label map stays empty, and under a policy that declares the kernel's data
secret where `main` writes it and the loads of `main` secret,

    store-default func <main> : H
    load-default func <main> : H

so that every store writes a secret label and every loaded value is secret. The ratio of the
two is the cost of the label map and of the labelled stores. `--plain NAME=PATH` adds another
build of the interpreter, run without a policy only (a build from before the labels knows none).

The method is bench/run.py's: one warm-up each, then the repetitions round-robin across the
configurations of a workload, child CPU seconds, the median. Allocation is read once per
configuration from GHC's `+RTS -s`, as bench/tripwire.py reads it; it is deterministic, so it
holds whatever else the machine is doing, which the timings do not. The load average at the
start and the end of the sweep is recorded with the results for that reason.

  ./bench/c/build-silent.sh
  ./bench/secrets.py                                  # the small sizes
  ./bench/secrets.py --size medium --reps 3
  ./bench/secrets.py --plain before=/path/to/old/wasm-ifc
"""

from __future__ import annotations

import argparse, fnmatch, json, platform, re, resource, subprocess, sys, tempfile, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MODULES = ROOT / "bench" / "wasm-t2-silent"
STEPS = ROOT / "bench" / "results" / "steps.json"


def main_index(module: Path) -> int | None:
    """The index of `main` in the module's function index space, from its name section."""
    listing = subprocess.run(["wasm-objdump", "-x", str(module)], capture_output=True, text=True).stdout
    found = re.search(r"^ - func\[(\d+)\] sig=\d+ <main>", listing, re.M)
    return int(found.group(1)) if found else None


def once(argv: list[str], timeout: float) -> tuple[float, float, int]:
    """Run once; return wall seconds, child CPU seconds, exit code."""
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.perf_counter()
    try:
        code = subprocess.run(argv, capture_output=True, timeout=timeout).returncode
    except subprocess.TimeoutExpired:
        code = -1
    wall = time.perf_counter() - start
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    return wall, (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime), code


def allocated(argv: list[str], timeout: float) -> int | None:
    try:
        done = subprocess.run(argv + ["+RTS", "-s", "-RTS"], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None
    found = re.search(r"([\d,]+) bytes allocated", done.stderr)
    return int(found.group(1).replace(",", "")) if done.returncode == 0 and found else None


def median(xs: list[float]) -> float:
    s = sorted(xs)
    mid = len(s) // 2
    return s[mid] if len(s) % 2 else (s[mid - 1] + s[mid]) / 2


def mad(xs: list[float]) -> float:
    m = median(xs)
    return median([abs(x - m) for x in xs])


def loadavg() -> str:
    try:
        return " ".join(Path("/proc/loadavg").read_text().split()[:3])
    except OSError:
        return "?"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--size", choices=["small", "medium"], default="small")
    ap.add_argument("-w", "--workload", action="append", help="restrict to these kernels (glob patterns on the module name)")
    ap.add_argument("--reps", type=int, default=7, help="timed repetitions (plus one warm-up)")
    ap.add_argument("--timeout", type=float, default=1800.0)
    ap.add_argument("--binary", metavar="PATH", help="the build to measure (default: cabal list-bin exe:wasm-ifc)")
    ap.add_argument("--plain", action="append", default=[], metavar="NAME=PATH", help="another build, run without a policy only")
    ap.add_argument("-o", "--out", help="results file (default bench/results/<date>-<commit>-secrets-<size>.json)")
    args = ap.parse_args()

    ours = args.binary or subprocess.run(["cabal", "list-bin", "exe:wasm-ifc"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    if not ours:
        print("no wasm-ifc binary", file=sys.stderr)
        return 2
    plain = dict(spec.split("=", 1) for spec in args.plain)
    wanted = lambda m: not args.workload or any(fnmatch.fnmatch(m.stem, pattern) for pattern in args.workload)
    modules = [m for m in sorted(MODULES.glob(f"pb-*-{args.size}-silent.wasm")) if wanted(m)]
    if not modules:
        print(f"no kernels in {MODULES}: run bench/c/build-silent.sh", file=sys.stderr)
        return 2
    steps = json.loads(STEPS.read_text()).get("t2", {}) if STEPS.exists() else {}
    load_before = loadavg()

    rows = []
    with tempfile.TemporaryDirectory() as scratch:
        for module in modules:
            index = main_index(module)
            if index is None:
                print(f"{module.stem:34s} no `main` in the name section", flush=True)
                continue
            policy = Path(scratch) / f"{module.stem}.policy"
            policy.write_text(f"store-default func {index} : H\nload-default func {index} : H\n")
            configurations = {"wasm-ifc": [ours, "run", str(module)], "wasm-ifc+secret": [ours, "run", "--policy", str(policy), str(module)]}
            configurations.update({name: [path, "run", str(module)] for name, path in plain.items()})
            live = {name: argv for name, argv in configurations.items() if once(argv, args.timeout)[2] == 0}
            for name in configurations.keys() - live.keys():
                print(f"{module.stem:34s} {name:18s} unavailable", flush=True)
                rows.append({"workload": module.stem, "runtime": name, "ok": False})
            walls: dict[str, list[float]] = {name: [] for name in live}
            cpus: dict[str, list[float]] = {name: [] for name in live}
            broken: set[str] = set()
            for _ in range(args.reps):
                for name, argv in live.items():
                    if name in broken:
                        continue
                    wall, cpu, code = once(argv, args.timeout)
                    if code != 0:
                        broken.add(name)
                        continue
                    walls[name].append(wall)
                    cpus[name].append(cpu)
            for name, argv in live.items():
                if name in broken:
                    rows.append({"workload": module.stem, "runtime": name, "ok": False})
                    continue
                row = {
                    "workload": module.stem,
                    "runtime": name,
                    "ok": True,
                    "cpu_s": median(cpus[name]),
                    "cpu_mad_s": mad(cpus[name]),
                    "wall_s": median(walls[name]),
                    "wall_mad_s": mad(walls[name]),
                    "reps": args.reps,
                    "allocated": allocated(argv, args.timeout),
                }
                # The silent kernel runs the same kernel as the timing build of bench/c/build.sh.
                counted = steps.get(module.stem.removesuffix("-silent"))
                if counted:
                    row["steps_of_timing_build"] = counted
                rows.append(row)
                megabytes = f"{row['allocated'] / 1e6:10.1f} MB" if row["allocated"] else "         ? MB"
                print(f"{module.stem:34s} {name:18s} {row['cpu_s']:8.3f}s cpu (mad {row['cpu_mad_s']:.3f})  {megabytes}", flush=True)

    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(["git", "status", "--porcelain", "--", "src", "app", "wasm-ifc.cabal", "cabal.project"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    cpu = next((line.split(":", 1)[1].strip() for line in open("/proc/cpuinfo") if line.startswith("model name")), "?")
    environment = {
        "date": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "commit": commit + ("-dirty" if dirty else ""),
        "size": args.size,
        "cpu": cpu,
        "kernel": platform.release(),
        "binaries": {"wasm-ifc": ours, **plain},
        "policy": "store-default func <main> : H; load-default func <main> : H",
        "loadavg_before": load_before,
        "loadavg_after": loadavg(),
    }
    out = Path(args.out) if args.out else ROOT / "bench" / "results" / f"{time.strftime('%Y-%m-%d')}-{environment['commit']}-secrets-{args.size}.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"environment": environment, "measurements": rows}, indent=2) + "\n")
    print(f"\nload average before {load_before}, after {environment['loadavg_after']}\nwrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
