#!/usr/bin/env python3
"""Time every benchmark workload on every available runtime.

Each workload is a self-contained module exporting a zero-argument @run@ returning an i32
checksum, so every runtime is invoked the same way and the checksums cross-validate.
Results (with the environment that produced them) go to bench/results/<stamp>.json.

  ./bench/run.py                      # everything available
  ./bench/run.py -r wasm-ifc -w fib   # one runtime, one workload
  ./bench/run.py --reps 11
"""

from __future__ import annotations

import argparse, json, os, platform, resource, shutil, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WASM = ROOT / "bench" / "wasm"
# Pinning is opt-in (BENCH_CPU=2): on this hybrid CPU under WSL2 it measurably *slows* runs
# and does not reduce the spread, so the default is to let the scheduler place them.
_CPU = os.environ.get("BENCH_CPU")
PIN = ["taskset", "-c", _CPU] if _CPU and shutil.which("taskset") else []


def wasmtime() -> str | None:
    return shutil.which("wasmtime") or shutil.which(str(Path.home() / ".wasmtime/bin/wasmtime"))


def runtimes() -> dict[str, list[str]]:
    """name -> argv prefix; the module path is appended, then the invocation arguments."""
    found: dict[str, list[str]] = {}
    ours = subprocess.run(["cabal", "list-bin", "wasm-ifc"], cwd=ROOT, capture_output=True, text=True)
    if ours.returncode == 0:
        found["wasm-ifc"] = [ours.stdout.strip(), "invoke"]
    wt = wasmtime()
    if wt:
        found["wasmtime-cranelift"] = [wt, "run", "--invoke", "run"]
        found["wasmtime-winch"] = [wt, "run", "-C", "compiler=winch", "--invoke", "run"]
        found["wasmtime-pulley"] = [wt, "run", "--target", "pulley64", "--invoke", "run"]
    wi = shutil.which("wasm-interp")
    if wi:
        found["wabt-interp"] = [wi, "--run-all-exports"]
    w3 = shutil.which("wasm3")
    if w3:
        found["wasm3"] = [w3, "--func", "run"]
    return found


def argv_for(name: str, prefix: list[str], module: Path) -> list[str]:
    # Only ours takes the export name after the file; the others carry it in their flags.
    return PIN + prefix + ([str(module), "run"] if name == "wasm-ifc" else [str(module)])


def checksum(out: str) -> str:
    """The i32 the kernel returned, as an unsigned decimal.

    Each runtime prints it its own way (`i32:-1`, `Result: -1`, a bare `4294967295`), and
    some print it signed, so the comparable form is the last integer read modulo 2^32.
    """
    digits = "".join(c if (c.isdigit() or c == "-") else " " for c in out).split()
    return str(int(digits[-1]) % 2**32) if digits else out


def once(argv: list[str], timeout: float) -> tuple[float, float, str, int]:
    """Run once; return wall seconds, child CPU seconds, stdout, exit code."""
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.perf_counter()
    try:
        done = subprocess.run(argv, capture_output=True, text=True, timeout=timeout)
        code, out = done.returncode, checksum(done.stdout.strip())
    except subprocess.TimeoutExpired:
        code, out = -1, ""
    wall = time.perf_counter() - start
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime)
    return wall, cpu, out, code


def median(xs: list[float]) -> float:
    s = sorted(xs)
    mid = len(s) // 2
    return s[mid] if len(s) % 2 else (s[mid - 1] + s[mid]) / 2


def mad(xs: list[float]) -> float:
    m = median(xs)
    return median([abs(x - m) for x in xs])


def environment(rts: dict[str, list[str]]) -> dict:
    def line(path: str, key: str) -> str:
        try:
            for row in open(path):
                if row.startswith(key):
                    return row.split(":", 1)[1].strip()
        except OSError:
            pass
        return "?"

    def version(argv: list[str]) -> str:
        try:
            return subprocess.run(argv, capture_output=True, text=True, timeout=20).stdout.strip().splitlines()[0]
        except Exception:
            return "?"

    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, capture_output=True, text=True)
    # Only the interpreter's own source decides whether a measurement is of a known revision;
    # uncommitted benchmark scripts and result files do not change what was measured.
    measured = ["src", "app", "test", "wasm-ifc.cabal", "cabal.project"]
    dirty = subprocess.run(["git", "status", "--porcelain", "--", *measured], cwd=ROOT, capture_output=True, text=True)
    return {
        "date": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "commit": commit.stdout.strip() + ("-dirty" if dirty.stdout.strip() else ""),
        "cpu": line("/proc/cpuinfo", "model name"),
        "kernel": platform.release(),
        "pinned_to": PIN[-1] if PIN else None,
        "ghc": version(["ghc", "--version"]),
        "versions": {n: version([p[0], "--version"]) for n, p in rts.items() if n != "wasm-ifc"},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("-r", "--runtime", action="append", help="restrict to these runtimes")
    ap.add_argument("-w", "--workload", action="append", help="restrict to these workloads")
    ap.add_argument("--reps", type=int, default=7, help="timed repetitions (plus one warm-up)")
    ap.add_argument("--timeout", type=float, default=120.0)
    ap.add_argument("-o", "--out", help="results file (default bench/results/<stamp>.json)")
    args = ap.parse_args()

    rts = {n: p for n, p in runtimes().items() if not args.runtime or n in args.runtime}
    if not rts:
        print("no runtimes found", file=sys.stderr)
        return 2
    mods = sorted(WASM.glob("*.wasm"))
    if args.workload:
        mods = [m for m in mods if m.stem in args.workload]
    if not mods:
        print(f"no workloads in {WASM} (run bench/build.sh)", file=sys.stderr)
        return 2

    rows = []
    for module in mods:
        for name, prefix in rts.items():
            argv = argv_for(name, prefix, module)
            _, _, warm, code = once(argv, args.timeout)
            if code != 0:
                print(f"{module.stem:18s} {name:20s} unavailable (exit {code})", flush=True)
                rows.append({"workload": module.stem, "runtime": name, "ok": False})
                continue
            walls, cpus = [], []
            for _ in range(args.reps):
                wall, cpu, out, code = once(argv, args.timeout)
                if code != 0 or out != warm:
                    break
                walls.append(wall)
                cpus.append(cpu)
            if len(walls) < args.reps:
                print(f"{module.stem:18s} {name:20s} inconsistent", flush=True)
                rows.append({"workload": module.stem, "runtime": name, "ok": False})
                continue
            row = {
                "workload": module.stem,
                "runtime": name,
                "ok": True,
                "checksum": warm,
                "wall_s": median(walls),
                "wall_mad_s": mad(walls),
                "cpu_s": median(cpus),
                "reps": args.reps,
            }
            rows.append(row)
            print(f"{module.stem:18s} {name:20s} {row['cpu_s']:8.4f}s cpu  {row['wall_s']:8.4f}s wall  -> {warm}", flush=True)

    env = environment(rts)
    out = Path(args.out) if args.out else ROOT / "bench" / "results" / f"{time.strftime('%Y-%m-%d')}-{env['commit']}.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"environment": env, "measurements": rows}, indent=2) + "\n")
    print(f"\nwrote {out}")

    return record_checksums(rows)


def record_checksums(rows: list[dict]) -> int:
    """Cross-validate the kernels, and write down what the runtimes agreed on.

    A kernel's checksum has no independent oracle the way `samples/check.sh`'s expected values
    do, so its authority is agreement: bench/checksums.txt holds the value every runtime that
    ran the kernel produced, and bench/smoke.sh holds us to it afterwards. Kernels the runtimes
    disagree on are reported and deliberately left out of the file.
    """
    seen: dict[str, set[str]] = {}
    for row in rows:
        if row.get("ok"):
            seen.setdefault(row["workload"], set()).add(row["checksum"])
    agreed = {w: next(iter(sums)) for w, sums in sorted(seen.items()) if len(sums) == 1}
    split = [w for w, sums in sorted(seen.items()) if len(sums) > 1]
    for workload in split:
        print(f"CHECKSUM MISMATCH {workload}: {sorted(seen[workload])}", flush=True)
    path = ROOT / "bench" / "checksums.txt"
    if agreed and not split:
        path.write_text(
            "# The i32 every runtime returns from each kernel's `run`, as an unsigned decimal.\n"
            "# Written by bench/run.py when the runtimes agree; checked by bench/smoke.sh.\n"
            + "".join(f"{w} {c}\n" for w, c in sorted(agreed.items()))
        )
        print(f"wrote {path.name} ({len(agreed)} kernels)")
    return 1 if split else 0


if __name__ == "__main__":
    sys.exit(main())
