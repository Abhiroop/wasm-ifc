#!/usr/bin/env python3
"""Time every benchmark workload on every available runtime.

Two tiers of workload:

* t1 (default): the micro-kernels in bench/wasm/. Each exports a zero-argument `run` that
  returns an i32 checksum, so every runtime invokes them the same way and the checksums
  cross-validate; agreement is recorded in bench/checksums.txt.
* t2: the real programs in bench/wasm-t2/ (bench/c/build.sh). Each is a WASI command run
  through `_start`. Its checksum is its exit code and a hash of the output lines that carry
  results (CoreMark's CRCs); `--verify` compares the arrays PolyBench's `-dump` builds print.

Repetitions are taken round-robin across the runtimes of a workload (A B C A B C ...), not
one runtime at a time: this laptop CPU runs a short burst at higher clocks than a sustained
load, so an A/B taken in sequence compares thermal states as much as code. `--binary` adds
another build of our interpreter under a name of its own, for exactly that kind of A/B.

`--ticky PATH` names a build of ours with GHC's ticky-ticky counters (bench/README.md). Each
workload runs on it once, and the number of times the machine's `step` was entered is recorded
as its step count: one small-step transition per instruction, block entry and exit, or call.
The count belongs to the program and its input, not to a runtime, so dividing any runtime's
time by it gives comparable nanoseconds per step.

  ./bench/run.py                                   # t1, everything available
  ./bench/run.py -r wasm-ifc -w fib                # one runtime, one workload
  ./bench/run.py --tier t2 --ticky "$(cabal list-bin exe:wasm-ifc --builddir=/tmp/ticky)"
  ./bench/run.py --tier t2 --verify
  ./bench/run.py --binary before=/path/to/old/wasm-ifc -r wasm-ifc -r before -r wabt-interp
"""

from __future__ import annotations

import argparse, fnmatch, hashlib, json, os, platform, re, resource, shutil, subprocess, sys, tempfile, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# Where bench/tools/fetch.sh installs the runtimes that are not on PATH.
BENCH_TOOLS = Path(os.environ.get("WASM_BENCH_TOOLS", Path.home() / ".local" / "wasm-bench-tools"))
TIERS = {"t1": ROOT / "bench" / "wasm", "t2": ROOT / "bench" / "wasm-t2"}
# Pinning is opt-in (BENCH_CPU=2): on this hybrid CPU under WSL2 it measurably *slows* runs
# and does not reduce the spread, so the default is to let the scheduler place them.
_CPU = os.environ.get("BENCH_CPU")
PIN = ["taskset", "-c", _CPU] if _CPU and shutil.which("taskset") else []
# Builds of our interpreter. Every other runtime is foreign, and only agreement with a foreign
# runtime makes a recorded checksum authoritative.
OURS_LIKE: set[str] = {"wasm-ifc"}
MODULE = "{module}"
TICKY_STEP = re.compile(r"^\s*(\d+)\s.*Runtime\.Interpreter\.\$?w?step\{")


def runtimes(extra: list[str]) -> dict[str, dict[str, list[str]]]:
    """name -> {tier: argv}, `{module}` marking where the module goes."""
    found: dict[str, dict[str, list[str]]] = {}

    def ours(path: str) -> dict[str, list[str]]:
        return {"t1": [path, "invoke", MODULE, "run"], "t2": [path, "run", MODULE]}

    built = subprocess.run(["cabal", "list-bin", "wasm-ifc"], cwd=ROOT, capture_output=True, text=True)
    if built.returncode == 0:
        found["wasm-ifc"] = ours(built.stdout.strip())
    for spec in extra:
        name, _, path = spec.partition("=")
        if not name or not path:
            raise SystemExit(f"--binary wants NAME=PATH, got {spec!r}")
        found[name] = ours(path)
        OURS_LIKE.add(name)

    def tool(name: str) -> str | None:
        return shutil.which(str(BENCH_TOOLS / "bin" / name)) or shutil.which(name)

    wt = tool("wasmtime") or shutil.which(str(Path.home() / ".wasmtime" / "bin" / "wasmtime"))
    if wt:
        for tier, flags in [("cranelift", []), ("winch", ["-C", "compiler=winch"]), ("pulley", ["--target", "pulley64"])]:
            found[f"wasmtime-{tier}"] = {"t1": [wt, "run", *flags, "--invoke", "run", MODULE], "t2": [wt, "run", *flags, MODULE]}
    if tool("wasm-interp"):
        found["wabt-interp"] = {"t1": [tool("wasm-interp"), "--run-all-exports", MODULE], "t2": [tool("wasm-interp"), "--wasi", MODULE]}
    if tool("wasm3"):
        found["wasm3"] = {"t1": [tool("wasm3"), "--func", "run", MODULE], "t2": [tool("wasm3"), MODULE]}
    if tool("iwasm"):
        # WAMR's release binary also carries JIT tiers; --interp pins the interpreter.
        found["wamr-interp"] = {"t1": [tool("iwasm"), "--interp", "-f", "run", MODULE], "t2": [tool("iwasm"), "--interp", MODULE]}
    if tool("wasmi"):
        found["wasmi"] = {"t1": [tool("wasmi"), "run", "--invoke", "run", MODULE], "t2": [tool("wasmi"), "run", MODULE]}
    return found


def argv_for(template: list[str], module: Path) -> list[str]:
    return PIN + [str(module) if part == MODULE else part for part in template]


def i32_checksum(out: str) -> str:
    """The i32 a kernel returned, as an unsigned decimal.

    Each runtime prints it its own way (`i32:-1`, `Result: -1`, a bare `4294967295`, WAMR's
    hexadecimal `0xffffffff:i32`), and some print it signed, so the comparable form is the
    last integer read, modulo 2^32.
    """
    hexadecimal = re.search(r"0x([0-9a-fA-F]+):i32", out)
    if hexadecimal:
        return str(int(hexadecimal.group(1), 16) % 2**32)
    digits = "".join(c if (c.isdigit() or c == "-") else " " for c in out).split()
    return str(int(digits[-1]) % 2**32) if digits else out


def program_checksum(out: str, code: int) -> str:
    """A WASI program's answer: its exit code and the lines that carry its results.

    Only CoreMark's CRC lines count. Everything else it prints depends on how fast the runtime
    was (the ticks, the iterations per second, and whether the run passed the ten seconds
    CoreMark wants for a valid score), and PolyBench's timing builds print nothing at all.
    """
    results = "\n".join(line for line in out.splitlines() if "crc" in line.lower())
    return f"exit {code}, results {hashlib.sha1(results.encode()).hexdigest()[:12]}"


def once(argv: list[str], timeout: float, tier: str) -> tuple[float, float, str, int]:
    """Run once; return wall seconds, child CPU seconds, the answer, exit code."""
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.perf_counter()
    try:
        done = subprocess.run(argv, capture_output=True, encoding="utf-8", errors="replace", timeout=timeout)
        # A kernel's result may come on stderr (wasm3 prints it there); a program's output is stdout.
        code, out = done.returncode, done.stdout if tier == "t2" or done.stdout.strip() else done.stderr
    except subprocess.TimeoutExpired:
        code, out = -1, ""
    wall = time.perf_counter() - start
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime)
    answer = i32_checksum(out.strip()) if tier == "t1" else program_checksum(out, code)
    return wall, cpu, answer, code


def count_steps(ticky: str, tier: str, module: Path, timeout: float) -> int | None:
    """Run a module once on the ticky build and read how often `step` was entered."""
    with tempfile.TemporaryDirectory() as scratch:
        report = Path(scratch) / "steps.ticky"
        template = {"t1": [ticky, "invoke", MODULE, "run"], "t2": [ticky, "run", MODULE]}[tier]
        subprocess.run(argv_for(template, module) + ["+RTS", f"-r{report}", "-RTS"], capture_output=True, timeout=timeout)
        if not report.exists():
            return None
        for line in report.read_text(errors="replace").splitlines():
            match = TICKY_STEP.match(line)
            if match:
                return int(match.group(1))
    return None


def median(xs: list[float]) -> float:
    s = sorted(xs)
    mid = len(s) // 2
    return s[mid] if len(s) % 2 else (s[mid - 1] + s[mid]) / 2


def mad(xs: list[float]) -> float:
    m = median(xs)
    return median([abs(x - m) for x in xs])


def environment(rts: dict[str, dict[str, list[str]]], tier: str) -> dict:
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
        "tier": tier,
        "cpu": line("/proc/cpuinfo", "model name"),
        "kernel": platform.release(),
        "pinned_to": PIN[-1] if PIN else None,
        "ghc": version(["ghc", "--version"]),
        "versions": {n: version([t["t1"][0], "--version"]) for n, t in rts.items() if n not in OURS_LIKE},
        "binaries": {n: t["t1"][0] for n, t in rts.items() if n in OURS_LIKE},
    }


def dumped_arrays(text: str) -> str:
    """What a PolyBench `-dump` build printed between its dump markers, and nothing else."""
    begin, end = text.find("==BEGIN DUMP_ARRAYS=="), text.find("==END   DUMP_ARRAYS==")
    return text[begin:end] if 0 <= begin < end else ""


def verify(rts: dict[str, dict[str, list[str]]], modules: list[Path], timeout: float) -> int:
    """Run each PolyBench `-dump` build once on each runtime and compare the arrays."""
    split = 0
    for module in modules:
        answers: dict[str, str] = {}
        for name, templates in rts.items():
            try:
                done = subprocess.run(argv_for(templates["t2"], module), capture_output=True, encoding="utf-8", errors="replace", timeout=timeout)
            except subprocess.TimeoutExpired:
                continue
            arrays = dumped_arrays(done.stderr + done.stdout)
            if done.returncode == 0 and arrays:
                answers[name] = hashlib.sha1(arrays.encode()).hexdigest()[:12]
        distinct = set(answers.values())
        foreign = any(n not in OURS_LIKE for n in answers)
        verdict = "agree" if len(distinct) == 1 and foreign and "wasm-ifc" in answers else "DISAGREE" if len(distinct) > 1 else "incomplete"
        split += verdict == "DISAGREE"
        print(f"{module.stem:28s} {verdict:10s} {len(answers)} runtimes  " + ("" if verdict == "agree" else str(answers)), flush=True)
    return 1 if split else 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("-r", "--runtime", action="append", help="restrict to these runtimes")
    ap.add_argument("-w", "--workload", action="append", help="restrict to these workloads (glob patterns: 'pb-*-small')")
    ap.add_argument("--tier", choices=sorted(TIERS), default="t1")
    ap.add_argument("--reps", type=int, default=7, help="timed repetitions (plus one warm-up)")
    ap.add_argument("--timeout", type=float, default=600.0)
    ap.add_argument("-o", "--out", help="results file (default bench/results/<date>-<commit>[-t2].json)")
    ap.add_argument("--binary", action="append", default=[], metavar="NAME=PATH", help="another build of our interpreter to time")
    ap.add_argument("--ticky", metavar="PATH", help="a ticky-instrumented build of ours: record each workload's step count")
    ap.add_argument("--verify", action="store_true", help="t2 only: compare PolyBench's dumped arrays across runtimes, then stop")
    args = ap.parse_args()

    rts = {n: t for n, t in runtimes(args.binary).items() if not args.runtime or n in args.runtime}
    if not rts:
        print("no runtimes found", file=sys.stderr)
        return 2
    wanted = lambda m: not args.workload or any(fnmatch.fnmatch(m.stem, pattern) for pattern in args.workload)
    if args.verify:
        return verify(rts, [m for m in sorted(TIERS["t2"].glob("*-dump.wasm")) if wanted(m)], args.timeout)
    mods = [m for m in sorted(TIERS[args.tier].glob("*.wasm")) if not m.stem.endswith("-dump") and wanted(m)]
    if not mods:
        print(f"no workloads in {TIERS[args.tier]}", file=sys.stderr)
        return 2

    rows = []
    for module in mods:
        steps = count_steps(args.ticky, args.tier, module, args.timeout) if args.ticky else None
        # One warm-up each, which also finds out who can run this workload at all.
        live: dict[str, tuple[list[str], str]] = {}
        for name, templates in rts.items():
            argv = argv_for(templates[args.tier], module)
            _, _, warm, code = once(argv, args.timeout, args.tier)
            if code == 0:
                live[name] = (argv, warm)
            else:
                print(f"{module.stem:22s} {name:20s} unavailable (exit {code})", flush=True)
                rows.append({"workload": module.stem, "runtime": name, "ok": False})
        walls: dict[str, list[float]] = {n: [] for n in live}
        cpus: dict[str, list[float]] = {n: [] for n in live}
        broken: set[str] = set()
        for _ in range(args.reps):
            for name, (argv, warm) in live.items():
                if name in broken:
                    continue
                wall, cpu, out, code = once(argv, args.timeout, args.tier)
                if code != 0 or out != warm:
                    broken.add(name)
                    continue
                walls[name].append(wall)
                cpus[name].append(cpu)
        for name, (_, warm) in live.items():
            if name in broken:
                print(f"{module.stem:22s} {name:20s} inconsistent", flush=True)
                rows.append({"workload": module.stem, "runtime": name, "ok": False})
                continue
            row = {
                "workload": module.stem,
                "runtime": name,
                "ok": True,
                "checksum": warm,
                "wall_s": median(walls[name]),
                "wall_mad_s": mad(walls[name]),
                "cpu_s": median(cpus[name]),
                "reps": args.reps,
            }
            if steps:
                row["steps"] = steps
            rows.append(row)
            print(f"{module.stem:22s} {name:20s} {row['cpu_s']:8.4f}s cpu  {row['wall_s']:8.4f}s wall  -> {warm}", flush=True)

    env = environment(rts, args.tier)
    suffix = "" if args.tier == "t1" else f"-{args.tier}"
    out = Path(args.out) if args.out else ROOT / "bench" / "results" / f"{time.strftime('%Y-%m-%d')}-{env['commit']}{suffix}.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"environment": env, "measurements": rows}, indent=2) + "\n")
    print(f"\nwrote {out}")
    return record_checksums(rows, write=args.tier == "t1")


def record_checksums(rows: list[dict], write: bool) -> int:
    """Cross-validate the workloads, and (for t1) write down what the runtimes agreed on.

    A kernel's checksum has no independent oracle the way `samples/check.sh`'s expected values
    do, so its authority is agreement with an independent implementation: a kernel is recorded
    only when every runtime that ran it returned the same value and at least one of them is not
    a build of ours. The file is merged, never rewritten from a partial run, so timing a few
    kernels cannot drop the others. Workloads the runtimes disagree on are reported and left out.
    """
    seen: dict[str, set[str]] = {}
    foreign: set[str] = set()
    for row in rows:
        if row.get("ok"):
            seen.setdefault(row["workload"], set()).add(row["checksum"])
            if row["runtime"] not in OURS_LIKE:
                foreign.add(row["workload"])
    split = [w for w, sums in sorted(seen.items()) if len(sums) > 1]
    for workload in split:
        print(f"CHECKSUM MISMATCH {workload}: {sorted(seen[workload])}", flush=True)
    if not write:
        return 1 if split else 0
    agreed = {w: next(iter(sums)) for w, sums in seen.items() if len(sums) == 1 and w in foreign}
    path = ROOT / "bench" / "checksums.txt"
    recorded: dict[str, str] = {}
    if path.exists():
        for line in path.read_text().splitlines():
            if line and not line.startswith("#"):
                name, value = line.split()
                recorded[name] = value
    changed = {w: c for w, c in agreed.items() if recorded.get(w) != c}
    if changed:
        recorded.update(changed)
        path.write_text(
            "# The i32 every runtime returns from each kernel's `run`, as an unsigned decimal.\n"
            "# Written by bench/run.py when the runtimes agree; checked by bench/smoke.sh.\n"
            + "".join(f"{w} {c}\n" for w, c in sorted(recorded.items()))
        )
        print(f"updated {path.name}: {', '.join(sorted(changed))}")
    return 1 if split else 0


if __name__ == "__main__":
    sys.exit(main())
