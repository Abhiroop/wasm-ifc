#!/usr/bin/env python3
"""Run the case studies with secrets and record, per program, what the paper's RQ4 asks for:
the policy lines written, the labels inference raised, the static rejection (rule and site) or
the trap (and the load's site), whether SecWasm's restrictions would also accept the program
(if not, the program has one of the lift shapes the lift-free rules accept), the output, and
the running time. The results go to casestudies/results/<date>-<commit>.json.

    ./casestudies/password/build.sh      # and the other studies' build scripts
    ./casestudies/run.py [STUDY...]      # all studies, or those named

A study is a list of programs, each with its policy, the directories it is given (created
fresh for every run, with the files listed), its arguments, and the outcome expected.
"""
import datetime
import json
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "casestudies"
BUILD = HERE / "build"

PASSWORD_DIRS = [
    {"guest": "/secrets", "files": {"password": "letmein\n"}},
    {"guest": "/log", "files": {}},
]

def secwasm_study():
    """SecWasm's examples and the counterexamples to its printed rules (casestudies/secwasm/)."""
    programs = []
    for line in (HERE / "secwasm" / "expected.txt").read_text().splitlines():
        name, expect, *args = line.split()
        programs.append({"name": name, "wasm": f"secwasm/{name}.wasm", "policy": f"secwasm/{name}.policy", "invoke": "f", "args": args, "expect": expect})
    return programs


WASI_C = ROOT / "test/wasi/testsuite/tests/c/testsuite/wasm32-wasip1"


def wasi_c_study():
    """The C programs of the wasi-testsuite, their files secret: once with a secret standard
    output (can the rules type them?), once with a public one (their output may depend on the
    files, so they must be rejected or trap unless it does not)."""
    programs = []
    for wasm in sorted(WASI_C.glob("*.wasm")):
        config_path = wasm.with_suffix(".json")
        config = json.loads(config_path.read_text()) if config_path.exists() else {}
        dirs = [{"guest": "/", "copy": str(WASI_C / config["root"])}] if "root" in config else []
        for stdout in ("H", "L"):
            programs.append({
                "name": f"{wasm.stem} (stdout {stdout})", "wasm": str(wasm), "dirs": dirs, "args": config.get("args", []),
                "policy_text": f"preopen / : H\nstdout : {stdout}\nstderr : {stdout}\n", "declare": True,
            })
    return programs


def polybench_study():
    """Ten PolyBench/C kernels at the MINI size, their data secret where main writes it, and the
    arrays they print secret: can the rules type computation over secret data in memory?"""
    kernels = ["2mm", "3mm", "atax", "gemm", "jacobi-2d", "seidel-2d", "floyd-warshall", "nussinov", "correlation", "lu"]
    policy = "stdout : H\nstderr : H\nstore-default func {main} : H\nload-default func {main} : H\nload-default func {print_array} : H\n"
    silent = "store-default func {main} : H\nload-default func {main} : H\n"
    return [{"name": k, "wasm": f"polybench/{k}.wasm", "policy_text": policy, "declare": True} for k in kernels] + [
        {"name": f"{k} (printing compiled out)", "wasm": f"polybench/{k}-silent.wasm", "policy_text": silent, "declare": True} for k in kernels
    ]


STUDIES = {
    "password": [
        # Under checker.policy the three branch-free variants trap in read(), on the byte count
        # that fd_read stored: the count of a read from a secret file is secret.
        {"name": "password", "wasm": "password/password.wasm", "policy": "password/checker.policy", "dirs": PASSWORD_DIRS, "expect": "trapped"},
        {"name": "password-leak-control", "wasm": "password/password-leak-control.wasm", "policy": "password/checker.policy", "dirs": PASSWORD_DIRS, "expect": "trapped"},
        {"name": "password-leak-memory", "wasm": "password/password-leak-memory.wasm", "policy": "password/checker.policy", "dirs": PASSWORD_DIRS, "expect": "trapped"},
        # With that load declared, the error check on the count raises the pc of the rest of main.
        {"name": "password (count declared)", "wasm": "password/password.wasm", "policy": "password/checker-count-declared.policy", "dirs": PASSWORD_DIRS, "expect": "rejected"},
        {"name": "password-naive", "wasm": "password/password-naive.wasm", "policy": "password/checker.policy", "dirs": PASSWORD_DIRS, "expect": "rejected"},
    ],
    "secwasm": secwasm_study(),
    "wasi-c": wasi_c_study(),
    "polybench": polybench_study(),
}


def run(command, **kwargs):
    return subprocess.run(command, capture_output=True, text=True, **kwargs)


def binary():
    return run(["cabal", "list-bin", "exe:wasm-ifc"], cwd=ROOT, check=True).stdout.strip()


def explain(wasm_ifc, policy, wasm, restricted=False):
    command = [wasm_ifc, "explain", "--policy", str(policy)] + (["--secwasm-restrictions"] if restricted else []) + [str(wasm)]
    lines = run(command).stdout.splitlines()
    return {
        "verdict": lines[0] if lines else "",
        "attempts": next((int(l.split(": ")[1]) for l in lines if l.startswith("attempts: ")), None),
        "secret_locals": sum(1 for l in lines if l.startswith("secret local: ")),
        "raised_functions": [l[len("raised function "):] for l in lines if l.startswith("raised function ")],
    }


def site_of(error):
    placed = re.search(r"InFunction (\d+) \(AtInstruction (\d+) \((\w+)(.*)\)\)", error)
    if placed:
        return {"function": int(placed.group(1)), "instruction": int(placed.group(2)), "rule": placed.group(3) + placed.group(4)}
    load = re.search(r"`load (\d+) (\d+) : H`", error)
    if load:
        return {"function": int(load.group(1)), "load": int(load.group(2))}
    return None


def function_indices(wasm):
    """The function names of the module's name section, with their indices (wabt's wasm-objdump)."""
    listing = run(["wasm-objdump", "-x", str(wasm)]).stdout
    return {m.group(2): int(m.group(1)) for m in re.finditer(r"^ - func\[(\d+)\] sig=\d+ <([^>]+)>", listing, re.M)}


def attempt(wasm_ifc, program, wasm, policy, scratch):
    """One run in fresh directories: the result, the time, and the files the run created."""
    run_dir = Path(tempfile.mkdtemp(dir=scratch))
    dirs = []
    for i, d in enumerate(program.get("dirs", [])):
        host = run_dir / f"dir{i}"
        if "copy" in d:
            shutil.copytree(d["copy"], host)
        else:
            host.mkdir()
            for name, content in d["files"].items():
                (host / name).write_text(content)
        dirs += ["--dir", f"{host}::{d['guest']}"]
    started = time.monotonic()
    if "invoke" in program:
        command = [wasm_ifc, "invoke", "--policy", str(policy), str(wasm), program["invoke"], *program.get("args", [])]
    else:
        command = [wasm_ifc, "run", "--policy", str(policy), *dirs, str(wasm), *program.get("args", [])]
    result = run(command)
    elapsed = time.monotonic() - started
    written = {}
    for i, d in enumerate(program.get("dirs", [])):
        if "files" in d:
            for f in sorted((run_dir / f"dir{i}").iterdir()):
                if f.name not in d["files"]:
                    written[f"{d['guest']}/{f.name}"] = f.read_text(errors="replace")
    return result, elapsed, written


def evaluate(wasm_ifc, program):
    wasm = Path(program["wasm"]) if Path(program["wasm"]).is_absolute() else BUILD / program["wasm"]
    declared = []
    with tempfile.TemporaryDirectory() as scratch:
        if "policy_text" in program:
            policy = Path(scratch) / "policy"
            base = program["policy_text"]
            if "{" in base:
                base = base.format(**function_indices(wasm))
        else:
            policy = HERE / program["policy"]
            base = policy.read_text()
        # With "declare", every load that traps on a secret byte is declared secret, as a user
        # reading the traps would do, until the program runs through or fails otherwise.
        while True:
            if "policy_text" in program:
                policy.write_text(base + "".join(line + "\n" for line in declared))
            result, elapsed, written = attempt(wasm_ifc, program, wasm, policy, scratch)
            trap = re.search(r"declare it with `(load \d+ \d+) : H`", result.stderr)
            if program.get("declare") and trap and len(declared) < 500:
                declared.append(trap.group(1) + " : H")
                continue
            break
        final_policy = policy.read_text()
        lift_free = explain(wasm_ifc, policy, wasm)
        restricted = explain(wasm_ifc, policy, wasm, restricted=True)
    error = result.stderr.strip()
    if error.startswith("Validation error") or error.startswith("Policy error"):
        outcome = "rejected"
    elif error.startswith("trap"):
        outcome = "trapped"
    else:
        outcome = "ran"
    return {
        "name": program["name"],
        "wasm": str(wasm.relative_to(ROOT)) if wasm.is_relative_to(ROOT) else str(wasm),
        "policy": program.get("policy") or final_policy,
        "policy_lines": sum(1 for line in base.splitlines() if line.split(";", 1)[0].strip()),
        "loads_declared_from_traps": len(declared),
        "outcome": outcome,
        "expected": program.get("expect"),
        "as_expected": program.get("expect") in (None, outcome),
        "exit_code": result.returncode,
        "error": error or None,
        "site": site_of(error) if error else None,
        "stdout": result.stdout,
        "files_written": written,
        "inference": lift_free,
        "secwasm_restrictions": restricted["verdict"],
        "lift_shape": lift_free["verdict"] == "accepted" and restricted["verdict"] != "accepted",
        "seconds": round(elapsed, 3),
    }


def main():
    names = sys.argv[1:] or list(STUDIES)
    wasm_ifc = binary()
    commit = run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT).stdout.strip()
    dirty = bool(run(["git", "status", "--porcelain", "--", "src", "app"], cwd=ROOT).stdout.strip())
    results = {
        "commit": commit + ("-dirty" if dirty else ""),
        "date": datetime.date.today().isoformat(),
        "studies": {name: [evaluate(wasm_ifc, program) for program in STUDIES[name]] for name in names},
    }
    out = HERE / "results" / f"{results['date']}-{results['commit']}.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(results, indent=2) + "\n")
    for name, programs in results["studies"].items():
        for p in programs:
            mark = "ok  " if p["as_expected"] else "DIFF"
            print(f"{mark} {name}/{p['name']}: {p['outcome']} (expected {p['expected']}), {p['policy_lines']} policy lines, "
                  f"{p['inference']['secret_locals']} secret locals, {len(p['inference']['raised_functions'])} raised functions, "
                  f"restricted: {p['secwasm_restrictions']}, {p['seconds']} s")
    print(f"wrote {out.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
