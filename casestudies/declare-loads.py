#!/usr/bin/env python3
"""Complete a policy the way a user reading the traps would: run the program, and while it traps
on a load that reads a secret byte, declare that load secret (the declaration the trap names) and
run again. Stops when the program runs to the end, is rejected statically, or traps otherwise.

    casestudies/declare-loads.py BASE.policy PROGRAM.wasm [--dir HOST::GUEST]... [--limit N]

Prints one JSON object: the outcome, the declarations added, the final policy, the static error
if any, and what inference raised (from `wasm-ifc explain`). The declarations it adds are an
upper bound on what a user must write: a person might declare a function's default instead.
"""
import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def binary():
    out = subprocess.run(["cabal", "list-bin", "exe:wasm-ifc"], cwd=ROOT, capture_output=True, text=True, check=True)
    return out.stdout.strip()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("policy")
    parser.add_argument("program")
    parser.add_argument("--dir", action="append", default=[], help="HOST::GUEST, copied fresh for every run")
    parser.add_argument("--limit", type=int, default=200)
    parser.add_argument("args", nargs="*")
    options = parser.parse_args()

    wasm_ifc = binary()
    base = Path(options.policy).read_text()
    declarations = []
    runs = 0
    outcome, detail, stdout = None, None, None
    with tempfile.TemporaryDirectory() as scratch:
        while runs < options.limit:
            runs += 1
            policy = Path(scratch) / "policy"
            policy.write_text(base + "".join(line + "\n" for line in declarations))
            dirs = []
            for i, spec in enumerate(options.dir):
                host, guest = spec.split("::")
                copy = Path(scratch) / f"dir{i}-{runs}"
                shutil.copytree(host, copy)
                dirs += ["--dir", f"{copy}::{guest}"]
            run = subprocess.run([wasm_ifc, "run", "--policy", str(policy), *dirs, options.program, *options.args], capture_output=True, text=True)
            error = run.stderr.strip()
            trap = re.search(r"declare it with `(load \d+ \d+) : H`", error)
            if trap:
                declarations.append(trap.group(1) + " : H")
                continue
            if error.startswith("Validation error"):
                outcome, detail = "rejected", error
            elif error.startswith("trap"):
                outcome, detail = "trapped", error
            else:
                outcome, detail = "ran", f"exit {run.returncode}"
            stdout = run.stdout
            break
        else:
            outcome, detail = "gave up", f"{options.limit} runs"
        explained = subprocess.run([wasm_ifc, "explain", "--policy", str(policy), options.program], capture_output=True, text=True).stdout
    json.dump(
        {
            "program": options.program,
            "outcome": outcome,
            "detail": detail,
            "runs": runs,
            "declarations_added": declarations,
            "policy": base + "".join(line + "\n" for line in declarations),
            "stdout": stdout,
            "explain": explained.splitlines(),
        },
        sys.stdout,
        indent=2,
    )
    print()


if __name__ == "__main__":
    main()
