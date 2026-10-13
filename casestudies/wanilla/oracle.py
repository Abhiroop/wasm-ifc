#!/usr/bin/env python3
"""WANILLA's labelled modules as an oracle (Scherer et al., CCS 2025; artifact
https://researchdata.tuwien.ac.at/records/hc4rp-xp328, AGPL, not copied into this repository).

Every test specification of the artifact's noninterference suite gives a module, the function
called, the labels of its inputs and outputs, and whether a leak exists (SAT, interferent) or
not (UNSAT, noninterferent). We translate each specification whose attacker we can express into
a policy, validate the module under it, and compare:

  SAT   and rejected  -> caught statically
  SAT   and accepted  -> missed: a leak our rules should have rejected (or a spec we mistranslate)
  UNSAT and accepted  -> precise
  UNSAT and rejected  -> a precision loss of SecWasm's rules against WANILLA's analysis

WANILLA's lattice has an integrity dimension; we keep confidentiality (ST, SU -> H; PT, PU -> L).
A specification is not expressible, and reported as such, when it queries integrity only,
labels a global differently on entry and on exit, gives an imported function a secret
parameter, result or context (a host import must be public here) or lets it write the module's
state, or asks about areas of the memory or about a table.

Two kinds of query are translated since 2026-10-13 (the verdicts without them are recorded
too, as `verdict_narrow`, which is the translation of the results before that date):

  * What flows into an imported function whose parameters, results and context are public.
    That is our default for an import: a secret argument or a call under a secret pc is
    rejected.
  * The data of the memory, when the attacker observes it at the end (`memory_data`, `memory`
    with public data on exit). Our attacker observes the bytes labelled public, so the policy
    declares every store of the module public (`store-default func i : L`): a store of a
    secret is then rejected, every byte stays public, and the two attackers observe the same.

    casestudies/wanilla/oracle.py [ARTIFACT_DIR]   # default ~/.local/wasm-bench-tools/src/wanilla
"""
import collections
import datetime
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEFAULT = Path.home() / ".local/wasm-bench-tools/src/wanilla"
SUITE = "wanilla/src/test/resources/wien/secpriv/wasm/NoninterferenceTests"
DIRECTORIES = ["basic", "complex", "examples", "figures-final", "rapid", "integrity"]
SECRET = {"ST": "H", "SU": "H", "PT": "L", "PU": "L"}


def run(command, **kwargs):
    return subprocess.run(command, capture_output=True, text=True, **kwargs)


def load_specs(path):
    text = re.sub(r"//.*", "", path.read_text())
    return json.loads(text)


def exports_of(wat):
    """Map an exported function's name to its index, from the text of the module."""
    names, index = {}, 0
    imported = len(re.findall(r"\(import\s+\"[^\"]*\"\s+\"[^\"]*\"\s+\(func", wat))
    for match in re.finditer(r"\(func\b([^()]*)((?:\(export \"([^\"]+)\"\))?)", wat):
        if match.group(3):
            names[match.group(3)] = imported + index
        index += 1
    for match in re.finditer(r"\(export \"([^\"]+)\" \(func \$?(\w+)\)\)", wat):
        if match.group(2).isdigit():
            names[match.group(1)] = int(match.group(2))
    return names


def public_import(imported):
    """Whether an imported function is what our default makes of an import: public parameters, results and context, and no state of the module written."""
    labels = [imported.get("context", "PT")] + imported.get("param", []) + imported.get("result", [])
    writes = any(key in imported for key in ("table_in", "table_out", "memory_out", "global_out"))
    return not writes and all(SECRET.get(label, "L") == "L" for label in labels)


def translate(spec, wat, wide=True):
    """Our policy for a specification, or the reason it is not expressible. `wide` translates the queries on imports and on the memory's data too."""
    queries = spec.get("queries", {})
    beyond = set(queries) - {"result", "global", "memory_size"}
    observed_memory = False
    if beyond:
        if not wide or not beyond <= {"memory_data", "memory", "imported_function"}:
            return None, "queries memory, tables or imports"
        observed_memory = bool(beyond & {"memory_data", "memory"}) and SECRET.get(spec.get("memory_out", {}).get("data", "PT"), "L") == "L"
    if all(label in ("PT", "ST") for label in spec.get("param", [])) is False and "integrity" in spec.get("comment", ""):
        return None, "integrity"
    if spec.get("imported_function"):
        if not wide or not all(public_import(imported) for imported in spec["imported_function"]):
            for imported in spec["imported_function"]:
                if SECRET.get(imported.get("context", "PT")) == "H" or any(SECRET.get(p) == "H" for p in imported.get("param", [])):
                    return None, "an import with a secret parameter or context"
            return None, "imports a function the host does not provide" if not wide else "an import with a secret result, or that writes the module's state"
    global_in, global_out = spec.get("global_in", []), spec.get("global_out", [])
    if global_out and any(SECRET[a] != SECRET[b] for a, b in zip(global_in, global_out)):
        return None, "a global labelled differently on entry and exit"
    if "function_id" in spec:
        function = spec["function_id"]
    else:
        name = spec.get("function_name") or spec.get("export")
        function = exports_of(wat).get(name) if name else None
        if function is None:
            return None, "no function named"
    params = " ".join(SECRET[l] for l in spec.get("param", []))
    # WANILLA lists results with the top of the stack first; a declaration lists them in order.
    results = " ".join(SECRET[l] for l in reversed(spec.get("result", [])))
    lines = [f"func {function} : {params} -> {results}".replace("  ", " ")]
    lines += [f"global {i} : {SECRET[l]}" for i, l in enumerate(global_in)]
    memory = spec.get("memory_in")
    if memory and SECRET[memory["data"]] == "H":
        lines.append("load-default : H")
    if observed_memory:
        lines += [f"store-default func {i} : L" for i in range(len(re.findall(r"\(func\b", wat)))]
    return "\n".join(lines) + "\n", None


def verdict_of(wasm_ifc, scratch, wasm, expected, policy, reason):
    """The comparison's verdict for one translation of a specification."""
    if policy is None:
        return {"verdict": "not expressible", "reason": reason}
    policy_file = Path(scratch) / "policy"
    policy_file.write_text(policy)
    checked = run([wasm_ifc, "check", "--policy", str(policy_file), str(wasm)])
    accepted = checked.returncode == 0
    error = checked.stderr.strip()
    if not accepted and ("Decode error" in error or "BadPolicy" in error):
        return {"verdict": "not expressible", "reason": error}
    if expected == "SAT":
        return {"verdict": "missed" if accepted else "caught statically", "error": error or None, "policy": policy}
    return {"verdict": "precise" if accepted else "precision loss", "error": error or None, "policy": policy}


def main():
    artifact = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT
    suite = artifact / SUITE
    wasm_ifc = run(["cabal", "list-bin", "exe:wasm-ifc"], cwd=ROOT, check=True).stdout.strip()
    rows = []
    with tempfile.TemporaryDirectory() as scratch:
        for directory in DIRECTORIES:
            for spec_file in sorted((suite / directory).glob("*.json")):
                wasm, wat_path = spec_file.with_suffix(".wasm"), spec_file.with_suffix(".wat")
                wat = wat_path.read_text() if wat_path.exists() else ""
                for spec in load_specs(spec_file):
                    if spec.get("ignore"):
                        continue
                    queries = spec.get("queries", {})
                    expected = "SAT" if '"SAT"' in json.dumps(queries) else "UNSAT"
                    row = {"module": f"{directory}/{spec_file.stem}", "test_id": spec.get("test_id"), "expected": expected}
                    if directory == "integrity":
                        row.update(verdict="not expressible", reason="integrity", verdict_narrow="not expressible")
                        rows.append(row)
                        continue
                    row.update(verdict_of(wasm_ifc, scratch, wasm, expected, *translate(spec, wat)))
                    row["verdict_narrow"] = verdict_of(wasm_ifc, scratch, wasm, expected, *translate(spec, wat, wide=False))["verdict"]
                    rows.append(row)
    counts = collections.Counter(r["verdict"] for r in rows)
    reasons = collections.Counter(r.get("reason") for r in rows if r["verdict"] == "not expressible")
    commit = run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT).stdout.strip()
    out = ROOT / "casestudies/results" / f"{datetime.date.today().isoformat()}-{commit}-wanilla.json"
    narrow = collections.Counter(r["verdict_narrow"] for r in rows)
    out.write_text(json.dumps({"commit": commit, "counts": counts, "counts_narrow": narrow, "not_expressible": reasons, "specifications": rows}, indent=2) + "\n")
    print(dict(counts))
    print(dict(reasons))
    print("without the queries on imports and memory data:", dict(narrow))
    print(f"wrote {out.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
