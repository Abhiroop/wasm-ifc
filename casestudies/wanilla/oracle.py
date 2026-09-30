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
parameter or context (a host import must be public here), or queries memory, whose attacker
observes every byte where ours observes the bytes labelled public.

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


def translate(spec, wat):
    """Our policy for a specification, or the reason it is not expressible."""
    queries = spec.get("queries", {})
    if set(queries) - {"result", "global", "memory_size"}:
        return None, "queries memory, tables or imports"
    if all(label in ("PT", "ST") for label in spec.get("param", [])) is False and "integrity" in spec.get("comment", ""):
        return None, "integrity"
    if spec.get("imported_function"):
        for imported in spec["imported_function"]:
            if SECRET.get(imported.get("context", "PT")) == "H" or any(SECRET.get(p) == "H" for p in imported.get("param", [])):
                return None, "an import with a secret parameter or context"
        return None, "imports a function the host does not provide"
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
    return "\n".join(lines) + "\n", None


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
                    expected = "SAT" if any(v == "SAT" for v in queries.values() if isinstance(v, str)) else "UNSAT"
                    row = {"module": f"{directory}/{spec_file.stem}", "test_id": spec.get("test_id"), "expected": expected}
                    if directory == "integrity":
                        row.update(verdict="not expressible", reason="integrity")
                        rows.append(row)
                        continue
                    policy, reason = translate(spec, wat)
                    if policy is None:
                        row.update(verdict="not expressible", reason=reason)
                        rows.append(row)
                        continue
                    policy_file = Path(scratch) / "policy"
                    policy_file.write_text(policy)
                    checked = run([wasm_ifc, "check", "--policy", str(policy_file), str(wasm)])
                    accepted = checked.returncode == 0
                    error = checked.stderr.strip()
                    if not accepted and ("Decode error" in error or "BadPolicy" in error):
                        row.update(verdict="not expressible", reason=error)
                    elif expected == "SAT":
                        row.update(verdict="missed" if accepted else "caught statically", error=error or None)
                    else:
                        row.update(verdict="precise" if accepted else "precision loss", error=error or None)
                    row["policy"] = policy
                    rows.append(row)
    counts = collections.Counter(r["verdict"] for r in rows)
    reasons = collections.Counter(r.get("reason") for r in rows if r["verdict"] == "not expressible")
    commit = run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT).stdout.strip()
    out = ROOT / "casestudies/results" / f"{datetime.date.today().isoformat()}-{commit}-wanilla.json"
    out.write_text(json.dumps({"commit": commit, "counts": counts, "not_expressible": reasons, "specifications": rows}, indent=2) + "\n")
    print(dict(counts))
    print(dict(reasons))
    print(f"wrote {out.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
