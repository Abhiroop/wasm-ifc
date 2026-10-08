#!/usr/bin/env python3
"""Summarise a run of the spec testsuite by the feature each skipped assertion needs.

    WASM_IFC_SPEC_REPORT=/tmp/spec.jsonl cabal test wasm-ifc-spec
    ./scripts/spec-report.py /tmp/spec.jsonl

The runner appends one JSON line per script (test/SpecSuite.hs). A skip's reason is "needs F"
where `wasm-tools validate` says the module uses the features F beyond the supported subset,
and otherwise the decoder's or the harness's own message, which GAPS groups.
"""
import collections
import json
import re
import sys

GAPS = [
    ("text-format modules (not a feature: the harness runs binaries)", r"text-format"),
    ("exceptions", r"assert_exception"),
    ("in the subset: imports of tables, memories and globals; linking between modules", r"import|register|could not be linked|module_definition|module_instance|action "),
    ("in the subset: passive element segments and the bulk table instructions", r"element segment|0xFC opcode|table"),
]


def main():
    rows = [json.loads(line) for line in open(sys.argv[1])]
    by_feature, other = collections.Counter(), collections.Counter()
    for row in rows:
        for reason, count in row["reasons"]:
            if reason.startswith("needs "):
                by_feature[reason[len("needs "):]] += count
                continue
            for gap, pattern in GAPS:
                if re.search(pattern, reason):
                    by_feature[gap] += count
                    break
            else:
                other[reason] += count
    print(f"{len(rows)} scripts: {sum(r['passed'] for r in rows)} passed, {sum(r['failed'] for r in rows)} failed, {sum(r['skipped'] for r in rows)} skipped")
    print(f"scripts with no skipped assertion: {sum(1 for r in rows if not r['skipped'])}")
    for feature, count in by_feature.most_common():
        print(f"{count:7d}  {feature}")
    for reason, count in other.most_common(15):
        print(f"{count:7d}  other: {reason[:100]}")


if __name__ == "__main__":
    main()
