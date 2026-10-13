#!/usr/bin/env bash
# An anonymized copy of this tree, for the paper's artifact and its data-availability statement.
#
#   ./scripts/artifact.sh [OUT]        # default ../wasm-ifc-artifact
#
# It writes OUT/wasm-ifc/ and OUT/wasm-ifc-artifact.tar.gz, and publishes nothing. The copy is
# the files of HEAD, so it has no history and no commit messages. Removed: the agents' guide
# and the pointer to the paper. Rewritten: the licence's and the package's author lines, the
# authors' names where a document mentions them, e-mail addresses, and absolute paths under a
# home directory (in recorded results). The archive's entries carry no user name and one fixed
# date. The script then searches every file, binaries included, for what it was to remove, and
# fails if it finds any.
set -euo pipefail
cd "$(dirname "$0")/.."
OUT=$(mkdir -p "${1:-../wasm-ifc-artifact}" && cd "${1:-../wasm-ifc-artifact}" && pwd)
TREE=$OUT/wasm-ifc
commit=$(git rev-parse --short HEAD)
if [ -n "$(git status --porcelain)" ]; then echo "the working tree has changes that HEAD does not have: commit first" >&2; exit 1; fi

rm -rf "$TREE" "$OUT/wasm-ifc-artifact.tar.gz"
mkdir -p "$TREE"
git archive HEAD | tar -x -C "$TREE"
# (This script names what it removes, so it is not in the copy either.)
rm -rf "$TREE/CLAUDE.md" "$TREE/paper" "$TREE/.gitmodules" "$TREE/scripts/artifact.sh"

# The two official test suites are submodules, which a copy without history cannot fetch.
suites=""
for path in test/spec/testsuite test/wasi/testsuite; do
    url=$(git config -f .gitmodules "submodule.$path.url")
    pinned=$(git ls-tree HEAD "$path" | awk '{print $3}')
    suites+="git clone $url $path && git -C $path checkout $pinned"$'\n'
done

python3 - "$TREE" "$commit" "$suites" <<'EOF'
import re, sys
from pathlib import Path

tree, commit, suites = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
REWRITES = [
    (re.compile(r"/tmp/claude-\d+/[^/\"\s]+"), "/tmp/scratch"),
    (re.compile(r"/home/[A-Za-z0-9_.-]+/(?:[A-Za-z0-9_.-]+/)*?wasm-ifc[A-Za-z-]*"), "."),
    (re.compile(r"/home/[A-Za-z0-9_.-]+"), "~"),
    (re.compile(r"-home-[A-Za-z0-9_]+-repos-[A-Za-z0-9_]+-wasm-ifc[A-Za-z-]*"), "scratch"),
    (re.compile(r"\b(Daniel|Abhi(roop)?)'s\b"), "an author's"),
    (re.compile(r"\b(Daniel|Abhi(roop)?)\b"), "an author"),
    (re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9-]+\.[A-Za-z]{2,}(\.[A-Za-z]{2,})*"), "anonymous@example.org"),
]
changed = 0
for path in sorted(p for p in tree.rglob("*") if p.is_file()):
    try:
        text = path.read_text()
    except UnicodeDecodeError:
        continue
    new = text
    for pattern, replacement in REWRITES:
        new = pattern.sub(replacement, new)
    if path.name == "LICENSE":
        new = re.sub(r"^Copyright \(c\) (\d+) .*$", r"Copyright (c) \1 the authors", new, count=1, flags=re.M)
    if path.suffix == ".cabal":
        new = re.sub(r"^author:.*$", "author:             Anonymous", new, flags=re.M)
    if new != text:
        path.write_text(new)
        changed += 1
reproduce = tree / "REPRODUCE.md"
text = reproduce.read_text()
before = "git submodule update --init                 # the two official test suites\n"
assert before in text, "REPRODUCE.md no longer has the line that fetches the suites"
reproduce.write_text(
    text.replace(before, suites)
    + f"\n## This copy\n\nAn anonymized copy of the repository at commit `{commit}`. A script of the repository made\n"
    "it and is not in it: the copy has no history, no author lines and no absolute paths of the\n"
    "machines it was developed on. The two test suites are fetched by the commands above instead\n"
    "of as submodules.\n"
)
print(f"rewrote {changed} files")
EOF

# Nothing of what was to go may be left, in text or in a binary.
if grep -r -a -l -E "Daniel|Gal[aá]n|Abhi|dgalan|asiamgenius|/home/[a-z]|[Aa]nthropic|Claude|overleaf|ethz" "$TREE" > "$OUT/left.txt"; then
    echo "still identifying, see $OUT/left.txt:" >&2
    head -20 "$OUT/left.txt" >&2
    exit 1
fi
rm -f "$OUT/left.txt"
user=$(id -un)
if grep -r -a -l -w "$user" "$TREE" > "$OUT/left.txt"; then echo "the user's name is in:" >&2; head "$OUT/left.txt" >&2; exit 1; fi
rm -f "$OUT/left.txt"

tar -C "$OUT" --sort=name --owner=0 --group=0 --numeric-owner --mtime='2026-10-13 00:00Z' -czf "$OUT/wasm-ifc-artifact.tar.gz" wasm-ifc
echo "commit $commit: $(find "$TREE" -type f | wc -l) files, $(du -sh "$TREE" | cut -f1) unpacked, $(du -h "$OUT/wasm-ifc-artifact.tar.gz" | cut -f1) packed"
echo "sha256 $(sha256sum "$OUT/wasm-ifc-artifact.tar.gz" | cut -d' ' -f1)"
echo "written to $OUT (not published)"
