#!/usr/bin/env python3
"""What a step of the machine can reach that the types do not vouch for, from GHC's Core.

  ./scripts/step-inventory.py             # build the dumps, compare with the two lists
  ./scripts/step-inventory.py --list      # print what was found, in the lists' format

The paper's lemma on type safety says that `Runtime.Interpreter.step` terminates and returns
one of its four results. GHC checks neither termination nor that a function raises no
exception. This script takes two inventories from the desugared Core of the library
(`-ddump-ds`), over the definitions that `step` can reach, and compares each with a list in
`test/`, in which every entry has its reason. Something found and not listed fails the check,
so that nothing of the kind appears unnoticed, and so does an entry that is no longer found.

1. Recursion (`test/recursion-allowed.txt`): the recursive binding groups, which GHC forms by
   dependency analysis: the `Rec { ... }` groups at the top level and the `letrec`s inside
   definitions. Each has the argument it descends on.
2. Partial functions (`test/partial-allowed.txt`): the uses of a function that can raise an
   exception or read outside an array (`error`, `head`, `fromJust`, `div`, an unchecked index
   and so on, the names in `PARTIAL` and `PARTIAL_METHODS` below). Each has why it does not.

Reachability is by name. The dump prints a name that is in scope without its module, so a
name that occurs in the Core of a definition is taken for the definition of that name in the
same module, or else for the one in each module that the module imports. A local variable
that shares its name with such a definition therefore adds an edge that is not there, which
only makes the lists longer. Definitions of other packages (base, containers, vector,
primitive) are not followed: that they terminate and raise nothing but what their
documentation says is assumed.

Not listed under recursion: the group that a derived `Eq` instance forms with its `/=`. There
`/=` is the class's default, which calls `==` through the instance's own dictionary, and `==`
does not call `/=`.

The library is built without optimization into `dist-recursion/`, apart from the ordinary
build, since the desugared Core does not depend on the optimization level.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / "dist-recursion"
RECURSION = ROOT / "test" / "recursion-allowed.txt"
PARTIALITY = ROOT / "test" / "partial-allowed.txt"
ENTRY = ("Runtime.Interpreter", "step")
FLAGS = "-O0 -ddump-ds -ddump-to-file -dsuppress-uniques -dsuppress-idinfo -dsuppress-coercions -dsuppress-type-applications -dsuppress-ticks -dppr-cols=100000"

SIGNATURE = re.compile(r"^(\S+) ::")
IMPORT = re.compile(r"^import\s+(?:qualified\s+)?([\w.]+)", re.M)
LOCAL_GROUP = re.compile(r"^(\s*)(?:letrec|joinrec) \{")
TOKEN = re.compile(r"[^\s()\[\]{},;`\\]+")

# Functions of other packages that can raise an exception, read outside an array, or defeat the
# types. A method of a class counts where it is applied to a dictionary, which tells it from a
# type variable of the same name (`mod`). The shifts are here because they raise on a negative
# count.
PARTIAL = {
    "error", "errorWithoutStackTrace", "undefined", "patError", "recSelError", "recConError", "noMethodBindingError",
    "nonExhaustiveGuardsError", "absentError", "impossible", "assert", "throw", "throwIO", "ioError",
    "head", "tail", "init", "last", "fromJust", "!!", "!", "read", "chr", "cycle",
    "unsafeCoerce", "unsafeCoerce#", "unsafePerformIO", "unsafeDupablePerformIO", "unsafeInterleaveIO",
}  # fmt: skip
PARTIAL_METHODS = {"div", "mod", "quot", "rem", "divMod", "quotRem", "toEnum", "succ", "pred", "^", "^^", "foldr1", "foldl1", "maximum", "minimum", "shiftL", "shiftR", "shift", "bit", "testBit", "setBit", "clearBit"}
UNCHECKED = re.compile(r"^(unsafe\w+|index\w+#|read\w+Array#|write\w+Array#|unchecked\w+#)$")


def base_name(token: str) -> str:
    """A name without its package and module."""
    if token in ("!", "!!", "^", "^^"):
        return token
    match = re.match(r"^(?:[\w-]+:)?(?:[A-Z][\w']*\.)+(.+)$", token)
    return match.group(1) if match else token


def build() -> None:
    result = subprocess.run(
        ["cabal", "build", "lib:wasm-ifc", f"--builddir={BUILD}", f"--ghc-options={FLAGS}"],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        sys.exit("the build for the dumps failed:\n" + result.stdout[-2000:] + result.stderr[-2000:])


def read_module(module: str, path: Path) -> tuple[dict[str, list[str]], list[list[str]]]:
    """The top-level definitions of a dump with the lines of each, and its top-level recursive groups."""
    definitions: dict[str, list[str]] = {}
    groups: list[list[str]] = []
    current: str | None = None
    group: list[str] | None = None
    for line in path.read_text().splitlines():
        if line.startswith("Rec {"):
            group, current = [], None
        elif line.startswith("end Rec }"):
            assert group is not None
            groups.append(group)
            group, current = None, None
        elif line.startswith("-- RHS size") or line.startswith("===================="):
            current = None
        elif match := SIGNATURE.match(line):
            # (An exported instance is printed with its module.)
            current = match.group(1).removeprefix(module + ".")
            definitions[current] = []
            if group is not None:
                group.append(current)
        elif current is not None:
            definitions[current].append(line)
    return definitions, groups


def local_groups(lines: list[str]) -> list[list[str]]:
    """The names that each `letrec` or `joinrec` of a definition binds."""
    found = []
    for number, line in enumerate(lines):
        match = LOCAL_GROUP.match(line)
        if not match:
            continue
        inner = re.compile(rf"^{match.group(1)}  (\S+) ::")
        names = []
        for later in lines[number + 1 :]:
            if later.startswith(match.group(1)) and len(later) > len(match.group(1)) and later[len(match.group(1))] != " ":
                break
            if bound := inner.match(later):
                names.append(bound.group(1))
        found.append(names)
    return found


def main() -> None:
    if "--no-build" not in sys.argv:
        build()
    modules: dict[str, dict[str, list[str]]] = {}
    imports: dict[str, set[str]] = {}
    recursive: dict[tuple[str, str], str] = {}
    for path in sorted(BUILD.rglob("*.dump-ds")):
        module = ".".join(path.relative_to(next(p for p in path.parents if p.name == "src")).with_suffix("").parts)
        definitions, groups = read_module(module, path)
        modules[module] = definitions
        source = (ROOT / "src" / Path(*module.split("."))).with_suffix(".hs").read_text()
        imports[module] = set(IMPORT.findall(source))
        for group in groups:
            if all(name == "$c/=" or name.startswith("$fEq") for name in group):
                continue
            for name in group:
                recursive[(module, name)] = "itself" if len(group) == 1 else "group " + " ".join(sorted(group))
    if ENTRY[0] not in modules or ENTRY[1] not in modules[ENTRY[0]]:
        sys.exit(f"no definition of {ENTRY[0]}.{ENTRY[1]} in the dumps under {BUILD}")

    defined_in: dict[str, list[str]] = {}
    for module, definitions in modules.items():
        for name in definitions:
            defined_in.setdefault(name, []).append(module)

    def references(module: str, name: str) -> set[tuple[str, str]]:
        found = set()
        for line in modules[module][name]:
            for token in TOKEN.findall(line):
                if token in modules[module]:
                    found.add((module, token))
                elif token in defined_in:
                    found.update((other, token) for other in defined_in[token] if other in imports[module])
                elif "." in token:
                    qualifier, _, rest = token.rpartition(".")
                    # (An operator such as `Mod..+.` splits at the wrong dot; none is defined here.)
                    if qualifier in modules and rest in modules[qualifier]:
                        found.add((qualifier, rest))
        return found

    reached, frontier = {ENTRY}, [ENTRY]
    while frontier:
        for target in references(*frontier.pop()):
            if target not in reached:
                reached.add(target)
                frontier.append(target)

    found: dict[str, str] = {}
    for module, name in sorted(reached):
        if (module, name) in recursive:
            found[f"{module}.{name}"] = recursive[(module, name)]
        for group in local_groups(modules[module][name]):
            for local in group:
                found[f"{module}.{name}/{local}"] = "itself" if len(group) == 1 else "group " + " ".join(sorted(group))

    partial: set[tuple[str, str]] = set()
    for module, name in sorted(reached):
        tokens = [token for line in modules[module][name] for token in TOKEN.findall(line)]
        for token, following in zip(tokens, tokens[1:] + [""]):
            if token in modules[module]:
                continue
            base = base_name(token)
            applied = base_name(following).startswith(("$f", "$d"))
            if base in PARTIAL or UNCHECKED.match(base) or (base in PARTIAL_METHODS and applied):
                partial.add((f"{module}.{name}", base))

    if "--list" in sys.argv:
        for key, kind in found.items():
            print(f"{key} | {kind} | ")
        print()
        for key, base in sorted(partial):
            print(f"{key} | {base} | ")
        print(f"# {len(reached)} definitions reached from {ENTRY[0]}.{ENTRY[1]}: {len(found)} recursive, {len(partial)} uses of partial functions", file=sys.stderr)
        return

    def entries(path: Path) -> list[tuple[str, str, str]]:
        listed = []
        for line in path.read_text().splitlines():
            if line.strip() and not line.startswith("#"):
                key, second, reason = (part.strip() for part in line.split("|", 2))
                if not reason:
                    sys.exit(f"{path.name}: {key} has no reason")
                listed.append((key, second, reason))
        return listed

    failed = False
    allowed = {key for key, _, _ in entries(RECURSION)}
    for key in sorted(set(found) - allowed):
        print(f"FAIL recursive and not in {RECURSION.name}: {key} ({found[key]})")
        failed = True
    for key in sorted(allowed - set(found)):
        print(f"FAIL in {RECURSION.name} and no longer recursive or reached: {key}")
        failed = True
    # (In the list of partial functions, `*` for the definition allows a function everywhere.)
    listed = {(key, base) for key, base, _ in entries(PARTIALITY)}
    everywhere = {base for key, base in listed if key == "*"}
    for key, base in sorted(partial):
        if (key, base) not in listed and base not in everywhere:
            print(f"FAIL a partial function that is not in {PARTIALITY.name}: {base} in {key}")
            failed = True
    for key, base in sorted(listed):
        if (key != "*" and (key, base) not in partial) or (key == "*" and base not in {b for _, b in partial}):
            print(f"FAIL in {PARTIALITY.name} and no longer found: {base} in {key}")
            failed = True
    if failed:
        sys.exit(1)
    print(f"step inventory ok ({len(reached)} definitions reached, {len(found)} recursive and {len(partial)} uses of partial functions, all listed)")


if __name__ == "__main__":
    main()
