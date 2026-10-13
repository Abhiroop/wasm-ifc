#!/usr/bin/env python3
"""Count, in compiled modules, the instructions that SecWasm's printed rules reject and
WebAssembly's validation accepts (the paper's "rules that are too strict for compiled code").

  ./scripts/secwasm-shapes.py LABEL=DIR-OR-FILE[,DIR-OR-FILE...]...     # a table, one row per label
  ./scripts/secwasm-shapes.py --json out.json LABEL=DIR...

Four shapes, each counted per instruction and per module that has one:

  table > blocks   a `br_table` with more targets (the default included) than there are
                   enclosing blocks, loops and conditionals: T-Br-Table asks |gamma| >= m.
  table, below     a `br_table` reached with values on the block's stack below the ones it
                   carries: T-Br-Table keeps them in the type of the rest of the block.
  unreachable      an `unreachable` where the block's stack is not the block's result type:
                   T-Unreachable leaves the stack as it is, so the block's end does not type.
  branch to body   a `br`, `br_if` or `br_table` whose target is the function body: T-Func
                   types a body without a label.

The script reads `wasm-tools print` of each module with its custom sections stripped, and
types the instructions as validation does, by the stack of each block. It checks itself: where
a block ends, its stack must be the block's result type, and a module in which that fails, or
that uses an instruction the script does not know, is reported as not analysed, not counted.
"""

from __future__ import annotations

import json, re, subprocess, sys, tempfile
from collections import Counter
from pathlib import Path

NUM = ("i32", "i64", "f32", "f64")
UNARY = {"clz", "ctz", "popcnt", "abs", "neg", "sqrt", "ceil", "floor", "trunc", "nearest", "extend8_s", "extend16_s", "extend32_s"}
BINARY = {"add", "sub", "mul", "div", "div_s", "div_u", "rem_s", "rem_u", "and", "or", "xor", "shl", "shr_s", "shr_u", "rotl", "rotr", "min", "max", "copysign"}
COMPARE = {"eq", "ne", "lt", "gt", "le", "ge", "lt_s", "lt_u", "gt_s", "gt_u", "le_s", "le_u", "ge_s", "ge_u"}
CONVERSION = re.compile(r"_(i32|i64|f32|f64)(_[su])?$")
SHAPES = ("table > blocks", "table, below", "unreachable", "branch to body")


class NotAnalysed(Exception):
    pass


def types_in(text: str, keyword: str) -> list[str]:
    return [t for group in re.findall(rf"\({keyword}((?: [a-z0-9]+)*)\)", text) for t in group.split()]


class Frame:
    def __init__(self, label: list[str], results: list[str], stack: list[str]):
        self.label, self.results, self.stack, self.unreachable = label, results, stack, False


def analyse(wat: str) -> Counter:
    counts: Counter = Counter()
    types, functions, globals_ = {}, [], []
    for index, body in re.findall(r"^\s*\(type \(;(\d+);\) \(func(.*)\)\)$", wat, re.M):
        types[int(index)] = (types_in(body, "param"), types_in(body, "result"))
    lines = wat.splitlines()
    position = 0
    while position < len(lines):
        line = lines[position].strip()
        position += 1
        imported = re.match(r'\(import "[^"]*" "[^"]*" \((func|global|table|memory|tag)\b(.*)\)\)$', line)
        if imported:
            if imported.group(1) == "func":
                functions.append(types[int(re.search(r"\(type (\d+)\)", imported.group(2)).group(1))])
            elif imported.group(1) == "global":
                globals_.append(re.search(r"(i32|i64|f32|f64|funcref|externref)", imported.group(2)).group(1))
            continue
        declared = re.match(r"\(global \(;\d+;\) (?:\(mut (\w+)\)|(\w+))", line)
        if declared:
            globals_.append(declared.group(1) or declared.group(2))
            continue
        if line.startswith("(func "):
            functions.append(types[int(re.search(r"\(type (\d+)\)", line).group(1))])
    # Second pass: the bodies, now that every function's type is known.
    defined = len([1 for line in lines if re.match(r'\s*\(import "[^"]*" "[^"]*" \(func', line)])
    position = 0
    while position < len(lines):
        line = lines[position].strip()
        position += 1
        if not line.startswith("(func "):
            continue
        params, results = functions[defined]
        defined += 1
        locals_ = list(params)
        body = []
        # (A function without instructions is printed on one line, closed where it opens.)
        while position < len(lines) and line.count("(") != line.count(")"):
            inner = lines[position].strip()
            position += 1
            if inner.startswith("(local"):
                locals_ += types_in(inner, "local")
            elif inner == ")":
                break
            else:
                body.append(inner)
        function_shapes(body, locals_, results, types, functions, globals_, counts)
        counts["functions"] += 1
    return counts


def block_type(text: str, types: dict) -> tuple[list[str], list[str]]:
    named = re.search(r"\(type (\d+)\)", text)
    if named:
        return types[int(named.group(1))]
    return types_in(text, "param"), types_in(text, "result")


def function_shapes(body, locals_, results, types, functions, globals_, counts) -> None:
    frames = [Frame(results, results, [])]

    def pop(expected: str | None = None) -> str:
        frame = frames[-1]
        if not frame.stack:
            if frame.unreachable:
                return expected or "?"
            raise NotAnalysed("pop from an empty stack")
        return frame.stack.pop()

    def push(*pushed: str) -> None:
        frames[-1].stack.extend(pushed)

    def leave() -> None:
        frame = frames[-1]
        if not frame.unreachable and [t for t in frame.stack] != frame.results:
            if not (len(frame.stack) == len(frame.results) and all(a == b or "?" in (a, b) for a, b in zip(frame.stack, frame.results))):
                raise NotAnalysed(f"a block ends with {frame.stack}, declared {frame.results}")

    def transfer() -> None:
        frames[-1].stack.clear()
        frames[-1].unreachable = True

    for index, line in enumerate(body):
        line = re.sub(r"\s*;; label = @\d+$", "", line)
        words = re.sub(r"\(;[^;]*;\)", "", line).split()
        if not words:
            continue
        op = words[0]
        counts["instructions"] += 1
        depth = len(frames) - 1
        if op in ("block", "loop", "if"):
            if op == "if":
                pop("i32")
            taken, given = block_type(line, types)
            arguments = [pop(t) for t in reversed(taken)][::-1]
            frames.append(Frame(taken if op == "loop" else given, given, arguments))
            frames[-1].params = taken
        elif op == "else":
            leave()
            frame = frames[-1]
            frame.stack, frame.unreachable = list(frame.params), False
        elif op == "end":
            leave()
            done = frames.pop()
            if not frames:
                raise NotAnalysed("an end without a block")
            push(*done.results)
        elif op in ("br", "br_if", "br_table"):
            targets = [int(w) for w in words[1:]]
            if op != "br":
                pop("i32")
            if any(t > depth for t in targets):
                raise NotAnalysed("a branch out of the function")
            if op == "br_table":
                counts["br_table"] += 1
                if len(targets) > depth:
                    counts["table > blocks"] += 1
                carried = len(frames[-1 - targets[-1]].label)
                if not frames[-1].unreachable and len(frames[-1].stack) > carried:
                    counts["table, below"] += 1
            counts["branches"] += 1
            if any(t == depth for t in targets):
                counts["branch to body"] += 1
            if op != "br_if":
                transfer()
        elif op == "unreachable":
            counts["unreachable (all)"] += 1
            frame = frames[-1]
            if not frame.unreachable and frame.stack != frame.results:
                counts["unreachable"] += 1
            transfer()
        elif op == "return":
            transfer()
        elif op == "nop":
            pass
        elif op == "drop":
            pop()
        elif op == "select":
            pop("i32")
            first = pop()
            pop()
            push(first)
        elif op in ("local.get", "local.set", "local.tee"):
            kind = locals_[int(words[1])]
            if op != "local.get":
                pop(kind)
            if op != "local.set":
                push(kind)
        elif op in ("global.get", "global.set"):
            kind = globals_[int(words[1])]
            push(kind) if op == "global.get" else pop(kind)
        elif op in ("call", "return_call"):
            taken, given = functions[int(words[1])]
            for t in reversed(taken):
                pop(t)
            transfer() if op == "return_call" else push(*given)
        elif op in ("call_indirect", "return_call_indirect"):
            taken, given = block_type(line, types)
            pop("i32")
            for t in reversed(taken):
                pop(t)
            transfer() if op == "return_call_indirect" else push(*given)
        elif op == "memory.size":
            push("i32")
        elif op == "memory.grow":
            pop("i32")
            push("i32")
        elif op in ("memory.copy", "memory.fill", "memory.init", "table.copy", "table.init", "table.fill"):
            pop(), pop(), pop()
        elif op in ("data.drop", "elem.drop"):
            pass
        elif op == "ref.null" or op == "ref.func":
            push("ref")
        elif op == "ref.is_null":
            pop()
            push("i32")
        elif op == "table.get":
            pop("i32")
            push("ref")
        elif op == "table.set":
            pop(), pop("i32")
        elif op == "table.size":
            push("i32")
        elif op == "table.grow":
            pop("i32"), pop()
            push("i32")
        elif "." in op and op.split(".")[0] in NUM:
            kind, name = op.split(".", 1)
            converted = CONVERSION.search(name)
            if name == "const":
                push(kind)
            elif name.startswith("load"):
                pop("i32")
                push(kind)
            elif name.startswith("store"):
                pop(kind), pop("i32")
            elif converted:
                pop(converted.group(1))
                push(kind)
            elif name == "eqz":
                pop(kind)
                push("i32")
            elif name in COMPARE:
                pop(kind), pop(kind)
                push("i32")
            elif name in UNARY:
                pop(kind)
                push(kind)
            elif name in BINARY:
                pop(kind), pop(kind)
                push(kind)
            else:
                raise NotAnalysed(f"instruction {op}")
        else:
            raise NotAnalysed(f"instruction {op}")
    leave()
    if len(frames) != 1:
        raise NotAnalysed("a block that does not end")


def modules_of(target: Path) -> list[Path]:
    return [target] if target.is_file() else sorted(target.rglob("*.wasm"))


def main() -> int:
    arguments = sys.argv[1:]
    out = None
    if arguments[:1] == ["--json"]:
        out, arguments = Path(arguments[1]), arguments[2:]
    if not arguments:
        print(__doc__, file=sys.stderr)
        return 2
    report = {}
    with tempfile.TemporaryDirectory() as scratch:
        for argument in arguments:
            label, _, where = argument.partition("=")
            total: Counter = Counter()
            having: Counter = Counter()
            skipped = []
            modules = [module for part in where.split(",") for module in modules_of(Path(part))]
            for module in modules:
                stripped = Path(scratch) / "m.wasm"
                subprocess.run(["wasm-tools", "strip", "-a", str(module), "-o", str(stripped)], check=True)
                wat = subprocess.run(["wasm-tools", "print", str(stripped)], capture_output=True, text=True, check=True).stdout
                try:
                    counts = analyse(wat)
                except NotAnalysed as reason:
                    skipped.append((module.name, str(reason)))
                    continue
                total.update(counts)
                having.update(shape for shape in SHAPES if counts[shape])
                having["any"] += any(counts[shape] for shape in SHAPES)
            report[label] = {"modules": len(modules), "analysed": len(modules) - len(skipped), "not_analysed": skipped, "instructions": dict(total), "modules_with": dict(having)}
    print("| Binaries | Modules | Functions | " + " | ".join(f"{s} (instr.; modules)" for s in SHAPES) + " | `br_table` | `unreachable` | Modules with any |")
    print("|---|---:|---:|" + "---:|" * (len(SHAPES) + 3))
    for label, row in report.items():
        total, having = row["instructions"], row["modules_with"]
        cells = [f"{total.get(s, 0):,}; {having.get(s, 0)}" for s in SHAPES]
        analysed = f"{row['analysed']}" + (f" of {row['modules']}" if row["analysed"] != row["modules"] else "")
        print(f"| {label} | {analysed} | {total.get('functions', 0):,} | " + " | ".join(cells) + f" | {total.get('br_table', 0):,} | {total.get('unreachable (all)', 0):,} | {having.get('any', 0)} |")
        for name, reason in row["not_analysed"]:
            print(f"<!-- not analysed: {label}/{name}: {reason} -->")
    if out:
        out.write_text(json.dumps(report, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
