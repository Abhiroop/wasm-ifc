#!/usr/bin/env python3
"""Write lean/STATEMENTS.md, the reading guide, with the current line numbers.

  cd lean && ./guide.py

The guide's text is here; the line of each definition and rule is looked up in the sources, so
run this again after a change to `WasmIfc/Defs.lean`, `Basic.lean`, `Statement.lean` or
`Machine.lean`, or to `src/Runtime/Interpreter.hs`.
"""

from __future__ import annotations

import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCES = {name: (HERE / "WasmIfc" / f"{name}.lean").read_text().splitlines() for name in ("Defs", "Basic", "Statement", "Noninterference", "Confinement", "Machine")}
INTERPRETER = (HERE.parent / "src" / "Runtime" / "Interpreter.hs").read_text().splitlines()


def hs(pattern: str) -> str:
    """Where the Haskell machine has something, as a line of `src/Runtime/Interpreter.hs`."""
    for number, line in enumerate(INTERPRETER, 1):
        if re.search(pattern, line):
            return f"`Interpreter.hs:{number}`"
    raise SystemExit(f"Interpreter.hs: nothing matches {pattern!r}")


def line_of(source: str, pattern: str) -> int:
    for number, line in enumerate(SOURCES[source], 1):
        if re.search(pattern, line):
            return number
    raise SystemExit(f"{source}.lean: nothing matches {pattern!r}")


def at(source: str, pattern: str) -> str:
    return f"`{source}.lean:{line_of(source, pattern)}`"


def constructors(source: str, inductive: str) -> dict[str, int]:
    """The constructors of an inductive type, with the lines they start at."""
    lines = SOURCES[source]
    start = line_of(source, rf"^inductive {inductive}\b")
    found: dict[str, int] = {}
    for number in range(start + 1, len(lines) + 1):
        line = lines[number - 1]
        # (The next declaration, or its comment, starts in the first column.)
        if re.match(r"^(inductive|def|structure|theorem|abbrev|end|/--|/-!)", line):
            break
        match = re.match(r"^  \| (\w+)", line)
        if match:
            found.setdefault(match.group(1), number)
    return found


# Each typing rule: the constructor of `Syntax.Instructions.Instr` it stands for, the rule of the
# paper's appendix B ("The Rules") or the part of the paper that has it, and what differs.
RULES = [
    ("nil", "`INil`, the end of a sequence", "W-Seq", ""),
    ("const", "`IConst`", "W-Const", ""),
    ("binop", "`IAdd` and the other operations on two values", "W-Binop", "one rule for all of them"),
    ("unop", "the operations on one value, `IRefIsNull` among them", "W-Binop", ""),
    ("dup", "`IDuplicate`", "typed references", "written by the elaborator for `br_on_null`"),
    ("select", "`ISelect`", "W-Select", ""),
    ("drop", "`IDrop`", "W-Drop", ""),
    ("nop", "`INop`", "W-Nop", ""),
    ("relabel", "`IRelabelResults`", "W-Relabel, W-Nop-Sub", "raises labels of the block's whole segment"),
    ("localGet", "`ILocalGet`", "W-Get-Local", ""),
    ("localSet", "`ILocalSet`", "W-Set-Local", ""),
    ("localTee", "`ILocalTee`", "W-Tee-Local", ""),
    ("globalGet", "`IGlobalGet`", "as in SecWasm", ""),
    ("globalSet", "`IGlobalSet`", "W-Set-Global", "for a global that is not preserved"),
    ("globalSetPreserved", "`IGlobalSetPreserved`", "preserved globals", "the same instruction, for a preserved global"),
    ("load", "`ILoad`, `ILoadN`", "W-Load", "the level is the load's declaration; the check is in the semantics"),
    ("store", "`IStore`, `IStoreN`", "W-Store", "the level is at least the join, where the implementation takes the join"),
    ("fill", "`IMemFill`", "W-Memory-Fill", ""),
    ("copy", "`IMemCopy`", "W-Memory-Copy", ""),
    ("memInit", "`IMemInit`", "W-Memory-Init", ""),
    ("dataDrop", "`IDataDrop`", "bulk memory", "no premise"),
    ("memSize", "`IMemSize`", "as in SecWasm", ""),
    ("memGrow", "`IMemGrow`", "W-Memory-Grow", ""),
    ("tableGet", "`ITableGet`", "tables", "one table"),
    ("tableSet", "`ITableSet`", "tables", ""),
    ("tableFill", "`ITableFill`", "tables", ""),
    ("tableCopy", "`ITableCopy`", "tables", "one table, so the source's level is the table's"),
    ("tableSize", "`ITableSize`", "tables", ""),
    ("tableGrow", "`ITableGrow`", "tables", ""),
    ("hostRead", "a call of a host import that reads (`HostFunc`), with the driver's labelling", "W-Host", "one call stands for the reading ones"),
    ("hostWrite", "a call of a host import that writes, with the driver's check", "W-Host", "one call stands for the writing ones"),
    ("hostOpen", "the host function `PathOpen` (`Runtime.Host`), which is not an instruction", "appendix B, Host-Open", "`path_open` with the operands of the paper's `host.open`"),
    ("block", "`IBlock`", "W-Block", "with `Restores`, the comparison of preserved globals"),
    ("loop", "`ILoop`", "W-Loop", "with `Restores`"),
    ("iter", "none: the iterations of a loop's body", "none", "no program contains it; the loop's rule types the body, and this one says the same of its iterations"),
    ("ite", "`IIf`", "W-If", "with `Restores`"),
    ("br", "`IBr`", "W-Br", ""),
    ("brIf", "`IBrIf`", "W-Br-If", "not taken, the carried values keep their labels"),
    ("brTable", "`IBrTable`", "W-Br-Table'", "the repaired rule"),
    ("ret", "`IReturn`", "W-Return", "the branch to the outermost label"),
    ("call", "`ICall`", "W-Call", ""),
    ("retCall", "`IReturnCall`", "tail calls", ""),
    ("retCallIndirect", "`IReturnCallIndirect`", "tail calls", ""),
    ("callIndirect", "`ICallIndirect`", "W-Call-Indirect", "the table's level is in the premise"),
    ("callRef", "`ICallRef`", "typed references", ""),
    ("unreachable", "`IUnreachable`", "W-Unreachable-Poly", ""),
    ("throw", "`IThrow`", "exceptions", "a tag is the number of public values it carries"),
    ("throwRef", "`IThrowRef`", "exceptions", "the reference is to an exception the state keeps"),
    ("tryTable", "`ITryTable`", "exceptions", ""),
]


def main() -> None:
    typed, evaluated = constructors("Defs", "Typed"), constructors("Defs", "Eval")
    missing = set(typed) - {name for name, *_ in RULES}
    if missing:
        raise SystemExit(f"rules without an entry in guide.py: {sorted(missing)}")
    semantics: dict[str, list[int]] = {}
    for name, number in evaluated.items():
        for rule, *_ in sorted(RULES, key=lambda r: -len(r[0])):
            if name.startswith(rule) or (rule == "ite" and name.startswith("ite")):
                semantics.setdefault(rule, []).append(number)
                break
    semantics["tryTable"] = [evaluated["tryCont"], evaluated["tryExit"]]
    semantics["globalSetPreserved"] = [evaluated["globalSet"]]
    rule_rows = "\n".join(
        f"| `{name}` | {typed[name]} | {', '.join(map(str, semantics.get(name, []))) or 'none: a trap'} | {constructor} | {paper} | {note} |" for name, constructor, paper, note in RULES
    )
    total = sum(len(lines) for lines in SOURCES.values()) + len((HERE / "WasmIfc" / "Examples.lean").read_text().splitlines())
    text = f"""# Reading the Lean development: what to check

For a reviewer who checks the definitions and the statement and leaves the proofs to Lean.
`lake build` checks every proof, and `#print axioms WasmIfc.machine_noninterference` lists
`propext`, `Classical.choice` and `Quot.sound` only. So what remains to be checked by a person
is that the definitions say what the paper says, and that the machine of the last section is
the implementation's. They are in three files, {len(SOURCES["Defs"])}, {len(SOURCES["Statement"])}
and {len(SOURCES["Machine"])} lines long, of the development's {total:,}:

- `WasmIfc/Defs.lean`: the syntax, the typing judgment, the states and the semantics.
- `WasmIfc/Statement.lean`: low equivalence, a call from outside, and the theorem.
- `WasmIfc/Machine.lean`: the small-step machine, down to `Config.entry`
  ({at("Machine", r"^def Config.entry")}), and the two theorems at its end. What is between
  is proof.

The other files (`Basic.lean`, `Confinement.lean`, `Noninterference.lean`) are lemmas and
proofs, and `Examples.lean` has small programs with their typings and runs. This file is
written by `lean/guide.py`, which looks the line numbers up.

## 1. Levels and types

| What | Where | Convince yourself that |
|---|---|---|
| `Lab`, `Lab.le`, `Lab.join` | {at("Defs", r"^inductive Lab")} | there are two levels, `L` flows into both, `H` only into `H`, and `join` is the least upper bound. |
| `STy`, `Pcs` | {at("Defs", r"^abbrev STy")} | a type stack and a pc stack are lists of levels, the top or the innermost block first. All values have one type, so a labelled type is its label. |
| `SFlows`, `AllGe` | {at("Defs", r"^def AllGe")} | `SFlows s t` is the paper's `st ⊑ st'` on stacks of one length, and `AllGe a st` says the level `a` flows into every label of `st`. |
| `raise`, `joinEach` | {at("Defs", r"^def raise")} | `raise a P i` joins `a` into the entries 0 to `i` of a pc stack (what a branch to label `i` does), and `joinEach` joins two pc stacks entry by entry (where the two arms of a conditional meet). |

## 2. Syntax

`Instr`, {at("Defs", r"^inductive Instr")}. Check that each constructor is the instruction its
comment names. Three things are not WebAssembly's syntax:

- A block type is two type stacks, the parameters and the results with their levels, where a
  binary has value types only. The elaborator chooses them.
- A block, a loop, a conditional and a `try_table` carry `keep`, the globals they compare
  where control comes out of them. In the implementation this is a witness of the typed
  instruction (`Restores`), and the compared globals are all the preserved ones.
- `iter` is not an instruction of any program (section 4 below).

`Func` ({at("Defs", r"^structure Func")}) is a function: its type, the levels of its other
locals, the globals compared at its return, and its body. `FuncTy`
({at("Defs", r"^structure FuncTy")}) is the paper's labelled function type: parameters, the
bound on the pc of its callers, results.

## 3. The typing judgment

`Typed C Ls e P st P' st'`, {at("Defs", r"^inductive Typed")}, is the paper's judgment of
appendix B, "The Rules": under the labels `Ls` (innermost first), the sequence `e` takes the pc
stack `P` and the current block's segment `st` to `P'` and `st'`. Each rule types one
instruction followed by the rest of its sequence, so the paper's W-Seq is built into every
rule. `Ctx` ({at("Defs", r"^structure Ctx")}) has the levels of the locals and the globals,
which globals are preserved, the function types, the level of the table and the tags.

Check each rule against the constructor of `Syntax.Instructions.Instr` and the paper's rule in
the table. The Lean rules are the lift-free ones: no rule raises the label of a value that was
on the stack before a branch.

| Lean rule | Line | Semantics (lines) | `Instr` constructor | Paper's rule | Note |
|---|---:|---|---|---|---|
{rule_rows}

Where the column of the paper's rule names no W-rule, the rule is in the paper's section on
what it adds to SecWasm (`sec:ifc-beyond`) and has no printed inference rule.

Two side definitions carry premises:

- `Restores C pcEnd after keep` ({at("Defs", r"^def Restores")}): either the pc does not drop
  where the construct ends (`pcEnd` flows into the first pc of `after`), or `keep` has every
  preserved global. Convince yourself that this is `Validation.Shape.Restores`.
- `ClauseOk` ({at("Defs", r"^def ClauseOk")}): a clause of a `try_table` names a label whose
  type has as many values as its tag carries, or none for a clause that catches everything.

What the Lean rules leave out of the paper's: the bracketed premises of the W-rules, which
hold only under SecWasm's restrictions (the theorem is for the rules without them, the weaker
hypothesis), and value types.

`WellTyped C F` ({at("Defs", r"^def WellTyped")}) is the paper's rule for functions, for every
function of the module: its body is typed under the one label of the function, from an empty
segment, at the function's bound; and either it ends under a public pc or the function
compares every preserved global at its return (`Validation.Shape.ReturnsWith`). It does not
ask a function's results to be at least its bound; the rules for the indirect call and the
call through a reference ask that of the type they expect, which is where the proof uses it.

## 4. States and semantics

`State`, {at("Defs", r"^structure State")}: the locals, the globals, the memory as bytes with a
level each, its size and limit, the function table with its size and limit, the levels of the host's channels (a stream, a directory, a file), the descriptor table, the
names of the files in each directory, what
was written to each and what is left to read from each, the data segments, and the
exceptions kept for the references to them.

`Eval F n ls e σ s o`, {at("Defs", r"^inductive Eval")}: in the module `F`, with enclosing
labels of arities `ls`, the sequence `e` on the segment `σ` and the state `s` ends as `o`. `n`
is the size of the derivation and nothing else. An outcome (`Out`,
{at("Defs", r"^inductive Out")}) is the end of the sequence, a branch to an enclosing label
with the values it carries, or an exception that nothing in the sequence caught. A trap is the
absence of a rule, and so is a run that does not terminate.

Convince yourself of six things, which are where this semantics is not the specification's
text:

1. **A block's body runs on the block's parameters alone** (`blockCont`,
   line {evaluated["blockCont"]}), and what is below them on the stack waits. On validated code
   this is what WebAssembly does, since a body cannot reach below its parameters. That the two
   agree is not proved.
2. **The run-time checks are premises.** A load goes on only if every byte it reads is within
   the memory and its level flows into the load's declared level (line {evaluated["load"]}).
   An instruction on the table goes on only if the entries it names are within the table.
   An indirect call goes on only if the entry names a function with the expected parameters
   and results whose bound is at least the expected one (line {evaluated["callIndirect"]}).
   A host write goes on only if every byte it takes flows into the level of the descriptor's
   channel (line {evaluated["hostWrite"]}), and a file is opened only if every byte of its
   name is public (line {evaluated["hostOpen"]}). These are the paper's hybrid checks.
3. **The comparison of preserved globals is a premise too** (`Kept`,
   {at("Defs", r"^def Kept")}): where control comes out of a block, a loop, a conditional or a
   `try_table` by its end or by a branch to its label, and where a call returns, the globals
   in `keep` hold what they held at the construct's start or at the call. A branch further
   out and an exception skip it.
4. **A loop runs `iter`** (lines {evaluated["loopCont"]} to {evaluated["iterExn"]}): the body
   again while it branches to the loop's label. The loop's comparison is therefore with the
   state at its first entry, as in the implementation.
5. **A call** (line {evaluated["call"]}) runs the callee's body on an empty segment with a
   frame made of the arguments, and gives the caller its own locals back. `return` and a
   branch to the function's label end the callee alike (`Out.lands`).
6. **A tail call** (line {evaluated["retCall"]}) is written as a call whose results the
   function returns. The function is gone when its callee runs, so an exception that leaves
   the callee is not offered to the function's own `try_table`s: it is the outcome `tailExn`,
   which every block passes (`Out.caught`, `Out.exits`) and which is an exception again for
   the function's caller (`Out.thrown`, in the rules `callExn` and `retCallExn`).

## 5. Low equivalence and the theorem

`LowEq C s t`, {at("Statement", r"^def LowEq")}, is the paper's low equivalence
(`def:attacker`). Clause by clause:

| The paper | `LowEq` |
|---|---|
| agree on every local variable labelled public, which includes the arguments | first clause, and the hypothesis `StkRel f.ty.params a0 a1` of the theorem for the arguments |
| agree on every public global | second clause |
| agree on every byte of memory labelled public in both | third clause |
| memories of the same size | `s.size = t.size`, and the same limit |
| the same table of descriptors | `s.sameHost t`: the descriptor table (`fdt`), and `s.chan = t.chan`: the channels' levels |
| the input not yet read from and the output written to every public channel | the clause on `out` and `inp` |
| every stack position labelled public | none: a call from outside starts on an empty stack |
| the same names of files in every directory | `s.sameHost t`: `names`, and the function that gives a file its channel (`file`) |
| (not in the paper) | the function table with its size and limit, if it is public (`State.sameTable`); a data segment that both states still have is the same; the two states keep the same exceptions for the references to them, and these carry as many values as their tags say (`ExnOk`), which holds of a new instance, which keeps none |

`Invoke F f a s e`, {at("Statement", r"^inductive Invoke")}: the function `f` called from
outside on the arguments `a` in the state `s` ends as `e`, by returning results or by an
exception. Convince yourself that it is `Eval` of the body as rule `call` runs it, the
comparison of the function's `keep` included, which the machine makes for the invoked function
as for a callee.

`noninterference`, {at("Statement", r"^theorem noninterference")}:

> For a well-typed module whose preserved globals are public, a function of it, two calls from
> low-equivalent states with arguments that agree where the parameters are public: if both
> calls end, both return or both end by the same exception with the same values; if they
> return, the results agree where the result type is public; and the final states are
> low-equivalent.

The paper's attacker observes the final values of the public globals, the bytes written to
public descriptors, and the results of the invoked function. All three are in the conclusion:
the second clause of `LowEq` for the final states, its clause on `out`, and the agreement of
the results.

### What is assumed

- `WellTyped C F`: every function of the module is typed, as section 3 says.
- `∀ i, C.preserved i → C.globals i = L`: a preserved global is public, which the policy
  ensures (`Validation.Policy`).
- The two calls are of the same function, and their arguments and states are related as above.
- Both calls end. A call that traps, fails a comparison of preserved globals, or runs for ever
  has no `Invoke`, and the theorem says nothing of it: the property is termination-insensitive.
- No declassification: the core has no such instruction.

### Where the statement differs from the paper's

- The paper's theorem is about the implementation's `step`, through an erasure, a typing
  inclusion and a refinement. `noninterference` is about the typed program directly, under
  the big-step semantics, and section 6 carries it to a small-step machine in Lean. The
  correspondence between the Lean rules and the Haskell constructors (the table of section
  3), and between the Lean machine and `step` (the table of section 6), is by reading.
- It concludes more than the paper states: whether a call ends by an exception, and which, is
  public.
- `tini` in `Noninterference.lean` is the same theorem in the terms of the proof (`StRel` and
  `PresEq`, which together are `LowEq`: `LowEq.split`, `LowEq.join`).

## 6. The machine, and refinement

`Machine.lean` has a small-step machine for the core, written after the implementation's
`step` ({hs(r"^step ::")}), and proves that `Eval` describes it.

`Step F c nx`, {at("Machine", r"^inductive Step")}: one transition, from the configuration
`c` to the next one or to the end of the run. `Runs F c e`,
{at("Machine", r"^inductive Runs")}: the transitions from `c` to the end `e`. A run that traps
or does not end has no `Runs`.

| Lean | Where | Haskell | Where | Convince yourself that |
|---|---|---|---|---|
| `Config`: `s`, `σ`, `e`, `K` | {at("Machine", r"^structure Config")} | `Config store locals stack code control` | {hs(r"^data Config ")} | the fields are the same; the Lean state has the local variables in it (`s.loc`). |
| `Frame.label` | {at("Machine", r"^  [|] label ")} | `BlockLabel below cont rest`, `HandlerLabel handlers below cont rest` | {hs(r"^    BlockLabel ::")} | a label has the operands below its block and the code after it; a block's label is one with no clauses. `keep` and `recorded` are the `IRequireRestored recorded` that the Haskell puts in front of `cont` ({hs(r"^comparingAfter ::")}). |
| `Frame.loop` | {at("Machine", r"^  [|] loop ")} | `LoopLabel below body cont rest` | {hs(r"^    LoopLabel ::")} | it has the body besides. |
| `Frame.call` | {at("Machine", r"^  [|] call ")} | `CallBoundary depth below callerLocals cont callerControl` | {hs(r"^    CallBoundary ::")} | it has the caller's locals. `checks` is the comparisons in front of `cont`: one for a call ({hs(r"^restoringOnReturn ::")}), and one more for each tail call made in the callee's place. The Lean machine has no bound on the depth of calls. |
| the empty control stack; `Config.entry` | {at("Machine", r"^def Config.entry")} | `EntryBoundary`; `startFunction` | {hs(r"^startFunction ::")} | a call from outside runs the body over a boundary of its own that has the function's comparison. |
| `Basic`, `Step.basic` | {at("Machine", r"^inductive Basic")} | the clauses of `stepInstr` that end in `stepped` | {hs(r"^stepInstr ::")} | each instruction that is not one of control does to the operands and the state what its `Eval` rule says (section 4), and traps where the rule has a premise that fails. |
| `Step.block`, `tryTable`, `loop`, `ite` | {at("Machine", r"^  [|] block ")} | the clauses for `IBlock`, `ITryTable`, `ILoop`, `IIf` | | the body runs on the construct's parameters over a new label. |
| `Step.endLabel`, `endLoop`, `endCall`, `done` | {at("Machine", r"^  [|] endLabel ")} | `popControl` | {hs(r"^popControl ::")} | at the end of the current block the top of the control stack says what follows, behind its comparisons. |
| `Unwind`, in `Step.br`, `brIf`, `brTable`, `ret` | {at("Machine", r"^inductive Unwind")} | `unwind`, `unwindTo`, `returnUnwind` | {hs(r"^unwind ::")} | a branch drops the labels it passes without their comparisons; a loop's label stays and its body runs again; the function's label is its boundary. |
| `Step.call`, `callIndirect`, `callRef` | {at("Machine", r"^  [|] call [{]i f")} | `enterCall` | {hs(r"^enterCall ::")} | the callee's body runs on no operands with locals made of the arguments, over a boundary. The checks of an indirect call are premises, as in `Eval`. |
| `boundary`, in `Step.retCall`, `retCallIndirect` | {at("Machine", r"^def boundary")} | `tailCall` | {hs(r"^tailCall ::")} | the labels of the running function are dropped, its clauses with them, and the callee is entered over the function's own boundary, which gets the callee's comparison too. |
| `Raise`, in `Step.throw` | {at("Machine", r"^inductive Raise")} | `throwException` | {hs(r"^throwException ::")} | an exception passes labels without a clause for it and call boundaries, where the caller's locals are back; the first clause for it is a branch from around the clause's block; below the last boundary it ends the run. |

`refinement`, {at("Machine", r"^theorem refinement")}: a run of the machine from
`Config.entry f a s` to an end `e` is `Invoke F f a s e`. No typing is assumed. This is the
paper's `lem:refinement`, in the direction the theorem needs.

`machine_noninterference`, {at("Machine", r"^theorem machine_noninterference")}: the statement
of `noninterference` with two runs of the machine for the two `Invoke`s.

What stays by reading is the table above: that the Haskell `step` makes the transitions of
`Step`. Four differences are known. The Haskell machine bounds the depth of calls and traps
beyond it. It suspends at a call of the host and is resumed with the results, where the
core's two host calls are instructions. Its typed instructions carry coercions between
segments (`relabelStack`), which do nothing to the values. And a clause by reference that
catches an exception thrown by `throw_ref` gets the reference it was thrown from, where the
Lean machine keeps the exception once more and hands out a new reference; WebAssembly has no
instruction that compares two references to exceptions.

### Outside the core

More than one value type, and so the numeric and vector instructions as such; 64-bit and
several memories; several tables;
linking; the WASI calls other than one that reads, one that writes and one that opens a file
in a directory, the error codes but the one for a missing file, and sockets; local variables split into webs and the inference of labels, which
happen before typing; declassification.
"""
    (HERE / "STATEMENTS.md").write_text(text)
    print(f"wrote lean/STATEMENTS.md ({len(text.splitlines())} lines)")


if __name__ == "__main__":
    main()
