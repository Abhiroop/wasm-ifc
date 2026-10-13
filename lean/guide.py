#!/usr/bin/env python3
"""Write lean/STATEMENTS.md, the reading guide, with the current line numbers.

  cd lean && ./guide.py

The guide's text is here; the line of each definition and rule is looked up in the sources, so
run this again after a change to a file of `WasmIfc/`, or to `src/Runtime/Interpreter.hs`.
"""

from __future__ import annotations

import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCES = {name: (HERE / "WasmIfc" / f"{name}.lean").read_text().splitlines() for name in ("Defs", "Basic", "Statement", "Noninterference", "Confinement", "Machine", "Findings", "SecWasmPrinted", "ValueTypes")}
INTERPRETER = (HERE.parent / "src" / "Runtime" / "Interpreter.hs").read_text().splitlines()
WASI = (HERE.parent / "src" / "Runtime" / "Wasi.hs").read_text().splitlines()


def wasi(pattern: str) -> str:
    """Where the host has something, as a line of `src/Runtime/Wasi.hs`."""
    for number, line in enumerate(WASI, 1):
        if re.search(pattern, line):
            return f"`Wasi.hs:{number}`"
    raise SystemExit(f"Wasi.hs: nothing matches {pattern!r}")


# The functions of WASI Preview 1 (sockets included), each with the constructor of its case in
# `runWasiCall`, the Lean primitive of its shape, and what in `Runtime.Wasi` makes it so.
HOST = [
    ("fd_read", "FdRead", "hostRead", "what is read and its count are stored at the descriptor's level (`readInto`, `pokeWord32At`)"),
    ("fd_pread", "FdPread", "hostRead", "as `fd_read`, at an offset that is an operand"),
    ("sock_recv", "SockRecv", "hostRead", "as `fd_read`; the flags it stores are at the connection's level too"),
    ("fd_readdir", "FdReaddir", "hostRead", "the entries and their size are stored at the directory's level"),
    ("path_readlink", "PathReadlink", "hostRead", "the link's contents are stored at the directory's level"),
    ("fd_filestat_get", "FdFilestatGet", "hostRead", "the attributes are stored at the descriptor's level (`pokeStat`)"),
    ("path_filestat_get", "PathFilestatGet", "hostRead", "the attributes are stored at the directory's level"),
    ("fd_tell", "FdTell", "hostRead", "the position is stored at the descriptor's level"),
    ("fd_write", "FdWrite", "hostWrite", "every byte taken must flow into the descriptor's level, or the run traps (`gather`)"),
    ("fd_pwrite", "FdPwrite", "hostWrite", "as `fd_write`"),
    ("sock_send", "SockSend", "hostWrite", "as `fd_write`"),
    ("path_open", "PathOpen", "hostOpen", "the new descriptor has the directory's level and a public number (`openPath`, `insertFd`); the path is public (`peekPath`) and stays in the directory (`confine`)"),
    ("sock_accept", "SockAccept", "hostOpen", "the connection has the listening socket's level and a public number; in the model the connections of a socket are one channel, its file of the empty name"),
    ("args_get", "ArgsGet", "hostGet", "public bytes from the run's configuration"),
    ("args_sizes_get", "ArgsSizesGet", "hostGet", "as `args_get`"),
    ("environ_get", "EnvironGet", "hostGet", "as `args_get`"),
    ("environ_sizes_get", "EnvironSizesGet", "hostGet", "as `args_get`"),
    ("clock_res_get", "ClockResGet", "hostGet", "a public constant"),
    ("clock_time_get", "ClockTimeGet", "hostGet", "the time, stored as public: a public input of the run"),
    ("random_get", "RandomGet", "hostGet", "random bytes, stored as public: a public input of the run"),
    ("fd_prestat_get", "FdPrestatGet", "hostGet", "the length of a granted directory's name, from the descriptor table"),
    ("fd_prestat_dir_name", "FdPrestatDirName", "hostGet", "a granted directory's name, from the descriptor table"),
    ("fd_fdstat_get", "FdFdstatGet", "hostGet", "the kind, the flags and the rights of a descriptor, from the descriptor table, stored as public (`pokeFdstat`)"),
    ("fd_close", "FdClose", "hostCtl", "removes a descriptor"),
    ("fd_renumber", "FdRenumber", "hostCtl", "moves a descriptor, with its level"),
    ("fd_fdstat_set_flags", "FdFdstatSetFlags", "hostCtl", "changes a descriptor's flags"),
    ("fd_fdstat_set_rights", "FdFdstatSetRights", "hostCtl", "narrows a descriptor's rights"),
    ("fd_seek", "FdSeek", "hostCtl", "moves the position; the new position is stored at the descriptor's level, as `fd_tell` stores it; a failure that the file's size or position decides traps on a secret file"),
    ("fd_advise", "FdAdvise", "hostCtl", "changes nothing"),
    ("fd_allocate", "FdAllocate", "hostCtl", "not supported: a status and nothing else"),
    ("fd_datasync", "FdDatasync", "hostCtl", "changes nothing that a program sees"),
    ("fd_sync", "FdSync", "hostCtl", "as `fd_datasync`"),
    ("fd_filestat_set_size", "FdFilestatSetSize", "hostCtl", "cuts or extends the file by an operand: what is left to read changes"),
    ("fd_filestat_set_times", "FdFilestatSetTimes", "hostCtl", "sets times that are operands"),
    ("path_create_directory", "PathCreateDirectory", "hostCtl", "adds a name to a directory"),
    ("path_filestat_set_times", "PathFilestatSetTimes", "hostCtl", "sets times that are operands"),
    ("path_link", "PathLink", "hostCtl", "adds a name; the two directories must have one level, or the run traps (`requireSameLevel`)"),
    ("path_remove_directory", "PathRemoveDirectory", "hostCtl", "removes a name"),
    ("path_rename", "PathRename", "hostCtl", "moves a name; the two directories must have one level, or the run traps (`requireSameLevel`)"),
    ("path_symlink", "PathSymlink", "hostCtl", "adds a name; the link's contents are a path and so public"),
    ("path_unlink_file", "PathUnlinkFile", "hostCtl", "removes a name"),
    ("sock_shutdown", "SockShutdown", "hostCtl", "closes a direction of a connection"),
    ("sched_yield", "SchedYield", "hostCtl", "changes nothing"),
    ("proc_raise", "ProcRaise", "hostCtl", "not supported: a status and nothing else"),
    ("poll_oneoff", "PollOneoff", "hostPoll", "the events and their number are stored at the join of the levels of the sockets polled (`pollOneoff`); the subscriptions are public"),
    ("proc_exit", "ProcExit", "none", "ends the run; the core has no rule for it, so a run that exits is as one that traps, and the theorem says nothing of it"),
]


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
# paper's appendix B ("The Rules of SecWasm+"), or the rule it is typed like, and what differs.
RULES = [
    ("nil", "`INil`, the end of a sequence", "T-Seq (SecWasm)", ""),
    ("const", "`IConst`", "T-Const (SecWasm)", ""),
    ("binop", "`IAdd` and the other operations on two values", "T-Binop (SecWasm)", "one rule for all of them"),
    ("unop", "the operations on one value, `IRefIsNull` among them", "T-Unop (SecWasm)", ""),
    ("partialBinop", "`IDiv`, `IRem`", "T-Binop (SecWasm)", "the operation is a partial function, and where it is not defined the instruction traps"),
    ("partialUnop", "`IConvert` with a truncation that traps", "T-Unop (SecWasm)", "as `partialBinop`"),
    ("dup", "`IDuplicate`", "none", "written by the elaborator for `br_on_null`"),
    ("select", "`ISelect`", "T-Select (SecWasm)", ""),
    ("drop", "`IDrop`", "T-Drop (SecWasm)", ""),
    ("nop", "`INop`", "T-Nop (SecWasm)", ""),
    ("relabel", "`IRelabelResults`", "T+-Relabel-Results", "raises labels of the block's whole segment"),
    ("localGet", "`ILocalGet`", "T-Get-Local (SecWasm)", ""),
    ("localSet", "`ILocalSet`", "T-Set-Local (SecWasm)", ""),
    ("localTee", "`ILocalTee`", "T-Tee-Local (SecWasm)", ""),
    ("globalGet", "`IGlobalGet`", "T-Get-Global (SecWasm)", ""),
    ("globalSet", "`IGlobalSet`", "T-Set-Global (SecWasm)", "for a global that is not preserved"),
    ("globalSetPreserved", "`IGlobalSetPreserved`", "T+-Set-Global-Preserved", "the same instruction, for a preserved global"),
    ("load", "`ILoad`, `ILoadN`", "T-Load (SecWasm)", "the level is the load's declaration; the check is in the semantics"),
    ("store", "`IStore`, `IStoreN`", "T-Store (SecWasm)", "the level is at least the join, where the implementation takes the join"),
    ("fill", "`IMemFill`", "T+-Memory-Fill", ""),
    ("copy", "`IMemCopy`", "T+-Memory-Copy", "within a memory or between two; the rule does not depend on which"),
    ("memInit", "`IMemInit`", "as T+-Memory-Copy", ""),
    ("dataDrop", "`IDataDrop`", "in the text: no premise", ""),
    ("memSize", "`IMemSize`", "T-Memory-Size (SecWasm)", ""),
    ("memGrow", "`IMemGrow`", "T-Memory-Grow (SecWasm)", ""),
    ("tableGet", "`ITableGet`", "T+-Table-Get", "the table is an index, and each table has a level"),
    ("tableSet", "`ITableSet`", "T+-Table-Set", ""),
    ("tableFill", "`ITableFill`", "as T+-Table-Set", "with the count"),
    ("tableInit", "`ITableInit`", "as T+-Table-Set", "with the count and the place in the element segment, which is public"),
    ("elemDrop", "`IElemDrop`", "none", "no premise, as `data.drop`"),
    ("tableCopy", "`ITableCopy`", "as T+-Table-Set", "between two tables: the level of the table copied from is in the premise too"),
    ("tableSize", "`ITableSize`", "T+-Table-Size", ""),
    ("tableGrow", "`ITableGrow`", "T+-Table-Grow", ""),
    ("hostRead", "a call of a host import that reads (`HostFunc`), with the driver's labelling", "T+-Call", "the paper types a call of a host import by its rule for calls; one instruction stands for the reading ones (section 8)"),
    ("hostWrite", "a call of a host import that writes, with the driver's check", "T+-Call", "one instruction stands for the writing ones"),
    ("hostGet", "a call of a host import that stores public data from no descriptor", "T+-Call", "the arguments, the environment, the clocks, random numbers"),
    ("hostCtl", "a call of a host import that changes the descriptor table, a directory or a position", "T+-Call", "`fd_close`, `fd_seek`, `path_rename` and the like"),
    ("hostPoll", "the host function `PollOneoff`", "T+-Call", "what it reports is at the join of the levels of the descriptors polled"),
    ("hostOpen", "the host function `PathOpen` (`Runtime.Host`), which is not an instruction", "T+-Call", "`path_open`"),
    ("block", "`IBlock`", "T+-Block", "with `Restores`, the comparison of preserved globals"),
    ("loop", "`ILoop`", "T+-Loop", "with `Restores`"),
    ("iter", "none: the iterations of a loop's body", "none", "no program contains it; the loop's rule types the body, and this one says the same of its iterations"),
    ("ite", "`IIf`", "T+-If", "with `Restores`"),
    ("br", "`IBr`", "T+-Br", ""),
    ("brIf", "`IBrIf`", "T+-Br-If", "not taken, the carried values keep their labels"),
    ("brTable", "`IBrTable`", "T+-Br-Table", "the repaired rule"),
    ("ret", "`IReturn`", "T+-Return", "the branch to the outermost label"),
    ("call", "`ICall`", "T+-Call", ""),
    ("retCall", "`IReturnCall`", "T+-Return-Call", ""),
    ("retCallIndirect", "`IReturnCallIndirect`", "T+-Call-Indirect with the premises of T+-Return-Call", ""),
    ("callIndirect", "`ICallIndirect`", "T+-Call-Indirect", "the table's level is in the premise"),
    ("callRef", "`ICallRef`", "T+-Call-Ref", ""),
    ("unreachable", "`IUnreachable`", "T+-Unreachable", ""),
    ("throw", "`IThrow`", "T+-Throw", "a tag is the number of public values it carries"),
    ("throwRef", "`IThrowRef`", "T+-Throw-Ref", "the reference is to an exception the state keeps"),
    ("tryTable", "`ITryTable`", "T+-Try-Table", ""),
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
    host_rows = "\n".join(
        f"| `{name}` | {wasi(rf'^    [(]{constructor},')} | {'`' + primitive + '`' if primitive != 'none' else 'none'} | {note} |" for name, constructor, primitive, note in HOST
    )
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
proofs, `Examples.lean` has small programs with their typings and runs, `Findings.lean`
and `SecWasmPrinted.lean` are the paper's findings (section 7), and `ValueTypes.lean` has the
judgment with value types (section 9). This file is
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
appendix B, "The Rules of SecWasm+": under the labels `Ls` (innermost first), the sequence `e` takes the pc
stack `P` and the current block's segment `st` to `P'` and `st'`. Each rule types one
instruction followed by the rest of its sequence, so SecWasm's T-Seq is built into every
rule. `Ctx` ({at("Defs", r"^structure Ctx")}) has the levels of the locals and the globals,
which globals are preserved, the function types, the level of each table and the tags.

Check each rule against the constructor of `Syntax.Instructions.Instr` and the paper's rule in
the table. The Lean rules are the lift-free ones: no rule raises the label of a value that was
on the stack before a branch.

| Lean rule | Line | Semantics (lines) | `Instr` constructor | Paper's rule | Note |
|---|---:|---|---|---|---|
{rule_rows}

The paper cites sixteen rules from SecWasm under their own names, T-Const and so on (Fig. 13
of SecWasm's full version): the column marks them "(SecWasm)". Its own rules are named
T+-Block and so on (its figures of rules in the appendix). Where the column says "as" a rule,
the paper prints no rule for the instruction and says in the text of the appendix that it
follows that one. The paper types a call of a
host import by T+-Call; the core's six host instructions stand for such calls (section 8), with the
host's part of the call in their rules.

Two side definitions carry premises:

- `Restores C pcEnd after keep` ({at("Defs", r"^def Restores")}): either the pc does not drop
  where the construct ends (`pcEnd` flows into the first pc of `after`), or `keep` has every
  preserved global. Convince yourself that this is `Validation.Shape.Restores`.
- `ClauseOk` ({at("Defs", r"^def ClauseOk")}): a clause of a `try_table` names a label whose
  type has as many values as its tag carries, or none for a clause that catches everything.

What the Lean rules leave out of the paper's: value types, and with them T+-Relabel, which
raises the label of one value (`relabel` here is T+-Relabel-Results, on the whole segment).
The premises that the paper prints in brackets are the witnesses of the Haskell constructors,
and each is a premise of the Lean rule.

`WellTyped C F` ({at("Defs", r"^def WellTyped")}) is the paper's rule for functions, for every
function of the module: its body is typed under the one label of the function, from an empty
segment, at the function's bound; and either it ends under a public pc or the function
compares every preserved global at its return (`Validation.Shape.ReturnsWith`). It does not
ask a function's results to be at least its bound (the premise of the paper's T+-Func that,
as the paper says, the types do not enforce); the rules for the indirect call and the
call through a reference ask that of the type they expect, which is where the proof uses it.

## 4. States and semantics

`State`, {at("Defs", r"^structure State")}: the locals, the globals, the memories as bytes with a
level each, the size and the limit of each memory, the tables, each with its size and limit, the element segments, the levels of the host's channels (a stream, a directory, a file), the descriptor table, the
names of the files in each directory, what
was written to each and what is left to read from each, the data segments, and the
exceptions kept for the references to them.

`Eval F n ls e σ s o`, {at("Defs", r"^inductive Eval")}: in the module `F`, with enclosing
labels of arities `ls`, the sequence `e` on the segment `σ` and the state `s` ends as `o`. `n`
is the size of the derivation and nothing else. An outcome (`Out`,
{at("Defs", r"^inductive Out")}) is the end of the sequence, a branch to an enclosing label
with the values it carries, or an exception that nothing in the sequence caught. A trap is the
absence of a rule, and so is a run that does not terminate. An operation that traps on some
operands (`partialBinop`, `partialUnop`) is a partial function, and its rule has the premise
that the function is defined there.

The paper's evaluation rules are named E+-Load and so on, and its figure `fig:eval` prints
five: E+-Load is `load` (line {evaluated["load"]}), E+-Br is `br` (line {evaluated["br"]}),
E+-Block is `blockCont` (line {evaluated["blockCont"]}), E+-Block-Exit is `blockExit` (line
{evaluated["blockExit"]}), and E+-Call is `call` (line {evaluated["call"]}). For every other
instruction, the rules are in the column "Semantics" of the table of section 3. The paper's
`lands`, `exits` and `kept` are `Out.lands` ({at("Defs", r"^def Out.lands")}), `Out.exits`
({at("Defs", r"^def Out.exits")}) and `Kept` ({at("Defs", r"^def Kept")}).

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

| The paper's clause | `LowEq` |
|---|---|
| (i) every global labelled public | the clause on `glob` |
| (ii) every byte labelled public in both states | the clause on `mem` and `lab`, for every memory |
| (iii) the size and the limit of the memory | `s.size = t.size`, `s.cap = t.cap`: the sizes and the limits of all memories, as functions of the memory's index |
| (iv) the table, if its label is public | `∀ x, C.table x = L → s.sameTable t x`: for every table, the entries, the size and the limit ({at("Defs", r"^def State.sameTable")}) |
| (v) the descriptors, the labels of the channels, and the names of the files in every directory | `s.chan = t.chan` and `s.sameHost t` ({at("Defs", r"^def State.sameHost")}): the descriptor table `fdt`, the names `names`, and `file`, which gives a file of a directory its channel |
| (vi) the output written to and the unread input of every public channel | the clause on `out` and `inp` |
| (vii) every data segment that neither state has dropped | the clause on `segs`, and the one on `elems` for the element segments |
| (viii) the exceptions held for references | `s.exns = t.exns` |

`LowEq` has two clauses that the paper's definition lacks:

- **The public local variables** (the first clause). These are the locals of whoever makes
  the call: the callee gets a frame made of its arguments, which the hypothesis
  `StkRel f.ty.params a0 a1` relates, and the final state has the caller's locals as they
  were. So the clause is assumed of the two initial states and holds of the final ones for
  that reason alone. It is there because the relation of the proof (`StRel`) has it, and the
  paper's definition can leave it out.
- **`ExnOk C s`**: every exception that the state keeps carries as many values as its tag
  says. It is a condition on one state and no agreement of two. A new instance keeps no
  exception, so it holds there.

In the other direction the paper's definition lacks nothing of substance, with two remarks.
Clauses (ii) and (iii) speak of "the memory", where the core has any number: read them for
each.
And clause (v) includes `file`, the function from a directory's channel and a name to the
file's channel, which the paper's wording covers as part of the descriptors' state.

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

### Where the statements differ from the paper's

The paper states its theorem for the calculus (`lem:swp-ni`) as `noninterference` is stated:
two `Invoke`s of one function from low-equivalent states. Its `ret(r, s')` is
`Ended.returned r s'` and its `exn_t(w, s')` is `Ended.threw t w s'`. The differences left:

- `refinement` is for every end of a run, by a return or by an exception; the paper's
  `lem:refinement` states the case of a return. `machine_noninterference` has the case of two
  runs that end by the same exception too, which the paper's `thm:tini` does not state.
- The paper's `thm:tini` is about the implementation: a typed program and `step`. Two links
  of it are outside Lean, by reading: that a value of the Haskell instruction type is a
  derivation of `Typed` (the table of section 3), and that `step` makes the transitions of
  `Step` (the table of section 6).
- `tini` in `Noninterference.lean` is `noninterference` in the terms of the proof (`StRel` and
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
core's host calls are instructions. Its typed instructions carry coercions between
segments (`relabelStack`), which do nothing to the values. And a clause by reference that
catches an exception thrown by `throw_ref` gets the reference it was thrown from, where the
Lean machine keeps the exception once more and hands out a new reference; WebAssembly has no
instruction that compares two references to exceptions.

## 7. The findings

`Findings.lean` has the three programs of the paper's findings (its figure `fig:examples`), and
`SecWasmPrinted.lean` has SecWasm's rules as printed for the five instructions of the first.

| Lean | Where | What it says |
|---|---|---|
| `leak` | {at("Findings", r"^def leak ")} | the program (a): four nested blocks, a `br_table` on the secret local with the targets 0 and 3, and a write to the public global after the third block. |
| `leak_not_typed` | {at("Findings", r"^theorem leak_not_typed")} | `Typed` has no derivation for it from a public pc, for any labels, segment and result. |
| `leak_runs_differ`, `leak_runs_globals` | {at("Findings", r"^theorem leak_runs_differ")} | `Eval` has a run that ends with 1 in the public global if the secret local is 0, and one that leaves the global if it is not. |
| `call_after_secret_branch_typed` | {at("Findings", r"^theorem call_after_secret_branch_typed")} | the program (b) is typed from a public pc. |
| `write_after_public_branch_typed` | {at("Findings", r"^theorem write_after_public_branch_typed")} | the program (c) is typed from a public pc. |
| `SecWasm.Typed` | {at("SecWasmPrinted", r"^inductive Typed")} | SecWasm's judgment on a stack of stacks, with T-Const, T-Get-Local, T-Set-Global, T-Block and T-Br-Table of the full version's Fig. 13, each composed with T-Seq. Check them against the figure. The parameter `lifted` is how many entries below the current one T-Br-Table lifts. |
| `SecWasm.printed`, `SecWasm.repaired` | {at("SecWasmPrinted", r"^def printed")} | the number of targets (as printed: the entries 0 to m - 1), and the deepest target (as T-Br-If lifts the entries 0 to i - 1). |
| `SecWasm.printed_rule_accepts_leak` | {at("SecWasmPrinted", r"^theorem printed_rule_accepts_leak")} | the printed rules type `leak` as a function body with a public bound. |
| `SecWasm.write_under_public_pc` | {at("SecWasmPrinted", r"^theorem write_under_public_pc")} | in any such typing the write to the global is under a public pc. |
| `SecWasm.repaired_rule_rejects_leak` | {at("SecWasmPrinted", r"^theorem repaired_rule_rejects_leak")} | with the lift down to the deepest target, `leak` has no typing. |
| `SecWasm.printed_rule_rejects_shallow_leak` | {at("SecWasmPrinted", r"^theorem printed_rule_rejects_shallow_leak")} | the printed rules do reject the same leak two blocks deep, where the lift reaches the write. |
| `SecWasm.printed_rule_unsound` | {at("SecWasmPrinted", r"^theorem printed_rule_unsound")} | the finding in one statement: typed by the printed rules, and two runs from states that differ in the secret local only end with different public globals. |

Three things to convince yourself of in `SecWasm.Typed`. The order `Below` is the full
version's Definition 14, entry by entry. A `br_table ts d` has the targets `ts` and then `d`,
so the `m` of the printed rule is `ts.length + 1`. And the code after a `br_table` is typed
from the rule's output, as T-Seq does, where `WasmIfc.Typed` does not type it. In `leak`
nothing follows the `br_table` in its block.

## 8. The host

The paper's one assumption about the host is that the status of a host call depends only on
its operands and on the public part of the state. In the core this is a definition and no
hypothesis: `hostStatus` ({at("Defs", r"^opaque hostStatus")}) is a function of the call, its
operands, the descriptor table, the names of the files in every directory, the channel of each
file, the levels of the channels and the size of the first memory, and of nothing else.
`State.status` applies it to a state. The proof uses the assumption in one lemma,
`StRel.status` ({at("Basic", r"^theorem StRel.status")}): two runs' states give a call with the
same operands the same status. Each host primitive has a rule for status 0, which does what the
call does, and one for any other status, which leaves the state as it was. Both push the status.
What a public pointer among the operands points to (a path, the subscriptions of a poll)
counts as an operand: the host checks those bytes to be public before it uses them.

There are six primitives, one for each shape of rule:

| Primitive | Rule | What it does on success |
|---|---|---|
| `hostRead` | line {evaluated["hostRead"]} | stores what it reads from a descriptor's channel, and how much, at the channel's level |
| `hostWrite` | line {evaluated["hostWrite"]} | sends cells to a descriptor's channel, and traps if one is more secret than the channel |
| `hostOpen` | line {evaluated["hostOpen"]} | makes a descriptor, with a public number, for a file of a directory; the name's bytes must be public |
| `hostGet` | line {evaluated["hostGet"]} | stores public data of a public source that has no descriptor |
| `hostCtl` | line {evaluated["hostCtl"]} | changes the descriptor table, the directories and the position of a descriptor, by functions of the operands and of what the table and the directories were (`State.control`, {at("Defs", r"^def State.control")}) |
| `hostPoll` | line {evaluated["hostPoll"]} | stores a report on several descriptors at the join of their channels' levels (`State.pollLevel`, {at("Defs", r"^def State.pollLevel")}); the report is a function of what those channels have left to read |

Each function of WASI Preview 1, with the case of `runWasiCall` ({wasi(r"^runWasiCall ::")})
that serves it:

| WASI function | Where | Shape | What in `Runtime.Wasi` makes it so |
|---|---|---|---|
{host_rows}

Convince yourself of three things that the table rests on:

- **A file has one level.** A file gets the level of the directory it is opened in
  (`openPath`, {wasi(r"^openPath ::")}). So a path must stay in its directory once symbolic
  links are followed (`confine`, {wasi(r"^confine ::")}), no call moves or links a file between
  directories of different levels (`requireSameLevel`, {wasi(r"^requireSameLevel ::")}), and
  the host refuses to start if a directory contains another of a different level
  (`newHost`, {wasi(r"^newHost ::")}). That the granted directories share no file by a hard
  link made outside the run is assumed.
- **What decides a public status is public.** Paths, the contents of a symbolic link and the
  subscriptions of a poll must be public bytes (`peekPath`, `requireAtMost`). The list of
  buffers of a read or a write may be as secret as the descriptor, and then a failure of the
  call traps and is no status (`usingBuffers`, {wasi(r"^usingBuffers ::")}). Whether a name exists in a directory and what
  kind of entry it is decide the status of the `path_` calls, in a secret directory too: the
  model has the names in `sameHost`, as public. A read from a secret socket that does not
  block, and a seek on a secret file that would land before its start, trap in place of a
  status (`unlessWouldBlock`, the case of `FdSeek`).
- **What the model leaves out.** A failure of the operating system on a secret file or
  connection (a full disk, a connection that the peer closed) is a status that the model does
  not have. `proc_exit` has no rule. `hostWrite` does not store how much it wrote, which the
  host stores at the descriptor's level. `fd_seek` is a `hostCtl` that also stores the new
  position, as `fd_tell` would.

## 9. Value types

`Typed` has one type for all values. `ValueTypes.lean` has the judgment with labelled value
types, the paper's `t⟨ℓ⟩`, over the same instructions and the same semantics:

| Lean | Where | Convince yourself that |
|---|---|---|
| `VTy`, `LTy`, `VSTy` | {at("ValueTypes", r"^inductive VTy")} | the value types are WebAssembly's numbers, vectors and references to functions and to exceptions, and a stack type is a list of pairs of a value type and a level. `labelsOf` forgets the types. |
| `VCtx` | {at("ValueTypes", r"^structure VCtx")} | the context has the labelled types of the locals and the globals, the types that each tag carries, and an address type for each memory and each table (`i32`, or `i64` for a 64-bit one). `VCtx.erase` is the `Ctx` of section 3. |
| `ValueTyped` | {at("ValueTypes", r"^inductive ValueTyped")} | each rule is the rule of `Typed` of the same name with the types that `Syntax.Instructions` gives the instruction: an address has its memory's or its table's address type, a condition and the operands of a host call are `i32`, a table holds references to functions, the operands of an operation on two values have one type. A block type in an instruction is the labels of the block's types. |
| `ValueTyped.erase` | {at("ValueTypes", r"^theorem ValueTyped.erase")} | a derivation with value types is, with the types forgotten, a derivation of `Typed`. |
| `WellValueTyped`, `WellValueTyped.erase` | {at("ValueTypes", r"^def WellValueTyped")} | a module whose functions are typed with value types is well typed in the sense of section 3. |
| `value_typed_noninterference`, `value_typed_machine_noninterference` | {at("ValueTypes", r"^theorem value_typed_noninterference")} | the two theorems for such a module: `noninterference` and `machine_noninterference` with the function's type and the context read through `labelsOf` and `VCtx.erase`. |

The semantics does not look at types: a value is a number whatever its type, and an operation
is a function on numbers. So the theorems with value types follow from the ones without, by
`ValueTyped.erase`, and no proof was done again. What the layer adds to the statement is that
the hypothesis is about programs typed as WebAssembly types them, with 64-bit memories and
tables among them. What it does not model: that a value of a type is within that type's range
(an `i32` below 2^32), and so the wrapping of an address.

### Outside the core

The numeric and vector instructions one by one (an operation is any function on numbers, of
one or two operands, total or partial); the ranges of the value types;
linking; `proc_exit`, and the failures of the operating system on a secret file or connection
(section 8); local variables split into webs and the inference of labels, which
happen before typing; declassification.
"""
    (HERE / "STATEMENTS.md").write_text(text)
    print(f"wrote lean/STATEMENTS.md ({len(text.splitlines())} lines)")


if __name__ == "__main__":
    main()
