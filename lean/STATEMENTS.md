# Reading the Lean development: what to check

For a reviewer who checks the definitions and the statement and leaves the proofs to Lean.
`lake build` checks every proof, and `#print axioms WasmIfc.machine_noninterference` lists
`propext`, `Classical.choice` and `Quot.sound` only. So what remains to be checked by a person
is that the definitions say what the paper says, and that the machine of the last section is
the implementation's. They are in three files, 1086, 120
and 587 lines long, of the development's 6,134:

- `WasmIfc/Defs.lean`: the syntax, the typing judgment, the states and the semantics.
- `WasmIfc/Statement.lean`: low equivalence, a call from outside, and the theorem.
- `WasmIfc/Machine.lean`: the small-step machine, down to `Config.entry`
  (`Machine.lean:280`), and the two theorems at its end. What is between
  is proof.

The other files (`Basic.lean`, `Confinement.lean`, `Noninterference.lean`) are lemmas and
proofs, `Examples.lean` has small programs with their typings and runs, and `Findings.lean`
and `SecWasmPrinted.lean` are the paper's findings (section 7). This file is
written by `lean/guide.py`, which looks the line numbers up.

## 1. Levels and types

| What | Where | Convince yourself that |
|---|---|---|
| `Lab`, `Lab.le`, `Lab.join` | `Defs.lean:21` | there are two levels, `L` flows into both, `H` only into `H`, and `join` is the least upper bound. |
| `STy`, `Pcs` | `Defs.lean:39` | a type stack and a pc stack are lists of levels, the top or the innermost block first. All values have one type, so a labelled type is its label. |
| `SFlows`, `AllGe` | `Defs.lean:45` | `SFlows s t` is the paper's `st ⊑ st'` on stacks of one length, and `AllGe a st` says the level `a` flows into every label of `st`. |
| `raise`, `joinEach` | `Defs.lean:53` | `raise a P i` joins `a` into the entries 0 to `i` of a pc stack (what a branch to label `i` does), and `joinEach` joins two pc stacks entry by entry (where the two arms of a conditional meet). |

## 2. Syntax

`Instr`, `Defs.lean:64`. Check that each constructor is the instruction its
comment names. Three things are not WebAssembly's syntax:

- A block type is two type stacks, the parameters and the results with their levels, where a
  binary has value types only. The elaborator chooses them.
- A block, a loop, a conditional and a `try_table` carry `keep`, the globals they compare
  where control comes out of them. In the implementation this is a witness of the typed
  instruction (`Restores`), and the compared globals are all the preserved ones.
- `iter` is not an instruction of any program (section 4 below).

`Func` (`Defs.lean:165`) is a function: its type, the levels of its other
locals, the globals compared at its return, and its body. `FuncTy`
(`Defs.lean:165`) is the paper's labelled function type: parameters, the
bound on the pc of its callers, results.

## 3. The typing judgment

`Typed C Ls e P st P' st'`, `Defs.lean:211`, is the paper's judgment of
appendix B, "The Rules of SecWasm+": under the labels `Ls` (innermost first), the sequence `e` takes the pc
stack `P` and the current block's segment `st` to `P'` and `st'`. Each rule types one
instruction followed by the rest of its sequence, so the paper's T+-Seq is built into every
rule. `Ctx` (`Defs.lean:174`) has the levels of the locals and the globals,
which globals are preserved, the function types, the level of each table and the tags.

Check each rule against the constructor of `Syntax.Instructions.Instr` and the paper's rule in
the table. The Lean rules are the lift-free ones: no rule raises the label of a value that was
on the stack before a branch.

| Lean rule | Line | Semantics (lines) | `Instr` constructor | Paper's rule | Note |
|---|---:|---|---|---|---|
| `nil` | 212 | 815 | `INil`, the end of a sequence | T+-Seq |  |
| `const` | 213 | 816 | `IConst` | T+-Const |  |
| `binop` | 216 | 818 | `IAdd` and the other operations on two values | T+-Binop | one rule for all of them |
| `unop` | 219 | 820 | the operations on one value, `IRefIsNull` among them | as T+-Binop |  |
| `partialBinop` | 223 | 822 | `IDiv`, `IRem` | T+-Binop | the operation is a partial function, and where it is not defined the instruction traps |
| `partialUnop` | 226 | 825 | `IConvert` with a truncation that traps | as T+-Binop | as `partialBinop` |
| `dup` | 229 | 828 | `IDuplicate` | none | written by the elaborator for `br_on_null` |
| `select` | 232 | 830 | `ISelect` | T+-Select |  |
| `drop` | 235 | 833 | `IDrop` | T+-Drop |  |
| `nop` | 238 | 835 | `INop` | T+-Nop |  |
| `relabel` | 241 | 837 | `IRelabelResults` | T+-Relabel-Results | raises labels of the block's whole segment |
| `localGet` | 245 | 839 | `ILocalGet` | T+-Get-Local |  |
| `localSet` | 248 | 841 | `ILocalSet` | T+-Set-Local |  |
| `localTee` | 252 | 843 | `ILocalTee` | as T+-Set-Local |  |
| `globalGet` | 256 | 846 | `IGlobalGet` | as T+-Get-Local |  |
| `globalSet` | 259 | 848 | `IGlobalSet` | T+-Set-Global | for a global that is not preserved |
| `globalSetPreserved` | 267 | 848 | `IGlobalSetPreserved` | T+-Set-Global-Preserved | the same instruction, for a preserved global |
| `load` | 271 | 850 | `ILoad`, `ILoadN` | T+-Load | the level is the load's declaration; the check is in the semantics |
| `store` | 274 | 853 | `IStore`, `IStoreN` | T+-Store | the level is at least the join, where the implementation takes the join |
| `fill` | 279 | 857 | `IMemFill` | T+-Memory-Fill |  |
| `copy` | 288 | 861 | `IMemCopy` | T+-Memory-Copy | within a memory or between two; the rule does not depend on which |
| `memInit` | 323 | 913 | `IMemInit` | as T+-Memory-Copy |  |
| `dataDrop` | 328 | 917 | `IDataDrop` | in the text: no premise |  |
| `memSize` | 363 | 939 | `IMemSize` | as T+-Const |  |
| `memGrow` | 367 | 941 | `IMemGrow` | T+-Memory-Grow |  |
| `tableGet` | 293 | 865 | `ITableGet` | T+-Table-Get | the table is an index, and each table has a level |
| `tableSet` | 297 | 869 | `ITableSet` | T+-Table-Set |  |
| `tableFill` | 332 | 919 | `ITableFill` | as T+-Table-Set | with the count |
| `tableInit` | 354 | 933 | `ITableInit` | as T+-Table-Set | with the count and the place in the element segment, which is public |
| `elemDrop` | 359 | 937 | `IElemDrop` | none | no premise, as `data.drop` |
| `tableCopy` | 340 | 923 | `ITableCopy` | as T+-Table-Set | between two tables: the level of the table copied from is in the premise too |
| `tableSize` | 345 | 927 | `ITableSize` | T+-Table-Size |  |
| `tableGrow` | 349 | 929 | `ITableGrow` | T+-Table-Grow |  |
| `hostRead` | 306 | 878 | a call of a host import that reads (`HostFunc`), with the driver's labelling | T+-Call | the paper types a call of a host import by its rule for calls; one instruction stands for the reading ones |
| `hostWrite` | 310 | 888 | a call of a host import that writes, with the driver's check | T+-Call | one instruction stands for the writing ones |
| `hostOpen` | 318 | 899, 906 | the host function `PathOpen` (`Runtime.Host`), which is not an instruction | T+-Call | `path_open` |
| `block` | 372 | 944, 949 | `IBlock` | T+-Block | with `Restores`, the comparison of preserved globals |
| `loop` | 378 | 953, 959 | `ILoop` | T+-Loop | with `Restores` |
| `iter` | 388 | 964, 968, 973, 976, 979 | none: the iterations of a loop's body | none | no program contains it; the loop's rule types the body, and this one says the same of its iterations |
| `ite` | 392 | 982, 988 | `IIf` | T+-If | with `Restores` |
| `br` | 398 | 992 | `IBr` | T+-Br |  |
| `brIf` | 402 | 994, 996 | `IBrIf` | T+-Br-If | not taken, the carried values keep their labels |
| `brTable` | 407 | 998 | `IBrTable` | T+-Br-Table | the repaired rule |
| `ret` | 412 | 1001 | `IReturn` | T+-Return | the branch to the outermost label |
| `call` | 417 | 1005, 1044 | `ICall` | T+-Call |  |
| `retCall` | 426 | 1019, 1025 | `IReturnCall` | T+-Return-Call |  |
| `retCallIndirect` | 441 | 1030, 1037 | `IReturnCallIndirect` | T+-Call-Indirect with the premises of T+-Return-Call |  |
| `callIndirect` | 436 | 1011, 1049 | `ICallIndirect` | T+-Call-Indirect | the table's level is in the premise |
| `callRef` | 450 | 1057, 1064 | `ICallRef` | T+-Call-Ref |  |
| `unreachable` | 454 | none: a trap | `IUnreachable` | T+-Unreachable |  |
| `throw` | 457 | 1071 | `IThrow` | T+-Throw | a tag is the number of public values it carries |
| `throwRef` | 461 | 1073 | `IThrowRef` | T+-Throw-Ref | the reference is to an exception the state keeps |
| `tryTable` | 467 | 1075, 1081 | `ITryTable` | T+-Try-Table |  |

The paper's rules are named T+-Block and so on (its figures `fig:wrules`, `fig:wrules2` and
`fig:wrules3`). Where the column says "as" a rule, the paper prints no rule for the instruction
and says in the text of the appendix that it follows that one. The paper types a call of a
host import by T+-Call; the core's three host instructions stand for such calls, with the
host's part of the call in their rules.

Two side definitions carry premises:

- `Restores C pcEnd after keep` (`Defs.lean:202`): either the pc does not drop
  where the construct ends (`pcEnd` flows into the first pc of `after`), or `keep` has every
  preserved global. Convince yourself that this is `Validation.Shape.Restores`.
- `ClauseOk` (`Defs.lean:189`): a clause of a `try_table` names a label whose
  type has as many values as its tag carries, or none for a clause that catches everything.

What the Lean rules leave out of the paper's: value types, and with them T+-Relabel, which
raises the label of one value (`relabel` here is T+-Relabel-Results, on the whole segment).
The premises that the paper prints in brackets are the witnesses of the Haskell constructors,
and each is a premise of the Lean rule.

`WellTyped C F` (`Defs.lean:500`) is the paper's rule for functions, for every
function of the module: its body is typed under the one label of the function, from an empty
segment, at the function's bound; and either it ends under a public pc or the function
compares every preserved global at its return (`Validation.Shape.ReturnsWith`). It does not
ask a function's results to be at least its bound (the premise of the paper's T+-Func that,
as the paper says, the types do not enforce); the rules for the indirect call and the
call through a reference ask that of the type they expect, which is where the proof uses it.

## 4. States and semantics

`State`, `Defs.lean:510`: the locals, the globals, the memories as bytes with a
level each, the size and the limit of each memory, the tables, each with its size and limit, the element segments, the levels of the host's channels (a stream, a directory, a file), the descriptor table, the
names of the files in each directory, what
was written to each and what is left to read from each, the data segments, and the
exceptions kept for the references to them.

`Eval F n ls e σ s o`, `Defs.lean:814`: in the module `F`, with enclosing
labels of arities `ls`, the sequence `e` on the segment `σ` and the state `s` ends as `o`. `n`
is the size of the derivation and nothing else. An outcome (`Out`,
`Defs.lean:707`) is the end of the sequence, a branch to an enclosing label
with the values it carries, or an exception that nothing in the sequence caught. A trap is the
absence of a rule, and so is a run that does not terminate. An operation that traps on some
operands (`partialBinop`, `partialUnop`) is a partial function, and its rule has the premise
that the function is defined there.

The paper's evaluation rules are named E+-Load and so on, and its figure `fig:eval` prints
five: E+-Load is `load` (line 850), E+-Br is `br` (line 992),
E+-Block is `blockCont` (line 944), E+-Block-Exit is `blockExit` (line
949), and E+-Call is `call` (line 1005). For every other
instruction, the rules are in the column "Semantics" of the table of section 3. The paper's
`lands`, `exits` and `kept` are `Out.lands` (`Defs.lean:737`), `Out.exits`
(`Defs.lean:745`) and `Kept` (`Defs.lean:700`).

Convince yourself of six things, which are where this semantics is not the specification's
text:

1. **A block's body runs on the block's parameters alone** (`blockCont`,
   line 944), and what is below them on the stack waits. On validated code
   this is what WebAssembly does, since a body cannot reach below its parameters. That the two
   agree is not proved.
2. **The run-time checks are premises.** A load goes on only if every byte it reads is within
   the memory and its level flows into the load's declared level (line 850).
   An instruction on the table goes on only if the entries it names are within the table.
   An indirect call goes on only if the entry names a function with the expected parameters
   and results whose bound is at least the expected one (line 1011).
   A host write goes on only if every byte it takes flows into the level of the descriptor's
   channel (line 888), and a file is opened only if every byte of its
   name is public (line 899). These are the paper's hybrid checks.
3. **The comparison of preserved globals is a premise too** (`Kept`,
   `Defs.lean:700`): where control comes out of a block, a loop, a conditional or a
   `try_table` by its end or by a branch to its label, and where a call returns, the globals
   in `keep` hold what they held at the construct's start or at the call. A branch further
   out and an exception skip it.
4. **A loop runs `iter`** (lines 953 to 976): the body
   again while it branches to the loop's label. The loop's comparison is therefore with the
   state at its first entry, as in the implementation.
5. **A call** (line 1005) runs the callee's body on an empty segment with a
   frame made of the arguments, and gives the caller its own locals back. `return` and a
   branch to the function's label end the callee alike (`Out.lands`).
6. **A tail call** (line 1019) is written as a call whose results the
   function returns. The function is gone when its callee runs, so an exception that leaves
   the callee is not offered to the function's own `try_table`s: it is the outcome `tailExn`,
   which every block passes (`Out.caught`, `Out.exits`) and which is an exception again for
   the function's caller (`Out.thrown`, in the rules `callExn` and `retCallExn`).

## 5. Low equivalence and the theorem

`LowEq C s t`, `Statement.lean:21`, is the paper's low equivalence
(`def:attacker`). Clause by clause:

| The paper's clause | `LowEq` |
|---|---|
| (i) every global labelled public | the clause on `glob` |
| (ii) every byte labelled public in both states | the clause on `mem` and `lab`, for every memory |
| (iii) the size and the limit of the memory | `s.size = t.size`, `s.cap = t.cap`: the sizes and the limits of all memories, as functions of the memory's index |
| (iv) the table, if its label is public | `∀ x, C.table x = L → s.sameTable t x`: for every table, the entries, the size and the limit (`Defs.lean:544`) |
| (v) the descriptors, the labels of the channels, and the names of the files in every directory | `s.chan = t.chan` and `s.sameHost t` (`Defs.lean:555`): the descriptor table `fdt`, the names `names`, and `file`, which gives a file of a directory its channel |
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

`Invoke F f a s e`, `Statement.lean:61`: the function `f` called from
outside on the arguments `a` in the state `s` ends as `e`, by returning results or by an
exception. Convince yourself that it is `Eval` of the body as rule `call` runs it, the
comparison of the function's `keep` included, which the machine makes for the invoked function
as for a callee.

`noninterference`, `Statement.lean:79`:

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
`step` (`Interpreter.hs:404`), and proves that `Eval` describes it.

`Step F c nx`, `Machine.lean:191`: one transition, from the configuration
`c` to the next one or to the end of the run. `Runs F c e`,
`Machine.lean:271`: the transitions from `c` to the end `e`. A run that traps
or does not end has no `Runs`.

| Lean | Where | Haskell | Where | Convince yourself that |
|---|---|---|---|---|
| `Config`: `s`, `σ`, `e`, `K` | `Machine.lean:40` | `Config store locals stack code control` | `Interpreter.hs:311` | the fields are the same; the Lean state has the local variables in it (`s.loc`). |
| `Frame.label` | `Machine.lean:32` | `BlockLabel below cont rest`, `HandlerLabel handlers below cont rest` | `Interpreter.hs:270` | a label has the operands below its block and the code after it; a block's label is one with no clauses. `keep` and `recorded` are the `IRequireRestored recorded` that the Haskell puts in front of `cont` (`Interpreter.hs:852`). |
| `Frame.loop` | `Machine.lean:34` | `LoopLabel below body cont rest` | `Interpreter.hs:288` | it has the body besides. |
| `Frame.call` | `Machine.lean:36` | `CallBoundary depth below callerLocals cont callerControl` | `Interpreter.hs:299` | it has the caller's locals. `checks` is the comparisons in front of `cont`: one for a call (`Interpreter.hs:843`), and one more for each tail call made in the callee's place. The Lean machine has no bound on the depth of calls. |
| the empty control stack; `Config.entry` | `Machine.lean:280` | `EntryBoundary`; `startFunction` | `Interpreter.hs:1331` | a call from outside runs the body over a boundary of its own that has the function's comparison. |
| `Basic`, `Step.basic` | `Machine.lean:70` | the clauses of `stepInstr` that end in `stepped` | `Interpreter.hs:417` | each instruction that is not one of control does to the operands and the state what its `Eval` rule says (section 4), and traps where the rule has a premise that fails. |
| `Step.block`, `tryTable`, `loop`, `ite` | `Machine.lean:194` | the clauses for `IBlock`, `ITryTable`, `ILoop`, `IIf` | | the body runs on the construct's parameters over a new label. |
| `Step.endLabel`, `endLoop`, `endCall`, `done` | `Machine.lean:223` | `popControl` | `Interpreter.hs:1040` | at the end of the current block the top of the control stack says what follows, behind its comparisons. |
| `Unwind`, in `Step.br`, `brIf`, `brTable`, `ret` | `Machine.lean:151` | `unwind`, `unwindTo`, `returnUnwind` | `Interpreter.hs:1062` | a branch drops the labels it passes without their comparisons; a loop's label stays and its body runs again; the function's label is its boundary. |
| `Step.call`, `callIndirect`, `callRef` | `Machine.lean:234` | `enterCall` | `Interpreter.hs:745` | the callee's body runs on no operands with locals made of the arguments, over a boundary. The checks of an indirect call are premises, as in `Eval`. |
| `boundary`, in `Step.retCall`, `retCallIndirect` | `Machine.lean:59` | `tailCall` | `Interpreter.hs:1118` | the labels of the running function are dropped, its clauses with them, and the callee is entered over the function's own boundary, which gets the callee's comparison too. |
| `Raise`, in `Step.throw` | `Machine.lean:172` | `throwException` | `Interpreter.hs:1168` | an exception passes labels without a clause for it and call boundaries, where the caller's locals are back; the first clause for it is a branch from around the clause's block; below the last boundary it ends the run. |

`refinement`, `Machine.lean:555`: a run of the machine from
`Config.entry f a s` to an end `e` is `Invoke F f a s e`. No typing is assumed. This is the
paper's `lem:refinement`, in the direction the theorem needs.

`machine_noninterference`, `Machine.lean:577`: the statement
of `noninterference` with two runs of the machine for the two `Invoke`s.

What stays by reading is the table above: that the Haskell `step` makes the transitions of
`Step`. Four differences are known. The Haskell machine bounds the depth of calls and traps
beyond it. It suspends at a call of the host and is resumed with the results, where the
core's two host calls are instructions. Its typed instructions carry coercions between
segments (`relabelStack`), which do nothing to the values. And a clause by reference that
catches an exception thrown by `throw_ref` gets the reference it was thrown from, where the
Lean machine keeps the exception once more and hands out a new reference; WebAssembly has no
instruction that compares two references to exceptions.

## 7. The findings

`Findings.lean` has the three programs of the paper's findings (its figure `fig:examples`), and
`SecWasmPrinted.lean` has SecWasm's rules as printed for the five instructions of the first.

| Lean | Where | What it says |
|---|---|---|
| `leak` | `Findings.lean:29` | the program (a): four nested blocks, a `br_table` on the secret local with the targets 0 and 3, and a write to the public global after the third block. |
| `leak_not_typed` | `Findings.lean:70` | `Typed` has no derivation for it from a public pc, for any labels, segment and result. |
| `leak_runs_differ`, `leak_runs_globals` | `Findings.lean:109` | `Eval` has a run that ends with 1 in the public global if the secret local is 0, and one that leaves the global if it is not. |
| `call_after_secret_branch_typed` | `Findings.lean:164` | the program (b) is typed from a public pc. |
| `write_after_public_branch_typed` | `Findings.lean:196` | the program (c) is typed from a public pc. |
| `SecWasm.Typed` | `SecWasmPrinted.lean:47` | SecWasm's judgment on a stack of stacks, with T-Const, T-Get-Local, T-Set-Global, T-Block and T-Br-Table of the full version's Fig. 13, each composed with T-Seq. Check them against the figure. The parameter `lifted` is how many entries below the current one T-Br-Table lifts. |
| `SecWasm.printed`, `SecWasm.repaired` | `SecWasmPrinted.lean:89` | the number of targets (as printed: the entries 0 to m - 1), and the deepest target (as T-Br-If lifts the entries 0 to i - 1). |
| `SecWasm.printed_rule_accepts_leak` | `SecWasmPrinted.lean:99` | the printed rules type `leak` as a function body with a public bound. |
| `SecWasm.write_under_public_pc` | `SecWasmPrinted.lean:115` | in any such typing the write to the global is under a public pc. |
| `SecWasm.repaired_rule_rejects_leak` | `SecWasmPrinted.lean:128` | with the lift down to the deepest target, `leak` has no typing. |
| `SecWasm.printed_rule_rejects_shallow_leak` | `SecWasmPrinted.lean:182` | the printed rules do reject the same leak two blocks deep, where the lift reaches the write. |
| `SecWasm.printed_rule_unsound` | `SecWasmPrinted.lean:213` | the finding in one statement: typed by the printed rules, and two runs from states that differ in the secret local only end with different public globals. |

Three things to convince yourself of in `SecWasm.Typed`. The order `Below` is the full
version's Definition 14, entry by entry. A `br_table ts d` has the targets `ts` and then `d`,
so the `m` of the printed rule is `ts.length + 1`. And the code after a `br_table` is typed
from the rule's output, as T-Seq does, where `WasmIfc.Typed` does not type it. In `leak`
nothing follows the `br_table` in its block.

### Outside the core

More than one value type, and so the numeric and vector instructions as such (the operations
that trap are in the core, as partial functions); 64-bit
memories and tables;
linking; the WASI calls other than one that reads, one that writes and one that opens a file
in a directory, the error codes but the one for a missing file, and sockets; local variables split into webs and the inference of labels, which
happen before typing; declassification.
