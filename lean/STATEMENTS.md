# Reading the Lean development: what to check

For a reviewer who checks the definitions and the statement and leaves the proofs to Lean.
`lake build` checks every proof, and `#print axioms WasmIfc.machine_noninterference` lists
`propext`, `Classical.choice` and `Quot.sound` only. So what remains to be checked by a person
is that the definitions say what the paper says, and that the machine of the last section is
the implementation's. They are in four files, 1218, 120,
630 and 577 lines long, of the development's 7,099:

- `WasmIfc/Defs.lean`: the syntax, the label part of the typing judgment, the states and the
  semantics.
- `WasmIfc/Statement.lean`: low equivalence, a call from outside, and the theorem on labels.
- `WasmIfc/Machine.lean`: the small-step machine, down to `Config.entry`
  (`Machine.lean:313`), and the two theorems at its end. What is between
  is proof.
- `WasmIfc/ValueTypes.lean`: the paper's judgment, with labelled value types, and the theorems
  under the paper's names.

**The names.** The names that the paper cites for the judgment and the theorems, `Typed`,
`WellTyped`, `rise`, `noninterference` and `machine_noninterference`, are those of the judgment
with labelled value types `t⟨ℓ⟩` and of its theorems, in `ValueTypes.lean` (section 9). The
proofs are about the label part of that judgment, which forgets the value types: `LTyped`,
`WellLTyped`, and the theorems with the suffix `_labels`. Sections 3 to 6 are about the label
part, which is where the rules and the proof are, and section 9 says how the two meet. The
lemmas of the proof that the paper names, `confine`, `ni` and `tini`, are about the label part.

The other files (`Basic.lean`, `Confinement.lean`, `Noninterference.lean`) are lemmas and
proofs, `Examples.lean` has small programs with their typings and runs, `Findings.lean`
and `SecWasmPrinted.lean` are the paper's findings (section 7), and `ValueTypes.lean` has the
judgment with value types (section 9). This file is
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

`Func` (`Defs.lean:171`) is a function: its type, the levels of its other
locals, the globals compared at its return, and its body. `FuncTy`
(`Defs.lean:171`) is the paper's labelled function type: parameters, the
bound on the pc of its callers, results.

## 3. The typing judgment

`LTyped C Ls e P st P' st'`, `Defs.lean:217`, is the label part of the
paper's judgment of appendix B, "The Rules of SecWasm+" (the judgment with value types is
`Typed`, section 9): under the labels `Ls` (innermost first), the sequence `e` takes the pc
stack `P` and the current block's segment `st` to `P'` and `st'`. Each rule types one
instruction followed by the rest of its sequence, so SecWasm's T-Seq is built into every
rule. `Ctx` (`Defs.lean:180`) has the levels of the locals and the globals,
which globals are preserved, the function types, the level of each table and the tags.

Check each rule against the constructor of `Syntax.Instructions.Instr` and the paper's rule in
the table. The Lean rules are the lift-free ones: no rule raises the label of a value that was
on the stack before a branch.

| Lean rule | Line | Semantics (lines) | `Instr` constructor | Paper's rule | Note |
|---|---:|---|---|---|---|
| `nil` | 218 | 890 | `INil`, the end of a sequence | T-Seq (SecWasm) |  |
| `const` | 219 | 891 | `IConst` | T-Const (SecWasm) |  |
| `binop` | 222 | 893 | `IAdd` and the other operations on two values | T-Binop (SecWasm) | one rule for all of them |
| `unop` | 225 | 895 | the operations on one value, `IRefIsNull` among them | T-Unop (SecWasm) |  |
| `partialBinop` | 229 | 897 | `IDiv`, `IRem` | T-Binop (SecWasm) | the operation is a partial function, and where it is not defined the instruction traps |
| `partialUnop` | 232 | 900 | `IConvert` with a truncation that traps | T-Unop (SecWasm) | as `partialBinop` |
| `dup` | 235 | 903 | `IDuplicate` | none | written by the elaborator for `br_on_null` |
| `select` | 238 | 905 | `ISelect` | T-Select (SecWasm) |  |
| `drop` | 241 | 908 | `IDrop` | T-Drop (SecWasm) |  |
| `nop` | 244 | 910 | `INop` | T-Nop (SecWasm) |  |
| `relabel` | 247 | 912 | `IRelabelResults` | T+-Relabel-Results | raises labels of the block's whole segment |
| `localGet` | 251 | 914 | `ILocalGet` | T-Get-Local (SecWasm) |  |
| `localSet` | 254 | 916 | `ILocalSet` | T-Set-Local (SecWasm) |  |
| `localTee` | 258 | 918 | `ILocalTee` | T-Tee-Local (SecWasm) |  |
| `globalGet` | 262 | 921 | `IGlobalGet` | T-Get-Global (SecWasm) |  |
| `globalSet` | 265 | 923 | `IGlobalSet` | T-Set-Global (SecWasm) | for a global that is not preserved |
| `globalSetPreserved` | 273 | 923 | `IGlobalSetPreserved` | T+-Set-Global-Preserved | the same instruction, for a preserved global |
| `load` | 277 | 925 | `ILoad`, `ILoadN` | T-Load (SecWasm) | the level is the load's declaration; the check is in the semantics |
| `store` | 280 | 928 | `IStore`, `IStoreN` | T-Store (SecWasm) | the level is at least the join, where the implementation takes the join |
| `fill` | 285 | 932 | `IMemFill` | T+-Memory-Fill |  |
| `copy` | 294 | 936 | `IMemCopy` | T+-Memory-Copy | within a memory or between two; the rule does not depend on which |
| `memInit` | 339 | 1045 | `IMemInit` | as T+-Memory-Copy |  |
| `dataDrop` | 344 | 1049 | `IDataDrop` | in the text: no premise |  |
| `memSize` | 379 | 1071 | `IMemSize` | T-Memory-Size (SecWasm) |  |
| `memGrow` | 383 | 1073 | `IMemGrow` | T-Memory-Grow (SecWasm) |  |
| `tableGet` | 299 | 940 | `ITableGet` | T+-Table-Get | the table is an index, and each table has a level |
| `tableSet` | 303 | 944 | `ITableSet` | T+-Table-Set |  |
| `tableFill` | 348 | 1051 | `ITableFill` | as T+-Table-Set | with the count |
| `tableInit` | 370 | 1065 | `ITableInit` | as T+-Table-Set | with the count and the place in the element segment, which is public |
| `elemDrop` | 375 | 1069 | `IElemDrop` | none | no premise, as `data.drop` |
| `tableCopy` | 356 | 1055 | `ITableCopy` | as T+-Table-Set | between two tables: the level of the table copied from is in the premise too |
| `tableSize` | 361 | 1059 | `ITableSize` | T+-Table-Size |  |
| `tableGrow` | 365 | 1061 | `ITableGrow` | T+-Table-Grow |  |
| `hostRead` | 312 | 953, 961 | a call of a host import that reads (`HostFunc`), with the driver's labelling | T+-Call | the paper types a call of a host import by its rule for calls; one instruction stands for the reading ones (section 8) |
| `hostWrite` | 316 | 969, 975 | a call of a host import that writes, with the driver's check | T+-Call | one instruction stands for the writing ones |
| `hostGet` | 320 | 984, 991 | a call of a host import that stores public data from no descriptor | T+-Call | the arguments, the environment, the clocks, random numbers |
| `hostCtl` | 323 | 999, 1003 | a call of a host import that changes the descriptor table, a directory or a position | T+-Call | `fd_close`, `fd_seek`, `path_rename` and the like |
| `hostPoll` | 326 | 1013, 1021 | the host function `PollOneoff` | T+-Call | what it reports is at the join of the levels of the descriptors polled |
| `hostOpen` | 334 | 1031, 1038 | the host function `PathOpen` (`Runtime.Host`), which is not an instruction | T+-Call | `path_open` |
| `block` | 388 | 1076, 1081 | `IBlock` | T+-Block | with `Restores`, the comparison of preserved globals |
| `loop` | 394 | 1085, 1091 | `ILoop` | T+-Loop | with `Restores` |
| `iter` | 404 | 1096, 1100, 1105, 1108, 1111 | none: the iterations of a loop's body | none | no program contains it; the loop's rule types the body, and this one says the same of its iterations |
| `ite` | 408 | 1114, 1120 | `IIf` | T+-If | with `Restores` |
| `br` | 414 | 1124 | `IBr` | T+-Br |  |
| `brIf` | 418 | 1126, 1128 | `IBrIf` | T+-Br-If | not taken, the carried values keep their labels |
| `brTable` | 423 | 1130 | `IBrTable` | T+-Br-Table | the repaired rule |
| `ret` | 428 | 1133 | `IReturn` | T+-Return | the branch to the outermost label |
| `call` | 433 | 1137, 1176 | `ICall` | T+-Call |  |
| `retCall` | 442 | 1151, 1157 | `IReturnCall` | T+-Return-Call |  |
| `retCallIndirect` | 457 | 1162, 1169 | `IReturnCallIndirect` | T+-Call-Indirect with the premises of T+-Return-Call |  |
| `callIndirect` | 452 | 1143, 1181 | `ICallIndirect` | T+-Call-Indirect | the table's level is in the premise |
| `callRef` | 466 | 1189, 1196 | `ICallRef` | T+-Call-Ref |  |
| `unreachable` | 470 | none: a trap | `IUnreachable` | T+-Unreachable |  |
| `throw` | 473 | 1203 | `IThrow` | T+-Throw | a tag is the number of public values it carries |
| `throwRef` | 477 | 1205 | `IThrowRef` | T+-Throw-Ref | the reference is to an exception the state keeps |
| `tryTable` | 483 | 1207, 1213 | `ITryTable` | T+-Try-Table |  |

The paper cites sixteen rules from SecWasm under their own names, T-Const and so on (Fig. 13
of SecWasm's full version): the column marks them "(SecWasm)". Its own rules are named
T+-Block and so on (its figures of rules in the appendix). Where the column says "as" a rule,
the paper prints no rule for the instruction and says in the text of the appendix that it
follows that one. The paper types a call of a
host import by T+-Call; the core's six host instructions stand for such calls (section 8), with the
host's part of the call in their rules.

Two side definitions carry premises:

- `Restores C pcEnd after keep` (`Defs.lean:208`): either the pc does not drop
  where the construct ends (`pcEnd` flows into the first pc of `after`), or `keep` has every
  preserved global. Convince yourself that this is `Validation.Shape.Restores`.
- `ClauseOk` (`Defs.lean:195`): a clause of a `try_table` names a label whose
  type has as many values as its tag carries, or none for a clause that catches everything.

What the Lean rules leave out of the paper's: value types, and with them T+-Relabel, which
raises the label of one value (`relabel` here is T+-Relabel-Results, on the whole segment).
The premises that the paper prints in brackets are the witnesses of the Haskell constructors,
and each is a premise of the Lean rule.

`WellLTyped C F` (`Defs.lean:516`) is the paper's rule for functions, for every
function of the module: its body is typed under the one label of the function, from an empty
segment, at the function's bound; and either it ends under a public pc or the function
compares every preserved global at its return (`Validation.Shape.ReturnsWith`). It does not
ask a function's results to be at least its bound (the premise of the paper's T+-Func that,
as the paper says, the types do not enforce); the rules for the indirect call and the
call through a reference ask that of the type they expect, which is where the proof uses it.

## 4. States and semantics

`State`, `Defs.lean:526`: the locals, the globals, the memories as bytes with a
level each, the size and the limit of each memory, the tables, each with its size and limit, the element segments, the levels of the host's channels (a stream, a directory, a file), the descriptor table, the
names of the files in each directory, what
was written to each and what is left to read from each, the data segments, and the
exceptions kept for the references to them.

`Eval F n ls e σ s o`, `Defs.lean:889`: in the module `F`, with enclosing
labels of arities `ls`, the sequence `e` on the segment `σ` and the state `s` ends as `o`. `n`
is the size of the derivation and nothing else. An outcome (`Out`,
`Defs.lean:782`) is the end of the sequence, a branch to an enclosing label
with the values it carries, or an exception that nothing in the sequence caught. A trap is the
absence of a rule, and so is a run that does not terminate. An operation that traps on some
operands (`partialBinop`, `partialUnop`) is a partial function, and its rule has the premise
that the function is defined there.

The paper's evaluation rules are named E+-Load and so on, and its figure `fig:eval` prints
five: E+-Load is `load` (line 925), E+-Br is `br` (line 1124),
E+-Block is `blockCont` (line 1076), E+-Block-Exit is `blockExit` (line
1081), and E+-Call is `call` (line 1137). For every other
instruction, the rules are in the column "Semantics" of the table of section 3. The paper's
`lands`, `exits` and `kept` are `Out.lands` (`Defs.lean:812`), `Out.exits`
(`Defs.lean:820`) and `Kept` (`Defs.lean:775`).

Convince yourself of six things, which are where this semantics is not the specification's
text:

1. **A block's body runs on the block's parameters alone** (`blockCont`,
   line 1076), and what is below them on the stack waits. On validated code
   this is what WebAssembly does, since a body cannot reach below its parameters. That the two
   agree is not proved.
2. **The run-time checks are premises.** A load goes on only if every byte it reads is within
   the memory and its level flows into the load's declared level (line 925).
   An instruction on the table goes on only if the entries it names are within the table.
   An indirect call goes on only if the entry names a function with the expected parameters
   and results whose bound is at least the expected one (line 1143).
   A host write goes on only if every byte it takes flows into the level of the descriptor's
   channel (line 969), and a file is opened only if every byte of its
   name is public (line 1031). These are the paper's hybrid checks.
3. **The comparison of preserved globals is a premise too** (`Kept`,
   `Defs.lean:775`): where control comes out of a block, a loop, a conditional or a
   `try_table` by its end or by a branch to its label, and where a call returns, the globals
   in `keep` hold what they held at the construct's start or at the call. A branch further
   out and an exception skip it.
4. **A loop runs `iter`** (lines 1085 to 1108): the body
   again while it branches to the loop's label. The loop's comparison is therefore with the
   state at its first entry, as in the implementation.
5. **A call** (line 1137) runs the callee's body on an empty segment with a
   frame made of the arguments, and gives the caller its own locals back. `return` and a
   branch to the function's label end the callee alike (`Out.lands`).
6. **A tail call** (line 1151) is written as a call whose results the
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
| (iv) the table, if its label is public | `∀ x, C.table x = L → s.sameTable t x`: for every table, the entries, the size and the limit (`Defs.lean:560`) |
| (v) the descriptors, the labels of the channels, and the names of the files in every directory | `s.chan = t.chan` and `s.sameHost t` (`Defs.lean:571`): the descriptor table `fdt`, the names `names`, and `file`, which gives a file of a directory its channel |
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

`noninterference_labels`, `Statement.lean:79`, which section 9
restates for the judgment with value types as `noninterference`:

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

- `WellLTyped C F`: every function of the module is typed, as section 3 says.
- `∀ i, C.preserved i → C.globals i = L`: a preserved global is public, which the policy
  ensures (`Validation.Policy`).
- The two calls are of the same function, and their arguments and states are related as above.
- Both calls end. A call that traps, fails a comparison of preserved globals, or runs for ever
  has no `Invoke`, and the theorem says nothing of it: the property is termination-insensitive.
- No declassification: the core has no such instruction.

### Where the statements differ from the paper's

The paper states its theorem for the calculus (`lem:swp-ni`) as `noninterference` is stated
(section 9; on labels, `noninterference_labels`):
two `Invoke`s of one function from low-equivalent states. Its `ret(r, s')` is
`Ended.returned r s'` and its `exn_t(w, s')` is `Ended.threw t w s'`. The differences left:

- `refinement` is for every end of a run, by a return or by an exception; the paper's
  `lem:refinement` states the case of a return. `machine_noninterference` has the case of two
  runs that end by the same exception too, which the paper's `thm:tini` does not state.
- The paper's `thm:tini` is about the implementation: a typed program and `step`. Two links
  of it are outside Lean, by reading: that a value of the Haskell instruction type is a
  derivation of `Typed`, whose label part is `LTyped` (the table of section 3), and that `step` makes the transitions of
  `Step` (the table of section 6).
- `tini` in `Noninterference.lean` is `noninterference_labels` in the terms of the proof (`StRel` and
  `PresEq`, which together are `LowEq`: `LowEq.split`, `LowEq.join`).

## 6. The machine, and refinement

`Machine.lean` has a small-step machine for the core, written after the implementation's
`step` (`Interpreter.hs:404`), and proves that `Eval` describes it.

`Step F c nx`, `Machine.lean:224`: one transition, from the configuration
`c` to the next one or to the end of the run. `Runs F c e`,
`Machine.lean:304`: the transitions from `c` to the end `e`. A run that traps
or does not end has no `Runs`.

| Lean | Where | Haskell | Where | Convince yourself that |
|---|---|---|---|---|
| `Config`: `s`, `σ`, `e`, `K` | `Machine.lean:40` | `Config store locals stack code control` | `Interpreter.hs:311` | the fields are the same; the Lean state has the local variables in it (`s.loc`). |
| `Frame.label` | `Machine.lean:32` | `BlockLabel below cont rest`, `HandlerLabel handlers below cont rest` | `Interpreter.hs:270` | a label has the operands below its block and the code after it; a block's label is one with no clauses. `keep` and `recorded` are the `IRequireRestored recorded` that the Haskell puts in front of `cont` (`Interpreter.hs:852`). |
| `Frame.loop` | `Machine.lean:34` | `LoopLabel below body cont rest` | `Interpreter.hs:288` | it has the body besides. |
| `Frame.call` | `Machine.lean:36` | `CallBoundary depth below callerLocals cont callerControl` | `Interpreter.hs:299` | it has the caller's locals. `checks` is the comparisons in front of `cont`: one for a call (`Interpreter.hs:843`), and one more for each tail call made in the callee's place. The Lean machine has no bound on the depth of calls. |
| the empty control stack; `Config.entry` | `Machine.lean:313` | `EntryBoundary`; `startFunction` | `Interpreter.hs:1331` | a call from outside runs the body over a boundary of its own that has the function's comparison. |
| `Basic`, `Step.basic` | `Machine.lean:70` | the clauses of `stepInstr` that end in `stepped` | `Interpreter.hs:417` | each instruction that is not one of control does to the operands and the state what its `Eval` rule says (section 4), and traps where the rule has a premise that fails. |
| `Step.block`, `tryTable`, `loop`, `ite` | `Machine.lean:227` | the clauses for `IBlock`, `ITryTable`, `ILoop`, `IIf` | | the body runs on the construct's parameters over a new label. |
| `Step.endLabel`, `endLoop`, `endCall`, `done` | `Machine.lean:256` | `popControl` | `Interpreter.hs:1040` | at the end of the current block the top of the control stack says what follows, behind its comparisons. |
| `Unwind`, in `Step.br`, `brIf`, `brTable`, `ret` | `Machine.lean:184` | `unwind`, `unwindTo`, `returnUnwind` | `Interpreter.hs:1062` | a branch drops the labels it passes without their comparisons; a loop's label stays and its body runs again; the function's label is its boundary. |
| `Step.call`, `callIndirect`, `callRef` | `Machine.lean:267` | `enterCall` | `Interpreter.hs:745` | the callee's body runs on no operands with locals made of the arguments, over a boundary. The checks of an indirect call are premises, as in `Eval`. |
| `boundary`, in `Step.retCall`, `retCallIndirect` | `Machine.lean:59` | `tailCall` | `Interpreter.hs:1118` | the labels of the running function are dropped, its clauses with them, and the callee is entered over the function's own boundary, which gets the callee's comparison too. |
| `Raise`, in `Step.throw` | `Machine.lean:205` | `throwException` | `Interpreter.hs:1168` | an exception passes labels without a clause for it and call boundaries, where the caller's locals are back; the first clause for it is a branch from around the clause's block; below the last boundary it ends the run. |

`refinement`, `Machine.lean:598`: a run of the machine from
`Config.entry f a s` to an end `e` is `Invoke F f a s e`. No typing is assumed. This is the
paper's `lem:refinement`, in the direction the theorem needs.

`machine_noninterference_labels`, `Machine.lean:620`: the
statement of `noninterference_labels` with two runs of the machine for the two `Invoke`s.
Section 9 restates it with value types as `machine_noninterference`.

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
| `leak` | `Findings.lean:36` | the program (a): four nested blocks, a `br_table` on the secret local with the targets 0 and 3, and a write to the public global after the third block. |
| `leak_not_typed` | `Findings.lean:107` | `Typed` has no derivation for it from a public pc, for any labels, segment and result; `leak_not_typed_labels` says it of `LTyped`, and the first follows. |
| `leak_runs_differ`, `leak_runs_globals` | `Findings.lean:121` | `Eval` has a run that ends with 1 in the public global if the secret local is 0, and one that leaves the global if it is not. |
| `call_after_secret_branch_typed` | `Findings.lean:181` | the program (b) is typed from a public pc (with value types; `_labels` for the label part). |
| `write_after_public_branch_typed` | `Findings.lean:220` | the program (c) is typed from a public pc (likewise). |
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
from the rule's output, as T-Seq does, where `WasmIfc.LTyped` does not type it. In `leak`
nothing follows the `br_table` in its block.

## 8. The host

The paper's one assumption about the host is that the status of a host call depends only on
its operands and on the public part of the state. In the core this is a definition and no
hypothesis: `hostStatus` (`Defs.lean:724`) is a function of the call, its
operands, the descriptor table, the names of the files in every directory, the channel of each
file, the levels of the channels and the size of the first memory, and of nothing else.
`State.status` applies it to a state. The proof uses the assumption in one lemma,
`StRel.status` (`Basic.lean:712`): two runs' states give a call with the
same operands the same status. Each host primitive has a rule for status 0, which does what the
call does, and one for any other status, which leaves the state as it was. Both push the status.
What a public pointer among the operands points to (a path, the subscriptions of a poll)
counts as an operand: the host checks those bytes to be public before it uses them.

There are six primitives, one for each shape of rule:

| Primitive | Rule | What it does on success |
|---|---|---|
| `hostRead` | line 953 | stores what it reads from a descriptor's channel, and how much, at the channel's level |
| `hostWrite` | line 969 | sends cells to a descriptor's channel, and traps if one is more secret than the channel |
| `hostOpen` | line 1031 | makes a descriptor, with a public number, for a file of a directory; the name's bytes must be public |
| `hostGet` | line 984 | stores public data of a public source that has no descriptor |
| `hostCtl` | line 999 | changes the descriptor table, the directories and the position of a descriptor, by functions of the operands and of what the table and the directories were (`State.control`, `Defs.lean:755`) |
| `hostPoll` | line 1013 | stores a report on several descriptors at the join of their channels' levels (`State.pollLevel`, `Defs.lean:765`); the report is a function of what those channels have left to read |

Each function of WASI Preview 1, with the case of `runWasiCall` (`Wasi.hs:866`)
that serves it:

| WASI function | Where | Shape | What in `Runtime.Wasi` makes it so |
|---|---|---|---|
| `fd_read` | `Wasi.hs:957` | `hostRead` | what is read and its count are stored at the descriptor's level (`readInto`, `pokeWord32At`) |
| `fd_pread` | `Wasi.hs:935` | `hostRead` | as `fd_read`, at an offset that is an operand |
| `sock_recv` | `Wasi.hs:1091` | `hostRead` | as `fd_read`; the flags it stores are at the connection's level too |
| `fd_readdir` | `Wasi.hs:962` | `hostRead` | the entries and their size are stored at the directory's level |
| `path_readlink` | `Wasi.hs:1037` | `hostRead` | the link's contents are stored at the directory's level |
| `fd_filestat_get` | `Wasi.hs:917` | `hostRead` | the attributes are stored at the descriptor's level (`pokeStat`) |
| `path_filestat_get` | `Wasi.hs:1007` | `hostRead` | the attributes are stored at the directory's level |
| `fd_tell` | `Wasi.hs:993` | `hostRead` | the position is stored at the descriptor's level |
| `fd_write` | `Wasi.hs:998` | `hostWrite` | every byte taken must flow into the descriptor's level, or the run traps (`gather`) |
| `fd_pwrite` | `Wasi.hs:949` | `hostWrite` | as `fd_write` |
| `sock_send` | `Wasi.hs:1102` | `hostWrite` | as `fd_write` |
| `path_open` | `Wasi.hs:1026` | `hostOpen` | the new descriptor has the directory's level and a public number (`openPath`, `insertFd`); the path is public (`peekPath`) and stays in the directory (`confine`) |
| `sock_accept` | `Wasi.hs:1078` | `hostOpen` | the connection has the listening socket's level and a public number; in the model the connections of a socket are one channel, its file of the empty name |
| `args_get` | `Wasi.hs:869` | `hostGet` | public bytes from the run's configuration |
| `args_sizes_get` | `Wasi.hs:870` | `hostGet` | as `args_get` |
| `environ_get` | `Wasi.hs:871` | `hostGet` | as `args_get` |
| `environ_sizes_get` | `Wasi.hs:872` | `hostGet` | as `args_get` |
| `clock_res_get` | `Wasi.hs:873` | `hostGet` | a public constant |
| `clock_time_get` | `Wasi.hs:881` | `hostGet` | the time, stored as public: a public input of the run |
| `random_get` | `Wasi.hs:1073` | `hostGet` | random bytes, stored as public: a public input of the run |
| `fd_prestat_get` | `Wasi.hs:941` | `hostGet` | the length of a granted directory's name, from the descriptor table |
| `fd_prestat_dir_name` | `Wasi.hs:944` | `hostGet` | a granted directory's name, from the descriptor table |
| `fd_fdstat_get` | `Wasi.hs:897` | `hostGet` | the kind, the flags and the rights of a descriptor, from the descriptor table, stored as public (`pokeFdstat`) |
| `fd_close` | `Wasi.hs:891` | `hostCtl` | removes a descriptor |
| `fd_renumber` | `Wasi.hs:972` | `hostCtl` | moves a descriptor, with its level |
| `fd_fdstat_set_flags` | `Wasi.hs:906` | `hostCtl` | changes a descriptor's flags; a secret socket is not made non-blocking (`ENOTSUP`, `nonBlockingRefused`) |
| `fd_fdstat_set_rights` | `Wasi.hs:912` | `hostCtl` | narrows a descriptor's rights |
| `fd_seek` | `Wasi.hs:977` | `hostCtl` | moves the position; the new position is stored at the descriptor's level, as `fd_tell` stores it; on a secret file a seek back from the end or the position is refused (`ENOTSUP`), since whether it lands before the start is the file's secret |
| `fd_advise` | `Wasi.hs:882` | `hostCtl` | changes nothing |
| `fd_allocate` | `Wasi.hs:887` | `hostCtl` | not supported: a status and nothing else |
| `fd_datasync` | `Wasi.hs:895` | `hostCtl` | changes nothing that a program sees |
| `fd_sync` | `Wasi.hs:896` | `hostCtl` | as `fd_datasync` |
| `fd_filestat_set_size` | `Wasi.hs:920` | `hostCtl` | cuts or extends the file by an operand: what is left to read changes |
| `fd_filestat_set_times` | `Wasi.hs:925` | `hostCtl` | sets times that are operands |
| `path_create_directory` | `Wasi.hs:1003` | `hostCtl` | adds a name to a directory |
| `path_filestat_set_times` | `Wasi.hs:1012` | `hostCtl` | sets times that are operands |
| `path_link` | `Wasi.hs:1017` | `hostCtl` | adds a name; between directories of different levels it fails with `EXDEV`, as between two file systems (`requireSameLevel`) |
| `path_remove_directory` | `Wasi.hs:1043` | `hostCtl` | removes a name |
| `path_rename` | `Wasi.hs:1047` | `hostCtl` | moves a name; between directories of different levels it fails with `EXDEV`, as between two file systems (`requireSameLevel`) |
| `path_symlink` | `Wasi.hs:1053` | `hostCtl` | adds a name; the link's contents are a path and so public |
| `path_unlink_file` | `Wasi.hs:1063` | `hostCtl` | removes a name |
| `sock_shutdown` | `Wasi.hs:1110` | `hostCtl` | closes a direction of a connection |
| `sched_yield` | `Wasi.hs:1072` | `hostCtl` | changes nothing |
| `proc_raise` | `Wasi.hs:1071` | `hostCtl` | not supported: a status and nothing else |
| `poll_oneoff` | `Wasi.hs:1070` | `hostPoll` | the events and their number are stored at the join of the levels of the sockets polled (`pollOneoff`); the subscriptions are public |
| `proc_exit` | `Wasi.hs:868` | none | ends the run; the core has no rule for it, so a run that exits is as one that traps, and the theorem says nothing of it |

Convince yourself of three things that the table rests on:

- **A file has one level.** A file gets the level of the directory it is opened in
  (`openPath`, `Wasi.hs:1182`). So a path must stay in its directory once symbolic
  links are followed (`confine`, `Wasi.hs:572`), no call moves or links a file between
  directories of different levels (`requireSameLevel`, `Wasi.hs:621`), and
  the host refuses to start if a directory contains another of a different level
  (`newHost`, `Wasi.hs:194`). That the granted directories share no file by a hard
  link made outside the run is assumed.
- **What decides a public status is public.** Paths, the contents of a symbolic link and the
  subscriptions of a poll must be public bytes (`peekPath`, `requireAtMost`). The list of
  buffers of a read or a write may be as secret as the descriptor, and then a buffer out of
  bounds is an access out of bounds of the memory, a trap as in WebAssembly, and no status
  (`usingBuffers`, `Wasi.hs:487`). Whether a name exists in a directory and what
  kind of entry it is decide the status of the `path_` calls, in a secret directory too: the
  model has the names in `sameHost`, as public. Where the outcome of a call would tell a
  secret, the host refuses the call before it is made, with a status that depends on the
  operands and on the levels of the descriptors, which are public: a secret socket is not made
  non-blocking (`ENOTSUP`, `nonBlockingRefused`, `Wasi.hs:798`), a seek back
  from the end or the position of a secret file is refused (`ENOTSUP`), and a rename or a link
  between directories of different levels fails with `EXDEV`. The model has these statuses:
  `hostStatus` takes the channels' levels.
- **What the model leaves out.** A failure of the operating system on a secret file or
  connection (a full disk, a connection that the peer closed) is a status that the model does
  not have. `proc_exit` has no rule. `hostWrite` does not store how much it wrote, which the
  host stores at the descriptor's level. `fd_seek` is a `hostCtl` that also stores the new
  position, as `fd_tell` would.

## 9. Value types, and the paper's names

`LTyped` has one type for all values. `ValueTypes.lean` has the paper's judgment, with labelled
value types `t⟨ℓ⟩`, over the same instructions and the same semantics, and it has the paper's
names:

| Lean | Where | Convince yourself that |
|---|---|---|
| `VTy`, `LTy`, `VSTy` | `ValueTypes.lean:18` | the value types are WebAssembly's numbers, vectors and references to functions and to exceptions, and a stack type is a list of pairs of a value type and a level. `labelsOf` forgets the types. |
| `VCtx` | `ValueTypes.lean:67` | the context has the labelled types of the locals and the globals, the types that each tag carries, and an address type for each memory and each table (`i32`, or `i64` for a 64-bit one). `VCtx.erase` is the `Ctx` of section 3. |
| `Typed` | `ValueTypes.lean:104` | each rule is the rule of `LTyped` of the same name with the types that `Syntax.Instructions` gives the instruction: an address has its memory's or its table's address type, a condition and the operands of a host call are `i32`, a table holds references to functions, the operands of an operation on two values have one type. A block type in an instruction is the labels of the block's types. |
| `Typed.erase` | `ValueTypes.lean:363` | a derivation of `Typed` is, with the types forgotten, a derivation of `LTyped`. |
| `rise` | `ValueTypes.lean:467` | the paper's `lem:rise` for `Typed`, from `rise_labels`. |
| `WellTyped`, `WellTyped.erase` | `ValueTypes.lean:499` | a module whose functions are `Typed` is `WellLTyped` with the types forgotten. |
| `noninterference`, `machine_noninterference` | `ValueTypes.lean:525` | the two theorems for such a module: `noninterference_labels` and `machine_noninterference_labels` with the function's type and the context read through `labelsOf` and `VCtx.erase`. |

The semantics does not look at types: a value is a number whatever its type, and an operation
is a function on numbers. So the theorems with value types follow from the ones on labels, by
`Typed.erase`, and no proof was done again. What the layer adds to the statement is that
the hypothesis is about programs typed as WebAssembly types them, with 64-bit memories and
tables among them. What it does not model: that a value of a type is within that type's range
(an `i32` below 2^32), and so the wrapping of an address.

### Outside the core

The numeric and vector instructions one by one (an operation is any function on numbers, of
one or two operands, total or partial); the ranges of the value types;
linking; `proc_exit`, and the failures of the operating system on a secret file or connection
(section 8); local variables split into webs and the inference of labels, which
happen before typing; declassification.
