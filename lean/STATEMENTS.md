# Reading the Lean development: what to check

For a reviewer who checks the definitions and the statement and leaves the proofs to Lean.
`lake build` checks every proof, and `#print axioms WasmIfc.noninterference` lists `propext`,
`Classical.choice` and `Quot.sound` only. So what remains to be checked by a person is that
the definitions say what the paper says. They are in two files, 845 and
116 lines long, of the development's 4,193:

- `WasmIfc/Defs.lean`: the syntax, the typing judgment, the states and the semantics.
- `WasmIfc/Statement.lean`: low equivalence, a call from outside, and the theorem.

The other files (`Basic.lean`, `Confinement.lean`, `Noninterference.lean`) are lemmas and
proofs, and `Examples.lean` has small programs with their typings and runs. This file is
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

`Func` (`Defs.lean:144`) is a function: its type, the levels of its other
locals, the globals compared at its return, and its body. `FuncTy`
(`Defs.lean:144`) is the paper's labelled function type: parameters, the
bound on the pc of its callers, results.

## 3. The typing judgment

`Typed C Ls e P st P' st'`, `Defs.lean:184`, is the paper's judgment of
appendix B, "The Rules": under the labels `Ls` (innermost first), the sequence `e` takes the pc
stack `P` and the current block's segment `st` to `P'` and `st'`. Each rule types one
instruction followed by the rest of its sequence, so the paper's W-Seq is built into every
rule. `Ctx` (`Defs.lean:153`) has the levels of the locals and the globals,
which globals are preserved, the function types, the level of the table and the tags.

Check each rule against the constructor of `Syntax.Instructions.Instr` and the paper's rule in
the table. The Lean rules are the lift-free ones: no rule raises the label of a value that was
on the stack before a branch.

| Lean rule | Line | Semantics (lines) | `Instr` constructor | Paper's rule | Note |
|---|---:|---|---|---|---|
| `nil` | 185 | 631 | `INil`, the end of a sequence | W-Seq |  |
| `const` | 186 | 632 | `IConst` | W-Const |  |
| `binop` | 189 | 634 | `IAdd` and the other operations on two values | W-Binop | one rule for all of them |
| `unop` | 192 | 636 | the operations on one value, `IRefIsNull` among them | W-Binop |  |
| `dup` | 195 | 638 | `IDuplicate` | typed references | written by the elaborator for `br_on_null` |
| `select` | 198 | 640 | `ISelect` | W-Select |  |
| `drop` | 201 | 643 | `IDrop` | W-Drop |  |
| `nop` | 204 | 645 | `INop` | W-Nop |  |
| `relabel` | 207 | 647 | `IRelabelResults` | W-Relabel, W-Nop-Sub | raises labels of the block's whole segment |
| `localGet` | 211 | 649 | `ILocalGet` | W-Get-Local |  |
| `localSet` | 214 | 651 | `ILocalSet` | W-Set-Local |  |
| `localTee` | 218 | 653 | `ILocalTee` | W-Tee-Local |  |
| `globalGet` | 222 | 656 | `IGlobalGet` | as in SecWasm |  |
| `globalSet` | 225 | 658 | `IGlobalSet` | W-Set-Global | for a global that is not preserved |
| `globalSetPreserved` | 233 | 658 | `IGlobalSetPreserved` | preserved globals | the same instruction, for a preserved global |
| `load` | 237 | 660 | `ILoad`, `ILoadN` | W-Load | the level is the load's declaration; the check is in the semantics |
| `store` | 240 | 663 | `IStore`, `IStoreN` | W-Store | the level is at least the join, where the implementation takes the join |
| `fill` | 245 | 667 | `IMemFill` | W-Memory-Fill |  |
| `copy` | 253 | 671 | `IMemCopy` | W-Memory-Copy |  |
| `memInit` | 279 | 697 | `IMemInit` | W-Memory-Init |  |
| `dataDrop` | 284 | 701 | `IDataDrop` | bulk memory | no premise |
| `memSize` | 298 | 709 | `IMemSize` | as in SecWasm |  |
| `memGrow` | 302 | 711 | `IMemGrow` | W-Memory-Grow |  |
| `tableGet` | 258 | 675 | `ITableGet` | tables | one table |
| `tableSet` | 262 | 678 | `ITableSet` | tables |  |
| `tableFill` | 288 | 703 | `ITableFill` | tables |  |
| `tableCopy` | 293 | 706 | `ITableCopy` | tables | one table, so the source's level is the table's |
| `hostRead` | 271 | 685 | a call of a host import that reads (`HostFunc`), with the driver's labelling | W-Host | one call stands for the reading ones |
| `hostWrite` | 275 | 692 | a call of a host import that writes, with the driver's check | W-Host | one call stands for the writing ones |
| `block` | 307 | 714, 719 | `IBlock` | W-Block | with `Restores`, the comparison of preserved globals |
| `loop` | 313 | 723, 729 | `ILoop` | W-Loop | with `Restores` |
| `iter` | 323 | 734, 738, 743, 746 | none: the iterations of a loop's body | none | no program contains it; the loop's rule types the body, and this one says the same of its iterations |
| `ite` | 327 | 749, 755 | `IIf` | W-If | with `Restores` |
| `br` | 333 | 759 | `IBr` | W-Br |  |
| `brIf` | 337 | 761, 763 | `IBrIf` | W-Br-If | not taken, the carried values keep their labels |
| `brTable` | 342 | 765 | `IBrTable` | W-Br-Table' | the repaired rule |
| `ret` | 347 | 768 | `IReturn` | W-Return | the branch to the outermost label |
| `call` | 352 | 772, 809 | `ICall` | W-Call |  |
| `retCall` | 361 | 786, 792 | `IReturnCall` | tail calls |  |
| `retCallIndirect` | 376 | 796, 803 | `IReturnCallIndirect` | tail calls |  |
| `callIndirect` | 371 | 778, 813 | `ICallIndirect` | W-Call-Indirect | the table's level is in the premise |
| `callRef` | 385 | 820, 827 | `ICallRef` | typed references |  |
| `unreachable` | 389 | none: a trap | `IUnreachable` | W-Unreachable-Poly |  |
| `throw` | 392 | 833 | `IThrow` | exceptions | a tag is the number of public values it carries |
| `tryTable` | 399 | 834, 840 | `ITryTable` | exceptions |  |

Where the column of the paper's rule names no W-rule, the rule is in the paper's section on
what it adds to SecWasm (`sec:ifc-beyond`) and has no printed inference rule.

Two side definitions carry premises:

- `Restores C pcEnd after keep` (`Defs.lean:175`): either the pc does not drop
  where the construct ends (`pcEnd` flows into the first pc of `after`), or `keep` has every
  preserved global. Convince yourself that this is `Validation.Shape.Restores`.
- `ClauseOk` (`Defs.lean:165`): a clause of a `try_table` names a label whose
  type has as many values as its tag carries, or none for a clause that catches everything.

What the Lean rules leave out of the paper's: the bracketed premises of the W-rules, which
hold only under SecWasm's restrictions (the theorem is for the rules without them, the weaker
hypothesis), and value types.

`WellTyped C F` (`Defs.lean:432`) is the paper's rule for functions, for every
function of the module: its body is typed under the one label of the function, from an empty
segment, at the function's bound; and either it ends under a public pc or the function
compares every preserved global at its return (`Validation.Shape.ReturnsWith`). It does not
ask a function's results to be at least its bound; the rules for the indirect call and the
call through a reference ask that of the type they expect, which is where the proof uses it.

## 4. States and semantics

`State`, `Defs.lean:442`: the locals, the globals, the memory as bytes with a
level each, its size and limit, the function table, the levels of the host's descriptors, what
was written to each and what is left to read from each, and the data segments.

`Eval F n ls e σ s o`, `Defs.lean:630`: in the module `F`, with enclosing
labels of arities `ls`, the sequence `e` on the segment `σ` and the state `s` ends as `o`. `n`
is the size of the derivation and nothing else. An outcome (`Out`,
`Defs.lean:552`) is the end of the sequence, a branch to an enclosing label
with the values it carries, or an exception that nothing in the sequence caught. A trap is the
absence of a rule, and so is a run that does not terminate.

Convince yourself of five things, which are where this semantics is not the specification's
text:

1. **A block's body runs on the block's parameters alone** (`blockCont`,
   line 714), and what is below them on the stack waits. On validated code
   this is what WebAssembly does, since a body cannot reach below its parameters. That the two
   agree is not proved.
2. **The run-time checks are premises.** A load goes on only if every byte it reads is within
   the memory and its level flows into the load's declared level (line 660).
   An indirect call goes on only if the entry names a function with the expected parameters
   and results whose bound is at least the expected one (line 778).
   A host write goes on only if every byte it takes flows into the descriptor's level
   (line 692). These are the paper's hybrid checks.
3. **The comparison of preserved globals is a premise too** (`Kept`,
   `Defs.lean:545`): where control comes out of a block, a loop, a conditional or a
   `try_table` by its end or by a branch to its label, and where a call returns, the globals
   in `keep` hold what they held at the construct's start or at the call. A branch further
   out and an exception skip it.
4. **A loop runs `iter`** (lines 723 to 746): the body
   again while it branches to the loop's label. The loop's comparison is therefore with the
   state at its first entry, as in the implementation.
5. **A call** (line 772) runs the callee's body on an empty segment with a
   frame made of the arguments, and gives the caller its own locals back. `return` and a
   branch to the function's label end the callee alike (`Out.lands`).

## 5. Low equivalence and the theorem

`LowEq C s t`, `Statement.lean:19`, is the paper's low equivalence
(`def:attacker`). Clause by clause:

| The paper | `LowEq` |
|---|---|
| agree on every local variable labelled public, which includes the arguments | first clause, and the hypothesis `StkRel f.ty.params a0 a1` of the theorem for the arguments |
| agree on every public global | second clause |
| agree on every byte of memory labelled public in both | third clause |
| memories of the same size | `s.size = t.size`, and the same limit |
| the same table of descriptors | `s.chan = t.chan`: the descriptors' levels |
| the input not yet read from and the output written to every public channel | the clause on `out` and `inp` |
| every stack position labelled public | none: a call from outside starts on an empty stack |
| the same names of files in every directory | none: the core's host has no directories |
| (not in the paper) | the function table, if it is public; and a data segment that both states still have is the same |

`Invoke F f a s e`, `Statement.lean:55`: the function `f` called from
outside on the arguments `a` in the state `s` ends as `e`, by returning results or by an
exception. Convince yourself that it is `Eval` of the body as rule `call` runs it, the
comparison of the function's `keep` included, which the machine makes for the invoked function
as for a callee.

`noninterference`, `Statement.lean:72`:

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
  inclusion and a refinement. The Lean theorem is about the typed program directly, under a
  big-step semantics. The correspondence between the Lean rules and the Haskell constructors,
  and between `Eval` and `step`, is by reading, with the table of section 3.
- It concludes more than the paper states: whether a call ends by an exception, and which, is
  public.
- `tini` in `Noninterference.lean` is the same theorem in the terms of the proof (`StRel` and
  `PresEq`, which together are `LowEq`: `LowEq.split`, `LowEq.join`).

### Outside the core

More than one value type, and so the numeric and vector instructions as such; 64-bit and
several memories; several tables, and a table's size and growth; references to exceptions (`exnref`, `throw_ref`, the clauses that hand one out);
linking; the WASI calls other than one that reads and one that writes, with directories,
error codes and sockets; local variables split into webs and the inference of labels, which
happen before typing; declassification.
