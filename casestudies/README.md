# Case studies with secrets

Programs compiled from C with wasi-sdk 34 (`./bench/tools/fetch.sh wasi-sdk`), run under a
policy with secret inputs and public outputs. They answer the paper's RQ4: can the rules type
real compiled programs that handle secrets, how many declarations do they need, and how often
does the load check fail.

```sh
./casestudies/password/build.sh     # into casestudies/build/ (not committed)
./casestudies/run.py                # results into casestudies/results/<date>-<commit>.json
```

Per program, `run.py` records the policy lines written, the labels inference raised (secret
locals, raised internal functions, attempts), the outcome with the static rejection's rule and
site or the trap's site, whether SecWasm's restrictions (`--secwasm-restrictions`) also accept
the program (if not, it has one of the lift shapes the lift-free rules accept), what it wrote,
and the running time.

`declare-loads.py` completes a policy the way a user reading the traps would, one load
declaration per trap, and reports how many it took: an upper bound on what a user writes.

## The password checker (`password/`)

The overview's scenario: read a password from `/secrets` (secret), compare its hash with a
dictionary of weak passwords, write the verdict to stdout (secret), and append a record to a
log in `/log` (public).

| Program | Outcome | Policy lines |
|---|---|---|
| `password.c` (branch-free), `checker.policy` | traps in libc's `read`, at the load of the byte count (`load 12 3`) | 4 |
| the same, with that load declared (`checker-count-declared.policy`) | rejected: `open` is called under a secret pc | 5 |
| `-DLEAK_CONTROL`, `-DLEAK_MEMORY` | trap at the same load, before the leak is reached | 4 |
| `password-naive.c` (the same program written plainly) | rejected: a call under a secret pc | 4 |

The first two rows changed when the host boundary rule was completed (the commit after
3614d3c). Before, the driver stored the byte count of a read as a public value; the
branch-free checker then ran under the four-line policy, printed its verdict and logged
`checked 4`, and its two leaking variants trapped when the record reached the public log
(`results/2026-09-30-624a05a.json`). Now the count of a read from a secret file is secret, as
the paper's rule says. `read` returns it, `main` checks it (`if (count < 0) return 1;`), and
that branch raises the pc of the rest of `main`, where the log is opened and written. The
first call under the raised pc, `open`, is rejected at the write of `__stack_pointer` in its
prologue. This is the paper's "statuses and errors" case: C checks the result of every read.

What it took, in the order we met it:

1. **C globals live in linear memory.** `hash` and `matched` are addresses, not WebAssembly
   globals (global 0 is the shadow-stack pointer), so they are covered by memory labels, loads
   and regions, not by `global` declarations.
2. **LLVM reuses locals.** At every optimisation level the compiler kept the descriptor of the
   password file and, later, bytes derived from the password in the same local, whose one label
   then made the descriptor secret and every host call on it illegal. The elaborator now splits
   every local into its webs before typing (`src/Validation/LocalWebs.hs`); without that no
   variant of the program is typable.
3. **A branch on a secret before output.** The naive checker compares the hash in a chain of
   branches, and the compiler moves the verdict's `write` into the blocks those branches target,
   so the call to the host happens under a secret pc and is rejected. The branch-free version
   combines the comparisons arithmetically and selects the verdict by an offset.
4. **Both leaks were caught at the host boundary**, at run time, while the byte count was
   public, because the log record is built in memory: the secret bytes reached `fd_write` on a
   public descriptor and the run trapped before they left.
5. **Declarations** (while the byte count was public): three lines for the channels and one for
   the loads of `main` (`load-default func 11 : H`); declaring each trapping load instead took
   five (`declare-loads.py`). Inference raised six locals and one internal function (`write`).
6. **The error check after the read.** With the byte count secret, the check of `read`'s
   result raises the pc of everything after it. The program as written is no longer typable;
   it would need the check removed or folded into branch-free code, or rules that let the host
   and the shadow stack be used under a secret pc (`TODO.md`).

## SecWasm's examples and the counterexamples to its printed rules (`secwasm/`)

`secwasm/build.sh` assembles (wabt) the examples of Bastys et al. (Figure 2a, Examples 1–8,
with their medium level mapped to secret) and one module per counterexample of the paper's
findings; `expected.txt` gives each one's verdict and arguments. Every program ends as SecWasm
says it should, and every counterexample as the repaired rules say:

| Program | Outcome |
|---|---|
| Fig. 2a, Examples 2, 6 (expr 5) and 7 | run |
| Examples 1 and 3 | trap: a load declared public reads a secret byte |
| Examples 4, 5, 6 (expr 3), 6 (expr 4) and 8 | rejected, with the rule and the instruction |
| Finding 1 (the printed `br_table` rule's leak) | rejected |
| Findings 2, 3, 4, 5 (the `br_table` block of §4.2), 6 and 7 (programs the printed rules cannot type) | run |

Two of the examples return a secret; as the command-line interface does not deliver a secret
result, they store it in a secret global instead. Example 1 declares its load public, as
SecWasm's does: without the declaration, the region would declare the constant-address load
secret and the module would be rejected statically instead.

## WANILLA's labelled modules as an oracle (`wanilla/`)

`wanilla/oracle.py` reads the noninterference suite of WANILLA's artifact (Scherer et al.,
CCS 2025; <https://researchdata.tuwien.ac.at/records/hc4rp-xp328>, AGPL, downloaded to
`~/.local/wasm-bench-tools/src/wanilla`, not copied here). Each of its 312 active
specifications names a module, the function called, the labels of its inputs and outputs, and
whether a leak exists (SAT) or not (UNSAT). The script translates each specification it can
express into a policy (confidentiality only: ST and SU are secret, PT and PU public; WANILLA
lists results with the top of the stack first), validates the module, and compares.

| Verdict | Specifications |
|---|---|
| leak, rejected statically | 63 of 63 |
| no leak, accepted | 152 of 196 |
| no leak, rejected (precision loss) | 44 of 196: at `result` 21, `return` 11, `memory.grow` 5, `call_indirect` 4, `call` 2, `local.tee` 1 |
| not expressible | 53: memory, table or import queries 33, memory or global imports 8, imported functions 3, globals relabelled on exit 2, integrity 3, unnamed function 4 |

No leak is missed. The precision losses are rules that decide on labels where WANILLA decides
on values: a `return` or a branch out of the body under a secret pc makes the results secret
even when both paths return the same value; `memory.grow` needs a public pc; one label per
function parameter joins the labels of every call site; and an indirect call is typed at the
all-public type unless the policy declares the type-section entry, which the translation does
not. The per-specification verdicts, policies and errors are in
`results/<date>-<commit>-wanilla.json`.

## The wasi-testsuite's C programs (`wasi-c` in `run.py`)

The fourteen C programs of the wasi-testsuite, with the directory they are given secret
(`preopen / : H`), once with secret and once with public standard streams; every load that
traps on a secret byte is declared secret and the program run again (`"declare"` in `run.py`).
Eight run in both configurations: they never load a byte that the host labelled secret. Six
are rejected (`fdopendir-with-access`, `lseek`, `pread-with-access`, `pwrite-with-access`,
`pwrite-with-append`, `stat-dev-ino`): each asserts on what a call reported about a secret
file (data, a byte count, a position, an attribute), and the failure path of the assertion
runs under a secret pc, where `__assert_fail` writes `__stack_pointer`.

## PolyBench (`polybench/`)

Ten PolyBench/C kernels at the MINI size, their data secret where `main` writes it
(`store-default func main : H`, `load-default func main : H`). With the printing compiled out
(`<kernel>-silent.wasm`), all ten are accepted and run under those two lines, with no further
declaration, and also under SecWasm's restrictions. Printing the results with `fprintf` is
rejected in every kernel: `printf_core` branches on the secret value, and the functions it
calls then run under a secret pc and write `__stack_pointer`. With the stack pointer declared
preserved (`preserved global 0`), validation gets past those functions and is rejected where
`vfprintf` writes its buffer out, an indirect call that ends in a host call under a secret pc.

## A helper called under a secret pc (`frames/`)

`frames.c` reads a key from `/secrets`, calls a helper with a stack frame if the key's first
byte is odd, and reports `done` on its standard output. The helper calls another function, so
it lowers the shadow-stack pointer on entry and raises it on exit (a leaf function uses the
stack without moving the pointer). With `preserved global 0` the program runs for an odd and
an even key; without it, the module is rejected at the helper's first write of the pointer.
