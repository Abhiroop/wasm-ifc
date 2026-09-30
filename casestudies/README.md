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
| `password.c` (branch-free) | runs, prints the verdict, logs `checked 4` | 4 |
| `-DLEAK_CONTROL` (logs the verdict, chosen by a branch) | traps when the record reaches the log | 4 |
| `-DLEAK_MEMORY` (logs the hash) | traps when the record reaches the log | 4 |
| `password-naive.c` (the same program written plainly) | rejected: a call to the host under a secret pc | 4 |

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
4. **Both leaks are caught at the host boundary**, at run time, because the log record is built
   in memory: the secret bytes reach `fd_write` on a public descriptor and the run traps before
   they leave.
5. **Declarations:** three lines for the channels and one for the loads of `main`
   (`load-default func 11 : H`); declaring each trapping load instead takes five
   (`declare-loads.py`). Inference raised six locals and one internal function (`write`).

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
| Findings 2, 3, 4, 6 and 7 (programs the printed rules cannot type) | run |

Two of the examples return a secret; as the command-line interface does not deliver a secret
result, they store it in a secret global instead. Example 1 declares its load public, as
SecWasm's does: without the declaration, the region would declare the constant-address load
secret and the module would be rejected statically instead.
