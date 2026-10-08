## wasm-ifc

A WebAssembly interpreter in Haskell whose instruction type makes ill-typed programs and, for
the programs it is given a security policy for, information leaks impossible to represent. The
information-flow rules are those of SecWasm (Bastys, Algehed, Sjösten and Sabelfeld, SAS 2022).

### How it works

A module goes through one pipeline. The decoder produces an untyped AST; the elaborator
validates it, which is type-checking, and in doing so recovers the type indices of an
intrinsically-typed module; instantiation links imports, allocates memories and tables,
places segments and runs the start function; and a small-step machine runs exports.

```
  bytes ──decode──▶ RawModule ──elaborate──▶ Module ──instantiate──▶ ModuleInst ──step──▶ result
   Codec.Wasm      Syntax.*    Validation.*  Syntax.*   Runtime.*    Runtime.*   Runtime.Interpreter
```

The typed instruction `Instr` is indexed by the module's shape, the function's frame, the
enclosing labels, a stack of program-counter labels before and after, and the operand stack
before and after. Every value type in those indices carries a security level, public or
secret. So one type states both what WebAssembly validation checks and what SecWasm's type
system checks: a computed value is as secret as its most secret operand, a write inside a
secret branch to a public place is a type error, and a call from a secret context needs a
callee that allows one. Each side condition of a rule is a witness the instruction carries,
which the elaborator constructs and a hand-written program states. Levels exist only in
types, with one exception: every byte of linear memory has a level at run time, and a load
that reads a byte more secret than it declares traps, which is SecWasm's one dynamic check.

The machine's `step` is total over every well-typed configuration and no configuration can be
ill-typed, so the machine is its own type-soundness argument: preservation holds by
construction and progress by totality. Without a policy every level is public and the
interpreter accepts exactly the modules WebAssembly validation accepts.

### Security policies

Levels come from a policy (`Validation.Policy`), one text format with two carriers: the
module's own `ifc` custom section, keyed by function index, global index and memory-access
position, and a file given with `--policy`, keyed by import and export names. It declares
function types with the bound on their calling context (`export check : H -{L}-> L`), globals,
memory accesses and regions, and the levels of the standard streams and preopened directories
the WASI host connects to. Stores need no declaration, since their level is inferred; loads
take a site declaration, a region, or a default. Annotations can also be written in the source
program as calls to an import module `ifc` (`secret_i32`, `load_secret_i32`, `declassify_i32`,
…), which a plain runtime serves with a shim and this one rewrites into the instructions they
stand for. Whatever the policy does not declare is public.

A policy can also declare a public global preserved (`preserved global 0`, the stack pointer
of compiled C). Code may then change it where a secret decided the control flow, and the
machine checks, where that code ends, that the global has its old value again.

At the host boundary an import is called from a public context with public arguments, and its
results take the policy's levels. Every byte a host call takes from memory is checked against
the level of the file descriptor it concerns, and the run traps if the byte is more secret:
the data of a write, the arrays that list the buffers of a read or a write, and the contents
of a symbolic link; paths and poll subscriptions must be public. Every byte a call stores
about a descriptor carries its level: the data it read, the byte counts, file positions, file
attributes and directory entries. Program arguments, the environment, clocks and random bytes
are public.

### Layout

| Path | Contents |
|------|----------|
| `src/Syntax/`     | the program, raw and typed side by side: types and security levels (`TypesIFC`), immediates, indices, instructions, functions, globals, the module |
| `src/Codec/`      | the binary decoder |
| `src/Validation/` | type-level shapes, singletons, the policy stage, the elaborator |
| `src/Runtime/`    | instantiation, the small-step interpreter, memory with byte levels, the WASI host |
| `app/Main.hs`     | the command-line interface |
| `test/`           | unit tests and typed examples; runners for the spec testsuite and the wasi-testsuite |
| `samples/`        | example programs checked by `samples/check.sh` |
| `bench/`          | benchmarks and the allocation tripwire; results in `BENCHMARKS.md` |
| `paper/`          | the paper draft (a submodule on Overleaf) |
| `Formalisation/`  | earlier Agda and Lean models |
| `app.old/`        | the original prototype, kept for reference (not built) |

Naming follows three layers: `Foo` is syntax, `FooShape` its type-level form in `Validation`,
and `FooInst` its run-time instance.

### Usage

```sh
cabal build
cabal run wasm-ifc -- check  [--policy P] <file.wasm>                      # decode and validate
cabal run wasm-ifc -- explain [--policy P] <file.wasm>                     # and show what inference raised
cabal run wasm-ifc -- invoke [--policy P] <file.wasm> <export> [args...]   # run an export
cabal run wasm-ifc -- run    [--policy P] [--dir D[::G]]... [--env K=V]... <file.wasm> [args...]   # a WASI program
cabal run wasm-ifc -- get    [--policy P] <file.wasm> <global>             # an exported global

./scripts/gate.sh   # format, -Werror build, all test suites, lint, samples
cabal test          # unit tests, the spec testsuite (needs wasm-tools), the wasi-testsuite;
                    # the suites are submodules: git submodule update --init
```

### Status

WebAssembly: the numeric, comparison and conversion instructions, memory including bulk
memory, structured control, calls, `call_indirect` through tables, globals, typed `select`,
whole-module validation and the start function. The official spec testsuite, at the
WebAssembly 3.0 release, passes for this subset (27,891 assertions over 257 scripts, none
failing; the rest need features listed below, and `scripts/spec-report.py` counts them by
feature), and so does
every program in the official wasi-testsuite (72 of 72), over the complete WASI Preview 1
interface.

Information flow: SecWasm's typing rules in full, with the repairs of its printed rules,
including the bound on function types, its subtyping as explicit witnesses, per-byte memory
levels with the run-time load check, and the policy and host boundary described above. The
labels of stores, block results, loop parameters, local variables (split into webs first)
and internal functions are inferred; `explain` shows what inference raised. A two-run
noninterference property test runs over generated programs, and `casestudies/` runs compiled
C programs and SecWasm's and WANILLA's examples under policies with secrets.

SecWasm's two run-time checks are typed obligations: an instruction's type names the check
its rule depends on, and the machine's step for it type-checks only with evidence that the
checked memory read, or the checked table lookup, hands out (`Runtime.Obligation`;
`test/obligations-must-not-compile.sh` checks that four wrong steps are rejected).

Not yet: a noninterference proof; imports of tables,
memories and globals; the `table.*` instructions; multiple memories; reference and SIMD types.
The backlog is `TODO.md`; what the paper can cite is in `HANDOFF.md`.

### Toolchain

GHC 9.12.2 and cabal 3.14 on a POSIX system; wabt (`wat2wasm`, `wasm-validate`) for the
samples; `wasm-tools` (1.261 or later) for the spec testsuite, to convert its scripts and to
say which features a module uses; `wasmtime` optionally, as a second opinion in
`samples/check.sh`.
