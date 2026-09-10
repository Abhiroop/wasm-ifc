## wasm-ifc

Experiments with WebAssembly and information-flow control, in Haskell.

The pipeline is a single path: decode the binary into an untyped AST, *elaborate* it
(validation = type-checking, recovering the type indices) into an intrinsically-typed module,
*instantiate* that (link imports, allocate memories and tables, place segments, run the start
function), and run exports on a small-step machine.

```
  bytes ──decode──▶ RawModule ──elaborate──▶ Module ──instantiate──▶ ModuleInst ──step──▶ result
   Codec.Wasm      Syntax.*    Validation.*  Syntax.*   Runtime.*    Runtime.*   Runtime.Interpreter
                  (untyped)    (validate +   (typed)   (Instantiate) (instances) (total `step`)
                               recover indices)
```

Each syntactic thing lives in one module in both its forms: `Syntax.Module` holds `RawModule`
(as decoded) and `Module shape` (as validated), `Syntax.Functions` holds `RawFunction` and
`Function`, `Syntax.Globals` holds `RawGlobal` and `Global`. Immediates (`MemArg`, signedness,
narrow widths) are in `Syntax.Immediates`; `Syntax.Types` holds only types.

The three layers follow one naming convention (with `Raw` for the decoder's untyped output):

* **Syntax** (`Syntax.*`): the program as written. Both the raw, unvalidated AST (`RawInstr`,
  `RawModule`, …) and the *intrinsically-typed* `Instr`/`Expr`/`Function`/`Module` — indexed
  by the value-stack shape, locals, labels and module shape they run within, so ill-typed
  programs are not representable.
* **Validation** (`Validation.*`): the type-level *shapes* the syntax is indexed by
  (`Validation.Shape`: `ModuleShape`, `MemShape`, `Append`, `Elem`), the singleton witnesses
  and decidable equality (`Validation.Reflect`), and the elaborator (`Validation.Elaborate`),
  which checks a whole decoded module and recovers its hidden type indices. It validates only;
  it never allocates or runs anything.
* **Runtime** (`Runtime.*`): instantiation (`Runtime.Instantiate`: a validated `Module` to a
  `ModuleInst`, with its own `InstantiationError`), the *instances* (`ModuleInst`, `FuncInst`,
  `MemInst`, the value containers) and the interpreter. `Runtime.Interpreter` is a total small-step abstract
  machine: a `Config` steps to the next `Config` (or finishes, or traps). Because only
  well-typed configurations are representable and `step` is total (enforced by
  `-Werror=incomplete-patterns`, no `error`/`unsafeCoerce`), the machine *is* the
  type-soundness argument — preservation by construction, progress by totality.

Naming: `Foo` is the static syntax (in `Syntax`); `FooShape` is its type-level abstraction
(in `Validation`); `FooInst (shape :: FooShape)` is the runtime instance (in `Runtime`).

### Layout

| Path | Contents |
|------|----------|
| `src/Syntax/`     | the program syntax, raw and typed side by side: types, immediates, indices, instructions, functions, globals, the module |
| `src/Codec/`      | the binary decoder |
| `src/Validation/` | type-level shapes (`Shape`), singletons + decidable equality (`Reflect`), the elaborator (`Elaborate`) |
| `src/Runtime/`    | instantiation, the small-step interpreter, the runtime instances, value/memory machinery, shared numerics, the WASI host |
| `test/`           | the hspec/hedgehog suite, the hand-written typed examples, the spec-testsuite runner |
| `app.old/`        | the original prototype, kept for reference (not built) |
| `app/Main.hs`     | the CLI |
| `samples/wat/`    | example programs (`.wat`); `samples/build.sh` compiles them with `wat2wasm` |
| `samples/wasi/`   | WASI programs run with `run`; checked by `samples/check.sh` |
| `test/spec/`      | the official spec testsuite (a pinned submodule) driven by `test/SpecSuite.hs` |
| `test/wasi/`      | the official wasi-testsuite (a pinned submodule) driven by `test/WasiSuite.hs` |

### Usage

```sh
cabal build
cabal run wasm-ifc -- invoke <file.wasm> <export> [args...]   # decode → validate → instantiate → run
cabal run wasm-ifc -- check <file.wasm>                        # decode → validate only
cabal run wasm-ifc -- run [--dir D[::G]]... [--env K=V]... <file.wasm> [args...]   # a WASI program

samples/build.sh    # compile every sample .wat to .wasm  (needs wabt's wat2wasm)
samples/check.sh    # run every sample and check it against its expected result (and against wasmtime, if installed)
samples/validate.sh # every sample must be accepted by both wasm-validate and our own check
cabal test          # the hspec/hedgehog suite, the spec testsuite (needs wabt's wast2json) and the
                    # wasi-testsuite; both suites are submodules: `git submodule update --init`
```

### Status and limitations

Runs today: the numeric, comparison and conversion instructions (including the saturating
truncations); memory loads and stores, `memory.size`/`memory.grow`, and bulk memory
(`memory.copy`/`fill`/`init`, `data.drop`, passive segments); structured control, branches,
calls, `call_indirect` through tables with element segments, and globals; whole-module
validation; the start function; exported functions invoked from the CLI with arguments typed
by their signature. The official spec testsuite passes for everything in this subset (21,510
assertions; the rest are skipped for features we do not have), and `wasmtime` agrees on every
sample it can run.

WASI: the complete Preview 1 interface (`wasi_snapshot_preview1`, all 45 functions) with a
sandboxed file system over preopened directories, arguments, environment, clocks, random
bytes and polling. `run [--dir HOST[::GUEST]]… [--env NAME=VALUE]… file.wasm [args…]`
executes a program's `_start`. Every program in the official `wasi-testsuite` passes (72 of
72, in C, Rust and AssemblyScript). The interpreter stays pure: a call into the host is handed
out as a request and the IO driver (`Runtime.Wasi`) serves it and resumes the module.

Not yet: information-flow control (the project's goal; `TODO.md` §F); imports of tables,
memories and globals; the `table.*` instructions and `elem.drop`; typed `select` (`0x1C`);
multiple memories; reference and SIMD types; sockets (the `sock_*` calls answer ENOTSOCK).
Linear memory is sparse and copy-on-write per 64 KiB page.

### Toolchain

```
cabal 3.14.2.0, GHC 9.12.2 on a POSIX system (the WASI host uses the unix package); wabt
(wat2wasm, wast2json, wasm-validate) for the samples and the spec testsuite; wasmtime
(optional) as a differential oracle in samples/check.sh
```
