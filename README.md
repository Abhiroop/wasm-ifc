## wasm-ifc

Experiments with WebAssembly and information-flow control, in Haskell.

The pipeline is a single path: decode the binary into an untyped AST, *elaborate* it
(validation = type-checking, recovering the type indices), and run the resulting
intrinsically-typed AST on a small-step machine.

```
  bytes ──decode──▶ RawModule ──elaborate──▶ ModuleInst ──step machine──▶ result
   Codec.Wasm      Syntax.*    Validation.*   Runtime.*      Runtime.Interpreter
                  (untyped)    (validate +    (instances)    (total `step`)
                               recover indices)
```

The three layers follow one naming convention (with `Raw` for the decoder's untyped output):

* **Syntax** (`Syntax.*`): the program as written. Both the raw, unvalidated AST (`RawInstr`,
  `RawModule`, …) and the *intrinsically-typed* `Instr`/`Expr` — indexed by the value-stack
  shape, locals, labels and module shape they run within, so ill-typed programs are not
  representable.
* **Validation** (`Validation.*`): the type-level *shapes* the syntax is indexed by
  (`Validation.Shape`: `ModuleShape`, `MemShape`, `Append`, `Elem`), the singleton witnesses
  and decidable equality (`Validation.Reflect`), and the elaborator (`Validation.Elaborate`),
  which checks a whole decoded module and recovers its hidden type indices.
* **Runtime** (`Runtime.*`): the *instances* (`ModuleInst`, `FuncInst`, `MemInst`, the value
  containers) and the interpreter. `Runtime.Interpreter` is a total small-step abstract
  machine: a `Config` steps to the next `Config` (or finishes, or traps). Because only
  well-typed configurations are representable and `step` is total (enforced by
  `-Werror=incomplete-patterns`, no `error`/`unsafeCoerce`), the machine *is* the
  type-soundness argument — preservation by construction, progress by totality.

Naming: `Foo` is the static syntax (in `Syntax`); `FooShape` is its type-level abstraction
(in `Validation`); `FooInst (shape :: FooShape)` is the runtime instance (in `Runtime`).

### Layout

| Path | Contents |
|------|----------|
| `src/Syntax/`     | the program syntax: raw AST + intrinsically-typed `Instr`/`Expr`, base types |
| `src/Codec/`      | the binary decoder |
| `src/Validation/` | type-level shapes (`Shape`), singletons + decidable equality (`Reflect`), the elaborator (`Elaborate`) |
| `src/Runtime/`    | the small-step interpreter, the runtime instances, value/memory machinery, shared numerics |
| `app.old/`        | the original prototype, kept for reference (not built) |
| `app/Main.hs`     | the CLI |
| `samples/wat/`    | example programs (`.wat`); `samples/build.sh` compiles them with `wat2wasm` |

### Usage

```sh
cabal build
cabal run wasm-ifc -- invoke <file.wasm> <export> [args...]   # decode → elaborate → run
cabal run wasm-ifc -- check <file.wasm>                        # decode → elaborate only

samples/build.sh    # compile every sample .wat to .wasm  (needs wabt's wat2wasm)
samples/check.sh    # run every sample and check it against its expected result
cabal test          # run the typed-example smoke tests
```

### Status and limitations

Runs today: the numeric, comparison and conversion instructions; memory loads and stores
(including the narrow forms), `memory.size`/`memory.grow`; structured control, branches,
calls and globals; whole-module validation; one linear memory per module; exported functions
invoked from the CLI with integer arguments.

Not yet: information-flow control (the project's goal; `TODO.md` §F); imports and WASI
(`TODO.md` §H — only an isolated host scaffold exists); tables and `call_indirect`; the start
function (decoded, not run); exported globals and memories (decoded, not reachable from the
CLI); typed `select` (`0x1C`); multiple memories; bulk memory, passive data segments,
reference and SIMD types. Linear memory is sparse and copy-on-write per 64 KiB page.

### Toolchain

```
cabal 3.14.2.0, GHC 9.12.2
```
