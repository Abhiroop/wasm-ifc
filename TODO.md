# wasm-ifc — work plan

Internal implementation checklist and audit backlog. This is the single home for "what's
missing / what to improve"; it replaces the scattered notes that used to live in `discussions/`
and in `-- TODO`/`-- XXX` comments in the source. Consumer-facing docs (`README.md`,
`CHANGELOG.md`, Haddock) stay in the tree; everything internal lives here.

## How to use

Each item: `- [ ] **[Pn·area]** Title — what & why. (file refs)`. Check items off as you land
them. **Exception (Daniel & Abhiroop's workflow for the IFC merge):** the open IFC design points
live as `TODO(ifc Pn)` comments in the code, beside the construct each one concerns;
`grep -rn 'TODO(ifc' src test` is that work list, and solving them all is finishing the merge.
Priorities:

- **P0** — defects that crash or misbehave on plausible input; fix first.
- **P1** — high value: robustness, the tooling that enforces `STYLE.md`, core test coverage.
- **P2** — refactors, readability, docs, medium features.
- **P3** — larger roadmap, research, and nice-to-haves.

## Relationship to STYLE.md

`STYLE.md` is the style reference. **One deliberate override applies to this whole project:**
its §2 "cap type-level machinery" invariant does *not* bind the intrinsically-typed core
(`Syntax.Instructions`, `Validation.*`, `Runtime.*`) — GADTs/`DataKinds`/type families/
singletons *are* the point here (they make ill-typed WebAssembly unrepresentable and turn the
interpreter into a type-soundness artifact). The rest of `STYLE.md` (totality, naming,
tests, tooling, records, deriving strategies, comments-say-why) **does** apply, and the
*spirit* of §2 still applies inside the type-level code: prefer the simpler type-level encoding
when there is a choice. Recorded as the signed-off override in `STYLE.md` §11 (item **E1**).

## Plan (September 2026): robustify what exists, audit against the spec, finish WASI

Sequenced work packages. Each lands as separate commits gated on the `-Werror` build, `cabal test`,
fourmolu, hlint and `samples/check.sh`. Items marked **[decision]** need Daniel's call first.
**Status (2026-09-11):** O1–O5, P0, R1, R2, R4, G1 and W0–W7 are done (WASI: 72/72 in the official wasi-testsuite; spec testsuite 23,306 assertions pass, 0 fail, 960 skipped as feature gaps); R3 and R5 are done except the items
marked **[decision]** and the ones that wait on a feature; open: the decisions, including the pre-IFC slice proposal under §F.

### O — code organisation (2026-09-10, Daniel's top priority)

- [x] **[O1·syntax]** `MemArg` is an immediate, not a type: moved with `Signedness`, `NumWithSign`
  and `NarrowWidth` to `Syntax.Immediates`; `Syntax.Types` holds only types.
- [x] **[O2·syntax]** One module per syntactic thing, raw and typed side by side: `Syntax.Module`
  (`RawModule` + `Module shape`, with `RawImport`, `RawMemory`, `RawTable`, `RawData`, `RawElem`,
  `Export`, and the typed `DataSegment`/`ElementSegment`), `Syntax.Functions` (`RawFunction` +
  `Function`/`Functions`, with `FunctionBody`), `Syntax.Globals` (`RawGlobal` + `Global`/`Globals`).
  The one-record modules `Expressions`, `Memories`, `Tables`, `Imports`, `DataSegments`,
  `Elements` are gone. `RawExpr` lives with `RawInstr`.
- [x] **[O3·syntax]** `Syntax.Indices` carries no commented-out code.
- [x] **[O4·pipeline]** Validation and instantiation are separate stages with separate error types:
  `Validation.Elaborate.elaborateModule :: RawModule -> Either ElabError SomeModule` only checks
  (bodies, constants, segment offsets, indices, the start function's type);
  `Runtime.Instantiate.instantiate :: SomeModule -> Either InstantiationError SomeModuleInst`
  links imports, allocates from the shape, places segments and runs the start function. The
  spec-suite runner now decides `assert_unlinkable` and `assert_uninstantiable`, and checks that
  `assert_invalid`/`assert_malformed` modules are rejected by the stage the assertion names.
- [x] **[O5·naming]** Distinct words for distinct concepts (Daniel: `Function` vs `Functions` are
  one letter apart; `RawData` does not match `DataSegment`). "One entry per member of an index
  space" is now a *space*: `FunctionSpace` (`NoFunctions`/`Defined`/`Imported`), `GlobalSpace`
  (`NoGlobals`/`Declared`) in Syntax; `FuncSpaceInst`, `GlobalSpaceInst`, `MemSpaceInst`,
  `TableSpaceInst`, `DataSpaceInst`, `LocalSpaceInst` in Runtime (each the instance of one index
  space, next to the singular `FuncInst`/`MemInst`/`TableInst`). Raw segments are named after their
  typed forms: `RawDataSegment`/`DataSegment`, `RawElementSegment`/`ElementSegment`. The module
  records agree on field names: `functions`, `globals`, `memories`, `tables`, `dataSegments`,
  `elementSegments` in `RawModule`, `Module` and `ModuleInst`/`Store`. Left as they are, being the
  spec's own nonterminals: `FuncType`, `FuncInst`, `MemType`, `MemShape`, `MemInst`, `MemArg`,
  `ModuleFuncs`/`ModuleMems`.

### P0 — spec violations found by audit probes (2026-09-09, each reproduced on a hand-written `.wat`)

- [x] **[P0·runtime]** `call` passes arguments in reverse: `sub(10, 3)` through a two-parameter
  call computes `3 - 10`, and a call to a function whose parameters have *different* types
  (`i32, i64`) is rejected outright ("arguments not on the stack"). Root cause: the shape's
  `FuncType ps rs` keeps `ps` in declared order, but a stack-segment type is top-first, so the
  elaborator's `matchPrefix psS stackIn` and the interpreter's `stackToLocals args` both read the
  segment backwards (same-typed parameters are silently swapped, mixed ones rejected). Fix, as one
  invariant: **every type-level `[ValType]` that describes a stack segment is in stack order (top
  first)**, including the params/results of `FuncType`/`BlockType` inside shapes; declared order
  survives only in the decoded `Syntax` and in locals. Conversions happen at the boundaries only:
  `reflectCtx`/`reflectStack` reverse the decoded lists before promoting; a hand-rolled
  `ReverseOnto :: [ValType] -> [ValType] -> [ValType]` (structural accumulator, no lemmas) with its
  `sReverseOnto` gives `FrameLocals = ReverseOnto ps declared`, so local 0 is the first parameter;
  `ICall` builds the callee's locals with `reverseOnto :: ValueStack ps -> LocalInsts acc ->
  LocalInsts (ReverseOnto ps acc)`; the entry path (`buildArgs`/`renderResults`) reverses. Tests:
  two-parameter `sub` through a call, the mixed-type call, a two-result function, and the
  hand-written `Runtime.Examples`.
- [x] **[P0·runtime]** `select` keeps the wrong operand: it returns the *second* value when the
  condition is non-zero (spec: the first). One-line swap in `step`; test and sample.
- [x] **[P1·runtime]** `f32/f64.ceil/floor/trunc/nearest` go through `Integer`, so NaN becomes ∞,
  ∞ becomes garbage and `-0.5` rounds to `+0.0` instead of `-0.0`. Implement the four with explicit
  NaN/∞ pass-through and sign-of-zero preservation (`nearest` keeps ties-to-even). Tests per corner.
- [x] **[P1·runtime]** `memory.grow` never fails and allocates without bound: growing a 1-page
  memory by 70000 pages returns `1` and allocates ~4.5 GB (spec: return `-1` when the new size
  would exceed the declared maximum or 65536 pages). `MemInst` carries its `Limits` at the term
  level (the `MemShape` index already names them); `growMemory` returns `Maybe`; `IMemGrow` pushes
  `0xFFFFFFFF` on failure. Test.

### R1 — a conformance harness, so this class of bug cannot hide again

- [x] **[P1·test]** **Spec-test runner** over the official WebAssembly test suite: wabt's
  `wast2json` (installed, 1.0.27) turns each `test/core/*.wast` into `.wasm` modules plus a JSON of
  `assert_return`/`assert_trap`/`assert_invalid`/`assert_malformed` commands. A Haskell runner (a
  second test-suite) executes them for the supported subset — `i32`, `i64`, `f32`, `f64`,
  `conversions`, `select`, `call`, `block`, `loop`, `br`, `br_if`, `br_table`, `return`,
  `unreachable`, `local_get/set/tee`, `global`, `memory`, `load`, `store`, `align`, `nop`, `stack`,
  `labels`, `fac`, `forward` — skipping modules that need unsupported features and reporting
  counts. Vendor the suite under `test/spec/` and pin its commit.
- [x] **[P1·cli]** Typed arguments and results on the entry path (needed by the runner and by the
  float samples): parse each argument at its parameter type — `i32`/`i64` as integers (also
  `0x…`), `f32`/`f64` as decimals, `nan`, `inf` and bit patterns (`nan:0x…`) — replacing
  `[Integer]`; render results the same way. `runModuleFunction` returns a `RunError` sum and typed
  values; `app/Main.hs` renders them.
- [x] **[P1·test]** `wasm-validate` (installed) as a second oracle for the *elaborator*: every
  sample and fixture our elaborator accepts must validate, and every module `wasm-validate` rejects
  within our subset must be rejected (a script over `samples/` and the fixtures).
- [x] **[P2·test]** Property tests over *generated* well-typed modules (hedgehog): elaboration
  accepts them; results agree with the oracle.
- [x] **[P2·test]** `wasmtime` (48, in `~/.wasmtime/bin`) is a differential oracle for the samples:
  `check.sh` runs every integer-valued check through `wasmtime run --invoke` and every trap check
  must trap there too (floats and negative arguments are outside what its CLI takes).

### R2 — decoder audit against the binary format (spec §5)

- [x] **[P1·decoder]** LEB128 bounds: `u32` ≤ 5 bytes, `s32` ≤ 5, `s33` (block types) ≤ 5, `s64` ≤
  10; reject non-zero/non-sign unused bits in the last byte. `i32.const` currently reads an `s64`
  and truncates; give it a real `s32` reader.
- [x] **[P1·decoder]** Invalid UTF-8 in a name crashes: `decodeUtf8` throws a pure exception that
  `runGetOrFail` cannot catch; use `decodeUtf8'` and `fail`.
- [x] **[P1·decoder]** Section order and uniqueness: ids must increase and appear at most once
  (custom sections anywhere); a duplicate section currently overwrites silently.
- [x] **[P1·decoder]** Code entries: `isolate` each function body with its declared size (read and
  ignored today), so a body/size mismatch is a decode error.
- [x] **[P2·decoder]** The reserved memory-index byte of `memory.size`/`memory.grow` must be `0x00`
  (read and ignored today).
- [x] **[P2·decoder]** Resource bounds: a six-byte input can declare 2³² locals or a 4 GB memory
  minimum. Cap total locals per function (document the bound) and either cap initial memory or
  allocate it lazily (ties in with the `memory.grow` item).
- [x] **[P2·decoder]** A hand-assembled byte fixture for each new rejection.

### R3 — validation audit against the validation rules (spec §3)

- [x] **[P1·validation]** Module-level checks missing today: memory limits well-formed (`min ≤ max`,
  `max ≤ 65536`); at most one memory (the MVP rule — today several are accepted and only the first
  is used); export names pairwise distinct; export indices in range for functions, globals *and*
  memories at elaboration time (today only functions, and only when invoked); the start function's
  type is `[] -> []`.
- [x] **[P1·style]** `ElabError` with structured fields (STYLE §3): the offending instruction and,
  where relevant, expected/actual types or indices — instead of formatted `String`s. Tests then
  assert on constructors, not substrings.
- [ ] **[P2·validation]** Global initialisers: `global.get` of an imported immutable global becomes
  legal once imports exist (W1); constant-only until then.

### R4 — interpreter audit against the execution rules (spec §4)

Beyond P0, mostly *verification*; the spec-test runner (R1) is the instrument.

- [x] **[P2·runtime]** Integer→float conversions: confirm `fromIntegral :: Word64 -> Float/Double`
  rounds to nearest-even at every magnitude (the spec requires it; pin with a property against the
  oracle).
  **Covered:** the spec's `conversions.wast` now runs in full (603 assertions, including every
  i64→f32/f64 rounding case) and passes.
- [x] **[P2·runtime]** Document the spec-permitted choices: NaN handling in `min`/`max` (we keep the
  operand), `nearest` ties-to-even (Haskell's `round` agrees).
  **Done** in the code: `wasmMin`/`wasmMax` (NaN handling) and `roundWith` (ties-to-even).
- [x] **[P3]** `runFor :: Int -> …`, a fuel-bounded runner for tests (G1). Done 2026-09-11: `runFor`
  in `Runtime.Interpreter` returns `Fuelled = Halted | OutOfFuel`; `test/Examples.hs` runs an
  endless `loop (br 0)` under a budget, the one test that states termination directly.
- [x] **[P1·runtime]** Call-stack exhaustion is a trap, not a crash (spec §4.4.8: an implementation
  may bound the stack, but exhaustion must trap). A runaway recursion used to grow the heap-allocated
  `Control` stack until memory ran out. Done 2026-09-11: each `CallBoundary` caches its activation
  depth; a call past `callDepthBound` (10 000 activations) traps with `CallStackExhausted`; the spec
  runner serves `assert_exhaustion` (the 5 skipped cases in `call`, `call_indirect`, `fac` now pass);
  a unit test pins the bound exactly (depth 10 000 runs, 10 001 traps).

### R5 — style and hygiene (no behaviour change; interleave when touching a file)

- [x] **[P2·style]** Plain record field names (STYLE §7): `env.shape`, `store.globals`,
  `inst.funcs`, `m.exports`, `e.name`, the `FrameShape`/`MemShape`/`ModuleShape` fields, and the
  decoder's `typeSection`/`codeSection`/…; the three record updates that became ambiguous under
  `DuplicateRecordFields` construct the record instead.
- [x] **[P2·test]** Move `Runtime.Examples` out of the library into `test/` (only the tests use it).
- [x] **[P2·ci]** Run CI on every branch (today only `main` and pull requests, so this branch has
  never been through it).
- [x] **[P2·repo]** Remove the committed Agda interface file `Formalisation/WASM-IFC.agdai` (a
  213 KB build artifact) and ignore `*.agdai`.
- [x] **[P2·style]** The constructor operators `:.`, `:#`, `:&` are blessed in STYLE §11 (cons-like
  constructors of list-shaped GADTs; the hand-written examples read as instruction sequences).
- [~] **[P3·naming]** Tag-style names: `Narrow8/16/32` are now `OneByte/TwoBytes/FourBytes` and the
  control-stack entries `EntryBoundary/BlockLabel/LoopLabel/CallBoundary` (the `F` was a leftover
  of the old `Frames` name). Left as is: `ANil/ACons` (the family's Nil/Cons convention) and the
  one-letter `m f l s` in the `Instr` constructor signatures (spelling them out doubles every
  line).
- [ ] **[P3·meta]** **[decision]** cabal `author`/`maintainer` (still Abhiroop), `synopsis`,
  `CHANGELOG` date.

### W — finish WASI (supersedes the H-list below; its open design questions are resolved here)

W0 goes first because a hello world needs its string in memory; W1–W4 change the audited core and
go in after P0 and the spec runner exist to guard them.

- [x] **[W0·decoder+runtime]** Active data segments: decode section 11 (`0x00 expr bytes`: memory
  0, constant `i32.const` offset; `fail` on passive and other forms) into `RawModule.dataSegments`;
  elaboration checks that offset + length fit the memory's minimum; instantiation writes the bytes.
  (Since O4: validation checks the offset is a constant and a memory exists; fitting is instantiation's.)
- [x] **[W1·decoder]** Import section: `Import {module, name, desc}` with `ImportDesc = ImportFunc
  TypeIdx`; `fail` on imported tables/memories/globals. The function index space is imports ++
  defined (calls and exports already index that space).
- [x] **[W2·types]** Host functions typed by construction: a `WasiFunc (ft :: FuncType)` GADT
  (`FdWrite :: WasiFunc ('FuncType '[I32,I32,I32,I32] '[I32])`, `ProcExit :: WasiFunc ('FuncType
  '[I32] '[])`), and `FuncInst` gains `HostFunc :: (ModuleMems mod ~ (m ': ms)) => WasiFunc ft ->
  FuncInst mod ft` — a WASI import is unrepresentable in a module without a memory, and a host
  function at the wrong type cannot be built. `runWasiCall :: WasiFunc ('FuncType ps rs) ->
  ValueStack ps -> MemInst m -> IO (WasiOutcome rs m)`: the arguments arrive exact by construction
  (no `[Word32]`), and `ProcExit`'s `rs ~ '[]` says it never resumes.
- [x] **[W3·machine]** The effect-request boundary, first-order: `StepResult` gains `HostCall ::
  WasiFunc ('FuncType ps rs) -> ValueStack ps -> Store mod -> Suspended mod res rs -> StepResult mod
  res`, where `Suspended` is the caller's continuation *as data* (locals, saved stack, remaining
  code, control stack) and `resumeWith :: Store mod -> ValueStack rs -> Suspended mod res rs ->
  Config mod res` rebuilds a configuration. `step` stays pure and total. The pure `run` returns
  `Either Trap (Halt mod res)` with `Halt = Finished (ValueStack res) | AwaitingHost …`, so a test
  can drive host calls with a fake `fd_write` purely; `runIO` performs `AwaitingHost` through
  `Runtime.Wasi`, writes the memory back, resumes and loops; `proc_exit` ends in `Exited code`.
- [x] **[W4·elaborate]** Imports: resolve `(wasi_snapshot_preview1, name)` to a `SomeWasiFunc`;
  `decideEquality` the declared type's singleton against the function's; require a memory; anything
  else is `UnsupportedImport`. `FuncInsts` = host entries first, then the defined functions.
  (Since O4 this linking is `Runtime.Instantiate`'s; validation keeps an import as `Imported`.)
- [x] **[W5·entry]** `wasm-ifc run file.wasm`: validate and run the start function if present, then
  the `_start` export through `runIO`; the process exit code is `proc_exit`'s. The existing
  `wasm-ifc file.wasm fn args…` stays pure and reports "module needs WASI; use run" on
  `AwaitingHost`.
- [x] **[W6·sample]** `samples/wasi/hello.wat` (imports `fd_write`/`proc_exit`, exports `memory`,
  data segment `"Hello, world!\n"`); `check.sh` compares stdout and exit code; plus the pure
  `AwaitingHost` test.
- [x] **[W7]** The complete Preview 1 interface (all 45 functions, `Runtime.Host`/`Runtime.Wasi`),
  a sandboxed file system on POSIX calls (`unix`), descriptor rights and flags, and the official
  `wasi-testsuite` as a submodule (`test/wasi/testsuite`, runner `test/WasiSuite.hs`): **72 of 72
  programs pass** (C, Rust, AssemblyScript). That is the evidence for the WASI-compliance claim.
  Prerequisites landed on the way: tables + `call_indirect` + element segments, bulk memory.

---

> **Status (2026-09):** §A–§D are done; §E and §C keep only the decisions that are Daniel's
> (cabal metadata, the Lean README stub, `exercises/`); §F is the roadmap (IFC first); §H is done
> (see the plan's W items). Nothing is blocked on tooling any more: wabt and wasmtime are installed.

## A. Correctness & robustness

Open P0/P1 correctness items live in the plan above (section **P0**); the list below is history.

- [x] **[P0·decoder]** Partial `!!` on a block's type index — now `nth` + `fail` on out-of-range.
  (`src/Codec/Wasm.hs` `getBlockType`/`nth`)
- [x] **[P0·decoder]** Partial `!!` on a function's type index — `assemble` now returns
  `Either String`; `toFunction` uses `nth` and `fail`s on out-of-range. (`src/Codec/Wasm.hs`)
- [x] **[P0·cli]** Partial `read` — CLI now uses `readMaybe` (a pure `Either String` pipeline) and
  `die`s on a non-integer argument. (`app/Main.hs`)
- [x] **[P1·runtime]** Effective-address overflow now traps — new `effectiveAddr` computes
  `base + offset` in `Int` (no 2³² wrap); an over-large address traps in `readBytes`/`writeBytes`.
  (`src/Runtime/Interpreter.hs`, `src/Runtime/MemInst.hs`)
- [x] **[P1·runtime]** Float `min`/`max` signed-zero handled explicitly (`min +0 -0 = -0`,
  `max +0 -0 = +0`); NaN still propagates (spec-permitted). (`src/Runtime/Numeric.hs`)
- [x] **[P1·decoder]** Function/code section length mismatch now `fail`s (was silent `zipWith`
  truncation). (`src/Codec/Wasm.hs` `assemble`)
- [x] **[P1·cli]** `main` now exits non-zero on any failure (via `die`); also catches a missing/
  unreadable file (was an uncaught `IOException`). (`app/Main.hs`)
- [x] **[P2·runtime]** `readBytes` now uses `UV.toList (UV.slice …)` (no partial `UV.!`).
  (`src/Runtime/MemInst.hs`)
- [x] **[P2·runtime]** `IBrTable` uses a total `case drop … of` instead of guarded `!!`.
  (`src/Runtime/Interpreter.hs`)

## B. Testing

- [x] **[P1·test]** Test suite migrated to `hspec`. (`test/Spec.hs`, `cabal.project` sets
  `tests: True` so the deps resolve by default.)
- [x] **[P1·test]** Haskell-level tests (no `wat2wasm`): elaborator acceptance and rejection
  (stack underflow, result mismatch, out-of-range local, operand type mismatch, the witness
  refinements), every trap (divide-by-zero, OOB, `unreachable`, invalid conversion), dead-code
  accept/reject under the polymorphic stack, and hand-assembled decoder byte fixtures for the
  malformed-input paths (bad magic/version, A1 block type index, A2 function type index, A6
  function/code length mismatch, unknown opcode). Built from `RawModule` values and raw bytes.
- [x] **[P1·test]** Property tests (`hedgehog`): `Runtime.Bytes` word↔bytes round-trips (32/64)
  unsigned `intDiv32` vs host `div`, and the conversion round-trips (extend/wrap, reinterpret,
  promote/demote, convert/trunc). (Generated-module properties still open.)
- [x] **[P2·test]** — **BLOCKED:** `wasmtime` is not installed, so no external `--invoke` oracle
  yet; `samples/check.sh` still uses hand-written expected values.
  **Resolved (2026-09):** installed; see the plan's R1 item.

## C. Tooling & build hygiene

- [x] **[P1·build]** STYLE cabal baseline adopted: `GHC2024`, `default-extensions`
  (`OverloadedStrings`/`OverloadedRecordDot`/`NoFieldSelectors`/`DuplicateRecordFields`), extra
  warnings (`-Wcompat -Wincomplete-record-updates -Wpartial-fields -Wredundant-constraints`).
  `-Wincomplete-uni-patterns` deliberately **omitted** (false-positives on GADT-total binds; noted
  in the cabal). Builds clean, incl. `-Werror`.
- [x] **[P1·build]** fourmolu (0.19) installed via `cabal install`; `fourmolu.yaml` pinned; whole
  tree formatted (STYLE §9). Build/`-Werror`/tests/hlint stay green. Trade-off accepted: it
  collapses hand-alignment and blank-line grouping inside the big GADTs, and expands `:.` operand
  chains (e.g. `Runtime.Examples`) one-per-line.
- [x] **[P1·build]** hlint set up (`.hlint.yaml`) and clean — `hlint src app test` reports no
  hints. (Declined the "avoid lambda using infix/section" family per STYLE §4, recorded in the
  config.)
- [x] **[P1·build]** Explicit deriving strategies (`deriving stock`) on every type; index newtypes
  dropped the unused `Enum` + `GeneralizedNewtypeDeriving`.
- [x] **[P2·build]** `-fno-cse` removed (traced to an "Uncommitted stuff" junk commit, no
  rationale). Also removed the stale top-level `Makefile` (hardcoded `/home/abhiroop/…` path,
  obsolete CLI).
- [x] **[P2·build]** CI added (`.github/workflows/ci.yml`): `cabal build all --ghc-options=-Werror`
  + `cabal test all` on GHC 9.12.2.
- [ ] **[P2·meta]** — **DEFERRED (docs):** cabal `author`/`maintainer` still stale; `synopsis`/
  `description` empty; `CHANGELOG.md` 0.1.0.0 entry undated.

## D. Refactors & readability (within the type-level design; STYLE simplicity spirit)

- [x] **[P2·readability]** Dense function-body signature — introduced the `FunctionBody mod locals
  rs` synonym; `FuncInst` now reads `LocalInsts declared -> FunctionBody mod (ps ++ declared) rs`.
  (`src/Runtime/Interpreter.hs`)
- [x] **[P2·design]** Typed conversions — the untyped `Val` bridge is gone. `convertVal ::
  ConvertOp from to -> HostType from -> Either Trap (HostType to)` is typed by the indexed
  opcode (which the soundness pass below made possible); `Runtime.Values` is deleted and its
  signed/unsigned views live in `Runtime.Numeric`. Demote/promote now use `double2Float`/
  `float2Double`, exact for NaN/∞ where `realToFrac` only is when GHC's rewrite rules fire.
  (`src/Runtime/Convert.hs`)
- [x] **[P2·modules]** Explicit export lists added to `Runtime.MemInst` (hides the constructor +
  `pageSize`; dropped dead `memoryBytes`), `Runtime.Numeric`, `Syntax.*`
  leaves, and `Syntax.Instructions`. `Syntax.Types`/`Validation.Shape` kept **open** (documented:
  single-constructor `Sing` constructors need an open import).
- [x] **[P2·records]** `NoFieldSelectors` + `DuplicateRecordFields` adopted; selector uses rewritten
  to `OverloadedRecordDot`. The duplicate `globalType` selector and the generic
  `signature`/`locals`/`body` selectors no longer pollute the top level.
- [x] **[P2·decoder]** `Codec.Wasm`: explicit `Data.Binary.Get` import; redundant parens stripped.
- [x] **[P3·naming]** `SomeModuleShapeS` → `SomeModuleShape`. (`src/Validation/Reflect.hs`)
- [x] **[P1·soundness]** `IsNum` witness added (this had been wrongly deferred to "when ref/vec
  land" — the deferral *was* the gap). Every numeric instruction now carries `IsNum`/`IsInt`/
  `IsFloat`, never a bare `Sing (t :: ValType)`, so the constraint holds by construction and does
  not rely on `ValType` being all-numeric. Fixes a latent gap (`funcref.add` would type-check once
  ref types exist) and a live bug (`IEqz` accepted `f32.eqz`). `decideNum` + `requireNum` refine in the
  elaborator.
- [x] **[P1·soundness]** Closed the remaining representable-illegal-states in the typed `Instr`
  (per the "soundness is never deferred" invariant, STYLE §2):
    - **Signed float div/compare** — `IDiv`/`ILt`/`IGt`/`ILe`/`IGe` now carry a `NumWithSign t`
      witness (`IntsHaveSign`/`FloatsHaveNoSign`); a signed float comparison/division is unrepresentable.
      `eq`/`ne` (no signedness) split off to `numEqNe`.
    - **`IConvert` op/type mismatch** — `ConvertOp` is now a GADT indexed by `from`/`to`, so the
      opcode *is* the type evidence; `IConvert :: ConvertOp from to -> …` (no separate witnesses).
    - **Arbitrary narrow width** — `ILoadN`/`IStoreN` carry a `NarrowWidth t` witness (8/16 for any
      int, 32 for i64 only) instead of a raw `Int`.
    - **Over-alignment** — the elaborator now rejects `2^align > access width` (spec validation
      rule), which was previously skipped.

## E. Documentation (consumer-facing)

- [x] **[P1·docs]** Record the type-level override in `STYLE.md` §11: the intrinsically-typed core
  deliberately uses GADTs/`DataKinds`/type families/singletons to model WASM's type system as an
  unrepresentable-illegal-states soundness artifact; §2's cap is overridden for those modules,
  while the simplicity spirit still applies.
- [x] **[docs]** README layout table referenced `src/Old/`; the reference prototype is `app.old/`.
  Fixed in this pass.
- [x] **[P2·docs]** README: add a "Status / limitations" section (single memory; no
  tables/`call_indirect`; no imports; integer CLI args only; start function not run; IFC pending).
- [ ] **[P2·docs]** `Formalisation/wasmifc/README.md` is a GitHub template stub ("remove this
  section…") — replace with real content or remove. (Separate Lean subproject.)
- [ ] **[P3·repo]** `exercises/TypeExercise.hs` is a scratch learning file, not in the build —
  decide: keep as a labelled learning reference, move out of the repo, or delete.

## F. Feature roadmap & known limitations

- [ ] **[P2·epic·ifc]** **Information-flow control — the actual goal.** Security-level typing on
  the typed layer (labels on value types / the stack; a noninterference argument).
  **Started (2026-09-11):** Abhiroop's first cut is merged and ported onto the current core as
  a parallel, not-yet-executed GADT: `Syntax.TypesIFC` (`SecLevel`, `LValType = ValType :~
  SecLevel`, `CanFlowInto`, the join `:/\`) and `Syntax.InstructionsIFC` (today's `Instr` over
  `[LValType]`; numeric results take the join of their operands' labels). `Append` is poly-kinded
  for it. The open design points are `TODO(ifc Pn)` comments beside the code they concern
  (`grep -rn 'TODO(ifc' src test`), grounded in the SecWasm paper (hybrid: static except the
  memory read check; per-byte flow-sensitive memory labels with `load ℓ`/`store ℓ` immediates;
  function types with a pc bound; flow-sensitive pc stack, which we recommend flattening to one
  pc per block computed by a pre-pass; TINI). P0 — parallel GADT vs one `Instr` generalised over
  the label; the pc label; where labels come from (a custom section; inferred store labels,
  `Low` default for loads). P1 — the pc index and `LabelShape`; `select`; flow witnesses
  (`FlowsInto`, `StackAtLeast`) on sets, stores, branches, calls; per-byte memory labels in
  `MemInst` and the dynamic load check + trap in `step`; labelled `FuncType`s and globals;
  labelled WASI signatures (our extension). P2 — singletons for `SecLevel`; explicit relabel;
  bulk-memory label rules; the noninterference property test; next examples. P3 — naming, the
  lattice, the termination channel, the flow-sensitive upgrade.
  References (folded in from the old `discussions/READING_LIST.md`):
  - SecWasm — the IFC model we follow: <https://plas2022.github.io/files/pdf/SecWasm.pdf>
    Full version with every rule (T-IF, T-LOOP, T-SELECT, the sets, E-*-TRAP):
    <https://www.cse.chalmers.se/research/group/security/secwasm/>. Read 2026-09-11; the
    `TODO(ifc …)` comments cite its rules by name.
  - WANILLA (CCS '25) — noninterference via SMT: <https://arxiv.org/pdf/2509.08758>
  - HLIO — hybrid IFC: <https://www.cse.chalmers.se/~russo/publications_files/hybrid-icfp2015.pdf>
  - In-place interpreter for WASM (perf, later): <https://dl.acm.org/doi/pdf/10.1145/3563311>
  - [x] **[decision]** **Pre-IFC base — proposed slice (2026-09-11; Daniel took it, merge started the same day).** The spec suite passes every
    assertion it runs (0 failing); all 960 skips are feature gaps, not defects, and 72/72 WASI
    programs from real compilers exercise `br_table`/`call_indirect`/memory in anger — strong
    evidence against "silly" bugs of the reversed-arguments kind. Proposal: **merge IFC on this
    base now**; only the exhaustion trap above was worth doing first. Known coverage holes, for the
    record, none of them worth closing before IFC:
    - `br_table` (150), `select` (119) and `global` (59) assertions skip because one
      reference-typed function rejects the script's single module; their numeric semantics are
      still covered by `switch`/`br`/`labels`, the assertions that do run, and the WASI programs.
      Closing them needs reference value types — a `ValType` change that collides head-on with
      IFC's own changes to values — so after the merge, if ever.
    - Imports of globals/memories/tables and cross-module linking (`imports` 151, `linking`
      excluded, `data`/`elem` partial): orthogonal to the IFC model (SecWasm is single-module);
      host calls are already the labelled I/O boundary. The `global.get`-in-initialiser item above
      waits on this.
    - Reference types, SIMD, multi-memory, text-format `assert_malformed`: irrelevant to IFC.
- [x] **[P2·feature]** Run the start function after instantiation — it is decoded (`start`)
  but never invoked.
  **Done (2026-09):** validated (in range, `[] -> []`) and run as the last step of instantiation.
- [x] **[P2·feature]** Expose exported globals to the CLI and the spec runner. Done 2026-09-11:
  `readGlobalExport` in `Runtime.Module`, CLI `get <file> <global>`, and the spec runner now serves
  the `get` action (+3 assertions). Still open: exported memories (no scalar rendering yet).
- [x] **[P3·feature]** Tables + `call_indirect` + element segments (2026-09-10; a table entry is a
  typed `SomeFuncRef`, the indirect call's type check is a `decideEquality`). Open: the `table.*`
  instructions, `elem.drop`, passive/declarative element segments, table imports.
- [x] **[P3·feature]** `select` with an explicit result type (opcode `0x1C`). Done 2026-09-11:
  decoded as `SelectTyped [ValType]`, validated to one numeric type the operands must match
  (`InvalidSelectArity` otherwise). The reference-typed cases in `select.wast` still skip, since
  they need reference value types.
- [x] **[P3·feature]** Float CLI arguments (`app/Main.hs` and `runModuleFunction` take
  `[Integer]`).
  **Done (2026-09):** arguments are parsed at the export's parameter types (`invoke`).
- [ ] **[P3·feature]** Multi-memory (currently memory 0 only, via the `ModuleMems ~ (m ': ms)`
  non-empty constraint).
- [ ] **[P3·feature]** Reference types & SIMD (`V128`) value types. `ValType` is flat and ready to
  extend, but `HostType` and the value stack would need reference/vector representations.
- [x] **[P3·feature]** Bulk memory (`memory.copy`/`fill`/`init`, `data.drop`, passive data segments;
  2026-09-10). Open: imports of tables, memories and globals.
- [ ] **[P3·perf]** Linear memory is sparse and copy-on-write per 1 KiB chunk, and whole values
  load and store as words with no byte lists (2026-09-15, §I E6). Every store still copies a
  chunk; a mutable or growable representation that keeps `step` pure is §I's "E6 next".

## G. Soundness-artifact niceties

- [ ] **[P3]** `run` is the only partial (non-terminating) function — optionally add a
  fuel-bounded `runFor :: Int -> …` for tests and to make termination explicit.

## H. Import system + WASI (done — see the plan's W items)

WASI functions *are* imports, so the **import system is the prerequisite** ("natural
dependency"). The guiding constraint: **admit imports + IO without breaking the pure/total
`step`** (the soundness artifact). Solution: an **effect-request boundary** — `step` stays pure
and, when a `call` resolves to a host function, *yields a request* rather than doing IO; a thin
IO driver performs the effect and resumes. IO is quarantined to the driver + `Runtime.Wasi`.

Scaffold already landed (isolated, additive, non-churning): **`Runtime.Wasi`** — the WASI
Preview 1 host layer (`wasi_snapshot_preview1`): `fd_write`/`proc_exit`, errno subset, iovec
parsing over `MemInst`, and `runWasiCall :: WasiFunc -> [Word32] -> MemInst m -> IO
(WasiOutcome m)` (the driver's entry point). Builds under `-Werror`, hlint-clean.

The remaining pieces (H1–H6) and the open design questions are superseded by the **W** package
in the plan at the top of this file, which also resolves the questions: host imports are typed by
construction against a `WasiFunc (ft :: FuncType)` GADT; the request carries the whole `Store`; host
functions are a `HostFunc` case of `FuncInst` in the one function index space.

## I. Performance experiments — is an intrinsically typed interpreter necessarily slow?

Planned 2026-09-11 (Daniel + Claude), **not started**. Goal: empirical evidence for the claim
that intrinsic typing (GADT-indexed syntax, total small-step `step`) does not by itself make an
interpreter slow. The argument the experiments must support has three separable parts, and
every measurement below is designed to attribute cost to exactly one of them:

1. **The typing discipline itself.** What survives GHC's type erasure is only the *witnesses*:
   the unary `Elem` index for `local.*`/`global.*`/`call` (`getLocal`, `getFunc` walk a list:
   O(index)), the `Append` spine at block/call boundaries (`splitStack`, `appendWith`), the
   `Sing` of a block type, and the `decideEquality` in `call_indirect`. Nothing else is
   typing-induced; the indices on `Instr`/`Config`/`Control` are free.
2. **Our representation choices**, all orthogonal to typing: linked-list `ValueStack`,
   `LocalSpaceInst`, `GlobalSpaceInst`, `FuncSpaceInst` (a typed *vector* could carry the same
   index); lazy constructor fields (`:#`, `:&`, `Config`, `Store`); `IntMap` of immutable
   pages + `[Word8]` marshalling (the P3·perf item in §F); `Integer` in `Runtime.Numeric` /
   `Runtime.Convert`; one `Config` + one `Either` allocated per step.
3. **The host language**: GHC code generation and the GC, versus C/C++/Rust interpreters.

### Results so far (2026-09-11)

Two sweeps are recorded in `bench/results/`, one per commit, taken identically: 25 kernels ×
5 runtimes, CPU seconds, median of 5, each runtime's own start-up subtracted. Ours and wabt's
numbers are steady (median relative MAD 2.6 % and 2.2 %); the compiling tiers finish these
kernels inside their own start-up spread, so they print as `<0.05` and take part in no ratio.
Placing us against a JIT needs the real-program tier below, not these.

**Method correction (found during E2).** Absolute times are not comparable across sweeps on
this laptop: a fifteen-minute sweep runs everything about 2.5× slower than a two-minute one
(wabt's `fib`: 0.57 s in both long sweeps, 0.22 s in a short one), and a short run compared
against a long sweep once reported a 1.4–2.0× "speed-up" that was entirely clock state.
`run.py` now takes repetitions round-robin across runtimes and times other builds of ours
with `--binary`, so every A/B happens inside one sweep; an A/A check of one binary against a
copy of itself agreed within 2 %. Re-taken that way, the E0 ratios to wabt below hold: 1.6×
`loop-arith`, 1.8× `float` and `call-indirect`, 2.0× `fib`.

**E0 — the baseline was a laziness leak, and had nothing to do with types.** At `48f8e3c`
`i32.add` pushed `op a b` unevaluated onto a lazy `:#`, so a program retained every value it
had ever computed:

| `fib 30` | before (`48f8e3c`) | after (`f69ac27`) |
|---|---|---|
| max residency | 163 MB | 44 KB |
| productivity | 52 % | 98.7 % |
| GC share | 48 % | 0.0 % |

Making the running state strict bought **2.2× to 30×** across the kernels while every other
runtime stayed within 0.97–1.04× — the control that says the harness measured the change and
not the weather. Against wabt's plain C++ interpreter, the honest comparator for a
tree-walking interpreter:

| kernel | ours | wabt | ratio |
|---|---|---|---|
| `loop-arith` (pure dispatch) | 0.42 s | 0.27 s | 1.6× |
| `float` | 0.27 s | 0.15 s | 1.8× |
| `call-indirect` | 0.42 s | 0.24 s | 1.8× |
| `fib` (calls) | 1.12 s | 0.59 s | 1.9× |
| `br-table` | 0.41 s | 0.15 s | 2.7× |
| `memory-random` | 1.52 s | 0.45 s | 3.4× |
| `locals-64` | 0.89 s | 0.20 s | 4.6× |
| `memory-stream` | 8.96 s | 0.41 s | 21.7× |

So on everything that is neither memory-heavy nor deeply indexed we are **within a factor of
two to three of a C++ interpreter**, in Haskell, with the program's type-correctness carried
in the types. That is already most of what these experiments were meant to establish.

**Both remaining gaps are representational, and both are already named in §F.**

- *An indexed write rebuilds a linked list.* The sweeps isolate it exactly: `funcs-N`, which
  only ever reads a deep index, barely moves (0.32 s at index 2, 0.44 s at 64), while
  `locals-N` still runs 0.36 → 0.89 s because `setLocal` rebuilds N cons cells per store.
  Strictness alone collapsed that spread from 10× to 2.5×; the rest is E2's typed vector.
  `labels-64` (1.66 s against wabt's 0.10 s) is the same shape one level up — though wabt
  flatters itself there, folding empty blocks away at validation time.
- *A 4-byte store copies a 64 KiB page.* `writeBytes` rebuilds the page with `UV.//`, so
  `memory-stream` moves tens of GB to write 4 MB. This is the §F P3·perf item, now with a
  number on it.

### Hypotheses

- **H0 (hygiene)** — **confirmed, and larger than predicted** (`f69ac27`). Strict fields
  throughout the running state removed the residency entirely and bought 2.2–30×; no nursery
  tuning was needed. Cost attributed to (2).
- **H1 (erasure)** — the typed interpreter and a mechanically *erased* copy of it (same
  algorithm, plain ADTs, `[Value]` stack, dynamic tag checks) run within ±10 % of each other on
  every workload. This is the thesis question in its purest form. **Confirmed (E1)**, once two
  optimiser effects on the typed driver were removed: 0.97 in geometric mean.
- **H2 (witness residue)** — **refined twice.** E0's sweeps said a read at index 64 is cheap
  (`funcs-N` flat) while an update is not (`locals-N`, `globals-N`), because the list is
  rebuilt. E2 then showed the walk is not innocent either: swap the rebuild for a vector copy
  but keep walking the witness on every access, and it gets *slower*. The unary witness is
  cheap only next to a rebuild. Removing its cost means resolving the position once, at
  elaboration — E2b, which is a design decision rather than an experiment.
- **H3 (untyped Haskell is not faster)** — the Hackage `wasm` package (SPY/haskell-wasm 1.1.1,
  an untyped, spec-conformant Haskell interpreter) is not faster than ours on the same GHC and
  RTS; where it is, the profile points at representation (2), not typing (1). **Confirmed
  (E3):** ours is 4.6× faster.
- **H4 (positioning against industrial interpreters)** — after H0 we are within a small
  constant of the plain C++ interpreter (wabt `wasm-interp`) and the gap to the fast
  interpreters (wasm3, WAMR fast-interp, Pulley) is attributable by profiling to allocation/GC
  and dispatch, i.e. to (2)+(3). Report the gap honestly in ns/instruction; do not predict it.
  **Confirmed in kind (E4):** 1.3× from wabt on the kernels; 23–111× from the optimised
  interpreters on real programs, where memory is used most.
- **H5 (front end)** — decoding + elaboration (singleton-based validation) + instantiation are
  linear in module size and take milliseconds, not seconds, on the largest real modules we
  have (the 72 WASI-suite programs, C/Rust/AssemblyScript). Startup never dominates.
  **Confirmed (E5).**

### Workloads (three tiers)

- **T1 micro-kernels**, hand-written `.wat` in `bench/wat/`, *self-contained*: a zero-argument
  export `run` returning an `i32` checksum, sizes fixed by constants, so every runtime invokes
  them identically (wabt's `wasm-interp --run-export` takes no arguments; that is what forced
  the convention). Each targets one cost centre:
  `fib` (call + if), `loop-arith` (i32/i64 ALU loop, no calls: pure dispatch),
  `locals-N` / `funcs-N` / `labels-N` (the same loop with the hot local / callee / branch
  target at index N ∈ {0, 4, 16, 64}: the `Elem` and label-depth residue of H2, generated by
  `bench/gen.py`), `globals`, `memory-stream` (load/store sweep over 1 MiB), `memory-random`
  (LCG-addressed loads), `call_indirect`, `br_table`, `float` (f64 mandelbrot/nbody-style),
  `bulk` (`memory.copy`/`fill`). Existing `samples/wat` programs scaled up where they fit.
- **T2 real programs**, C compiled with wasi-sdk (**installed 2026-09-11**: wasi-sdk 34.0,
  clang 23.1, by `bench/tools/fetch.sh` into `~/.local/wasm-bench-tools/wasi-sdk`, pinned and
  checksummed): CoreMark and a PolyBenchC subset (2mm, 3mm, atax,
  gemm, jacobi-2d, …, the set used by the original Wasm paper and by Titzer's in-place
  interpreter paper, §F reading list). Flags: clang 23's own default (`-target-cpu
  generic`) already produces modules we validate. A probe using `printf` with floats,
  `malloc`, `memcpy`, 64-bit arithmetic and `sqrt` agreed with wasmtime on stdout and exit
  code at the default, at `-mcpu=mvp` plus our extensions, and at bare `-mcpu=mvp`. So no
  special flags so far — but run `wasm-ifc check` on every real program, since one probe does
  not cover CoreMark or PolyBench. Run through WASI `_start`, print a
  checksum, and *compare the checksum across runtimes* (a differential test for free).
  Prebuilt corpora as a fallback if compiling is a rabbit hole: wasmi's `benches/wasm/*.wasm`
  (coremark, tiny_keccak, rev_complement, regex_redux), wasm3's `coremark-minimal.wasm`.
- **T3 front end**: decode / elaborate / instantiate, timed separately, on the T2 binaries and
  the WASI-suite programs; plotted against module size and function count (H5).

### Comparators

- **C1** `wasm-ifc` at the commit under test, `-O1` (default) and `-O2`; `-fllvm` optional.
- **C2** `wasm-ifc-erased`: `Runtime.Interpreter` + `Syntax.Instructions` with every index
  deleted, `data Value = I32 !Word32 | …`, `[Value]` stack, tag checks at each pop (`I32 x`
  pattern, mismatch = crash) — the naive untyped Haskell interpreter one would write first.
  **C2b** the same without tag checks (validation assumed). Lives in `bench/erased/`, a
  frozen measurement device produced by textual deletion from C1 and reviewed as a diff, so
  the evaluation strategy is provably the same; never part of the library.
- **C3** Hackage `wasm` 1.1.1 driven in-process by a small `bench/drivers/HaskellWasm.hs`.
  Risk: its bounds (`bytestring <0.12`, `containers <0.7`, `mtl <2.3`) need `allow-newer` on
  GHC 9.12; if it does not build, H3 is answered by C2 alone.
- **C4** industrial interpreters, three that span the design space: wabt `wasm-interp`
  (installed; plain C++ stack machine), wasmtime **Pulley** (installed; register bytecode,
  Rust), **wasm3** (C, the fastest classic interpreter; builds with `gcc` alone, cmake is not
  installed, or `pip install pywasm3`). Optional: WAMR `iwasm` classic + fast-interp (prebuilt
  release tarball), wasmi (prebuilt release), Wizard (Titzer's in-place interpreter).
- **C5** JITs as the floor, not a fair comparison: wasmtime Cranelift and Winch (installed).

### Metrics and method

- Wall time and user+sys CPU per run, median of ≥ 10 after one warm-up, MAD reported;
  pinned with `taskset` to one P-core (the i7-12700H is hybrid: unpinned runs land on E-cores
  and are 2× off); CPU model, governor, GHC and runtime versions, flags and commit hash
  recorded in the results file. WSL2 is noisy: CPU time is primary, wall time secondary, and
  the final tables should be re-run on native Linux.
- **ns per dynamic Wasm instruction**, the unit the interpreter papers use: count steps with a
  bench-only driver over `step` (a `Stepped` counter; `runFor` already has the shape). The
  same program has the same count in every runtime, so the ratio is comparable.
- GHC-only: `+RTS -s` bytes allocated per instruction, GC share, max residency (needs
  `-rtsopts` on the bench executable only). Profiling with `--enable-profiling
  --profiling-detail=late` (late cost centres do not disturb optimisation), `-hT` heap by
  closure type, and `-ddump-simpl` on typed vs erased `step` to *show* what remains of the
  indices (the H1 argument in Core, not just in numbers).
- Subtract the empty-program baseline per runtime, and make every workload run ≥ 1 s so
  load/validate/JIT time is negligible where a runtime cannot report the run phase alone.

### Infrastructure to build

- [x] **[P2·perf]** `bench/` layout — done for T1 (`gen.py`, `wat/`, `wasm/`, `build.sh`,
  `results/<date>-<commit>.json`, `checksums.txt`). Still to add when their experiments start:
  `c/` (T2 sources over wasi-sdk), `erased/` (C2), `drivers/` (C3 and the step counter).
  `tools/fetch.sh` exists (2026-09-11) and installs wasi-sdk; wasm3, WAMR and wasmi are
  still to be added to it. `micro/` and `prototypes/` arrived with E2.
- [x] **[P2·perf]** The `tasty-bench` stanza — **deliberately not built.** Its purpose was an
  in-process A/B and per-phase numbers, but tasty-bench runs benchmarks one after another, which
  is what the thermal lesson below rules out; A/Bs stay process-level and interleaved
  (`run.py --binary`). In its place: two benchmark stanzas built only with
  `--enable-benchmarks`, `wasm-ifc-erased` (C2) and `wasm-ifc-phases` (E5), and ticky step
  counts (`bench/steps.py`, `run.py --ticky`) for nanoseconds per step.
- [x] **[P2·perf]** `bench/run.py` and `bench/report.py`. Runtimes are discovered, not
  configured; CPU time comes from `resource.getrusage(RUSAGE_CHILDREN)`; `taskset` pinning is
  opt-in via `BENCH_CPU` because on this hybrid CPU under WSL2 it slows runs without steadying
  them. Still missing from `report.py`: ns per dynamic instruction, which needs the step
  counter.
- [x] **[P2·perf]** `bench/smoke.sh`: every kernel once on C1 against `checksums.txt`.
  **Deliberately not wired into `gate.sh`:** a full pass takes minutes (the kernels are sized
  to be slow) and covers nothing the spec suite does not. It is the manual check to run after
  editing `gen.py` or the hot path. Cross-runtime agreement, which is the real check, happens
  in `run.py` and is what wrote `checksums.txt`.

### Experiment sequence (each step informs the next)

- [x] **E0** Hygiene baseline — done 2026-09-11, both sweeps kept (`48f8e3c`, `f69ac27`).
  See the results above.
- [x] **E1** Typed vs erased — done 2026-09-15 (`bench/erased`; BENCHMARKS.md §E1). At `-O1`
  the typed machine was ~20 % slower and allocated more. Ticky and the final STG traced it to
  GHC's handling of the driver, not to the types: `step` was not inlined, and then a `Config`
  and a `Stepped` were built per step for a join point. `INLINE step` and `-O2` on
  `Runtime.Interpreter` closed it — typed / erased = **0.97** (geometric mean, 24 kernels). The
  existential in `Config` was tested and ruled out (`-DEXISTENTIAL_CONFIG`). C2b, the untagged
  twin, not built: the tag checks are worth at most the 3 % the typed machine now leads by.
- [x] **E2** Witness-residue sweeps and the witness-indexed vector — done 2026-09-11, and the
  vector **lost**. Prototype kept as `bench/prototypes/e2-vector-locals.patch`, the interleaved
  four-way sweep as `bench/results/2026-09-11-e2-vector-ab.json` (worst MAD 5.1 %; spec and
  WASI suites green on it). Locals stored as a flat vector of packed words, still addressed by
  walking the `Elem` witness (and the type singleton, to unpack), ran **1.2–1.5× slower than
  the E0 cons list on every kernel, `locals-64` included** (0.355 s list, 0.544 s vector).
  Building the callee's frame in one allocation won back part of the call path, not the rest.
  With the rebuild gone, each access walks the witness *and* the singleton, and pays a fresh
  box per read and a vector copy plus closure per write. The micro-benchmark
  (`bench/micro/IndexedUpdate.hs`) that promised 1.6–6.5× indexed by a precomputed `Int` —
  exactly the part the prototype lacked. Reverted: the core keeps the by-construction list,
  so here soundness and speed point the same way.
- [x] **E2b** — approved by Daniel 2026-09-15 and done (BENCHMARKS.md §E2b): `Validation.Ref.LocalRef`
  carries position and type, built only from the witness; frames are packed-word vectors. Real
  programs 1.43×, deepest-local kernel 2.6×, all kernels 1.00× (calls lose 13–19 %: vector frame
  per call, a box per local read); erased twin mirrored, typed / erased 0.95. Globals still walk
  their witness, as real programs barely index them (the stack pointer is global 0). The note
  below is the design as proposed:
  The one vector design the data still supports resolves the
  position once, at elaboration, and carries the value type at the access site
  (`ILocalGet`/`Set`/`Tee` and `IGlobalGet`/`Set` holding a resolved reference, not a bare
  `Elem`). That moves one property — "this position is where the witness points" — from the
  types into an abstract type built only from the witness, the same kind of invariant
  `Data.Vector.Sized` keeps. Its ceiling is the micro-benchmark's, on local accesses only
  (about a third of the kernels' steps): perhaps 1.1–1.3× overall at shallow depth, more on
  deep frames. Worth it only if real compiled code (T2: wasi-sdk output has dozens of locals)
  shows deep frames matter.
  The store-side gap (mutable memory in `ST`, `Word32` numerics without `Integer`) is the §F
  P3·perf item, independent of E2b and the larger one measured (`memory-stream` 21.7× wabt).
- [x] **E3** C1 vs C3 — done: the Hackage `wasm` 1.1.1 interpreter (`bench/drivers/haskell-wasm`;
  builds on GHC 9.12 with relaxed bounds and no patch) is **4.6×** slower than ours in geometric
  mean over the kernels (1.6–12.4×). It serves no WASI, so the programs tier does not apply.
- [x] **E4** Positioning — done (BENCHMARKS.md §E4). Per machine step: wabt 1.3× ahead on the
  kernels (its Ubuntu build has no WASI, so kernels only); on real programs, paired per step against ours at
  small sizes, WAMR's interpreter 23×, Pulley 36×, wasm3 102×, wasmi 111×, Winch ~320×,
  Cranelift ~640×. Attribution by ticky and
  STG rather than a cost-centre profile, which would change the optimisation it measures. Our
  cost per step triples from kernels (6–14 ns) to programs (19–58 ns): memory, as H4 expected.
- [x] **E5** Front end — done: 129 modules, median 6.2 ms, worst 43 ms; the largest (2.2 MB,
  42,775 instructions) decodes in 14 ms, validates in 19 ms, instantiates in 1.2 ms; ~85 ms per
  100,000 instructions, correlation 0.90 (`bench/results/2026-09-15-e5-phases.csv`).
- [x] **E6** Representation improvements, one at a time, each measured — done for three
  (BENCHMARKS.md §E6): memory in 4 KiB chunks with word loads and stores (kernels 1.09×,
  programs **4.07×**); `INLINE step` (1.42×, 1.15×); `-O2` on the interpreter module (1.26×,
  1.08×). Together ~1.95× on kernels and ~5.1× on programs; CoreMark 8.4 s → 1.8 s.
- [ ] **E6 next [P3·perf, design question for Daniel]** Memory is still the largest cost on real
  programs: to keep `step` pure, every store copies a chunk. **1 KiB chunks done 2026-09-15**, on top
  of E2b: 1.46× on programs, 1.07× on kernels (`bench/results/2026-09-15-chunk1k-*`). Ticky and the RTS total on
  CoreMark and `pb-2mm`: chunk copies are 52–63 % of all allocation, the locals list 15–17 %
  (since removed by E2b), the run loop 11–15 %, word loads 9 % (a `Just` and a box each).
  Measured candidates, interleaved against `45a93c6` (`bench/results/2026-09-15-candidates-*`):
  1 KiB chunks 1.26× on programs and 1.04× on kernels (256 bytes: the same, so 1 KiB); `-O2` on
  `Runtime.MemInst` and `Runtime.Stack` 1.07× and 0.97× (marginal); a 64 MB nursery 0.70× and
  0.69× (rejected — GC was only 1–6 % of time, and the big nursery costs cache); E2b with 1 KiB
  chunks and that `-O2`, together, 2.11× and 1.17×. Candidates to measure:
  smaller chunks (a cheaper copy, a deeper map), a wider-fanout persistent trie, or memory
  threaded linearly or through `ST` behind an interface that keeps `step` a pure function.
- [ ] **[P3·perf]** Retake the final tables on native Linux on a desktop CPU before quoting any
  absolute number; the ratios were taken interleaved and should hold.
- [x] Write-up `BENCHMARKS.md` — done 2026-09-15.

### Risks

- Erasure fidelity (C2): any divergence in evaluation order contaminates H1; mitigate by
  textual derivation, diff review and the Core comparison.
- Real programs may use instructions we lack (nontrapping float-to-int, `ref.func` in element
  segments from newer clang); detect with `wasm-ifc check`, adjust `-m` flags, and record any
  workload we had to drop.
- Timing noise (WSL2, hybrid cores, turbo): pin, repeat, report CPU time, re-run natively.


### Performance while IFC lands (agreed with Daniel, 2026-09-15)

IFC's P0 and P1 reshape exactly what the remaining optimisations touch — the instruction
indices, `step`, and memory with its label store — so performance work pauses at the changes
IFC cannot collide with, and the memory decision waits for the first IFC cut, when labels are
real. Done now: 1 KiB chunks, `bench/tripwire.py` with a recorded reference, and the erased twin
frozen at `15e5ace`. For the IFC work, the lessons that are cheap to honour while designing it:

- [ ] **[P1·perf·ifc]** Keep labels static wherever SecWasm allows — the value stack, locals,
  globals and the pc. Types erase, so static labels should cost nothing at run time; only memory
  needs labels at run time.
- [ ] **[P1·perf·ifc]** Keep memory labels at the bytes' chunk granularity (`chunkSize`). For the
  two-point lattice a label chunk can be a bitmap, an eighth the size of a byte chunk: under the
  persistent representation a labelled store copies both, so this keeps labels' cost small.
- [ ] **[P2·perf·ifc]** Build the label singletons that loads and stores need into the
  instructions at elaboration, as the numeric witnesses are, not per step.
- [ ] **[P1·perf·ifc]** Keep `INLINE step` and `-O2` on `Runtime.Interpreter`, and run
  `bench/tripwire.py` once the label index is in: E1 showed that an extra index can change what
  GHC's optimiser does to the driver, and allocation per step shows it at once.
- [ ] **[P2·perf]** At each IFC milestone, the tripwire; at larger ones, an interleaved sweep
  against the previous milestone's saved binary (bench/README.md). The first such sweep is also
  the next experiment: **IFC's own cost**, the all-`Low` instance of the labelled machine against
  the pre-IFC build.
- [ ] **[P3·perf, after the first IFC cut]** Decide memory with labels in place: mutable memory in
  `ST` (removes byte and label copies; `step` stays total and well-typed, but monadic), or linear
  types (keeps `step` pure-looking, but linearity runs through `Config`, `Store` and every helper,
  and `vector` is not linear). If linear types appeal, prototype them on `Runtime.MemInst` alone,
  on a throwaway branch, before committing the core to them.

---

### Provenance

Consolidated here and removed from the tree in this pass: `discussions/hackathon.md` (planning
notes — the naming/branching/memory/calls items are done; IFC is item **F1**),
`discussions/READING_LIST.md` (references — now under **F1**), and three in-code markers
(`-- XXX` in `Runtime/Interpreter.hs` → **D1**; `-- TODO` in `Runtime/Values.hs` → **D2**;
`-- TODO` in `Codec/Wasm.hs` → the module is now covered by **A1/A2** and **B2**).
