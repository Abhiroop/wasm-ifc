# wasm-ifc — work plan

Internal implementation checklist and audit backlog. This is the single home for "what's
missing / what to improve"; it replaces the scattered notes that used to live in `discussions/`
and in `-- TODO`/`-- XXX` comments in the source. Consumer-facing docs (`README.md`,
`CHANGELOG.md`, Haddock) stay in the tree; everything internal lives here.

## How to use

Each item: `- [ ] **[Pn·area]** Title — what & why. (file refs)`. Check items off as you land
them. Priorities:

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
Suggested order: **P0 → R1 → W0…W6 → R2/R3 → R5** (R5 interleaved as files are touched).

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

- [ ] **[P2·runtime]** Integer→float conversions: confirm `fromIntegral :: Word64 -> Float/Double`
  rounds to nearest-even at every magnitude (the spec requires it; pin with a property against the
  oracle).
- [ ] **[P2·runtime]** Document the spec-permitted choices: NaN handling in `min`/`max` (we keep the
  operand), `nearest` ties-to-even (Haskell's `round` agrees).
- [ ] **[P3]** `runFor :: Int -> …`, a fuel-bounded runner for tests (G1).

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
- [x] **[W5·entry]** `wasm-ifc run file.wasm`: validate and run the start function if present, then
  the `_start` export through `runIO`; the process exit code is `proc_exit`'s. The existing
  `wasm-ifc file.wasm fn args…` stays pure and reports "module needs WASI; use run" on
  `AwaitingHost`.
- [x] **[W6·sample]** `samples/wasi/hello.wat` (imports `fd_write`/`proc_exit`, exports `memory`,
  data segment `"Hello, world!\n"`); `check.sh` compares stdout and exit code; plus the pure
  `AwaitingHost` test.
- [ ] **[W7·later]** Widen the WASI surface only on demand: a wasi-sdk C hello world also imports
  `args_sizes_get`, `args_get`, `fd_close`, `fd_seek`, `fd_fdstat_get`; a hand-written `.wat` needs
  only the two we have.

---

> **Tech-debt pass (2026-07, continued 2026-09):** §A, §B, §D and most of §C/§E are **done** —
> see checkboxes. Open: the repo-hygiene decisions in §E, §F (IFC/roadmap), §H (WASI).
> Blocked by missing tooling: `wasmtime` oracle (B4).

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
- [ ] **[P2·test]** — **BLOCKED:** `wasmtime` is not installed, so no external `--invoke` oracle
  yet; `samples/check.sh` still uses hand-written expected values.

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
  the typed layer (labels on value types / the stack; a noninterference argument). Not started.
  References (folded in from the old `discussions/READING_LIST.md`):
  - SecWasm — the IFC model we follow: <https://plas2022.github.io/files/pdf/SecWasm.pdf>
  - WANILLA (CCS '25) — noninterference via SMT: <https://arxiv.org/pdf/2509.08758>
  - HLIO — hybrid IFC: <https://www.cse.chalmers.se/~russo/publications_files/hybrid-icfp2015.pdf>
  - In-place interpreter for WASM (perf, later): <https://dl.acm.org/doi/pdf/10.1145/3563311>
- [ ] **[P2·feature]** Run the start function after instantiation — it is decoded (`start`)
  but never invoked.
- [ ] **[P2·feature]** Expose exported globals/memories to the CLI — only exported *functions* are
  runnable today (`ExportMem`/`ExportGlobal` are decoded but unused by `runModuleFunction`).
- [ ] **[P3·feature]** Tables + `call_indirect` + element segments.
- [ ] **[P3·feature]** `select` with an explicit result type (opcode `0x1C`); only untyped
  `select` (`0x1B`) is supported.
- [ ] **[P3·feature]** Float CLI arguments (`app/Main.hs` and `runModuleFunction` take
  `[Integer]`).
- [ ] **[P3·feature]** Multi-memory (currently memory 0 only, via the `ModuleMems ~ (m ': ms)`
  non-empty constraint).
- [ ] **[P3·feature]** Reference types & SIMD (`V128`) value types. `ValType` is flat and ready to
  extend, but `HostType` and the value stack would need reference/vector representations.
- [ ] **[P3·feature]** Bulk memory (`memory.fill`/`copy`/`init`), data/passive segments, imports.
- [ ] **[P3·perf]** Linear memory is O(n) copy-on-write (`Runtime.MemInst`); byte marshalling uses
  `[Word8]` lists (`Runtime.Bytes`). Move to a mutable / growable-vector representation when perf
  matters.

## G. Soundness-artifact niceties

- [ ] **[P3]** `run` is the only partial (non-terminating) function — optionally add a
  fuel-bounded `runFor :: Int -> …` for tests and to make termination explicit.

## H. Import system + WASI (parallel track)

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

---

### Provenance

Consolidated here and removed from the tree in this pass: `discussions/hackathon.md` (planning
notes — the naming/branching/memory/calls items are done; IFC is item **F1**),
`discussions/READING_LIST.md` (references — now under **F1**), and three in-code markers
(`-- XXX` in `Runtime/Interpreter.hs` → **D1**; `-- TODO` in `Runtime/Values.hs` → **D2**;
`-- TODO` in `Codec/Wasm.hs` → the module is now covered by **A1/A2** and **B2**).
