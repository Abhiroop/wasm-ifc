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

---

> **Tech-debt pass (2026-07, continued 2026-09):** §A, §B, §D and most of §C/§E are **done** —
> see checkboxes. Open: the repo-hygiene decisions in §E, §F (IFC/roadmap), §H (WASI).
> Blocked by missing tooling: `wasmtime` oracle (B4).

## A. Correctness & robustness

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
  to `OverloadedRecordDot`. The duplicate `wasmType` selector and the generic
  `signature`/`locals`/`body` selectors no longer pollute the top level.
- [x] **[P2·decoder]** `Codec.Wasm`: explicit `Data.Binary.Get` import; redundant parens stripped.
- [x] **[P3·naming]** `SomeModuleShapeS` → `SomeModuleShape`. (`src/Validation/Reflect.hs`)
- [x] **[P1·soundness]** `IsNum` witness added (this had been wrongly deferred to "when ref/vec
  land" — the deferral *was* the gap). Every numeric instruction now carries `IsNum`/`IsInt`/
  `IsFloat`, never a bare `Sing (t :: ValType)`, so the constraint holds by construction and does
  not rely on `ValType` being all-numeric. Fixes a latent gap (`funcref.add` would type-check once
  ref types exist) and a live bug (`IEqz` accepted `f32.eqz`). `numType` + `withNum` refine in the
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
- [ ] **[P2·feature]** Run the start function after instantiation — it is decoded (`moduleStart`)
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

Remaining pieces (these edit the audited core):

- [ ] **[H1·decoder]** Import section in `Codec.Wasm` (currently hard-`fail`s on any import).
  Parse import entries (module name, field name, kind + type). MVP: imported **functions** only
  (kind 0x00 → typeidx); `fail` on imported tables/memories/globals for now (a WASI module
  provides and *exports* its own memory).
- [ ] **[H2·types]** Function index space `= imports ++ defined` (imports first, per spec).
  `ModuleFuncs shape` covers both; `FuncInst` becomes a sum — `HostFunc` (an opaque host id +
  its `FuncType`) vs. `WasmFunc` (the typed body). Touches `Runtime.Interpreter`
  (`FuncInst`/`FuncInsts`) and `Validation.Shape`/elaboration.
- [ ] **[H3·machine]** Effect-request boundary in `Runtime.Interpreter`: a new `StepResult`
  variant `HostCall`, carrying the host id, the popped `[Word32]` args, and a resume
  continuation `(WasiOutcome → Config)`. `step` stays pure/total (it only *builds* the request).
  Add `runIO :: … -> Config -> IO (Either Trap (ValueStack res))` alongside `run`, which on a
  `HostCall` calls `Runtime.Wasi.runWasiCall` with the store's memory, applies the result
  (store memory back, push the errno) and resumes; `WasiExit` short-circuits.
- [ ] **[H4·elaborate]** `Validation.Elaborate`: build `ModuleShape` with imports first; resolve
  each import `(module, field)` — for `wasi_snapshot_preview1`, check its declared `FuncType`
  against `Runtime.Wasi.wasiSignature`; map it to a host id. `ICall` into a host slot is typed
  exactly like any call.
- [ ] **[H5·entry]** Run the `_start` export (the WASI entry) — overlaps the deferred
  start-function item (**F2**); the module's own memory is what WASI reads/writes.
- [ ] **[H6·sample]** A `hello world` `.wat`/`.wasm` (imported `fd_write` + `proc_exit`, exported
  memory) end-to-end through `runIO`.

**Open design questions:** whether host imports type-check against `wasiSignature` or stay
generic typed slots; how the `HostCall` request threads the store's single memory (the driver
holds the `Store`, so it can read/write directly); whether host funcs live in `FuncInsts` (as a
sum) or a parallel host table.

---

### Provenance

Consolidated here and removed from the tree in this pass: `discussions/hackathon.md` (planning
notes — the naming/branching/memory/calls items are done; IFC is item **F1**),
`discussions/READING_LIST.md` (references — now under **F1**), and three in-code markers
(`-- XXX` in `Runtime/Interpreter.hs` → **D1**; `-- TODO` in `Runtime/Values.hs` → **D2**;
`-- TODO` in `Codec/Wasm.hs` → the module is now covered by **A1/A2** and **B2**).
