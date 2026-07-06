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
when there is a choice. See item **E1** (record this as the signed-off §11 override).

---

> **Tech-debt pass (2026-07):** all of §A, §D, and most of §B/§C are **done** — see checkboxes.
> Deferred by request: §E (docs), §F (IFC/roadmap). Blocked by missing tooling: `wasmtime`
> oracle (B4).

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
- [~] **[P1·test]** Haskell-level tests (no `wat2wasm`): **done** — elaborator acceptance
  (add/div), elaborator rejection (stack underflow, result mismatch, out-of-range local, operand
  type mismatch), and a divide-by-zero trap, all built from `RawModule` values. **Still open:**
  decoder byte fixtures for the malformed-input paths (A1/A2/A6), the remaining traps (OOB,
  `unreachable`, invalid conversion), and dead-code accept/reject.
- [x] **[P1·test]** Property tests (`hedgehog`): `Runtime.Bytes` word↔bytes round-trips (32/64)
  and unsigned `intDiv32` vs host `div`. (Convert-reinterpret + generated-module properties still
  open.)
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
- [x] **[P2·design]** Typed `Val (t :: ValType)` — **evaluated, decided against**: it would force
  indexing `ConvertOp` by source/target and threading it through the interpreter, for little gain,
  since the untyped `Val` is a contained bit-bridge that never escapes into the typed stack.
  Rationale recorded on `Val`. (`src/Runtime/Values.hs`)
- [x] **[P2·modules]** Explicit export lists added to `Runtime.MemInst` (hides the constructor +
  `pageSize`; dropped dead `memoryBytes`), `Runtime.Values` (hides the `Val` bit-rep), `Syntax.*`
  leaves, and `Syntax.Instructions`. `Syntax.Types`/`Validation.Shape` kept **open** (documented:
  single-constructor `Sing` constructors need an open import).
- [x] **[P2·records]** `NoFieldSelectors` + `DuplicateRecordFields` adopted; selector uses rewritten
  to `OverloadedRecordDot`. The duplicate `wasmType` selector and the generic
  `signature`/`locals`/`body` selectors no longer pollute the top level.
- [x] **[P2·decoder]** `Codec.Wasm`: explicit `Data.Binary.Get` import; redundant parens stripped.
- [x] **[P3·naming]** `SomeModuleShapeS` → `SomeModuleShape`. (`src/Validation/Reflect.hs`)
- [ ] **[P3·extensibility]** — **N/A until ref/vec types land:** add `IsNum` (+ `intIsNum`/
  `floatIsNum`) then (documented extension point already in `Syntax.Types`).

## E. Documentation (consumer-facing)

- [ ] **[P1·docs]** Record the type-level override in `STYLE.md` §11: the intrinsically-typed core
  deliberately uses GADTs/`DataKinds`/type families/singletons to model WASM's type system as an
  unrepresentable-illegal-states soundness artifact; §2's cap is overridden for those modules,
  while the simplicity spirit still applies.
- [x] **[docs]** README layout table referenced `src/Old/`; the reference prototype is `app.old/`.
  Fixed in this pass.
- [ ] **[P2·docs]** README: add a "Status / limitations" section (single memory; no
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

---

### Provenance

Consolidated here and removed from the tree in this pass: `discussions/hackathon.md` (planning
notes — the naming/branching/memory/calls items are done; IFC is item **F1**),
`discussions/READING_LIST.md` (references — now under **F1**), and three in-code markers
(`-- XXX` in `Runtime/Interpreter.hs` → **D1**; `-- TODO` in `Runtime/Values.hs` → **D2**;
`-- TODO` in `Codec/Wasm.hs` → the module is now covered by **A1/A2** and **B2**).
