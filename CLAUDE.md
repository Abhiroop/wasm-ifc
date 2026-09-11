# wasm-ifc — agent guide

Intrinsically-typed WebAssembly interpreter in Haskell (GHC 9.12, singletons-base).
Architecture, layout and conventions: see `README.md`; the backlog is `TODO.md`; the
style + working rules are `STYLE.md` (§11 records the type-level override for the core).

## Build, test, gate

- Full local gate (format, `-Werror` build, unit tests, hlint, samples): run the script the
  maintainer keeps in the scratch dir as `gate.sh`; core-only is `SUITES=wasm-ifc-test gate.sh`.
- Three cabal test suites: `wasm-ifc-test` (unit, ~1s), `wasm-ifc-spec` (official spec
  testsuite via `wast2json`, ~minutes), `wasm-ifc-wasi` (official wasi-testsuite).
- `cabal build all --ghc-options=-Werror` — warnings are errors; fix them, do not suppress.
- Format with `fourmolu -i <files>` before committing; `hlint src app test` must say "No hints".

## Conventions that bite

- Three-layer naming: `Foo` (syntax) / `FooShape` (Validation) / `FooInst` (Runtime); `Raw`
  prefix for decoder output; index-space vectors are `…Space`/`…SpaceInst`. Names read as prose.
- Soundness is never deferred: never leave an illegal state representable.
- Commit trailer: `Co-Authored-By: <model> <noreply@anthropic.com>`. Never push; that is the
  maintainer's call.

## Token hygiene (this repo is large; keep context small)

- NEVER grep or read under `test/spec/testsuite/` or `test/wasi/testsuite/` — they are vendored
  submodules with thousands of files. Scope every search to `src app test/*.hs` (the `.hs` tests
  live directly in `test/`, not in the submodules).
- Send long suite output to a file and grep it for the verdict; do not let full logs into context.
- Prefer small targeted edits over large embedded scripts.
