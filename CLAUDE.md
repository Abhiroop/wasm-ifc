# wasm-ifc — agent guide

Intrinsically-typed WebAssembly interpreter in Haskell (GHC 9.12, singletons-base) with
SecWasm's information-flow control in the same instruction type. Architecture, layout and
conventions: see `README.md`; the backlog is `TODO.md`; the style + working rules are
`STYLE.md` (§11 records the type-level override for the core).

## Two branches, two agents

Two agents work on this repository in separate worktrees, one branch each:

- `implement`: the implementation. Everything except `paper/`: source, tests, benchmarks,
  samples and the documents at the top level.
- `paper`: the paper. `paper/current` is the draft, a submodule on Overleaf; `paper/README.md`
  describes the workflow. Code is not changed on this branch.

Changes flow one way: merge `implement` into `paper` when the paper needs the current
implementation (for example to check a claim against the code). Never merge `paper` into
`implement`; the `paper/current` pointer on `implement` is not maintained.

## Build, test, gate

- Full local gate (format, `-Werror` build, tests, hlint, samples, cross-validate):
  `./scripts/gate.sh`; the fast core loop is `SUITES=wasm-ifc-test ./scripts/gate.sh`.
- Three cabal test suites: `wasm-ifc-test` (unit, ~1s), `wasm-ifc-spec` (official spec
  testsuite via `wast2json`, ~minutes), `wasm-ifc-wasi` (official wasi-testsuite).
- `cabal build all --ghc-options=-Werror` — warnings are errors; fix them, do not suppress.
- Format with `fourmolu -i <files>` before committing; `hlint src app test` must say "No hints".

## Conventions that bite

- Three-layer naming: `Foo` (syntax) / `FooShape` (Validation) / `FooInst` (Runtime); `Raw`
  prefix for decoder output; index-space vectors are `…Space`/`…SpaceInst`. Names read as prose.
- Soundness is never deferred: never leave an illegal state representable.
- Open design points are `TODO(ifc Pn)` comments beside the code they concern; `TODO.md`
  summarises them. Remove the comment when the point is settled.
- Prose written for Daniel (comments, reports, the paper) follows his academic-writing skill:
  `/mnt/c/Users/dgalan/.claude/skills/academic-writing/SKILL.md` (Windows side of WSL).
- Commit trailer: `Co-Authored-By: <model> <noreply@anthropic.com>`. Never push; that is the
  maintainer's call.

## Token hygiene (this repo is large; keep context small)

- NEVER grep or read under `test/spec/testsuite/` or `test/wasi/testsuite/` — they are vendored
  submodules with thousands of files. Scope every search to `src app test/*.hs` (the `.hs` tests
  live directly in `test/`, not in the submodules).
- Send long suite output to a file and grep it for the verdict; do not let full logs into context.
- Prefer small targeted edits over large embedded scripts.
