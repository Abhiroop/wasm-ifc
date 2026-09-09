# Haskell Style & Working Guide

This file is written **for coding agents**. Read it fully before writing or editing Haskell in
this repository, and keep it in context for the whole session.

It is a set of imperative rules with rationale and good/bad examples. Most rules are preferences
with a named fallback; a few are invariants that never bend.

---

## 0. How to read this file

**Prime directive.** Optimize, in order, for **clarity → correctness → maintainability**, then
**performance** as a secondary goal. When two rules collide, the one serving clarity/correctness
wins. Performance only overrides on a specific, stated suspicion — not a vibe.

**Readability mandate (Haskell-specific, and it overrides idiom).** Target the **legible subset of
idiomatic Haskell** — the "Simple Haskell" / "Boring Haskell" subset. The reader of this code is a
competent generalist programmer, **not** a Haskell expert. When two idiomatic options exist, pick
the one that a non-expert can read with the least prior Haskell knowledge. Most of what makes
Haskell idiomatic (ADTs, pattern matching, `do`, `Maybe`/`Either`, `ReaderT`, ordinary
`Functor`/`Monad` use) is fully legible and is encouraged. A specific *advanced tier* is switched
**off** by default here: effect systems, lens/optics, point-free golf, custom operators, and heavy
type-level programming. "Simpler" never means non-idiomatic or hand-rolled — it means the plain
idiom instead of the clever one.

**Two tiers of rules.** Every rule is tagged:

- **[invariant]** — never bends. If satisfying it gets hard, **stop and ask**; do not work around
  it and do not silently relax it.
- **[preference]** — bends under genuine pressure, to the *named fallback* stated with the rule.
  Take the cheap legal move; do not burn the session chasing perfection.

**Bounded effort.** Make a reasonable attempt, then take the documented fallback. If a
`[preference]` is fighting you, use its fallback. If an `[invariant]` is fighting you, the design
is wrong — surface it.

**Deviations.** Do not add exception comments to the code and do not keep a separate deviations
log. Note any deviation in your **end-of-session summary**. If a deviation is structural and
recurring, propose promoting it into §11 as a deliberate amendment.

---

## 1. Naming & identifiers

- **[preference]** Prefer full English words; identifiers are meaningful and self-explanatory.
  Terse names are allowed only where they are a convention of their own: the classic generic
  placeholders (`x`, `xs`, `f`, `k`, `v`) in short polymorphic helpers, and ubiquitous short forms
  (`env`, `cfg`, `db`). Everywhere a name carries domain meaning, spell it out.
- **[invariant]** A **type signature on every top-level binding.** The signature is the primary
  documentation and the thing a reader leans on; never omit it. (Local `where`/`let` helpers may
  omit signatures when obvious.)
- **[preference]** Constructors and conversions read by convention: `mkThing` / smart constructors
  for validated construction; `fromX` / `toX` for total conversions; `parseX` (returning
  `Either`/`Maybe`) for fallible ones. Predicates read as questions: `isValid`, `hasCapacity`.
- **[preference]** Type and constructor names are `UpperCamelCase`; functions and values are
  `lowerCamelCase`. Acronyms are one capitalized word: `HttpClient`, `MailboxId` — never
  `HTTPClient`, `MailboxID`.

---

## 2. Type design

- **[invariant]** Make illegal states unrepresentable. Model the domain with data types; keep
  distinct concepts in distinct types; use sum types to enumerate the real cases rather than
  encoding them in `Bool`/`Int`/`Maybe` combinations.
- **[invariant]** **Soundness is never deferred — we do things to the end.** Do not ship a
  definition that leaves an illegal state representable, or that skips a constraint the domain
  or the spec mandates, with a note to tighten it "later". Enforcing the constraint *is* part of
  writing the definition and is done in the same change: a `TODO`/`XXX` is not a substitute for
  a missing constraint. **"It happens to work because the current data only has valid cases" is
  never an argument** — that reliance on an internal, changeable fact is itself the bug (e.g. an
  op typed `Sing (t :: ValType)` "because every `ValType` is numeric today"). Deferring *feature
  scope* (an unimplemented instruction, a missing subsystem) is fine and expected; deferring
  *correctness* (a constraint, an unrepresentable-illegal-state) is not. If enforcing a
  constraint is genuinely blocked, **stop and say so** rather than leaving the weaker version in.
- **[preference]** **Newtype floor.** Introduce a `newtype` as soon as **any** holds, in order of
  strength: **(b, strongest)** it carries an invariant worth enforcing; **(a)** it crosses a module
  or public boundary; **(c, weakest)** it is confusable with another value of the same underlying
  type in scope. `newtype` is zero-cost, so the only cost is a few lines — pay it readily. A raw
  value used as a single, locally-validated field does not need one; the moment it **travels**,
  wrap it. *Fallback:* none needed; err toward a type when unsure, but do not wrap a single-use
  local.
- **[preference]** For an enforced invariant, use a **smart constructor**: hide the data
  constructor (export the type and the smart constructor, not `MkFoo`), validate on the way in,
  return `Either`/`Maybe`. Parse, don't validate — downstream code receives a value that cannot be
  invalid.
- **[preference]** **Abstraction floor.** Introduce a *typeclass* or a polymorphic abstraction only
  when **>=3 concrete uses share a real shape** *and/or* it **names a genuine domain concept**.
  Below that bar, write concrete functions over concrete types. Reusing the *standard* classes
  (`Functor`, `Foldable`, `Traversable`, `Monad`, ...) is not "abstraction" in this sense and is
  encouraged — the bar is about *inventing new* classes.
- **[invariant]** Do not invent lawless typeclasses to abstract two call sites, and do not build
  category-theoretic vocabulary that has no meaning in this domain.
- **[invariant]** **Cap type-level machinery.** GADTs, type families, `DataKinds`, and type-level
  programming are used **only** when they model a real domain invariant that has no simpler
  value-level encoding, and they are documented where used. In application code the default answer
  is a plain `data` type. (A module that genuinely needs this belongs in §11 as an override.)

```haskell
-- good: illegal states unrepresentable, invariant behind a smart constructor
newtype Age = Age Int
  deriving stock (Eq, Ord, Show)

mkAge :: Int -> Either Text Age          -- validated at the edge
mkAge n
  | n < 0 || n > 130 = Left "age out of range"
  | otherwise        = Right (Age n)

-- bad: stringly/loosely typed, invariant unenforced, illegal states representable
type Age = Int
data User = User { name :: Text, isAdmin :: Bool, isGuest :: Bool }  -- admin AND guest?
```

---

## 3. Error handling & totality

- **[invariant]** **No partial functions.** Never use `head`, `tail`, `init`, `last`, `fromJust`,
  `(!!)`, `read`, partial record fields, or incomplete pattern matches in non-test code. Use total
  alternatives (`listToMaybe`, `NonEmpty`, `readMaybe`, exhaustive `case`). This is the direct
  analog of the Rust `unwrap` ban and is warning-enforced (§9).
- **[preference]** Expected, recoverable failure is a **value**: return `Maybe` (one obvious way to
  fail) or `Either DomainError` / `ExceptT DomainError` (distinct failure cases). `DomainError` is
  a small, concrete sum type scoped to a module or operation, carrying **structured fields**, not
  formatted strings. This is the direct analog of small concrete `thiserror` enums.
- **[preference]** Genuinely *exceptional* IO (the disk is gone, the socket died) uses exceptions,
  caught with **`safe-exceptions`** at a sensible boundary. Do not invent bespoke exception
  hierarchies; do not use exceptions for expected control flow; do not thread `ExceptT` through
  deep `IO`.
- **[invariant]** `error` / `undefined` are permitted **only** for provably-impossible branches
  representing a broken internal invariant, with a message stating the invariant
  (`error "invariant: queue is non-empty here"`). Anything a valid caller can trigger is a value,
  not an `error`.

```haskell
-- good: expected failure as a typed value
data LoadError = FileMissing FilePath | BadFormat Text
  deriving stock (Eq, Show)

loadConfig :: FilePath -> IO (Either LoadError Config)

-- good: total
firstActive :: [User] -> Maybe User
firstActive = find isActive

-- bad: partial, crashes on empty input; and throws on an expected failure
firstActive users = head (filter isActive users)
loadConfig path = readFile path >>= parseOrThrow      -- expected failure via exception
```

---

## 4. Readability: the legible subset

This section is what makes the codebase readable to a non-expert. These rules **override** any
"but the clever version is more idiomatic" instinct.

- **[preference]** **Prefer `do`-notation and named steps over point-free chains.** Point-free is
  allowed only where it is *plainly* clearer (`sum . map cost` is fine). The moment a point-free
  expression needs thought to parse, name the steps with `let`/`where`. *Fallback:* a short, obvious
  pipeline may stay point-free.
- **[invariant]** **Do not define custom operators.** No new `<+>`/`.:`/`~>` symbols. Use named
  functions — a reader can hover a name, not a symbol.
- **[preference]** **Prefer explicit over clever.** Plain `map`/`filter`/`foldr`/`for_`/`traverse_`
  over exotic combinator gymnastics; a `case` over a nested `maybe`/`either` puzzle; an ordinary
  recursive function over a fold that needs a paragraph to explain.
- **[preference]** **Prefer concrete types over gratuitous polymorphism.** Do not generalize a
  signature with typeclass constraints (`MonadReader`, `MonadError`, ...) when a concrete type
  (`App`, `ReaderT Env IO`) reads clearer and is all you need. *Fallback:* generalize when a
  function genuinely has >=3 concrete instantiations (per the abstraction floor).
- **[invariant]** Comments say **why, not what**, judiciously, only where they earn it. Good code
  is obvious; do not narrate it.
- **[preference]** Exported items get a concise Haddock (`-- |`) focused on **semantics, invariants,
  laws, and edge cases** — never a restatement of the type signature. If the only thing it would
  say is the signature in prose, write nothing.

```haskell
-- bad: point-free golf — unreadable without mentally evaluating it
lookupValues key = map snd . filter ((== key) . fst)

-- good: say what it does
lookupValues :: Eq k => k -> [(k, v)] -> [v]
lookupValues key pairs =
  [ value | (k, value) <- pairs, k == key ]
```

---

## 5. Modules & visibility

- **[preference]** Use **explicit export lists** on every module — that list *is* the module's
  public surface and the smallest-visibility mechanism. Export the types and functions callers
  need; keep helpers unexported. Do not export data constructors of types that enforce an
  invariant (export the smart constructor instead).
- **[preference]** One primary concept per module, named for it. Present a **curated public
  surface**: if a package has many internal modules, re-export the intended API from a small number
  of top-level modules so callers import `Acme.User`, not `Acme.Internal.User.Detail.Rep`.
- **[preference]** Group imports and prefer **explicit import lists or qualified imports** for
  anything non-obvious (`import qualified Data.Map as Map`). `Text`, `Map`, `Set`, `ByteString` are
  conventionally imported qualified.

---

## 6. Effects & IO structure

- **[invariant]** Keep logic **pure by default**. Push `IO` to the edges; the core is total
  functions over data. A function that does not need `IO` does not get an `IO` type.
- **[preference]** When code needs configuration/environment or a handful of effects, use a single
  concrete application monad: **`ReaderT Env IO`** (the "three-layer cake" — pure core, a thin
  effectful layer, `ReaderT` on top). Put shared config, connections, and loggers in `Env`.
- **[invariant]** **No effect-system libraries** (`effectful`, `polysemy`, `fused-effects`) and
  **no deep mtl transformer stacks** in this codebase. `ReaderT`/`ExceptT` are the ceiling. This is
  a deliberate simplicity choice, not an oversight — if a module seems to truly need more, that is
  a §11 conversation, not a workaround.

```haskell
-- good: one concrete app monad, readable signature
type App = ReaderT Env IO

sendReminder :: UserId -> App ()

-- bad (for this codebase): effect-system constraints in every signature
sendReminder :: (Reader Config :> es, Log :> es, Db :> es) => UserId -> Eff es ()
```

---

## 7. Records

- **[preference]** Use modern records: `OverloadedRecordDot` for access (`user.name`),
  `NoFieldSelectors` + `DuplicateRecordFields` so field names need no type-prefix and generate no
  clashing top-level selectors. Field names are plain (`name`, not `userName`).
- **[invariant]** **No `lens` / `optics`.** No `^.`, `.~`, `%~`, `&` operator chains. Plain dot
  access and record-update syntax only.
- **[preference]** For a nested update that record syntax makes ugly, write a **named helper
  function** (`setCity :: Text -> User -> User`) rather than reaching for optics. Better still,
  prefer flatter data models so deep nested updates rarely arise. *Fallback:* a named helper is
  always the escape hatch; optics never are.

```haskell
-- good: dot access reads like any mainstream language
greeting :: User -> Text
greeting user = "Hello, " <> user.name

-- bad: optics for plain field access
greeting user = "Hello, " <> user ^. #name
```

---

## 8. Tests

- **[preference]** Use **`hspec`** for the test suite — its `describe`/`it` structure reads almost
  like English and has the gentlest learning curve. (`tasty` is a fine alternative if a repo
  already uses it.)
- **[preference]** Use **property tests for algebraic laws** — round-trips (encode/decode,
  parse/print), ordering/equality laws, idempotence — via **`hedgehog`** (explicit generators read
  more clearly than derived `Arbitrary` instances). Reach for a property whenever the invariant is
  law-shaped; example-based tests are fine otherwise.
- **[preference]** Use golden tests (`hspec-golden` / `tasty-golden`) for output-shaped assertions
  (rendered `Show`/`Display`, formatted output). Review the diff when accepting a golden file — the
  golden output is not the oracle, you are.
- The **dev-dependency bar is lower than the runtime bar** (§9): `hspec`, `hedgehog`, and the
  golden libraries are auto-approved as test dependencies.

---

## 9. Working protocol

How to *operate* in this repo (distinct from how the code looks):

- **[invariant]** Run **fourmolu** after editing. Never hand-format or hand-align; layout is the
  formatter's job. Spend effort on names and structure, not whitespace.
- **[invariant]** Keep the code **hlint-clean**; apply its suggestions unless one conflicts with a
  rule here (readability mandate wins — decline the hint and note why).
- **[preference]** When you hit a specific Haskell blocker, **research current community practice**
  (Hackage docs, the library's own guide) before inventing something. Reuse ecosystem knowledge.
- **[invariant]** **Dependency gate.** Slight anti-dependency bias for *runtime* deps: prefer the
  boring, established, widely-used library; ask before adding a runtime dep outside the
  auto-approved set.
  - Auto-approved runtime: `text`, `bytestring`, `containers`, `transformers`/`mtl` (for
    `ReaderT`/`ExceptT`), `safe-exceptions`, `aeson` (when JSON is needed).
  - Auto-approved dev: `hspec`, `hedgehog`, `hspec-golden` / `tasty-golden`.
- **[invariant]** **Bounded effort with named fallbacks.** Make a reasonable attempt at each
  `[preference]`, then take its fallback rather than burning tokens. Never work around an
  `[invariant]` — if one blocks you, stop and ask.
- **[invariant]** Surface every deviation in your **end-of-session summary**. No exception comments
  in code; no separate deviations file. Propose promoting structural/recurring deviations into §11.

### Language & compiler baseline

Declare per component in the `.cabal` file:

```
default-language: GHC2024
default-extensions:
    OverloadedStrings
    OverloadedRecordDot
    NoFieldSelectors
    DuplicateRecordFields
ghc-options: -Wall -Wcompat
             -Wincomplete-uni-patterns
             -Wincomplete-record-updates
             -Wpartial-fields
             -Wredundant-constraints
```

- `GHC2024` *enables* GADTs/`DataKinds`, but §2's cap governs their *use* — availability is not a
  licence to reach for them.
- Prefer `Text` as the string type; `String` only at interop edges; `ByteString` for bytes.
- Always use explicit **deriving strategies** (`deriving stock` / `newtype` / `anyclass`);
  `deriving via` only when it clearly earns its keep.
- Treat warnings as errors in CI (`-Werror`), not necessarily in local dev.

---

## 10. When rules conflict

1. `[invariant]` beats `[preference]`, always.
2. The **readability mandate** (§0) beats "the more idiomatic/clever version." When in doubt, write
   the version a non-expert can read.
3. Among same-tier rules, clarity/correctness/maintainability beats performance unless there is a
   specific, stated performance need.
4. If still ambiguous, take the simpler, more obvious option and note it in the session summary.

---

## 11. Project-specific overrides

Each entry names the rule overridden, its scope, and the reason. This section takes precedence
over the corresponding general rule.

- **§2 "Cap type-level machinery" — overridden for the intrinsically-typed core.**
  *Scope:* `Syntax.Instructions`, `Validation.*`, `Runtime.*`. *Reason:* this project is
  *about* modelling WebAssembly's type system at the type level. GADTs, `DataKinds`, type
  families and singletons are what make ill-typed programs unrepresentable and turn the
  interpreter into a type-soundness artifact (preservation by construction, progress as the
  totality of `step`). *Limits:* everything else in this guide still applies to those modules,
  and the spirit of §2 still binds inside them — prefer the simpler type-level encoding when
  there is a choice (a refinement-witness GADT over a class hierarchy; the library's singletons
  over hand-rolled ones; an explicit witness argument over a `KnownX` constraint outside the
  convenience API) — and the machinery stays out of the decoder, the CLI and the tests.
- **§4 "Do not define custom operators" — overridden for three cons-like constructors.**
  *Scope:* `:.` (`Expr`), `:#` (`ValueStack`) and `:&` (`LocalInsts`). *Reason:* they are
  constructors of list-shaped GADTs, not functions, and they let a hand-written program read
  as the instruction sequence it is (`ILocalGet Here :. IAdd I32IsNum :. INil`) rather than a
  tower of parentheses — the ecosystem's own convention for `:|`. *Limits:* no other operators;
  every other list-shaped type uses prefix constructors (`GCons`, `MCons`, `FsCons`, `SCons`).