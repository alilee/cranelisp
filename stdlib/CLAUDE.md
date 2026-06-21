# stdlib/

Standard library for Cranelisp. Owned by `/stdlib` skill.

## Current State (Sprint 87 hygiene — `num.bits` bitwise module)

Added `stdlib/num/bits.cl` (module `num.bits`; registered `(mod bits)` in
`num.cl`) — the bitwise API (`bit-and`/`bit-or`/`bit-xor`/`bit-not`/
`bit-shift-left`/`bit-shift-right`/`bit-test`/`bit-set`/`bit-clear`/`bit-flip`/
`popcount` + `pow2`/`full-mask`/`width`/`bit-at`) composed entirely from Ring 0
arithmetic primitives. **WIDTH = 30 bits** for the fixed-width ops (`bit-not` is
one's-complement within the low 30 bits, not machine two's-complement — keeps
intermediates positive). Clojure-aligned names; none reserved by §11.4a; reached
module-qualified / import-on-demand — **NOT bare-promoted**. 23 self-tests in
`num/bits/test.cl` (bare `(mod test)` parent, extraction-stable), **all green**
via the in-language runner (`(discover-tests ["num.bits.test"])` →
`23 passed, 0 failed, 0 panicked`). This is the STDLIB coverage of FIXME 0416's
need; the COMPILER-intrinsics version of 0416 stays DEFERRED/OPEN (future
perf-driven /arch+/backend decision). See `plan-stdlib.md §26.8`. The exemplar's
`grid.cl` C3 bit layer can now adopt `num.bits/*` (a future `/port` `.cl` swap).
`cargo nextest run --workspace` = **2865 passed / 0 failed / 0 skipped** (unchanged).

## Current State (Sprint 87 Phase 5 Wave 1d — Stage C.2 rollout)

The self-test rollout LANDED + the C.1 adequacy gaps were intaken.

- **Self-tests ship as SEPARATE backing files** (`<module-dir>/<stem>/test.cl`),
  with a bare `(mod test)` in each parent — NOT inline `(mod test …)` bodies.
  Rationale: the compiler EXTRACTS an inline `(mod test …)` body to its backing
  file on first compile (spec §8.2.5) and leaves the parent bare; but the
  extraction does NOT write the backing file when the lib dir is the in-place
  workspace `stdlib/`, so an inline body gets silently STRIPPED (observed: a
  full parallel `cargo nextest run` stripped every inline-bodied stdlib
  `(mod test)`, corrupting the tree). Authoring the backing file directly is
  extraction-stable — a full `cargo nextest run` now leaves stdlib
  byte-identical. **Do NOT author inline `(mod test …)` bodies in stdlib;
  write `<stem>/test.cl` and leave a bare `(mod test)` in the parent.**
- **14 modules carry green self-tests** (97 tests total, 0 fail / 0 panic via
  the in-language runner): testing.runner (6), compare.eq (6), compare.ord (7),
  num.num (4), text.display (3), fn.option (2), fn.result (7), collections.pair
  (4), collections.list (7), num.int (10), num.float (6), collections.vec (14,
  incl. `range`), text.string (17, incl. G4/G5). Trait-bedrock modules that the
  HARNESS depends on (`compare.eq`, `text.display`, `fn.option`) self-test
  HARNESS-FREE (inline `if`→`(Option String)`) to avoid the load cycle through
  `testing.assertions`.
- **Run the self-tests** (live REPL, the only mode `discover-tests` works in):
  ```
  (import [<module> [<a-public-name>]])   ; force-load the module
  (import [testing.runner [run-one tally tally-line]])
  (import [collections.vec [vec-map]])
  (import [primitives [discover-tests]])
  (tally-line (tally (vec-map run-one (discover-tests ["<module>.test"]))))
  ```
- **GAP INTAKE (C.1 §FULL):** G3 `range` (`collections.vec`, HALF-OPEN
  `[lo,hi)`), G4 `char-to-digit`/`digit-to-char` + G5 `replace-at`/`str-assoc`
  (`text/string.cl`) — all actioned with self-tests. G6–G10 are adoption gaps
  (verbs exist) → `/port` exemplar `.cl` swaps. G1/G2 are [COMPILER] → routed
  out (FIXME 0416; /backend repro). See `plan-stdlib.md §26.4`.
- **`conj` bare-promotion HELD** — `spec/11-stdlib.md §11.4a` RESERVES `conj`
  (the actual 0402 ruling included it, unlike the proposed resolution §26.2
  assumed). NO `(export …)` added; the full reserved set stays
  module-qualified. See `plan-stdlib.md §26.7`.
- **Stdlib-side fixes:** `core/syntax.cl` now imports `[primitives [str-concat]]`
  (was using it unimported — latent breakage); `default.cl` imports
  `[primitives [Int Float Bool String]]`. `default`/`derive` self-tests are
  DEFERRED (compiler limitations — nullary-trait-method codegen; same-module
  macro in own `(mod test)`; see those files + `plan-stdlib.md §26.6`).
- **Defects surfaced → /qa handoff** (`plan-stdlib.md §26.6`): D-either
  (discover-tests SIGBUS on `(Either String Int)`); D-name (`->` in a `defn`
  name won't parse); D-default (nullary trait-method codegen); D-regen
  (regen strips inline `(mod test)` + in-place-stdlib test isolation).
- `cargo nextest run --workspace` = **2833 passed / 0 failed / 0 skipped**.

## Current State (Sprint 86 Phase 6b — managed-surface revisit)

S86 reframed the stdlib around a **managed, curated surface** (the
hide-primitives pivot). See `plan-stdlib.md` §1.5 for the normative model.
What landed this sprint:

- **Curated Clojure verbs** `count`/`get`/`conj`/`assoc` added to
  `collections/vec.cl` (wrapping `vec-len`/`vec-get`/`vec-push`/`vec-set`).
  Reached module-qualified (`collections.vec/count`) or via import — NOT
  bare prelude (the bare names are reserved for Phase-H trait dispatch).
- **`Ord Bool`** impl added (`false < true`) in `compare/ord.cl`.
  **`Ord String` is BLOCKED** — needs a code-point comparison primitive
  (`char→int`/`str-lt`); the string primitive surface tests char equality
  but cannot order differing chars. Usability finding for `/platform`/`/spec`.
- **`head-of`/`tail-of` → `first`/`rest`** renamed in `collections/list.cl`
  (Clojure alignment). Module-qualified; the bare name is reserved
  (pair `first` coexists FQ-distinct). See FIXME 0402.
- **FIXME 0402** (`target: /spec`) filed: reserve
  `first`/`rest`/`get`/`count`/`map`/`filter`/`reduce` for Phase-H
  trait-dispatched unified forms; pin list-`first` vs pair-`first` coexistence.

**LANDED this sprint (S86 step 1.5d):**

- **The de-leak.** The ~31 raw-primitive bare re-exports were REMOVED from
  `prelude.cl` (`add-i64`/`vec-get`/`str-eq`/… no longer resolve bare; the
  4 bare type re-exports `Int Bool Float String` stay). Users see only the
  curated surface (`(+ a b)`/`(= a b)`/`(!= a b)`/`(< a b)`/`(show x)`).
  Unblocked by the D1 fix (trait DEFAULT-method bodies — `!=`/`<=`/`>=` —
  now resolve in the trait's defining module) and the D2 fix (`neq-string`
  primitive exists, so String `!=` works). Curation invariants verified:
  FQ `primitives/<name>` reachable; null-prelude module typechecks;
  exemplar unaffected (it imports primitives explicitly, not via prelude).

**STILL BLOCKED this sprint (carried — routed to `/qa` for narrow repros):**

- **The collection-verb bare half (DEF-1).** Promoting curated Vec verbs
  `count`/`get`/`conj` to BARE prelude is BLOCKED by a PIPELINE defect (not
  curation): a plain `defn` the prelude only RE-EXPORTS resolves in
  typecheck but its body never reaches the consuming program's codegen
  batch — `(count [1 2 3])` typechecks then fails codegen with "undefined
  function: count" (REPL + `--run`). Same defect already affects bare
  `pure` (`io.monad`) — PRE-EXISTING, not caused by the de-leak. Root cause:
  `derive_codegen_batch` (`src/worker.rs:621`) emits only `ModuleEntry::Def`
  symbols; re-export installs `ModuleEntry::Import` (codegen-skipped).
  Routed to `/qa` → `/int`. `count`/`get`/`conj`/`assoc` stay
  module-qualified; the import path WORKS today
  (`(import [collections.vec [count]])` then `(count [1 2 3])` ⇒ 3). When
  DEF-1 lands, un-comment the `(export [collections.vec [count get conj]])`
  line in `prelude.cl`.
- **Self-test rollout** (`(mod test …)` submodules). BLOCKED by: circular
  re-definition when a trait-module's test imports `testing.assertions`
  ("trait Eq already defined"); submodule trait resolution ("unknown
  trait Eq from module user"); `neq-string` codegen for String `!=`
  (pre-existing, reproducible with `(!= "a" "b")` on HEAD); and
  `testing.runner` cross-module-call SIGSEGV (unresolved
  `__cranelisp_got_testing_runner`). The S82/S83 "runner 4/4 pass" note
  does NOT reproduce on the current binary. Intended test bodies are
  documented inline (`compare/eq.cl` §Self-tests) as the durable record.

**Caching gotcha (S86):** REPL runs persist module scratch + a
`.cranelisp-cache` in the CWD. A stale root `.cranelisp-cache` masks
stdlib edits with confusing errors (e.g. "no impl of trait Ord for Bool"
when the impl is present). Clear `./.cranelisp-cache` (or use `--no-cache`)
when testing stdlib changes from the repo root.

## Current State (Sprint 82 Phase 6 — defect-restore)

S82 fixed four S81-surfaced defects that had forced stdlib workarounds.
Restored this phase:

- **assert-eq stacked bounds (0341 parse half).** `testing/assertions.cl`
  now LOADS — its `[:Eq :Display a :Eq :Display b]` signature parses, and
  the file imports `[primitives [Bool String str-concat]]` so the bare
  `:Bool`/`:String`/`str-concat` resolve under the null import.
  `assert-true`/`assert-false` work end-to-end. **CAVEAT:** *calling*
  `assert-eq` (a cross-module call of a stacked-trait-bound fn) currently
  SIGSEGVs — the `Bounds` carrier corrupts on module reload (the importer
  path of 0341 is not fully fixed). Filed as **FIXME 0354** (/typecheck).
  Until 0354 lands, stdlib self-tests use `assert-true`/`assert-false`,
  not `assert-eq`.
- **`(mod test)` self-tests restored in `testing/runner.cl`** (0342 super
  import + 0343 source-regen-no-clobber). The submodule imports the
  runner's parent helpers via `super`, asserts with `assert-true`/
  `assert-false`, survives a load without rewriting the backing `.cl`, and
  runs green via the in-language runner
  (`(discover-tests ["testing.runner.test"])` → 4/4 pass).
- **`vec-reduce` (0344) works** — `(vec-reduce add-i64 0 [1 2 3])` ⇒ 6,
  scheme `(Fn [(Fn [a b] a) a (Vec b)] a)`. It was never physically
  removed; 0344 unblocks its use (the runner's tally/report folds remain
  hand-rolled loops because they predate the fix — fine to migrate to
  `vec-reduce` in a later pass).

## Current State (Sprint 81 Wave I-5)

The prelude is a **pure re-export shell** — zero inline definitions. All macros
live in their plan-designated domain modules. The `do` macro uses IO semantics
(bind-based) per spec §10.4. Module discovery processes `(export ...)` forms so
the prelude can reference root-level domain modules without import statements.

Sprint 81 W-I-5 delivered: (1) the in-language test runner in
`testing/runner.cl` (FIXME 0273) — an ordinary `vec-map`/`vec-filter` runner
over the fn-value pairs `discover-tests` returns, retiring the dead
`run-tests-*` special-form fold helpers; (2) primitive TYPE re-exports
(`Int`/`Bool`/`Float`/`String`) added to `prelude.cl` (Finding B) so bare
`:Int`-style annotations resolve under the stdlib prelude; (3) a clean
stdlib-side fix to `core/trace.cl`'s separate-bracket `match` arms (FIXME 0339
— the parser was correct; the as-written separate-bracket arm form is not spec
grammar). See the per-feature sections below.

### Module Tree (implemented)

```
stdlib/
  prelude.cl              ; pure re-export shell (export only, no defmacro)
  control.cl              ; when, unless, cond, case macros
  defs.cl                 ; const, const-, def, def- macros
  compare.cl              ; shell: (mod eq) (mod ord)
  compare/eq.cl           ; Eq trait + primitive impls
  compare/ord.cl          ; Ord trait + primitive impls
  num.cl                  ; shell: (mod num) (mod int) (mod float)
  num/num.cl              ; Num trait + primitive impls
  num/int.cl              ; Int operations: rem, abs, sign, even?, odd?, etc.
  num/float.cl            ; Float operations: abs-float, sign-float, etc.
  text.cl                 ; shell: (mod display) (mod string)
  text/display.cl         ; Display trait + primitive impls
  text/string.cl          ; str macro + string operations
  fn.cl                   ; shell: (mod option) (mod result) (mod compose) (mod threading)
  fn/option.cl            ; Option type: None, Some
  fn/result.cl            ; Result type: Ok, Err + operations
  fn/compose.cl           ; compose, pipe, identity, flip
  fn/threading.cl         ; ->, ->> macros
  default.cl              ; Default trait + primitive impls
  collections.cl          ; shell: (mod pair) (mod either) (mod list) (mod vec)
  collections/pair.cl     ; Pair type + first, second, swap
  collections/either.cl   ; Either type: Left, Right + operations
  collections/list.cl     ; List type + list macro + operations
  collections/vec.cl      ; vec macro + Vec utility functions
  testing.cl              ; shell: (mod assertions) (mod runner)
  testing/assertions.cl   ; assert-eq, assert-true, assert-false
  testing/runner.cl       ; in-language test runner over discover-tests pairs + check macro
  core.cl                 ; shell for core.syntax + core.io + core.trace (+ re-exports)
  core/syntax.cl          ; SList helpers (standalone, not prelude dep)
  core/io.cl              ; IO combinators: pure, >>, map-io, when-io, unless-io, sequence-io
  core/trace.cl           ; Trace ADT re-export + trace-show/trace-show-tree display fns
  io.cl                   ; shell: (mod monad)
  io/monad.cl             ; pure, do (IO bind-based), bind! macros
  derive.cl               ; derive macro: derive-Eq, derive-Ord, derive-Display
  plan-stdlib.md          ; normative module tree and delivery plan
```

### What works

- `prelude.cl` is a pure re-export shell using only `(export ...)` forms
- Domain modules compiled in dependency order (toposorted)
- Traits (Num, Eq, Ord, Display) defined in domain modules, re-exported through prelude
- Option and Result types in separate modules
- Function composition utilities (compose, pipe, identity, flip)
- Default trait with primitive impls
- Pair and Either types with operations
- Testing assertions (assert-eq, assert-true, assert-false)
- In-language test runner (`testing/runner.cl`, FIXME 0273): an ordinary
  `vec-map`/`vec-filter` runner over the `(Vec (Pair String (Fn [] (Option
  String))))` pairs that `discover-tests` returns — NO macro runner. `run-one`
  folds each test three-way via `catch-runtime-error`: `(Err msg)`=PANIC,
  `(Ok None)`=pass, `(Ok (Some why))`=assertion FAIL → an `Outcome`
  (Passed/Failed/Panicked). `run-all` = `vec-map run-one` over `(discover-tests
  [])`; `run-matching substr` filters on the pair name first (fresh every call —
  the callables are late-bound through the live GOT). `report`/`tally`/
  `tally-line`/`passed?` present + aggregate. `discover-here` is a sugar macro
  normalising the no-arg (current module) and module-name shapes to the canonical
  `(primitives/discover-tests [<Vec String>])` extern. The retired `run-tests`
  special-form fold helpers (`run-tests-pass-default`/`-fail-default`/`-report`)
  are gone — `compile_run_tests` was deleted.
  - **Runtime scope:** `discover-tests` is a host-promised extern resolved only
    in a LIVE REPL session, so `run-all`/`run-matching` run in the REPL but NOT
    when `testing.runner` is compiled as a `--run`/cache dependency object
    (test-discovery.md §4.5 dev-session framing). The pure helpers (`run-one`,
    `present-one`, `tally`, `report`, `passed?`) work in every mode.
- Threading macros (`->`, `->>`) in `fn/threading.cl`
- String operations + `str` macro in `text/string.cl`
- Int operations (rem, abs, sign, negate, even?, odd?, min-int, max-int, clamp)
- Float operations (abs-float, sign-float, negate-float, min-float, max-float, clamp-float)
- Vec utilities + `vec` macro in `collections/vec.cl`
- List type + `list` macro in `collections/list.cl` with operations
- Control flow macros (when, unless, cond, case) in `control.cl`
- Definition macros (const, const-, def, def-) in `defs.cl`
- IO monadic interface (pure, do, bind!) in `io/monad.cl`
- `do` macro uses IO semantics (bind-based) per spec §10.4
- IO combinators (>>, map-io, when-io, unless-io, sequence-io) in `core/io.cl`
- Derive macro (derive-Eq, derive-Ord, derive-Display) ported from sketch

### Known blockers

- **No floor/ceil/round**: Float operations limited to what can be built from
  existing Ring 0 primitives. Need runtime extern functions for IEEE 754 rounding.
- **IO combinators untested**: `core/io.cl` is written but cannot be tested
  until the backend IO trampoline (I2) and platform DLL loading (I3) are complete.

### What is NOT in prelude (requires explicit import)

- `fn.result` operations: is-ok?, is-err?, unwrap-or, map-ok, map-err, and-then
- `fn.compose`: compose, pipe, identity, flip
- `default`: Default trait
- `collections.pair`: Pair, first, second, swap
- `collections.either`: Either, Left, Right, either, map-left, map-right
- `collections.list` operations: length, fold, map-list, filter-list, reverse, etc.
- `collections.vec`: vec-map, vec-filter, vec-reduce, vec-reverse, etc.
- `num.int`: rem, abs, sign, negate, even?, odd?, min-int, max-int, clamp
- `num.float`: abs-float, sign-float, negate-float, min-float, max-float, clamp-float
- `text.string`: blank?, repeat-str, index-of, reverse-str, pad-left, pad-right
- `testing.assertions`: assert-eq, assert-true, assert-false
- `testing.runner`: run-one, run-all, run-matching, report, tally, tally-line,
  passed?, present-one, the Outcome/Tally ADTs, discover-here, check
- `derive`: derive, derive-Eq, derive-Ord, derive-Display
- `core.io`: >>, map-io, when-io, unless-io, sequence-io
- `core.trace`: Trace, TraceCall, name/params/result/children/nanos accessors,
  trace-show, trace-show-tree (the `(trace …)` form itself is a ROOT SPECIAL FORM —
  no import needed; only the Trace ADT + accessors + display fns are re-exported)
- `primitives` (test discovery): discover-tests, catch-runtime-error, Pair,
  Result/Ok/Err — see the packaging decision below

### `discover-tests` / `catch-runtime-error` / Pair / Result prelude-packaging decision (0273 §3)

These are NOT re-exported through the stdlib prelude. The prelude stays a thin,
predictable convenience surface (traits, operators, the common types, named
arithmetic primitives); the test-discovery surface is a focused, import-on-demand
capability used by `testing.runner` and by anyone composing their own runner.
Users reach them with `(import [primitives [discover-tests catch-runtime-error
Pair Ok Err]])` or FQ `primitives/…`, exactly as the design states ("whether the
prelude re-exports these names is a stdlib packaging choice"). `Pair`/`Result` are
seeded in `primitives` and RE-EXPORTED (not redefined) by
`collections/pair.cl` / `fn/result.cl`, keeping ONE canonical type each.

Primitive TYPES: Int, Bool, Float, String (Finding B / Wave I-4 — re-exported so
bare `:Int`/`:Float`/`:Bool`/`:String` in `:Type` annotations, `deftype` fields,
and `deftrait` sigs resolve without per-file imports; spec 03-types.md §3.1
requires the prelude to re-export bare type refs or they must be explicitly
imported. FQ `:primitives/Int` is always available. Mirrors examples/lib/prelude.cl.
Without this, a stdlib-prelude program using `(deftype P [:Int x])` or a bare
`:Int 42` annotation errored `unknown type 'Int' (from module '')`.)
Traits: Eq, Ord, Num, Display (with =, !=, <, >, <=, >=, +, -, *, /, show)
Types: Option (None, Some), Result (Ok, Err), List (Nil, Cons, empty?)
Functions: pure, str-eq
Macros: ->, ->>, vec, when, unless, const, const-, do, cond, list, str, case, def, def-, bind!
Primitives (30, re-exported from `primitives` for `--run` parity with the REPL surface — see design/stdlib/examples-run-path.md): add-i64, sub-i64, mul-i64, div-i64, eq-i64, lt-i64, gt-i64, le-i64, ge-i64, not, eq-bool, add-f64, sub-f64, mul-f64, div-f64, eq-f64, lt-f64, gt-f64, le-f64, ge-f64, str-concat, str-eq, str-len, char-at, int-to-string, float-to-string, bool-to-string, vec-len, vec-get, vec-set, vec-push

## Conventions

- Trait method parameter names use `self` syntax per spec section 7.1
- Primitive names match the Ring 0/1 tables exactly (add-i64, str-concat, etc.)
- Macro bodies inline helper logic rather than calling defn-defined helpers
  (because defn forms are Phase 4, macros are Phase 3)
- Domain modules use `(import [...])` to declare dependencies
- Shell modules (compare.cl, num.cl, etc.) contain only `(mod ...)` declarations
- Prelude uses only `(export ...)` forms — pure re-export shell
- Modules outside prelude graph (derive.cl) use primitives directly, not trait operators
- Macros in submodules are registered in both expander AND symbol table (pipeline fix)
- **All stdlib modules MUST include `(import [prelude []])`** — the null import (spec §8.3.6) suppresses the implicit prelude glob (spec §8.8.1). This is required because any stdlib module could be re-exported by a project's custom prelude, and importing from a prelude that depends on you is a circular dependency. Stdlib modules use only primitives and explicit imports from each other, never prelude symbols.

## Pipeline Changes

### Sprint 17 Wave 2: Export-based module discovery

`discover_import_dependencies` in `src/pipeline.rs` was extended to also process
`(export ...)` specs during module graph discovery. Previously, exports were
excluded because they referenced submodules already discovered via `(mod ...)`
declarations. With the prelude converted to a pure re-export shell, exports now
reference root-level domain modules that need discovery. The function iterates
over both `import_specs` and `export_specs` module paths.

### Sprint 14 Wave 3: Macro symbol table registration

`compile_and_register_macro` in `src/pipeline.rs` was updated to register macros
in the current module's symbol table (as `ModuleEntry::Macro`), not just in the
expander's `MacroEnv`. Without this, macros defined in submodules could not be
imported by other modules via `(import [module [macro-name]])`. The REPL's
`eval_defmacro` already did this; the batch pipeline was missing it.

## Key Architecture Finding

The `load_prelude` function already supports multi-file module discovery.
It calls `discover_module_graph` on `prelude.cl`, which follows `(mod ...)`,
`(import [...])`, and `(export [...])` references to discover and toposort all
dependent modules. `set_current_module` correctly seeds new modules with
primitives from `user`.

A pipeline fix was needed: modules with only type definitions (e.g., fn/option.cl)
or only trait declarations have no function definitions for codegen. The pipeline
now skips codegen for such modules after typechecking (which registers the types
and traits).
