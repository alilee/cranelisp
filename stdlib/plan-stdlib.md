# Standard library design

`dev` owns this design of the reference standard library, deployed narrowly to
`stdlib/`. It records the principles, the curated surface, the module map, the
self-test model, the unbuilt surface and the open stdlib decisions. Module
source is the authority for exact names and signatures. The
[spec §11](../spec/11-stdlib.md) records what the language guarantees any
library author, and this document does not restate it. The
[stdlib memory](CLAUDE.md) carries authoring conventions and the self-test run
recipe. Delivery history is in Git.

Status labels used below:

- **Current:** verified against source.
- **Planned:** end-state design, not built or scheduled.
- **Open:** awaiting a decision or an owner's work.

## 1. Surface

### 1.1 Purpose

- Provide the vocabulary programs are written in: the primitives and special
  forms are the grammar, and the stdlib is the dictionary.
- Establish the trait bedrock (`Eq`, `Ord`, `Num`, `Display`) and the core data
  structures.
- Serve as model code: idiomatic stdlib source teaches how Cranelisp should be
  written.

### 1.2 Principles

- **Final form only.** Write each module in its end-state form, and add it only
  when the language supports it. Do not ship an interim or throwaway version.
  [No interim implementations](../design/arch/principles/08-no-interim-implementations.md)
  applies.
- **Modular.** A module carries at most about 100 lines of public API. Shell
  modules (`compare.cl`, `num.cl`, …) only declare submodules.
- **Depth signals generality** (§3.1).
- **Small, optional prelude.** Nothing in the prelude is required for the
  language to work, and an empty prelude is valid (root
  [design principles](../CLAUDE.md#design-principles)).
- **Self-testing.** Every definition-bearing module ships backing self-tests (§2).
- **Clojure-aligned vocabulary.** Unify `List`/`Vec`/`Seq` later through
  collection traits. In the interim, do not bind one concrete family to a
  shared bare name (§1.5).
- **Separation.** `tests/` and `examples/` never depend on the stdlib (root
  [design principles](../CLAUDE.md#design-principles)).

### 1.3 Naming

- Use kebab-case, a `?` suffix for predicates and a `!` suffix for effect
  sugar (`bind!`). Types and traits use PascalCase.
- Until a collection trait owns the shared verb, concrete families keep
  disambiguated names: `vec-map`, `map-list`, `seq-map`.
- Deliberate departures from Clojure:

| Cranelisp | Clojure | Reason |
|---|---|---|
| `show` | single-argument `str` | `Display` trait method |
| `fmap` (planned) | none | Functor method |
| `range-from` / `range` | `range` | `seq.lazy/range-from` is infinite; `collections.vec/range` is a finite half-open Vec |
| `pure`, `bind!` | none | IO model |
| `derive` | none | Generated trait implementations |
| `const` / `def` | `def` | Inline substitution versus a zero-argument function |
| `assert-eq` | `(is (= …))` | Returns `(Option String)` rather than raising |

### 1.4 Prelude

**Current.**

- `prelude.cl` is a pure re-export shell. Its `(export …)` forms are the
  authoritative prelude-bound set, so read that set from source rather than
  from a copy.
- The prelude exports:
  - the trait operators and `show`;
  - `str`;
  - `Option`, `Result` and `List` with their constructors, plus `empty?`;
  - the `list` and `vec` construction macros;
  - threading, control, definition and IO-monad macros;
  - the four scalar types `Int Bool Float String`, which bare type annotations
    need (spec §3.1).
- Everything else is reached by explicit import.

**Decision (S113), not exported:** `Default`/`default`. Import the method alone
(`(import [default [default]])`), which suffices for dispatch under spec §7.11.2.
The reasons:

- `default` is rare.
- It dispatches only with a `:Type` annotation, so promotion saves no call-site
  annotation.
- Bare `default` is a common word that downstream code would have to avoid.
- The other non-operator traits are module-qualified.

The user may revisit this boundary. Promotion is a one-line `(export …)`.

**Planned additions, not made:** `derive` (see §3.3 derive), `min`/`max` and
`inc`/`dec` (not built; §4.1). Keep the prelude to roughly 30–40 names.

### 1.5 Managed surface

**Current.**

- Users write the curated vocabulary (`+`, `=`, `<`, `show`, `str`, `count`)
  rather than raw primitive names (`add-i64`, `vec-get`). The prelude re-exports
  no raw primitive functions.
- Curation governs only which names are bare. It must not change reachability.
  Three invariants follow from spec §3.1, §8.8.1, §8.9.1 and §8.11.4:
  1. `primitives/<name>` stays reachable regardless of imports and prelude
     content.
  2. An empty prelude stays valid.
  3. Nothing curated is the only route to a capability.

| Tier | Contents | Reached by |
|---|---|---|
| Bare prelude | §1.4 | No import |
| Curated, module-qualified | Collection verbs, `vec-*` / `*-list` / `seq-*` families, string and number helpers | `(import [module [name]])` or `module/name` |
| Raw primitives | `add-i64`, `vec-get`, `str-concat`, … | `(import [primitives [name]])` or `primitives/name` |

- **Reserved verbs.** `collections.vec` curates `count`, `get`, `conj` and
  `assoc`. They and `map`/`filter`/`reduce` stay out of the prelude until a
  collection trait owns the bare name
  ([spec §11.4a](../spec/11-stdlib.md#114a-curated-collection-verb-naming-reservation-non-normative)).
  List `first`/`rest` and pair `first`/`second` are also module-qualified.
  §11.4a.1 permits re-exporting both `first` accessors, but that curation
  choice has not been made.
- **Downstream names.** A downstream definition that shares a prelude-bound
  spelling registers as a peer candidate (spec §8.6.4), and its unqualified use
  can be ambiguous (§8.6.5). Teaching surfaces should choose names outside the
  prelude-bound set or qualify them. [ACT-0961](../sprints/actions/ACT-0961-revisit-conflicting-import-rule.md)
  carries the user's deferred reconsideration of that rule.

## 2. Self-tests

**Current.**

- Each self-test module is a separate backing file at
  `<module-dir>/<stem>/test.cl`, module `<module>.test`. The parent declares
  `(mod- test)`.
- Tests are `test-*` functions of type `(Fn [] (Option String))` that use
  `testing.assertions`.
- `testing.runner` runs what `discover-tests` finds. The memory gives the
  recipe, and eligibility is in
  [the in-language runner](../design/arch/test-discovery.md#43-the-in-language-runner-over-discovered-pairs).
- Self-tests are stdlib-internal evidence. Solution-level evidence lives in
  `tests/stdlib_conformance.rs`, owned by `test`:
  - `stdlib_all_public_modules_compile_and_run` compiles and runs every public
    module;
  - the `stdlib_core_io_*` and `stdlib_timeout_*` cases exercise `core.io`.
- Coverage: 24 of the 38 non-prelude modules carry self-tests. Nine more are
  shells that need none. Five definition-bearing modules have no self-tests:
  `core.io`, `core.trace`, `derive.helpers` (exercised only through
  `derive.test`), `io.monad` and `seq.lazy`. See §6.3.
- Two test headers list withheld cases: `derive/test.cl` and
  `core/syntax/test.cl`.

## 3. Modules

### 3.1 Depth principle

| Depth | Character | Example |
|---|---|---|
| 1 | Standalone, small, universal | `control.cl`, `default.cl` |
| 2 | Foundational, grouped by domain | `compare/eq.cl`, `fn/option.cl` |
| 3+ | Specialised within a domain | `derive/helpers.cl` |

### 3.2 Module map

**Current.** Each module's responsibility is listed below. `(t)` marks a
backing self-test module.

```
stdlib/
├── prelude.cl              re-export shell (§1.4)
├── control.cl (t)          when, unless, cond, case
├── defs.cl (t)             const, const-, def, def-
├── default.cl (t)          Default trait + scalar impls
├── derive.cl (t)           derive dispatch + derive-Eq/-Ord/-Display macros
│   └── helpers.cl          Sexp construction helpers for derive
├── compare/  eq.cl (t)     Eq trait + scalar impls
│             ord.cl (t)    Ord trait + Int/Float/Bool impls
├── num/      num.cl (t)    Num trait + Int/Float impls
│             int.cl (t)    Int helpers
│             float.cl (t)  Float helpers
│             bits.cl (t)   64-bit bitwise layer over native primitives
├── text/     display.cl (t) Display trait + scalar impls
│             string.cl (t) str macro + string helpers
├── fn/       option.cl (t) re-exports primitives Option/Some/None
│             result.cl (t) re-exports primitives Result/Ok/Err + combinators
│             compose.cl (t) identity, compose, pipe, flip
│             threading.cl (t) ->, ->>
├── collections/ list.cl (t)     List type, list macro, list operations
│                vec.cl (t)      vec macro, curated verbs, vec-* family, range
│                pair.cl (t)     re-exports primitives Pair + accessors
│                either.cl (t)   Either type + operations
│                parallel.cl (t) par-map, par-reduce, par-map-reduce
├── seq/      lazy.cl       lazy Seq with producers and consumers
├── io/       monad.cl      pure, do, bind!
├── core/     syntax.cl (t) SList and reader-annotation helpers for macro authors
│             io.cl         IO combinators: >>, map-io, timeout, when-io, unless-io, sequence-io
│             trace.cl      Trace re-exports + display (spec §11.5)
└── testing/  assertions.cl (t) assert-eq, assert-true, assert-false
              runner.cl (t)     check, discovery runner, Outcome/Tally reporting
```

The depth-1 shells `collections.cl`, `compare.cl`, `core.cl`, `fn.cl`, `io.cl`,
`num.cl`, `seq.cl`, `testing.cl` and `text.cl` declare their submodules.

### 3.3 Module notes

**Current.** This section records non-obvious decisions only; source docstrings
carry the rest.

- **Traits.** The stdlib declares `Eq`, `Ord`, `Num`, `Display` and `Default`,
  with impls for the scalar primitives only. User ADTs obtain impls through
  `derive` or by hand.
- **One canonical seeded type.** `fn.option`, `fn.result` and
  `collections.pair` re-export the `primitives`-seeded `Option`, `Result` and
  `Pair` rather than defining second types. Because the source is the same,
  duplicate imports deduplicate (spec §8.6.4).
- **`Ord String` is deliberately absent.** Lexicographic order needs a
  code-point comparison primitive, and a substring-based order would be
  silently wrong. `Eq String` exists. See §6.4.
- **`num.bits`** applies full 64-bit two's-complement semantics over the native
  bitwise primitives (spec appendix A §A.3). `bit-shift-right` is arithmetic,
  and no unsigned shift exists.
- **`text.string`.** The public names `char-to-digit`/`digit-to-char` keep the
  `-to-` spelling. Names containing `->` now parse, but renaming would break
  callers. `str-assoc` is the Clojure-aligned alias of `replace-at`.
- **`collections.vec/range`** is half-open `[lo, hi)` and empty when `hi <= lo`.
- **`collections.parallel`.** The `par-*` functions are ordinary library
  functions. They split half-open index ranges over two independent `let`
  bindings and rely on inferred lenient evaluation
  ([lenient evaluation](../design/backend/lenient-eval.md);
  [effect concurrency](../design/arch/effect-concurrency.md) §7).
- **`core.syntax`** supplies SList helpers plus explicit-import reader-annotation
  helpers: `annotated?`, `annotation` (returns `(Option Sexp)`) and
  `unannotate`. They are macro-authoring tools, not prelude exports. The
  node contract is in the
  [annotated S-expression architecture](../design/arch/annotated-sexp-node.md).
  `~@` expands to `macros/sconcat`, which the compiler seeds
  (`crates/cranelisp-frontend/src/quasiquote.rs`), so the stdlib does not
  provide it. §6.5 records the stale spec wording.
- **`derive`.** `derive-Eq`/`-Ord`/`-Display` take a `deftype` form for
  introspection but do not define the type, so the type must already exist.
  The macros cannot be tested inside `derive.cl`'s own submodule, because a
  macro is available only to later forms in its module (spec §9.3.4). The
  consumer module `derive/test.cl` is therefore the test home. The dispatch
  form `derive` emits the `deftype` and its impls in one `begin`. S117 retired
  FIXME 0816 after addressing macro-expanded declaration staging
  ([S117 conformance recovery](../design/int/s117-conformance-recovery.md) §2),
  but the path has not been re-tested here (§6.3).
- **`core.io`.** `timeout` composes the `race` primitive with the `sleep` leaf.
  A timeout cancels the losing arm (spec §10.12.8–§10.12.9).
- **Accessors.** A deftype-level field list mints accessors. A constructor-arm
  payload does not, so `List`, `Seq`, `Either` and `Outcome` are destructured
  with `match`, with field verbs written by hand (memory §Current authoring
  constraint).

## 4. Unbuilt surface

### 4.1 Planned modules and operations

**Planned.** This is the end-state design. None of it is built or scheduled.

| Home | Planned surface |
|---|---|
| `compare.hash` | `Hash` trait + scalar impls; prerequisite for Map/Set |
| `compare.ord` | generic `min`, `max`, `clamp` over `Ord` (today `num.int`/`num.float` carry type-specific versions) |
| `num.num` | `inc`, `dec` |
| `num.int` | `quot`, `zero?`, `pos?`, `neg?` |
| `num.float` | `floor`, `ceil`, `round`, `sqrt`, `nan?`, `inf?` (may need primitives) |
| `num.unchecked` | `Unchecked` wrapping-arithmetic trait; never in the prelude |
| `text.string` | curated surface for the string primitives (`split`, `join`, `replace`, `trim`, `substring`, `to-upper`, …), which are reached from `primitives` today |
| `text.format` | number formatting with precision (`pad-left`/`pad-right` exist in `text.string`) |
| `fn.option` | `is-some?`, `is-none?`, `unwrap-or`, `and-then`, `and?`, `or?`, and a mapping operation (name subject to §1.5) |
| `fn.result` | `or-else` |
| `fn.compose` | a constant-function combinator; the name `const` is taken by the `defs` macro |
| `fn.combinators` | `partial`, `juxt`, `complement`, `memoize` |
| `fn.threading` | `as->` |
| `control` | variadic `and`/`or`; decided to live here as short-circuiting control macros |
| `collections.functor`, `collections.foldable` | `Functor` (`fmap`) and `Foldable` (`fold`) traits, with impls in each type's module; the trait-dispatched owner of the §1.5 reserved verbs |
| `collections.map`, `collections.set` | hash-based `Map`/`Set`. The implementation strategy is undecided (HAMT, balanced tree or sorted Vec) |
| `collections.vec` | `fold-right`, `find`, `take`, `drop`, `zip`, `enumerate`, `nth`, `contains?`, predicate count, `flat-map`, `distinct`, `index-of`, `sort`, `sort-by`, `min`, `max` |
| ADT trait impls | `Eq`/`Ord`/`Display` for `Option`, `Result`, `List`, `Pair`, `Either`; `Default` for `Option` |
| `testing.assertions` | shorter aliases `assert=`, `assert`, `assert-some`, `assert-ok`, only as thin aliases |
| prelude | `derive`, `min`/`max`, `inc`/`dec` once built (§1.4) |

### 4.2 Requested functions

This is the groomed backlog of requested library functions. A request is a
function or namespace that can be written in Cranelisp from existing
primitives and special forms. Other findings go elsewhere:

- a defect goes to a failing test;
- a needed primitive or language change goes to an action;
- per root [usability findings and defects](../CLAUDE.md#usability-findings-and-defects).

Flow:

1. `sprint` batches requests surfaced by other roles.
2. `dev` on `stdlib/` records each one with its Clojure analog and a priority:
   - P1: repeated friction;
   - P2: surfaced once and useful;
   - P3: completeness.
3. `sprint` pulls high-priority rows into an increment.
4. A row leaves this table when the function lands with self-tests.

| Function | Clojure analog | Surfaced by | Priority | Status |
|---|---|---|---|---|
| `vec-slice` | `(subvec v start end)` | Vec availability review (S3): take-then-drop traverses twice | P3 | requested |
| `vec-pop` | `(pop v)` | Vec availability review (S3): stack-like use | P3 | requested |

## 5. Future byte-backed text

**Planned, blocked on user rulings.**

- Cranelisp has native `String`. It has no `Byte`, no `(Vec Byte)` text, no
  `Utf8Literal` and no stdlib `int-to-string`.
- The [byte-backed text exploration](../design/arch/byte-backed-text.md) owns
  the recommended direction:
  - §12: the negative-accumulator `int-to-string` algorithm, correct at
    `INT_MIN`;
  - §13: the stdlib text verification matrix;
  - §16: the unresolved questions and the gate order.
- No stdlib implementation begins before that gate order is satisfied.
- Native `String` and its primitives stay live until a separately approved
  parity and migration.

The prospective module split has provisional names, pending user naming:

| Module | Responsibility |
|---|---|
| `text.bytes` | byte-vector construction, slicing, comparison, explicit byte indexing |
| `text.utf8` | validation and checked conversion between `(Vec Byte)` and validated text |
| `text.code-point` | scalar decoding/encoding and code-point iteration |
| `text.grapheme` | grapheme segmentation and traversal |
| `text.normalize` | explicit normalization transforms |
| `text.encoding` | approved alternate encodings (UTF-16/32) |
| `text.format` | value formatting, including stdlib `int-to-string` |

Rules for that design:

- Every index names its unit (byte, code point or grapheme). Plain ambiguous
  indexing is forbidden.
- A text carrier must have a field shape determined by its concrete
  parameters.
- Embedding a heap value takes one count per stored node
  ([structural embedding ownership](../design/runtime/s118-structural-embedding-ownership.md)).

## 6. Open decisions and obligations

### 6.1 Function-valued `def` (FIXME 0800 face 3) — user decision

**Open.** `def` is a stdlib macro, not a core form (spec §5.7). `(def k v)`
expands to a zero-argument `k-def` function and a zero-argument macro `k` that
expands to `(k-def)`. Bare `k` therefore yields the stored value, but `(k 1 2)`
fails with the macro's zero-argument clause even when the value is a closure.

- **A — value-only.** Keep the current expansion. A stored closure is called
  after a local binding, `(let [f k] (f 1 2))`. Direct application should get a
  deliberate value-only diagnostic instead of the macro-arity error.
  Compatibility is highest, and the ergonomic gap remains.
- **B — forwarding `def`.** Add a variadic clause so `(k a b)` expands to
  `((k-def) a b)`. Direct calls and currying work, and a non-function reaches
  the ordinary type error. The forwarding must not capture names or reorder
  argument evaluation.
- **C — separate callable binding macro.** `def` stays value-only, and a new
  macro forwards applications. Intent is explicit, but the vocabulary is
  duplicated. Its name must be checked against §1.5 and the §11.4a reservation.

Whichever option is selected must:

- stay a stdlib macro;
- not change how often the stored expression is evaluated relative to current
  `def`;
- specify closure, currying and non-function diagnostics;
- ship self-tests;
- produce a narrow failing `test` reproduction if the compiler fails the
  chosen contract.

The choice is independent of REPL definition presentation (FIXME 0863).

### 6.2 Restore `core.io` self-tests (FIXME 0907 item 2)

**Open.** FIXME 0907 is the gate: this obligation opens when its evidence cells
are accepted. At that point, author `core/io/test.cl` with a `(mod- test)` in
the parent, covering:

1. `>>` sequences two effects and discards the first result.
2. `map-io` applies a pure function to an IO result.
3. `when-io`: true runs the action; false yields `(Pure 0)`.
4. `unless-io`: false runs the action; true yields `(Pure 0)`.
5. `sequence-io` over `Nil`, and over a three-element list with order preserved.
6. `timeout`: the winning arm gives `(Some v)`; the timer arm gives `None` and
   cancels the loser.

### 6.3 Self-test gaps

**Open.** `core.trace`, `io.monad` and `seq.lazy` have no self-tests.
`derive.helpers` is covered only through `derive.test`. `io.monad` has the
highest value, because `pure`/`do`/`bind!` are prelude surface. `derive.test`
does not exercise the two-field constructor or the three-constructor
`derive-Ord`; both run on S122 source and are covered by the `stdlib_derive_*`
cases in `tests/stdlib_conformance.rs`, so they can be added as self-tests.
Before `derive` enters the prelude, add a `derive.test` case for the `derive`
dispatch form (§3.3).

### 6.4 `Ord String`

**Open usability finding, no filing.** It needs a code-point ordering
primitive (§3.3). A language-capability request is routed as an action.

### 6.5 Stale spec wording

**Open.** Spec §11.4 says `~@` requires `core.syntax/sconcat`. The expander
emits `macros/sconcat` (§3.3). This is routed to `spec`.
