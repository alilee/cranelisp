# Standard Library Plan

Motivation, end-state design, and delivery strategy for the Cranelisp standard library.

---

## 1. Motivation

### What the Standard Library Is For

The standard library is the vocabulary Cranelisp gives you to think with. The primitives and special forms are the grammar; the stdlib is the dictionary. It serves three purposes:

1. **Establishes the trait bedrock** — Eq, Ord, Num, Display define what it means to compare, compute, and display values. Everything else builds on these.
2. **Provides essential data structures** — Option, Result, List, Map, Set are the building blocks of programs.
3. **Teaches the language through use** — idiomatic stdlib code is the model for how users should write Cranelisp.

### Design Principles

1. **Design the end state first.** The stdlib is designed as if the language were fully implemented. Modules are written in their final form, targeting the compiler ring where they become compilable. They "light up" as the compiler advances — no interim versions, no throwaway code.

2. **Modular, not monolithic.** Small focused modules, not a mega-core namespace. No single module should exceed ~100 lines of public API.

3. **Depth signals generality.** Module path depth indicates how foundational a module is. Shallow modules are generic and heavily used; deeper modules are specialized and opinionated.

4. **Minimal prelude.** ~30 names re-exported — enough to be productive at the REPL, not enough to be overwhelming. Everything else requires explicit `(import ...)`.

5. **Optional prelude.** Nothing in the prelude is required for the language to work. An empty prelude is a valid starting point. The core language works without it.

6. **Self-testing.** The stdlib validates itself using its own test harness. Each module includes `.test` submodules that use `testing/assertions.cl`. If the test harness works, the language features it depends on also work.

7. **No interim stdlib for compiler tests.** Compiler skills use Rust integration tests or inline Cranelisp helpers. They get no stdlib assistance until the real modules arrive. Those helpers are deleted when the stdlib lights up.

---

## 2. Lessons from Other Languages

**Clojure** — Sequence abstraction is genius: `map`/`filter`/`reduce` work on everything. Cranelisp achieves this through Functor and Foldable traits. Naming style (kebab-case, `?` for predicates, `!` for effects) adopted throughout. Warning: `clojure.core` at ~600 vars is what happens without modular discipline.

**Rust** — Minimal prelude (~30 items). Trait-based polymorphism via `Iterator`. `From`/`Into` conversion traits formalize "how do I get X from Y." `Option` and `Result` are central to API design — both adopted. Clear module boundaries (`std::collections`, `std::fmt`).

**Haskell** — Typeclass hierarchy (Eq -> Ord, Functor -> Applicative -> Monad) is elegant. Cranelisp takes the useful parts (Functor, Foldable) without requiring the full tower. Prelude controversy (alternative preludes exist) teaches: keep it minimal from day one.

**Roc** — Extremely minimal stdlib, platform-provided IO, small focused modules. Closest analogue to Cranelisp's platform model. Proves a tiny standard library can serve a capable language.

**Synthesis**: Roc/Elm's minimalism + Clojure's sequence unification + Rust's trait organization + Haskell's algebraic rigor — tuned to Cranelisp's strengths (ADTs, HM inference, HKT traits, macros).

---

## 3. End-State Organization

### 3.1 Depth Principle

Module path depth signals how foundational a module is:

| Depth | Character | Example |
|---|---|---|
| 1 | Standalone, small, universal | `control.cl`, `default.cl` |
| 2 | Foundational, domain-grouped | `compare/eq.cl`, `fn/option.cl` |
| 3 | Specialized within a domain | `seq/producers.cl` |
| 4+ | Niche, opinionated | `io/web/html.cl` (future) |

### 3.2 Module Tree

```
lib/
├── prelude.cl
│
│   ── Depth-1 singles ──
├── control.cl                   ; cond, case, when, unless
├── defs.cl                      ; const, def, const-, def-
├── default.cl                   ; Default trait + impls
├── derive.cl                    ; derive dispatch macro
├── macros.cl                    ; sexp/slist helpers for macro authors
│
│   ── Depth-2 domain groups ──
├── compare/
│   ├── eq.cl                    ; Eq trait + impls + derive-Eq
│   ├── ord.cl                   ; Ord trait + impls + min, max, clamp + derive-Ord
│   └── hash.cl                  ; Hash trait + impls
├── num/
│   ├── num.cl                   ; Num trait + impls + inc, dec
│   ├── int.cl                   ; abs, sign, even?, odd?, rem, quot
│   ├── float.cl                 ; floor, ceil, round, sqrt, nan?, inf?
│   └── unchecked.cl             ; Unchecked trait + impls (not in prelude)
├── text/
│   ├── display.cl               ; Display trait + impls + show + derive-Display
│   ├── string.cl                ; split, join, replace, trim, contains? + str macro
│   └── format.cl                ; padding, number formatting
├── fn/
│   ├── compose.cl               ; compose, pipe, identity, const, flip
│   ├── combinators.cl           ; partial, juxt, complement, memoize
│   ├── threading.cl             ; ->, ->>, as->
│   ├── option.cl                ; Option: None/Some + map, and?, or?, unwrap-or
│   └── result.cl                ; Result: Ok/Err + map, map-err, and-then
├── collections/
│   ├── list.cl                  ; List: Cons/Nil + head, tail, reverse, concat + list macro
│   ├── vec.cl                   ; Vec extensions: map, filter, fold, sort, zip + vec macro
│   ├── map.cl                   ; Map + assoc, dissoc, get, keys, vals, merge
│   ├── set.cl                   ; Set + insert, remove, member?, union, intersection
│   ├── pair.cl                  ; Pair + first, second, map-first, map-second
│   ├── either.cl                ; Either: Left/Right + map-left, map-right, either
│   ├── functor.cl               ; Functor trait (impls in each type's module)
│   └── foldable.cl              ; Foldable trait + fold, fold-right
├── seq/
│   ├── lazy.cl                  ; Seq: SeqNil/SeqCons — lazy core
│   ├── producers.cl             ; range, range-from, iterate, repeat, cycle
│   └── consumers.cl             ; take, drop, nth, to-list, to-vec, zip-with
├── io/
│   ├── monad.cl                 ; pure, bind!, do
│   └── combinators.cl           ; map-io, sequence-io, when-io
├── testing/
│   ├── assertions.cl            ; assert-eq, assert-true, assert-false
│   ├── runner.cl                ; check macro, run-tests helpers
│   └── trace.cl                 ; Trace accessors, trace-show-tree
```

### 3.3 Module Descriptions

#### compare/ — Comparison and Equality

**`eq.cl`** — The Eq trait: `(deftrait Eq (= [self self] Bool))`. Impls for Int, Float, Bool, String. At Ring 3, adds `derive-Eq` macro for ADTs. The foundation everything else compares against.

**`ord.cl`** — The Ord trait: `<`, `>`, `<=`, `>=` methods. Impls for Int, Float, String. Functions: `min`, `max`, `clamp`. At Ring 3, adds `derive-Ord`. Depends on Eq.

**`hash.cl`** — The Hash trait: `(deftrait Hash (hash [self] Int))`. Impls for Int, String, Bool. Required by Map and Set. No derive initially — manual impls.

#### num/ — Arithmetic and Numerics

> **FIXME**: Should the Num trait be in num rather than num.num? Also, there should be a num/Unchecked trait next to it (definitely not in the prelude).

**`num.cl`** — The Num trait: `(deftrait Num (+ [self self] self) (- [self self] self) (* [self self] self) (/ [self self] self))`. Impls for Int, Float. Functions: `inc`, `dec`. This is where the builtin-to-trait transition happens — Ring 0 hardwired operators yield to trait dispatch.

**`int.cl`** — Int-specific operations beyond arithmetic: `abs`, `sign`, `even?`, `odd?`, `rem`, `quot`, `zero?`, `pos?`, `neg?`.

**`float.cl`** — Float-specific operations: `floor`, `ceil`, `round`, `sqrt`, `nan?`, `inf?`.

**`unchecked.cl`** — Unchecked arithmetic trait (overflow wraps instead of trapping). Not in prelude — explicit import required for intentional use.

#### text/ — Display and String Operations

> **FIXME**: This too could be promoted to text rather than text.display

**`display.cl`** — The Display trait: `(deftrait Display (show [self] String))`. Impls for Int, Float, Bool, String. At Ring 3, adds `derive-Display` for ADTs. Every type that wants human-readable output implements this.

**`string.cl`** — String operations: `split`, `join`, `replace`, `trim`, `starts-with?`, `ends-with?`, `contains?`, `length`, `substring`, `to-upper`, `to-lower`. At Ring 3, adds the `str` macro for string interpolation.

**`format.cl`** — Formatting utilities beyond Display: `pad-left`, `pad-right`, number formatting with precision control.

#### fn/ — Function Composition and Error Types

Option and Result live here because they're function composition tools — they model what happens when composition is partial (Option: might not return a value) or fallible (Result: might fail with an error).

**`compose.cl`** — Function-level composition: `compose`, `pipe`, `identity`, `const`, `flip`. Pure functions, no dependencies beyond primitives.

**`combinators.cl`** — Higher-order function transformers: `partial`, `juxt`, `complement`, `memoize`. Power tools for functional programming.

**`threading.cl`** — Threading macros: `->` (thread-first), `->>` (thread-last), `as->` (thread-as). Syntactic sugar for nested function application. Ring 3 (requires macros).

**`option.cl`** — `(deftype (Option a) None (Some [:a val]))`. Operations: `map`, `and?`, `or?`, `unwrap-or`, `and-then`, `is-some?`, `is-none?`. Trait impls: Eq, Ord, Display, Functor, Foldable, Default. The core "absence" type.

**`result.cl`** — `(deftype (Result a e) (Ok [:a val]) (Err [:e err]))`. Operations: `map`, `map-err`, `and-then`, `or-else`, `unwrap-or`, `is-ok?`, `is-err?`. Trait impls: Eq, Display, Functor. The core "error handling" type.

#### collections/ — Data Structures

Concrete containers and the abstract traits that unify them.

**`list.cl`** — `(deftype (List a) Nil (Cons [:a head :(List a) tail]))`. Operations: `head`, `tail`, `empty?`, `length`, `reverse`, `concat`, `nth`. At Ring 3, adds `list` construction macro. Trait impls: Eq, Display, Functor, Foldable.

**`vec.cl`** — Extensions for the compiler-seeded Vec type: `map`, `filter`, `fold`, `fold-right`, `sort`, `sort-by`, `zip`, `enumerate`, `contains?`, `find`, `any?`, `all?`. At Ring 3, adds `vec` construction macro. Trait impls: Eq, Display, Functor, Foldable.

**`map.cl`** — `(deftype (Map k v) ...)` (hash-based). Operations: `assoc`, `dissoc`, `get`, `contains-key?`, `keys`, `vals`, `entries`, `merge`, `map-vals`, `filter-keys`, `size`, `empty?`. Depends on Hash. Trait impls: Eq, Display, Foldable.

**`set.cl`** — `(deftype (Set a) ...)` (hash-based). Operations: `insert`, `remove`, `member?`, `union`, `intersection`, `difference`, `size`, `empty?`, `to-list`, `from-list`. Depends on Hash. Trait impls: Eq, Display, Foldable.

**`pair.cl`** — `(deftype (Pair a b) (Pair [:a first :b second]))`. Operations: `first`, `second`, `map-first`, `map-second`, `swap`. Used for Map entries and multi-value returns. Trait impls: Eq, Ord, Display.

**`either.cl`** — `(deftype (Either a b) (Left [:a val]) (Right [:b val]))`. Operations: `map-left`, `map-right`, `either`, `is-left?`, `is-right?`, `from-left`, `from-right`. The generic two-way sum type. Trait impls: Eq, Display, Functor.

**`functor.cl`** — `(deftrait (Functor f) (fmap [(Fn [a] b) (f a)] (f b))])`. The trait is defined here; impls live in each type's module (Option, Result, List, Vec, Seq, Either). "I can transform the thing inside."

**`foldable.cl`** — `(deftrait (Foldable f) (fold [(Fn [b a] b) b (f a)] b))`. Functions: `fold-right`, `to-list` (generic). Impls in each collection's module. "I can reduce to a single value."

#### seq/ — Lazy Sequences

Lazy computation streams. Collections can be viewed as sequences, but sequences are not collections — they represent on-demand computation rather than stored data.

**`lazy.cl`** — `(deftype (Seq a) SeqNil (SeqCons [:a head :(Fn [] (Seq a)) rest]))`. The core lazy sequence type with thunked tail. Trait impls: Functor, Foldable.

**`producers.cl`** — Sequence generators: `range` (finite), `range-from` (infinite from start), `iterate` (repeated function application), `repeat` (infinite constant), `cycle` (infinite repetition of a collection).

**`consumers.cl`** — Sequence consumers: `take`, `drop`, `nth`, `take-while`, `drop-while`, `to-list`, `to-vec`, `zip-with`.

#### io/ — Effects

IO combinators for the platform model. Platform operations produce `(IO a)` values; these modules provide ways to compose them.

> **FIXME**: io.monad could be lifted to just io

**`monad.cl`** — `pure` (lift value into IO), `bind!` macro (monadic bind sugar), `do` macro (monadic sequencing). Ring 4 — requires IO trampoline.

**`combinators.cl`** — Higher-order IO composition: `map-io`, `sequence-io`, `when-io`, `unless-io`. Ring 4.

#### testing/ — Validation

The stdlib's own test infrastructure. Also available to user programs.

> **FIXME**: Why aren't these assert=, assert, assert-not, assert-some, assert-none, assert-ok, assert-err?

**`assertions.cl`** — `assert-eq` (needs Eq + Display), `assert-true`, `assert-false`. Each returns `(Option String)` — `None` on success, `(Some "reason")` on failure. Written using only functions and primitives (no macros), so it lights up at Ring 2.

**`runner.cl`** — `check` macro (chains assertions, Ring 3). `run-tests-pass-default`, `run-tests-fail-default`, `run-tests-report` (Ring 4 — need Trace type and `run-tests` special form).

**`trace.cl`** — Accessors for the compiler-seeded Trace ADT: `trace-name`, `trace-params`, `trace-result`, `trace-children`, `trace-nanos`. Display functions: `trace-depth`, `trace-flatten`, `trace-show-tree`. Ring 4 — requires `trace` special form.

#### Depth-1 Singles

> **FIXME**: would (or Bool*) and (and Bool*) go in control? maybe they are more aligned to boolean logic?

**`control.cl`** — Branching macros: `cond` (multi-way if-else), `case` (equality dispatch), `when` (one-sided if), `unless` (negated when). Ring 3.

**`defs.cl`** — Definition macros: `const` (inline sexp substitution), `def` (named zero-arg fn + macro), `const-` (private const), `def-` (private def). Ring 3.

**`default.cl`** — `(deftrait Default (default [] self))`. Impls for Int (0), Float (0.0), Bool (false), String (""), Option (None). The "zero value" trait. Ring 2.

**`derive.cl`** — The `derive` dispatch macro: `(derive [Eq Ord Display] MyType)` expands to calls to `derive-Eq`, `derive-Ord`, `derive-Display` which live in their respective trait modules. Ring 3.

**`macros.cl`** — The macro-writing toolkit: `sfold`, `sreverse`, `sconcat`, `sempty?`, `slength`, `snth`, `smap`, `sdrop`, `slist` construction macro, `scontains?`. Operates on the compiler-seeded `Sexp` and `SList` types from the `macros` synthetic module. Ring 3.

**Unquote-splicing dependency** (Ring 3): The quasiquote expander (owned by `/frontend`) will emit `macros/sconcat` as the qualified path for unquote-splicing list concatenation. The `sconcat` function defined in this module must be available under that path by the time Ring 3 macros are delivered. This is a straightforward path constant in the expander — no cross-skill coordination needed beyond ensuring `macros.cl` exports `sconcat` and is importable as the `macros` module.

---

## 4. Prelude

The prelude grows with each ring, staying minimal throughout. Target: ~30 names at full maturity.

### Ring 2 Prelude (~22 names)

```clojure
;; Comparison
compare.eq          [Eq =]
compare.ord         [Ord < > <= >= min max]

;; Arithmetic
num.num             [Num + - * / inc dec]

;; Display
text.display        [Display show]

;; Core types
fn.option           [Option Some None]
fn.result           [Result Ok Err]
collections.list    [List Cons Nil]
```

### Ring 3 Additions (~12 names)

```clojure
;; Control flow
control             [cond case when unless]

;; Definitions
defs                [const def]

;; Threading
fn.threading        [-> ->>]

;; Derive
derive              [derive]

;; Construction
collections.list    [list]     ; macro
```

### Ring 4 Additions (~3 names)

```clojure
;; IO
io.monad            [pure do]
```

**Final total: ~37 names.** Comparable to Rust's prelude. Everything else — Map, Set, Seq, Pair, Either, function combinators, string operations, formatting, testing — requires explicit `(import ...)`.

Primitives re-exported through prelude: `bind`, `vec-len`, `vec-get`, `vec-set`, `vec-push`, `parse-int`, `str-concat`, `str-eq`.

---

## 5. Delivery

### 5.1 Principles

**Lights up, not rebuilt.** Each module is written in its final form. It becomes compilable when the compiler ring supports its features. No throwaway versions.

**Functions before macros.** Most modules are primarily functions and trait impls (Ring 2). Macros are added to the same files at Ring 3. The Ring 2 version is not interim — it's a complete functional subset that grows.

**Testing enables everything.** `testing/assertions.cl` is the first module built at Ring 2, because every subsequent module needs it for self-validation.

### 5.2 Ring Map

| Ring | Compiler gains | What lights up |
|---|---|---|
| **0** | Int, Bool, Float, fn, let, if, match | *Nothing.* Validates optional prelude. |
| **1** | String, ADTs, heap, RC | *Nothing.* No module system to load stdlib. |
| **2** | Traits, modules | Foundation traits, core types, function composition, collections, sequences, testing assertions. Most of the stdlib. |
| **3** | Macros, prelude | Control flow macros, threading, derive, macro toolkit, construction macros added to existing modules. Prelude activates. |
| **4** | IO, platform | IO combinators, trace, test runner, full testing harness. |

### 5.3 Ring 2 — Foundation (Build Order)

Ring 2 is the big bang. Most of the stdlib lights up here. Build order is driven by dependencies, starting with the test harness.

**Phase 1: Test bootstrap**

```
testing/assertions.cl     ; assert-eq, assert-true, assert-false
                          ; depends on: Eq, Display, Option
                          ; but those don't exist yet — so we build them first
```

In practice, the first three modules and testing bootstrap together:

```
1. compare/eq.cl          ; Eq trait + primitive impls — no stdlib deps
2. text/display.cl        ; Display trait + primitive impls — no stdlib deps
3. fn/option.cl           ; Option type + basic functions — no stdlib deps
4. testing/assertions.cl  ; assert-eq — depends on 1, 2, 3
```

Modules 1–3 are validated by module 4. If assert-eq works, Eq, Display, Option, and the module system all work.

**Phase 2: Remaining foundation traits**

```
5. compare/ord.cl         ; Ord + impls — depends on Eq
6. compare/hash.cl        ; Hash + impls — no trait deps
7. num/num.cl             ; Num + impls — no trait deps
8. default.cl             ; Default + impls — depends on Option
9. text/string.cl         ; String operations — depends on Eq
```

Each module includes `.test` submodules validated by `testing/assertions.cl`.

**Phase 3: Core types and structures**

```
10. fn/result.cl           ; Result type — depends on Eq, Display
11. fn/compose.cl          ; compose, pipe, identity — no deps
12. fn/combinators.cl      ; partial, juxt — no deps
13. collections/functor.cl ; Functor trait
14. collections/foldable.cl; Foldable trait
15. collections/list.cl    ; List type — depends on Eq, Display, Functor, Foldable
16. collections/pair.cl    ; Pair type — depends on Eq, Ord, Display
17. collections/either.cl  ; Either type — depends on Eq, Display, Functor
```

Add Functor and Foldable impls to Option (update fn/option.cl), Result, List.

**Phase 4: Extended collections and sequences**

```
18. collections/vec.cl     ; Vec extensions — depends on Eq, Functor, Foldable
19. collections/map.cl     ; Map type — depends on Hash, Eq, Foldable
20. collections/set.cl     ; Set type — depends on Hash, Eq, Foldable
21. num/int.cl             ; Int operations — depends on Num
22. num/float.cl           ; Float operations — depends on Num
23. num/unchecked.cl       ; Unchecked trait — no deps
24. text/format.cl         ; Formatting — depends on Display
25. seq/lazy.cl            ; Seq type — depends on Functor, Foldable
26. seq/producers.cl       ; range, iterate, repeat — depends on Seq, Num
27. seq/consumers.cl       ; take, drop, to-list — depends on Seq, List
```

**Phase 5: Prelude (Ring 2 version)**

```
28. prelude.cl             ; re-exports Ring 2 modules (~22 names)
```

### 5.4 Ring 3 — Macros

All macro-dependent features light up. Order matters less since macros don't depend on each other much.

```
29. macros.cl              ; sexp/slist helpers (sfold, sreverse, sconcat, etc.)
30. control.cl             ; cond, case, when, unless
31. defs.cl                ; const, def, const-, def-
32. fn/threading.cl        ; ->, ->>, as->
33. derive.cl              ; derive dispatch macro
34. compare/eq.cl          ; +derive-Eq added
35. compare/ord.cl         ; +derive-Ord added
36. text/display.cl        ; +derive-Display added
37. collections/list.cl    ; +list construction macro
38. collections/vec.cl     ; +vec construction macro
39. text/string.cl         ; +str interpolation macro
40. testing/runner.cl      ; +check macro
41. prelude.cl             ; updated with Ring 3 re-exports
```

### 5.5 Ring 4 — Effects

IO and diagnostic modules light up.

```
42. io/monad.cl            ; pure, bind!, do
43. io/combinators.cl      ; map-io, sequence-io
44. testing/trace.cl       ; Trace accessors and display
45. testing/runner.cl      ; +run-tests helpers (need Trace)
46. prelude.cl             ; final form with Ring 4 re-exports
```

---

## 6. Testing Strategy

### 6.1 Two Kinds of Tests

**Compiler tests** (owned by `/qa`, `/frontend`, `/typecheck`, `/backend`): Rust integration tests that exercise the compiler pipeline. These test the compiler, not the stdlib. They use inline Cranelisp helpers (raw builtins, no imports) and delete them when the real stdlib arrives. The stdlib provides no assistance to compiler tests until it naturally lights up.

**Stdlib tests** (owned by `/stdlib`): Cranelisp tests inside the stdlib, using the stdlib's own test harness. These validate that stdlib modules work correctly AND that the language features they depend on work correctly. Self-validating: if the test harness runs, the foundation is sound.

### 6.2 Bootstrap

`testing/assertions.cl` is the keystone. It's built alongside the first three foundation modules (Eq, Display, Option) and validates them. From that point forward, every module includes `.test` submodules that use `assert-eq`, `assert-true`, `assert-false`.

The bootstrap sequence:

```
Eq        ─┐
Display   ─┼─→ testing/assertions.cl ─→ validates everything from here on
Option    ─┘
```

At Ring 3, the `check` macro (in `testing/runner.cl`) enables richer test composition. At Ring 4, `run-tests` helpers complete the framework.

### 6.3 Self-Testing Pattern

Every stdlib module follows this pattern:

```clojure
;; In compare/eq.cl

(deftrait Eq
  (= [self self] Bool))

(impl Eq Int
  (defn = [a b] (int-eq a b)))

;; ... more impls ...

(mod test
  (import [testing.assertions [assert-eq assert-true]])

  (defn test-int-eq []
    (assert-eq true (= 1 1)))

  (defn test-int-neq []
    (assert-eq false (= 1 2))))
```

The `.test` submodule is compiled and run as part of the stdlib build. Test functions follow the `test-*` naming convention for discovery by `run-tests`.

---

## 7. Naming Conventions

### Style

Follow Clojure naming conventions:
- **kebab-case** for all names: `map-err`, `and-then`, `to-list`
- **`?` suffix** for predicates: `empty?`, `even?`, `is-some?`, `member?`
- **`!` suffix** for effect-producing operations: `bind!`
- **Lowercase traits**: `Eq`, `Ord`, `Num`, `Display` (PascalCase, matching Cranelisp convention)

### Intentional Deviations from Clojure

| Cranelisp | Clojure | Rationale |
|---|---|---|
| `show` | `str` (single-arg) | Display trait method — Haskell convention, appropriate for typed FP |
| `fmap` | (no equivalent) | Functor trait method — standard in typed FP ecosystem |
| `range-from` | `range` | Explicitly infinite; `range` reserved for finite ranges |
| `bind!` | (no equivalent) | Monadic bind sugar — Cranelisp IO model |
| `pure` | (no equivalent) | Monadic lift — Cranelisp IO model |
| `derive` | (no equivalent) | Auto-generate trait impls — Rust/Haskell convention |
| `const` / `def` | `def` | Meaningful distinction: inline substitution vs zero-arg function |
| `assert-eq` | `(is (= ...))` | Returns `(Option String)`, not exception-based |

### Names That Match Clojure

`map`, `filter`, `take`, `drop`, `reduce`, `concat`, `reverse`, `empty?`, `repeat`, `iterate`, `inc`, `->`, `->>`, `cond`, `case`, `str`, `do`, `not`, `list`, `vec`, `first`, `rest`, `nth`, `identity`, `comp`, `partial`, `assoc`, `dissoc`, `get`, `keys`, `vals`, `merge`, `sort`, `min`, `max`.

---

## 8. Risks

1. **Builtin-to-trait transition** (Ring 0 -> Ring 2): Ring 0 hardwires `+`, `=`, etc. Ring 2 replaces them with trait dispatch. Existing programs must continue working without changes. Requires careful coordination between `/typecheck` (operator resolution) and `/stdlib` (trait impls).

2. **`sconcat` qualified path**: `~@` (unquote-splicing) emits references to a qualified `sconcat`. The new module layout places this in `macros/sconcat` (was `core.syntax/sconcat`). Frontend must be updated to match.

3. **Map and Set implementation**: These are new types (not in the prototype). They need a hash-based implementation strategy. Options: hash-array mapped trie (HAMT, Clojure-style), red-black tree (Haskell-style), or simple sorted-vec (prototype quality). Decision deferred to implementation.

4. **Derive complexity**: derive-Eq, derive-Ord, derive-Display involve intricate Sexp manipulation (~35 private helpers in the prototype). These macros live in their trait modules, which makes the trait files larger. The macro-writing toolkit (`macros.cl`) provides shared helpers.

5. **Cross-module trait impls**: The design requires implementing traits from one module for types from another (e.g., `(impl Functor Option ...)` in `fn/option.cl`, where Functor is defined in `collections/functor.cl`). This is standard trait behavior but must be validated early at Ring 2.

6. **Result type is new**: The prototype only has Option. Result is a new addition that needs design validation: error type parameter, trait impls, integration with existing error handling patterns.

---

## 9. Ring 1 Review (Sprint 2, Wave 4)

Review of Ring 1 compiler (Chunks A+B+C) from the stdlib author's perspective. Performed by `/stdlib` as Task 13.

### 9.1 String Primitive Audit

**Available Ring 1 string primitives** (8 total, defined in `cranelisp-types/src/operator.rs` `ring1_primitives()`):

| Primitive | Type | Status |
|---|---|---|
| `str-concat` | `(Fn [String String] String)` | Available, tested |
| `str-eq` | `(Fn [String String] Bool)` | Available, tested |
| `str-len` | `(Fn [String] Int)` | Available, tested |
| `string-identity` | `(Fn [String] String)` | Available, tested (RC inc + return same ptr) |
| `int-to-string` | `(Fn [Int] String)` | Available, tested |
| `float-to-string` | `(Fn [Float] String)` | Available, tested |
| `bool-to-string` | `(Fn [Bool] String)` | Available, tested |
| `parse-int` | `(Fn [String] Int)` | Available but **broken type** — returns Int placeholder, not `(Option Int)` |

**Assessment for `text/string.cl` needs** (planned: `split`, `join`, `replace`, `trim`, `starts-with?`, `ends-with?`, `contains?`, `length`, `substring`, `to-upper`, `to-lower`):

- **`str-len`** covers `length`. Good.
- **`str-eq`** covers the equality primitive that `compare/eq.cl` needs for `(impl Eq String)`. Good.
- **`str-concat`** covers concatenation. Good.
- **Missing but deferrable**: `substring`, `char-at`, `split`, `join`, `replace`, `trim`, `starts-with?`, `ends-with?`, `contains?`, `to-upper`, `to-lower` are all absent. These are NOT needed for Ring 2 foundation modules (Eq, Display, Option, Result, assertions). They ARE needed for `text/string.cl` (Phase 2, module 9 in the build order), but that module can be delayed until the primitives exist. **Filed as U1.1.**
- **`parse-int` type mismatch**: The runtime implementation correctly returns `Option Int` layout (tag 0 for None, heap `[tag=1, n]` for Some), but the type system declares it as `(Fn [String] Int)`. Two integration tests are `#[ignore]` because of this. This blocks `text/string.cl` and any code that needs safe string-to-int conversion. **Filed as U1.2.**

**Assessment for `text/display.cl` needs** (planned: `(deftrait Display (show [self] String))`):

- `int-to-string`, `float-to-string`, `bool-to-string`, `string-identity` provide exactly the primitives needed for `(impl Display Int/Float/Bool/String)`. The sketch's `core/formats.cl` uses precisely these 4 primitives. **No gaps.**

### 9.2 ADT Representation Review

**Capabilities validated by Ring 1 tests**:

| Feature | Working | Evidence |
|---|---|---|
| Product types `(deftype Point [:Int x :Int y])` | Yes | `adt_product_construct_and_match`, etc. |
| Sum types `(deftype (Option a) None (Some [:a val]))` | Yes | `adt_sum_option_some/none`, etc. |
| Polymorphic ADTs with type params | Yes | `adt_polymorphic_type` — Option at Int and Bool |
| Shortcut syntax `(deftype Pair [first second])` | Yes | `adt_shortcut_syntax` |
| Constructor patterns with field bindings in match | Yes | All ADT match tests use field bindings |
| Mixed nullary + data constructors | Yes | `adt_enum_mixed_nullary_and_data` (Result type) |
| Nested ADTs `(Some Green)` where Green is an enum | Yes | `multiple_adt_definitions` |
| ADT as function argument and return | Yes | `adt_product_as_function_arg/return` |
| ADT heap allocation and RC | Yes | Implicitly validated by all data-constructor tests |
| ADT display in REPL | Yes | `repl_adt_product` shows `:Point (Point 3 4)` |

**Assessment for stdlib needs**:

- **`fn/option.cl`**: `(deftype (Option a) None (Some [:a val]))` works. Match patterns with field bindings work. Polymorphic instantiation works. The `map`, `and-then`, `unwrap-or` functions (which use match + closures) have the primitives they need. **No gaps.**
- **`fn/result.cl`**: `(deftype (Result a e) (Ok [:a val]) (Err [:e err]))` — two-param polymorphic ADTs with mixed nullary and data constructors are tested (`adt_either_type`). **No gaps.**
- **`collections/list.cl`**: `(deftype (List a) Nil (Cons [:a head :(List a) tail]))` — recursive polymorphic ADT. Not directly tested in Ring 1, but the machinery (polymorphic ADTs, data constructors, match patterns) is all present. **Potential concern**: nested heap RC for `(List (Option Int))` — not exercised. **Filed as U1.3.**
- **`collections/pair.cl`**: `(deftype (Pair a b) (Pair [:a first :b second]))` — two-param product. Covered by shortcut syntax test. **No gaps.**
- **Field accessors**: The plan mentions "field accessor generation" for ADTs. Ring 1 does NOT appear to generate field accessor functions (e.g., auto-generated `Point.x :: (Fn [Point] Int)`). All field access goes through `match`. This is a significant ergonomic difference from the sketch, which had dotted field accessors. **Not a blocker** — stdlib functions can use `match` — but it increases verbosity for simple field extraction. **Filed as U1.4.**

### 9.3 Closure Capability Check

**Capabilities validated by Ring 1 tests**:

| Feature | Working | Evidence |
|---|---|---|
| Simple capture | Yes | `closure_simple_capture` |
| Multiple captures | Yes | `closure_multiple_captures` |
| Closure returned from function | Yes | `closure_returned_from_function` |
| Nested closures | Yes | `closure_nested` |
| Higher-order functions | Yes | `closure_with_higher_order` |
| Named function as value | Yes | `named_function_as_value_apply` |
| Closure in if branches | Yes | `closure_in_if_branch` |
| TCO with closure parameter | Yes | `closure_and_tco` |
| Closure returning ADT | Yes | `closure_returning_adt` |
| Closure capturing int, returning match | Yes | `closure_capturing_int_returning_match_result` |
| Let-bound identity at multiple types | Yes | `let_bound_identity_at_multiple_types` |
| Compose pattern | Yes | `closure_compose` |
| Apply-twice pattern | Yes | `closure_apply_twice` |

**Assessment for stdlib needs**:

- **`fn/compose.cl`**: `compose`, `pipe`, `identity`, `const`, `flip` — all are pure higher-order functions. `compose` is directly validated by `closure_compose` test. **No gaps.**
- **`fn/combinators.cl`**: `partial`, `juxt`, `complement` — higher-order transformers using closures. The patterns are supported (closures capturing arguments, returning closures). **No gaps for Ring 2 subset** (memoize needs mutation, deferred to later).
- **`collections/functor.cl`**: `(deftrait (Functor f) (fmap [(Fn [a] b) (f a)] (f b))])` — requires closures as arguments and HKT. Closures-as-arguments are validated. HKT is Ring 2 (traits). **No closure gaps.**
- **Closure capturing heap types**: `closure_returning_adt` validates closure returning heap ADT. But closure *capturing* a String or ADT is not directly tested. The RC infrastructure should handle it, but it is an untested interaction. **Filed as U1.5.**

### 9.4 Error Message Quality

**Tested error paths in Ring 1**:

| Error | Test | Quality |
|---|---|---|
| String where Int expected | `error_string_where_int_expected` | Produces type error (empty message check) |
| Int where String expected | `error_int_where_string_expected` | Produces type error (empty message check) |
| Constructor wrong arg count | `error_adt_constructor_wrong_arg_count` | Produces error |
| Constructor wrong type | `error_adt_constructor_wrong_type` | Produces type error |
| If branches type mismatch (String/Int) | `error_if_branches_type_mismatch_string_int` | Produces type error |
| Closure arity mismatch | `error_closure_arity_mismatch` | Produces error |
| Undefined constructor | `error_undefined_constructor` | Produces error |
| Non-exhaustive match | `non_exhaustive_match_panics` | Runtime panic (not a type error) |

**Observation**: All error tests use empty string matchers `assert_type_error(src, "")`, which means they only verify that *some* error occurs, not that the error message is helpful. This is a testing gap — error message quality is not validated. However, this is a `/qa` concern, not a `/stdlib` blocker. From a library author perspective, the errors that *do* fire are appropriate (type mismatches, arity mismatches). **No usability findings filed** — this is noted for `/qa` awareness.

### 9.5 Readiness Assessment

**Go/No-Go for Ring 2 stdlib development: GO.**

Ring 1 provides the heap foundation needed for stdlib work to begin at Ring 2. The critical requirements are met:

1. **String primitives**: All 4 Display-impl primitives present (`int-to-string`, `float-to-string`, `bool-to-string`, `string-identity`). Core string operations (`str-concat`, `str-eq`, `str-len`) present. The 11 missing string operations (`substring`, `split`, etc.) are not needed until Phase 2 module 9 (`text/string.cl`), which can be deferred within Ring 2.

2. **ADT types**: Product, sum, polymorphic, shortcut syntax, field binding in match — all work. This covers Option, Result, List, Pair, Either type definitions and their function implementations via `match`.

3. **Closures**: Capture, higher-order, compose patterns — all work. This covers `fn/compose.cl`, `fn/combinators.cl`, and lambda-taking collection functions like `fmap`.

4. **No module system yet** (Ring 2): This is expected. No stdlib code can be written until modules arrive. The plan's Ring 2 build order stands.

**Blockers for later Ring 2 phases** (not Ring 2 start):

- `parse-int` type signature must be fixed before `text/string.cl` can safely convert strings to integers (U1.2).
- Additional string primitives (`substring`, `char-at`) must be added before `text/string.cl` is complete (U1.1). These can be added incrementally during Ring 2.

### 9.6 Risk Assessment Updates

**Risk 1 (builtin-to-trait transition)**: Unchanged. Ring 1 introduced no new operator-level primitives — only extern function primitives. The 19 Ring 0 monomorphic primitives (`add-i64`, etc.) remain the substrate for Ring 2 trait dispatch. The transition path is clean.

**Risk 7 (NEW — parse-int type mismatch)**: `parse-int` returns `Option Int` at runtime but `Int` in the type system. This is a known placeholder (per the comment in `operator.rs`). Must be resolved before `text/string.cl` or any safe string parsing. Requires either: (a) a way to express `(Option Int)` as a return type referencing a user-defined Option, or (b) a compiler-seeded Option type in primitives. Option (b) would conflict with the "optional prelude" principle. Option (a) requires the module system (Ring 2). **Severity: important, not blocking Ring 2 start.**

**Risk 8 (NEW — missing string primitives for text/string.cl)**: 11 string operations planned for `text/string.cl` have no runtime primitive. These need to be added as extern primitives in `cranelisp-runtime` and registered in `ring1_primitives()` (or a new `ring2_primitives()` batch). The runtime implementation is straightforward (Rust's `str` methods). The registration mechanism exists. **Severity: important, not blocking Ring 2 start.**

**Risk 9 (NEW — no field accessors)**: Ring 1 ADTs require `match` for all field access. The sketch had auto-generated dotted field accessors (`Point.x`). If the reimplementation does not plan to add these, stdlib code will be more verbose (3-line match instead of 1-line accessor). This affects ergonomics but not capability. **Severity: deferred — match works, accessors are a convenience.**

**Risk 10 (NEW — closure capturing heap types not tested)**: Closures capturing Strings or ADTs with heap fields are not directly tested in Ring 1. The RC infrastructure should handle this, but a specific test gap exists. If RC is wrong for captured heap values, stdlib higher-order functions over strings will leak or crash. **Severity: important — `/qa` should add specific tests.**

---

## 10. Vec Availability Assessment (Sprint 3)

Vec is now implemented in the Ring 1 compiler with these primitives:

| Primitive | Type | Semantics |
|---|---|---|
| `vec-len` | `(Fn [(Vec a)] Int)` | Number of elements |
| `vec-get` | `(Fn [(Vec a) Int] a)` | 0-based indexed access, bounds-checked |
| `vec-set` | `(Fn [(Vec a) Int a] (Vec a))` | Returns new Vec with element replaced |
| `vec-push` | `(Fn [(Vec a) a] (Vec a))` | Returns new Vec with element appended |

Vec is polymorphic (`(Vec Int)`, `(Vec String)`, `(Vec (Option Int))`, etc.) and uses COW: if rc==1 and is-last-use, `vec-set` and `vec-push` mutate in place. Vec literals use bracket syntax: `[1 2 3]`.

### 10.1 What This Unlocks for `collections/vec.cl`

The planned `collections/vec.cl` module (Phase 4, item 18) provides higher-order operations over Vec. With the four primitives now available, the following functions can be implemented using **only** Ring 2 features (functions, closures, recursion — no macros, no traits):

**Immediately implementable at Ring 2** (functions only, no trait dependency):

| Function | Signature | Implementation strategy |
|---|---|---|
| `vec-map` | `(Fn [(Fn [a] b) (Vec a)] (Vec b))` | Tail-recursive loop: get each element, apply f, push to accumulator |
| `vec-filter` | `(Fn [(Fn [a] Bool) (Vec a)] (Vec a))` | Loop: test predicate, conditionally push |
| `vec-fold` | `(Fn [(Fn [b a] b) b (Vec a)] b)` | Tail-recursive loop: get each element, apply f to acc |
| `vec-fold-right` | `(Fn [(Fn [a b] b) b (Vec a)] b)` | Loop from len-1 down to 0 |
| `vec-reverse` | `(Fn [(Vec a)] (Vec a))` | Fold from end to start, push each |
| `vec-concat` | `(Fn [(Vec a) (Vec a)] (Vec a))` | Fold over second Vec, push each onto copy of first |
| `vec-any?` | `(Fn [(Fn [a] Bool) (Vec a)] Bool)` | Loop with early return via if |
| `vec-every?` | `(Fn [(Fn [a] Bool) (Vec a)] Bool)` | Loop with early return on false |
| `vec-find` | `(Fn [(Fn [a] Bool) (Vec a)] (Option a))` | Loop, return Some on match, None at end |
| `vec-take` | `(Fn [Int (Vec a)] (Vec a))` | Loop from 0 to min(n, len), push each |
| `vec-drop` | `(Fn [Int (Vec a)] (Vec a))` | Loop from n to len, push each |
| `vec-zip` | `(Fn [(Vec a) (Vec b)] (Vec (Pair a b)))` | Loop to min(len-a, len-b), get from each, push Pair |
| `vec-enumerate` | `(Fn [(Vec a)] (Vec (Pair Int a)))` | Loop 0..len, push (Pair i elem) |
| `vec-nth` | `(Fn [Int (Vec a)] (Option a))` | Bounds check, then vec-get wrapped in Some/None |
| `vec-contains?` | `(Fn [(Fn [a a] Bool) a (Vec a)] Bool)` | Loop with equality function (no Eq trait yet) |
| `vec-count` | `(Fn [(Fn [a] Bool) (Vec a)] Int)` | Loop, increment counter on predicate match |
| `vec-flat-map` | `(Fn [(Fn [a] (Vec b)) (Vec a)] (Vec b))` | Map then concat results |

All of these are pure functions over the four Vec primitives plus recursion. They need no macros, no traits, no special forms beyond what Ring 1 provides plus Ring 2 modules.

**Requires Eq trait (Ring 2, after `compare/eq.cl`)**:

| Function | Dependency |
|---|---|
| `vec-contains?` (Eq version) | `(impl Eq a)` for element equality |
| `vec-distinct` | Eq for dedup |
| `vec-index-of` | Eq for element search |

**Requires Ord trait (Ring 2, after `compare/ord.cl`)**:

| Function | Dependency |
|---|---|
| `vec-sort` | Ord for comparison — also needs a sorting algorithm (insertion sort is sufficient for Ring 2) |
| `vec-sort-by` | Takes comparison function, no Ord needed |
| `vec-min` / `vec-max` | Ord for comparison |

**Requires Functor/Foldable traits (Ring 2, after `collections/functor.cl`)**:

| Function | Dependency |
|---|---|
| `fmap` impl for Vec | Functor trait definition; wraps `vec-map` |
| `fold` impl for Vec | Foldable trait definition; wraps `vec-fold` |

**Requires macros (Ring 3)**:

| Function | Dependency |
|---|---|
| `vec` construction macro | `(vec 1 2 3)` as alternative to `[1 2 3]` — may not be needed given literal syntax |

### 10.2 Impact on Build Order

The original Phase 4 placed `collections/vec.cl` at item 18, after Functor and Foldable trait definitions. With Vec primitives available, this module can be **split across two phases**:

**Revised Phase 2 addition** — After item 9 (`text/string.cl`), add:

```
9a. collections/vec.cl (core)   ; vec-map, vec-filter, vec-fold, vec-reverse, vec-concat,
                                ; vec-take, vec-drop, vec-any?, vec-every?, vec-find,
                                ; vec-zip, vec-enumerate, vec-nth, vec-count, vec-flat-map
                                ; depends on: Option (item 3), Pair (when available)
                                ; NO trait dependencies — pure functions over primitives
```

This is significant: most Vec operations need nothing beyond closures and the four primitives. They can ship immediately when modules are available, providing the most-used collection operations early. The Pair dependency for `vec-zip` and `vec-enumerate` means those two functions wait for item 16 (`collections/pair.cl`) or use tupled returns.

**Revised Phase 3 (after Functor/Foldable traits)**:

```
18. collections/vec.cl (traits)  ; Functor impl, Foldable impl, Eq-dependent ops
                                 ; depends on: functor.cl, foldable.cl, eq.cl
```

This two-phase approach means Vec collection functions are available for testing all subsequent modules from Phase 2 item 9a onward — a significant testing convenience.

### 10.3 Sketch Comparison

The sketch (`sketch/lib/core/sequences.cl`) implements Vec operations by converting Vec to lazy Seq and delegating to `fmap`/`lazy-filter`/`lazy-reduce`. This is elegant but has two costs:

1. **Indirection**: Every Vec operation allocates a Seq, processes it lazily, then (if needed) materializes back to Vec. For `vec-map`, this means: Vec → Seq → (process) → Vec — two traversals and intermediate allocations.

2. **Multi-sig dispatch**: The sketch uses multi-signature functions (`map`, `filter`, `reduce`) that dispatch on Vec/List/Seq. The reimplementation should keep Vec-specific functions (`vec-map`, `vec-filter`, `vec-fold`) as the concrete implementations, with unified `map`/`filter`/`reduce` names introduced later via Functor/Foldable traits or multi-sig dispatch.

**Decision**: The reimplementation uses **direct Vec iteration** (loop over indices using `vec-get`/`vec-len`) rather than the sketch's Seq-conversion approach. This is simpler, avoids intermediate allocations, and works without the Seq type (which arrives later in Phase 4). The Functor/Foldable trait impls (Phase 3) provide the unified API.

### 10.4 Usability Observations

1. **No `vec-empty`**: There is no primitive to create an empty Vec. The literal `[]` serves this purpose, but a named function `(vec-empty)` returning `(Vec a)` would be useful for building Vecs programmatically in folds. Workaround: `(vec-push [] first-elem)`. Low priority — literal syntax is sufficient.

2. **No `vec-slice`**: There is no primitive for extracting a sub-Vec. `vec-take` and `vec-drop` can be composed, but a direct `vec-slice` would avoid double traversal. Can be added as a runtime primitive later if profiling shows need.

3. **No `vec-pop`**: There is no primitive to remove the last element. Can be simulated with `vec-take (- (vec-len v) 1) v`, but a direct primitive would enable efficient stack-like usage. Low priority for stdlib — file if exemplar needs it.

4. **Functional API is natural**: The immutable-return-new-Vec API (`vec-set`, `vec-push` return new Vecs) aligns perfectly with the functional stdlib design. COW makes this efficient. No friction here.

### 10.5 Updated Risk Assessment

**Risk 3 (Map and Set implementation)**: Unchanged. Vec availability does not affect Map/Set — those need hash-based data structures that require additional runtime primitives. Vec *does* make a sorted-Vec-based prototype Map feasible as a stopgap, but this would be a stdlib-internal choice, not a compiler concern.

**Risk 11 (NEW — Vec fold performance)**: Tail-recursive folds over Vec using `vec-get` at each index should be TCO-eligible (self-recursive tail calls). If TCO does not fire for these patterns, large Vec operations will stack-overflow. The Ring 1 TCO implementation should handle this, but it needs validation. `/qa` should include a large-Vec fold test (1000+ elements).

---

## 11. Trait Hierarchy Design (Sprint 4, Wave 3)

Sprint 4 delivers Ring 2A: trait declarations, trait impls, constrained polymorphism, and operator dispatch. This section records the trait hierarchy as now implemented in the compiler and assesses what it means for stdlib planning.

### 11.1 Core Traits — Registered at Startup

Per arch decision 17, the three core traits are registered by the typechecker in `register_builtins()` (in `crates/cranelisp-typecheck/src/builtins.rs`), **not** from stdlib `.cl` files. Stdlib files require the module system, which arrives in Sprint 5. This means:

- The trait declarations and their builtin impls exist from the moment the compiler starts.
- Stdlib modules (`compare/eq.cl`, `compare/ord.cl`, `num/num.cl`) will **not** re-declare these traits. Instead they will provide:
  - Convenience functions built on the trait methods (e.g., `min`, `max`, `clamp`, `inc`, `dec`)
  - Additional impls for ADT types (e.g., `(impl Eq (Option a) ...)`)
  - Derive macros at Ring 3 (e.g., `derive-Eq`)

#### Num — Numeric Operations

| Method | Signature | Default body |
|--------|-----------|-------------|
| `+` | `(Fn [a a] a)` | — |
| `-` | `(Fn [a a] a)` | — |
| `*` | `(Fn [a a] a)` | — |
| `/` | `(Fn [a a] a)` | — |

**Built-in impls:**

| Type | `+` | `-` | `*` | `/` |
|------|-----|-----|-----|-----|
| `Int` | `add-i64` | `sub-i64` | `mul-i64` | `div-i64` |
| `Float` | `add-f64` | `sub-f64` | `mul-f64` | `div-f64` |

All four methods are required (no defaults). All map directly to Ring 0 inline primitives.

#### Eq — Equality

| Method | Signature | Default body |
|--------|-----------|-------------|
| `=` | `(Fn [a a] Bool)` | — |
| `!=` | `(Fn [a a] Bool)` | `(fn [x y] (not (= x y)))` |

**Built-in impls** (only `=` is provided; `!=` uses the default):

| Type | `=` primitive |
|------|---------------|
| `Int` | `eq-i64` |
| `Float` | `eq-f64` |
| `Bool` | `eq-bool` |
| `String` | `str-eq` |

`eq-bool` is new in Ring 2A (Ring 0 only had `not`). `str-eq` is a Ring 1 extern primitive.

#### Ord — Ordering

| Method | Signature | Default body |
|--------|-----------|-------------|
| `<` | `(Fn [a a] Bool)` | — |
| `>` | `(Fn [a a] Bool)` | `(fn [x y] (< y x))` |
| `<=` | `(Fn [a a] Bool)` | `(fn [x y] (not (< y x)))` |
| `>=` | `(Fn [a a] Bool)` | `(fn [x y] (not (< x y)))` |

**Built-in impls** (only `<` is provided; `>`, `<=`, `>=` use defaults):

| Type | `<` primitive |
|------|---------------|
| `Int` | `lt-i64` |
| `Float` | `lt-f64` |

Only `<` needs a primitive; the other three comparisons are derived from it via default methods.

### 11.2 Impact on Stdlib Module Design

The original plan (sections 3.3 and 5.3) assumed stdlib modules would declare the core traits. With startup registration, the design shifts:

| Module | Original plan | Revised plan |
|--------|--------------|--------------|
| `compare/eq.cl` | Declare `Eq` trait + impls for Int, Float, Bool, String | Provide ADT impls (Option, List, etc.) + `derive-Eq` (Ring 3) + convenience fns |
| `compare/ord.cl` | Declare `Ord` trait + impls for Int, Float | Provide ADT impls + `min`, `max`, `clamp` + `derive-Ord` (Ring 3) |
| `num/num.cl` | Declare `Num` trait + impls for Int, Float | Provide `inc`, `dec` + any convenience wrappers |

This is a simplification: the foundation traits are available from the start with no module-system dependency. The stdlib modules become thinner — focused on extensions and convenience rather than the trait bedrock.

### 11.3 Stdlib Modules Now Plannable with Trait Support

With Num, Eq, and Ord available at startup, the following modules can be written at Ring 2 (once the module system arrives in Sprint 5) using trait-dispatched operators throughout:

**Fully plannable now (no additional compiler work needed beyond modules):**

| Module | Trait dependencies | Notes |
|--------|-------------------|-------|
| `compare/eq.cl` | Eq (startup) | ADT impls, convenience fns |
| `compare/ord.cl` | Eq (startup), Ord (startup) | `min`, `max`, `clamp` |
| `num/num.cl` | Num (startup) | `inc`, `dec` — trivial wrappers |
| `num/int.cl` | Num (startup), Ord (startup) | `abs`, `sign`, `even?`, `odd?`, `rem`, `quot` |
| `num/float.cl` | Num (startup), Ord (startup) | `floor`, `ceil`, `round` (need runtime primitives) |
| `fn/compose.cl` | None | Pure higher-order fns |
| `fn/combinators.cl` | None | Pure higher-order fns |
| `fn/option.cl` | Eq, Ord (startup) for impls | Type + ops + trait impls |
| `fn/result.cl` | Eq (startup) for impls | Type + ops + trait impls |
| `collections/vec.cl` (core) | None | Already assessed (section 10) |
| `testing/assertions.cl` | Eq (startup) | `assert-eq` needs `=` |
| `default.cl` | None (declares its own trait) | `Default` trait |
| `collections/pair.cl` | Eq, Ord (startup) | Product type + impls |

**Blocked on additional trait declarations (Display, Functor, Foldable, Hash):**

| Module | Missing trait | When available |
|--------|--------------|---------------|
| `text/display.cl` | `Display` must be declared in stdlib or startup | Sprint 5+ |
| `collections/functor.cl` | `Functor` (HKT trait) | Requires HKT support |
| `collections/foldable.cl` | `Foldable` (HKT trait) | Requires HKT support |
| `compare/hash.cl` | `Hash` must be declared | Sprint 5+ |
| `collections/map.cl` | `Hash` + runtime | Sprint 5+ |
| `collections/set.cl` | `Hash` + runtime | Sprint 5+ |

**Key insight**: Display is not a startup trait. The stdlib must declare it (or it must be added to startup registration). The current `builtins.rs` registers only Num, Eq, and Ord. Display is needed for `testing/assertions.cl` (which uses `show` for failure messages) and for most ADT impls. This is a planning decision for Sprint 5.

### 11.4 Constrained Polymorphism Impact

Ring 2A introduces constrained polymorphism: `(defn add [x y] (+ x y))` infers `add :: forall a. { a: [Num] } => (Fn [a a] a)` and monomorphises at call sites. This directly enables:

- **`num/num.cl`**: `(defn inc [x] (+ x 1))` and `(defn dec [x] (- x 1))` — these are constrained polymorphic (work for any `Num` type).
- **`compare/ord.cl`**: `(defn min [x y] (if (< x y) x y))` and `(defn max [x y] (if (< x y) y x))` — constrained on `Ord`.
- **`compare/ord.cl`**: `(defn clamp [lo hi x] (min hi (max lo x)))` — constrained on `Ord`.
- **`testing/assertions.cl`**: `assert-eq` can use `(= actual expected)` generically across all `Eq` types.

This is a significant expressiveness gain. Without constrained polymorphism, these functions would need per-type overloads or would be limited to specific types.

### 11.5 Build Order Refinement

The Phase 1 bootstrap (section 5.3) assumed Eq and Display needed to be declared first. With Eq available at startup:

**Revised Phase 1** (when modules arrive):

```
1. fn/option.cl            ; Option type — no stdlib deps (Eq impl uses startup trait)
2. testing/assertions.cl   ; assert-eq — depends on Eq (startup), Option
                           ; NOTE: show/Display not available yet — use primitives for
                           ; error messages until Display is declared or startup-registered
3. compare/ord.cl          ; min, max, clamp — depends on Eq (startup), Ord (startup)
4. num/num.cl              ; inc, dec — depends on Num (startup)
```

The bottleneck shifts from "declare Eq" to "declare Display". `testing/assertions.cl` needs some way to render values in failure messages. Options:

1. **Add Display to startup registration** — aligns with Num/Eq/Ord pattern. Requires `int-to-string`, `float-to-string`, `bool-to-string` primitives already present.
2. **Use primitives directly** — `assert-eq` calls `int-to-string` etc. explicitly. Works but loses generic rendering.
3. **Defer show integration** — `assert-eq` returns `(Option String)` with a fixed message, no value display. Functional but less informative.

**Recommendation**: Option 1 (add Display to startup) is cleanest. Filed as observation — not a usability finding since it is a planning-stage decision.

### 11.6 Updated Risk Assessment

**Risk 1 (builtin-to-trait transition)**: Now **resolved by design**. Ring 0-1 named primitives (`add-i64`, etc.) retain their `BuiltinFn` path. Operators (`+`, etc.) gain a `TraitMethod` path. Both coexist per arch principle 9 (rings are accretive). The transition is transparent — `(+ 1 2)` dispatches through `Num.+$Int` which the backend maps back to `iadd` inline. No user-visible change.

**Risk 12 (NEW — Display not a startup trait)**: The stdlib plan assumes Display is available alongside Eq/Ord/Num for the bootstrap sequence. Display is not currently registered at startup. This must be resolved before stdlib Phase 1 can execute. Severity: important — blocks the testing bootstrap but not Ring 2A compiler work. Decision point: Sprint 5 planning.

---

## 12. Ring 2B Module Readiness Confirmation (Sprint 6)

The module infrastructure survey (Phase 3, Sprint 5) confirmed that 25 stdlib modules are writable once cross-module imports are fully wired. The compiler now supports:

- `(mod name)` declarations and file resolution
- `(import [module [name1 name2]])` selective imports
- `(export [name1 name2])` visibility control
- Qualified name access (`module/name`)
- Private definitions with `defn-`
- `/mod` namespace switching in the REPL

**Status**: The stdlib can begin implementation as soon as cross-module imports are fully operational. The Phase 1 bootstrap sequence (Option -> assertions -> Ord -> Num) is ready to execute. No additional compiler infrastructure is needed beyond completing the module wiring already underway in Ring 2B.

---

## Next Skills

- `/arch` — Confirm the builtin-to-trait transition strategy. Validate that cross-module trait impls work (trait in module A, type in module B, impl in module B). Review Map/Set implementation strategy.
- `/frontend` — Update `~@` expansion to emit `macros/sconcat` instead of `core.syntax/sconcat`.
- `/typecheck` — Coordinate operator resolution handoff: Ring 0 `ResolvedCall::BuiltinFn` must transparently yield to Ring 2 `ResolvedCall::TraitMethod` when trait impls are loaded. Fix `parse-int` return type when Option is available.
- `/backend` — Add missing string primitives (`substring`, `char-at`, etc.) as extern functions in `cranelisp-runtime` when Ring 2 needs them.
- `/qa` — Plan stdlib self-test execution. Add tests for closure-capturing-heap-types. Process usability findings U1.1–U1.5. Add large-Vec fold test (Risk 11).
- `/review` — The stdlib is Cranelisp's model code. Review it for idiom, clarity, and consistency from the first module.
