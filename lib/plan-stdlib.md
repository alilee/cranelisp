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

**`num.cl`** — The Num trait: `(deftrait Num (+ [self self] self) (- [self self] self) (* [self self] self) (/ [self self] self))`. Impls for Int, Float. Functions: `inc`, `dec`. This is where the builtin-to-trait transition happens — Ring 0 hardwired operators yield to trait dispatch.

**`int.cl`** — Int-specific operations beyond arithmetic: `abs`, `sign`, `even?`, `odd?`, `rem`, `quot`, `zero?`, `pos?`, `neg?`.

**`float.cl`** — Float-specific operations: `floor`, `ceil`, `round`, `sqrt`, `nan?`, `inf?`.

**`unchecked.cl`** — Unchecked arithmetic trait (overflow wraps instead of trapping). Not in prelude — explicit import required for intentional use.

#### text/ — Display and String Operations

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

**`monad.cl`** — `pure` (lift value into IO), `bind!` macro (monadic bind sugar), `do` macro (monadic sequencing). Ring 4 — requires IO trampoline.

**`combinators.cl`** — Higher-order IO composition: `map-io`, `sequence-io`, `when-io`, `unless-io`. Ring 4.

#### testing/ — Validation

The stdlib's own test infrastructure. Also available to user programs.

**`assertions.cl`** — `assert-eq` (needs Eq + Display), `assert-true`, `assert-false`. Each returns `(Option String)` — `None` on success, `(Some "reason")` on failure. Written using only functions and primitives (no macros), so it lights up at Ring 2.

**`runner.cl`** — `check` macro (chains assertions, Ring 3). `run-tests-pass-default`, `run-tests-fail-default`, `run-tests-report` (Ring 4 — need Trace type and `run-tests` special form).

**`trace.cl`** — Accessors for the compiler-seeded Trace ADT: `trace-name`, `trace-params`, `trace-result`, `trace-children`, `trace-nanos`. Display functions: `trace-depth`, `trace-flatten`, `trace-show-tree`. Ring 4 — requires `trace` special form.

#### Depth-1 Singles

**`control.cl`** — Branching macros: `cond` (multi-way if-else), `case` (equality dispatch), `when` (one-sided if), `unless` (negated when). Ring 3.

**`defs.cl`** — Definition macros: `const` (inline sexp substitution), `def` (named zero-arg fn + macro), `const-` (private const), `def-` (private def). Ring 3.

**`default.cl`** — `(deftrait Default (default [] self))`. Impls for Int (0), Float (0.0), Bool (false), String (""), Option (None). The "zero value" trait. Ring 2.

**`derive.cl`** — The `derive` dispatch macro: `(derive [Eq Ord Display] MyType)` expands to calls to `derive-Eq`, `derive-Ord`, `derive-Display` which live in their respective trait modules. Ring 3.

**`macros.cl`** — The macro-writing toolkit: `sfold`, `sreverse`, `sconcat`, `sempty?`, `slength`, `snth`, `smap`, `sdrop`, `slist` construction macro, `scontains?`. Operates on the compiler-seeded `Sexp` and `SList` types from the `macros` synthetic module. Ring 3.

<!-- FIXME(/frontend): The ~@ (unquote-splicing) operator currently emits references to core.syntax/sconcat. In the new module layout, this should be macros/sconcat. Coordinate the qualified path. -->

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

## Next Skills

- `/arch` — Confirm the builtin-to-trait transition strategy. Validate that cross-module trait impls work (trait in module A, type in module B, impl in module B). Review Map/Set implementation strategy.
- `/frontend` — Update `~@` expansion to emit `macros/sconcat` instead of `core.syntax/sconcat`.
- `/typecheck` — Coordinate operator resolution handoff: Ring 0 `ResolvedCall::BuiltinFn` must transparently yield to Ring 2 `ResolvedCall::TraitMethod` when trait impls are loaded.
- `/qa` — Plan stdlib self-test execution. The `.test` submodule pattern needs to be compatible with the test runner infrastructure.
- `/review` — The stdlib is Cranelisp's model code. Review it for idiom, clarity, and consistency from the first module.
