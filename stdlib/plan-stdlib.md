<!-- FIXME RESOLVED (Sprint 14 Wave 2):

     All items resolved. The prelude is now a re-export shell importing from
     domain modules per §3.2. Submodule primitive seeding works correctly
     (the FIXME(/int) was stale). Pipeline fix: modules with only type/trait
     definitions skip codegen after typechecking.

     Ring 2 Phase 1-3 modules implemented: compare/eq, compare/ord, num/num,
     text/display, fn/option, fn/result, fn/compose, default, collections/pair,
     collections/either, testing/assertions. List type still blocked by
     recursive type support not yet exercised in prelude.
     -->

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

## 1.5 Managed-surface model (S86 Phase 6b)

The stdlib presents a **managed, curated surface** rather than exposing raw
compiler primitives. The user thinks in Clojure-aligned vocabulary —
`(+ a b)`, `(= a b)`, `(< a b)`, `(show x)`, `(str …)`, `(count v)`,
`(get v i)`, `(conj v x)` — never in raw primitive names like `add-i64`,
`eq-i64`, `vec-get`. This is a **bare-name-curation concern only**
(S86 `/arch` sign-off): it governs which names the prelude/curated shell
re-export as *bare* names; it MUST NOT touch reachability.

**The three invariants that keep curation safe** (all pre-existing
normative text — spec §8.9.1 / §8.11.4 / §3.1 / §8.8.1):

1. **FQ always reachable.** `primitives/<name>` works regardless of
   imports and regardless of prelude content. The escape hatch is
   constitutionally guaranteed and never removed.
2. **Empty prelude valid.** The core language — primitives, special
   forms, inference — works with zero prelude content.
3. **Never load-bearing.** Nothing the curated surface re-exports may be
   the *only* way to reach a capability. Every capability stays
   expressible via the FQ form with an empty prelude.

**The three tiers of the surface:**

| Tier | What | How reached |
|---|---|---|
| **Bare prelude** | trait operators (`+ - * / = != < > <= >= show`), core types (`Int Bool Float String Option Some None Result Ok Err List Nil Cons Pair`), macros (`list vec str when unless cond case -> ->> def def- const const- do bind! pure`) | bare, no import |
| **Curated, module-qualified** | Clojure verbs `count`/`get`/`conj`/`assoc` (`collections.vec`) — bare-promotion of `count`/`get`/`conj` BLOCKED on DEF-1 (see §"de-leak status"); `first`/`rest` (`collections.list`); the `vec-*`/`*-list`/`seq-*` families, string verbs, num helpers | `(import [module [name]])` or `module/name` |
| **Raw primitives** | `add-i64`, `vec-get`, `str-concat`, … — **de-leaked from the prelude (S86); no longer bare** | `(import [primitives [name]])` or `primitives/name` |

**Naming reservation (FIXME 0402, `target: /spec`).** The bare names
`first`/`rest`/`get`/`count`/`map`/`filter`/`reduce` are **reserved** for
the future Phase-H trait-dispatched (Functor/Foldable) unified forms.
S86 does NOT promote them to bare prelude names — they stay
module-qualified — so the Phase-H trait method can own the bare name
without a §8.6.4 collision. (List `first`/`rest` and pair `first` already
coexist FQ-distinct; promoting either bare would collide.)

**The currently-globbed prelude BOUND set — the §8.6.4 collision surface**
(FIXME 0646, motivating instance). The prelude is `(import [prelude [*]])`
in scope of every downstream module (spec §8.6.4: prelude = an implicit
import, in scope identically to an explicit glob — NOT an outer scope). A
downstream `def`/`defn`/`defmacro`/`deftype`/`deftrait` of a bare name that
the prelude already globs is a **§8.6.4 CONFLICT (a compile error), not a
shadow** — the two bindings coexist in one scope and clash. So every
name in the glob is reserved against redefinition at the bare-name tier.
The set the prelude binds today (`stdlib/prelude.cl:27-52`) is:

| Source module | Bound names (bare) |
|---|---|
| `compare.eq` | `Eq` `=` `!=` |
| `compare.ord` | `Ord` `<` `>` `<=` `>=` |
| `num.num` | `Num` `+` `-` `*` `/` |
| `text.display` | `Display` `show` |
| `text.string` | `str` |
| `fn.option` | `Option` `Some` `None` |
| `fn.result` | `Result` `Ok` `Err` |
| `fn.threading` | `->` `->>` |
| `collections.list` | `List` `Nil` `Cons` `empty?` `list` |
| `collections.vec` | `vec` |
| `io.monad` | `pure` `do` `bind!` |
| `control` | `when` `unless` `cond` `case` |
| `defs` | `const` `const-` `def` `def-` |
| `primitives` (types) | `Int` `Bool` `Float` `String` |

**Rule for downstream surfaces** (examples, demos, docs, primers,
exemplar): pick names that do NOT collide with this set — a bare `def`/
`deftrait` over a globbed name errors, and (the 0646 trap) an ill-chosen
teaching name that happens to collide can MASK the actual failure under a
conflict diagnostic. FIXME 0646's instance: a REPL primer defined a bare
name colliding with the prelude glob, so the primer's own failure was
hidden behind the §8.6.4 conflict. When authoring across the prelude
boundary, either choose a fresh bare name or reach the intended symbol FQ /
via explicit import. This table decays as the prelude glob changes (e.g. a
DEF-1-unblocked `conj` promotion, §"de-leak status") — re-derive from
`stdlib/prelude.cl` when in doubt; the live `(export …)` forms are
authoritative.

### S86 de-leak status — LANDED (the raw-primitive half) + one carried defect

**The de-leak LANDED (S86 step 1.5d).** The ~31 raw-primitive bare
re-exports were **removed** from `prelude.cl`:

```
add-i64 sub-i64 mul-i64 div-i64 eq-i64 lt-i64 gt-i64 le-i64 ge-i64 not eq-bool
add-f64 sub-f64 mul-f64 div-f64 eq-f64 lt-f64 gt-f64 le-f64 ge-f64
str-concat str-eq str-len char-at int-to-string float-to-string bool-to-string
vec-len vec-get vec-set vec-push
```

Bare `add-i64`/`vec-get`/`str-eq`/… no longer resolve through the prelude
(REPL + `--run`: "undefined variable"). The user sees only the curated
surface: `(+ a b)`, `(- a b)`, `(* a b)`, `(/ a b)`, `(= a b)`, `(!= a b)`,
`(< a b)`, `(<= a b)`, `(show x)`. The **4 bare type re-exports**
(`Int Bool Float String`) are KEPT (needed for bare `:Int`-style
annotations; spec §3.1).

**Unblocked by two S86 compiler fixes:**
- **D1 (/typecheck):** trait DEFAULT-method bodies (`Eq`'s `!=`, `Ord`'s
  `<=`/`>=`) now resolve their free symbols in the trait's DEFINING module,
  not the call-site scope. Before the fix, dropping the bare `add-i64`
  re-export made `(!= 1 2)` / `(<= 2 2)` fail because the default-method
  body resolved at the call site. (Mirror of `recheck_body_for_mono`,
  FIXME 0355.) Verified: `(!= 1 2)` ⇒ true, `(<= 2 2)` ⇒ true,
  `(< false true)` ⇒ true — all de-leaked.
- **D2 (/backend + primitives):** the `neq-string` primitive now exists.
  Verified: `(!= "a" "b")` ⇒ true, `(= "a" "a")` ⇒ true — de-leaked.

**Curation invariants verified intact** (spec §8.9.1/§8.11.4/§3.1/§8.8.1):
FQ `(primitives/add-i64 3 4)` ⇒ 7, `(primitives/vec-get [10 20] 1)` ⇒ 20
work in REPL; a null-prelude module (`(import [prelude []])` +
`(import [primitives [add-i64 Int]])`) typechecks (only the `--run` IO-main
shape check fires, which is unrelated to resolution). No prelude leak is
load-bearing. **No existing code broke:** the exemplar (`exemplar/*.cl`)
uses bare primitives only via its own `(import [primitives [*]])` — the
de-leak removes prelude re-exports, not explicit imports.

**One carried defect — the collection-verb bare half (DEF-1).** The de-leak
also TARGETED promoting curated Vec verbs `count`/`get`/`conj` to BARE
prelude (so collection access needs no raw primitive). That half is BLOCKED
by a **pipeline defect, not a curation problem:** a plain `defn` that the
prelude only RE-EXPORTS (or imports-then-re-exports) is resolved by
typecheck but its body is never pulled into the *consuming program's*
codegen batch — `(count [1 2 3])` typechecks then fails at codegen with
"undefined function: count" (REPL and `--run` alike). The same defect
already affected the long-re-exported bare `pure` (`io.monad`), so it is a
PRE-EXISTING gap, not introduced by the de-leak. Root cause (per src survey):
`derive_codegen_batch` (`src/worker.rs:621`) emits only local
`ModuleEntry::Def` symbols; re-export/import installs `ModuleEntry::Import`,
which is codegen-skipped, and the prelude's import does not cascade the body
into the consuming module's batch. Trait methods (`+`/`show`) and macros
(`vec`) are unaffected (they materialise on demand at the call site — which
is exactly why the raw-primitive de-leak above succeeds). DEF-1 is routed to
`/qa` → `/int`. **Workaround that fully reaches the capability today:**
`(import [collections.vec [count get conj]])` then `(count [1 2 3])` ⇒ 3
(verified). So `count`/`get`/`conj`/`assoc` remain **module-qualified /
import-on-demand** (the "Curated, module-qualified" tier) until DEF-1 lands;
when it does, `count`/`get`/`conj` promote to bare prelude (the
`(export [collections.vec [count get conj]])` line, currently commented in
`prelude.cl`, un-comments). `assoc`/`first`/`rest`/`map`/`filter`/`reduce`
stay reserved for Phase-H trait dispatch (FIXME 0402) regardless.

### S86 self-test rollout — BLOCKED-and-carried on D3/D4/D5 (carried)

The TARGET was `(mod test …)` submodules across all modules, run via the
0273 in-language runner. BLOCKED this sprint by carried compiler defects in
the `(mod test …)`/cross-module path (committed RED guards; owned by
`/typecheck`+`/backend`, carried to pre-H). **`/stdlib` did NOT author any
`(mod test …)` submodules this step** — they would hit D3/D4 and
SIGSEGV/fail:

- **D3 — `(mod test)` re-defines parent trait.** A `(mod test …)` inside a
  trait-defining module re-enters the parent through the
  `testing.assertions` import chain (`compare.eq → compare.eq.test →
  testing.assertions → compare.eq`) and errors "trait Eq already defined".
  RED guard: `tests/spec_08_modules.rs::mod_test_child_in_trait_module_does_not_redefine_parent_trait`.
- **D4 — super-imported parent trait not in child scope.** A test submodule
  importing the parent trait via `super` resolves it in the wrong scope
  ("unknown trait Eq from module user"). RED guard:
  `tests/spec_08_modules.rs::mod_test_child_super_imported_parent_trait_resolves_as_constraint`.
- **D5 — cross-module/runner SIGSEGV.** Calling any `testing.runner`-defined
  fn cross-module SIGSEGVs (unresolved `__cranelisp_got_testing_runner`),
  blocking the runner path even for trait-free tests; the AOT-link path also
  fails (`undefined reference to discover-tests` — pre-existing Linux
  link-baseline). The S82/S83 "runner 4/4 pass" note does not reproduce on
  the current binary.

(The earlier `neq-string` blocker in this list was **D2**, now FIXED — String
`!=` works; it no longer blocks the self-test rollout. The remaining
blockers are the submodule-scope D3/D4 and the runner D5.)

Direct-call validation of trait-free `assert-true`/`assert-false` tests in
non-trait modules is the only path that partially works, but the circular
re-definition defect blocks adding `(mod test …)` to the trait-defining
foundation modules at all. Rollout resumes once `/qa`+owning skills clear
these. The intended test bodies are documented inline (see `compare/eq.cl`
§Self-tests) as the durable record of the planned coverage.

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
stdlib/
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

**`ord.cl`** — The Ord trait: `<`, `>`, `<=`, `>=` methods. Impls for Int, Float, **Bool** (S86: false < true), String. Functions: `min`, `max`, `clamp`. At Ring 3, adds `derive-Ord`. Depends on Eq. **S86 blocker:** `Ord String` is NOT implemented — lexicographic ordering needs a code-point comparison primitive (`char→int`/`str-lt`); the string primitive surface can test character equality but cannot order two differing characters. Tracked as a usability finding for a future `/platform`/`/spec` primitive addition; `Eq String` covers equality in the meantime.

**`hash.cl`** — The Hash trait: `(deftrait Hash (hash [self] Int))`. Impls for Int, String, Bool. Required by Map and Set. No derive initially — manual impls.

#### num/ — Arithmetic and Numerics

> **Decision (S86)**: Keep `Num` in `num.num` (re-exported bare through the prelude). The shell-module-plus-submodule shape (`num.cl` shell → `num/num.cl`, `num/int.cl`, `num/float.cl`) is the realised structure and matches the other domains (`compare`, `text`, `fn`, `collections`); promoting `Num` to a bare `num` module would make `num` both a leaf and a package. The `num/Unchecked` trait remains aspirational (not yet built; explicitly never in the prelude when it lands).

**`num.cl`** — The Num trait: `(deftrait Num (+ [self self] self) (- [self self] self) (* [self self] self) (/ [self self] self))`. Impls for Int, Float. Functions: `inc`, `dec`. This is where the builtin-to-trait transition happens — Ring 0 hardwired operators yield to trait dispatch.

**`int.cl`** — Int-specific operations beyond arithmetic: `abs`, `sign`, `even?`, `odd?`, `rem`, `quot`, `zero?`, `pos?`, `neg?`.

**`float.cl`** — Float-specific operations: `floor`, `ceil`, `round`, `sqrt`, `nan?`, `inf?`.

**`unchecked.cl`** — Unchecked arithmetic trait (overflow wraps instead of trapping). Not in prelude — explicit import required for intentional use.

#### text/ — Display and String Operations

> **Decision (S86)**: Keep `Display` in `text.display` (re-exported bare through the prelude), consistent with the §1.5 shell-plus-submodule structure used everywhere else. No promotion to a bare `text` module.

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

> **Decision (S86)**: Keep `pure`/`do`/`bind!` in `io.monad` (re-exported bare through the prelude), with `io.cl` as the shell. Consistent with the §1.5 structure; no promotion to a bare `io` module.

**`monad.cl`** — `pure` (lift value into IO), `bind!` macro (monadic bind sugar), `do` macro (monadic sequencing). Ring 4 — requires IO trampoline.

**`combinators.cl`** — Higher-order IO composition: `map-io`, `sequence-io`, `when-io`, `unless-io`. Ring 4.

#### testing/ — Validation

The stdlib's own test infrastructure. Also available to user programs.

> **Decision (S86)**: Keep the realised names `assert-eq`/`assert-true`/
> `assert-false`. They read as full English verbs (Clojure `is`-style
> brevity is not the house idiom here), and each returns `(Option String)`
> for the runner's None/Some fold. The shorter `assert=`/`assert`/`assert-some`/
> `assert-ok` family is deferred — it can be added as thin aliases later
> without breaking the current surface.

**`assertions.cl`** — `assert-eq` (needs Eq + Display), `assert-true`, `assert-false`. Each returns `(Option String)` — `None` on success, `(Some "reason")` on failure. Written using only functions and primitives (no macros), so it lights up at Ring 2.

**`runner.cl`** — `check` macro (chains assertions). The realised runner (FIXME 0273, S81) is an ordinary `vec-map`/`vec-filter` over the `discover-tests` pairs: `run-one`, `run-all`, `run-matching`, `report`, `tally`, `tally-line`, `passed?`, `present-one`, the `Outcome`/`Tally` ADTs, `discover-here`. The old `run-tests-*` special-form fold helpers were retired. **S86 note:** cross-module CALLS into `testing.runner`-defined fns currently SIGSEGV (unresolved `__cranelisp_got_testing_runner`) — see §1.5 "self-test rollout — blocked".

**`trace.cl`** — Accessors for the compiler-seeded Trace ADT: `trace-name`, `trace-params`, `trace-result`, `trace-children`, `trace-nanos`. Display functions: `trace-depth`, `trace-flatten`, `trace-show-tree`. Ring 4 — requires `trace` special form.

#### Depth-1 Singles

> **Decision (S86)**: When variadic `(or …)`/`(and …)` land, they go in
> `control` (alongside `cond`/`case`/`when`/`unless`) — they are
> short-circuiting control-flow macros, not `Eq`/`Ord`-style value
> operators. (Not yet built.)

**`control.cl`** — Branching macros: `cond` (multi-way if-else), `case` (equality dispatch), `when` (one-sided if), `unless` (negated when). Ring 3.

**`defs.cl`** — Definition macros: `const` (inline sexp substitution), `def` (named zero-arg fn + macro), `const-` (private const), `def-` (private def). Ring 3.

**`default.cl`** — `(deftrait Default (default [] self))`. Impls for Int (0), Float (0.0), Bool (false), String (""), Option (None). The "zero value" trait. Ring 2. Backing self-test `default/test.cl` shipped S112 6b (parent declares `(mod- test)`); exercises each impl via the annotation-selected `(let [x :Int (default)] …)` form (return-type dispatch, S112 leg (c)).

> **Prelude-promotion decision (S113 6b, /stdlib): DECLINE — keep
> module-qualified.** S112's deferral rested on two reasons; D2 (reason 2) is
> now RULED and LANDED, so the blocker is gone and the decision is a pure
> weight call — which /stdlib resolves AGAINST promotion. `Default`/`default`
> stay reached by explicit import — now `(import [default [default]])`
> (method-only, no trait) OR `(import [default [Default default]])` OR FQ.
>
> **D2 resolved (S113).** The user ruled *importing a trait METHOD without its
> TRAIT suffices for dispatch* (`spec §7.11.2`); the typecheck fix landed in
> W2a. Verified end-to-end (S113 6a): `(import [default [default]])` then
> `(let [x :Int (default)] …)` dispatches to the Int impl and runs — all four
> impls (Int/Float/Bool/String) confirmed. The S112 "residual defect" note in
> `default.cl` is retired. This method-only reachability IS the S113 ergonomic
> win, and it costs zero §8.6.4 reservation.
>
> **Promotion is technically sound but declined on intent.** Glob-import
> return-dispatch works (`(import [default [*]])` → annotated `(default)`
> resolves; verified), and DEF-1 does not block it (trait methods materialise
> on demand at the call site, like `+`/`show`). The four reasons to decline:
> **(1)** the prelude promotes *pervasive bare operators* (`+ = < > show`);
> `default` is called rarely and is not in this plan's §4 prelude spec.
> **(2)** `default` is annotation-required to dispatch — bare `(default)` is
> `§3.11`-ambiguous (verified diagnostic), so it is never "bare and
> productive" the way `(+ 1 2)` is; promotion saves one import line while the
> `:Type` annotation stays at every call site. **(3)** `default` is a
> high-traffic bare word — globbing it reserves it against every downstream
> module-level `(defn default …)`/`(def default …)` at the §8.6.4 collision
> surface (§1.5 BOUND set), a poor trade for a niche trait. (Rust precedent
> cuts *against*: Rust puts the *trait* `Default` in prelude but `default()` is
> always called qualified — `T::default()` — so the bare word never collides;
> Cranelisp's `default` is a bare free function.) **(4)** consistency — Hash,
> Functor, Foldable (the other non-operator foundation traits) are all
> module-qualified; Default belongs with them.
>
> **§1.5 BOUND set unchanged** — `default`/`Default` are NOT added to the glob;
> no reservation taken. This is a movable boundary: the user arbitrates at
> Phase 7, and may revisit if a real scenario demands frictionless bare
> `default` (contingency = the one-line `(export [default [Default default]])`
> promotion + BOUND-row + §4 update, S114).

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

## 13. Ring 3 Dependencies — Prelude Macro Survey (Sprint 9)

Analysis of the 12 prelude macros from `spec/09-macros.md` section 9.10, classifying each by required macro features and runtime dependencies. This informs the Ring 3 implementation order.

### Macro Feature Classification

| Macro | Clauses | Bracket Destr. | `&` rest | Quasiquote | `begin` | Helpers needed |
|-------|---------|---------------|----------|------------|---------|----------------|
| `const` | single | no | no | yes (`\``) | no | `quote-sexp` primitive |
| `const-` | single | no | no | yes | no | `quote-sexp` primitive |
| `def` | single | no | no | yes | yes | `quote-sexp`, `make-def-name` |
| `def-` | single | no | no | yes | yes | `quote-sexp`, `make-def-name` |
| `list` | multi (2) | no | yes | yes | no | `sfold`, `sreverse` |
| `vec` | single | no | yes | no | no | none (direct `SexpBracket` ctor) |
| `do` | multi (2) | no | yes | yes | no | recursive self-call |
| `bind!` | single | yes | no | yes | no | recursive helper or self-call |
| `cond` | multi (2) | no | yes | yes | no | recursive self-call |
| `case` | single | no | yes | no | no | recursive `case-fold` helper |
| `->` | single | no | yes | no | no | recursive `thread-first-fold` helper |
| `->>` | single | no | yes | no | no | recursive `thread-last-fold` helper |
| `str` | multi (2) | no | yes | yes | no | recursive `str-fold` helper |
| `when` | single | no | no | yes | no | none |

### Required Macro Infrastructure by Phase

**Phase A — Core macro pipeline (no quasiquote needed):**
- `vec` — single-clause, variadic, no quasiquote. Uses direct `SexpBracket` constructor. Simplest possible macro.

**Phase B — Quasiquote engine:**
- `const`, `const-` — single-clause, quasiquote + `quote-sexp` primitive.
- `when` — single-clause, quasiquote only. No helpers.

**Phase C — Multi-clause + variadic + quasiquote:**
- `do` — multi-clause, variadic, quasiquote with recursive self-call.
- `cond` — multi-clause, variadic, quasiquote with recursive self-call.
- `list` — multi-clause, variadic, quasiquote. Needs `sfold`, `sreverse` from SList helpers.
- `str` — multi-clause, variadic. Needs `str-fold` helper (recursive, builds `str-concat`/`show` chains).

**Phase D — Helpers + `begin`:**
- `def`, `def-` — single-clause, quasiquote + `begin` multi-form. Needs `make-def-name` helper.
- `case` — single-clause, variadic. Needs `case-fold` recursive helper (manual Sexp construction, no quasiquote in body).
- `->`, `->>` — single-clause, variadic. Need `thread-first-fold`/`thread-last-fold` recursive helpers.

**Phase E — Bracket destructuring:**
- `bind!` — single-clause, bracket destructuring on bindings parameter, quasiquote. Needs recursive fold over binding pairs.

### Runtime Dependencies

| Macro | Runtime dependency | Ring gate |
|-------|--------------------|-----------|
| `const`, `const-` | none (pure substitution) | Ring 3 |
| `def`, `def-` | none (defines a zero-arg fn) | Ring 3 |
| `vec` | Vec type (Ring 1) | Ring 3 |
| `list` | List type with `Cons`/`Nil` (Ring 1) | Ring 3 |
| `when` | none | Ring 3 |
| `do` | `let` (core language) | Ring 3 |
| `cond` | `if` (core language) | Ring 3 |
| `case` | `let`, `if`, `=` via Eq trait (Ring 2) | Ring 3 |
| `str` | `show` via Display trait (Ring 2), `str-concat` primitive | Ring 3 |
| `->`, `->>` | none (pure syntactic rewriting) | Ring 3 |
| `bind!` | `bind` function from IO model (Ring 4) | **Ring 4** (useless without IO) |

### Key Findings

1. **All prelude macros except `bind!` can be implemented and tested at Ring 3.** `bind!` depends on the `bind` function from the IO model (Ring 4), so while the macro itself can be *defined* at Ring 3, it cannot be *used* until IO arrives.

2. **`vec` is the simplest macro** (no quasiquote, no helpers) and should be the first prelude macro implemented, making it ideal for validating the macro pipeline end-to-end.

3. **SList helpers (`sfold`, `sreverse`, `sconcat`) are prerequisites for `list` and `str`.** These must be defined in `core/syntax.cl` (or its reimplementation equivalent) before those macros.

4. **`case` depends on Eq trait** (`=` operator) which is Ring 2 infrastructure. The macro itself is Ring 3 but its expansion uses `=`, so it requires that Eq impls are registered.

5. **`begin` multi-form support is required only by `def`/`def-`.** All other macros return a single Sexp.

6. **Bracket destructuring is required only by `bind!`.** This is the most complex parameter form and can be deferred to the end of Ring 3 macro implementation.

7. **Recommended implementation order**: `vec` -> `when` -> `const`/`const-` -> `do` -> `cond` -> `list` -> `str` -> `case` -> `->` / `->>` -> `def`/`def-` -> `bind!`.

---

## 14. Sprint 11 Preparation (Sprint 10, Wave 1)

Analysis of `/stdlib` deliverables for Sprint 11, based on macro infrastructure built in Sprint 10 (Phases 1-4) and pipeline integration (Phase 5, early Sprint 11).

### 14.1 SList Helper Dependency Matrix

Which prelude macros depend on which SList helpers:

| Helper | Used by | How |
|--------|---------|-----|
| `sfold` | `list` | Folds over reversed element list to build nested `(Cons e acc)` |
| `sreverse` | `list` | Reverses element list so `sfold` builds `Cons` in correct order |
| `sconcat` | `~@` (quasiquote-splicing) | Emitted by the quasiquote expander for splice operations; used implicitly by any macro with `~@` in its body (`do`, `cond`, `str`, `bind!`) |
| `sempty?` | (no direct prelude macro use) | Available for user-written recursive macros that need a base-case test on `(SList Sexp)` |

Additional helper functions needed by specific macros (these are NOT SList helpers but are macro-authoring utilities):

| Helper | Used by | Purpose |
|--------|---------|---------|
| `quote-sexp` | `const`, `const-`, `def`, `def-` | Converts runtime `Sexp` to a self-reproducing `Sexp` (primitive or stdlib fn) |
| `make-def-name` | `def`, `def-` | Appends `"-def"` suffix to a symbol name, producing backing fn name |

### 14.2 Implementation Order Confirmation

The recommended order from section 13 is: `vec` -> `when` -> `const`/`const-` -> `do` -> `cond` -> `list` -> `str` -> `case` -> `->` / `->>` -> `def`/`def-` -> `bind!`.

After Sprint 10 builds Phases 1-4 and Sprint 11 wires in Phase 5 (pipeline integration + two-pass prelude loading), this order **holds with one refinement**:

1. **`vec`** — simplest macro (no quasiquote, no helpers). Validates the end-to-end pipeline.
2. **`when`** — single-clause, quasiquote only. Validates quasiquote expansion.
3. **`const` / `const-`** — requires `quote-sexp`. Validates bare-symbol expansion.
4. **`do`** — multi-clause, recursive self-call. Validates multi-clause dispatch.
5. **`cond`** — multi-clause, recursive self-call. Similar pattern to `do`.
6. **`list`** — multi-clause, requires `sfold` + `sreverse`. **SList helpers must be compiled before this point.**
7. **`str`** — multi-clause, recursive. Requires `show` (Display trait, Ring 2).
8. **`case`** — manual Sexp construction, needs `=` (Eq trait, Ring 2).
9. **`->` / `->>`** — variadic, recursive fold over forms. Pure syntactic rewriting.
10. **`def` / `def-`** — requires `begin` multi-form + `make-def-name` + `quote-sexp`. Most complex infrastructure dependency.
11. **`bind!`** — bracket destructuring. Definable at Ring 3 but untestable until Ring 4 (IO).

**Refinement**: `bind!` should still be *defined* in Sprint 11 to validate bracket destructuring, but marked as Ring 4 for testing.

### 14.3 SList Helper Ordering Constraint

The SList helpers (`sfold`, `sreverse`, `sconcat`, `sempty?`) are **ordinary Cranelisp functions**, not macros. They must be compiled as regular `defn` forms before any macro that references them. This creates a hard ordering requirement in the two-pass prelude loading sequence:

1. SList helpers are defined in `lib/core/syntax.cl` (or the reimplementation equivalent, `lib/macros.cl` per section 3.2).
2. The module containing these helpers must be loaded and compiled **before** `lib/prelude.cl` processes its `defmacro` forms.
3. Per spec section 9.12, Pass 2 processes forms sequentially — a `defmacro` body can call functions defined earlier. So the module loading order must be: `macros.cl` (SList helpers) -> `prelude.cl` (prelude macros).

The `sconcat` function has an additional constraint: it is referenced by quasiquote-generated code (`~@` expansion emits qualified `macros/sconcat` calls). It must be compiled and resolvable before any macro whose body uses `~@` is expanded.

### 14.4 Sprint 11 Stdlib Task Summary

`/stdlib` deliverables for Sprint 11:

**(a) SList helper functions** — in `lib/macros.cl`:
- `sfold`, `sreverse`, `sconcat`, `sempty?` as `defn` forms
- `slist` as a `defmacro` (convenience constructor for `(SList a)`)
- Only `sconcat` re-exported through prelude (per spec section 9.7.0)

**(b) Macro-authoring helpers** — in `lib/macros.cl` or `lib/defs.cl`:
- `make-def-name` — symbol name transformation for `def`/`def-`
- `quote-sexp` — either as a stdlib function (pattern match on all 7 Sexp variants) or as a compiler primitive

**(c) Prelude macros** — in `lib/prelude.cl` (or distributed across `lib/control.cl`, `lib/defs.cl`, `lib/fn/threading.cl`, etc. per section 3.2):
- 12 macros in the order from section 14.2
- Each macro validated by at least one integration test

**(d) Prelude wiring** — update `lib/prelude.cl` to re-export Ring 3 additions (~12 names per section 4): `cond`, `case`, `when`, `const`, `def`, `->`, `->>`, `derive`, `list`, plus macro-specific helpers.

---

## 15. Sprint 59 Audit Reconciliation — `(import [prelude []])` Null-Import Surface

Closes Sprint 58 Wave 6 /review Important finding **I-2** (stdlib audit count drift).

### Authoritative count

**35 `.cl` source files** carry `(import [prelude []])`. Sprint 58 commit `98bf4ef`
reported 32 — an undercount of 3. (A 36th match is in `stdlib/CLAUDE.md`, which is
documentation citing the convention, not a source file.)

### Enumerated audit surface (35 files)

Root-level modules (14):
- `stdlib/collections.cl`, `stdlib/compare.cl`, `stdlib/control.cl`, `stdlib/core.cl`
- `stdlib/default.cl`, `stdlib/defs.cl`, `stdlib/derive.cl`, `stdlib/fn.cl`
- `stdlib/io.cl`, `stdlib/num.cl`, `stdlib/seq.cl`, `stdlib/testing.cl`
- `stdlib/text.cl`
- (note: `stdlib/prelude.cl` is the re-export shell and does NOT carry `(import [prelude []])` — it IS the prelude)

Submodules (21):
- `collections/`: `either.cl`, `list.cl`, `pair.cl`, `vec.cl`
- `compare/`: `eq.cl`, `ord.cl`
- `core/`: `io.cl`, `syntax.cl`, `trace.cl`
- `fn/`: `compose.cl`, `option.cl`, `result.cl`, `threading.cl`
- `io/`: `monad.cl`
- `num/`: `float.cl`, `int.cl`, `num.cl`
- `seq/`: `lazy.cl` (Defect 2 resolved in 98bf4ef)
- `testing/`: `assertions.cl`, `runner.cl`
- `text/`: `display.cl`, `string.cl`

### Spot-check: the 3 files missed by the Sprint 58 audit

The three files most likely to have been missed — per the Sprint 58 /review
finding — are `stdlib/derive.cl`, `stdlib/defs.cl`, `stdlib/default.cl`. Each
re-checked against the `seq/lazy.cl` defect pattern: **bare identifiers
referenced without explicit imports, masked by an earlier dep-load race and
surfaced only after /int's Defect 1 fix**.

| File | Explicit imports | Bare identifiers used | Verdict |
|---|---|---|---|
| `stdlib/derive.cl` | `primitives [*]`, `macros [*]`, `core.syntax [sfold sreverse sempty? slist]` | All bare names (`SNil`, `SCons`, `SexpSym`, `SexpList`, `SexpBracket`, `SexpStr`, `add-i64`, `str-concat`, etc.) resolve via the three wildcard/explicit imports | **CLEAN** |
| `stdlib/defs.cl` | `primitives [*]` | Qualified references only (`primitives/quote-sexp`, `macros/SexpSym`, `macros/SexpList`, `macros/SCons`, `macros/SNil`, `primitives/str-concat`). No bare unqualified names outside macro local bindings | **CLEAN** |
| `stdlib/default.cl` | `fn.option [Option None]` | `Int`, `Float`, `Bool`, `String` — these are compiler-seeded primitive types (not symbols that need import) resolved by the typechecker's builtin type table. `None` is explicitly imported. No other bare names | **CLEAN** |

No analogous defect to `seq/lazy.cl` exists in these three files. The
Sprint 58 conclusion ("`seq/lazy.cl` was the only at-risk file") holds after
the count correction.

### Fixes applied

None. All three spot-checked files resolve their identifiers correctly under
the null-prelude-import regime. No source changes required; no FIXMEs filed.

### Demo status

`repl/demos/stdlib-progress.demo` (Ring 3, owned by `/repl`) exercises the
prelude surface: trait-dispatched operators (`+`, `=`, `<`, `show`),
constrained polymorphism, `Option`/`Result` pattern matching, `str` macro,
string primitives (`to-upper`, `split`, `join`, `replace`, `trim`, `contains?`),
compose/pipeline. Static read confirms the demo references only names that
the current prelude re-export shell provides (per `stdlib/CLAUDE.md`'s
"Prelude re-exports" list). No drift detected between the demo and current
stdlib API shape.

### I-2 closure

Authoritative count locked at 35. Audit surface fully enumerated. Three
spot-checked files clean. Sprint 58 Wave 6 /review Important finding I-2
resolved.

---

## 26. Stage C.2 Rollout Design (Sprint 87, Phase 3)

The de-risked S86 follow-up. S86 closed having FIXED the compiler blockers
that stopped the self-test rollout and the bare-verb promotion last sprint:
**D3** (`(mod test)` child re-defines parent trait — `register_trait_decl`
now idempotent on structurally-identical re-registration), **D4**
(`super`-imported parent trait now seeded into child constraint scope), and
**DEF-1** (re-export-only `defn` body now reaches the consuming program's
codegen batch — the mono chokepoint `collect_imported_constrained_calls`
routes through `resolve_terminal_entry_or_prelude`). **D5** (the
`testing.runner` cross-module-call SIGSEGV) — the runner's own `(mod test)`
submodule already ships green again per `testing/runner.cl` §S82/S83 notes;
the dev-session-runner path (`discover-tests`) is REPL-live by design
(`test-discovery.md §4.5`). This section is the **authoring plan for Phase 5**
— no `.cl` is edited in Phase 3.

> **Dependency on the 0402 ruling (binding, R4).** The bare-verb promotion
> below is **conditioned on the FIXME 0402 ruling that resolves in Stage A
> FIRST** (`target: /spec`, curated-overload naming reservation). 0402
> reserves `first`/`rest`/`get`/`count`/`map`/`filter`/`reduce` as
> Phase-H trait-dispatched names. This plan assumes the **default ruling**
> (0402's proposed resolution: those bare names stay reserved; concrete
> families keep disambiguated names). If `/spec` rules differently, the
> promotion set in §26.2 adapts per the table there. **No name this plan
> promotes bare may pre-bind a reserved Phase-H trait name.**

### 26.0 Constitutional invariants (must survive the rollout)

All three are pre-existing normative text (§1.5); the rollout MUST NOT
weaken any of them, and each is on the Phase-5 acceptance checklist:

1. **`primitives/<name>` FQ path stays valid** — every capability the
   curated surface offers is also reachable FQ with an empty prelude.
2. **Empty prelude stays valid** — `(import [prelude []])` + core language
   works with zero prelude content. The promoted verbs are convenience,
   never load-bearing.
3. **Bare-name curation MUST NOT change reachability** — promoting a verb
   to bare prelude only changes how it is *named at the call site*; the
   module-qualified and FQ paths to the same `defn` are unchanged.

### 26.1 Self-test rollout

**Mechanism (DISTINCT from `tests/`).** Stdlib self-tests are `(mod test …)`
submodules *inside each stdlib module*, asserting with
`testing.assertions` (`assert-true`/`assert-false`/`assert-eq`) and run via
the in-language runner (`testing.runner` — `discover-tests` → `run-all` /
`run-matching` in a live REPL session, or `run-one` direct-call in any mode).
They are NOT in the `tests/` suite (owned by `/qa`, free-standing,
zero-stdlib-dependency per CLAUDE.md §Stdlib separation). The
free-standing discipline is preserved by construction: this work lives
entirely under `stdlib/`.

**The proven pattern (the template every submodule follows).**
`testing/runner.cl` already ships a green `(mod test)` submodule (S82/S83):
it imports the parent module's symbols via **`super`** (D4-path, fixed) and
asserts with `assert-true`/`assert-false`/`assert-eq`. That is the template.
The trait-defining modules (`compare/eq`, `compare/ord`, `num/num`,
`text/display`) were the ones that hit **D3** (now fixed: idempotent
re-registration) — their test submodules import the parent trait + methods
via `super` rather than re-importing `testing.assertions` through a chain
that re-enters the parent.

**Rollout order** (bootstrap-first, per §5.3 — the foundation validates the
rest; matches the §6.2 keystone sequence):

| Wave | Modules | What the `(mod test)` asserts |
|---|---|---|
| **S1 (keystone)** | `testing/assertions.cl` | `assert-true`/`assert-false`/`assert-eq` return `None` on success, `(Some why)` on failure — the harness self-validates first (if this works, everything downstream is trustworthy). |
| **S2 (trait bedrock — was D3-blocked)** | `compare/eq.cl`, `compare/ord.cl`, `num/num.cl`, `text/display.cl` | `(= 1 1)`⇒true / `(= 1 2)`⇒false / `(!= "a" "b")`⇒true; `(< 1 2)`, `(<= 2 2)`, `Ord Bool` `(< false true)`; `(+ 2 3)`⇒5, `(* 2 3)`, `inc`/`dec`; `(show 42)`⇒"42", `(show true)`. (The intended bodies are already documented inline in `compare/eq.cl §Self-tests` — promote them to a real `(mod test)`.) |
| **S3 (core types)** | `fn/option.cl`, `fn/result.cl`, `collections/pair.cl`, `collections/either.cl` | `(is-some? (Some 1))`, `unwrap-or`, `map` over Some/None; `Ok`/`Err`, `is-ok?`, `map-err`, `and-then`; pair `first`/`second`/`swap`; `Left`/`Right`, `map-left`/`map-right`, `either`. |
| **S4 (collections + num/text helpers)** | `collections/list.cl`, `collections/vec.cl`, `num/int.cl`, `num/float.cl`, `text/string.cl` | list `first`/`rest`/`length`/`reverse`/`fold`; vec `count`/`get`/`conj` + `vec-map`/`vec-filter`/`vec-reduce`; `abs`/`even?`/`odd?`/`rem`; `abs-float`/`min-float`; string `blank?`/`index-of`/`reverse-str`/`pad-left`. |
| **S5 (fn + defaults + derive)** | `fn/compose.cl`, `default.cl`, `derive.cl` | `compose`/`pipe`/`identity`/`flip`; `Default` `(default)` per type; derive-Eq/Ord/Display on a small test ADT. |

**Per-submodule shape** (the canonical form, all waves):

```clojure
(mod test
  ;; parent symbols via super (D4 path — fixed); harness via import
  (import [super [<names under test>]])
  (import [testing.assertions [assert-true assert-false assert-eq]])

  (defn test-<behaviour> []          ; (Fn [] (Option String)) — test- prefix
    (assert-true (<predicate under test>)))
  ...)
```

**How they are run / verified** (cannot depend on `tests/`):

1. **In-language runner, live REPL** — the primary path.
   `(import [testing.runner [run-all run-matching report]])` then
   `(report (run-all))` in a REPL session loaded with the stdlib prelude.
   `discover-tests` returns the eligible `test-*` fns (correct `test-`
   prefix AND exact `(Fn [] (Option String))` signature); `run-all` folds
   each three-way (pass / assertion-fail / panic) via `catch-runtime-error`.
   Green = every `test-*` returns `None`.
2. **Direct-call, any mode** — for the pure helpers and as a `--run`-mode
   smoke check: a tiny driver `(defn -main [] (report (run-matching "test-")))`
   exercises the runner's pure path (`run-one`/`tally`/`report`) which works
   in every mode (the `discover-tests` *host extern* is REPL-only, but the
   fold machinery is not).
3. **Demo replay** — `repl/demos/*` (owned by `/repl`) that load the prelude
   replay green at each wave gate, confirming no surface drift.

**Defect-handoff posture.** If authoring a `(mod test)` surfaces a NEW
language defect (not a stdlib bug), the wave is not closed until `/qa` has a
narrow failing-not-ignored repro with `// spec:` + `FIXME(/owner)` (CLAUDE.md
§Usability Findings and Defects). Two specifically-flagged candidates to
watch (pre-existing, carried as design notes, NOT assumed present):
- The **fork-join error-slot ferry** defect (`test-discovery.md` §"OWED…") —
  only if a self-test wraps `catch-runtime-error` *around a parallel branch*
  (a `Par`/lenient-`let` spark). Keep self-tests sequential to avoid it; if a
  test legitimately needs it, route the surfaced defect to `/qa`, don't
  work around it silently.
- Any residual D3/D4-class re-entry in a module not yet exercised — the S87
  Stage-A entry check confirms the live red set is exactly the 4 named
  guards, so a fresh red here is a genuine regression, route to `/qa`.

### 26.2 Bare-verb promotion (the `(export …)` un-comment)

DEF-1 is FIXED — a `defn` the prelude only re-exports now reaches the
consuming program's codegen batch. This de-risks promoting the curated
collection verbs from **module-qualified** to **bare prelude**. The verbs
already exist as wrappers in their domain modules (`collections/vec.cl`:
`count`/`get`/`conj`/`assoc` over `vec-len`/`vec-get`/`vec-push`/`vec-set`;
`collections/list.cl`: `first`/`rest`). Promotion is purely the
`prelude.cl` re-export line — **bare-name curation, MUST NOT touch
reachability** (invariant 3).

**The 0402 conditioning — what may and may not be promoted.** 0402 reserves
`first`/`rest`/`get`/`count`/`map`/`filter`/`reduce` as Phase-H
trait-dispatched bare names. Promoting any of those bare now would
**pre-bind a reserved Phase-H trait name** (R4 — forbidden). So the
promotion is conservative and adapts to the ruling:

| Verb | Domain module | 0402 status (proposed ruling) | S87 promotion decision |
|---|---|---|---|
| `count` | `collections.vec` | **RESERVED** (Phase-H Foldable/collection trait) | **DO NOT bare-promote.** Stays module-qualified / import-on-demand. |
| `get` | `collections.vec` | **RESERVED** (Phase-H) | **DO NOT bare-promote.** Module-qualified. |
| `first` | `collections.list` (+ pair `first`) | **RESERVED** + §8.6.4 list-vs-pair collision | **DO NOT bare-promote.** Both stay FQ-distinct. |
| `rest` | `collections.list` | **RESERVED** (Phase-H seq trait) | **DO NOT bare-promote.** Module-qualified. |
| `conj` | `collections.vec` | **NOT reserved** by 0402 | **BARE-PROMOTE** (un-comment) — no Phase-H trait name collision; safe under DEF-1 fix. |
| `assoc` | `collections.vec` | **NOT reserved** by 0402 (Phase-H Map verb candidate, but not in 0402's list) | **CANDIDATE** — promote bare only if `/spec` confirms it is not a future trait-dispatched name. Default: HOLD module-qualified pending 0402 ruling confirmation; promote in a follow-up if cleared. |

> **Net effect under the default 0402 ruling:** of the six verbs named in
> the S87 task (`count`/`get`/`conj`/`assoc`, `first`/`rest`), only **`conj`**
> is unambiguously bare-promotable in-sprint; **`assoc`** is a conditional
> candidate; the other four (`count`/`get`/`first`/`rest`) stay
> module-qualified because they are 0402-reserved Phase-H trait names.
> This is the de-risked, forward-compatible subset — it removes the raw
> primitive (`vec-push`) need for the most common append idiom (`conj`)
> while not pre-binding any name the Phase-H trait must own. **The full
> Clojure collection-verb surface arrives bare at Phase H via trait
> dispatch, owning these reserved names cleanly** — this sprint does not
> race it.

**The mechanism.** Un-comment in `prelude.cl` (currently the commented
"Curated collection verbs" block, lines ~54–81):

```clojure
(export [collections.vec  [conj]])          ; bare-promoted (0402-safe)
;; (export [collections.vec [assoc]])       ; HOLD — pending 0402 assoc ruling
;; count/get/first/rest stay module-qualified — 0402-reserved (Phase H)
```

If `/spec`'s actual 0402 ruling **releases** any of the reserved names for
S87 concrete binding (override of the proposed resolution), add the matching
`(export …)` line(s) per the same one-line mechanism — the verbs already
exist; only the re-export changes.

**Verification of each promotion** (Phase 5, the acceptance gate for §26.2):
1. **Reachability unchanged (invariant 3):** before and after, the verb is
   reachable FQ (`collections.vec/conj`) and via import — promotion adds the
   bare path, removes nothing.
2. **DEF-1 fix exercised:** `(conj [1 2] 3)` bare (no import) typechecks
   AND codegens AND runs in BOTH the REPL and `--run` — the exact shape that
   failed pre-DEF-1 ("undefined function: count"). This is also the durable
   stdlib-side regression guard for DEF-1.
3. **Empty prelude still valid (invariant 2):** a `(import [prelude []])`
   module still compiles; the promoted bare name is simply absent there.
4. **No existing code broke:** exemplar + demos replay green (they import
   primitives explicitly, so the promotion does not touch them; this
   confirms the promotion is additive).

### 26.3 Adequacy-gap intake (triage of the Stage C.1 `/port` gap list)

Stage C.1 (`/port`) produces a **collated, prioritized stdlib gap list** from
re-reading the Sudoku exemplar — each entry naming the exemplar site
(`file:line`), what was awkward, and the proposed stdlib feature. `/port`
pre-classifies each entry as **pure stdlib gap** or **compiler/language gap**.
`/stdlib`'s triage applies this **decision rule**:

> **DECISION RULE.** For each gap entry:
> 1. **Compiler/language gap** (the feature needs typecheck / codegen / spec /
>    new-primitive support) → **ROUTE OUT, not in-sprint.** Feed it to the
>    Stage B audit backlog (`audits/s87-findings.md`) and/or file a numbered
>    FIXME (`design/arch/fixmes/NNNN-name.md`, `target:` the owning skill) per
>    CLAUDE.md §Cross-Skill Changes. Record the entry in §26.4 of this plan
>    with its routing destination. **Do NOT author a stdlib workaround for a
>    compiler gap** — that bakes a workaround into the model code.
> 2. **Pure stdlib gap** (a missing function/macro **composable from existing
>    primitives + existing stdlib**, needing no compiler change) → assess
>    **cheap AND obviously-correct**:
>    - **Cheap** = adds to an existing domain module, no new module, no new
>      type, ≤ ~15 lines of public API, follows an existing Clojure-aligned
>      pattern.
>    - **Obviously-correct** = the implementation is a direct composition with
>      no inference-friction risk, AND it ships with a `(mod test)` self-test
>      in the same change-set (§26.1 discipline).
>    - **Both true → ACTION IN-SPRINT** (Phase 5), with self-test.
>    - **Either false** (large, new module/type, ambiguous semantics, naming
>      that might collide with a Phase-H reserved name per 0402, or
>      inference-risky) → **DEFER** into this plan (§26.4) with rationale +
>      target sprint. Borderline cases default to DEFER (a deferred gap is
>      cheap to revisit; a rushed wrong API is expensive to retract).
> 3. **0402 cross-check (mandatory for every pure-stdlib action):** if the
>    proposed name is on the 0402 reserved set, it is NOT actioned bare —
>    same conditioning as §26.2.

**Why route compiler gaps out, not action them:** the exemplar's flagship
awkwardness (per S86 FIXME 0408) — copy-per-guess grid + no parallel search —
is a *language/perf* gap, not a stdlib gap; actioning it in stdlib would be a
workaround masking the real audit input. Compiler/language gaps are precisely
the Stage B audit's currency; routing them there keeps the backlog complete
and prevents stdlib from accreting band-aids. (CLAUDE.md §Stdlib separation +
the project's "defects need failing tests, not doc-only closure" discipline.)

### 26.4 Gap-intake ledger (populated Phase 5 from C.1 `§FULL`)

Source: `exemplar/notes-stdlib-adequacy-s87.md §FULL` (G1–G10). Each row:
`gap` | `exemplar site` | `classification` | `disposition`.

| Gap | Site | Class | Disposition (S87 Stage C.2) |
|---|---|---|---|
| **G1** | `grid.cl:83-126` (9-bit mask layer) | [COMPILER] bitwise intrinsics | **STDLIB-COVERED (S87 hygiene) + intrinsics route-out HELD.** A reusable `num.bits` module (composed from arithmetic, §26.8) now provides the bitwise API. FIXME 0416 (`target: /arch`) stays **OPEN** for the COMPILER-intrinsics version (a future perf-driven decision — the stdlib version is O(width) per op, an intrinsic is one CLIF instruction). The exemplar's `grid.cl` bit layer can now adopt `num.bits/*` (a `/port` `.cl` swap, not stdlib's job). |
| **G2** | `grid.cl`/`solver.cl`/`html.cl` (bare `vec-push` not `conj`) | [COMPILER] DEF-2 heap-ADT-`conj` RC | **ROUTE-OUT** — repro queued for /qa → /backend (no new FIXME). Not actioned in stdlib (would bake a workaround). |
| **G3** `range` | `solver.cl`/`grid.cl`/`html.cl`/`form.cl` (~15 hand-threaded index folds) | [STDLIB] authoring | **ACTION-IN-SPRINT** — `(range lo hi)` added to `collections/vec.cl`, **HALF-OPEN [lo,hi)** (Clojure `(range start end)` semantics: inclusive lo, exclusive hi). Empty when `hi<=lo`. Ships with 5 self-tests (`collections/vec/test.cl`). Unreserved by §11.4a (but NOT bare-promoted; reached module-qualified / import). |
| **G4** `char-to-digit`/`digit-to-char` | `form.cl:41-53`, `grid.cl:191-202` | [STDLIB] authoring | **ACTION-IN-SPRINT** — both added to `text/string.cl` (`-1` sentinel for non-digit; empty string for out-of-range). 6 self-tests. **NAMING:** the proposed `char->digit`/`digit->char` do NOT parse (a `defn` name containing `->` is mis-read as the threading-macro head — see DEFECT D-name below); shipped as `-to-` spelling. |
| **G5** `replace-at`/`str-assoc` | `form.cl:57-59` | [STDLIB] authoring | **ACTION-IN-SPRINT** — both added to `text/string.cl` (`str-assoc` is the Clojure-aligned alias of `replace-at`). Out-of-range `idx` returns `s` unchanged. 4 self-tests. |
| **G6** `int-to-string` adoption | `solver.cl:197-207` | [STDLIB] adoption | **DEFER** — exemplar-side `.cl` swap, owned by `/port` (the `digit-to-char` from G4 also serves this; verb exists). Not a stdlib authoring gap. |
| **G7** `num.int/rem` reuse | `grid.cl:68-69` etc. | [STDLIB] adoption | **DEFER** — exemplar redefines `rem-i64`; `num.int/rem` already exists. `/port` swap; DEF currently rationalises the inline alias. |
| **G8** `repeat-str` adoption | `form.cl:33-38` | [STDLIB] adoption | **DEFER** — `text.string/repeat-str` exists; `/port` swap. |
| **G9** `str` macro adoption | `html.cl`/`solver.cl`/`user.cl` | [STDLIB] adoption (optional) | **DEFER / DO-NOT-FORCE** — `text.string/str` exists; exemplar deliberately avoids it (documented in `exemplar/CLAUDE.md`). Flag only. |
| **G10** reuse `rem`/`row-of`/`col-of` | `user.cl:45-48` | [STDLIB] adoption | **DEFER** — verbs exist; `/port` de-duplication. |

**Net Stage-C.2 stdlib authoring delivered:** G3 `range`, G4 `char-to-digit`/
`digit-to-char`, G5 `replace-at`/`str-assoc` — all composable from existing
primitives + existing stdlib, ≤~15 LOC each, each ships with self-tests. The
5 adoption gaps (G6–G10) are exemplar-side `.cl` swaps owned by `/port` (the
verbs already exist), not stdlib authoring. The 2 [COMPILER] gaps (G1/G2) are
routed out, not worked around.

### 26.6 Defects surfaced by the Stage-C.2 rollout (handoff to /qa)

Authoring the self-tests + gaps surfaced several **language/compiler defects**
(not stdlib bugs). Each needs a narrow failing-not-ignored repro by /qa →
owning skill (CLAUDE.md §Usability Findings and Defects). The stdlib-side
record (a correct `(mod test)` that can't go green, or a workaround) is noted.

1. **D-either (discover-tests SIGBUS on two-param ADT). — RETIRED S115 6b.**
   The S87 record: running `collections.either.test` through the discover-tests
   → `run-one` path SIGBUSed on `test-is-right`, the `(Either String Int)`
   `(Right 1)` shape (heap-ADT, String-then-Int field order), while the same
   assertion passed when called directly. **Re-verified at S115 6b: the module
   runs 6 passed / 0 failed / 0 panicked through that path, reproducibly.** The
   note is retired from `collections/either/test.cl`; `test-is-right` stays as
   the standing guard for the shape that used to crash.

   The path itself is NOT exonerated. FIXME 0835 shows the same
   discover-tests → `run-one` path aborting in glibc on a **two**-level nested
   heap ADT (`SCons` of `SCons` of `SexpSym`); `(Either String Int)` is one
   level. The S87 diagnosis was pointed at the right seam and the wrong depth.

2. **D-name (`->` in a `defn` name fails to parse). — RETIRED S115 6b.**
   The S87 record: `(defn char->digit "doc" [..] ..)` failed with `parse error
   … defn: expected params [...] or variant`, the reader treating the `->` in
   the symbol as the threading-macro head. **Re-verified at S115 6b: it parses.**
   `(defn char->digit "doc" [:String ch] :Int 1)` now defines
   `:(Fn [primitives/String] primitives/Int) user/char->digit` and calls
   correctly. The shipped names stay `char-to-digit`/`digit-to-char` — they have
   been public since S87 and are used by the exemplar, so renaming would break
   callers for a cosmetic match with a never-normative proposal. Recorded in
   `text/string.cl` so it is not re-litigated from the stale blocker.

3. **D-default (nullary return-type-polymorphic trait method → codegen).**
   `:Int (default)` typechecks but fails `codegen error … undefined function:
   default` — a nullary trait method whose only type info is the return type
   does not monomorphise/dispatch at codegen even with a `:Type` annotation.
   Blocks the `default` self-test (held — see `default.cl`). → **/qa repro →
   /typecheck/backend.** Minimal: `(deftrait T (z [] self)) (impl T Int (defn
   z [] 0)) (:Int (z))`.

4. **D-derive (same-module macro in its own `(mod test)`). — CONSUMER MODULE
   BUILT S115 6b.** The limitation stands and is the documented §9.3.4
   behaviour: a `(derive …)` call inside derive.cl's own submodule forms fails
   at expansion, because the `derive`/`derive-*` macros are defined in the same
   module. The consumer-side test this row deferred in S87 — and that nothing
   built for three sprints — now exists: **`stdlib/derive/test.cl`** (module
   `derive.test`), a separate module that imports the macros from `super` and
   derives against its own four ADTs. 28 tests green.

   Building it immediately surfaced what its absence had been hiding: two
   conformance breaks that made `derive-Eq`/`derive-Ord` fail at EVERY use
   (`derive-Eq` never emitted `!=`, `derive-Ord` never emitted `<=`/`>=` — both
   fixed S115 6b, both pinned by that module), plus FIXMEs 0815/0816/0835. This
   is the §26.1 discipline's clearest single data point: the module was
   declared delivered at S87 and was non-functional the whole time.

5. **D-regen-strips-`(mod test)` + in-place-stdlib test isolation.** The REPL
   source-regeneration path strips an INLINE `(mod test …)` body to a bare
   `(mod test)` (the §8.2.5 one-time-extraction behaviour) but does NOT write
   the extracted `…/test.cl` backing file when the lib dir is the in-place
   workspace `stdlib/`. Combined with the e2e tests that point
   `CRANELISP_LIB` at the in-place real `stdlib/`
   (`use_workspace_stdlib_for_stdlib_conformance_only`), a full parallel
   `cargo nextest run` was observed to STRIP every inline-bodied stdlib
   `(mod test)`, corrupting the working tree and breaking the prelude load.
   **Stdlib-side mitigation applied:** every self-test is authored as a
   SEPARATE backing file (`<mod>/test.cl`) with a bare `(mod test)` in the
   parent — extraction-stable (nothing to strip), so a full `cargo nextest run`
   leaves the tree byte-identical (verified). → /qa + /int may still want to
   fix the regen-write-target / test-isolation (tests should copy stdlib to a
   tmpdir, not use it in place), but the stdlib rollout no longer depends on it.

### 26.7 `conj` bare-promotion — HELD (0402 ruling reserves `conj`)

The Phase-3 plan (§26.2) assumed the **proposed** 0402 resolution left `conj`
unreserved and so bare-promotable in-sprint. The **actual** /spec ruling
recorded in `spec/11-stdlib.md §11.4a` (Stage A, this sprint) RESERVES `conj`
explicitly: the §11.4a table row reads *"`conj` … Do NOT re-export bare `conj`
through the prelude until the trait owns the name."* Bare-promoting `conj`
would therefore pre-bind a reserved Phase-H trait name (R4 — forbidden).

**Decision: HOLD `conj` (and `assoc`) module-qualified.** No `(export …)` line
is added to `prelude.cl`. The full reserved set — `map`/`filter`/`reduce`/
`count`/`get`/`conj`/`assoc`, `first`/`rest` — stays module-qualified /
import-on-demand. The capability is fully reachable
(`(import [collections.vec [conj]])` then `(conj v x)`, verified ⇒ works;
`collections.vec/conj` FQ; `vec-push` primitive). When the Phase-H collection
trait is built, it owns these bare names cleanly. Net S87 bare-promotion: NONE
(the conservative, forward-compatible subset under the actual ruling is empty).

### 26.8 `num.bits` — bitwise ops as STDLIB (S87 hygiene; FIXME 0416 stdlib coverage)

**Intake: 0416-as-stdlib.** FIXME 0416 (`target: /arch`) proposes adding bitwise
*intrinsics* (`band`/`bor`/`bxor`/`bnot`/`ishl`/`ushr`/`popcnt`) to the primitive
surface — a 1:1 CLIF lowering. That **COMPILER decision stays DEFERRED** (a future
perf-driven call by `/spec` for width/shift semantics + `/backend` for lowering;
0416 remains OPEN, not deleted). User direction 2026-06-21: *"this should be in
stdlib for now"* — so the same surface ships **now** as a pure-stdlib module
composed from existing Ring 0 arithmetic.

**Module:** `stdlib/num/bits.cl` (registered `(mod bits)` in `num.cl`; module
`num.bits`). Self-tests in `num/bits/test.cl` (bare `(mod test)` in the parent —
the S87 extraction-stable backing-file convention, §26.1).

**WIDTH decision: 30 bits** (positions 0..29) for the fixed-width ops
(`bit-and`/`bit-or`/`bit-xor`/`bit-not`/`popcount`). 30 keeps `(pow2 width)` and
a fully-set mask inside the positive Int range, so the arithmetic simulation
never touches the sign bit. `bit-not x` is therefore the **one's complement
within the low 30 bits** (`(- (full-mask) x)`), NOT a machine two's-complement —
the correct model for bitmask/flags/candidate-set domains (operands expected
non-negative, < 2^30). The exemplar's 9-bit Sudoku masks fit comfortably.

**Ops (Clojure-aligned names):** `bit-and`, `bit-or`, `bit-xor`, `bit-not`,
`bit-shift-left`, `bit-shift-right`, `bit-test`, `bit-set`, `bit-clear`,
`bit-flip`, `popcount`, plus the building blocks `pow2`, `full-mask`, `width`,
`bit-at`. **Composition:** `(1<<n)≡(pow2 n)`; `(x<<n)≡(* x (pow2 n))`;
`(x>>n)≡(/ x (pow2 n))`; `bit n ≡ (rem (/ x (pow2 n)) 2)`; and/or/xor are a
bit-by-bit fold over 0..width re-weighting each result bit by `(pow2 i)`;
`bit-not ≡ (- (full-mask) x)`; `popcount` folds the set bits. None of these
names are reserved by §11.4a, so they are safe; reached **module-qualified /
import-on-demand — NOT bare-promoted** to the prelude (import-on-demand per the
managed-surface model).

**Self-tests:** 23 `test-*` fns in `num/bits/test.cl` covering every op against
known values (`12&10=8`, `12|10=14`, `12^10=6`, shift round-trips, bit-test/set/
clear/flip, `bit-not` round-trip, `popcount(full-mask)=30`). **Verified green**
via the in-language runner: `(discover-tests ["num.bits.test"])` → `run-one` →
`tally-line` reports `23 passed, 0 failed, 0 panicked`.

**Note for /port:** `exemplar/grid.cl`'s ~55-line C3 bit layer (`pow2`,
`bit-set?`, `bit-clear`, `bit-set`, `bit-count`, `bit-lowest`) can now adopt
`num.bits/*` (`bit-test`/`bit-clear`/`bit-set`/`popcount`, etc.). That is a
future exemplar-side `.cl` swap owned by `/port`, not stdlib authoring.

### 26.5 Phase-3 plan for SPRINT.md "Skill plans / /stdlib"

**Task.** Stage C.2 stdlib rollout (de-risked S86 follow-up), three parts:
(1) author `(mod test)` self-test submodules across stdlib modules in the
bootstrap order S1→S5 (§26.1), run via the in-language runner; (2)
bare-promote the 0402-safe curated collection verb(s) — `conj` (and `assoc`
if 0402 clears it), un-commenting the matching `(export …)` in `prelude.cl`
now that DEF-1 is fixed, holding the 0402-reserved `count`/`get`/`first`/`rest`
module-qualified (§26.2); (3) triage the Stage C.1 `/port` adequacy-gap list
per the §26.3 decision rule — action cheap + obviously-correct pure-stdlib
gaps in-sprint (each with a self-test), route compiler/language gaps to the
Stage B audit backlog / FIXME store, defer the rest into §26.4 with rationale.

**Design refs.** `stdlib/plan-stdlib.md` §1.5 (managed-surface model + the
three curation invariants), §26 (this rollout design); `stdlib/CLAUDE.md`
S86 state; `design/arch/fixmes/0402-spec-curated-overload-naming-reservation.md`
(the binding naming reservation — must be RESOLVED in Stage A before §26.2
authoring); `design/arch/test-discovery.md` §4.3/§4.5/§5/§6 (runner +
dev-session scope + the fork-join ferry note); `testing/runner.cl §S82/S83`
(the proven `(mod test)` + `super`-import template); `tests/spec_08_modules.rs`
D3/D4 guards (the fixes that unblock the trait-module self-tests); S86 archive
DEF-1 entry (the fix that unblocks the bare promotion).

**Sequencing / dependencies.**
- Depends on **0402 resolving in Stage A first** (R4) — §26.2's promotion set
  is conditioned on the ruling; the conservative default ships only `conj`.
- Authoring is **source-touching → single agent at a time, serial with the
  Stage-A Wave-0 fixes** (CLAUDE.md §Testing — worktree isolation broken).
- **C.1 gates into Wave 2** (SPRINT.md Phase-4 note) — §26.3 triage consumes
  the C.1 list, so the gap-intake part runs after C.1 produces it; the
  self-test rollout (§26.1) and `conj` promotion (§26.2) do NOT depend on C.1
  and proceed on the green base.

**Acceptance.**
1. **Self-tests green** — every authored `(mod test)` submodule's `test-*`
   fns return `None` under the in-language runner (`(report (run-all))` in a
   prelude-loaded REPL session shows 0 failures across waves S1–S5); the
   direct-call pure-helper path (`run-one`/`report`) works in `--run` mode.
2. **`conj` bare-promoted + guarded** — `(conj [1 2] 3)` bare (no import)
   typechecks, codegens, and runs in BOTH REPL and `--run` (the DEF-1
   regression shape); `count`/`get`/`first`/`rest` confirmed still
   module-qualified-reachable (not bare) per the 0402 reservation; `assoc`
   per the 0402 ruling.
3. **Constitutional invariants intact** — `primitives/<name>` FQ reachable;
   `(import [prelude []])` empty-prelude module compiles; no promoted verb is
   load-bearing (each reachable FQ with empty prelude). Guarded by the
   existing spec-conformance suite (the FQ-path / empty-prelude guards).
4. **Adequacy gaps dispositioned** — every C.1 gap entry recorded in §26.4
   with an explicit disposition; in-sprint pure-stdlib actions each ship with
   a `(mod test)` self-test; compiler/language gaps routed to the audit
   backlog / FIXME store (not worked around in stdlib).
5. **Free-standing discipline preserved** — `tests/` and `examples/` remain
   zero-stdlib-dependency (no edits there); self-tests are stdlib-internal
   `(mod test)` submodules only.
6. **Prior demos / exemplar replay green** — `repl/demos/*` (prelude-loading)
   + `exemplar/` replay green at the wave gate; `cargo nextest run --workspace`
   shows no regression beyond the (now-cleared) Stage-A named guards.

**Next skills.**
- `/qa` — narrow repro for any NEW language defect a `(mod test)` surfaces
  (the durable record + cross-skill trigger); confirm the DEF-1 bare-`conj`
  guard and the spec-conformance FQ/empty-prelude guards stay green.
- `/repl` — demos model the post-promotion curated surface (bare `conj`);
  refresh `stdlib-progress`-style demos if the bare set changed.
- `/spec` — if the 0402 ruling releases any reserved name for S87 binding,
  this plan's §26.2 promotion set widens per the one-line `(export …)` mechanism.

---

## 27. Future byte-backed text track (Sprint 117 design record)

**Status: UNIMPLEMENTED.** This section records a future stdlib shape; it does
not describe the current language. Cranelisp currently has native `String`.
There is no native `Byte`, `(Vec Byte)` text representation, `Utf8Literal`,
transparent one-field text wrapper, or stdlib replacement for the native
`int-to-string` primitive.

The architecture recommendation in `design/arch/byte-backed-text.md` is:

- a future native `Byte` with user-settled semantics, occupying one `i64`
  register and one ordinary wide Vec slot initially;
- ordinary `(Vec Byte)`, using the generic Vec surface rather than a native
  `Bytes` type or a Byte-only Vec implementation;
- a compiler-certified nominal `Utf8Literal` candidate whose payload is
  representation-identical to `(Vec Byte)`;
- Unicode policy in stdlib, not in primitive `Char` types;
- compact Byte storage deferred to a later general element-layout extension
  of Vec.

### 27.1 Prospective module split

Names remain provisional until the user settles the public text type and
conversion contracts. The responsibility split should be:

| Prospective module | Responsibility |
|---|---|
| `text.bytes` | Byte-vector construction, slicing, comparison, and explicit byte indexing |
| `text.utf8` | UTF-8 validation plus checked conversion between arbitrary `(Vec Byte)` and validated text |
| `text.code-point` | Unicode scalar decoding/encoding and code-point iteration |
| `text.grapheme` | Grapheme segmentation and grapheme-oriented traversal |
| `text.normalize` | Explicit normalization transforms and normalization-form policy |
| `text.encoding` | UTF-16/UTF-32 and other approved alternate representations |
| `text.format` | Numeric and value formatting, including stdlib `int-to-string` |

The modules must expose whether an index is a byte, code point, or grapheme;
plain ambiguous indexing is forbidden. Invalid UTF handling, normalization,
certification, and literal naming remain user/spec gates. Native `String` and
its primitives stay live until behavioral coverage, mode parity, migration,
and removal policy are separately approved.

### 27.2 `int-to-string` algorithm

The future implementation needs no native character type or host formatter.
It uses a ten-entry certified ASCII digit table and keeps the working integer
non-positive:

1. zero produces the single zero digit;
2. a positive input is converted to its negative counterpart;
3. while `n < 0`, compute `q = n / 10`;
4. compute the digit as `-(n - q * 10)`, which is in `0..9`;
5. append or prepend the corresponding digit byte and continue with `q`;
6. add the minus byte iff the original input was negative.

The negative domain is essential: `INT_MIN` is representable, while
`abs(INT_MIN)` is not. The exact builder and checked validated-text result
wait for the Byte/literal boundary.

Required future self-tests:

| Case | Required result/property |
|---|---|
| zero | `"0"` |
| positive | decimal digits with no leading zero |
| negative | one leading `-`, correct magnitude |
| `INT_MAX` | exact maximum signed-64 decimal spelling |
| `INT_MIN` | exact minimum signed-64 decimal spelling without overflow |

### 27.3 Delivery gates

No stdlib implementation begins until:

1. the user settles Byte, literal, validation, invalid-input, and public text
   naming semantics;
2. `/spec` records those decisions;
3. `/arch` promotes the representation and cache/ABI contracts;
4. ordinary wide-slot `(Vec Byte)` and certified literal construction exist;
5. `/qa` approves the byte/text verification matrix.

Packing is an independent later gate. The initial wide representation is the
same language API at lower storage precision, not a temporary `Bytes` model.

### 27.4 `def` function-value API

Sprint 117 did not settle FIXME 0800 face 3. The concrete stdlib options,
trade-offs, and decision gate are recorded in
`stdlib/def-face-3-options.md`. No option is selected here, and the question
remains independent of FIXME 0863's compiler-side presentation transaction.

---

## Next Skills

- `/arch` — Confirm the builtin-to-trait transition strategy. Validate that cross-module trait impls work (trait in module A, type in module B, impl in module B). Review Map/Set implementation strategy.
- `/frontend` — Update `~@` expansion to emit `macros/sconcat` instead of `core.syntax/sconcat`.
- `/typecheck` — Coordinate operator resolution handoff: Ring 0 `ResolvedCall::BuiltinFn` must transparently yield to Ring 2 `ResolvedCall::TraitMethod` when trait impls are loaded. Fix `parse-int` return type when Option is available.
- `/backend` — Add missing string primitives (`substring`, `char-at`, etc.) as extern functions in `cranelisp-runtime` when Ring 2 needs them.
- `/qa` — Plan stdlib self-test execution. Add tests for closure-capturing-heap-types. Process usability findings U1.1–U1.5. Add large-Vec fold test (Risk 11).
- `/review` — The stdlib is Cranelisp's model code. Review it for idiom, clarity, and consistency from the first module.
