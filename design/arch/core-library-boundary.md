# Core and library boundary — technical determinations

**Status.** Determination record, `arch`, 2026-11-21. It answers the fifteen
rows of the specification's open question S124-Q16 that need a technical
determination. It approves and schedules nothing: the user confirms the
classification, then `spec` revises the chapters. Retire this document when
stage two of S124-Q16 closes, after any compiler consequence below has its own
action.

**The rule applied.** [Spec §8.8.3](../../spec/08-modules.md#883-empty-prelude)
(user ruling, 2026-11-21): the specification rests on no prelude; a construct
a library or a user can implement on the language as specified belongs to the
library; a construct that cannot is a built-in or primitive, and a built-in
macro emits fully-qualified references to primitives. The inventory and each
row's question are in
[appendix D](../../spec/appendix-d-open-questions.md), S124-Q16.

**Evidence.** Each row cites the specification and source at `ed7e4182`.
Probes ran on 2026-11-21 against the existing debug binary, with no prelude,
no standard library and a cleared environment; a probe is named where a row
rests on one. Where a row is evidence-limited it says what would settle it.

## 1. The fifteen determinations

| Row | Determination | Basis | If confirmed |
|---|---|---|---|
| CL04 `Num`, `Eq`, `Ord`, `Display`, operators, `show` | **Library.** Every declaration, impl and method is an ordinary `deftrait` or `impl` over primitives that exist: `primitives/add-i64` and its siblings, `eq-*`, `neq-*`, `lt-*` to `ge-*`, `str-eq`, `int-to-string`, `float-to-string`, `bool-to-string`, `string-identity` | `stdlib/num/num.cl` and its siblings define them so. The compiler seeds no trait: `crates/cranelisp-typecheck/src/builtins.rs::test_no_traits_at_startup`. Spec §7.7's implementation note, which calls them compiler-seeded, is false against source. Value display (spec §12.9) is the compiler's own renderer and reads no `Display` impl | Spec-only, plus one compiler change (§3, C1) |
| CL05 `Functor`, `fmap` | **Library.** A single-parameter higher-kinded trait is in the language (spec §7.2, §7.3.4), and the three described instances, `Option`, `List` and `Seq`, are impls on user-declared ADTs | `examples/26-functor.cl` (`Option`, `IO`); `tests/spec_07_traits.rs::hkt_impl_on_user_well_kinded_adt_dispatches`. Evidence-limited for `Seq`: no instance on a type with a thunk field was found or run; one cell settles it | Spec-only |
| CL07 `bind` | **Language: a built-in is required.** The sequencing node has type `IO a → (a → IO b) → IO b`, existential in `a`. `deftype` refuses a variable its head does not declare (probe: "type variable `b` is not declared by the type head"), and a user function cannot run an `Effect` to feed a continuation. The user's recollection is correct | The built-in exists: `primitives/bind`, `(Fn [(IO a) (Fn [a] (IO b))] (IO b))`, seeded by `src/bootstrap.rs::register_bind_primitive` and lowered inline by the backend (`IoCombinator::Bind`). Spec §10.3 already says so; spec §3.2.3's "can be defined as ordinary library functions" is true of `pure` and false of `bind` | Spec-only. §2 lists two things `spec` should see |
| CL10 scheduling, ordering and launch rules | **Expressible over the core composition; no sugar is recognised.** The analysis runs after macro expansion on an application whose callee resolves to `primitives/bind` and whose second argument is a one-parameter lambda. A discarded result and source order are properties of that shape | [Bind-chain analysis §1 and §3.1](../int/bind-chain-analysis.md); `src/bootstrap.rs::bind_primitive`; `src/bind_chain_analysis.rs` tests no `do` or `bind!` spelling (read by search). `stdlib/io/monad.cl` expands both macros to `primitives/bind` | Spec-only: §10.12 and §12.4 are restated over `bind` chains |
| CL19 user-callable `sconcat` | **Library.** General `(SList a)` concatenation is a two-arm recursive function over `macros/SCons` and `macros/SNil` (probe: a user definition concatenates and returns the expected length) | The compiler's helper `macros/sconcat` is a different thing: it is monomorphic, `(SList Sexp)`, and is what quasiquote emits (`crates/cranelisp-frontend/src/quasiquote.rs::make_sconcat`). Its public callability stays the user's Q12-R1 question; `stdlib/fn/threading.cl` calls it today | Spec-only |
| CL20 `slist` | **Library.** A two-clause variadic `defmacro` with quasiquote, emitting `macros/SCons` and `macros/SNil` qualified | `stdlib/core/syntax.cl` | Spec-only |
| CL21 named macro-building helpers | **Library; none is needed.** Each is a function from `Sexp` to `Sexp` over the compiler-seeded constructors and `primitives/str-concat`. No language facility is missing | Only `make-def-name` exists (`stdlib/core/syntax.cl`). The standard library writes `do`, `bind!`, `cond`, `case`, `->`, `->>` and `str` by multi-clause recursion with no helper (`stdlib/io/monad.cl`, `stdlib/control.cl`, `stdlib/fn/threading.cl`, `stdlib/text/string.cl`). The seven unwritten helpers are asserted expressible, not run | Spec-only |
| CL24 collection and pipeline helpers | **Library.** Every concrete-family function is expressible over `primitives/vec-len`, `vec-get`, `vec-set`, `vec-push`, user ADTs and closures. `map`, `filter`, `reduce`, `count` and `conj` across families need only a single-parameter higher-kinded trait. `get` and `assoc` across keyed families need a second trait parameter, which spec §7.12.1 excludes and §7.12.2 keeps future | `stdlib/collections/vec.cl`, `stdlib/collections/list.cl`, `stdlib/seq/lazy.cl`. `inc`, `head`, `fold-list`, `lazy-take` and `lazy-drop` are not in the standard library and are one-line definitions. §2 records one limit on `Vec` | Spec-only |
| CL31 `timeout` | **Library.** `(race (map-io Some io) (map-io (fn [_] None) (sleep d)))` | `stdlib/core/io.cl`. Probe: a user definition with no library returns `Some` when the action wins and `None` when the timer wins. That the loser is cancelled is inherited from the first-completion node and was not measured here; the existing timeout cells are the evidence. Needs `primitives/select` or `race`, `primitives/sleep`, `primitives/Option`, `primitives/bind` | Spec-only: §12.4.4 stops calling it part of the language's IO model |
| CL32 `race`, `select`, `sleep` | **`select` and `sleep` are language; `race` is derivable.** First completion with cancellation of the losers needs the trampoline and reactor, and a timer needs the reactor. `(race a b)` is `(select [a b])` (probe: a user `race` over `select` gives both `timeout` outcomes) | All three exist as built-ins: `primitives/race`, `primitives/select`, `primitives/sleep`, seeded by `src/bootstrap.rs::register_combinators` and lowered by the backend's `IoCombinator`. Evidence-limited: the equivalence of `race` and a two-branch `select` was observed for the value only, not for tie order, a panicking branch or cancellation timing | `select`, `sleep`: spec-only. `race` as library: a stdlib change and a compiler change (§3, C2) |
| CL34 library-based programs and transcripts | **No further compiler-only dependency found.** The samples use the rows above, the `primitives` ADTs and functions, quasiquote, `trace` and the `platform.stdio` effects that appendix B imports explicitly | Evidence-limited: the samples were scanned, not each run. Running every sample with explicit imports and no prelude settles it, as the `user/` sample harness does for the guides | Spec-only |
| CL35 prelude contents in `/mod` turns | **No particular content is required.** Parity is "the turn compiles under the imports the file body compiled under, the implicit prelude import included, whatever it supplies". `+`, `show` and `Int` are examples of content | REPL §3.9; spec §8.8.1. The suite's parity cells run on the test prelude, not the standard library's, so parity already holds for a different content | Spec-only |
| CL36 alternative collections and channels | **Mixed.** Persistent vectors, maps and deques are expressible now as ADTs over `Vec` and `primitives/bit-and`, `shr` and `popcount`. A `Hash` trait is declarable, and its `Int` and `Bool` impls expressible. Its `String` and `Float` impls are not: no primitive yields a byte, a character code or a float's bits. Channels are not expressible: the language has no shared mutable cell and no parking operation, so they need runtime effects from intrinsics or a platform. A type backed by new extern functions needs a compiler or platform change by definition | The primitive names in `crates/cranelisp-primitives/src/declarations.rs` (read by search; appendix A.3 would confirm the list is complete); spec C.2.2, C.2.4, C.4.4, which already call these runtime additions | Spec-only now. Each capability names its primitive when it is scheduled |
| CL37 bit helpers | **Library.** One-line wrappers over `primitives/shl`, `shr`, `bit-and`, `bit-or`, `eq-i64` and `not` | `stdlib/num/bits.cl` | Spec-only |
| CL38 `trace-show`, `trace-call-string` | **Library.** Functions over the `Trace` ADT and string primitives | `stdlib/core/trace.cl` imports only `primitives` and `macros` | Spec-only |

## 2. The rows `spec` classified

No classification is disputed. Source agrees with each: `Option`, `Result` and
`Pair` are seeded in `primitives` and the standard library re-exports them
(`stdlib/fn/option.cl`, `stdlib/fn/result.cl`, `stdlib/collections/pair.cl`);
`derive` is syntactic over the `deftype` form (`stdlib/derive.cl`); every
library macro row is a `defmacro` in the standard library.

Four observations for stage two, none a dispute:

- **Spec §3.2.3 gives `IO` as `(deftype (IO a) (IOVal [:a ioval]))`.** Source
  seeds the constructors `Pure`, `Effect` and `Bind`.
- **`primitives/Bind` is callable.** The seeded constructor is marked internal,
  and a user function `(defn mybind [io f] (primitives/Bind io f))` compiles
  and sequences (probe). Spec §10.3 calls the node internal. A chain built
  this way is not a `bind` chain, so it runs sequentially. Whether the
  constructor is part of the language is a question for the user.
- **`Vec` is refused as a higher-kinded impl target.**
  `(impl (Functor f) (Functor Vec) …)` fails with "Vec has 0 type parameters"
  (probe). Spec C.2.4 expects primitive and library collections to share
  collection traits. Whether that is a defect is `qa`'s to classify.
- **Library macros emit bare library names.** `when` and `unless` emit `Some`
  and `None`, `case` emits `=`, `str` emits `show`. That is the library's
  concern; the rule's qualified-reference clause binds built-in macros.

## 3. Consequences that are compiler changes

Neither is approved or scheduled.

- **C1 (CL04): the compiler names library traits by spelling.**
  `crates/cranelisp-typecheck/src/traits/dispatch.rs::primitive_for_trait_method`
  replaces a trait method call with a primitive when the trait is spelled
  `Num`, `Eq`, `Ord` or `Display`, the method has the expected spelling and
  the type is a primitive. It does not look at the impl's body.
  - **It is a defect today, independent of the classification.** A user trait
    `Num` whose `Int` impl defines `+` as `sub-i64` returns 8 for `(+ 5 3)`;
    the same program with the trait renamed returns 2 (probe). Its intake and
    reproduction are `qa`'s.
  - **The change is interior to typecheck.** The table's product is the
    existing `BuiltinFn` resolution, so no public item and no crate boundary
    is involved. Removing it costs a constant factor per operator call, which
    the dev tier does not keep
    ([Principle 27](principles/27-dev-tier-optimises-only-against-blow-up.md));
    keying it on a name is against
    [Principle 19](principles/19-no-module-privileged-by-name.md).
- **C2 (CL32, only if `race` is classified library):** remove the `race`
  built-in. It crosses crates: the binary seeds it
  (`src/bootstrap.rs::register_combinators`) and the backend lowers it
  (`IoCombinator::Race`), and the intrinsics runtime may hold a body only it
  reaches. The standard library gains a one-line `race`. Keeping `race` as a
  built-in beside `select` is the no-change alternative; the rule's wording
  is "SHOULD", so the choice is the user's.

Every other row is a specification move with no source change.
