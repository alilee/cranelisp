# ADT typing

Owner: `design` narrow-deployed to typecheck. Subordinate to `typecheck.md` §9.4.
Covers type-definition registration, constructor schemes, the product dual facet,
constructor-pattern inference and exhaustiveness. Required behaviour:
`spec/05-definitions.md` §5.2 and `spec/06-pattern-matching.md`.

Neighbouring designs this one uses without restating:

| Subject | Design |
|---|---|
| Canonical `Type.Ctor` keys, the bare candidate, the member resolver and exhaustiveness normalisation | [`dotted-ctor-registration.md`](dotted-ctor-registration.md) |
| Field accessors: keying, candidates and which fields get one | [`fixme-0365-field-accessor-dotted.md`](fixme-0365-field-accessor-dotted.md) |
| Concrete versus template constructors and accessors, and re-synthesis | [`non-concrete-producer-obligations.md`](non-concrete-producer-obligations.md) |
| Bare constructor selection in value and pattern position | [`use-site-candidate-selection.md`](use-site-candidate-selection.md) §5, §7 |
| `TypeExpr → Type` resolution and type-argument arity | [`type-expr-resolver-convergence.md`](type-expr-resolver-convergence.md) |
| Internal constructors (`IO`'s `Bind`, `Pure`, `Effect`) | [`io-types.md`](io-types.md) §1 |

## 1. Registration

A source `deftype` enters through
`crates/cranelisp-typecheck/src/adt.rs::register_type_def`:

1. Allocate a fresh type variable per type parameter.
2. Pre-seed a type-only binding for the type name, so a recursive field such as
   `:(List a) tail` resolves. If a field fails to resolve, the placeholder is
   removed before the error returns.
3. Resolve each field's `TypeExpr` through the one resolver, which also checks
   type-argument arity.
4. Hand the resolved constructors to `register_type_def_with_ctor_infos`.

`register_type_def_with_ctor_infos` is also the synthetic-bootstrap entry: a
synthetic module has no imports, so its caller supplies fully qualified field types
already resolved. It stays thin:

- `cranelisp_types::build_adt_entries` derives the ordered `(key, entry)` set once.
  The binary's bootstrap calls the same builder, so bootstrap and typecheck
  registration cannot disagree (Principle 24).
- A non-callable entry installs as a binding. A callable recipe settles through one
  lifecycle funnel chosen by scheme concreteness: concrete with a synthesised body,
  or a slotless template for re-synthesis. An existing template is kept; an
  existing concrete or broken entry is retired before re-settlement.
- A sum constructor's bare spelling is exposed as a candidate onto its canonical
  key ([canonical key and bare candidate](dotted-ctor-registration.md#11-the-canonical-key-and-the-bare-candidate-sum-constructors)).
- A product then synthesises its field accessors (§4).

A type is a **product** when it has exactly one constructor and that constructor's
name equals the type's name. A single differently named constructor is a sum
variant.

## 2. Constructor Scheme Generation

Each constructor's scheme is quantified over the type's parameters:

| Constructor | Scheme |
|---|---|
| Nullary: `None` in `(deftype (Option a) None (Some [:a val]))` | `∀a. (Option a)` |
| Data: `Some` in the same type | `∀a. (Fn [a] (Option a))` |
| Monomorphic product: `(deftype Point [:Int x :Int y])` | `(Fn [Int Int] Point)` |

The scheme lives on the constructor's own callable binding, which is its single
source; no type entry holds a copy.

## 3. Product Type Handling — the dual facet

A product's type name and constructor name are one key, so one binding carries both
facets: the constructor callable, with the completed `TypeDefInfo` on
`CallableOrigin::Ctor { type_def: Some(..) }`. A sum registers a separate type
binding, and its constructors carry `type_def: None`. Registration retires the
provisional type-only binding before settling the product constructor, so the
facet is never registered twice.

- **One "entry as a type" reader.** `checker::type_def_view_of` answers for a type
  binding or a product constructor's facet. Every site that needs an entry as a
  type goes through it, including type-position resolution of `:Box` and
  `(Box Int)`. Do not pattern-match the type binding directly where a product
  must also answer.
- **Products do not auto-curry.** A product constructor's scheme is curry-shaped,
  so `(Point 1)` would otherwise become a closure; the constructor guard in
  `try_auto_curry` reports an arity error instead (spec §5.2.7;
  `auto-curry.md` §1.1).
- **No product special case downstream.** Constructor-to-type lookups and pattern
  resolution read the constructor origin's `type_name` for products and sums
  alike.

Considered: renaming a product's constructor (a `Mk` prefix). Rejected because
`(Point 1 2)` must construct a `Point` (spec §5.2).

## 4. Field accessors

Only product fields get accessors; a sum payload label is positional metadata
extracted by `match` (`fixme-0365-field-accessor-dotted.md` §1.6.7). A concrete
product's accessors settle concrete. A generic product's settle as templates with a
synthesis recipe, and each instance is re-synthesised at concrete type arguments
rather than produced by re-checking a body
(`non-concrete-producer-obligations.md` §2.3).

## 5. Constructor-pattern inference

`infer.rs::check_constructor_pattern`:

1. Rejects an internal constructor.
2. Resolves a dotted, bare or module-qualified name to one constructor through
   `resolve_constructor_entry`. A module-qualified name resolves by the qualified
   walk value position uses (`typecheck.md` §3.5). A bare name with several
   candidates is selected by the scrutinee type, or held as a pending pattern use
   until inference settles it
   (`dotted-ctor-registration.md` §3.3; `use-site-candidate-selection.md` §7).
3. Instantiates the constructor afresh for the arm (`instantiate_ctor`) and records
   the resolved storage identity for the pattern span in
   `MethodResolutions.pattern_ctors`.
4. Unifies with the scrutinee: a nullary constructor takes no bindings and its type
   unifies with the scrutinee; a data constructor needs one binding per field, its
   result type unifies with the scrutinee, and each binding takes its field type.

A fresh instantiation per arm lets `(Some x)` in one arm and `None` in another
constrain the scrutinee without sharing constructor variables:

```clojure
(match opt
  [(Some x) x]      ;; Some: (Fn [t1] (Option t1)); (Option t1) unifies with the scrutinee
  [None default])   ;; None: (Option t2); unifies with the scrutinee
```

Pattern-position selection does not yet follow the approved candidate lifecycle
in every branch; that obligation is recorded among the
[constructor design's unresolved obligations](dotted-ctor-registration.md#8-unresolved-obligations).

## 6. Exhaustiveness

After the arm bodies have constrained the scrutinee and pending constructor uses
have settled, `infer_match` checks a match whose scrutinee is a concrete ADT:

- the covered constructors are the settled `pattern_ctors` identities belonging to
  the scrutinee's type, never the as-written names;
- a wildcard or variable pattern covers everything;
- internal constructors are excluded, so user code need not cover them;
- `crates/cranelisp-typecheck/src/adt.rs::check_exhaustiveness_in_module` compares
  by constructor name within the
  type's home module and reports the missing constructors sorted, for
  deterministic diagnostics.

A non-exhaustive match on an ADT is a located type error, not a warning
(spec §6.5.1). Coverage is by constructor name only: the language has no nested,
literal, or- or guarded patterns (spec §6.6), so no pattern-structure analysis is
needed.
