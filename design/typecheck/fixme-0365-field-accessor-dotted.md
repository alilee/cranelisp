# Field accessors — canonical `Type.field` and the bare spelling

Owner: `design` narrow-deployed to `cranelisp-typecheck`. Subordinate to
[`typecheck.md`](typecheck.md) §9.4. Reader: anyone changing how product-field
accessors are synthesised, typed, resolved or listed.

Required behaviour is in `spec/05-definitions.md` §5.2.6,
`spec/08-modules.md` §8.5.2 and §8.6.4–§8.6.5, and `spec/07-traits.md` §7.3.1.
Neighbouring authorities this design uses without restating:

| Subject | Authority |
|---|---|
| `SymbolEntry`, `Binding`, `NameCandidate` and the per-spelling entry | `design/arch/symbol-table-lifecycle.md` §3, §5.8, §5.9 |
| Selecting one declaration from a bare spelling's candidates | [`use-site-candidate-selection.md`](use-site-candidate-selection.md) |
| Concrete versus template accessors and their re-synthesis | [`non-concrete-producer-obligations.md`](non-concrete-producer-obligations.md) §2.3 |
| Product/sum shape and constructor registration | [`adt.md`](adt.md); dotted constructors in [`dotted-ctor-registration.md`](dotted-ctor-registration.md) |

Section numbers are cited from source, tests and sibling designs; retired
numbers are not reused, so gaps are deliberate. The file name predates the
subject name and is kept because it is cited.

## 0. Model

- Each product field has exactly one accessor declaration: the canonical
  binding keyed `Type.field` (`Box.v`) in the type's home module, typed
  `(Fn [Type] FieldType)` and always Public.
- The bare field spelling (`v`) is a candidate reference to that binding, not
  a second function. It carries the `deftype`'s visibility.
- Shared bare spellings are candidate sets resolved at each use. No sentinel
  is installed, no declaration is refused, and the canonical form is always
  valid.
- Typing reads the canonical binding's scheme, so the dotted and bare
  spellings type identically.
- Only product fields mint accessors (§1.6.7).

## 1. Typing

### 1.1 Resolution routes

- **Dotted `Type.field`.** The checker's dotted-member resolution
  (`checker.rs::resolve_dotted_member`) resolves the head through ordinary
  scope resolution, then probes `Type.field` in the type's home module through
  the staging-then-live union view. It accepts the entry only when
  `adt::committed_member_owner` names that exact type. A non-member such as
  `Box.nonfield` does not resolve as an accessor.
- **Bare `field`.** Ordinary module-scope resolution yields the spelling's
  candidates. Use-site candidate selection settles which declaration a use
  denotes. Typecheck then types the selected canonical binding.

### 1.2 Typing rule

```
canonical `Type.field` has scheme Σ = ∀ᾱ. (Fn [Type] FieldType)
────────────────────────────────────────────────────────────────
Γ ⊢ Type.field : instantiate(Σ)
```

A bare use that selects `Type.field` has the same type. The scheme is
quantified over the type's parameters, so `(deftype (Box a) [:a v])` gives
`(Fn [(Box a)] a)`. Typing is ordinary value-position scheme instantiation.
`FieldType` is read from the scheme's `Fn` result, not from a separate field
table, so the canonical binding's scheme is the single source of an accessor's
type. First-class use is automatic because the accessor is an ordinary
callable. No accessor-specific typing mechanism exists.

## 1.6 Storage and resolution

### 1.6.1 Synthesis

`crates/cranelisp-typecheck/src/adt.rs::synthesise_one_accessor` mints, per product field:

- **The canonical binding** under `Type.field`, with:
  - scheme `(Fn [ADT] FieldType)`;
  - body `(fn [self$accessor] (match self$accessor [(Ctor f…) field]))`;
  - `CallableOrigin::Accessor`; and
  - `Visibility::Public`.

  A concrete type installs a concrete callable carrying its codegen view. A
  generic type installs a template carrying its synthesis recipe. An existing
  template is kept. An unpublished synthesized entry for the same key is
  replaced in place, so re-establishing a structurally identical type does
  not duplicate the entry.
- **The bare candidate** through `expose_candidate(field, <module>/Type.field,
  visibility)`. It adds no slot and no second compiled function.

`adt::committed_accessor_kind` recognises an accessor from the durable entry:
it checks `CallableOrigin::Accessor` together with a one-argument
`(Fn [ADT] _)` scheme. Same-cluster and cross-cluster readers therefore use
one recogniser.

Minting the canonical binding unconditionally is the load-bearing choice. It
is always present and always Public, whatever else shares the bare spelling.
No path reconstructs, re-mints or re-scopes it when the spelling becomes
contested. The former design made bare `v` the real function and `Box.v` a
secondary alias whose existence and visibility changed with contest. Do not
re-propose that shape: it left a contested field without a stable handle and
needed per-case visibility rules.

### 1.6.2 Shared bare spellings

Suppose two types in scope own field `v`, or `v` is also a user `defn`, an
import or a trait method. The spelling `v` then has several candidates, and
each keeps its own canonical identity:

- use-site selection settles a use when ordinary context leaves one candidate;
- a use that still has several candidates must be written in canonical form;
- nothing is chosen by declaration or import order.

Synthesis records the field's owning types in `CheckState.accessor_owning_types`.
`reconstruct_accessor_alternatives` re-derives them from the durable table for
a later REPL cluster. Ambiguity diagnostics list the surviving canonical
identities (`use-site-candidate-selection.md` §9).

### 1.6.3 Modes and modules

- The dotted form resolves identically in value and call position, across
  `--run`, `--link` and the REPL. The REPL finds an earlier cluster's
  accessor because the probe reads the union view.
- The dotted form works across modules: `m/Box.v` is Public, so the §8.7.3
  visibility filter in `cranelisp-types::resolve` admits it whether or not
  bare `v` is contested in `m`.
- A bare `m/v` resolves across modules when its candidates select one
  declaration.

### 1.6.5 Listing and export

`public_symbols()` enumerates bindings, not candidate references. Listing and
glob-export consumers therefore see exactly one accessor per field, the
canonical `Type.field`. The bare spelling is exposed to importers as a
candidate with the `deftype`'s visibility. It is never a second listed symbol.
How `/list` and `/exports` render entries is `repl/spec.md`'s.

### 1.6.7 Accessor source — product fields only

Only the fields of the lone same-name constructor that defines a product
generate accessors. A differently named constructor arm is a sum variant even
when it is the only arm. Its payload labels are positional declaration
metadata: they mint neither `Type.field` nor a bare candidate, and payloads are
extracted by exhaustive `match`. This keeps every accessor total and avoids an
implicit runtime variant check. The user ruled this on 2026-09-02, superseding
the FIXME 0867 proposal for partial accessors over every arm. The `is_product`
restriction in `adt.rs` is therefore the required boundary, not an enumeration
defect.

## 2. Trait methods sharing a field spelling

Spec §7.3.1 permits an `impl` method whose name equals a field-accessor name of
its target type. The two declarations remain distinct:

- `Box.v` is the accessor;
- `HasV.v` is the trait method, realised for `Box`; and
- both project the bare spelling `v`, which resolves under §1.6.2.

Impl coherence continues to govern competing implementations of the same
method. Accessor names add no impl-registration check.

### 2.1 Unresolved obligation — the source still rejects the overlap

`traits/impl_check.rs::check_impl_method_accessor_collisions` still rejects such
an `impl` before registration. The following tests assert that superseded
behaviour:

- the four `impl_method_colliding_*` cases in `adt/tests.rs`;
- `tests/spec_05_definitions.rs::impl_method_colliding_with_field_accessor_rejected_neg`.

This is a spec violation awaiting defect intake by `qa` under
[`ACT-0983`](../../sprints/actions/ACT-0983-accessor-impl-collision-intake.md).
Once intake is complete:

- `dev` deletes the gate and the helper in §2.3; and
- `test` replaces the rejection tests with evidence for the permitted overlap
  and its ambiguous-use diagnostic.

### 2.3 Accessor enumeration

`crates/cranelisp-typecheck/src/adt.rs::field_accessor_names_of` walks the owning module's union view and
keeps the entries that `committed_accessor_kind` classifies as accessors of the
target type. It returns each canonical key's terminal field segment
(`Box.v` → `v`). Its only consumer is the gate in §2.1. Delete it with the gate
rather than retain a helper with no consumer.

## 3. Public surface

Accessors add no public typecheck item, `cranelisp-types` type or
`public-api.txt` line. Synthesis uses the types-owned builder and candidate
operations already on that crate's approved surface.

## 4. Evidence

- **Unit (in-crate).** The accessor and dotted-member cases in
  `crates/cranelisp-typecheck/src/adt/tests.rs` cover:
  - canonical binding and bare-candidate shape;
  - monomorphic, polymorphic and first-class typing;
  - contested and unique bare use;
  - rejection of a non-member dotted reference.
- **End-to-end.** `tests/spec_field_accessor.rs` and the §5.2.6/§8.5.2 cases in
  `tests/spec_05_definitions.rs`. Coverage status is the spec-side
  annotation band, which `qa` maintains.

## Former section numbers

| Former | Now |
|---|---|
| Inversion box; §0 "unifying insight" | §0 and §1.6.1 |
| §1.1–§1.3 | §1.1–§1.2 |
| §1.4, §1.6.6, §2.7 (test plans) | §4 and §2.1 |
| §1.5–§1.5.3 (visibility-by-arm ruling) | Retired, never implemented as final; §1.6.1 records why |
| §1.6.4 (rework edits) | Delivered; §1.6.1 states the result |
| §2.1–§2.2, §2.4–§2.6 (impl-time rejection) | §2 and §2.1 — superseded by spec §7.3.1 |
| §3 zero-baseline disposition; §4 quality attributes | §3 and the rationale in §1.6.1 |
| §5 cross-references | The authority table at the top |
