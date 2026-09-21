# Non-concrete producer obligations — typecheck's half of the release contract

**Status:** current design, verified against source on 2026-09-21. The work it specified
has landed; filings 0924, 0913 and 0935 are retired.
**Owner:** `design`, narrow-deployed to `cranelisp-typecheck`.
**Subordinate to:** [`typecheck.md`](typecheck.md) §9.3 / §9.4; extends
[monomorphisation](monomorphisation.md) §1–§3 and [`adt.md`](adt.md) §"Product Type
Handling".
**Governed by:**
- the unified symbol-table lifecycle, `design/arch/symbol-table-lifecycle.md` §§3–7 — the
  representation, its enforcement and its residual limits;
- [the non-concrete release contract](../backend/non-concrete-release-contract.md), rules
  R-2 and R-3 and §5.2 / §5.4.

Where this document and either disagrees, they govern.

**R-2, no fabricated concreteness:** no producer in this crate hands a downstream gate a
type, category or lifecycle state more concrete than the value actually is. This is
Principle 25 applied to the type channel. Callables meet it by representation (§2).
Values meet it by a narrowly licensed defaulting step that carries its own check (§3).

- §1 The producer populations
- §2 Callables: the funnel, one identity, and accessor instances
- §3 Values: residual-parameter defaulting
- §4 The product/sum accessor boundary
- §5 Observations
- §6 Evidence and residuals

---

## 1. The producer populations

Five producers once handed downstream something more concrete than they had. Each now
has a single route:

| Population | Former fabrication | Current route |
|---|---|---|
| ADT constructors | a slot for a generic ADT's constructor | concrete ADT ⇒ `Life::Concrete`; generic ADT ⇒ `Life::Template { body: Synth(..) }` (`crates/cranelisp-typecheck/src/adt.rs`) |
| Product field accessors | a concrete, slotted state over `∀a. (Fn [(Bx a)] a)` | the same split, and a template instance minted by re-synthesis (§2.3) |
| Trait-implementation methods | a `mono` scheme over a type still carrying variables, then a slot | the method scheme is generalised, then settled as a `Parametric` or `Constrained` template when non-concrete (`crates/cranelisp-typecheck/src/traits/impl_check.rs`) |
| Monomorphised instances | a slot minted without a concreteness gate | the demand's concrete signature installed through the funnel ([monomorphisation](monomorphisation.md) §3) |
| Codegen views of concrete bodies | a node whose real type was not concrete presented as `Int` | eligible residual parameters defaulted on a clone, then a strict retry (§3) |

The first four are one defect at the frame level. The last is the same defect at the
value level.

---

## 2. Callables: the funnel, one identity, and accessor instances

### 2.1 P-1 — the gate is the funnel

> **P-1.** `Life::Concrete { slot, … }` is constructed only by the lifecycle's
> `settle_concrete`. It checks `Type::is_concrete()`, accepts the realisation, and mints or
> rebinds the slot in one act. A non-concrete callable is `Life::Template`, which has no
> field for a slot or a view. This crate's obligation is consumption: every population
> settles through the funnel, and none mints a slot or a concrete state itself.

- This is [monomorphisation](monomorphisation.md) §1, enforced at the table boundary
  rather than by caller convention.
- It exists because a convention decays. The invariant was once graded "unconstructable"
  on the strength of one inspected function, while two other sites quietly violated it
  (root `CLAUDE.md` §Assurance, row R11). A later census then found two more.
- [Lifecycle enforcement](../arch/symbol-table-lifecycle.md#6-enforcement) prevents
  ordinary consumers from bypassing settlement.
  [Residual responsibilities](../arch/symbol-table-lifecycle.md#7-residual-responsibilities)
  keep the clone/serde and copied-claim limits, and their load and publication
  validation. That qualified boundary is the end state.

### 2.2 P-2 — one instance identity

> **P-2.** A monomorphised accessor or trait-method instance is named by the one
> context-bearing `InstanceLink::instance_key(&template_scheme)` contract
> ([identity packet](../arch/s122-overload-reorder-publication.md)). The name is derived
> once, at registration, from the authored owner and the complete concrete function
> signature. It is never re-composed at a probe site.

`mangle_trait_method` survives unchanged as the **template** name, the key that trait
discovery and dispatch use. Only the call is redirected: the site's
`ApplyRef::Dispatch` is rewritten to the instance.

| Role | Symbol | `Life` |
|---|---|---|
| implementation-method template | `Functor.fmap$primitives/Option` | `Template { body: Ast(..), kind: Parametric }` |
| concrete instance, minted on demand | authored owner + full concrete signature | `Concrete { slot, realization: Body { view }, … }` |

**Considered: widening `mangle_trait_method` with the receiver's type arguments**
(`…$primitives/Option$Int`). Rejected for three reasons:

1. It is lossy on the axis that matters. `Functor.fmap` instantiates `(a, b)`, and `b`
   comes from the function argument's result, so `(fmap show (Some 1))` and
   `(fmap inc (Some 1))` would collide.
2. The shared key already carries the whole signature, and residual types fail key
   derivation rather than producing a partial spelling.
3. A second grammar for "a concrete instance of a generic body" would be a second
   identity home (Principle 7).

### 2.3 A-MINT — accessor instances are re-synthesised

> **A-MINT.** A monomorphised field accessor is produced by re-running the accessor
> synthesis at the concrete type arguments. Its template stores the synthesis recipe
> (`TemplateBody::Synth`), and `monomorphise_synth` derives the instance. It is keyed by
> the canonical identity, never rechecks a body, and never consults a span-keyed sidecar.

Rechecking would be wrong here, as it is right for an authored implementation method.
An accessor body:

- is entirely `Span::SYNTHETIC`, so span-keyed carriers cannot be transported for it;
- has its constructor identity supplied at synthesis, so rechecking would re-derive a
  settled fact (Principle 24);
- is derived from the field list, so re-checking a derivation to recover its inputs is a
  second derivation (Principles 7 and 26).

The accessor's canonical `Type.field` symbol and its bare candidate still exist; they are
a template rather than a compiled body. So the bare-alias import edge, the `Ambiguous`
poison, the cross-cluster accessor-kind classification and the §8.6.5 contest rules are
unaffected. They read the entry, not its lifecycle state.

### 2.4 Implementation methods follow the ordinary path

- An implementation method's scheme quantifies the variables it actually has. A method
  that is non-concrete therefore settles as a template, and ordinary monomorphisation
  reaches it.
- The body is rechecked in the implementing module's scope, with the three
  cross-module facts of [monomorphisation](monomorphisation.md) §3.7.
- **Collection.** A trait-dispatched `Apply` whose dispatch target is a template, with
  concrete argument types, is one more trigger in `collect_mono_call_sites`. It feeds the
  same worklist and core; it is a successor-discovery widening, not a second entry point.

### 2.5 Demands carry the storage identity

- Every collector builds its demand through one constructor,
  `program/mono_collect.rs::mono_demand_from_spans`. The template field is the
  carrier-read canonical storage identity (`resolved.canonical`), not a composed or
  written spelling.
- So a bare-alias import of a generic function, or of an accessor, reaches the terminal
  entry by construction, and a written spelling cannot be demanded.
- A demand that finds no instance fails loudly downstream, because the template has no
  slot to fall through to.

### 2.6 What must not change

1. No new `cranelisp-types` item and no second lifecycle vocabulary. A need the lifecycle
   lacks is a filing to `arch`.
2. No second key grammar, and in particular no widened `mangle_trait_method`.
3. No accessor body recheck. A body that really was checked is never routed through the
   synthetic view builder, whose synthetic-span assertion exists to catch that.
4. A concrete product's constructor and accessor, and a concrete implementation method,
   keep their slot, body and view. A golden CLIF difference outside generic frames is a
   finding.
5. The §8.6.5 bare-alias contest and the implementation-time collision pre-flight read the
   canonical entry and are untouched.

---

## 3. Values: residual-parameter defaulting

### 3.1 The requirement

- A concrete frame's codegen view must never replace a node's type. `(Result a String)`
  must not become `Int`. That discards the constructor and its concrete arguments, and
  the backend then derives no drop glue and leaks the value.
- It may become `(Result Int String)`: the constructor survives, `String` survives, and
  only a position that nothing inhabits is filled.

### 3.2 The licence and its fences

> **L-1 (the licence).** A residual variable at a node of frame `F` may be defaulted only
> if it occurs in none of `F`'s declared parameter types. Then nothing outside `F` can
> supply a value inhabiting it. Every nullary frame qualifies, including `__expr` (every
> REPL turn) and `main`.

- A container at an un-unified element type is necessarily empty, because inserting an
  element would have unified it. So defaulting an interior `(Vec a)` binding frees its
  buffer correctly, with no element discharge.
- **The counter-shape L-1 excludes:** the body of a multi-signature `$Var` template
  carries residual parameters that a caller instantiates. A value of that type exists, and
  it is the argument. Defaulting there would under-discharge a heap payload.

> **L-2 (the shape).** Defaulting applies only below a type-constructor root (`ADT` or
> `Fn`). It replaces residual argument positions below the root, recursively, and
> preserves the constructor and every concrete argument. A residual root
> (`Type::Var`, `Type::TyConApp`) is never defaulted: with no constructor there is no
> category and no glue (R-1).

> **L-3 (the check).** Defaulting a variable that appears in the scheme's constraints is a
> located error. Choosing a type for `Eq a` would choose a trait instance, which is
> fabrication of another kind.

The default is `Int`, a declared never-heap type, reached only inside
`default_residual_parameters`. There is no inline `unwrap_or` default anywhere.

### 3.3 The mechanism and its self-check

`crates/cranelisp-typecheck/src/program/support.rs::build_concrete_codegen_view` is the
seam.

- The settled scheme's concrete result type is authoritative for the body root. A
  forward-reference result node can keep a pre-drain variable after its frame's return
  has settled, and that must not be mistaken for a residual root.
- A strict `from_expr` success is the view.
- **`NotConcrete`:** `default_residual_parameters` rewrites a clone under L-1 to L-3, then
  strict construction is retried. A second `NotConcrete` is a located ambiguity error
  naming the frame.
- **`Unresolved`:** a real-span reference with no typed verdict always propagates as a
  located error. It is never swallowed into defaulting.
- **Self-check.** Defaulting succeeds only if the strict builder then accepts the body, so
  a defaulting that left a residual cannot pass silently (Principle 25).
- The stored AST keeps its real types. The REPL's residual-parameter displays
  (`repl/spec/01-display-format.md` §1.5.1, `repl/spec/04-self-documentation.md` §4.1)
  are unaffected.
- The backend and Binary/int derive release glue from the view's type without change.
  `(Result Int String)` gets canonical glue, and the `Err` arm's `String` is discharged.

### 3.4 Residual roots

A frame whose body still has a residual root after defaulting has two admissible
dispositions and no third:

1. **It is not a codegen target.** It stays `Life::Template`, and any reachable use
   demands a concrete instance.
2. **It is a codegen-reaching value nothing pins.** That is spec §3.11.1's located
   ambiguity error, raised by the scan in [monomorphisation](monomorphisation.md) §4, or
   here.

A bare polymorphic value displayed at the REPL (§3.11.4) is not compiled and never
reaches this seam.

---

## 4. The product/sum accessor boundary

- A product has one constructor, named like its type. A differently named constructor is
  a sum variant even when it is the only arm.
- A product mints a total canonical `Type.field` accessor and a bare candidate. A
  monomorphic product settles them `Concrete`, and a polymorphic product settles them
  `Template`.
- Sum payload labels are positional metadata. They mint no dotted or bare accessor, and a
  positional `match` extracts the payload. A-MINT therefore applies to polymorphic
  products only.
- Declarations are explicit (spec §5.2.4). A bare head is monomorphic, a parenthesised
  head is the complete parameter list, and every field has a written type. The frontend
  rejects missing field types and undeclared type variables before typecheck sees them
  (`design/frontend/s116-syntax-and-annotation.md` §3.1). Typecheck adds no compensating
  shape check.
- What typecheck owns: a written field type naming a concrete type that does not resolve
  is its own located resolution error. It also owns making a valid generic declaration such as `(deftype (B a) (Mk [:a v]))`
  construct, match and, for a product, access at every concrete instantiation.

---

## 5. Observations

- **The backend owns the release criterion.** Its category-licence instrument, partitioned
  by callable origin, is the release contract's measure (§5.1 there).
- **Typecheck keeps one keyed observation.** It is for the ownership pass's conservative
  seed: `ownership/fixpoint.rs::residual_param_frames`
  ([ownership inference](ownership-inference.md) §10.3). It explains which frames took the
  conservative path and is not a zero-count gate.
- **The codegen-view refusal carries no counter.** It is already a located compile error.
  An aggregate counter on the same branch recorded no frame or reason, and had no reset or
  reader. It could neither prove the arm empty nor change its safe disposition, so it was
  retired.
- **The fabrication census.** Other `ConcreteType::from_type` discard-and-substitute arms
  belong to their owning contexts. The residual grade on register row R18 is `arch`'s
  (`design/arch/safety-invariants.md`).

---

## 6. Evidence and residuals

**Evidence:**

- `adt::tests::polymorphic_constructors_are_slotless_templates` — the template boundary;
- the carrier units in `crates/cranelisp-typecheck/src/program/mono_collect/tests/carriers.rs`
  — bare-accessor and renamed-import demands carry the canonical storage identity;
- `tests/residual_type_param_result_leak_0913.rs::unannotated_result_turn_releases_like_its_annotated_twin`
  — an exact marginal balance between an unannotated `Result` turn and its annotated twin;
- `ownership::fixpoint::tests::a_residual_parameter_frame_publishes_nothing_and_stays_in_the_keyed_set`
  — the ownership observation.

**Residuals:**

| Item | Owner and trigger |
|---|---|
| `MonoExpr::lenient_from_expr` has no production caller. Typecheck no longer calls it, and its remaining callers are backend test support (`crates/cranelisp-backend/src/test_support.rs`) | `arch` (a `cranelisp-types` public item). Deletion needs its own complete consumer case; this refusal path neither licenses nor blocks it |
| Distinct-instantiation code size | A performance characteristic, not a correctness gate. The expected multiplier for accessors is near one |

## Former section numbers

- §0, §1 (site verification) → §1
- §2.1–§2.3 → unchanged
- §2.4, §2.5, §2.7 → §2.4, §2.5, §2.6
- §2.6 (census cost) → §6 residuals
- §3.1–§3.5 → §3.1–§3.4
- §3.6 (`lenient_from_expr`) → §6 residuals
- §4, §4.4 → §4
- §5 → §5
- §6, §6.1 (public API and schema) → no public item or schema change remains owed; the lifecycle's schema window was `CACHE_SCHEMA_VERSION` 24→25
- §7 (change-sets), §8 (as-built disposition) → §1, §6
- §9, §10 → §2.1, the header

The S119 census figures, line-level verification and change-set plan are in Git history.
