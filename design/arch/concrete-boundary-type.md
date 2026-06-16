# Concrete-only codegen-boundary type + generic-body-codegen elimination

**Status: TARGET ARCHITECTURE (user-ratified direction 2026-06-16) — a dedicated arc run within S84.** Phase 1 (`ConcreteType` + the fallible conversion) LANDED in `crates/cranelisp-types/src/concrete.rs` (commit `5b3319c`). **Phase 2a LANDED (S84, /arch):** the §2.4 decision is settled (`MonoExpr` — parallel codegen AST) and the `MonoExpr`/`MonoDefnVariant` representation + `MonoExpr::from_expr` builder + unit tests landed in `crates/cranelisp-types/src/mono_expr.rs` (produces-but-unused; cache bumped 6 → 7). **Phase 2b LANDED (S84, /dev(typecheck)):** the mono-population seam built `MonoExpr` at `traits.rs:~1479` with an interim `allowed_vars` carve-out admitting scheme-quantified body vars. **Phase 4 DETAILED + RE-SEQUENCED before Phase 3 (S84, /arch, 2026-06-16):** §4 now splits Phase 4 into (A) mono-completeness (root-caused: a spurious partial instance is minted from the generic-caller recursion — `traits.rs::monomorphise_inner_parametric_hops` over-eagerly mints on the bare-var-result trigger with non-concrete args; the fix SUPPRESSES that mint, not "completes" it), (B) generic-body-codegen elimination (two filter sites — `defined_symbols()` + `derive_codegen_batch::try_push` — exclude `Polymorphic`), (C) the 0344 reconciliation. New sequence: Phase 1 → 2 → 4 → 3 → 5. Phases 3+5 follow. This document is the standing reference for that arc.

Owner: `/arch`. Cited by `bounded-contexts.md` §2 (typecheck) + §3 (backend, invariant 9) + §7 (types) and Principle 18/20. Supersedes the *enforcement framing* of FIXME 0379's two-predicate belt-and-braces (which stays as the interim guard until this arc lands); subsumes the resolution proposal of FIXME 0381.

---

## 0. The ruling and what it demands

> **User, 2026-06-16:** "The main goal is to remove passing generics to the backend — they shouldn't even be REPRESENTABLE [there]."

The architectural reading: **there must be a concrete-only type at the typecheck→backend boundary — a type with NO `Var` variant — such that a generic / `Type::Var` is *structurally unrepresentable* at codegen.** This is Principle 18 (enforce invariants structurally) applied to the boundary *type itself*, and the fullest expression of Principle 20 (model a correlated invariant by representation): the S84 slot-gate work made the *callability* invariant structural (a non-concrete def has no slot); this arc makes the *value-representation* invariant structural (a value reaching codegen has no representation-undetermined type, **by the type system of the compiler**, not by a downstream check).

### What is wrong today (the root the ruling pinpoints)

The typed AST carries `inferred_type: Option<Box<Type>>` on **every** `Expr` node (`crates/cranelisp-types/src/ast.rs`, ~16 sites), and `Type` *has* a `Var` variant. The backend's `compile_to_module` consumes that AST and `HeapCategory::classify(&Type, …)` (`heap.rs:438`) reads those `inferred_type`s at RC sites. So a `Type::Var` is **representable at every codegen-reaching position by construction of the boundary type** — and the entire S83/S84 defence is a *pile of downstream checks* trying to prove that the representable-but-illegal state never actually occurs:

- `Type::contains_var()` — a `debug_assert!`-only tripwire (`types.rs:55`).
- The §3.11.1 position-complete ambiguity check (typecheck side, FIXME 0379) — rejects genuinely-free vars.
- `classify == Mixed && is_representation_undetermined()` (backend backstop, FIXME 0375/0379) — panics on residuals.
- The slot gate `is_concrete()` (S84 Wave 1) — keeps a non-concrete def from getting a callable slot.

Four guards, all enforcing "no `Type::Var` reaches codegen" *behaviourally*, because the type that crosses the boundary *permits* a `Type::Var`. Principle 18 says: when the type system can foreclose the violation by construction, prefer that. **The boundary type can foreclose it.** A no-`Var` type makes all four guards either unnecessary or relocated to a single fallible-conversion choke point.

### The critical finding that forced the re-direction (FIXME 0381)

Arming the FIXME-0379 backstop fired **317×** on the valid prelude/stdlib, because the compiler today does **uniform-word generic-body compilation** — the §12.1 "every value is one machine word" model. The prelude's generic functions (`collections.list`'s `(List a)` body, `option/Some`'s arg field) are compiled **once, as templates carrying free `Type::Var`s**, relying on the conservative `<1024` RC guard to survive. This is **NOT** per-instance monomorphisation for unconstrained generics — it is a second, latent compilation model that the slot-gate work did not touch (the slot gate makes the template *slot-less*, but the template's *body is still emitted*).

So the ruling has **two** structural consequences, and the boundary type alone is insufficient without the second:

1. **A concrete-only boundary type** (§1) — `Var` is unrepresentable at the seam.
2. **Generic-body-codegen elimination** (§2) — a generic body *has no concrete-boundary-type annotation*, so it *cannot be handed to codegen at all*; only its monomorphised concrete instances are emitted. This is what stops the 317× — the prelude generics stop being pre-compiled as templates and become on-demand mono roots per use.

The two are the same move from two angles: (1) makes the *type* unrepresentable; (2) makes the *generic body* unannotatable-and-therefore-unemittable. A generic body cannot be annotated with the concrete-only type ⟹ it cannot reach the backend.

---

## 1. The boundary type — `ConcreteType`

### 1.1 Name and location

**`ConcreteType`**, in `crates/cranelisp-types/src/concrete.rs` (new module), `pub` from the crate root. Chosen over `MonoType` (overloads "monomorphisation", a typecheck *process*) and `CodegenType` (names a *consumer*, not the *property*). `ConcreteType` names the **property** — fully concrete, no representation-undetermined component — which is exactly the invariant it structurally guarantees.

### 1.2 Shape — the concrete subset, NO `Var`, NO `TyConApp`

```rust
/// A fully-concrete type at the typecheck→backend boundary.
///
/// **STRUCTURAL GUARANTEE: this enum has no `Var` and no `TyConApp` variant.**
/// A representation-undetermined type (a generic / `Type::Var` / unpinned HKT
/// head) is *unrepresentable* as a `ConcreteType` by construction (Principle 18).
/// Therefore the backend, which consumes only `ConcreteType`, can never be handed
/// a value whose machine shape is undecidable — `HeapCategory::classify` is total
/// over `ConcreteType` (no `Var` arm, no panic case).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ConcreteType {
    Int,
    Bool,
    String,
    Float,
    /// Function type: concrete params -> concrete return.
    Fn(Vec<ConcreteType>, Box<ConcreteType>),
    /// ADT: FQ type name + **fully-concrete** type arguments.
    ADT(FQTypeName, Vec<ConcreteType>),
}
```

Note the recursion is on `ConcreteType`: an `ADT`'s args and an `Fn`'s params/return are themselves `ConcreteType`, so concreteness is total and structural at every depth. There is no way to build a `ConcreteType::ADT(Option, [<something with a Var>])` — the `<something>` would itself have to be a `ConcreteType`, which has no `Var`.

`Eq + Hash` are added (not on `Type`, which carries `Var(TypeId)` that hashes unstably across inference runs) — concrete types are stable keys, useful for the mono `done`-set and the codegen cache key.

### 1.3 The fallible conversion — `Type → ConcreteType` (the single choke point)

```rust
impl ConcreteType {
    /// The ONLY way to obtain a `ConcreteType` from a `Type`. Succeeds iff the
    /// `Type` is fully concrete; the failure IS the "could-not-monomorphise" /
    /// §3.11.1-ambiguity error (Principle 18 — the illegal state is caught at the
    /// one boundary it cannot pass, not by N downstream guards).
    pub fn from_type(ty: &Type) -> Result<ConcreteType, NotConcrete> {
        match ty {
            Type::Int => Ok(ConcreteType::Int),
            Type::Bool => Ok(ConcreteType::Bool),
            Type::String => Ok(ConcreteType::String),
            Type::Float => Ok(ConcreteType::Float),
            Type::Fn(ps, r) => Ok(ConcreteType::Fn(
                ps.iter().map(ConcreteType::from_type).collect::<Result<_, _>>()?,
                Box::new(ConcreteType::from_type(r)?),
            )),
            Type::ADT(n, args) => Ok(ConcreteType::ADT(
                n.clone(),
                args.iter().map(ConcreteType::from_type).collect::<Result<_, _>>()?,
            )),
            Type::Var(id)        => Err(NotConcrete::Var(*id)),
            Type::TyConApp(id, _) => Err(NotConcrete::HktHead(*id)),
        }
    }

    /// Inverse — a `ConcreteType` is always a valid `Type` (the embedding is total).
    pub fn to_type(&self) -> Type { /* trivial structural map back */ }
}

#[derive(Debug, Clone)]
pub enum NotConcrete {
    Var(TypeId),       // a residual unification variable — ambiguity (0373 ii)
    HktHead(TypeId),   // an unresolved higher-kinded head
}
```

**The conversion's failure is the unified expression of three errors that are currently three separate guards:** (a) the §3.11.1 "ambiguous type" error, (b) the "monomorphisation could not produce a concrete type here" error, (c) the `classify(Type::Var)` panic. They are the same fact — *this position's type is not concrete* — surfaced at the one boundary where it is structurally caught. The user's reframing ("the §3.11.1 ambiguity error is 'monomorphisation could not produce a concrete (boundary) type here'") is exactly `from_type` returning `Err(NotConcrete::Var)`.

### 1.4 `is_concrete()` and `is_representation_undetermined()` after this lands

- `Type::is_concrete()` becomes definitionally `ConcreteType::from_type(self).is_ok()` — it survives as the GOT-slot-eligibility predicate at the *typecheck* slot gate (which still operates on `Type`, pre-conversion). It does not go away; it is re-expressed in terms of the conversion's success.
- `Type::is_representation_undetermined()` and the whole FIXME-0379 backend backstop become **unnecessary at the boundary**: `classify` takes `ConcreteType`, which cannot be representation-undetermined. The predicate may be retired once Phase 3 lands (the typecheck-side position-complete check is *subsumed* by the conversion — see §3). It is KEPT until then as the interim guard (it is the current load-bearing fix).
- `Type::contains_var()`'s `debug_assert!` callers are subsumed — the type no longer admits a `Var` to assert against.

---

## 2. Generic-body-codegen elimination

### 2.1 The current (wrong) model

Today a generic/unconstrained def's body is compiled **once** as a uniform-word template carrying free `Type::Var`s. The slot gate (S84) made the def slot-less (`UserFnState::Polymorphic`), but `defined_symbols()` **still includes `Polymorphic` as a codegen target** (BC §7: "`defined_symbols()` treats it as a mono target … because the `Polymorphic` template's body IS what monomorphisation specialises"). The intent was that the template body gets *specialised* per instance — but in practice the **template itself is also emitted** (FIXME 0381: the 317× fire), because nothing prevents `compile_to_module` from being called on the slot-less `Polymorphic` entry's body, and that body's value positions carry the scheme-quantified free vars.

### 2.2 The target model — only concrete instances have a boundary-type annotation

Under `ConcreteType`, the AST handed to codegen is annotated with `ConcreteType` (or carries a `ConcreteType` codegen view — §2.4). **A generic body cannot be so annotated** — its value positions are `Type::Var`, and `ConcreteType::from_type` fails on them. Therefore:

- **A slot-less `Polymorphic` def is NEVER emitted to codegen.** It has no `ConcreteType`-annotated body to hand over. It is a *template only*, consumed by monomorphisation, never by the backend. `defined_symbols()` stops yielding `Polymorphic` entries as codegen targets (it yields them as *mono sources* to a different consumer — the mono pass — but not to `compile_to_module`). This is the structural realisation of FIXME 0381's proposed resolution ("a slot-less `Polymorphic` generic def's body is NOT emitted to codegen at all"). **TWO filter sites enforce this** (Phase-4 part B, §4): `SymbolTable::defined_symbols()` (`crates/cranelisp-types/src/module.rs:640`) AND `derive_codegen_batch`'s `try_push` (`src/worker.rs:620`) — both currently `!Constrained && !Overloaded`; both must add `Polymorphic` to the exclusion in lockstep (Principle 7 — consolidate to one predicate if the wave allows).
- **Monomorphisation mints a concrete instance per reachable instantiation** (`id$Int`, `map$Int_String`, …), each fully `ConcreteType`-annotated (the per-instance re-check assigns concrete types to every node) and slotted (`Concrete { got_slot }`). These — and *only* these — are the `UserFn` bodies `compile_to_module` sees.

The 317× disappears because the prelude's `(List a)` / `option/Some` generic bodies stop being compiled as templates — they are compiled *only* as the concrete instances each program reaches.

### 2.3 How mono enumerates the instances (builds on the landed machinery — Principle 7)

This is the **same enumeration** S84's `pass4_monomorphise` worklist drives — NOT a new pass. The instance set is the reachable closure from the program roots:

- **Roots** = the concrete instantiations the cluster's top-level forms demand (`main`'s entry type, the test-fn mono roots from Wave 1b, any concrete-typed top-level value), plus — *new under this model* — **every concrete instantiation the prelude/stdlib's reachable call sites demand**. The prelude is no longer pre-compiled wholesale; it is mono-rooted on demand per use (§2.5).
- **Successors** = every reachable polymorphic instance re-checked at concrete type args; the `Var`s pin to concrete types via the call site's argument types and the result-hop machinery (`collect_local_parametric_calls`, `monomorphise_inner_parametric_hops`).
- **Dedup** = the existing mangled-name `name$T1+T2` `done`-set, now keyable by `ConcreteType` (stable `Hash`).
- **Termination** = monomorphic-recursion enforcement (rank-1 HM) + the `done`-set — unchanged from S84.

The single load-bearing change to the enumeration: **its output is the *complete* set of `ConcreteType`-annotatable bodies, because the slot-less template is no longer a fallback codegen target.** Where today a missed instance silently falls back to the uniform-word template (and survives by the `<1024` guard), under this model a missed instance is a **missing slot at the call site** → either the mono pass mints it (correct) or the conversion fails at the call (the ambiguity error). There is no template to fall back to. This is what makes mono coverage *forced by representation* rather than chased shape-by-shape (Principle 20).

### 2.4 Where `ConcreteType` lives on the AST — the central migration decision

**SETTLED (Phase 2, /arch, 2026-06-16): `MonoExpr` — a distinct post-mono codegen AST whose nodes carry `ConcreteType` *non-optionally*.** The two candidate forms were the field form (Option B-field) and the parallel-AST form (`MonoExpr`); the latter is the settled choice. Rationale and the rejected forms follow.

**The ruling forces the parallel AST.** The user's direction is "generics shouldn't even be REPRESENTABLE at the backend." Of the three forms below, only `MonoExpr` makes that literally true at the type level — the other two leave a `Type`-with-`Var` reachable on the node the backend reads, so they enforce the invariant *behaviourally* (a downstream "read the concrete field, trust it has no `Var`" convention) rather than *structurally*. `MonoExpr` is the fullest expression of Principle 18 (enforce invariants structurally) and Principle 20 (model the correlated invariant by representation) applied to the AST node itself: a codegen node's type field IS a `ConcreteType`, so a `Var` cannot be present on the path codegen reads — not by a `None`-vs-`Some` convention, but because the field's *type* has no `Var` variant.

- **Option A — replace `inferred_type` (REJECTED).** Change `Expr.inferred_type: Option<Box<Type>>` to `Option<Box<ConcreteType>>`. Clean end-state, but typecheck *produces* `Type` (with `Var`s) during inference and only resolves to concrete late — so the same AST node would need a `Type` annotation during inference and a `ConcreteType` annotation post-mono. One field cannot be both. Rejected as the single field.
- **Option B-field — a parallel `Option<Box<ConcreteType>>` field (REJECTED as the target; viable only as a transitional).** Keep `inferred_type: Option<Box<Type>>` as the inference-stage annotation; add a `codegen_type: Option<Box<ConcreteType>>` that mono populates only on concrete-instance nodes; backend reads `codegen_type` exclusively. **Rejected** because the node *still carries* an inference-stage `Type` (with a `Var` variant) reachable on the same struct — the structural guarantee degrades to "the backend reads the concrete field," not "the node cannot hold a `Var`." It is a wide, error-prone change (a new `Option` field threaded through all 16 `Expr` variants + the `span()`/`inferred_type()`/`set_inferred_type()` match arms + serde) that buys a *weaker* guarantee than `MonoExpr` for comparable surface churn. The migration-budget argument that would favour it (smaller than a parallel AST) does not hold: the field-threading touch count is within a small factor of the `MonoExpr` mirror, and the mirror's `from_expr` builder is purely mechanical. Retained here only as the named transitional fallback **if** Phase-2 implementation surfaces an unforeseen blocker in the parallel-AST form.
- **Option B — `MonoExpr`, a distinct post-mono codegen view (SETTLED TARGET).** A parallel codegen AST `MonoExpr` mirroring `Expr`'s variants, each carrying `ty: ConcreteType` (NON-optional) in place of `inferred_type: Option<Box<Type>>`. `MonoDefn` wraps a `MonoExpr` body (via `MonoDefnVariant`) rather than a `Defn`. The fallible builder `MonoExpr::from_expr(&Expr) -> Result<MonoExpr, NotConcrete>` walks an `inferred_type`-annotated `Expr` and produces a `MonoExpr`, failing (via `ConcreteType::from_type`) at the first node whose `inferred_type` is absent or non-concrete — **THIS failure is the unified ambiguity / could-not-monomorphise error** (§1.3, §2.6). Backend consumes `MonoExpr`; it *literally cannot* express a non-concrete or un-annotated codegen node. The architectural commitment — **the backend consumes a type that has no `Var`, on an AST view that has no inference-stage `Type` on its read path** — is realized in its fullest form: there is no `Type` field on `MonoExpr` at all.

  **What `MonoExpr` carries beyond `ConcreteType`.** Mirroring `Expr` faithfully, every `MonoExpr` node carries its `span: Span` (the backend still overlays the global `MethodResolutions` side maps — `pattern_ctors`, residual `resolved_calls` — keyed by span, so spans must survive into the codegen view). `resolved_call: Option<Box<ResolvedCall>>` rides along on the `Apply` and `Var` nodes where `Expr` carries it (the backend reads it directly off the node — `compiler/mod.rs:1133`). The `Annotate` node's `TypeExpr` annotation is *erased* in `MonoExpr` (its only role is to constrain inference, already discharged by the time mono runs; codegen reads the resolved `ty`, never the syntactic `TypeExpr`) — `MonoExpr::from_expr` collapses `Annotate { expr, .. }` to its inner `MonoExpr`. `Lambda` param `TypeExpr` annotations are likewise erased; the lambda's `ConcreteType::Fn(..)` carries the concrete param types.

  **As landed (Phase 2a, `crates/cranelisp-types/src/mono_expr.rs`).** `MonoExpr` mirrors the 14 non-`Annotate` `Expr` variants (`Annotate` has no counterpart — erased at build). Match arms are carried by a sibling `MonoMatchArm { pattern: Pattern, body: MonoExpr, span }` (the `Pattern` is reused verbatim — it carries no type annotation). The mono-defn wrapper is `MonoDefnVariant { name: Symbol, params: Vec<Symbol>, body: MonoExpr, span }` (the params' `TypeExpr` annotations erased, mirroring the `Lambda` erasure; `MonoDefn`-carries-`MonoExpr` is realised at the Phase-2b seam by the typecheck mono pass building this wrapper). `MonoExpr` derives `Debug, Clone, Serialize, Deserialize` (the cranelisp-types convention); it does **not** derive `PartialEq`/`Eq` — `Expr` cannot (it carries `f64`), and the codegen view inherits that. Accessors `MonoExpr::span()` and `MonoExpr::ty()` are provided. **An un-annotated node (`inferred_type == None`) fails identically to a residual `Var`** — `from_expr` surfaces `NotConcrete::Var(0)` (a sentinel: "no representation-determined type at this position"), since an un-annotated codegen node is as illegal as a `Var`-typed one.

  **Migration sizing (honest).** This IS the largest of the three forms — a parallel AST plus the backend's rewrite to consume it. But the cost splits cleanly across the existing phase boundary: **Phase 2 lands `MonoExpr` + the builder + unit tests in `cranelisp-types` (produces-but-unused), and the mono pass is wired by /dev(typecheck) to build it.** The backend's switch from reading `Expr.inferred_type` to consuming `MonoExpr.ty` is **Phase 3** (the existing plan — `HeapCategory::classify` takes `&ConcreteType`, `compile_to_module` consumes `MonoExpr`). The parallel-AST form does not enlarge Phase 3 beyond what §4 already budgets (the backend was always going to migrate its read path); it *relocates* the type carried on that path from `Option<Box<Type>>` to `ConcreteType`. The builder is mechanical and fully unit-tested at the seam where the bug would live.

#### The mono-population seam (Phase 2b spec for /dev(typecheck))

The conversion `MonoExpr::from_expr` plugs in at **one site**: the `MonoDefn` construction in `monomorphise_call` (`crates/cranelisp-typecheck/src/traits.rs`, the `let mono_defn = MonoDefn { … }` site at ~`:1479`), **immediately after `apply_subst_to_defn(&state.subst, &mut mono_defn_ast)`**. At that point the per-instance re-check (`recheck_body_for_mono` → `check_defn_body_with_types`) has already inferred every node's type, `annotate_defn_from_maps` has written each node's `inferred_type` from the span-keyed `expr_types`, and `apply_subst_to_defn` has resolved every `inferred_type` through the substitution — so every node of `mono_defn_ast` carries a *substitution-resolved* `inferred_type`. This is the invariant `from_expr` requires.

The seam, in shape:

1. `recheck_body_for_mono` + `annotate_defn_from_maps` + `apply_subst_to_defn` run unchanged — they leave `mono_defn_ast: Defn` fully `inferred_type`-annotated and subst-resolved.
2. `MonoExpr::from_expr(mono_defn_ast.body())` (per variant) builds the `MonoExpr`. On `Ok`, `MonoDefn` is constructed carrying the `MonoExpr` body (via `MonoDefnVariant`) — *replacing* today's `Defn`-bodied `MonoDefn`. On `Err(NotConcrete::Var(_) | HktHead(_))`, the mono pass returns `Err(CranelispError::TypeError { … })` — the **ambiguity / could-not-monomorphise** error (§1.3, §2.6), reusing the §3.11.1 diagnostic wording (the message the current `is_representation_undetermined` position-complete scan produces, so no rejection-coverage regression — see §3's "SUBSUMED by the conversion" row).
3. `register_mono_entry` is unaffected — it reads `mono.defn`'s name/scheme/visibility to build the `ModuleEntry::Def`; the symbol-table entry shape does not change (the GOT-slot/`UserFnState::Concrete` machinery is independent of the body's AST form).
4. **`pass4_monomorphise`'s `Vec<MonoDefn>` output is unchanged in cardinality and dedup** — only each element's *body representation* changes from `Defn`(`Expr`) to `MonoDefn`(`MonoExpr`). The worklist/`seen`-set/mangled-name dedup is untouched (Principle 7 — the enumeration is extended at the body-build step, not forked).

**Phase-2 boundary:** the backend still reads `Expr.inferred_type` in Phase 2 — it does NOT yet consume `MonoExpr`. So Phase 2b's `MonoDefn`-carries-`MonoExpr` change is **produced-but-unused for codegen**; whatever scaffolding currently hands `mono.defn: Defn` to `compile_to_module` keeps a `Defn` view until Phase 3 (either the mono pass retains both the `Defn` and the `MonoExpr` transitionally, or Phase 3 flips the consumer — /dev(typecheck) + /dev(backend) coordinate the exact transitional shape at Phase 2b/3; the `cranelisp-types` representation supports both, since `from_expr` is non-destructive over the source `Expr`). The suite stays green because codegen behaviour is unchanged.

### 2.5 Prelude/stdlib generics become on-demand mono roots

Today: prelude generic bodies are compiled at session init as templates. Target: the prelude is type-checked (its schemes registered, its `Polymorphic` templates available as mono *sources*) but **its generic bodies are not codegen'd until a program reaches a concrete instantiation**. Each reaching use is a mono root; the mono pass mints `option/Some$Int`, `collections.list/cons$String`, etc. This is the direct cause-fix for FIXME 0381's 317× — those bodies stop being emitted as templates.

Concrete fully-monomorphic prelude functions (no `Var` in their signature) are unaffected — they are `Concrete`, slotted, emitted once as today.

### 2.6 First-class generic values — the conversion failure IS the rule

A generic referenced *as a first-class value* (not applied — e.g. `(map id xs)` where `id : ∀a.a→a` is passed un-instantiated, or a generic stored in a vec) must be **monomorphised at the use** — the use site's expected type concretises it, the mono pass mints the instance, and that instance's slot is what the value resolves to. If no use-site type pins it (a genuinely ambiguous first-class generic), `ConcreteType::from_type` fails at that position → the ambiguity error (0373 ii). This is the natural, structural failure the user named: "it must be monomorphised at the use, or it is the ambiguity error." No special case — it falls out of the conversion.

### 2.7 Reconciliation with the constrained-polymorphism path

Trait-dictionary monomorphisation already exists: a `Constrained` template is slot-less, and `monomorphise_call` mints `cmp$Int+Int` concrete instances per call. **This arc UNIFIES with it.** Both `Constrained` and `Polymorphic` are slot-less templates that are *never emitted as templates* and are *specialised to concrete slotted instances per reachable use*. The only difference is *why* the vars are free (trait dictionaries vs plain parametricity) and *how* they pin (dictionary resolution vs argument-type unification) — both end at a `Concrete { got_slot }` instance whose body is `ConcreteType`-annotatable. Under this arc, "the template body is never emitted" becomes true for **both** slot-less arms identically — today it is true for `Constrained` (`defined_symbols()` skips it) but *false* for `Polymorphic` (`defined_symbols()` yields it, the 0381 bug). The arc makes the two arms symmetric: **neither is a codegen target; both are mono sources.** That symmetry is the cleanest statement of the fix — the `Polymorphic` arm was the odd-one-out and that asymmetry was the leak.

---

## 3. Reconciliation with what S84 landed

| S84-landed item | Disposition under this arc |
|---|---|
| **Slot gate `is_concrete()`** (Wave 1) — `Concrete{slot}` ⟺ `is_concrete()` | **KEEPS.** Operates on `Type` at the typecheck slot gate, *before* conversion. Re-expressed as `ConcreteType::from_type(ty).is_ok()`. The gate is the typecheck-side determinant of which defs get slots; the boundary type is the *downstream* structural guarantee. They are complementary, both retained. |
| **`UserFnState::Polymorphic`** slot-less variant (Wave 1, FIXME 0377) | **KEEPS + its `defined_symbols()` treatment CHANGES.** `Polymorphic` stays the slot-less generic template. But `defined_symbols()` stops yielding it as a `compile_to_module` codegen target (§2.2) — it becomes a mono *source* only, symmetric with `Constrained`. This is the one behavioural change to a landed item. |
| **Wave 1b test-fns-as-mono-roots** (carve-out retired) | **KEEPS.** Unaffected — test fns are already mono roots minting concrete instances; those instances are exactly the `ConcreteType`-annotatable bodies this arc emits. |
| **§3.11.1 position-complete typecheck check** (Wave 2, FIXME 0379, commit `9569536`) | **SUBSUMED by the conversion.** The position-complete scan calling `is_representation_undetermined()` at every codegen-reaching position *becomes* `ConcreteType::from_type` failing at the mono boundary for that position. The check is the *interim* enforcement; the conversion is the *structural* one. Phase 3 retires the standalone scan once the conversion is the choke point. KEEP it until Phase 3 lands (it is the current load-bearing fix; FIXME 0381 deferred the backend half precisely so this typecheck half carries the soundness alone). |
| **`Type::is_representation_undetermined()`** (Wave 2 predicate) | **MADE REDUNDANT at the boundary; retired Phase 3.** Its job (flag a representation-undetermined value at an RC site) is done by `ConcreteType` not admitting such a value. Retire when `classify` takes `ConcreteType`. |
| **`Type::is_concrete()`** (Wave 1 predicate) | **KEEPS** — re-expressed via the conversion; still the slot-gate predicate. |
| **FIXME 0375 backend backstop** (`classify(Type::Var)`/`Mixed`-with-var panic) | **DROPPED — superseded by structural enforcement.** `classify` takes `ConcreteType`; the `Var` arm and the `is_representation_undetermined()` gate both become *inexpressible* (the input type has no `Var`). No backstop is needed because the illegal input is unconstructable. The deferred-backstop state of FIXME 0381 is the *correct interim* until this arc lands; the arc retires the backstop entirely rather than re-arming it. |
| **FIXME 0381** (backstop blocked on generic-body compilation) | **SUBSUMED.** Its proposed resolution ("a slot-less `Polymorphic` def's body is NOT emitted to codegen at all") IS §2.2 of this arc. 0381 is annotated to point here; it closes when Phase 4 lands (generic-body elimination), at which point the backstop it tracks is not re-armed but *deleted*. |
| **§12.1 uniform-word mandate / FIXME 0373(iii)** | **RELAXED — Phase 5.** Once generic bodies are no longer compiled uniform-word and every codegen value is `ConcreteType`, §12.1's uniformity is genuinely backend-internal and 0373(iii) relaxation is sound (the backend chooses each concrete type's representation). |

**Net:** the arc KEEPS the slot gate, `is_concrete()`, `Polymorphic`, and Wave 1b; SUBSUMES the §3.11.1 check and `is_representation_undetermined()` into the conversion; SUPERSEDES/DROPS the 0375 backstop and the FIXME-0381 deferred state by making the illegal input unconstructable; folds 0375 in (it does not re-arm — it deletes).

---

## 4. Phased plan + HONEST sizing

**Bottom line on sizing: this is a dedicated arc, NOT the remainder of S84.** Only Phase 1 is S84-sized (a small foundational scaffold). Phases 2–5 are a multi-sprint migration whose centre of gravity is Phase 2 (mono produces `ConcreteType`) and Phase 4 (generic-body elimination) — each comparable in scope to a full S84-Cluster-A spine wave. The honest recommendation is to **land Phase 1 as a scaffold now (or early next sprint) and open a dedicated sprint for Phases 2–5.** Do not attempt Phases 2–4 in the S84 remainder — S84 already carries the interim guards (the §3.11.1 check + the deferred 0381 backstop) that hold the line until this arc runs.

### Phase 1 — `ConcreteType` + the fallible conversion (scaffold, no behaviour change)

- **Crates:** `cranelisp-types` only.
- **Work:** the `ConcreteType` enum (§1.2), `from_type`/`to_type` (§1.3), `NotConcrete`, unit tests (concrete round-trips; every `Var`/`TyConApp` failure arm; nested `ADT`/`Fn` concreteness). Re-express `Type::is_concrete()` in terms of `from_type(..).is_ok()` (or leave it; either is fine).
- **Public-API / BC / cache:** additive — new public type + two methods + one error enum. `public-api.txt` regen (a handful of additive lines). `ConcreteType` derives `Serialize`/`Deserialize` (cache convention) but is *not yet on any cached shape*, so **no cache bump**. No BC shape change (this doc is the manifestation site; `interfaces.md` gains a one-line pointer).
- **Risk:** near-zero — dead code until a consumer uses it. Pure addition.
- **Size:** SMALL — S84-fits as a foundational scaffold (see §Commit note).

### Phase 2 — mono produces `ConcreteType`; the AST carries it

**§2.4 SETTLED: `MonoExpr` (parallel codegen AST). Phase 2 splits into 2a (cranelisp-types representation — LANDED) and 2b (mono population — /dev(typecheck)).**

- **Crates:** `cranelisp-types` (the `MonoExpr`/`MonoDefnVariant` types + builder — Phase 2a), `cranelisp-typecheck` (mono pass builds `MonoExpr` — Phase 2b).
- **Phase 2a work (LANDED, /arch, `crates/cranelisp-types/src/mono_expr.rs`):** the §2.4 decision recorded; `MonoExpr` mirroring `Expr`'s 14 non-`Annotate` variants with `ty: ConcreteType` (non-optional) + `MonoMatchArm` (pattern reused verbatim) + `MonoDefnVariant { name, params, body: MonoExpr, span }` wrapping a `MonoExpr` body; the fallible builder `MonoExpr::from_expr(&Expr) -> Result<MonoExpr, NotConcrete>` walking an `inferred_type`-annotated `Expr`, failing via `ConcreteType::from_type` at the first non-concrete node and via the `NotConcrete::Var(0)` sentinel at the first un-annotated node — THIS failure is the unified ambiguity/could-not-mono error (§1.3/§2.6). `Annotate`/`Lambda`-param `TypeExpr` erasure realised. Serde (`Serialize`/`Deserialize`) + `Debug`/`Clone` derives + 10 unit tests (concrete int/adt/apply/match round-trips; un-annotated node fails; residual-`Var` node fails with `NotConcrete::Var` at that node; nested-`Annotate` and `Lambda`-param erasure exercised). `MonoExpr` is **produced-but-unused** in 2a — dead until 2b wires it and Phase 3 consumes it. **Cache `CACHE_SCHEMA_VERSION` bumped 6 → 7** (`crates/cranelisp-backend/src/cache/mod.rs`) — the one authorised backend touch.
- **Phase 2b work (/dev(typecheck)):** the mono pass calls `MonoExpr::from_expr` on each concrete instance's fully-annotated `Defn` body at the seam **immediately after `apply_subst_to_defn`** in `monomorphise_call` (`crates/cranelisp-typecheck/src/traits.rs` — the `MonoDefn` construction site, ~`:1479`; see §2.4 "mono-population seam" below). The `from_expr` failure surfaces as the existing `CranelispError::TypeError` ambiguity error (reuse the §3.11.1 / `is_representation_undetermined` diagnostic wording — no regression in rejection coverage). `pass4_monomorphise` returns `Vec<MonoDefn>` carrying `MonoExpr` bodies. **In Phase 2 the backend does NOT yet consume `MonoExpr` — it still reads `Expr.inferred_type` (Phase 3 switches it). So Phase 2 is produces-but-unused for codegen: no behaviour change, suite stays green.**
- **Public-API / BC / cache:** `cranelisp-types` gains the `MonoExpr`/`MonoDefnVariant`/`MonoExpr::from_expr` surface → `public-api.txt` move (additive). **`CACHE_SCHEMA_VERSION` bump 6 → 7** — the `MonoDefn`/AST serde shape participates in the cached `.meta.json` shape (Phase 2a lands the bump; the constant is `cranelisp-backend/src/cache/mod.rs`). BC §2 amended (typecheck produces the concrete-boundary annotation). `interfaces.md` gains the `MonoExpr` narrative. This is the first behaviour-relevant phase (2b changes what mono produces, though codegen does not yet read it).
- **Risk:** MEDIUM-HIGH at 2b — the mono-coverage completeness (every reachable node converts) is the correctness obligation, guarded by the existing 0344/0349 fold canary + the S84 Tier-2 e2e guards. The `from_expr`-failure-as-error path must produce the same diagnostics the §3.11.1 check produces today. **2a risk: near-zero** (produces-but-unused additive type + mechanical builder, fully unit-tested).
- **Size:** 2a SMALL-MEDIUM (the parallel-type mirror + builder + tests); 2b MEDIUM (wire the seam + error path). The backend's consumption (the larger cost) is Phase 3, unchanged.

### Phase 3 — backend consumes `ConcreteType`; `classify` loses the `Var` arm

- **Crates:** `cranelisp-backend` (the ~13 files reading `inferred_type`), `cranelisp-runtime`/`-intrinsics` only if a signature crosses.
- **Work:** `HeapCategory::classify` takes `&ConcreteType`; the `Var`/`TyConApp` arms and the `is_representation_undetermined()` gate are deleted (inexpressible). `compile_to_module` reads `codegen_type`/`MonoExpr`. A `None`/missing codegen annotation is a single relocated `expect` (the one backstop replacing the four). Retire the §3.11.1 standalone scan + `is_representation_undetermined()` (now subsumed).
- **Public-API / BC / cache:** `classify` is backend-internal (no baseline move). BC §3 invariant 9 rewritten — the belt-and-braces two-predicate framing collapses to "the boundary type has no `Var`; `classify` is total." `is_representation_undetermined()` retired from `cranelisp-types` (`public-api.txt` removal — a *removal* line, the only non-additive baseline move in the arc).
- **Risk:** MEDIUM — the breadth of `inferred_type` read sites in backend; each must move to the concrete view. The `#[should_panic]` backstop tests retire.
- **Size:** MEDIUM-LARGE.

### Phase 4 — mono-completeness + generic-body-codegen elimination (DETAILED — /arch, 2026-06-16, re-sequenced BEFORE Phase 3)

> **Re-sequencing note.** Phase 4 is run *before* Phase 3. Phase 2b (mono population) LANDED with an `allowed_vars` carve-out (`crates/cranelisp-typecheck/src/traits.rs:1514`) that ADMITS a mono instance whose body retains scheme-quantified vars — producing **no `MonoExpr`** for that instance. Phase 3 (backend consumes `MonoExpr`) cannot proceed until **every** instance has a `MonoExpr`, so the mono-completeness work (Phase-4 part A) is the gate. Part B (generic-body-codegen elimination) is the original Phase 4. They are coupled and land in order **A → B**.

Phase 4 has **two coupled parts** plus a **reconciliation constraint**:

- **(A) Mono-completeness** — make every monomorphised instance's BODY fully concrete, so `MonoExpr::from_expr` succeeds on every instance and the `allowed_vars` carve-out becomes dead code.
- **(B) Generic-body-codegen elimination** — `Polymorphic` stops being a `compile_to_module` codegen target (symmetric with `Constrained`); prelude/stdlib generics become on-demand mono roots. This is the cause-fix for FIXME 0381's 317×.
- **(C) The 0344 reconciliation** — (A) must concretise the fold accumulator for a *concrete* call without re-introducing the over-unification 0344/0349 guard against.

---

#### 4-A. Mono-completeness — ROOT CAUSE (diagnosed concretely, /arch 2026-06-16)

**The witness.** For the 0344 fold repro (`tests/spec_04_expressions.rs::polymorphic_accumulator_fold_does_not_over_unify`), the mono pass produces TWO `reduce-loop` instances:

| Instance | `resolved` param/return types | `from_expr` |
|---|---|---|
| `reduce-loop$Int+Vec+Int+Int` | `Fn([Fn([Int,Int],Int), Int, (Vec Int), Int, Int], Int)` — **fully concrete** | `Ok` |
| `reduce-loop$Vec+Int+Int` | `Fn([Fn([Var34,Var31],Var34), Var34, (Vec Var31), Int, Int], Var34)` — **partial** | `Err(Var(34))` |

The `Ok` instance is the genuine concrete chain `main → reduce$Int+Vec → reduce-loop$Int+Vec+Int+Int`. The `Err` instance is **spurious**.

**The mechanism (file:line).** The `$Vec+Int+Int` instance is minted by `monomorphise_inner_parametric_hops` (`crates/cranelisp-typecheck/src/traits.rs:1860`) via `collect_apply_var_calls` recursing into `reduce`'s body `(reduce-loop f init v (vec-len v) 0)`. At the point this inner hop is collected, only `(vec-len v) → Int` and `0 → Int` are concrete; `f`, `init`/`acc`, and the element type are still **`reduce`'s OWN generic scheme vars** (`Var34` = accumulator `b`, `Var31` = element `a`). The hop is nonetheless collected because the call-collection gate `local_parametric_call_triggers` (`crates/cranelisp-typecheck/src/program.rs:3217`) **trigger-1** (`result_is_bare_var`) fires — `reduce-loop`'s result IS the accumulator `Var34`. So `monomorphise_call` runs with `concrete_param_types = [(Fn[Var34,Var31]→Var34), Var34, (Vec Var31), Int, Int]` — a **partial instantiation**.

Two consequences compound:

1. **The mangled name is LOSSY.** `build_mangled_name` (`traits.rs:2065`) → `concrete_type_name` (`traits.rs:2076`) returns `None` for `Type::Var` and `filter_map` **silently drops** the Var-typed params. So `[(Fn...), Var34, (Vec Var31), Int, Int]` mangles to `reduce-loop$Vec+Int+Int` — the `f`, `acc`, and return positions vanish from the name. Two *genuinely distinct* partial instantiations could collide on this name (a latent correctness hazard, not just incompleteness).
2. **The body inherits the surviving vars.** `apply_subst_to_defn` resolves each node's `inferred_type` through `state.subst`, but `Var34`/`Var31` were never unified to concrete types (the call did not pin them), so they survive into the body — `from_expr` fails at the `acc`-typed node.

**Root statement.** *A generic hop reached from a generic caller's body is monomorphised at the CALLER's generic instantiation, not at a concrete instantiation.* The inner-hop collector recurses **eagerly** on a result-bare-var trigger even when the hop's arguments are still the parent's free scheme vars. The instance it mints is structurally a *re-spelling of the generic template* (same free vars, new name), not a concrete specialisation. This is distinct from the genuine concrete chain, which arrives at `reduce-loop` with all args pinned.

**Why the accumulator IS concretizable for a concrete call.** For `(reduce + 0 [1 2 3])`, the chain `reduce$Int+Vec` re-checks `reduce`'s body with `init: Int`, so the `reduce-loop` call inside it has `acc → Int`, `f → (Fn[Int,Int]→Int)`, element `→ Int`: the `reduce-loop$Int+Vec+Int+Int` instance is fully concrete (the `Ok` row above). **The concrete instance already exists and already succeeds.** The completeness problem is *not* that the concrete accumulator can't be determined — it is that a *second, spurious, partially-instantiated instance* is ALSO minted from the generic-caller recursion, and that one is incomplete.

#### 4-A. Mono-completeness — THE FIX (design; /dev(typecheck) lands it)

**The fix is to NOT mint the spurious partial instance, NOT to "complete" it.** A partially-instantiated hop is not a codegen target — it is a generic template under a different name. The completeness end-state ("every minted instance is concrete") is reached by **suppressing the partial-instance mint at the collection gate**, so the only `reduce-loop` instances are the genuinely-concrete ones.

**Primary change — tighten the inner-hop collection gate to require ALL ARGS CONCRETE.** The inner-hop collectors must mirror `local_parametric_call_triggers` **trigger-2** (all args concrete), and must NOT mint on the bare-var-result trigger alone when the args are not concrete:

- `monomorphise_inner_parametric_hops` (`traits.rs:1860`, the `for (inner_name, arg_spans, inner_span) in &inner_sites` loop, ~`:1892`): it already computes `inner_arg_types` and skips if `inner_arg_types.len() != arg_spans.len()`. **Add: skip if any `inner_arg_types[k]` is not `is_concrete()`** (after `apply(&state.subst, …)`). A hop whose args are still the parent's free vars is not a concrete instance — it must not be minted. The genuine concrete instance is minted by the parent's *concrete* re-check chain (the `reduce$Int+Vec` → `reduce-loop$Int+Vec+Int+Int` path), which already passes the all-concrete gate.
- The same all-args-concrete guard belongs anywhere a hop is collected from a *generic* re-check context. Audit `collect_apply_var_calls` callers + `collect_local_parametric_calls` (`program.rs:3258`) for the same eager-on-bare-var-result shape. `collect_local_parametric_calls` already routes through `local_parametric_call_triggers` — but trigger-1 (`result_is_bare_var`) is exactly the over-eager path; **the completeness fix is to make trigger-1 ALSO require all-args-concrete, OR to drop trigger-1 entirely** (see "trigger-1 disposition" below).

**Trigger-1 disposition (the load-bearing decision).** Trigger-1 (`result_is_bare_var`) was the original 0373 polymorphic-result-hop fix: a hop whose *result* is a bare var leaves a `Type::Var`-result body at codegen. But the diagnosis shows trigger-1 *also* fires on the generic-caller recursion, minting the spurious partial. Two options:

- **Option 1 (preferred) — require all-args-concrete on BOTH triggers.** A hop is a mono site iff its args are all concrete (trigger-2's guard), regardless of result shape. The result-bare-var case is then covered *only when the args are concrete* — which is exactly when the result CAN be concretised (a concrete-arg call whose result var is pinned by the body re-check). A result-bare-var hop with non-concrete args is the spurious partial — excluded. This unifies the two triggers into one predicate (all-args-concrete) and is the cleanest statement: **a mono instance is minted iff every argument is concrete; its result is then concrete by the per-instance re-check** (the body re-check + `unify(body_ty, ret_ty)` pins it). This is Principle 7 (one predicate, not two) and Principle 20 (the mintability invariant is "all args concrete").
- **Option 2 (narrower) — keep trigger-1 but add the all-args-concrete guard to it.** Same effect, but leaves two triggers where one suffices. Rejected on Principle 6/7 unless Option 1 surfaces a regression in the existing 0373 result-hop e2e guards (`tests/regression.rs` Tier-1/1.5 hops).

**The /dev(typecheck) obligation: land Option 1, verify the 0373 result-hop guards stay green.** If a genuine result-hop case requires minting on a bare-var result with non-concrete args (it should not — that case is the ambiguity error, §2.6), that is a FIXME `target: /arch` escalation, not a silent re-widening.

**Secondary hardening — make `build_mangled_name` total or var-faithful (Principle 18).** The lossy `filter_map`-drop of Var-typed params (`traits.rs:2065`) is a latent collision hazard independent of the trigger fix. Once Option 1 lands, a minted instance has all-concrete *args* — but the mangled name is built from `concrete_param_types`, which the all-concrete gate guarantees are concrete, so the drop never fires for a correctly-gated instance. **Disposition: after Option 1, assert that `build_mangled_name` is called only with all-concrete param types** (a `debug_assert!` that `concrete_type_name` returns `Some` for every param), turning the silent drop into a tripwire. This is the structural complement: the gate guarantees concreteness; the assert proves the mangler never sees a var. /dev(typecheck) lands the assert alongside Option 1.

**The carve-out becomes dead code.** With Option 1, every minted instance is concrete ⇒ `MonoExpr::from_expr` succeeds on every instance ⇒ the `allowed_vars` computation + the `Err(NotConcrete::Var(id)) if allowed_vars.contains(&id) => {}` arm (`traits.rs:1514–1538`) is never taken. **/dev(typecheck) DELETES the `allowed_vars` block and that match arm** as part of part A; the remaining `Err(nc) => { …ambiguity error… }` arm stays (it now catches genuinely-free residuals, the real ambiguity case). The deletion IS the completeness proof: if any prelude/stdlib instance still fails `from_expr` after the carve-out is removed, the suite goes red at that instance — exactly the forcing function the arc wants (Principle 20: completeness forced by representation, not chased by hand).

**Functions to change (part A):**
- `crates/cranelisp-typecheck/src/traits.rs::monomorphise_inner_parametric_hops` (~`:1892`) — add all-args-concrete guard before minting an inner hop.
- `crates/cranelisp-typecheck/src/program.rs::local_parametric_call_triggers` (`:3217`) — Option 1: collapse trigger-1+trigger-2 into the single all-args-concrete predicate (or guard trigger-1 with it).
- `crates/cranelisp-typecheck/src/traits.rs::build_mangled_name` / `concrete_type_name` (`:2065`) — add the all-concrete `debug_assert!` tripwire.
- `crates/cranelisp-typecheck/src/traits.rs` mono-population seam (`:1514–1558`) — delete the `allowed_vars` block + the scheme-quantified-var admit arm; keep the genuine-ambiguity-error arm.

**Unit tests (part A, /dev(typecheck), mandatory per CLAUDE.md §Testing):**
- A fold-shape instance (`reduce`/`reduce-loop`) mints ONLY concrete `reduce-loop` instances (no `$Vec+Int+Int` partial) — assert the mono-variant set contains `reduce-loop$Int+Vec+Int+Int` and NOT a Var-bearing partial.
- The existing 0373 result-hop unit guards (Tier-1/1.5) stay green (the all-args-concrete gate still mints the genuine concrete result-hop).
- `from_expr` succeeds on every minted instance for the fold repro (the completeness assertion at the seam).

#### 4-C. The 0344 reconciliation (why part A coexists with the over-unification guard)

The 0344/0349 invariant: a polymorphic accumulator threaded through a recursive fold MUST stay polymorphic so a sibling `(Vec a)`-accumulator use does not collapse the scheme — *distinct instantiations stay distinct*. Part A's fix is **compatible by construction** and in fact *strengthens* the invariant:

- Part A does NOT pin `reduce`'s accumulator scheme var. It *suppresses minting a partial instance* — it never unifies `Var34` to anything. The over-unification 0344 guards against is a *scheme-collapse during inference* (`program.rs` generalize-before-cross-defn-use, `:912`); part A operates *after* inference, at the mono-collection gate, and only *narrows which instances are minted*. It touches no unification.
- The `monomorphise_inner_parametric_hops` subst-isolation (`traits.rs:1923–1943` — `saved_subst`/`state.subst = saved_subst`) that protects 0344 from the inner-mono FIXME-0349 propagation **stays** — part A's all-args-concrete guard runs *before* that recursion is entered, so it composes cleanly (the guard skips the spurious hop; the isolation protects the genuine ones).
- The genuine concrete instance `reduce-loop$Int+Vec+Int+Int` has accumulator `Int` because the concrete *call* `(reduce + 0 …)` pinned it through `reduce`'s concrete re-check — that is a per-instance fact, not a scheme collapse. A second concrete call at a different accumulator type mints a *different* concrete instance (`reduce-loop$String+…`), distinct by construction. **Distinct instantiations stay distinct** — exactly the 0344 invariant.

**The 0344 canary is the completeness guard.** `tests/regression.rs::mono_tier2_fold_accumulator_not_over_monomorphised` + `tests/spec_04_expressions.rs::polymorphic_accumulator_fold_does_not_over_unify` + the 0344/0349 unit guards MUST stay green through part A. If part A's gate-tightening accidentally suppresses a *genuine* concrete instance (over-narrowing), the fold returns the wrong value and these go red. They are the bidirectional guard: red-if-incomplete (a missing concrete instance) AND red-if-over-unified (a collapsed scheme).

> **NOTE on the pre-existing 0344 over-unification bug.** `polymorphic_accumulator_fold_does_not_over_unify` currently FAILS (exit 0, not 6) — the 0344 over-unification is a *separate, pre-existing* `/typecheck` defect (scheme collapse during inference, `program.rs:912`), NOT introduced or fixed by this arc. Part A does not depend on 0344 being fixed first: part A's completeness fix (suppress the partial instance) is orthogonal to the inference-side collapse. After part A, the *partial* `reduce-loop$Vec+Int+Int` instance disappears regardless of whether the 0344 collapse is resolved. /dev(typecheck) should note this when landing part A — the fold e2e may stay red on the *separate* 0344 inference bug, but the *completeness* assertion (`from_expr` succeeds on every MINTED instance) must pass, and no partial instance is minted. The 0344 inference fix is tracked separately under its existing FIXME and is NOT a Phase-4 gate.

#### 4-B. Generic-body-codegen elimination — DETAILED (design; /dev(typecheck) + /dev(int) land it)

Part B makes `Polymorphic` symmetric with `Constrained`: never a `compile_to_module` codegen target, only a mono source. **There are TWO filter sites** (both currently `!Constrained && !Overloaded`, both INCLUDE `Polymorphic`):

1. **`SymbolTable::defined_symbols()`** — `crates/cranelisp-types/src/module.rs:640–649`. The canonical codegen-eligibility filter. Its rustdoc (`:631–639`) explicitly documents the asymmetry ("`Polymorphic` is a mono target, NOT skipped like `Constrained`") — that rustdoc is the thing part B reverses.
2. **`derive_codegen_batch`'s `try_push` predicate** — `src/worker.rs:620–625` (int). The same `!Constrained && !Overloaded` match, applied as int derives the per-module codegen batch. This is a *second* gate that must move in lockstep (Principle 7 — and a reminder that the eligibility predicate is duplicated; part B should consider consolidating, see below).

**The change (both sites):** add `| DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }` to the excluded set. After this, a slot-less `Polymorphic` template's body is never enumerated as a codegen target — only its concrete `Concrete { got_slot }` mono instances (minted by part A's enumeration, registered by `register_mono_entry`) flow to `compile_to_module`.

**Consolidation opportunity (Principle 7 — /arch flags, /dev decides).** The eligibility predicate lives in two places (`module.rs:641` and `worker.rs:620`). The arc is the natural moment to make `defined_symbols()` the single source and have `worker.rs::try_push` *call it* (or call a shared `ModuleEntry::is_codegen_target()` predicate on `cranelisp-types`) rather than re-spell the match. /dev(typecheck) owns `module.rs`; /dev(int) owns `worker.rs`; coordinate so the predicate is written once. If consolidation is out of scope for the wave, BOTH sites must still change identically — a `Polymorphic` slipping through `try_push` (int) while excluded by `defined_symbols()` (types) is exactly the asymmetry that hides bugs.

**`Constrained` is already correctly skipped** — confirmed at both sites (`module.rs:645`, `worker.rs:623`). Part B makes `Polymorphic` join it; no `Constrained` change.

**Prelude-as-mono-source (the 317× cause-fix).** Survey finding (src/int): the prelude is type-checked at session init (`src/worker.rs:1382` typecheck; `src/scheduler.rs:242` priority codegen) and its `defined_symbols()` batch is codegen'd eagerly via `derive_codegen_batch` → `inline_jit_codegen_for_module` → `compile_to_module`. Today a generic prelude body (e.g. `collections.list`'s `(List a)` cons, `option/Some`'s field) is `Polymorphic` with `ast: Some(_)` ⇒ it IS in the `defined_symbols()` batch ⇒ it is compiled as a template carrying free `Type::Var`s — **the 317× fire**. After part B's filter change, that generic body is *excluded from the batch* at both gates; it is codegen'd only as the concrete instances each program reaches (minted on-demand by part A's enumeration when a concrete use is type-checked). **No new int code path is needed** — the existing `register_mono_entry`-registers-a-`Concrete`-entry + the existing `defined_symbols()`-enumerates-`Concrete`-entries path already codegens the concrete instances. Part B is *subtractive at the gate*, not additive at the loader: the concrete-instance codegen path already exists (it is how `cmp$Int+Int` constrained instances and `reduce$Int+Vec` parametric instances already reach codegen today). The prelude's *fully-monomorphic* functions (no `Var` in signature — `Concrete`, slotted) are unaffected; they stay in the batch and codegen once as today.

**src/int surface assessment (part B):**
- `src/worker.rs:620` `try_push` — the one int filter change (add `Polymorphic` to the exclusion). The dominant int touch.
- `src/worker.rs:671–687` — the trailing `defined_symbols()` sweep (codegens any synthesised symbol not in the TopLevel forms). After `defined_symbols()` excludes `Polymorphic`, this sweep no longer sees generic templates — correct, no further change.
- **No prelude-loading control-flow change.** The prelude is still loaded, type-checked, and its `Concrete` bodies codegen'd at init. What changes is *which entries `defined_symbols()` yields* — a data change at the filter, not a flow change at the loader. The "prelude pre-compiles generic bodies" framing in the earlier Phase-4 prose is realised purely by the filter exclusion.
- **Mode uniformity** — the filter lives in `defined_symbols()` (types) + `try_push` (int worker), both mode-independent (the same `derive_codegen_batch` serves `--run`/`--link`/REPL). One change, all modes.

**Unit tests (part B):**
- /dev(typecheck): `defined_symbols()` does NOT yield a `Polymorphic` entry (symmetric with the existing `Constrained`-exclusion test, if any; add both directions).
- /dev(int): `derive_codegen_batch` excludes a `Polymorphic` entry, includes its `Concrete` mono instance.

#### Phase-4 — Public-API / BC / cache + sizing

- **Public-API:** `defined_symbols()` signature is unchanged (the filter body changes, not the signature) — **no `cranelisp-types` baseline move** unless the consolidation introduces a new `pub fn is_codegen_target()` (then one additive line + the two-update discipline). The `traits.rs`/`program.rs` mono changes are `pub(crate)`/internal — no typecheck baseline move. `worker.rs` is int (binary, no baseline).
- **BC:** §2 (typecheck) amended — the mono enumeration mints only all-args-concrete instances; the `allowed_vars` carve-out is retired; `defined_symbols()` excludes `Polymorphic`. §7 (types) amended — `Polymorphic`/`Constrained` are *symmetric* codegen non-targets (the `defined_symbols()` rustdoc at `module.rs:631–639` is rewritten to state the symmetry). The Principle-20 worked example (callability-structural) gains the codegen-target symmetry.
- **Cache:** no `CACHE_SCHEMA_VERSION` bump — part A/B change *which entries are produced/enumerated*, not any serialized shape (the `MonoDefnVariant`/`MonoExpr` shape + its 6→7 bump landed in Phase 2a).
- **Sizing — HONEST.** Part A is MEDIUM (a focused gate-tightening + carve-out deletion + the mangler tripwire + unit tests — the diagnosis is done, the change is localised to 3 functions). Part B is SMALL-MEDIUM (two filter-line changes + the rustdoc rewrite + optional consolidation + unit tests; the heavy lifting is the e2e validation that the 317× is gone). **Phase 4 is plausibly ONE /dev wave with two sub-steps (A then B), NOT a multi-wave LARGE** — the original "LARGE" sizing assumed the completeness fix would require *completing* partial instances (propagating subst into every body position); the diagnosis shows it requires the *opposite and simpler* move (suppress the spurious partial mint), which is a gate tightening, not a body-rewrite. **Sub-phase order: A strictly before B.** Part A makes every minted instance concrete (so `from_expr` succeeds everywhere + the carve-out is deletable); part B then removes the template fallback that B's absence currently relies on. Landing B before A would emit no template AND leave incomplete instances with no `MonoExpr` — a gap. A-then-B is the only sound order. Each is its own /dev sub-step (A's unit tests must be green before B's filter flips), but they can land in **one wave / one change-set** if the agent sequences A's verification before B's edit.

- **Risk:** part A is MEDIUM (the gate-tightening must not over-narrow — the 0344 canary + the 0373 result-hop guards are the bidirectional witnesses). Part B is HIGH on the e2e axis — it changes *which bodies are emitted across the whole prelude/stdlib*; **every prelude-using e2e test is a witness** (the full `tests/` suite under `PreludeVariant::TestPrelude`, plus the stdlib-using exemplar tests). The validation gate: after A+B, (1) `from_expr` succeeds on every minted instance (no carve-out needed — it is deleted), (2) the prelude/stdlib suite is green with NO generic template emitted (the 317× is gone), (3) the 0344 canary + 0373 result-hop guards stay green. FIXME 0381 is the standing record; it closes when part B lands and the backstop it tracks is *deleted* (Phase 3), not re-armed.

### Phase 5 — relax §12.1 (now genuinely backend-internal)

- **Crates:** `spec/` (the staged 0373(iii) wording), no compiler change required by the relaxation itself.
- **Work:** land the staged §12.1 relaxation (backend-chooses-representation). Optionally, backend may *then* exploit it (unboxed small ADTs, `char`/`u16`/`f32`) — but that exploitation is future capability, not part of this arc's correctness.
- **Risk:** LOW (spec text) for the relaxation; any representation-exploitation is separately scoped.
- **Size:** SMALL (the relaxation) + open-ended (exploitation, out of arc).

### Phase 5 — relax §12.1 (now genuinely backend-internal)

- **Crates:** `spec/` (the staged 0373(iii) wording), no compiler change required by the relaxation itself.
- **Work:** land the staged §12.1 relaxation (backend-chooses-representation). Optionally, backend may *then* exploit it (unboxed small ADTs, `char`/`u16`/`f32`) — but that exploitation is future capability, not part of this arc's correctness.
- **Risk:** LOW (spec text) for the relaxation; any representation-exploitation is separately scoped.
- **Size:** SMALL (the relaxation) + open-ended (exploitation, out of arc).

### Sequencing + gating

**RE-SEQUENCED (/arch, 2026-06-16, user-directed): Phase 1 → 2 → 4 → 3 → 5.** Phase 4 (mono-completeness + generic-body elimination) runs *before* Phase 3 (backend consumes `MonoExpr`), because Phase 3 requires every instance to have a `MonoExpr`, which only Phase-4 part A delivers (Phase 2b's `allowed_vars` carve-out admits instances with no `MonoExpr`). Within Phase 4: part A (mono-completeness — suppress the spurious partial-instance mint; delete the carve-out) strictly before part B (generic-body elimination — exclude `Polymorphic` from both codegen-target filters), because B removes the template fallback that an incomplete instance would otherwise rely on. Phase 1 + 2a + 2b LANDED. Phase 1 is independent. The interim S84 guards (§3.11.1 check + deferred 0381 backstop) hold the soundness line across the gap until Phase 3 retires them — they are why the arc can stage without re-opening the SIGSEGV.

---

## 5. Principle consistency

- **Principle 18** (enforce invariants structurally): this arc is its fullest expression — the boundary *type* forecloses the violation, replacing four behavioural guards with one structural property + one relocated choke point (the conversion). The worked-example list in Principle 18 gains "concrete-only boundary type" as a structural mechanism alongside dep-bans / sealed traits / sum-type-collapse. *(Add at Phase 2 close, per the mid-sprint-principle-stability rule — not now.)*
- **Principle 20** (model a correlated invariant by representation): the slot-gate work made *callability* structural; this arc makes *value-representation* structural. Same axiom, the boundary type is the representation that encodes "this value's machine shape is decidable." Consistent — Principle 20's cross-ref list gains this doc at Phase 2 close.
- **Principle 7** (single source of truth): the mono enumeration is extended, never forked (§2.3); the conversion is the single home of the concreteness verdict, retiring the scattered `contains_var`/`is_representation_undetermined`/`classify`-panic copies.
- **Principle 6** (complexity budget): the arc *removes* net complexity (four guards → one type + one conversion). The `MonoExpr`-vs-field decision (§2.4) is the one place to spend carefully — the parallel-AST form is the strongest but the most surface; settle against the budget at Phase 2.
