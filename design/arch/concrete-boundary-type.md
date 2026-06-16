# Concrete-only codegen-boundary type + generic-body-codegen elimination

**Status: TARGET ARCHITECTURE (user-ratified direction 2026-06-16) — DESIGN ONLY; a dedicated arc, NOT the remainder of S84.** Phase 1 (`ConcreteType` + the fallible conversion) is a small foundational scaffold landable in `cranelisp-types`; Phases 2–5 are a multi-sprint migration. This document is the standing reference for that arc.

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

- **A slot-less `Polymorphic` def is NEVER emitted to codegen.** It has no `ConcreteType`-annotated body to hand over. It is a *template only*, consumed by monomorphisation, never by the backend. `defined_symbols()` stops yielding `Polymorphic` entries as codegen targets (it yields them as *mono sources* to a different consumer — the mono pass — but not to `compile_to_module`). This is the structural realisation of FIXME 0381's proposed resolution ("a slot-less `Polymorphic` generic def's body is NOT emitted to codegen at all").
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

Two options; **Option B is the target**, Option A is a possible Phase-2 transitional shape.

- **Option A — replace `inferred_type`.** Change `Expr.inferred_type: Option<Box<Type>>` to `Option<Box<ConcreteType>>`. Clean end-state, but typecheck *produces* `Type` (with `Var`s) during inference and only resolves to concrete late — so the same AST node would need a `Type` annotation during inference and a `ConcreteType` annotation post-mono. One field cannot be both. Rejected as the single field.
- **Option B — a distinct post-mono codegen view (TARGET).** Keep `inferred_type: Option<Box<Type>>` as the **inference-stage** annotation (typecheck's working annotation, may carry `Var`). Add a **codegen-stage** annotation `codegen_type: Option<Box<ConcreteType>>` that monomorphisation populates *only* on the AST nodes of concrete instances. The backend reads `codegen_type` exclusively; it never reads `inferred_type`. **A node with `codegen_type == None` is never reached by `compile_to_module`** (it belongs to a template body that is not emitted). The `MonoDefn`/`Defn` produced by the mono pass carries `codegen_type`-annotated nodes by construction.

  This makes the boundary structural at the *node* level: `compile_to_module` matches `codegen_type` and the type is `ConcreteType` — there is no `Type::Var` to encounter because there is no `Type` field on the path it reads. The slot-gate + mono guarantee `codegen_type` is `Some` for every node `compile_to_module` reaches (a `None` would be a located compiler-bug `expect`, the relocated single backstop — replacing the four guards).

  *Refinement (Phase decision):* rather than a parallel `Option` field on all 16 `Expr` variants (a wide, error-prone change), `MonoDefn` may wrap a **separate codegen-AST type** whose nodes carry `ConcreteType` non-optionally (`MonoExpr` mirroring `Expr` with `ty: ConcreteType` instead of `inferred_type: Option<Box<Type>>`). This is the strongest structural form — codegen literally cannot express an un-annotated or non-concrete node — but is the largest migration (a parallel AST). `/design`(typecheck) + `/design`(backend) settle Option-B-field vs MonoExpr-type at Phase 2 against the migration budget. The *architectural commitment* is: **the backend consumes a type that has no `Var`, on an AST view that has no inference-stage `Type` on its read path.**

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

- **Crates:** `cranelisp-typecheck` (mono pass annotates), `cranelisp-types` (the `codegen_type` field or `MonoExpr` type — §2.4).
- **Work:** the §2.4 decision (parallel `Option<Box<ConcreteType>>` field vs `MonoExpr`); mono's per-instance re-check populates it; `from_type` is the choke at the point a node's concrete type is assigned (failure = the ambiguity/could-not-mono error, surfaced as the existing `CheckError`/`TypeError`).
- **Public-API / BC / cache:** `cranelisp-types` AST shape changes → `public-api.txt` move **and a `CACHE_SCHEMA_VERSION` bump** (the AST is part of the cached `.meta.json` serde shape). BC §2 amended (mono produces the concrete-boundary annotation). This is the first behaviour-affecting phase.
- **Risk:** MEDIUM-HIGH — the AST-annotation migration touches the widest surface; the mono-coverage completeness (every reachable node gets a concrete annotation) is the correctness obligation, guarded by the existing 0344/0349 fold canary + the S84 Tier-2 e2e guards. The `from_type`-failure-as-error path must produce the same diagnostics the §3.11.1 check produces today (no regression in rejection coverage).
- **Size:** LARGE — a sprint spine on its own.

### Phase 3 — backend consumes `ConcreteType`; `classify` loses the `Var` arm

- **Crates:** `cranelisp-backend` (the ~13 files reading `inferred_type`), `cranelisp-runtime`/`-intrinsics` only if a signature crosses.
- **Work:** `HeapCategory::classify` takes `&ConcreteType`; the `Var`/`TyConApp` arms and the `is_representation_undetermined()` gate are deleted (inexpressible). `compile_to_module` reads `codegen_type`/`MonoExpr`. A `None`/missing codegen annotation is a single relocated `expect` (the one backstop replacing the four). Retire the §3.11.1 standalone scan + `is_representation_undetermined()` (now subsumed).
- **Public-API / BC / cache:** `classify` is backend-internal (no baseline move). BC §3 invariant 9 rewritten — the belt-and-braces two-predicate framing collapses to "the boundary type has no `Var`; `classify` is total." `is_representation_undetermined()` retired from `cranelisp-types` (`public-api.txt` removal — a *removal* line, the only non-additive baseline move in the arc).
- **Risk:** MEDIUM — the breadth of `inferred_type` read sites in backend; each must move to the concrete view. The `#[should_panic]` backstop tests retire.
- **Size:** MEDIUM-LARGE.

### Phase 4 — eliminate generic-body codegen; prelude generics become on-demand mono roots

- **Crates:** `cranelisp-typecheck` (`defined_symbols()` stops yielding `Polymorphic` as a codegen target; symmetric with `Constrained`), `src`/int (prelude loading no longer pre-compiles generic bodies; mono-on-demand per use).
- **Work:** the §2.2/§2.5 change — `Polymorphic` (and confirm `Constrained`) bodies are mono *sources* only, never `compile_to_module` targets. Prelude generic bodies codegen lazily per reaching instantiation. **This is the phase that retires FIXME 0381's 317× root** — and the phase whose absence is *why* the backstop is deferred today.
- **Public-API / BC / cache:** BC §2 + §7 amended (the `Polymorphic`/`Constrained` codegen-target symmetry; prelude-as-mono-source). Possible session-init/prelude-loading behaviour change (int) — assess e2e. No new boundary type.
- **Risk:** HIGH — this is the phase that historically fired 317×; it changes *which bodies are emitted* across the whole prelude/stdlib. Heavy e2e reliance (every prelude-using test is a witness). FIXME 0381 is the standing record of the failure mode.
- **Size:** LARGE.

### Phase 5 — relax §12.1 (now genuinely backend-internal)

- **Crates:** `spec/` (the staged 0373(iii) wording), no compiler change required by the relaxation itself.
- **Work:** land the staged §12.1 relaxation (backend-chooses-representation). Optionally, backend may *then* exploit it (unboxed small ADTs, `char`/`u16`/`f32`) — but that exploitation is future capability, not part of this arc's correctness.
- **Risk:** LOW (spec text) for the relaxation; any representation-exploitation is separately scoped.
- **Size:** SMALL (the relaxation) + open-ended (exploitation, out of arc).

### Sequencing + gating

Phase 1 → 2 → 3 → 4 → 5, strictly ordered (each depends on the prior). Phase 1 is independent and landable now. The interim S84 guards (§3.11.1 check + deferred 0381 backstop) hold the soundness line across the gap between Phase 1 and Phase 3 — they are the reason the arc can be deferred without re-opening the SIGSEGV.

---

## 5. Principle consistency

- **Principle 18** (enforce invariants structurally): this arc is its fullest expression — the boundary *type* forecloses the violation, replacing four behavioural guards with one structural property + one relocated choke point (the conversion). The worked-example list in Principle 18 gains "concrete-only boundary type" as a structural mechanism alongside dep-bans / sealed traits / sum-type-collapse. *(Add at Phase 2 close, per the mid-sprint-principle-stability rule — not now.)*
- **Principle 20** (model a correlated invariant by representation): the slot-gate work made *callability* structural; this arc makes *value-representation* structural. Same axiom, the boundary type is the representation that encodes "this value's machine shape is decidable." Consistent — Principle 20's cross-ref list gains this doc at Phase 2 close.
- **Principle 7** (single source of truth): the mono enumeration is extended, never forked (§2.3); the conversion is the single home of the concreteness verdict, retiring the scattered `contains_var`/`is_representation_undetermined`/`classify`-panic copies.
- **Principle 6** (complexity budget): the arc *removes* net complexity (four guards → one type + one conversion). The `MonoExpr`-vs-field decision (§2.4) is the one place to spend carefully — the parallel-AST form is the strongest but the most surface; settle against the budget at Phase 2.
