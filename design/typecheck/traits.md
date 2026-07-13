# Trait System

Solution design for the Cranelisp trait system as implemented in `cranelisp-typecheck`. Covers trait declarations, implementations, default methods, constrained polymorphism, monomorphisation, method resolution, and core-trait provisioning.

This document is the authoritative design reference for the trait subsystem. It describes the data structures, algorithms, and invariants that govern how traits interact with the rest of the typechecker and backend. It is subordinate to `design/typecheck/typecheck.md` (master) and cites `design/typecheck/monomorphisation.md` for the monomorphisation engine detail.

> **Model note (S87+; this doc rewritten S109 against the as-built).** Traits are **symbol-table-resident**, not held in checker-side registries. The former `TraitRegistry` / `ImplRegistry` / `TypeDefRegistry` global caches on a `TypeChecker` struct were **eliminated** — there is no `TypeChecker` struct. The checker is `TypeCheckEnv<'a, C, L>` (borrowed shared state) + `CheckState` (per-check transient state); all trait declarations, impls, and the method→trait reverse index live as `ModuleEntry` entries in the per-module `SymbolTable`s reached through Principle-17 chain-following resolution. The `TraitRegistry`/`ImplRegistry` names survive only as rustdoc tombstones (`checker.rs:17–18`, `traits/mod.rs:9`). The **ring axis was retired as a scheduling/framing axis (Sprint 64)** — pre-S64 "Ring N" annotations elsewhere are historical; this doc uses sprint-only framing.

## 1. Where trait state lives — symbol-table-resident model

### 1.1 The two checker types (no registry fields)

```rust
// checker.rs — borrowed shared state; NO registry fields.
pub struct TypeCheckEnv<'a, C = (), L = ()>
where C: CodeStore, L: LinkerStore {
    next_id: &'a AtomicU32,                              // fresh type-var IDs
    modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>, // per-module tables
    staging: Option<TypeCheckStaging<'a, 'a, C, L>>,    // cluster-mode write redirect
    module_aliases: &'a ModuleAliases,                  // §8.6.6 alias table
    prelude_fallback: &'a PreludeFallback,              // §8.6.1 prelude-fallback bits
}

// checker.rs — per-check transient state.
pub struct CheckState {
    // ... subst, env (scope stack), current_module, side-maps (method_resolutions,
    //     expr_types, user_fn_refs, pending_auto_curry) ...
    active_constraints: ActiveConstraints,   // the ONE surviving "registry-like" field
}
```

Trait decls, impls, type defs, and the method→trait index are **not** HashMaps on the checker — they are `ModuleEntry` entries in the `modules` DashMap, keyed per module, resolved by chain-follow (Principle 17: short-name lookup is current-module-only with per-symbol `Import`/`Reexport` chain-follow; no universe scan). This is the structural realisation of "the crate carries no shared session state" (BC §2) — the durable trait facts live in the caller-supplied module tables, and only the transient inference companion (`active_constraints`) rides `CheckState`.

### 1.2 Trait declaration entry — `ModuleEntry::TraitDecl`

```rust
// cranelisp-types::module — module.rs:1049
TraitDecl { info: TraitDeclInfo, visibility: Visibility, docstring: Option<String> }
```

`TraitDeclInfo` (a slimmed payload, S72 Phase B — it no longer embeds the frontend AST node) carries the trait `name`, `type_params`, and `methods` (each a `TraitMethodSig`). `visibility`/`docstring` live on the entry, not duplicated in the payload. One `TraitDecl` entry per declared trait, under the trait-name key in its defining module.

### 1.3 Trait impl entry — `ModuleEntry::TraitImpl`

```rust
// cranelisp-types::module — module.rs:1110
TraitImpl {
    trait_name: FQTraitName,   // fully-qualified trait identity
    impl_type: FQTypeName,     // fully-qualified target-type identity
    methods: Vec<Symbol>,      // the method names this impl provides
    visibility: Visibility,    // always Public (see below)
}
```

- **Key.** The impl entry is stored under the **synthetic key `impl${FQTypeName}${FQTraitName}`** (minted at `impl_check.rs:149–152`). This is an index/metadata entry — it has no `callees`, no scheme; it records *that* `(Trait, Type)` has an impl, so dispatch can answer "is there an impl?" without a universe scan.
- **Placement — Decision 45 / Pattern B.** The impl entry is written to the **trait's defining module's** table, NOT the writer's module (`impl_check.rs:125–161`, via `symbol_table_mut_in(&trait_home)`). The write target is resolved by chain-following the trait reference from the writer's module to the trait's home. This is what makes cross-module impl discovery a single-module scan: to find all impls of a trait, dispatch chain-follows to the trait's home and scans *that one module's* `TraitImpl` entries (`has_impl_in_module`, `get_implementing_types_in_module`).
- **Visibility.** `TraitImpl` is always constructed `Public` (spec §5.11.1; the lossless-mark convention, `module.rs:1120`) — an impl is globally visible for coherence.

### 1.4 The method→trait reverse index — `trait_origin` on the method `Def`

The old `method_to_trait: HashMap<Symbol, TraitName>` is gone. Each trait method is registered as an ordinary constrained `ModuleEntry::Def`, and that `Def` carries:

```rust
// cranelisp-types::module — module.rs:760
trait_origin: Option<FQTraitName>,   // "Replaces the method_to_trait reverse index"
```

So "which trait owns method `+`?" is answered by **resolving the name `+` to its `Def` and reading `trait_origin`** — a chain-follow, prelude-fallback-aware lookup, not a map probe. Three read-throughs (`checker.rs`):
- `method_to_trait(method_name)` (`:2088`) — defaults the root to the `user` module.
- `method_to_trait_in_module(module_path, method_name)` (`:2094`) — resolves an entry in a named module and reads `Def { trait_origin: Some(fqtn), .. } => fqtn.name`.
- `method_to_trait_with_state(state, method_name)` (`:2113`) — roots at `state.current_module`, chain-follows via `resolve_terminal_entry_scoped`, prelude-fallback aware. **This is the dispatch-path entry** (§7).

Consequence: method-name→trait resolution obeys the same module-locality and prelude-fallback discipline as every other name (Principle 17 + the `scope_resolve` chokepoint) — there is no privileged global method table.

### 1.5 `ActiveConstraints` — the transient inference companion

```rust
// traits/registry.rs:16
pub struct ActiveConstraints { constraints: HashMap<TypeId, Vec<FQTraitName>> }
```

Held on `CheckState.active_constraints` (`checker.rs:145`). Tracks trait constraints on type variables **during** inference: populated when a constrained scheme is instantiated (`instantiate_constrained`, `monomorphise.rs:22` → `active_constraints.add(fresh_var, trait)`), consulted during `generalize` (`checker.rs:1900`) to propagate constraints onto the generalized scheme. Idempotent adds (duplicate `(TypeId, FQTraitName)` ignored). Snapshotted/restored across passes (`form.rs:284`, `program.rs:2426`); reset only by the test-only `clear_transient_state`. It accumulates across a compilation unit and is NOT cleared between top-level forms — `generalize` resolves constraints through the substitution so a constraint recorded on one variable correctly attaches to the variable it was unified with (§6 Invariant 7).

### 1.6 The `traits/` module layout (S87 Wave-5e decomposition)

The former monolithic `traits.rs` is five cohesive production submodules under a hub (`design/typecheck/s87-traits-decomposition.md` §1). All items are crate-private (`lib.rs` declares `mod traits;` — never `pub`; `public-api.txt` byte-identical):

| Submodule | LOC | Concern |
|---|--:|---|
| `traits/mod.rs` | ~89 | hub: submodule decls, crate-internal re-exports, `mangle_trait_method` |
| `traits/registry.rs` | ~364 | **write-side**: `TraitDecl` → symbol-table state; `ActiveConstraints`; `register_trait_decl`, `register_hkt_trait`, `register_trait_method`, `build_method_type` |
| `traits/impl_check.rs` | ~889 | impl recording (`register_trait_impl`) + method-body checking (`check_impl_method`, `check_impl_method_with_sig`, default generation) |
| `traits/dispatch.rs` | ~452 | **read-side**: `try_resolve_trait_method`, `primitive_for_trait_method`, HKT/return-type dispatch helpers |
| `traits/monomorphise.rs` | ~1107 | the monomorphisation engine + mangling primitives (`monomorphise_call`, `recheck_body_for_mono`, `build_mangled_name`, `concrete_type_name`) |
| `traits/type_resolve.rs` | ~456 | `TypeExpr → Type` resolution free functions |

`traits/test_helpers.rs` (~324, test-only) + a sibling `{mod}/tests.rs` per production submodule carry the test surface.

## 2. Trait Declaration (`deftrait`)

### Surface syntax

```clojure
(deftrait (TraitName a)
  (method1 [a a] a)                           ;; required method
  (method2 [x y] Bool (not (method1 x y))))   ;; default method
```

### Registration pipeline

`deftrait` registration runs in two seams — the **§8.6.4 name-freedom gate** (in `program.rs`) then the **write** (in `registry.rs`):

1. **§8.6.4 seam (name-freedom), at the `check_form_register` `TraitDecl` arm (`program.rs:932–937`).** Before any write, `reject_def_over_binding(state, name, span)` is called for the trait **name** AND **each method name** (the loop at `:935`). A definition over any name already in scope — explicit import, export, or prelude-provided — is a §8.6.4 compile-time conflict, never a shadow (`home == current_module` ⇒ the module's own prior def ⇒ redefinition allowed; otherwise reject). This is the single definition-freedom chokepoint (`crates/cranelisp-typecheck/CLAUDE.md §"Bare-name resolution"`).

2. **`register_trait_decl(state, decl)` (`registry.rs:79`)** then performs the write:
   - **Idempotency probe (the ONE legitimate fallback-less probe, `registry.rs:84–115`).** A **raw current-module** `probe_module_entry_owned` (no chain-follow, no prelude hop) answering same-module IDENTITY — NOT name-freedom (that already ran at step 1). The cluster orchestrator retries a module's typecheck from the top with no resume index (loading a declared submodule), re-submitting the parent's structural decls while prior results are committed to live. A re-submission of the *same* declaration (`trait_decl_matches`) is a no-op (`Ok(())`, idempotent, mirroring `deftype`, S86 D3); a genuinely-different same-module redeclaration is rejected (`"trait … already defined"`, spec §7.1).
   - **Fresh type-var allocation.** One `fresh_var_id()` allocates the trait's type parameter (e.g. `a`); all methods share it — they are polymorphic over the same `a`.
   - **Method registration** (`register_trait_method`, `registry.rs:262`): builds each method's function type via `build_method_type`, wraps it in a `Scheme { vars: [type_var_id], constraints: { type_var_id: [trait_name] } }`, inserts the method as a constrained `ModuleEntry::Def` carrying `trait_origin: Some(fq_trait)` (§1.4), and — for HKT traits — routes through `register_hkt_trait` (`registry.rs:168`).
   - **Trait entry.** Inserts the `ModuleEntry::TraitDecl { info, visibility, docstring }` under the trait-name key (`registry.rs:150`).

### Type-variable allocation in method signatures

`build_method_type` resolves `TypeExpr` values against a `var_map`:

- Trait type parameters (e.g. `a`) → `Type::Var(type_var_id)` (the shared variable).
- `TypeExpr::Named("Bool")` → `Type::Bool` (`Type::from_name`).
- `TypeExpr::SelfType` → `Type::Var(type_var_id)`.
- A `TypeExpr::TypeVar` that does NOT match a trait type parameter gets a fresh variable (handles method-local extra type params).

**Example** — `(deftrait (Num a) (+ [a a] a))` gives `+`:

```
Scheme { vars: [42], constraints: { 42: ["Num"] }, ty: Fn([Var(42), Var(42)], Var(42)) }
```

`+` is polymorphic over one variable, constrained to types implementing `Num`.

## 3. Trait Implementation (`impl`)

### Surface syntax

```clojure
(impl Num Int
  (+ [x y] (add-i64 x y))
  (- [x y] (sub-i64 x y))
  (* [x y] (mul-i64 x y))
  (/ [x y] (div-i64 x y)))
```

### Registration pipeline — `register_trait_impl(state, impl_) -> Result<Vec<Defn>>` (`impl_check.rs:18`)

1. **Trait lookup + target resolution.** Chain-follow the trait reference to its `TraitDecl` (error if unknown); resolve the impl target to its `FQTypeName` (`concrete_type_for_impl_target`, ADT-arity-checked).
2. **Required-method check** (`check_impl_methods_present`, `impl_check.rs:196`): every method without a `default_body` MUST be provided; defaulted methods may be omitted.
3. **Field-accessor collision check (spec §7.3.1, FIXME 0365).** An impl method whose name equals an existing field-accessor name of the target type is rejected at impl time (see `design/typecheck/fixme-0365-field-accessor-dotted.md` §2 — the check runs alongside `check_impl_methods_present`, before the impl entry is written).
4. **Default-method generation** (`generate_default_methods`): for each omitted defaulted method, mint a mangled `Defn` (§3.1) whose body is built by `build_default_body`.
5. **Impl entry write.** Insert `ModuleEntry::TraitImpl { trait_name, impl_type, methods, visibility: Public }` under `impl${FQTypeName}${FQTraitName}` in the **trait's defining module** (Decision 45, §1.3). There is no explicit dedup guard — a re-run re-`insert`s under the synthetic key, overwriting idempotently.
6. **Method-body type-checking** (`check_impl_method` / `check_impl_method_with_sig`): resolve the concrete `Self` type, seed a `var_map` `{ trait_type_param → concrete_self }`, resolve each signature param/return through `resolve_trait_type_expr`, and check the body against those concrete types (`check_defn_body_with_types`). The mangled-name `Def` writeback (with its `codegen_view`, `callees`, `ast`) runs through the shared `finalize_impl_method_writeback` tail (the single/HKT paths converge there).
7. **Return.** The provided + default `Defn` nodes are returned to the caller for codegen (core-trait impls' returns are discarded — §5).

### Post-inference

`resolve_deferred_trait_calls` runs after body checking to resolve trait-method calls in the impl body that couldn't resolve eagerly (§7).

### 3.1 Mangling convention — `mangle_trait_method`

Trait-method implementations use:

```
{TraitName}.{method_name}${home}/{TargetType}
```

Examples: `Num.+$primitives/Int`, `Eq.=$primitives/String`, `Eq.!=$primitives/Int` (a default), `Describe.describe$a/Widget` (a user impl on a module-`a` ADT).

**FQ `$Type` suffix (S102 — lossy-head cure).** The `$Type` suffix carries the **fully-qualified, home-qualified** type head (`module/Type`), not the bare head. Spec §3.8.4 makes two same-bare-named types from different modules (`a/Widget` ≠ `b/Widget`) DISTINCT; a bare-head grammar collapsed both onto one linker symbol, silently wrong-dispatching every `(describe x)`. Home-qualifying the suffix makes the symbol collision-free by construction (Principle 20) — the same lossy-head class 0519 cured for the mono-instance mangler, extended to the trait-method grain.

**One mint, both sides — the lock-step invariant (name-path == definition-path).** The dispatch site (`dispatch.rs::try_resolve_trait_method`) and the definition/writeback sites (`impl_check.rs` — `check_impl_method_with_sig`, `check_hkt_impl_method`, `generate_default_methods`) mint through the ONE shared `mangle_trait_method(trait, method, &FQTypeName)` helper (`traits/mod.rs:74`) against the SAME canonical `FQTypeName`, or the call's linker symbol would not match the impl method's definition symbol. The two sides derive the `FQTypeName` differently but land on the same value:
- **Definition side** — `resolve_type` on the impl target, resolved ONCE in `register_trait_impl` and threaded to all writeback paths (Principle 7).
- **Dispatch side** — `fq_type_for_dispatch_mangle(&resolved_arg, &fallback)` takes the FQ head from the resolved argument's OWN type (an ADT carries its home). It does NOT re-resolve the bare head in the caller's module — that re-resolution is the home-erasing bug.

**Grain: receiver HEAD only.** The suffix carries the receiver type's FQ head; ADT type-args are not recursed (`Vec Int` and `Vec String` both yield head `primitives/Vec`). This matches the impl-registration grain (impl target head), so both sides agree; arg-distinguishing the grain would require a coordinated impl-registration change and is out of scope.

*(The `primitive_for_trait_method` short-circuit means operator impls on primitive types — `Num.+$…/Int`, `Display.show$…/Int` — never actually mint a trait-method symbol; they collapse to `ResolvedCall::BuiltinFn` and inline. The mangle path is exercised by user traits and user impls on ADTs.)*

## 4. Default Methods

Default methods are trait methods with a body that may be omitted from `impl` blocks; the trait decl supplies the body and impls inherit it unless they override.

### Declaration

In `TraitMethodSig`, `default_body: Option<Sexp>` signals a default. For the core traits, default bodies are flagged with a placeholder (`Sexp::Symbol("default", …)`) and `build_default_body` hard-codes the AST:

| Method | Body |
|--------|------|
| `Eq.!=` | `(not (= x y))` |
| `Ord.>` | `(< y x)` |
| `Ord.<=` | `(not (< y x))` |
| `Ord.>=` | `(not (< x y))` |

> **Follow-up (was "Ring 3"):** user-defined traits with parsed-source default bodies would replace `build_default_body`'s hard-coding with a frontend-parse of the `default_body` Sexp. The current hard-coded approach covers only the four builtin defaults; parsed defaults are unscheduled.

### Generation + override

When `register_trait_impl` finds a defaulted method the impl omits, it mints the mangled name (§3.1), builds the body via `build_default_body`, and includes the `Defn` in the returned vector — compiled by the backend like any other function. If the impl *provides* a defaulted method, `generate_default_methods` skips it (the provided body wins). Default `Defn`s ride `CheckResult.default_method_defns`.

## 5. Core-trait provisioning

The core traits (`Num`, `Eq`, `Ord`, `Display`) and their primitive-type impls are provisioned so `(+ 1 2)` type-checks before any user source. Two facts govern the design:

1. **Same pipeline as user traits (former Decision 17, resolved S9).** Core traits flow through the *same* `register_trait_decl` / `register_trait_impl` code paths as user traits — no special-case registration logic. The provisioning code constructs `TraitDecl` / `TraitImpl` AST structs directly in Rust (the typecheck crate cannot depend on the frontend, so it cannot parse them from `.cl` source — a permanent architectural constraint, not a temporary compromise). Pipeline uniformity does not require parsing from source; it requires the same registration code paths.

2. **Bootstrap ordering + transient-state cleanup.** Provisioning runs before any user source; registering core impls type-checks their method bodies (e.g. `(add-i64 x y) : (Fn [Int Int] Int)`), populating `expr_types` / `method_resolutions` / `subst` at `Span::SYNTHETIC`. A cleanup step wipes those transient maps so synthetic entries do not leak into user-program checking and cause spurious span matches.

> **Provisioning locus — verify at implementation time.** The historical text placed core-trait construction in `register_builtins()`/`builtins.rs`; `design/typecheck/typecheck.md` records that core traits now live in `.cl` files loaded at session start (per `design/arch/CLAUDE.md` Decision 17 retraction note). The two are not contradictory if `builtins.rs` is the *test-fixture* world-builder (`TestFixture` seeds `Num`/`Eq`/`Ord`/`Display` in-crate) while production loads the core-trait `.cl` files through the same `register_trait_decl`/`register_trait_impl` seams. When touching this path, confirm which locus is production vs test — the invariant that matters (and is asserted below) is *same registration code path*, not *which caller constructs the structs*.

### 12 core impl registrations (the primitive coverage)

| Trait | Int | Float | Bool | String |
|-------|-----|-------|------|--------|
| Num | `+` `-` `*` `/` | `+` `-` `*` `/` | — | — |
| Eq | `=` | `=` | `=` | `=` |
| Ord | `<` | `<` | — | — |
| Display | `show` | `show` | `show` | `show` |

Defaults (`!=`, `>`, `<=`, `>=`) auto-generate for all Eq/Ord impls.

## 6. Constrained Polymorphism

A function is *constrained polymorphic* when its generalized scheme has non-empty `constraints` — its body calls trait methods, leaving the concrete type unresolved:

```clojure
(defn add [x y] (+ x y))     ;; add :: forall a:Num. (Fn [a a] a)
```

`a` must implement `Num`. Unlike unconstrained polymorphism (compile once), a constrained function is *monomorphised* per concrete type combination at its call sites (§7).

### Scheme.constraints

```rust
pub struct Scheme { vars: Vec<TypeId>, constraints: HashMap<TypeId, Vec<FQTraitName>>, ty: Type }
```

`constraints` maps quantified var IDs to the traits they must implement. Empty `constraints` ⇒ unconstrained (or monomorphic if `vars` empty too).

### Constraint propagation — three stages

- **Instantiation** — `instantiate_constrained` (`monomorphise.rs:22`) maps old vars to fresh ones and carries constraints to the fresh vars in `active_constraints`.
- **Unification** — during body checking, fresh vars may unify with the function's param vars; the substitution records the binding but does NOT move constraints (they stay on the original fresh var).
- **Generalization** — `generalize(state, ty)` (`checker.rs:1900`) resolves each `active_constraints` entry through `state.subst`: a constraint on `Var(X)` where `subst[X] = Var(Y)` and `Y ∈ scheme.vars` attaches to `Y` in the scheme (dedup per FIXME 0354 Bug A). This is the critical step — the constraint recorded on an instantiation-fresh var correctly reaches the scheme's quantified var it was unified with.

### Detection (in the register/body passes)

- **Eager marking.** After each body is checked, a trial `generalize`; if the trial scheme has constraints, the function is immediately marked constrained (a `ConstrainedFn` stored in its `DefKind::UserFn { fn_state: Constrained(..) }`). Eager because later bodies in the same unit may pin this function's vars through the shared substitution.
- **Final clearing.** After all bodies, re-generalize; if a function's final scheme has no constraints (later call sites pinned all vars), the eager marker is cleared.
- **Re-resolution.** A final `resolve_deferred_trait_calls` pass retries trait calls that were unresolved when first seen.

### ConstrainedFn storage

```rust
pub struct ConstrainedFn { defn: Defn, scheme: Scheme }   // in DefKind::UserFn { fn_state: Constrained(Box<ConstrainedFn>) }
```

`defn` is the original definition (re-checked during monomorphisation); `scheme` is the constrained polymorphic scheme.

## 7. Method Resolution

Resolution happens in `infer_apply` and is refined post-inference by `resolve_deferred_trait_calls`. The result is a `ResolvedCall` in `method_resolutions`, keyed by the `Apply` node's span.

### During inference — `try_resolve_trait_method` (`dispatch.rs:21`)

`try_resolve_trait_method(state, callee_name, arg_types, span) -> Result<Option<ResolvedCall>>`:

1. `method_to_trait_with_state(state, callee_name)` (§1.4) → the owning trait, or bail `Ok(None)`.
2. Select the dispatch argument — `hkt_param_idx_for_method` (default arg 0) or return-type dispatch for nullary-return-poly methods.
3. `concrete_type_name` of the resolved dispatch arg; if still a `Var`, return `None` (defer to mono).
4. `has_impl_with_state(state, &trait_name, &impl_type_name)` — chain-follow to the trait's home and scan its `TraitImpl` entries (Decision 45); error `no impl of trait T for type X` if absent.
5. Primitive short-circuit: `primitive_for_trait_method` hit ⇒ `ResolvedCall::BuiltinFn`.
6. Otherwise mint `ResolvedCall::TraitMethod { trait_name, method_name, impl_type, mangled_name }` via `mangle_trait_method`.

If not a trait method, `infer_apply` falls to `is_primitive` (⇒ `BuiltinFn`) or leaves no entry (regular function call).

### Deferred resolution — `resolve_deferred_trait_calls`

During inference an argument type may still be a `Var` (e.g. `x`/`y` in `(defn add [x y] (+ x y))`), so `concrete_type_name` returns `None` and step 3 defers. After all bodies are checked and the substitution is populated, `resolve_deferred_trait_calls` walks the tree and retries resolution for any trait-method `Apply` with no `method_resolutions` entry, reading argument types from `expr_types` (subst-applied) rather than re-inferring. It runs after each body (eager), after all bodies (re-resolution), and after `check_defn_body_with_types` (impl methods, mono).

### ResolvedCall

```rust
pub enum ResolvedCall {
    TraitMethod { trait_name: TraitName, method_name: Symbol, impl_type: TypeName, mangled_name: JitSymbol },
    SigDispatch { mangled_name: JitSymbol },
    AutoCurry   { target_name: Symbol, applied_count: usize },
    BuiltinFn   { name: Symbol },
}
```

Backend dispatch (`compile_resolved_call`): `TraitMethod` checks `primitive_for_trait_method` first (inline IR / extern call for primitives; direct call to the mangled name for user impls); `SigDispatch` is a direct call to the mangled specialization; `BuiltinFn` emits inline IR; `AutoCurry` builds a closure capturing applied args.

### `primitive_for_trait_method` (Decision 14)

The typechecker emits `ResolvedCall::TraitMethod` for *all* trait-method calls; the backend decides inline-vs-call. `primitive_for_trait_method(trait, method, impl_type) -> Option<&'static str>` (`dispatch.rs:144`) is a static `(Trait, method, Type) → primitive` table (26+ entries across Num/Eq/Ord/Display for Int/Float/Bool/String). `Some(prim)` ⇒ backend inlines / extern-calls; `None` ⇒ user-defined impl compiled as a direct call to the mangled name. Macro-/user-compiled impls never appear in the table, so they take the `None` (direct-call) path — correct, no change needed.

### `concrete_type_name`

`concrete_type_name(ty) -> Option<TypeName>`: `Int/Float/Bool/String → Some(name)`, `ADT(name,_) → Some(name)`, `Var(_) → None`, `Fn(_,_) → None`. Returning `None` for `Var` is exactly what triggers deferred resolution.

## 8. Monomorphisation

Full engine design: `design/typecheck/monomorphisation.md`. Locus: the **collection/driver** lives in `program.rs` (Pass 4), the **per-call engine** in `traits/monomorphise.rs`.

### Collection (Pass 4, `program.rs`)

`pass4_monomorphise(state, defns, constrained_fn_names) -> Result<Vec<MonoDefn>>` (`program.rs:3367`):

1. `collect_constrained_calls` (`program.rs:3858`) walks non-constrained bodies for `Apply` nodes whose callee is a known constrained function → `(fn_name, arg_spans, call_span)` triples (plus `collect_imported_constrained_calls` for cross-module callees, and the parametric-call collectors).
2. Resolve argument types from the resolved `expr_types`.
3. Deduplicate on the mangled key `fn_name$Type1+Type2+…` — one `MonoDefn` per unique specialization.
4. `monomorphise_call` per unique specialization.
5. Record `ResolvedCall::SigDispatch { mangled_name }` per call site.

### The engine — `monomorphise_call` (`traits/monomorphise.rs:83`)

`monomorphise_call(state, fn_name, arg_types, call_span, home: Option<&ModuleFullPath>) -> Result<Option<MonoDefn>>` is a 7-phase sequential driver (phase boundaries + state-channel invariants: `s87-traits-decomposition.md` §2). Sketch: look up the `ConstrainedFn` (module `home` for imported callees); instantiate + unify params to concrete; verify each constraint has an impl (rooted in `home`); pin the call-site return; re-check the body with concrete types under the `home` module switch (`recheck_body_for_mono`), harvesting per-mono resolutions/expr-types; record self-recursion dispatch; build the annotated mono `Defn` and its concrete-boundary codegen view (`MonoExpr::from_expr` — the §3.11.1 ambiguity error on a non-concrete body); register the mono entry.

**Cross-module scoping (load-bearing).** The `home` (defining) module threads into `get_constrained_fn`, `recheck_body_for_mono`, `resolve_inner_constrained_calls`, and `verify_constraints`. Three facts, any wrong ⇒ spurious `no impl of trait T for type X`: (1) body re-check switches `state.current_module` to `home`; (2) constraint verification resolves through the instantiation `var_mapping`, not raw scheme var-ids (cross-module the raw ids may collide with a caller var); (3) impl lookup for verification roots in `home` too. Full walkthrough: `monomorphisation.md` §3.7.

### `MonoDefn` — the codegen-view carrier (shape change vs the retired model)

```rust
// cranelisp-types::check — check.rs:156
pub struct MonoDefn { pub defn: Defn }
```

> **Delta from the old design.** The pre-S84 `MonoDefn` carried its own `resolutions: MethodResolutions` + `expr_types: HashMap<Span, Type>` side maps. Those were **dropped**: a minted mono instance is registered as an ordinary concrete `ModuleEntry::Def` in the **caller's** module (its own GOT slot), and its per-specialization body view rides the entry's **`codegen_view: Option<MonoDefnVariant>`** (the concrete-boundary `MonoExpr` body, `crates/cranelisp-typecheck/CLAUDE.md §"Concrete-boundary codegen_view"`), not a side `Vec`. The backend's existing concrete-mono codegen path wires it — no backend special-case. `MonoDefnVariant` (the codegen-view type, `mono_expr.rs:477`) is distinct from `MonoDefn`.

### REPL path

The REPL monomorphises on demand: scan the symbol table for constrained-fn names, `collect_constrained_calls` on the expression, resolve arg types from `expr_types` (subst-applied), `monomorphise_call` per site. Runs for both expression and defn REPL inputs.

## 9. Multi-Signature Functions

### Surface syntax + AST

```clojure
(defn map ([f :Vec v] (vec-map f v)) ([f :List l] (list-map f l)) ([f :Seq s] (seq-map f s)))
```

`TopLevel::DefnMulti { name, docstring, variants: Vec<DefnVariant>, visibility, span }` — each `DefnVariant` is essentially a standalone function definition.

### Dispatch + mangling

Multi-sig dispatch is resolved at type-check time by matching concrete argument types against variant param-type annotations; each call site produces `ResolvedCall::SigDispatch { mangled_name }`. Variants use the same `$Type1+Type2+…` mangling as monomorphisation (e.g. `map$Vec+Fn`). Registration is `register_mangled_variants` / `register_overloaded_base` / `resolve_pending_overloads` (`program.rs`). See `design/typecheck/signature-match.md` for the match-predicate detail.

### Known interaction limit

Multi-sig + constrained polymorphism are not yet combined — a multi-sig variant that calls trait methods is not auto-detected as constrained.

## 10. Invariants

These must always hold; violations are implementation bugs.

### Storage + registration

1. **Method-name uniqueness within a scope.** Two visible traits declaring the same method name collide at the §8.6.4 seam (the method-name loop, `program.rs:935`) — dispatch never sees an ambiguous `trait_origin`.
2. **Idempotent re-registration.** `register_trait_decl`'s same-module identity probe (`registry.rs:84`) is fallback-less and answers IDENTITY only; name-freedom is decided upstream at the §8.6.4 seam. A same-decl re-submission is a no-op; a different same-module redecl is rejected.
3. **Impl completeness.** Every impl provides all non-defaulted methods (`check_impl_methods_present`).
4. **Impl type-correctness.** Every impl method body type-checks against the trait method signature with `Self` substituted for the concrete target.
5. **Decision-45 placement.** A `TraitImpl` entry lives in the **trait's defining module** under `impl${FQType}${FQTrait}`; impl discovery chain-follows to that module and scans it — no universe scan.
6. **`trait_origin` consistency.** If method `m` resolves to a `Def { trait_origin: Some(T) }`, then `T`'s `TraitDecl` exists and declares a method named `m`.

### Constraints

7. **Constraint resolution.** After generalization, every `Scheme.constraints` key is in the scheme's `vars`.
8. **Active-constraints accumulation.** `active_constraints` is not cleared between top-level forms within a `check` unit — later generalizations may need earlier constraints.
9. **Substitution resolution.** `generalize` resolves constraints through `state.subst` (a constraint on `Var(X)` with `subst[X]=Var(Y)` attaches to `Y`).

### Monomorphisation

10. **Constrained functions not compiled directly.** The backend skips any `Defn` in `CheckResult.constrained_fn_names`; only `MonoDefn` specializations compile.
11. **Per-mono isolation via the entry.** Each mono instance's body view rides its own registered entry's `codegen_view` (§8), not a program-wide map.
12. **Deduplication.** At most one `MonoDefn` per unique `(fn_name, concrete_arg_types)`; multiple call sites share via `SigDispatch`.
13. **Mangle lock-step.** Dispatch and definition mint through the ONE `mangle_trait_method` against the same `FQTypeName` (§3.1) — else the call symbol misses the definition symbol.

### Resolution

14. **Span-keyed resolutions.** `method_resolutions` is keyed by `Apply` span; each span → exactly one `ResolvedCall`; a missing span ⇒ regular function call.
15. **Deferred completeness.** After `resolve_deferred_trait_calls`, every trait-method call with concrete arg types has a `TraitMethod` entry; calls with still-`Var` types (inside constrained bodies) resolve during mono re-checking.

### Provisioning

16. **Same code path.** Core traits use the same `register_trait_decl` / `register_trait_impl` seams as user traits — no special-case registration logic (§5).
17. **Transient-state cleanup.** After core-impl body checking, the `Span::SYNTHETIC` transient maps (`expr_types`, `method_resolutions`, `subst`) are wiped before user checking.

## 11. Evolution notes (ring axis retired)

The ring axis (which structured earlier trait work) was **retired as a scheduling/framing axis in Sprint 64**; the capabilities below are all landed. Retained here as a capability inventory, not a ring roadmap:

- **Landed:** trait decls + impls (single + HKT); constrained-polymorphism detection + monomorphisation (batch + on-demand REPL); core-trait provisioning through the shared pipeline; deferred method resolution; Eq/Ord default methods; the `primitive_for_trait_method` backend optimization; multi-signature functions (batch + REPL); module-scoped decls/impls with cross-module resolution + monomorphisation.
- **Unscheduled follow-ups:** user-defined default method bodies parsed from `.cl` source (replacing `build_default_body`'s hard-coding); macro-defined trait impls; applied types in trait-method signatures (`resolve_trait_type_expr` currently errors); multi-sig + constrained-polymorphism interaction.

## 12. Cross-references

- `design/typecheck/typecheck.md` — master design (this doc is subordinate).
- `design/typecheck/monomorphisation.md` §3.7 — the monomorphisation engine + cross-module scoping.
- `design/typecheck/signature-match.md` — multi-sig match predicates.
- `design/typecheck/s87-traits-decomposition.md` — the `traits/` module cut + `monomorphise_call` phase boundaries.
- `design/typecheck/fixme-0365-field-accessor-dotted.md` §2 — the impl-time field-accessor collision check (§3 step 3).
- Sources: `crates/cranelisp-typecheck/src/traits/{mod,registry,impl_check,dispatch,monomorphise,type_resolve}.rs`; `checker.rs` (`TypeCheckEnv`, `CheckState`, `method_to_trait_*`, `has_impl_*`, `generalize`); `program.rs` (§8.6.4 seam arms, `pass4_monomorphise`); `cranelisp-types::module` (`ModuleEntry::TraitDecl`/`TraitImpl`, `Def.trait_origin`); `cranelisp-types::check` (`Scheme`, `ConstrainedFn`, `MonoDefn`).
