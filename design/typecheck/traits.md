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

### Occurrence-rule enforcement (§7.1.1, S115 — FIXME 0709)

**Status:** DESIGN (S115 Phase 3, `/design`(typecheck)). Closes the F-D2
`silent-accept`/`check-gate-leak` corner: `(deftrait Zeroable (zed [] Int))` —
empty params, CONCRETE `Int` return, no `self` — is today accepted silently, and
the downstream `(zed)` call leaks past the typecheck gate to a raw
`codegen error … undefined function: zed`
(`tests/nondispatchable_trait_method_0709.rs`, retargeted `/testing`).

**The rule (spec/07-traits.md §7.1, line 79 — spec-settled, no user question).**
Each required method signature of a CONVENTIONAL (bare-head, kind-`*`) trait MUST
contain **at least one occurrence of the implementing type** — in parameter OR
return position — **except higher-kinded trait methods (§7.2)**. An occurrence is:

- a **bare parameter** (`[x …]` — an unannotated param defaults to the
  implementing type, §7.1 "Parameters"),
- a **`:self`-annotated parameter**, or
- **`self` in the return type** (a bare `type_expr` return of `self`; `(zed [] self)`).

A method mentioning the implementing type **nowhere** "has nothing to dispatch on
and MUST be rejected **for 'no occurrence of the implementing type to dispatch
on.'**" The diagnostic MUST carry that reason substring
(`"no occurrence of the implementing type"` — the test's assertion). It is a
**declaration-time** reject — the occurrence rule is a structural property of the
method signature, decidable when the trait is declared (Principle 18 — enforce
invariants structurally, at the seam where the malformed form is representable).

**Boundary — the reject must NOT over-reach (the GREEN control).**
`(zed [] self)` (empty params, `self` in return) SATISFIES the rule → accepted at
declaration; its resolution is at USE (§3.3.3 ascription `:Int (zed)` selects the
impl, or the §3.11 ambiguity error for an unresolved use). This is the settled
**declaration-vs-use** split: a WELL-FORMED method (with an occurrence) is
silently accepted at declaration and its dispatch/no-impl enforcement is at USE
(§7.11.2, §3.11); only the MALFORMED no-occurrence form is a declaration reject.
`(size [x] Int)` (bare param `x` = implementing type) SATISFIES — a concrete
return is fine when a parameter carries the occurrence. Do NOT reject on "concrete
return" alone; reject only on the *conjunction* no-param-occurrence ∧
no-self-return.

**Distinct from the §7.2.3 HK kind-check.** Rejecting a primitive as an HK impl
target is *"not a type constructor"* (`traits/impl_check.rs:225`, the only
§7.1.1-adjacent text today); a no-occurrence method is *"nothing to dispatch on."*
The diagnostic MUST name the correct reason — a no-occurrence method MUST NOT be
reported as an "HKT-on-primitive" error (§7.1 line 79). The parenthesized-head
never-applied-var case (`(deftrait (Sizeable a) (size [:a x] Int))`, §7.1 line 29)
is a SEPARATE malformed-head reject already covered at declaration (§7.2.1); the
occurrence rule here is for the conventional bare-head form.

**Seam and placement.** The `check_form_register` `TraitDecl` arm
(`program/register.rs:38–59`) already routes name-freedom through
`reject_def_over_binding` and then calls `register_trait_decl`
(`traits/registry.rs:79`). The occurrence check fires in the **conventional**
registration path of `register_trait_decl` (where the method signatures are in
hand and the conventional-vs-HKT discrimination already lives — HKT routes to
`register_hkt_trait`, exempt), BEFORE the trait entry is written, per method.
`build_method_type` already maps a `TypeExpr::SelfType` return and a bare param to
the implementing-type var, so the occurrence predicate reads the same parsed
signal (bare param / `:self` param / `self` return) off `decl.methods` — no new
parsing. Placement at the arm (mirroring the name-freedom loop's "ONE visible
place") is the alternative; the registry is preferred because it holds the
signature data and the HKT discrimination. `/dev` settles the exact call site; the
requirement is: conventional-only, per-method, declaration-time, correct reason.

**The negative twin flips as a consequence.** Once (i) rejects `(deftrait Zeroable
(zed [] Int))` at declaration, `(zed)` never reaches codegen, so the (ii)
`undefined function` codegen leak is closed with no separate use-site work — the
F-D2 check-gate-leak symptom in this degenerate corner is subsumed by the
declaration reject. Located error uses existing error machinery
(`CranelispError::TypeError` + `ErrorLocation` from the decl span) — no
`cranelisp-types` edit (arch §7).

**Unit tier (`/dev`, METHOD §2.2).** At the registration seam, an accept/reject
pair: `(deftrait Zero (z [] self))` accepted (occurrence via self-return);
`(deftrait Zeroable (zed [] Int))` rejected with the reason substring; a bare-param
method (`(size [x] Int)`) accepted (occurrence via bare param). The GREEN control
`(zed [] self)` (§7.1.1's own example) staying accepted is the fix's boundary
guard (test plan §1.3).

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

### 3.2 TB-24 — poly-applied conventional impl target: bind the target's con-vars (converge the resolver mirror, S113 W2)

**Spec:** §7.3.5 Case 1 + §7.3.3 + §5.4.3 — a conventional (kind-`*`) trait impl over a
poly-applied target `(Option a)` is admissible (`✓`): it registers a polymorphic impl
over every `Option a`, and dispatch on a concrete `(Some 3)` resolves it. Likewise the
canonical constrained form `(Option :Disp a)`. This is spec-admissible and was the only
`✓` Case-1 row with no test — broken on HEAD (`class=wrong-reject`).

**The defect — a `resolver-mirror` (P7 divergent duplication).** For `(impl Disp (Option a) …)`,
`Disp` is conventional, so the arity gate (`impl_check.rs:283–317`) passes (`Option` arity
1 == 1). The reject fires later, resolving the target's type-args at
`impl_check.rs:645–662` (`check_impl_method_with_sig`): each target arg is reduced to its
**bare head string** and resolved as a NAMED type via `concrete_type_for_impl_target`
(`impl_check.rs:654` → `checker.rs:1170`), which does a plain `scope_resolve(state, "a", span)`
(`checker.rs:1183`) and returns `TypeNotFound { name: "a" }` — the "unknown type a" reject,
*before* the value gate. This path passes **no con-var binding** — no `var_map`, no
`mint_free_var`, no `ConVars` — so the lowercase target var `a` cannot resolve as anything
but a nominal type name. It is the 0590-tightening blast-radius shape (a mint site
hardened to reject `/`-qualified vars) landing on a position that legitimately holds a var.

**The fix — route the conventional impl-target args through the shared resolver with a
con-var binding, mirroring the HKT pairing path.** The HKT pairing-head impl path already
binds its con-vars: `resolve_hkt_impl_type_expr` (`checker.rs:2803–2827`, `ConVars::Impl { names, target }`)
routes through the shared `resolve_type_expr_ctx` (`checker.rs:2835`) →
`crate::resolve::resolve_type_expr`, which mints/binds lowercase con-vars as
`Type::Var`/`TyConApp`; the con-var map is built in `register_hkt_trait`
(`registry.rs:206–211`). The conventional impl-target-arg path bypasses
`resolve_type_expr_ctx` entirely and uses the string-head NAMED-lookup shortcut with no
`ConVars`. **Converge them** (P7 — one type-expr resolver, not two): resolve the
conventional target args through `resolve_type_expr_ctx` with a con-var/mint binding for
the target's own lowercase vars, exactly as the HKT `ConVars` path does. The polymorphic
impl then registers over `(Option a)` and dispatch on `(Some 3)` resolves it (both the
bare `(Option a)` and the constrained `(Option :Disp a)` forms — the constraint annotation
rides the same resolver context).

**Attribution:** typecheck-only (`impl_check.rs` + `checker.rs`, converging onto the
existing `resolve_type_expr_ctx`); backend never involved (matches the repro — the reject
is a typecheck resolve-layer diagnostic, parse already accepts `Applied(Option,[a])`); no
types diff; no schema bump. This is the resolver-mirror class (`display-envelope-mirror`'s
resolution-seam sibling) — the fix REDUCES codepaths rather than adding one.

**AS-LANDED (S113 W2a, review APPROVE — records the settled state, P26): ARGS-ONLY, head
kept.** The landed fix is narrower than "route the whole target through the shared resolver."
It routes the target's **ARGS** through the shared `resolve_annotation_type_expr_in_module`
(`impl_check.rs:659–665`, with a `var_map` for con-var mint-on-miss/co-reference) while
**keeping `concrete_type_for_impl_target` for the HEAD** (`impl_check.rs:667`). Review judged
this **safer than whole-target routing**: the head path preserves the §7.3.5 Case-3
kind-check rejects (a primitive as an HKT target, a con-var arity mismatch) that a wholesale
reroute could have loosened. So a poly-applied target `(Option a)` binds its lowercase
con-var `a` as a fresh `Type::Var` (in the SAME `var_map` the method sigs mint into, so a
target var co-refers with a like-named sig var, §3.3.1), a concrete arg (`Int` in `(Option
Int)`) resolves byte-identically, and the §7.3.5 head-position rejects are untouched. The
resolver-mirror convergence is real but scoped to the arg position (the head keeps its
dedicated Case-3-aware path by design). Same P24-corollary family as D2 — see FIXME 0653.

**TB24b (W2 close) — the impl-target CONSTRAINT slot's trait refs now resolve.** A companion
gap on the same target: the impl-target constraint slot (`(Box :Disp a)` →
`impl_.type_constraints = [(a, Disp)]`) carried trait references that were **never routed
through trait resolution** — an unknown trait there (`(Box :NoSuchTrait a)`) was silently
accepted. Landed fix: `check_impl_method_with_sig` (`impl_check.rs:630`) resolves each
`type_constraints` trait ref through the ONE `resolve_trait` (honouring qualification via
`scope_resolve`'s `/`-split, exactly as a param-position bound `:C x` does via
`resolve_bound_param`), erroring `TraitNotFound` on an unknown trait or a non-`TraitDecl`
terminal. Placed **before the HK branch** so it covers every impl kind (conventional + HKT).
Typecheck-only, no types diff, no schema bump.

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

### 7.0.1 D2 — method-import-sufficient dispatch: root at the method's home, not trait-in-scope (S113 W2)

**Spec:** §7.11.2 (settled 2026-07-19) — importing a trait method *without* its trait
is sufficient for **dispatch**; §7.11.2(e) — the nullary return-type-dispatched
method-only-import cell MUST accept and compile (D2 accept-side; the earlier
`undefined function: zed` codegen leak on this cell is a compiler bug, §7.1.1 note).
§7.11.2(d) — **declaration** still requires the trait head in scope (the over-inversion
fence; do NOT touch the impl-declaration path).

**The defect — a P24 "resolve once then throw the home away" anti-pattern.** The
resolution reason the spec gives is *identity, not search*: a method reference carries
its FQ identity, which names the one trait that declares it and hence that trait's home
module (§7.11.2 ¶2). But `try_resolve_trait_method` (`dispatch.rs:21`) roots dispatch at
the trait **name in current scope**, not at the method's chain-followed home:

1. `method_to_trait_with_state` (`checker.rs:2407`) resolves the method's `Def`, reads
   `trait_origin` (which carries the trait's FULL `FQTypeName` — module + name), then
   **discards `fqtn.module` and returns only the bare `TraitName`** (`checker.rs:2415`).
   The home is known and thrown away — the resolve-once violation (P24).
2. `has_impl_with_state(state, &trait_name, …)` (`dispatch.rs:63` → `checker.rs:2457`)
   re-resolves the **bare** trait name via `resolve_terminal_entry_scoped` and requires
   a `TraitDecl` terminal (`checker.rs:2466–2470`); a second bare re-resolution is
   `resolve_trait` (`dispatch.rs:97` → `checker.rs:1201`). When only the METHOD is
   imported, the bare trait name resolves nowhere → `has_impl_with_state` returns
   `false` → the `no impl of trait T for type X` reject fires at `dispatch.rs:70`,
   even though `has_impl_in_home` (`checker.rs:2485`) is already home-rooted and would
   have found the impl had it been handed the discarded home.

**The fix — thread the home (P24 "Resolve once"), no new machinery (arch Q4).** Preserve
the trait's home through `method_to_trait_with_state` (return the `FQTypeName`, or a
`(TraitName, ModuleFullPath)` pair — a typecheck-internal signature change, no
`cranelisp-types` diff) and root the impl lookup at that home via the EXISTING
`has_impl_in_home` (`checker.rs:2485`) instead of the bare `resolve_terminal_entry_scoped`
/ `resolve_trait` re-resolutions. Reaching the method reaches the home reaches the impl
by keyed lookup on (method identity, dispatch type) — the §7.11.2(a) global-coherence
statement, realised as a bounded chain-follow (P24, no scan). The **carrier is already
populated on the accept side**: the nullary path (`dispatch.rs:46`) falls THROUGH into
the shared `ResolvedCall::TraitMethod { … }` tail (`dispatch.rs:138`) — so once the
impl lookup succeeds home-rooted, the carrier codegen keyed-reads (`callees.rs:177`) is
written and `:Int (zed)` links. **The leak closes on the ACCEPT side, not by adding a
reject** (spec ruling; SPRINT §Scope B).

**Watch-cells (spec-pinned, do NOT overshoot):**
- **Two same-named method imports stay a CONFLICT** (§7.11.2(b), §8.6.4): the D2 fix
  roots dispatch at a method's home only AFTER the method reference resolved to a SINGLE
  binding. A duplicate bare-name import (two traits' `m` from two modules) is rejected at
  import time by the existing §8.6.4 conflict seam (`reject_def_over_binding`), BEFORE any
  dispatch resolution — so (b) is preserved by construction; the D2 change touches a
  different seam (dispatch), never the import-conflict path. Do NOT weaken the conflict
  check to "resolve one of them at dispatch."
- **The unary case INVERTS to accept** (§7.11.2(e) final sentence): a unary method
  imported without its trait now dispatches on its argument's concrete type — same
  home-rooting fix, no separate path. (`tests/…::unary_arg_dispatch_method_only_import_*`
  flips must-reject → must-accept; /testing W1 fence-inversion, arch revision 5.)
- **Declaration stays gated** (§7.11.2(d)): the `(impl T Type …)` slot-1 trait-reference
  resolution (`impl_check.rs`, §3) is UNCHANGED — importing a method of `T` does not
  license declaring an impl of `T`. The declaration gate is a different seam; the D2 fix
  must not touch it (the F-D2-8 over-inversion fence stays GREEN).
- **Diagnostics name the owning trait** (§7.11.2(c)): a genuine no-impl/ambiguity error
  MUST still name the trait even when it is not in scope — the trait name is on
  `trait_origin`, available at the error site once the home is threaded (do not drop it
  when re-pointing the lookup).

**Attribution:** typecheck-only (`dispatch.rs` + `checker.rs`); no types diff; no schema
bump (the `ResolvedCall::TraitMethod` carrier shape is unchanged — this populates it for
a cell that previously rejected).

**AS-LANDED (S113 W2a, review APPROVE — records the settled state, P26).** Threading the
home was NOT one hop but **four**, because the trait's home is consulted at four distinct
resolution seams that all previously re-resolved a bare name in ambient scope (the P24
corollary — FIXME 0653):

1. **`method_to_trait_with_state` (`checker.rs:2451`) now returns `(TraitName,
   ModuleFullPath)`** — the trait's home, no longer discarded. This pair is threaded as
   `(trait_name, trait_defining_module)` through `try_resolve_trait_method` (`dispatch.rs:36`).
2. **Impl lookup roots at the home** via the existing `has_impl_in_home(&trait_defining_module,
   …)` (`dispatch.rs:75`). `has_impl_with_state` (`checker.rs:2509`) is now **test-only dead
   code** (its bare re-resolution was the wrong-reject).
3. **A THIRD home-hop in `find_trait_method_decl` (`dispatch.rs:430`)** — the nullary
   `method_self_in_return` decl-scan (which decides whether a method dispatches on its
   `Self` return) must find the method's `TraitDecl`, but a method-only import leaves that
   decl invisible to the current-module + prelude scans. A third hop roots the scan at the
   method's `trait_origin` home, **gated by a new `trait_filter: Option<&TraitName>` param**
   (`find_trait_method_decl_in_module`, `dispatch.rs:483`) so the home-hop reads the method
   off its OWN trait, not any home-resident trait with a same-named method (defence-in-depth
   over §8.6.4 per-module method-name uniqueness). Without this hop `method_self_in_return`
   defaults `false`, the call defers unresolved, and codegen leaks `undefined function` —
   the §7.11.2(e) accept-side leak.
4. **A FOURTH home-hop at dispatch-type resolution** (`dispatch.rs:124` →
   `checker::resolve_type_in_module`, `checker.rs:1187`), a **P24 case-split**: an ADT
   dispatch arg already carries its `FQTypeName` on `Type::ADT(fqtn, _)` — use it directly
   (a user ADT impl'd on a prelude trait lives in the USER module, NOT the trait home, so
   home-rooting would wrong-miss it); an intrinsic scalar (`Int`/…) carries no embedded
   fqtn, so it resolves at the trait's HOME (which reaches `primitives`). Re-resolving the
   bare `Int` in the caller's scope was the "unknown type Int" wrong-reject (W2a Important 3).

Also **`verify_constraints` home-rooted** (`monomorphise.rs`, via `has_impl_in_home`) — the
same P24 corollary instance. **Cross-ref FIXME 0653** (P24 corollary — "a resolution product
carrying FQ identity narrowed to its bare name is a defect marker"; the three W2a instances
above share that shape): resolved identity, not a bare name, is the currency past a
resolution seam.

### 7.0.2 D1 — the multi-sig variant constraint lives on the template scheme, not the OverloadVariant (settled-state contract for the display)

**Spec:** repl/spec.md §4.1.1 — a multi-sig clause `([a b] (+ a b))` MUST display
`:(Fn [:Num a :Num a] a)`, never the constraint-stripped `:(Fn [a a] a)`; dropping the
bound from a variant's display is a §1.4 non-conformance even when it is still enforced.

**Evidence — the fix is int-side (src/), NOT W2 typecheck (this contradicts arch
revision 9's placement assumption; reported to /sprint).** The render seam is int-side:
`src/repl/format_type.rs:42` (`format_overloaded_variants_doc`) builds a `Type::Fn` from
the **bare** `OverloadVariant { param_types, ret_type, mangled_name }`
(`cranelisp-types/src/module.rs:2294`) and never consults a `Scheme`. A bare `Type`
cannot encode a trait bound (constraints live only in `Scheme.constraints`), so the
constraint is structurally absent from what the seam reads. **Typecheck records the
constraint correctly** — it is the settled state: a genuinely-constrained clause is
re-keyed to its `$Var` template entry keeping its `Scheme` (constraints intact) and its
`ast` (`register.rs:559–572`), and that `$Var` mangle is what `OverloadVariant.mangled_name`
carries (`register.rs:571` → `register_overloaded_base`). So the constraint IS reachable
at display time by following `mangled_name` to the template entry and reading its existing
`Scheme.constraints`.

**Two options, and the no-bump one is int-side:**
- **(A) int-side read-follow (no bump).** The display follows `OverloadVariant.mangled_name`
  to the template entry in the module table and renders with `Scheme.constraints`. This
  **reads recorded settled state** (the template scheme) — it is NOT the forbidden
  echo-re-derive shape (the eval.rs `impl_echo_type_name` precedent, arch revision 9): it
  re-derives nothing, it reads the constraint typecheck already recorded. No
  `cranelisp-types` change, no `CACHE_SCHEMA_VERSION` bump.
- **(B) enrich the carrier so the display reads it directly.** Add a constraint field to
  `OverloadVariant` so the render needs no pointer-follow. This is a `cranelisp-types`
  shape change → **schema bump** → **blocked in W2** (SPRINT §Scope B).

**Verdict:** the render seam is int-side and the only typecheck-side alternative needs a
schema bump W2 forbids, so **D1 is an int-side read-follow (option A), best placed in W4
(src/) or as an int-side rider — not W2 typecheck.** The typecheck side is already
correct (the template scheme is the faithful settled record); the fix is teaching the
int display to read that recorded scheme instead of the bare variant. This preserves the
arch-revision-9 *principle* (read recorded settled state, never re-derive at the echo)
while correcting its *placement* (the echo is int's, not typecheck's). `/sprint` to
re-attribute D1 W2→W4.

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
