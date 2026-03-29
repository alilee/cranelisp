# Per-Form Typecheck API (`check_form`)

Design document for Sprint 40 Step 1: decomposing the monolithic `tc.check()` into a per-form API that the v4 scheduler can drive.

## Problem

The current `TypeChecker::check()` method (in `crates/cranelisp-typecheck/src/program.rs`) processes an entire program slice (`&[TopLevel]`) in one call through a multi-pass pipeline. The v4 scheduler (`pipeline-v4.md` section 3.2) needs to typecheck modules form-by-form so that:

1. **Per-symbol codegen readiness**: After a `defn` form is checked, its method resolutions and expr_types are immediately available for codegen workers — no waiting for the whole module.
2. **Macro blocking**: When a macro call needs compiled functions, the worker can block mid-module and resume later.
3. **Lazy dependency discovery**: Imports encountered during processing trigger dependency loading on the fly.
4. **Inter-module parallelism**: Multiple modules can be typechecked concurrently by different workers, each processing their own forms sequentially.

The decomposition must not change the external `CheckResult` contract. Existing callers of `tc.check()` must see identical results.

## Current Structure

`check()` (lines 107-254 of `program.rs`) executes these passes over the entire program:

### Pre-processing

- Set active module, create fresh `CheckState`.
- Handle `ModuleStrategy::Additive` (REPL): reconstruct overloads from symbol table.
- Handle `ModuleStrategy::Replace`: clear module state.
- Wrap `TopLevel::Expr` variants as synthetic zero-arg `Defn` named `__expr`.

### Pass 1: Registration (4 sub-passes over all forms)

1. **Type definitions** (`register_type_defs_from_program`): Iterates all `TopLevel::TypeDef` forms. Registers ADTs in `type_defs` registry, constructors in symbol table.
2. **Trait declarations** (`register_trait_decls_from_program`): Iterates all `TopLevel::TraitDecl` forms. Registers traits in `trait_registry`.
3. **Trait implementations** (`register_trait_impls_from_program`): Iterates all `TopLevel::TraitImpl` forms. Validates and registers in `impl_registry`. Returns default method `Defn`s.
4. **Function signatures** (`pass1_register_signatures`): For each `Defn` (single-sig + expanded multi-sig variants), allocates fresh type variables for parameters and return type, registers a preliminary `ModuleEntry::Def` in the symbol table. Returns `defn_type_vars: HashMap<Symbol, (Vec<Type>, Type)>`.

Between sub-passes 3 and 4, multi-sig `DefnMulti` forms are expanded into synthetic single-variant `Defn`s with internal names (`name__v0`, `name__v1`), and the base name gets an `Overloaded` placeholder in the symbol table.

### Pass 2: Body checking + generalization

`pass2_check_bodies` (lines 944-1017) has three internal phases:

- **Phase 1**: For each defn, check the body via `check_defn_body` (push scope, bind params, infer body, unify with return type, pop scope). After each body, resolve deferred trait calls and eagerly detect constrained polymorphism.
- **Phase 2**: Generalize all functions (apply final substitution, quantify free vars, record constraints). Clear false-positive constrained markers where later call sites pinned the type vars.
- **Phase 3**: Re-resolve deferred trait calls now that all types are pinned.

### Pass 2.5: Multi-sig overload resolution

`resolve_multi_sig_overloads`: For each multi-sig defn, apply substitution to get concrete parameter types, mangle names (`foo$Int+Bool`), register mangled names in symbol table, populate `resolved_overloads`.

### Pass 3: Detect constrained polymorphic functions

`detect_constrained_fns`: Scan symbol table for `DefKind::UserFn { constrained_fn: Some(..) }` entries (already marked during Pass 2 Phase 1).

### Pass 4: Monomorphisation

`pass4_monomorphise`: Scan all defn bodies for calls to constrained functions. For each call site, look up concrete arg types from `expr_types`, generate a monomorphised specialization, record `SigDispatch` resolution.

### Pass 5: Overload dispatch + auto-curry resolution

`resolve_pending_overloads`: Match pending overload call sites against resolved variants.
`resolve_auto_curry`: Resolve pending auto-curry sites.

### Result assembly

`build_check_result`: Drain `CheckState` into `CheckResult`. Compute `DisplayInfo` for REPL output.

## Proposed Decomposition

### Two-pass model with per-form granularity

The fundamental constraint is that **all signatures must be registered before any body is checked** — this is what allows mutual recursion. A function body may call any other function defined in the same module, so all signatures must be visible before inference begins.

With per-form processing, this means `check_form()` must be called in two passes by its caller:

- **Pass 1 (registration)**: For each form in source order, call `check_form(module, form, CheckPass::Register)`. This registers type definitions, trait declarations, trait implementations, and function signatures.
- **Pass 2 (body checking)**: For each `Defn` form in source order, call `check_form(module, form, CheckPass::CheckBody)`. This checks the function body, generalizes the type, and detects constrained polymorphism.

The caller (currently `check()` internally; in v4, `process_module_forms` in the scheduler worker loop) drives the two-pass iteration.

### Pass indicator

A `CheckPass` enum distinguishes the two passes:

```rust
pub enum CheckPass {
    /// Pass 1: register type/trait/signature.
    /// For Defn: registers signature only. For TypeDef/TraitDecl/TraitImpl: full registration.
    Register,
    /// Pass 2: check function body, generalize, detect constraints.
    /// Only meaningful for Defn forms. Other form kinds return an empty result.
    CheckBody,
}
```

This is the simplest approach (per /arch review section 6b). The alternative of two separate methods (`register_form` / `check_form_body`) would work equally well but adds API surface without benefit. A single method with a pass parameter makes the calling pattern explicit.

### `FormCheckResult`

```rust
pub struct FormCheckResult {
    /// Method resolutions discovered while checking this form.
    /// In Pass 1: empty (registration produces no resolutions).
    /// In Pass 2: resolutions from the body of this defn.
    pub method_resolutions: MethodResolutions,

    /// Expression types for this form's AST nodes.
    /// In Pass 1: may contain constructor types for TypeDef forms.
    /// In Pass 2: contains all expr types from the defn body + the defn's Fn type.
    pub expr_types: HashMap<Span, Type>,

    /// If this form defines a constrained polymorphic function (Pass 2 only),
    /// the function name. Used by the caller to build the constrained_fn_names set.
    pub constrained_fn: Option<Symbol>,

    /// Monomorphised definitions generated from this form's call sites (Pass 2 only).
    /// In the current check(), monomorphisation is a separate pass 4 that scans
    /// all defn bodies. With per-form processing, monomorphisation for a defn's
    /// call sites happens during that defn's Pass 2 check.
    pub mono_defns: Vec<MonoDefn>,

    /// Default method definitions expanded from trait impls in this form (Pass 1 only).
    /// Produced when a TraitImpl form triggers default method synthesis.
    pub default_method_defns: Vec<Defn>,

    /// Multi-sig mangled definitions produced during overload resolution.
    /// Populated when a multi-sig DefnMulti's variants are resolved after Pass 2.
    pub multi_sig_defns: Vec<Defn>,

    /// Warnings emitted during checking this form.
    pub warnings: Vec<Warning>,
}
```

**Field justification against Step 3 requirements:**

| Field | Step 3 need |
|-------|-------------|
| `method_resolutions` | Codegen workers read per-symbol resolutions immediately after typecheck. |
| `expr_types` | Codegen workers need expr types for heap classification. |
| `constrained_fn` | Scheduler tracks which functions are constrained for monomorphisation. |
| `mono_defns` | Each mono defn is an additional codegen unit the scheduler must track. |
| `default_method_defns` | Additional defns that need signature registration and body checking. |
| `multi_sig_defns` | Additional defns from multi-sig expansion, need codegen. |
| `warnings` | Accumulated and reported after module completion. |

### `merge_form_result()`

Accumulates a `FormCheckResult` into the module's growing state:

```rust
impl TypeChecker {
    pub fn merge_form_result(
        &mut self,
        module: &ModuleFullPath,
        result: FormCheckResult,
    ) {
        // Merge method_resolutions into the module's accumulated resolutions.
        // Merge expr_types into the module's accumulated expr_types.
        // Append mono_defns to the module's accumulated mono_defns.
        // Append default_method_defns to the module's accumulated defaults.
        // Append multi_sig_defns to the module's accumulated multi-sig.
        // If constrained_fn is Some, add to the module's constrained_fn_names set.
        // Append warnings.
    }
}
```

The merge target is a new per-module accumulator struct stored alongside the `CheckState`:

```rust
pub(crate) struct ModuleCheckAccumulator {
    pub method_resolutions: MethodResolutions,
    pub expr_types: HashMap<Span, Type>,
    pub constrained_fn_names: HashSet<Symbol>,
    pub mono_defns: Vec<MonoDefn>,
    pub default_method_defns: Vec<Defn>,
    pub multi_sig_defns: Vec<Defn>,
    pub warnings: Vec<Warning>,
    /// Type vars from pass 1 registration, keyed by defn name.
    /// Needed by pass 2 to check bodies against registered signatures.
    pub defn_type_vars: HashMap<Symbol, (Vec<Type>, Type)>,
}
```

After all forms are processed, `finalize_check_result()` runs post-passes, sweeps their outputs into the accumulator, and builds `CheckResult` exclusively from the accumulator:

```rust
impl TypeChecker {
    pub fn finalize_check_result(
        &mut self,
        module: &ModuleFullPath,
        accumulator: &mut ModuleCheckAccumulator,
        working_program: &[TopLevel],
        strategy: ModuleStrategy,
    ) -> Result<CheckResult, CranelispError> {
        // Run post-passes (generalization, deferred trait resolution,
        // multi-sig overloads, constrained fn detection, monomorphisation,
        // pending overloads, auto-curry).
        //
        // Post-passes write new method_resolutions into self.state.
        // After post-passes complete, sweep self.state.method_resolutions,
        // self.state.expr_types, and self.state.warnings into the accumulator.
        // Then build CheckResult from the accumulator (authoritative source).
        // type_defs and constructor_to_type are read from TypeChecker module
        // tables, not from the accumulator.
    }
}
```

**Data flow**: During per-form checking, `merge_form_result()` collects method_resolutions, expr_types, and warnings into the accumulator. Post-passes in `finalize_check_result()` write additional resolutions into `self.state.method_resolutions` (the working scratch space). After all post-passes complete, these are swept into the accumulator. The `CheckResult` is built exclusively from the accumulator. `self.state` is working scratch; the accumulator is the authoritative record.

### `check_form()` implementation

```rust
pub fn check_form(
    &mut self,
    module: &ModuleFullPath,
    form: &TopLevel,
    pass: CheckPass,
) -> Result<FormCheckResult, CranelispError>
```

The method dispatches on `(form variant, pass)`:

| Form | `Register` pass | `CheckBody` pass |
|------|----------------|-----------------|
| `TypeDef` | Register type def, constructors in symbol table. Return expr_types for constructor types. | No-op (empty result). |
| `TraitDecl` | Register trait in `trait_registry`. | No-op. |
| `TraitImpl` | Validate and register impl. Synthesize default method defns. Return `default_method_defns`. | No-op. |
| `Defn` (single-sig) | Register signature with fresh type vars. Store in accumulator's `defn_type_vars`. | Check body, generalize, detect constraints. Scan body for constrained fn calls (monomorphisation). Return `method_resolutions`, `expr_types`, `constrained_fn`, `mono_defns`. |
| `Defn` (multi-sig) | Expand variants into internal names. Register each variant's signature. Register base name as `Overloaded` placeholder. | Check each variant's body. After all variants checked, resolve overloads (mangle names, register in symbol table). Return `multi_sig_defns`, `method_resolutions`, `expr_types`. |
| `Expr` | Wrapped as synthetic `__expr` defn. Register signature. | Check body. Return `method_resolutions`, `expr_types`. |

### Rewriting `check()` to use `check_form()`

The existing `check()` method is rewritten to:

```rust
pub fn check(&mut self, program: &[TopLevel], ctx: &CompileContext, strategy: ModuleStrategy)
    -> Result<CheckResult, CranelispError>
{
    // Pre-processing: set module, create CheckState, handle strategy.
    // Wrap Expr forms as synthetic Defns.

    // Pass 1: register all forms
    for form in &working_program {
        let result = self.check_form(&ctx.module, form, CheckPass::Register)?;
        self.merge_form_result(&ctx.module, result);
    }

    // Register default method defns generated during Pass 1 TraitImpl processing.
    // These need Pass 1 signature registration too.
    let defaults = self.take_accumulated_defaults(&ctx.module);
    for defn in &defaults {
        // Register signature for each default method defn.
        let result = self.check_form_defn_register(defn)?;
        self.merge_form_result(&ctx.module, result);
    }

    // Pass 2: check bodies for all Defn forms
    for form in &working_program {
        let result = self.check_form(&ctx.module, form, CheckPass::CheckBody)?;
        self.merge_form_result(&ctx.module, result);
    }

    // Check bodies of default method defns too.
    for defn in &defaults {
        let result = self.check_form_defn_body(defn)?;
        self.merge_form_result(&ctx.module, result);
    }

    // Finalize: resolve pending overloads, auto-curry, build CheckResult.
    let result = self.finalize_check_result(&ctx.module);
    Ok(result)
}
```

This preserves the exact pass ordering and produces identical `CheckResult` output. All existing callers are unchanged.

## Multi-Pass Invariants

### Invariant 1: All signatures before all bodies

Every `Defn` in the module must have its signature registered (Pass 1) before any body is checked (Pass 2). This enables mutual recursion: `f` can call `g` and `g` can call `f` because both signatures are visible during body checking.

**Enforcement**: The caller drives the two-pass iteration. `check_form` with `CheckPass::CheckBody` looks up the defn's type vars from the accumulator's `defn_type_vars` — if the signature was not registered, this is a missing-key error.

### Invariant 2: Type defs before trait decls before trait impls before signatures

Within Pass 1, the ordering matters:
- Type definitions must be registered before trait impls can reference them.
- Trait declarations must be registered before trait impls can validate against them.
- Trait impls must be registered before function signatures, because default method defns generated from impls need signature registration.

**Enforcement**: Source order in Cranelisp is the programmer's responsibility (spec section 9.12). The `check_form` caller processes forms in source order, which must respect these dependencies. The current `check()` iterates all TypeDefs first, then all TraitDecls, then all TraitImpls, then all signatures — this is a four-sub-pass structure within Pass 1.

For `check_form()` to work form-by-form in source order, each form's Pass 1 does the right thing based on its variant: TypeDef registers immediately, TraitDecl registers immediately, TraitImpl validates and registers immediately, Defn registers its signature immediately. This works correctly as long as the source file declares types before traits, traits before impls, and impls before functions that use them — which is the spec-required ordering.

**Complication**: The current `check()` does four separate sweeps (all TypeDefs, then all TraitDecls, etc.) which allows forms to appear in any order. A strict source-order single-sweep changes the required ordering. However, the spec (section 9.12) requires source order to be meaningful, so this is acceptable. The key question is whether any existing programs interleave TypeDef/TraitDecl/TraitImpl/Defn in ways that break single-sweep processing. If this is a concern, `check_form` in `Register` pass can internally buffer and sort by kind, but the simpler approach is to process in source order and let programs that violate ordering get clear errors.

**Decision**: Process in source order during `Register` pass. Each form kind does its own registration immediately. This matches the v4 scheduler's form-by-form model. If existing programs break, they can be reordered — but in practice, Cranelisp programs already follow the natural dependency order because the sketch enforced similar constraints.

### Invariant 3: Shared substitution within a module

All forms in a module share a single `CheckState` (and thus a single substitution environment). Type variables allocated in Pass 1 for function `f` may be unified with type variables from function `g` during Pass 2 body checking (e.g., `f` calls `g`). This shared substitution is what enables type inference across function boundaries.

**Enforcement**: `check_form` operates on `self.state` (the `CheckState` on the `TypeChecker`). The caller creates one `CheckState` per module before starting Pass 1, and it persists through Pass 2. `FormCheckResult` snapshots the relevant portions of state (expr_types, method_resolutions) but the substitution remains shared.

### Invariant 4: Generalization after all bodies

In the current `check()`, generalization happens in Pass 2 Phase 2 — after all bodies are checked. This is important: a function's type may be constrained by how it is called in other functions' bodies. Generalizing too early (before all bodies are checked) would quantify type variables that later unification would have pinned.

**Adaptation for per-form**: In `check_form` with `CheckPass::CheckBody`, we check the body and do an eager generalization trial (as the current Pass 2 Phase 1 does). Final generalization happens in `finalize_check_result()` (matching the current Pass 2 Phase 2). This means `FormCheckResult.expr_types` from Pass 2 may contain unresolved type variables — `finalize_check_result()` applies the final substitution.

However, for the v4 scheduler's per-symbol codegen readiness (where a codegen worker starts compiling a defn before the whole module is done), we need expr_types with concrete types. The resolution: `FormCheckResult.expr_types` are **partially resolved** (substitution applied at form-check time). When `finalize_check_result()` runs, it re-applies the final substitution to catch any variables pinned by later body checking. Codegen workers that start early use the partially-resolved types, which are correct for functions whose types are already fully determined (no later unification will change them). For functions involved in mutual-recursion cycles where types are still evolving, the codegen worker waits for `notify_typecheck_done`.

**For Step 1, this is not yet a concern** — `check()` still processes the whole program before returning. The early-codegen optimization is a Step 3 concern.

## Edge Cases

### `defmacro` forms

Macros do not go through the typecheck pipeline — they are compiled directly from Sexp. In the current codebase, macro registration happens during AST building (before `check()` is called). `check_form()` will never see a `defmacro` — by the time a form reaches the typechecker, macros have already been expanded. If a future `TopLevel::Macro` variant is added, `check_form` in `Register` pass would register it in the module table as `ModuleEntry::Macro`, and `CheckBody` pass would be a no-op.

In the v4 scheduler (Step 4), macro forms are registered during form processing but not compiled until first use. This is a scheduler concern, not a typechecker concern — `check_form` does not need to handle macro compilation.

### `impl` blocks (TraitImpl)

`TraitImpl` forms may generate default method definitions (for trait methods with default bodies that the impl does not override). These default method defns need to go through both Pass 1 (signature registration) and Pass 2 (body checking).

In the current `check()`, default defns are collected during the TraitImpl registration sub-pass and added to the `all_defn_refs` list for Pass 1 and Pass 2. With per-form processing, `check_form(TraitImpl, Register)` returns the default defns in `FormCheckResult.default_method_defns`. The caller is responsible for feeding these back through `check_form(Defn, Register)` and `check_form(Defn, CheckBody)`.

The `check()` rewrite handles this explicitly: after Pass 1 processes all original forms, it takes the accumulated default defns and runs Pass 1 registration and Pass 2 body checking on them. In the v4 scheduler, this becomes additional forms injected into the processing queue after the TraitImpl form.

### Constrained polymorphism

Detection of constrained polymorphic functions happens during Pass 2 body checking (eager detection) and is confirmed during generalization. With per-form processing, `check_form(Defn, CheckBody)` checks the body and detects if the function is constrained. The `FormCheckResult.constrained_fn` field carries this information.

Monomorphisation of call sites also happens per-form in Pass 2: after checking a defn body, `check_form` scans that body for calls to known constrained functions (from the accumulator's `constrained_fn_names` set) and generates mono defns. This is a change from the current separate Pass 4, where all defn bodies are scanned after all body checking is complete.

**Ordering concern**: A function `f` that calls constrained function `g` can only be monomorphised if `g` has already been detected as constrained. Since Pass 2 processes forms in source order, `g` must appear before `f` in the source. For within-module cases, this is the spec-required ordering. For cross-module cases, the dependency module is already fully typechecked, so its constrained functions are already known.

**Complication**: The current Pass 4 scans all bodies after all generalization is complete, which means it has the benefit of final substitution. Per-form monomorphisation happens before later functions' bodies might pin type variables. However, monomorphisation only operates on call sites in non-constrained functions, and those call sites have concrete arg types (the function itself is not polymorphic). So the arg types in `expr_types` should already be concrete after the body check. This is safe.

### DefnMulti (multi-sig functions)

Multi-sig defns are expanded into internal single-variant defns during Pass 1. With per-form processing:

- `check_form(DefnMulti, Register)`: Expands variants into `name__v0`, `name__v1`, etc. Registers each variant's signature. Registers base name as `Overloaded` placeholder. The expanded internal defns are returned (via `default_method_defns` or a new field) for the caller to also register.
- `check_form(DefnMulti, CheckBody)`: Checks each variant's body. After all variant bodies are checked, resolves overloads (mangles names, checks for duplicates, registers mangled names). Returns `multi_sig_defns` for codegen.

The multi-sig variants share the module's substitution, so their types are resolved in the same context as other functions. Overload resolution (Pass 2.5 in current code) is folded into the `CheckBody` pass for the multi-sig form.

### `Expr` forms (REPL expressions)

`Expr` forms are wrapped as synthetic zero-arg `Defn` named `__expr` during pre-processing (before `check_form` is called). From `check_form`'s perspective, they are ordinary `Defn` forms. The synthetic wrapping happens in `check()` pre-processing or in the v4 caller.

## Sketch Comparison

The sketch (`sketch/src/typechecker/program.rs`) has a monolithic `check_program()` with the same multi-pass structure:

1. Register type defs, traits, trait impls
2. Expand multi-sig defns
3. Pass 1: register all function signatures
4. Pass 2: check all bodies, generalize
5. Post-passes: constrained fn detection, monomorphisation, overload resolution, auto-curry

The sketch has no per-form typecheck API. This is new ground for the reimplementation, driven by the v4 scheduler's form-by-form processing requirement.

**Key difference from sketch**: The sketch processes the entire program as a unit, which is simple but prevents incremental codegen. The reimplementation's per-form API enables the scheduler to interleave typechecking and codegen — a symbol's codegen can start as soon as its typecheck completes, without waiting for the rest of the module.

**What we preserve from the sketch**: The two-pass structure (register all, then check all) is fundamental to Algorithm W with mutual recursion. Both the sketch and the reimplementation use this structure. The decomposition preserves it by having the caller drive the two-pass iteration, not by changing the fundamental algorithm.

**What we diverge on**: The sketch's monolithic function is ~200 lines with interleaved concerns (multi-sig expansion, impl method synthesis, overload resolution). The reimplementation decomposes these into `check_form` dispatch + `merge_form_result` accumulation + `finalize_check_result` post-processing. This is cleaner separation of concerns and enables the v4 scheduler to call individual pieces.

## Architecture Review

**Reviewer**: /arch
**Date**: 2026-03-29
**Verdict**: APPROVED with minor changes requested

### 1. `FormCheckResult` — Carries What Step 3 Needs

**Approved.** The field set is sufficient for the Step 3 scheduler (`process_module_forms` in `pipeline-v4-roadmap.md` Step 3) to drive per-symbol codegen readiness.

Verification against `concurrent-pipeline.md` section 10.2 and `pipeline-v4.md` section 3.2:

| Scheduler need | Covered by | Verdict |
|---|---|---|
| Per-symbol method resolutions for immediate codegen | `method_resolutions` | OK |
| Per-symbol expr_types for heap classification | `expr_types` | OK |
| Constrained fn tracking for monomorphisation | `constrained_fn` | OK |
| Additional codegen units from monomorphisation | `mono_defns` | OK |
| Default method defns needing registration + body check | `default_method_defns` | OK |
| Multi-sig mangled defns needing codegen | `multi_sig_defns` | OK |
| Warnings for post-module reporting | `warnings` | OK |

**Missing field — `call_graph` contribution.** `CheckResult` has a `call_graph: CallGraph` field (see `interfaces.md`). The design doc does not mention how per-form call graph edges accumulate. The current `check()` presumably builds the call graph during body checking. `FormCheckResult` should carry per-form call graph edges, and `ModuleCheckAccumulator` should merge them. Without this, `finalize_check_result()` cannot populate `CheckResult.call_graph`.

**Action required**: Add a `call_graph_edges` field (or similar) to `FormCheckResult` and `ModuleCheckAccumulator`. The scheduler in Step 3 also needs call graph edges for macro dependency walks (`pipeline-v4.md` section 3.2, step 1 — "walks the resolved calls to collect the transitive closure of function dependencies"). If `FormCheckResult` does not carry call graph data, the scheduler cannot perform macro call graph walks without reaching into TypeChecker internals.

**Missing field — `type_defs` / `constructor_to_type`.** `CheckResult` carries `type_defs: HashMap<TypeName, TypeDefInfo>` and `constructor_to_type: HashMap<Symbol, TypeName>`. These are populated during Pass 1 (TypeDef registration). `FormCheckResult` does not carry them. This is acceptable IF `finalize_check_result()` reads them from the TypeChecker's internal state rather than from the accumulator. But the design should be explicit about this. If the intent is that the accumulator holds everything needed for `CheckResult` assembly, these fields should be present.

**Recommendation**: Document explicitly that `type_defs` and `constructor_to_type` are read from the TypeChecker's module tables during `finalize_check_result()`, not accumulated per-form. This is the natural approach since TypeDef registration writes directly into the module's symbol table. No field addition needed, just document the intent.

### 2. `CheckPass` Enum

**Approved.** The two-variant enum (`Register` / `CheckBody`) correctly models the fundamental two-pass structure. This is the simplest approach as noted in the Architecture Review section 6b of the sprint plan.

One observation: the `Register` pass does four logically distinct things depending on form kind (register type def, register trait decl, register trait impl, register signature). The current `check()` does these as four separate sub-sweeps. The design doc's "Decision" section correctly notes that source-order single-sweep processing is acceptable per spec section 9.12. This is sound — the spec requires source order to be meaningful, so programs that violate the ordering get a clear error rather than silent mis-behavior.

No additional pass variants needed. The post-passes (overload resolution, auto-curry, final substitution) are correctly placed in `finalize_check_result()`, not modeled as additional `CheckPass` values.

### 3. `merge_form_result()` / `ModuleCheckAccumulator` / `finalize_check_result()`

**Approved with one concern.**

The three-step pattern (produce per-form result, merge into accumulator, finalize into CheckResult) is sound. It preserves the exact semantics of the current monolithic `check()` while enabling form-by-form processing.

**Concern: `defn_type_vars` lifetime.** The accumulator stores `defn_type_vars: HashMap<Symbol, (Vec<Type>, Type)>` from Pass 1. Pass 2 reads these to check bodies. This is correct for the current `check()` rewrite. However, in the Step 3 scheduler world, there is a gap between Pass 1 and Pass 2 during which codegen workers might be active on other modules. The `defn_type_vars` must remain valid across this gap. Since the accumulator is per-module and persists until `finalize_check_result()`, this is fine — just noting it as a future consideration. No action needed.

**Observation on `take_accumulated_defaults()`.** The `check()` rewrite shows `self.take_accumulated_defaults(&ctx.module)` between Pass 1 and Pass 2 to retrieve default method defns. This is a mutation of the accumulator during the iteration. The pattern is:
1. Pass 1 on all original forms (some produce `default_method_defns`)
2. Take defaults from accumulator
3. Pass 1 registration on defaults
4. Pass 2 on all original forms
5. Pass 2 on defaults

This ordering is correct and necessary. The v4 scheduler (Step 3) will need the same pattern — after Pass 1 of all forms, extract defaults and run Pass 1 registration on them before starting Pass 2. Document this as a caller contract.

### 4. Multi-Pass Invariants

**Invariants 1-3 are correct and complete.**

**Invariant 4 (generalization after all bodies) — needs clarification.** The design says `FormCheckResult.expr_types` from Pass 2 "may contain unresolved type variables" and that `finalize_check_result()` re-applies the final substitution. This is correct. But the doc then discusses early-codegen optimization (codegen starting before the module is fully checked) and says "For Step 1, this is not yet a concern."

This is fine for Step 1. For Step 3 readiness, the key question is: can a codegen worker start compiling a defn using `FormCheckResult.expr_types` that still contain unresolved type variables? The design correctly identifies that non-mutually-recursive functions will have fully concrete types, while mutually-recursive ones may not. This is the right analysis.

**Action**: No change needed for Step 1. When Step 3 is designed, the `notify_symbol_typechecked` call in the worker loop must distinguish between "fully resolved" (safe for immediate codegen) and "partially resolved" (wait for `finalize_check_result`). This should be noted as a Step 3 concern, not a Step 1 concern.

**Missing invariant — accumulator ownership.** Add an invariant: "One `ModuleCheckAccumulator` per module, created before Pass 1 and consumed by `finalize_check_result()`. No concurrent access — a single worker processes one module's forms sequentially." This is implicit but should be stated, since the v4 scheduler will have multiple workers and needs to know that a module's accumulator is private to its worker.

### 5. No Throwaway Infrastructure (Principle 8)

**Approved.** Every artifact in this design survives to the target architecture:

- `check_form()` is the permanent per-form entry point called by the Step 3 worker loop.
- `FormCheckResult` is the permanent per-form output consumed by `merge_form_result()` and (in Step 3) by the scheduler for `notify_symbol_typechecked`.
- `ModuleCheckAccumulator` is the permanent per-module accumulation state.
- `finalize_check_result()` is the permanent post-pass entry point.
- `CheckPass` is the permanent pass indicator.

The `check()` rewrite is the internal consumer in Step 1; the scheduler's `process_module_forms` is the external consumer in Step 3. Both call the same API.

### 6. Edge Cases

**defmacro**: Correctly identified as not a typecheck concern. No issues.

**TraitImpl with defaults**: The `default_method_defns` field and the caller contract to feed defaults back through both passes is correct. The `check()` rewrite handles this explicitly.

**Constrained polymorphism**: The ordering concern (function `f` calling constrained `g` requires `g` to appear first) is correctly identified as acceptable per spec section 9.12. The analysis that monomorphisation is safe with partially-applied substitution (because non-constrained call sites have concrete arg types) is correct.

**DefnMulti**: The design says expanded internal defns are "returned via `default_method_defns` or a new field." This is sloppy — `default_method_defns` is specifically for trait impl default methods. Multi-sig variant defns should NOT be conflated with default method defns.

**Action required**: Clarify that multi-sig variant expansion in `check_form(DefnMulti, Register)` does NOT use `default_method_defns`. The expanded variants are registered internally by `check_form` (their signatures are registered in the module table within the `Register` call). The `check()` rewrite does not need to see them as returned defns because `check_form(DefnMulti, CheckBody)` knows the variant names from the module table. If the variants do need to be returned for external visibility, use a dedicated field (e.g., rename or repurpose `multi_sig_defns`). Do not overload `default_method_defns`.

### 7. Summary of Required Changes

1. **Add `call_graph_edges` field** to `FormCheckResult` and `ModuleCheckAccumulator`. The Step 3 scheduler needs per-form call graph data for macro dependency walks and for populating `CheckResult.call_graph`.
2. **Clarify `type_defs`/`constructor_to_type` sourcing** — document that these are read from TypeChecker module tables in `finalize_check_result()`, not accumulated per-form.
3. **Add accumulator ownership invariant** — one accumulator per module, no concurrent access.
4. **Fix DefnMulti variant return path** — do not overload `default_method_defns` for multi-sig variant defns. Either handle them internally in `check_form` or use a dedicated field.

None of these are blocking concerns — they are refinements to an otherwise sound design. The `/typecheck` skill may address them during implementation. The design is approved for implementation to proceed.
