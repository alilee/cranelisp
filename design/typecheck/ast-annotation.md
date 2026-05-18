# AST Annotation: Co-locating Types and Resolved Calls with AST Bodies

Sprint 55, Steps 1a + 1b. Prerequisite for Steps 1c + 1d (backend reads from AST, CheckResult elimination).

## 1. Problem

Today, typecheck produces three separate outputs that codegen consumes:

1. **AST bodies** (`Vec<TopLevel>`) -- passed via `CodegenInput.program`
2. **Resolved calls** (`HashMap<Span, ResolvedCall>`) -- on `CheckResult.method_resolutions`
3. **Expression types** (`HashMap<Span, Type>`) -- on `CheckResult.expr_types`

These are structurally disconnected. The AST bodies live in a transient `CodegenInput` struct, while resolved calls and expr types live on `CheckResult`. Both are threaded through the integration layer as side-channel data. The `Span` keys that connect expr types and resolved calls back to specific AST nodes are a fragile indirection -- they work only because spans are unique within a compilation unit, but they carry no structural relationship to the AST.

The pipeline-v4 target (`pipeline-v4.md` Section 9.1) eliminates this separation: typecheck writes AST bodies, resolved calls, and expression types directly onto `ModuleEntry::Def` entries in the symbol table. Codegen reads them from the symbol table by name. `CheckResult` stops being a boundary type.

This document describes Steps 1a and 1b -- the write side of the migration. Steps 1c and 1d (read side, elimination) are in `design/backend/ast-sourced-codegen.md`.

## 2. Step 1a: `ast: Option<Defn>` on `ModuleEntry::Def`

### 2.1 Field Definition

Add to `ModuleEntry::Def` in `crates/cranelisp-types/src/module.rs`:

```rust
ModuleEntry::Def {
    // ... existing fields ...

    /// Typechecked function body. Written by typecheck after check_form(CheckBody).
    /// Read by codegen. None for primitives, special forms, and pre-body-check entries.
    #[serde(default)]
    ast: Option<Defn>,
}
```

### 2.2 When It Is Populated

The `ast` field is `None` in three cases:
- **Primitives and special forms**: no AST body exists (they are implemented in Rust or as IR patterns).
- **Pass 1 registration**: the entry is created with signature information only; the body has not been checked yet.
- **Constructors, imports, macros**: these are not `ModuleEntry::Def` entries, or (for constructors) their code is generated synthetically by the backend.

The `ast` field is set to `Some(defn)` after `check_form(CheckBody)` succeeds for a `TopLevel::Defn`. The typecheck crate already has access to the `Defn` at this point (it is the input to `check_form_body_single_defn`). The integration layer (`worker.rs`) clones the `Defn` onto the entry.

### 2.3 Why `Defn` Not `DefnVariant`

The pipeline-v4.md target specifies `ast: Option<DefnVariant>`, anticipating Phase 2 where `compile_to_module` takes `names: &[Symbol]` and reads the name from the symbol table key. For Phase 1, we use `Defn` because:

- `compile_to_module` currently expects `Defn` (reads `defn.name`, `defn.variants`).
- Using `DefnVariant` now would force Step 1c to reconstruct `Defn` from entry fields -- unnecessary intermediate work.
- The `Defn` -> `DefnVariant` narrowing is a Phase 2 concern (Step 2a).

### 2.4 Multi-sig Functions

For a `DefnMulti` with N variants, the current pipeline creates N internal entries (`foo__v0`, `foo__v1`, ...) plus a base name entry with `DefKind::Overloaded`. Each internal entry gets its own `ast: Option<Defn>` set to a synthetic single-variant `Defn`. The base name entry has `ast: None` (it is a dispatch index, not a compilable function).

### 2.5 Dual-Write Period

During Step 1a, the `ast` field is **write-only**. No consumers read it. The existing `CodegenInput.program` continues to carry AST bodies to codegen. This is not interim architecture -- it is a migration strategy. The dual path is validated in Step 1b and eliminated in Step 1d.

### 2.6 TraitImpl Forms

`TopLevel::TraitImpl` forms produce method entries via the existing trait impl registration path. Each method within a `TraitImpl` becomes a `ModuleEntry::Def` with a mangled name (e.g., `Display.show$Option$Int`). These entries get `ast: Some(method_defn)` after body checking — but this requires the annotation fix described in Section 3.7.

**Key consequence**: Once trait impl methods have fully annotated `ast` fields on their `ModuleEntry::Def` entries, `compile_regular_defns` in the integration layer can find them by mangled name — the same as any other function. There is no need to iterate `TopLevel::TraitImpl` forms during codegen. The integration layer's `TopLevel::TraitImpl(_) => {}` (skip) is correct: the methods are already on the symbol table under their mangled names, with populated `ast` fields ready for compilation.

### 2.7 TypeDef and Expr Forms

- **TypeDef**: produces `ModuleEntry::TypeDef` and `ModuleEntry::Constructor` entries. No `ast` field needed -- constructors are compiled synthetically by the backend.
- **Expr** (REPL trailing expressions): wrapped in a synthetic zero-arg `Defn` named `__expr` by the checker. This synthetic defn flows through the same path as regular defns. Its `ast` is not written to the symbol table because `__expr` is not a persistent symbol -- it is compiled and executed once. The eval closure path (pipeline-v4.md Section 6.2) handles this outside the symbol table.

## 3. Step 1b: Annotation Strategy

### 3.1 Design Decision: Where Types and Resolved Calls Live

Three approaches were considered:

**(A) Per-Expr-node `inferred_type: Option<Type>` (unboxed)** -- add an unboxed `Option<Type>` field to every `Expr` variant. Rejected: `Type` is ~56 bytes, inflating every variant. See Section 4 (size analysis).

**(B) `resolved_call: Option<ResolvedCall>` on `Expr::Apply` only + `expr_types: HashMap<Span, Type>` on `Defn`** -- considered as a hybrid approach. Moves the sparse type map from `CheckResult` to `Defn`, but retains Span-keyed lookup. Rejected: Span is a fragile key (byte-offset reverse lookup, span collision risk with synthesized code). See Section 3.3 rationale.

**(C) Full wrapping `TypedExpr` struct** -- `struct TypedExpr { expr: Expr, inferred_type: Option<Type>, resolved_call: Option<ResolvedCall> }`. Rejected: requires converting all recursive `Expr` positions (`Box<Expr>`, `Vec<Expr>`) to `Box<TypedExpr>` and `Vec<TypedExpr>`, touching every construction site and every pattern match across the codebase.

**Chosen: `resolved_call: Option<Box<ResolvedCall>>` on `Expr::Apply` + `inferred_type: Option<Box<Type>>` on every `Expr` variant.** This eliminates `HashMap<Span, _>` entirely — types and resolved calls are co-located with the AST nodes they describe. Span is retained for error messages only, not as a lookup key. See Sections 3.2–3.4 for details and Section 4.3 for size analysis.

### 3.2 `resolved_call` on `Expr::Apply`

Add to `Expr::Apply` in `crates/cranelisp-types/src/ast.rs`:

```rust
Expr::Apply {
    callee: Box<Expr>,
    args: Vec<Expr>,
    span: Span,
    /// How this call was resolved by the typechecker.
    /// None before typecheck; Some after body checking.
    /// Boxed to avoid bloating the Expr enum (see §4.3).
    #[serde(default)]
    resolved_call: Option<Box<ResolvedCall>>,
    #[serde(default)]
    inferred_type: Option<Box<Type>>,
}
```

This requires `Expr` to be mutable during inference. Currently, `check_form_body_single_defn` takes `defn: &Defn` (immutable reference). The change: typecheck operates on a **clone** of the `Defn` for body checking (it already clones for constrained-fn storage), and the annotated clone is what gets written to `ModuleEntry::Def.ast` in Step 1a.

### 3.3 `inferred_type` on Every `Expr` Node

Add to every `Expr` variant in `crates/cranelisp-types/src/ast.rs`:

```rust
Expr::Apply {
    callee: Box<Expr>,
    args: Vec<Expr>,
    span: Span,
    #[serde(default)]
    resolved_call: Option<Box<ResolvedCall>>,
    #[serde(default)]
    inferred_type: Option<Box<Type>>,
}

Expr::Let {
    bindings: Vec<(Symbol, Expr)>,
    body: Box<Expr>,
    span: Span,
    #[serde(default)]
    inferred_type: Option<Box<Type>>,
}

// ... same pattern for all variants
```

Every `Expr` variant gains `inferred_type: Option<Box<Type>>`. Using `Box<Type>` keeps the field at 8 bytes (pointer with null niche optimization for `Option`). Before typecheck, all nodes have `None`. Typecheck writes `Some(Box::new(ty))` during inference.

This **eliminates `HashMap<Span, Type>` entirely** — no more Span-keyed side maps. Types are co-located with the AST nodes they describe. Spans are retained only for error messages, not as lookup keys. This is the pipeline-v4.md §9.1 target:

> "Typecheck writes resolved calls and expression types **directly onto AST nodes** — not into side maps keyed by Span."

**Why not `HashMap<Span, Type>` on `Defn`?** Span is a fragile key — it's a byte-offset reverse lookup that assumes spans are unique per expression within a function. Synthesized code (macro expansion, default methods) uses synthetic spans to avoid collisions, but the fundamental problem is architectural: Span carries no structural relationship to the AST. Putting the type directly on the node eliminates an entire class of bugs (span collisions, stale spans, missing entries) and makes the AST self-describing.

### 3.4 How Typecheck Populates the Annotations

**Design principle**: `check_form(CheckBody)` returns a fully annotated `Defn`. No downstream enrichment from side maps. No batch post-passes. The returned `Defn` has:
- All `inferred_type` fields concrete (no `Var(N)`) — final substitution applied
- All `resolved_call` fields populated — including deferred trait calls, auto-curry, overloads
- Ready to write directly to `ModuleEntry::Def.ast`
- Ready to compile immediately (e.g., macro clause path) without any enrichment

**Why per-defn completion is possible**: The post-passes that currently run in batch in `finalize_check_result_inner` appear to need cross-defn information, but they do not. Each defn's body checking creates fresh type variables via `register_defn_signature`, and cross-defn calls instantiate the callee's scheme with fresh vars. All type variables within a single defn's body are fully determined by the end of that defn's body check. Specifically:

1. **`resolve_deferred_trait_calls`** — already called per-defn in `check_form_body_single_defn` (line 670). It reads `state.expr_types` for argument types and the trait registry (symbol table) for impls. Both are available immediately after body check. The second pass in `finalize_check_result_inner` (Phase 3, line 917) is a safety net that adds no new information — substitutions from other defns do not refine this defn's type variables.

2. **`resolve_pending_overloads`** — processes `state.pending_overload_resolutions`, which accumulates entries during `infer_expr`. These entries contain type variables that are resolved via `apply(&state.subst, t)`. Since the substitution is fully determined after body check, this can run per-defn.

3. **`resolve_auto_curry`** — processes `state.pending_auto_curry`, same pattern as overloads. Uses `apply_subst` to resolve types. Can run per-defn.

4. **Final substitution walk** — `apply(&state.subst, ty)` on all `inferred_type` fields. The substitution is complete after body check.

**The flow inside `check_form(CheckBody)`**:

```
check_form(CheckBody)
  └─ check_form_body_single_defn(state, defn, accumulator)
       1. Clone the Defn to get a mutable copy
       2. check_defn_body(state, &mut defn_clone, param_types, ret_ty)
          └─ infer_expr(&mut expr) annotates during inference:
             - expr.set_inferred_type(Some(Box::new(ty))) on every node
             - apply.resolved_call = Some(Box::new(resolution)) on Apply nodes
             (types are pre-substitution; some resolved_calls are None)
       3. Per-defn post-passes on the mutable clone:
          a. resolve_deferred_trait_calls(state, &mut defn_clone.body())
             — fills resolved_call on Apply nodes that were deferred
          b. resolve_pending_overloads_for_defn(state, &mut defn_clone)
             — fills resolved_call for multi-sig dispatch sites
          c. resolve_auto_curry_for_defn(state, &mut defn_clone)
             — fills resolved_call for partial application sites
       4. Final substitution walk on defn_clone:
          apply_subst_to_defn(&state.subst, &mut defn_clone)
             — replaces Var(N) with concrete types on all inferred_type fields
       5. Return the fully annotated defn_clone
  └─ Caller writes defn_clone to ModuleEntry::Def.ast
```

**`&mut Expr` threading**: `infer_expr` takes `&mut Expr`. Since the `Defn` is cloned at the start of body checking, all mutation is on the clone — the original AST is untouched. The clone becomes the annotated version stored on `ModuleEntry::Def.ast`.

**Per-defn post-pass variants**: The current `resolve_pending_overloads` and `resolve_auto_curry` drain ALL pending entries from `CheckState` (via `std::mem::take`). The per-defn variants (`resolve_pending_overloads_for_defn`, `resolve_auto_curry_for_defn`) drain only the entries accumulated during this defn's body check. Since `check_form(CheckBody)` processes one defn at a time, the pending queues contain only entries from the current defn when these post-passes run. The `std::mem::take` pattern still works — the queues are empty before each defn's body check begins (cleared by the previous defn's post-passes or empty at the start).

**Helper method on Expr**: Add `fn set_inferred_type(&mut self, ty: Option<Box<Type>>)` that matches on self and sets the field. This keeps the mutation localized — callers don't need to match on every variant.

**Side map elimination**: With per-defn completion, `state.expr_types` and `state.method_resolutions` become unnecessary for annotation. They may be retained temporarily for verification (Section 3.5) and for `FormCheckResult` fields consumed by the accumulator, but they are no longer the source of truth. See Section 3.8 for `FormCheckResult` field disposition.

### 3.5 Dual-Write Verification

During the migration period, both paths are populated:

- **Old path**: `FormCheckResult.method_resolutions` and `FormCheckResult.expr_types` flow into `ModuleCheckAccumulator`, then into `CheckResult`.
- **New path**: `Expr.inferred_type` and `Expr::Apply.resolved_call` on the annotated AST stored in `ModuleEntry::Def.ast`.

Verification assertions (debug-only, via `debug_assert!`) run **inside `check_form(CheckBody)` after per-defn post-passes and final substitution complete** — i.e., on the fully annotated `Defn` before it is returned.

Verification assertions:

1. Walk the annotated `Defn` returned by `check_form_body_single_defn`.
2. For every `Expr` node with `inferred_type.is_some()`, assert that `state.expr_types` (after `apply(&state.subst, ty)`) has an entry for that span with the same type.
3. For every `Expr::Apply` with `resolved_call.is_some()`, assert that `state.method_resolutions` has a matching entry for that span.
4. Assert completeness: every entry in the side maps for this defn's spans has a corresponding AST annotation. This catches cases where a side map has an entry but the AST node was not updated.

These assertions run in test builds and CI. They do not run in release builds (no performance impact). They are removed in Step 1d when the side maps are deleted.

### 3.6 Per-Defn Post-Passes (Inside `check_form`)

All annotation post-passes run per-defn inside `check_form(CheckBody)`, immediately after `infer_expr` returns. There is no batch post-pass phase for annotation purposes. The `finalize_check_result_inner` phase continues to exist for non-annotation concerns (generalization, constrained-fn detection, monomorphisation dispatch), but it does NOT touch AST nodes.

#### 3.6.1 Post-Passes That Run Per-Defn

Each post-pass takes `&mut Defn` (the clone from Section 3.4) and writes directly to AST nodes:

**`resolve_deferred_trait_calls`** (`infer.rs:495`): Walks the `&mut Expr` tree to resolve trait method calls deferred during `infer_expr` because the concrete type was not yet known. Currently takes `&Expr` and writes to `state.method_resolutions`. The change: take `&mut Expr`, and when a resolution is found for an `Expr::Apply` node, write `resolved_call = Some(Box::new(resolution))` directly on the node. This pass already runs per-defn in `check_form_body_single_defn` (line 670); the change is gaining `&mut` access and writing to the node instead of (or in addition to) the side map.

**Why per-defn is sufficient**: This pass reads `state.expr_types` for argument types and the trait registry for impls. Both are available after body check. The pass does NOT need types from other defns' bodies — each defn's type variables are fresh (allocated by `register_defn_signature`), and cross-defn calls instantiate the callee's scheme with fresh vars. The second pass of `resolve_deferred_trait_calls` in `finalize_check_result_inner` (Phase 3, line 917) currently exists as a safety net but adds no new resolutions — it can be removed.

**`resolve_pending_overloads_for_defn`**: Drains `state.pending_overload_resolutions` (which contains only entries from the current defn's body check) and resolves multi-sig dispatch. For each resolved overload, walks the `&mut Defn` to find the `Expr::Apply` node by span and sets its `resolved_call`. This replaces the batch `resolve_pending_overloads` for annotation purposes.

**`resolve_auto_curry_for_defn`**: Drains `state.pending_auto_curry` and resolves partial application sites. Same pattern: resolve, then walk the `&mut Defn` to set `resolved_call` on the matching `Expr::Apply` node.

**Multi-sig variant handling**: For `DefnMulti` forms, `check_form_body_multi_sig` checks each variant's body independently. Each variant gets its own clone, post-passes, and substitution walk. The internal variant defns (`foo__v0`, `foo__v1`) are each fully annotated before being written to `ModuleEntry::Def.ast`.

#### 3.6.2 Final Substitution Walk

After all per-defn post-passes complete (still inside `check_form`), a final walk applies `apply(&state.subst, ty)` to every `inferred_type` on every `Expr` node in the annotated `Defn`. This replaces `Var(N)` type variables with their concrete bindings.

```rust
fn apply_subst_to_defn(subst: &Subst, defn: &mut Defn) {
    for variant in &mut defn.variants {
        apply_subst_to_expr(subst, &mut variant.body);
    }
}

fn apply_subst_to_expr(subst: &Subst, expr: &mut Expr) {
    if let Some(ty) = expr.inferred_type_mut() {
        *ty = Box::new(apply(subst, ty));
    }
    // Recurse into children (Let bindings, Apply args, Match arms, etc.)
    // ... same recursive structure as resolve_deferred_trait_calls
}
```

This runs per-defn, not in batch. The current bulk resolution in `finalize_check_result_inner` (lines 998-1002 of `program.rs`) that builds a `HashMap<Span, Type>` by applying substitution to accumulated `expr_types` becomes unnecessary for annotation — it may be retained for side-map verification during the dual-write period.

#### 3.6.3 `finalize_check_result_inner` — What Remains

With per-defn annotation, `finalize_check_result_inner` no longer touches AST nodes. Its remaining responsibilities:

1. **Phase 2 — Generalize**: finalize function schemes, clear false-positive constrained markers. No AST changes.
2. ~~Phase 3 — `resolve_deferred_trait_calls`~~: **Removed.** Already handled per-defn in `check_form(CheckBody)`.
3. **Pass 2.5 — `resolve_multi_sig_overloads`**: Produces overload dispatch info. AST annotation is handled per-variant in `check_form_body_multi_sig`.
4. **Pass 3 — `detect_constrained_fns`**: Identifies constrained functions. No AST changes.
5. **Pass 4 — `pass4_monomorphise`**: Generates mono defns. Each mono defn is annotated during its generation (see Section 3.6.4).
6. ~~Pass 5 — `resolve_pending_overloads` / `resolve_auto_curry`~~: **Removed from batch.** Already handled per-defn.
7. ~~Final substitution walk~~: **Removed from batch.** Already handled per-defn.
8. ~~AST write to `ModuleEntry::Def.ast`~~: **Removed from batch.** Each `check_form(CheckBody)` writes its own result.

The `working_program: &[TopLevel]` parameter to `finalize_check_result_inner` is still needed for Pass 2.5 (multi-sig structure) and Pass 3 (constrained-fn detection), but NOT for any AST mutation.

#### 3.6.4 Mono Defn Annotation

Monomorphised defns are generated in `pass4_monomorphise` → `monomorphise_constrained_fn` → `recheck_body_for_mono`. The mono defn follows the same per-defn annotation pattern:

1. `recheck_body_for_mono` calls `check_defn_body_with_types(state, &mut mono_defn, ...)` — `infer_expr` annotates during inference.
2. Per-defn post-passes run on the `&mut mono_defn`:
   - `resolve_deferred_trait_calls(state, &mut mono_defn.body())`
   - `resolve_auto_curry_for_defn(state, &mut mono_defn)`
   - `resolve_inner_constrained_calls` entries applied to AST nodes
3. Final substitution walk on the mono defn.
4. The `MonoDefn.defn` is fully annotated before being returned.

When `pass4_monomorphise` writes the mono defn to `ModuleEntry::Def.ast` (per Section 5.3), the AST is already complete. No `annotate_defn_from_maps` call is needed.

The `MonoDefn` struct's `resolutions` and `expr_types` fields become redundant once per-defn annotation is in place. They are retained during the dual-write period for verification, then removed in Step 1d.

#### 3.6.5 REPL Path

The REPL paths follow the same per-defn pattern. Each entry point produces a fully annotated AST before returning:

**`check_repl_input_inner` for `TopLevel::Expr`**: The expression is wrapped in a synthetic `__expr` defn. The same per-defn flow applies: `infer_expr` on `&mut expr`, per-defn post-passes (`resolve_auto_curry_for_defn`, `monomorphise_expr_calls` with `&mut` AST propagation), final substitution walk. The annotated expression is returned before `build_repl_result`.

**`check_single_defn` for single-sig `TopLevel::Defn`**: Already has its own per-defn flow (register, check body, resolve deferred traits, generalize). The changes are:
1. Clone the `Defn` and pass `&mut` to body checking and post-passes.
2. After generalize: `resolve_auto_curry_for_defn(state, &mut defn_clone)`.
3. `monomorphise_expr_calls` with `&mut` propagation to AST nodes.
4. Final substitution walk on `defn_clone`.
5. Write `defn_clone` to `ModuleEntry::Def.ast`.

Note: `check_single_defn` stores the *original* `defn` (not the annotated clone) in `ConstrainedFn.defn`. This is correct — the constrained-fn template stores the original for later monomorphisation.

**`check_repl_multi_sig` for multi-sig `TopLevel::Defn`**: Same per-variant pattern as batch multi-sig (Section 3.6.1). Each variant is annotated independently.

#### 3.6.6 Macro Clause Path

`compile_macro_clause_with_state` in `src/worker.rs` calls `check_form(Register)` then `check_form(CheckBody)` per form, WITHOUT calling `finalize_check_result`. This is what motivated the per-defn annotation design.

With per-defn completion, the macro clause path works without modification:

```
compile_macro_clause_with_state
  └─ check_form(Register) — registers signature
  └─ check_form(CheckBody) — returns fully annotated Defn
       (post-passes and substitution already applied)
  └─ compile_and_register_defn_shared — compiles the annotated Defn
```

No `finalize_check_result` call is needed. No `enrich_defn_from_side_maps` workaround is needed. The annotated `Defn` returned by `check_form(CheckBody)` is ready to compile immediately.

This eliminates a structural asymmetry in the current codebase: the batch path runs `finalize_check_result_inner` (which does batch annotation via `annotate_defn_from_maps`), the macro clause path skips it (producing incompletely annotated ASTs that require the `enrich_defn_from_side_maps` workaround in the integration layer), and the REPL path has its own annotation logic. With per-defn completion, all three paths produce the same output from `check_form(CheckBody)`.

#### 3.6.7 No Integration-Layer Enrichment

`enrich_defn_from_side_maps` in `src/worker.rs` and `crates/cranelisp-backend/src/lib.rs` exists because `check_form(CheckBody)` did not produce complete output. The integration layer had to patch up annotations from `CheckResult`'s side maps using Span-keyed lookup with "overwrite if `contains_var`" heuristics — a fragile workaround.

With per-defn completion inside `check_form(CheckBody)`, this function is eliminated entirely. It never needs to exist because:
- `check_form(CheckBody)` returns a `Defn` with all `inferred_type` fields concrete and all `resolved_call` fields populated
- The caller writes this `Defn` to `ModuleEntry::Def.ast`
- Codegen reads `ModuleEntry::Def.ast` directly
- No intermediate enrichment layer exists

This is the pipeline-v4.md target: typecheck writes, codegen reads, no intermediate enrichment layer.

### 3.7 Trait Impl Method Annotation

Trait impl methods follow the same per-defn annotation pattern as regular defns. `check_impl_method` produces a fully annotated `Defn` — no batch post-pass or integration-layer enrichment is needed.

#### 3.7.1 The Pattern

1. **Clone**: `check_impl_method` clones the `&Defn` to get a mutable copy.
2. **Body check with annotation**: `check_defn_body_with_types(state, &mut defn_clone, ...)` — `infer_expr` receives `&mut Expr` and annotates `inferred_type` and initial `resolved_call` during inference.
3. **Per-defn post-passes**: Same as regular defns (Section 3.4 step 3):
   - `resolve_deferred_trait_calls(state, &mut defn_clone.body())`
   - `resolve_pending_overloads_for_defn(state, &mut defn_clone)`
   - `resolve_auto_curry_for_defn(state, &mut defn_clone)`
4. **Final substitution walk**: `apply_subst_to_defn(&state.subst, &mut defn_clone)`.
5. **Write to symbol table**: Write the fully annotated `Defn` to `ModuleEntry::Def.ast` under the mangled name (e.g., `Display.show$Option$Int`). The entry already exists from Pass 1 registration.

#### 3.7.2 HKT Impl Methods

`check_hkt_impl_method` follows the identical pattern. HKT resolution (constructor variable substitution, ADT application) happens before body checking when building `param_types` and `ret_ty`. Once concrete types are determined, the body-checking and annotation path is the same as non-HKT methods.

#### 3.7.3 Consequence for the Integration Layer

Once trait impl methods have populated `ast` fields on their `ModuleEntry::Def` entries, `compile_regular_defns` finds them by iterating symbol table entries — the same path as any user-defined function. The `TopLevel::TraitImpl(_) => {}` skip in the codegen dispatch loop is correct: the methods are already on the symbol table under mangled names with self-contained annotated ASTs.

### 3.8 `FormCheckResult` Field Disposition

`FormCheckResult` currently carries:

| Field | Purpose | After per-defn annotation |
|-------|---------|---------------------------|
| `method_resolutions` | Side map of resolved calls | **Redundant** — now on AST nodes. Retained during dual-write for verification (Section 3.5), then removed in Step 1d. |
| `expr_types` | Side map of expression types | **Redundant** — now on AST nodes. Same disposition as `method_resolutions`. |
| `constrained_fn` | Detected constrained fn name | **Kept** — needed by accumulator for Pass 3 constrained-fn detection. |
| `mono_defns` | Mono specializations | **Kept** — generated during Pass 4 in `finalize_check_result_inner`. Mono defns are annotated during generation (Section 3.6.4). |
| `default_method_defns` | Default trait method bodies | **Kept** — generated during Pass 1 trait impl processing. Annotated during their own body check. |
| `multi_sig_defns` | Multi-sig internal variant defns | **Kept** — generated by Pass 2.5. Annotated per-variant. |
| `warnings` | Accumulated warnings | **Kept** — unchanged. |
| `call_graph_edges` | Call graph for scheduler | **Kept** — unchanged. |

**The annotated `Defn` itself** is a new implicit output of `check_form(CheckBody)`: it is written to `ModuleEntry::Def.ast` by the caller (or by `check_form` internals). It does not appear on `FormCheckResult` because it flows through the symbol table, not through the accumulator.

**Step 1d target**: Remove `method_resolutions` and `expr_types` from `FormCheckResult`, `ModuleCheckAccumulator`, and `CheckResult`. The annotated AST on `ModuleEntry::Def.ast` is the single source of truth for types and resolutions.

## 4. Expr Size Impact Analysis

### 4.1 Current Sizes (estimated, 64-bit target)

Rust enum size = max variant size + discriminant (+ padding). Key component sizes:

| Type | Size (bytes) | Components |
|------|-------------|------------|
| `Span` | 8 | `u32 + u32` |
| `Symbol` | 24 | `String` (ptr + len + cap) |
| `Box<Expr>` | 8 | pointer |
| `Vec<Expr>` | 24 | `ptr + len + cap` |
| `Vec<Symbol>` | 24 | `ptr + len + cap` |
| `bool` | 1 | |
| `i64` / `f64` | 8 | |

Current `Expr` variants (payload only, excluding discriminant):

| Variant | Fields | Payload (bytes) |
|---------|--------|-----------------|
| `IntLit` | `i64 + Span` | 16 |
| `FloatLit` | `f64 + Span` | 16 |
| `BoolLit` | `bool + Span` | 9 (padded to 16) |
| `StringLit` | `String + Span` | 32 |
| `Var` | `Symbol + Span` | 32 |
| `Let` | `Vec<(Symbol, Expr)> + Box<Expr> + Span` | 40 |
| `If` | `3 * Box<Expr> + Span` | 32 |
| `Lambda` | `Vec<Symbol> + Vec<Option<TypeExpr>> + Box<Expr> + Span` | 56 |
| `Apply` | `Box<Expr> + Vec<Expr> + Span` | 40 |
| `Match` | `Box<Expr> + Vec<MatchArm> + Span + bool` | 40 |
| `VecLit` | `Vec<Expr> + Span` | 32 |
| `Annotate` | `TypeExpr + Box<Expr> + Span` | variable, ~56 |
| `Trace` | `Vec<Symbol> + Box<Expr> + Span` | 40 |
| `ParBind` | `Vec<(Symbol, Expr)> + Box<Expr> + Span` | 40 |

The current `Expr` enum size is dominated by `Lambda` and `Annotate` (largest variants). Estimated total: **~64 bytes** (largest payload + 8 bytes discriminant + alignment).

### 4.2 Impact of Approach A (rejected): `Option<Type>` on every variant

`Type` is a recursive enum containing `Vec<Type>`, `Box<Type>`, `FQTypeName` (two `String` fields). Estimated `Type` size: **~56 bytes** (the `Fn` variant with `Vec<Type> + Box<Type>`).

`Option<Type>` adds ~56 bytes to every variant's payload. Since Rust enum size equals the largest variant, and most variants are already smaller than `Lambda`, this would push every variant up to Lambda's payload + 56 = ~112+ bytes. **Total `Expr` enum size: ~120 bytes** -- nearly doubling it.

Every `Expr` construction site (14 variants across frontend, AST builder, macro expander, test helpers) would need to add `inferred_type: None`. This is a widespread, error-prone change.

**Conclusion**: Approach A is rejected. The size bloat is unacceptable.

### 4.3 Impact of Chosen Approach: `resolved_call` + `inferred_type` on Every Variant

Both new fields use `Option<Box<_>>` — 8 bytes each (pointer with null niche optimization).

**Per-variant impact**: Every variant gains `inferred_type: Option<Box<Type>>` (+8 bytes). `Apply` also gains `resolved_call: Option<Box<ResolvedCall>>` (+8 bytes).

**Enum size impact**: The Rust enum is sized to its largest variant. Adding 8 bytes to every variant increases the enum from ~64 to ~72 bytes (+12.5%). Adding 16 bytes to `Apply` makes it ~56 bytes — still smaller than `Lambda` (~64 with the extra 8), so `Lambda` remains the largest variant. **Total `Expr` enum size: ~72 bytes.**

This is acceptable. The 12.5% increase is modest, and the architectural benefit (no Span-keyed side maps, self-describing AST) is substantial.

**Construction site impact**: Every `Expr` construction site must add `inferred_type: None`. This is mechanical — a project-wide search-and-replace. `Apply` sites also add `resolved_call: None`. Both fields are `#[serde(default)]` for cache backward compatibility.

**Memory impact**: Most `inferred_type` fields are `None` before typecheck. After typecheck, every node has `Some(Box::new(ty))`. For a function with 100 expression nodes, this is 100 heap allocations of `Type` — comparable to the current `HashMap<Span, Type>` which allocates the same `Type` values plus hashmap overhead. Net memory usage is comparable or better (no hash table overhead).

## 5. Mono Defns and Default Method Defns Placement

### 5.1 Current Location

`CheckResult` carries:
- `mono_defns: Vec<MonoDefn>` -- monomorphised specializations (e.g., `add$Int+Int`) generated during Pass 4.
- `default_method_defns: Vec<Defn>` -- default trait method implementations expanded during Pass 1 trait impl processing.

Both are consumed by `compile_to_module` as additional functions to compile.

### 5.2 Target: Separate `ModuleEntry::Def` Entries

Per pipeline-v4.md Section 9.1, mono specializations and default method implementations are separate `ModuleEntry::Def` entries on the symbol table with their own `ast` fields. This aligns with the principle that the symbol table is the single store.

### 5.3 How Typecheck Registers Them

**Mono defns**: During `finalize_check_result` (Pass 4, `pass4_monomorphise`), the typechecker generates mono specializations. Currently these are returned as `Vec<MonoDefn>` on `CheckResult`. The change:

1. For each `MonoDefn`, typecheck creates a `ModuleEntry::Def` with:
   - `scheme`: the monomorphised (fully concrete) scheme
   - `kind`: `DefKind::UserFn { constrained_fn: None }` (it is already fully specialized)
   - `ast`: `Some(mono_defn.defn)` — the mono defn's AST nodes carry `inferred_type` and `resolved_call` annotations directly, populated during monomorphisation (same per-node annotation as regular defns)
   - `got_slot`: allocated via `allocate_got_slot()`
   - `param_names`: from the defn's params
   - `callees`: extracted from the mono defn's resolutions
2. The entry is inserted into the module's symbol table under the mangled name (e.g., `add$Int+Int`).
3. The `constrained_fn_names` set is still returned (as part of `CheckOutput` -- see Section 6) so the integration layer knows which base names have specializations.

**Default method defns**: During `check_form(RegisterSig)` for `TraitImpl` forms, the typechecker expands default method bodies. Currently these are returned as `Vec<Defn>` on `FormCheckResult.default_method_defns`. The change:

1. After expanding a default method body, typecheck creates a `ModuleEntry::Def` for the method with the mangled impl name (e.g., `Display.show$MyType`).
2. The entry gets `ast: Some(method_defn)` after body checking.
3. The entry is inserted into the module's symbol table.

In both cases, the entries look identical to regular user-defined functions from codegen's perspective. `compile_to_module` compiles them by name, reading `ast` and `scheme` from the symbol table. Types and resolved calls are on the AST nodes themselves.

### 5.4 Timing Consideration

Mono defns are generated during `finalize_check_result`, which runs after all forms are body-checked. This means their symbol table entries appear after the per-form processing loop completes. This is fine for the v4 pipeline: codegen workers do not start compiling until typecheck notifies completion (`notify_typecheck_done`). The mono entries exist by that point.

For the REPL (Additive strategy), mono defns generated during eval are registered on the current module's symbol table and persist across evals. This matches the existing behavior where mono defns are compiled and their code pointers stored in the GOT.

Default method defns are generated during Pass 1 (signature registration). Their bodies must be checked in Pass 2 like regular defns. The current flow already handles this: `default_method_defns` are accumulated and then fed into the Pass 2 body-checking loop. The change is that after body checking, they get `ast` written to their `ModuleEntry::Def` entry, same as regular defns.

<!-- FIXME(/typecheck): Sprint 57 Wave 2 review I-1 — `MonoDefn.resolutions` and `MonoDefn.expr_types` at `crates/cranelisp-types/src/check.rs:43-50` are Span-keyed side maps retained inside typecheck after the Phase-1 AST-annotation migration. No cross-crate consumer reads them post-Wave-2. The `Defn` inside `MonoDefn` is already annotated by `monomorphise_call` in `traits.rs`, so the side maps are redundant — `annotate_defn_from_maps` could read annotations off AST nodes directly. Either drop the fields (making `MonoDefn` a newtype wrapping `Defn`) or document the retention rationale and schedule elimination. See `design/review/sprint57-wave2-review.md` I-1. -->

## 6. CheckResult Rename

`CheckResult` currently serves as the boundary type between typecheck and codegen. After Step 1d, it no longer crosses crate boundaries. Its remaining role:

- **Warnings**: `Vec<Warning>` -- consumed by the integration layer for display.
- **Display info**: `Option<DisplayInfo>` -- consumed by the REPL for output formatting.
- **Constrained fn names**: `HashSet<Symbol>` -- consumed by the integration layer for REPL on-demand monomorphisation.

Renamed to `CheckOutput` to reflect that it is a typecheck-internal output type, not a cross-boundary result. The rename happens in Step 1d when the boundary usage is removed.

```rust
/// Output from typecheck after all forms are processed.
/// Internal to the typecheck crate (not a boundary type).
pub struct CheckOutput {
    pub warnings: Vec<Warning>,
    pub display: Option<DisplayInfo>,
    pub constrained_fn_names: HashSet<Symbol>,
}
```

The `method_resolutions`, `expr_types`, `mono_defns`, and `default_method_defns` fields are removed -- they now live on `ModuleEntry::Def.ast` entries in the symbol table.

## 7. Sketch Comparison

The sketch (`sketch/src/typechecker.rs`) used the same side-map approach: `expr_types: HashMap<Span, Type>` and `method_resolutions: HashMap<Span, ResolvedCall>` on `TypeChecker`, drained into `CheckResult` and passed to codegen. The sketch never co-located types with AST nodes.

The sketch's approach worked for a single-threaded, single-module-at-a-time prototype. The reimplementation's concurrent pipeline makes this untenable: when multiple workers process different modules simultaneously, a global `CheckResult` that aggregates all resolution data cannot work. The per-entry annotation approach (types and resolutions on `ModuleEntry::Def.ast`) provides natural per-symbol isolation that concurrent workers can read independently.

The sketch's `resolve_expr_types()` method (line 661) applied the final substitution to all expr types in bulk. The reimplementation applies substitution per-defn inside `check_form(CheckBody)`, immediately after body checking and post-passes complete. This is more granular than the sketch's bulk approach — each defn's AST is fully resolved before `check_form` returns.

**Divergence**: The reimplementation annotates AST nodes with both resolved calls and inferred types. The sketch did not — it used Span-keyed side maps for both. This is a deliberate improvement: it eliminates the fragile Span-keyed indirection (byte-offset reverse lookup) and makes the AST self-describing for codegen. Span is retained for error messages only, not as a data lookup key.

## 8. Edge Cases

### 8.1 Span Collisions (Eliminated)

The previous `HashMap<Span, Type>` approach was vulnerable to span collisions — synthesized code could produce duplicate spans. The per-node `inferred_type` approach eliminates this entirely: types are stored on the AST node itself, not looked up by span. No span uniqueness assumption is required.

### 8.2 Multi-sig Variant Bodies

Multi-sig `DefnMulti` forms produce internal variant entries (`foo__v0`, `foo__v1`). Each gets its own `ast: Some(synthetic_defn)` with `inferred_type` and `resolved_call` annotations on its AST nodes. The base name entry (`foo`) has `ast: None` and `DefKind::Overloaded`. No special handling needed.

### 8.3 Constrained Polymorphic Function Templates

A constrained fn template (e.g., `(defn add [x y] (+ x y))`) has its `ast` set to the template body. The template is never compiled directly -- only its monomorphised specializations are compiled. The template body on the `ModuleEntry::Def` serves as the source for generating specializations. The `inferred_type` annotations on the template's AST nodes are the unresolved (pre-mono) versions with type variables; each mono specialization clones the template body and re-annotates with fully resolved types and `resolved_call` entries.

### 8.4 REPL Additive Strategy

In REPL mode, redefining a function replaces the `ModuleEntry::Def` entry (including its `ast`). The old annotated `Defn` is dropped. Mono specializations from prior evals persist as separate entries until the typechecker snapshot/restore mechanism removes them on error.

### 8.5 Cache Serialization

`Defn`, `Expr`, `ResolvedCall`, and `Type` all derive `Serialize` + `Deserialize`. The new `inferred_type: Option<Box<Type>>` and `resolved_call: Option<Box<ResolvedCall>>` fields on `Expr` variants are standard `Option` types that serialize naturally. The `#[serde(default)]` attributes on these fields ensure backward-compatible deserialization of existing cache files (new fields default to `None`). Cache files written after this change include the annotated AST, enabling cache-hit modules to skip typecheck entirely (the symbol table already contains everything codegen needs). No `HashMap<Span, _>` serialization is involved.

---

## 9. Sprint 56 Wave 0 / Phase 2 Extension

Sprint 55 (Phase 1) established `ast: Option<Defn>` on `ModuleEntry::Def` for *regular* defns, default method defns, trait-impl methods, internal multi-sig variant names (`foo__v0`), and the REPL `__expr` synthetic. Two categories still carry `ast: None` after Sprint 55:

1. **Mangled multi-sig variant entries** (e.g. `add$Int+Int`) — created by `register_mangled_variants` (`crates/cranelisp-typecheck/src/program.rs:1558`). The internal `foo__v0` entry (which does carry `ast: Some(_)`) is removed at line 1579, and the mangled entry is inserted without transferring the annotated body. The backend reconstitutes per-variant bodies at codegen time via `expand_multi_sig_defn` (`crates/cranelisp-backend/src/lib.rs:123, 379`).
2. **Mono specialisation entries** (e.g. `add$Float+Float`) — monomorphisation currently writes bodies into `CheckResult.mono_defns: Vec<MonoDefn>` (`program.rs:2526–2534` / `traits.rs:1147–1151`). Per-mono entries are NOT inserted into the symbol table by typecheck at all; the integration layer (`src/worker.rs:1254–1258`) inlines them into `program` with post-hoc enrichment from `mono.resolutions` and `mono.expr_types`.

Sprint 56 Wave 0 closes both gaps so that `compile_to_module(path, names, symbol_tables, module)` (the Step 2a signature — `pipeline-v4.md` §9.3) can uniformly read bodies from `ModuleEntry::Def.ast` — without `expand_multi_sig_defn`, without `finalize_module`'s program-inlining, and without integration-layer enrichment. This aligns with `/arch` review §5.1, §5.2, and §5.6, and with `pipeline-v4.md` §9.1 ("the typechecker expands DefnMulti into mangled variant entries ... each as a separate `ModuleEntry::Def` with its own `ast`"). Decision 21 in `design/arch/CLAUDE.md` applies: these mangled/mono entries carry `callees` like any other `ModuleEntry::Def`. Decision 22 (`defined_symbols()` is the shared codegen-compilable predicate) is implemented in §9.5.

**Wave 0 ordering (four steps, all land green before Step 2a opens):**

| Step | Covered by | Deliverable |
|------|------------|-------------|
| 1 | §9.3 | Mangled multi-sig variant entries carry `ast: Some(annotated)` (name rewritten to mangled). |
| 2 | §9.4 | Mono specialisation entries registered via `register_mono_entry` with `ast: Some(annotated)`. |
| 3 | §9.5 | `SymbolTable::defined_symbols()` iterator (the single codegen-compilable predicate). |
| 4 | §9.8 | **G7 pull-forward** — `got: GotTable` field on `SymbolTable`; `TypecheckProduct.got` deleted. |

Steps 1–3 were the original Wave 0 scope (Sprint 56 §9.3–§9.5). Step 4 is pulled forward from `pipeline-v4-roadmap.md` §Phase 3 Step 3a (G7) so that `compile_to_module` can stay at four parameters — the JIT path's `symbol_lookup_fn` closure needs to read the GOT base from `symbol_tables[m]` without a second DashMap argument. See §9.8 for the full rationale and change set.

All four steps must pass the `cargo nextest run` baseline (1590 passed / 22 failed) before Step 2a (`/backend` — `compile_to_module` unification) opens. Principle 11 (single pipeline, mode parameters) requires the four-param shape: deferring G7 would force a five-param `compile_to_module` (`... symbol_tables, typecheck_products, module ...`) or a bespoke `got_bases: &DashMap<ModuleFullPath, Arc<GotTable>>` parameter — either would violate the "one entry point, one code path" target in `pipeline-v4.md` §9.3.

### 9.1 Authoritative Table — `ast` Field Population

Every `ModuleEntry::Def` entry that codegen will compile MUST carry `ast: Some(_)` after Phase 2. The table below enumerates every category, the point at which the entry is registered, the `DefKind` variant it carries, where the body AST comes from, and the point at which the body is annotated (types + resolved calls written onto AST nodes).

| # | Category | Registered by | `kind` variant | Body source | Annotated during |
|---|----------|---------------|----------------|-------------|------------------|
| 1 | Regular defn | `check_form(Register)` (sig only) → body attached in `check_form_body_single_defn` | `UserFn { constrained_fn: None }` | Original `Defn` from `TopLevel::Defn` | `infer_expr` + per-defn post-passes inside `check_form(CheckBody)` (§3.4) |
| 2 | Multi-sig internal variant (`foo__v0`) | `register_defn_signature` (via `check_form_register_multi_sig`) | `UserFn { constrained_fn: None }` (or `Some` if detected constrained) | Synthetic single-variant `Defn` built from `DefnVariant` | `check_form_body_multi_sig` per-variant annotation (program.rs:832–852) |
| 3 | Multi-sig **mangled** variant (`add$Int+Int`) — **WAVE 0 NEW** | `register_mangled_variants` (program.rs:1558) | `UserFn { constrained_fn: None }` | **Clone internal-variant entry's already-annotated `ast`** (§9.3 option A) | *Already annotated* — inherits from internal-variant entry (no re-annotation) |
| 4 | Mono specialisation (`add$Float+Float`) — **WAVE 0 NEW** | New `register_mono_entry` helper called from `pass4_monomorphise` and `monomorphise_expr_calls` | `UserFn { constrained_fn: None }` | `MonoDefn.defn` (already annotated by `recheck_body_for_mono` + `annotate_defn_from_maps` + `apply_subst_to_defn` in `monomorphise_call`, traits.rs:1127–1146) | `monomorphise_call` (traits.rs:1127–1146) — before symbol-table insertion |
| 5 | Default method defn (trait decl default) | `check_impl_method_with_sig` default path | `UserFn { constrained_fn: None }` | Synthesized from the trait declaration's default body | `infer_expr` + per-defn post-passes inside `check_impl_method` (traits.rs:683–700) |
| 6 | Trait-impl method (`Display.show$Option$Int`) | `check_impl_method` / `check_hkt_impl_method` | `UserFn { constrained_fn: None }` | User-written method body, inserted under mangled name | `infer_expr` + per-defn post-passes inside `check_impl_method` (traits.rs:683–700) |
| 7 | REPL `__expr` synthetic | `check_repl_input_inner` for `TopLevel::Expr` | `UserFn { constrained_fn: None }` | Expression wrapped in zero-arg `__expr` defn | `infer_expr` + per-defn post-passes + final substitution inside `check_repl_input_inner` |

Rows 3 and 4 are the Wave 0 deliverables. Rows 1, 2, 5, 6, 7 landed in Sprint 55 (Phase 1).

### 9.2 Entries that remain `ast: None` post-Phase-2

| Category | `kind` | Why `ast: None` |
|----------|--------|-----------------|
| Multi-sig base name (e.g. `add`) | `Overloaded { variants }` | Dispatch index, not a compilable function. Its variants (row 3 above) are what codegen compiles. |
| Constrained polymorphic fn **template** (e.g. `add` before any call site) | `UserFn { constrained_fn: Some(ConstrainedFn) }` | Template is never compiled directly. Mono specialisations (row 4 above) replace it at codegen time. The `ConstrainedFn.defn` on the `kind` holds the template body for later mono generation — the entry's `ast` field stays `None` to signal "skip at codegen". |
| Primitives, special forms | `Primitive { ... }` / `SpecialForm { ... }` | Implemented in Rust or as IR patterns — no AST body exists. |
| `Constructor`, `TypeDef`, `TraitDecl`, `TraitImpl`, `Macro`, `PlatformDecl`, `Import`, `Reexport`, `Ambiguous` | — | Not `ModuleEntry::Def`. Codegen handles constructors synthetically; macros are compiled via their own path (each clause is a regular `Def`); type/trait declarations have no code; import/reexport forward to the source entry. |

`defined_symbols()` (§9.5) MUST exclude the `Overloaded` base entry and the constrained-fn template entry — both carry useful metadata but no compilable body.

### 9.3 Wave 0 Change Set — `register_mangled_variants` (Prerequisite 5.1)

**Current behaviour** (`program.rs:1558–1616`): For each resolved variant, remove the internal-name entry (`foo__v0`) and insert a fresh mangled entry (`add$Int+Int`) with `ast: None`. The synthetic single-variant `Defn` is pushed into `mangled_defns: Vec<Defn>` and returned for the caller to feed into `CheckResult`.

**Wave 0 change**: When removing the internal-name entry, **capture its annotated `ast`** (populated by `check_form_body_multi_sig` at program.rs:847–851) and write it onto the new mangled entry under the mangled name.

```rust
// program.rs register_mangled_variants — revised body sketch
for (concrete_params, concrete_ret, internal_name, idx) in resolved {
    let variant = &defn.variants[*idx];
    let mangled = mangle_sig(defn.name.as_ref(), concrete_params);
    let fn_ty = Type::Fn(concrete_params.clone(), Box::new(concrete_ret.clone()));
    let scheme = self.generalize(state, &fn_ty);

    let mut st = self.current_symbol_table_mut(state);
    // Take the internal-name entry so we can move its `ast` onto the mangled entry.
    let internal_entry = st.symbols.remove(internal_name.as_ref());
    let annotated_ast: Option<Defn> =
        if let Some(ModuleEntry::Def { ast, .. }) = internal_entry {
            // Rename the cloned Defn so defn.name == mangled (codegen uses this name).
            ast.map(|mut d| { d.name = mangled.clone(); d })
        } else { None };

    let slot = st.allocate_got_slot();
    st.insert(
        mangled.clone(),
        ModuleEntry::Def {
            scheme: scheme.clone(),
            visibility: defn.visibility,
            docstring: defn.docstring.clone(),
            param_names: variant.params.clone(),
            kind: Box::new(DefKind::UserFn { constrained_fn: None }),
            callees: Vec::new(),
            got_slot: Some(slot),
            trait_origin: None,
            ast: annotated_ast,           // <- Wave 0 NEW
        },
    );
    // ... existing mangled_defns.push / resolved_info.push stays for now;
    // remove in Step 2b when expand_multi_sig_defn is deleted.
}
```

**Annotation-source choice (key design decision)**: The cloned `Defn` inherits its annotations from the internal-variant entry's already-annotated `ast`, rather than re-running inference or re-walking side maps. Rationale:

1. **The internal variant is already authoritative.** `check_form_body_multi_sig` runs `check_defn_body` → `resolve_deferred_trait_calls` → `resolve_auto_curry` → `annotate_defn_from_maps` → `apply_subst_to_defn` per-variant, writing the fully annotated tree onto the internal-name entry's `ast` at program.rs:847–851. All post-passes that affect annotation have already run by the time `register_mangled_variants` executes.
2. **Re-annotating would duplicate work and risk divergence.** Running `annotate_defn_from_maps` a second time against the accumulator's side maps would re-do work for unchanged nodes and depend on the accumulator state being perfectly in sync with the internal entry's `ast`.
3. **The internal name is discarded anyway.** The entry is removed at line 1579. The annotated body is a by-product we'd otherwise throw away. Moving it onto the mangled entry is strictly cheaper than any re-derivation.
4. **The only structural edit is `defn.name`.** The cloned `Defn`'s `name` field must be rewritten from `foo__v0` to `add$Int+Int` so that when codegen does `table.get("add$Int+Int")` and reads `ast`, `defn.name == "add$Int+Int"`. No AST-node mutation is needed — `Expr` nodes are oblivious to the enclosing `Defn.name`.

**Batch vs REPL**: `check_form_body_multi_sig` runs in the batch path. The REPL path (`check_repl_multi_sig`, program.rs:2379+) uses the same internal-name → mangled-name transformation and goes through `register_mangled_variants` as well (program.rs:2444). No REPL-specific code path is needed — the annotation-transfer lives in one place.

**Consequence for the backend**: `expand_multi_sig_defn` in `crates/cranelisp-backend/src/lib.rs` becomes dead once callers pass mangled names (Step 2a) and the mangled entries carry `ast`. `/backend` deletes it in Step 2b. The `mangled_defns: Vec<Defn>` return value of `register_mangled_variants` can be collapsed into `Vec<()>` in Step 2b once `CheckResult.multi_sig_defns` is eliminated — Wave 0 keeps the existing return shape to stay green.

### 9.4 Wave 0 Change Set — `register_mono_entry` (Prerequisite 5.2)

**Current behaviour**: `pass4_monomorphise` (program.rs:2467) and `monomorphise_expr_calls` (program.rs:2545) generate `MonoDefn` values via `monomorphise_call` (traits.rs:1078). The `MonoDefn` carries a fully-annotated `defn` (traits.rs:1128–1146). The list is returned on `CheckResult.mono_defns`. `finalize_module` in `src/worker.rs:1254–1258` inlines them into `program` for codegen, re-running `enrich_defn_from_side_maps`. No symbol-table entry is created.

**Wave 0 change**: Introduce a new typecheck-internal helper `register_mono_entry(&self, state, mono: &MonoDefn) -> Result<(), CranelispError>` that inserts the mono specialisation as a `ModuleEntry::Def` with `ast: Some(mono.defn.clone())` on the current module's symbol table. Call it from `monomorphise_call` (immediately before `Ok(Some(mono_defn))`) so every generated mono shows up on the symbol table as soon as it is produced — both batch and REPL paths are covered.

```rust
// traits.rs (new) — register_mono_entry
fn register_mono_entry(
    &self,
    state: &mut CheckState,
    mono: &MonoDefn,
) -> Result<(), CranelispError> {
    // Build scheme from the mono defn's fn type (fully concrete — no generalization).
    let param_types = /* derived from mono.defn.params() via mono.expr_types */;
    let ret_ty      = /* derived from mono.defn.body() type */;
    let fn_ty       = Type::Fn(param_types.clone(), Box::new(ret_ty));
    let scheme      = crate::scheme::mono(fn_ty);

    let mut st = self.current_symbol_table_mut(state);
    let got_slot = Some(st.allocate_got_slot());
    st.insert(
        mono.defn.name.clone(),
        ModuleEntry::Def {
            scheme,
            visibility: mono.defn.visibility,
            docstring: mono.defn.docstring.clone(),
            param_names: mono.defn.params().to_vec(),
            kind: Box::new(DefKind::UserFn { constrained_fn: None }),
            callees: Vec::new(),   // populated by finalize_check_result's call-graph write
            got_slot,
            trait_origin: None,
            ast: Some(mono.defn.clone()),   // fully annotated; resolutions already applied
        },
    );
    Ok(())
}
```

**Call sites**: Insert the call at the end of `monomorphise_call` (traits.rs:1152) — right before `Ok(Some(mono_defn))`. This keeps both the batch path (`pass4_monomorphise` → `monomorphise_call`) and the REPL path (`monomorphise_expr_calls` → `monomorphise_call`) covered by one insertion point. De-duplication of mono variants is handled by the `seen: HashMap` tracking in `pass4_monomorphise` / `monomorphise_expr_calls`, which short-circuits before calling `monomorphise_call` a second time for the same mangled name — so `register_mono_entry` is invoked exactly once per mangled name.

**Annotation source (key design decision)**: `monomorphise_call` already produces a fully-annotated `mono_defn_ast` via `annotate_defn_from_maps` + `apply_subst_to_defn` at traits.rs:1140–1145, BEFORE constructing the `MonoDefn`. We clone `mono.defn` onto the entry as-is. Rationale:

1. The `recheck_body_for_mono` inner pass (traits.rs:1209) runs `check_defn_body_with_types` (which invokes `infer_expr`), then `resolve_auto_curry`, then captures per-specialization `resolutions` and `mono_expr_types`, then restores the parent state's side maps.
2. `monomorphise_call` then calls `resolve_inner_constrained_calls` to add `SigDispatch` entries for inner constrained calls (traits.rs:1120–1125).
3. `annotate_defn_from_maps` writes these onto the cloned AST; `apply_subst_to_defn` applies the final substitution.
4. All enrichment that `src/worker.rs:1254–1258` currently re-runs via `enrich_defn_from_side_maps` is **already baked into `mono.defn`** by the time `MonoDefn` is constructed. There is nothing left to patch up at the integration layer — the entry is codegen-ready.

**Consequence for the integration layer**: The inlining loop at `src/worker.rs:1254–1258` (mono) and the companion loop at `src/worker.rs:1245–1247` (default methods) are dead after Wave 0. `finalize_module` stops needing `CheckResult.mono_defns` and `CheckResult.default_method_defns` to populate `program`. This must be explicitly called out in `/int`'s Phase 2 design doc (the loop is owned by `/int`). Wave 0 retains `CheckResult.mono_defns` and `CheckResult.default_method_defns` as-is for the dual-write period — the symbol-table entries are a second, authoritative source; the `CheckResult` fields become slimming candidates tracked under the FIXME filed on `check.rs` (Phase 5 work, not this sprint).

**Impact on `finalize_module`** (src/worker.rs:1245–1258): Both the default-method-defn inlining loop and the mono-defn inlining loop become dead after Wave 0 closes. /int deletes them in Step 2a once `compile_to_module` reads bodies from symbol-table entries instead of `program`. They MUST remain in place during Wave 0 to preserve the 1590/22 baseline — Wave 0 is additive to the symbol table only.

### 9.5 `SymbolTable::defined_symbols()` — Shared Codegen Filter (Prerequisite 5.6)

Two callers need the same "codegen-compilable entries" predicate: Step 2a's `compile_to_module` caller (the priority worker / cache paths deciding which names to pass) and the backend's internal compile loop. `/arch` review §5.6 requires the filter to live in one place.

**Proposed API** on `SymbolTable` in `crates/cranelisp-types/src/module.rs`:

```rust
impl SymbolTable {
    /// Iterate over codegen-compilable entries: those with `ast: Some(_)`
    /// whose kind is NOT `Overloaded` (dispatch index — its mangled variants
    /// are compiled instead) and NOT `UserFn { constrained_fn: Some(_) }`
    /// (template — mono specializations are compiled instead).
    ///
    /// Callers:
    /// - `compile_to_module(path, names, ...)` — step 2a: backend enumerates names.
    /// - Priority worker (step 2b, in /int): decide which names to hand to
    ///   `compile_to_module`.
    /// - `constrained_fn_names` derivation (lib.rs:95–109) — collapses into this
    ///   same iterator pattern.
    pub fn defined_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry)> {
        self.symbols.iter().filter(|(_, entry)| match entry {
            ModuleEntry::Def { ast: Some(_), kind, .. } => match kind.as_ref() {
                DefKind::Overloaded { .. } => false,
                DefKind::UserFn { constrained_fn: Some(_) } => false,
                _ => true,
            },
            _ => false,
        })
    }
}
```

Notes:
- Returns `(&Symbol, &ModuleEntry)` so callers have access to both the name (for passing into `compile_to_module`) and the `ast` / `scheme` / `callees` (for call-graph walks).
- The filter is deliberately strict: a `ModuleEntry::Def` with `ast: None` is never compilable (whether pre-body-check, primitive, special form, Overloaded base, or constrained-fn template). Keeping the predicate `ast.is_some()`-first means adding new non-compilable categories never silently breaks codegen.
- No `Ambiguous` / `Import` / `Reexport` / `TypeDef` / `TraitDecl` / `TraitImpl` / `Macro` / `PlatformDecl` entries match — they are never `ModuleEntry::Def`.
- This method is read-only and cheap (a single pass over the `HashMap<Symbol, ModuleEntry>`). Callers that want the count can `.count()`; callers that need an owned list can `.collect()`. The backend's internal loop can iterate directly without intermediate collection.

**Centralisation of `constrained_fn_names`** (/arch condition 5): The existing inline computation at `crates/cranelisp-backend/src/lib.rs:95–109` scans the symbol table for `UserFn { constrained_fn: Some(_) }` entries. This becomes the negation of `defined_symbols()`'s second filter clause. Either expose a companion `constrained_fn_templates()` iterator, or inline the check at call sites — `/typecheck` and `/backend` align on one of these in Wave 1 (the doc update for `compile-to-module.md` by `/backend` is the forcing function).

### 9.6 Impact on `finalize_check_result_inner`

With mono entries registered eagerly by `register_mono_entry` (§9.4), the re-annotation loop at program.rs:1102–1152 becomes partly redundant:

- The multi-sig variant re-annotation path (program.rs:1107–1119) looks up `internal_name` (`foo__v0`). After Wave 0, internal names are removed by `register_mangled_variants` BEFORE `finalize_check_result_inner` runs — so this arm becomes a no-op in the batch path. It MUST be kept for the REPL-multi-sig path where internal names may persist. Conservative stance: leave the code in place at Wave 0; `/typecheck` revisits it in Phase 5 slimming.
- The regular-defn re-annotation path (program.rs:1121–1132) already runs after `check_form_body_single_defn`'s per-defn annotation and overwrites with final substitution. Still needed for cross-defn substitution refinement (e.g., constrained-fn call-site pinning). Keep at Wave 0.
- The trait-impl method re-annotation path (program.rs:1133–1148) — same as regular-defn. Keep at Wave 0.

Wave 0 is strictly additive at the symbol-table level — it does not remove any existing annotation path. The annotation-path consolidation is a Phase 5 cleanup tracked under the `CheckResult` slimming FIXME on `check.rs`.

### 9.7 Test Plan

**Existing coverage to re-run (no changes expected — must stay green at 1590/22):**
- `cargo nextest run -p cranelisp-typecheck` — all inference / multi-sig / mono tests
- `cargo nextest run -p cranelisp-backend` — object codegen + JIT backend unit tests
- `cargo nextest run -p cranelisp --test sketch_port` (baseline: 3 multi-sig JIT failures remain — Wave 0 does NOT fix them; Step 2b does)
- REPL smoke via repl demos: `ring4m.demo` and earlier

**New unit tests** (in `crates/cranelisp-typecheck/src/program.rs` under `#[cfg(test)] mod tests`):

1. `wave0_mangled_variant_carries_ast`:
   - Check a multi-sig program `(defn add ([:Int a :Int b] (add-i64 a b)) ([:Float a :Float b] (add-f64 a b)))`.
   - After `check()`, look up `add$Int+Int` and `add$Float+Float` on the current module's symbol table.
   - Assert both entries are `ModuleEntry::Def { ast: Some(_), kind: UserFn { constrained_fn: None }, .. }`.
   - Assert `ast.name == "add$Int+Int"` (not `add__v0` or `add`).
   - Assert the internal names `add__v0` / `add__v1` are NOT present in the table.
   - Negative: assert `add$Float+Int` is NOT present (no cross-variant entries).

2. `wave0_mangled_variant_ast_is_annotated`:
   - Same setup. Walk `ast`'s body recursively; assert every `Expr` has `inferred_type.is_some()`.
   - Assert the `Expr::Apply` for the inner `add-i64` call has `resolved_call.is_some()` with `ResolvedCall::BuiltinFn { name: "add-i64" }`.
   - Negative: assert NO `inferred_type` on the mangled `ast` is `Type::Var(_)` (final substitution applied).

3. `wave0_overloaded_base_has_no_ast`:
   - Same setup. Look up `add` (the base name).
   - Assert `ast: None` and `kind == DefKind::Overloaded { variants: [...] }`.

4. `wave0_mono_entry_registered`:
   - Check `(defn add [x y] (+ x y))` (constrained polymorphic) plus a caller `(defn use-add [] (add 1 2))`.
   - Assert `add` is registered with `kind: UserFn { constrained_fn: Some(_) }` and `ast: None`.
   - Assert `add$Int+Int` is registered with `kind: UserFn { constrained_fn: None }` and `ast: Some(_)`.
   - Assert the mono's `ast` body has fully concrete `inferred_type` values and `ResolvedCall` set on the `+` call site.
   - Assert the mono entry has a distinct `got_slot` from the template.

5. `wave0_defined_symbols_filters_correctly`:
   - Program combining: one regular defn, one multi-sig, one constrained polymorphic with mono, one trait impl, one type def, one import.
   - Assert `defined_symbols()` yields exactly:
     - the regular defn
     - `add$Int+Int`, `add$Float+Float` (mangled multi-sig variants)
     - the mono specialisations
     - the trait-impl mangled method(s)
   - Negative: assert the `Overloaded` base, the constrained-fn template, the type def, the import, and the trait-impl index entry are ALL absent from the iterator.

6. `wave0_repl_multi_sig_carries_ast`:
   - REPL path: `check_repl_input_inner` for a multi-sig `TopLevel::Defn`.
   - After the call, assert the mangled variants carry `ast: Some(_)` on the current module's table.
   - This exercises `check_repl_multi_sig` → `register_mangled_variants` (program.rs:2444).

**Step 4 (§9.8 G7 pull-forward) unit tests** (in `crates/cranelisp-types/src/module.rs` under `#[cfg(test)] mod tests`):

7. `wave0_symbol_table_new_has_empty_got`:
   - `let st = SymbolTable::new(ModuleFullPath::from("user"));`
   - Assert `st.got.base_ptr().is_null() == false` (GOT allocated eagerly at table construction; address stable for the table's lifetime).
   - Assert `st.got.load_slot(0).is_null()` and `st.got.load_slot(1).is_null()` — all slots start null.
   - Assert `st.next_got_slot == 0`.

8. `wave0_got_slot_allocation_monotonic`:
   - `let mut st = SymbolTable::new(...);`
   - `let a = st.allocate_got_slot(); let b = st.allocate_got_slot(); let c = st.allocate_got_slot();`
   - Assert `a == 0 && b == 1 && c == 2` (monotonic, no gaps, already covered by existing `next_got_slot` tests).
   - Negative: `allocate_got_slot()` MUST NOT mutate `st.got.base_ptr()` — capture `st.got.base_ptr()` before and after; assert equality.

9. `wave0_got_base_ptr_stable_across_reads`:
   - `let st = SymbolTable::new(...);`
   - `let p1 = st.got.base_ptr(); let p2 = st.got.base_ptr();`
   - Assert `p1 == p2` (stable address across multiple reads — `Box<[AtomicPtr<u8>; GOT_TABLE_SIZE]>` is not reallocated).
   - Negative: after `allocate_got_slot()`, `st.got.base_ptr()` MUST be equal to `p1` (allocation of a slot index is bookkeeping only; the GOT array is allocated at construction).

10. `wave0_got_store_load_through_symbol_table`:
    - Construct `SymbolTable`, allocate a slot, call `st.got.store_slot(slot, fake_ptr); assert_eq!(st.got.load_slot(slot), fake_ptr);` — duplicates `GotTable` tests but verifies the field wiring on `SymbolTable`.

11. `wave0_got_skipped_in_serde_round_trip`:
    - Serialize a `SymbolTable` with one entry and one allocated GOT slot via `serde_json::to_string()`.
    - Deserialize back into a fresh `SymbolTable`.
    - Assert the deserialized table has `next_got_slot == 1` (bookkeeping preserved) and a fresh GOT (`load_slot(0).is_null()`) — the `#[serde(skip)]` field reconstructs via `GotTable::new()` on load.
    - Rationale: cached symbol tables must NOT round-trip runtime pointers. Code pointers are re-filled at codegen time on cache hit (re-JIT or .o relocation).

**Integration test touchpoints** (no new tests required but should be verified):
- `tests/` multi-sig / constrained polymorphism integration tests must stay green.
- `sketch_port` 3 multi-sig JIT failures stay failing (fixed in Step 2b, not Wave 0).
- After Step 4 lands, `cargo check -p cranelisp` MUST fail if any code still references `TypecheckProduct.got` — this is the compile-time proof that G7 is complete. The deletion of the field is the forcing function; the test plan does not need a runtime assertion for it.

**Wave 0 exit gate**: All new unit tests pass; nextest baseline remains 1590 passed / 22 failed. If any previously-passing test fails, Wave 0 blocks and `/typecheck` investigates before `/backend` opens Step 2a.

### 9.8 G7 Pull-Forward — `GotTable` on `SymbolTable`

Steps 1–3 (§9.3–§9.5) make `SymbolTable` the single source of truth for AST bodies. Step 4 finishes the job: the GOT — the runtime memory region where code pointers live — moves off `TypecheckProduct` and onto `SymbolTable` itself. After this step, `symbol_tables[m]` carries everything codegen needs for module `m`: types, ASTs, GOT slot assignments, AND the GOT base pointer.

**Rationale (why pull G7 forward from Phase 3 into Sprint 56 Wave 0):** `pipeline-v4.md` §9.3 fixes `compile_to_module` at four parameters:

```rust
pub fn compile_to_module<M: Module>(
    module_path: ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    module: &mut M,
) -> Result<CompilationResult, CranelispError>
```

For this signature to serve both JIT and object paths with no mode discriminator (Principle 11), the JIT path's `JITBuilder::symbol_lookup_fn` closure must resolve `__cranelisp_got_{target_module}` to a raw address using only `symbol_tables`. Today that address lives on `TypecheckProduct.got` (`src/session_v4.rs:406`), which is NOT reachable from `&DashMap<ModuleFullPath, SymbolTable>`. The choices are:

1. **Add a fifth parameter** (`typecheck_products` or a bespoke `got_bases` map). Violates Principle 11 (single pipeline, mode parameters) and contradicts `pipeline-v4.md` §9.3. The target signature is four parameters, not "four, plus a side map for GOT bases".
2. **Keep the current `SessionCompilationEnv` / `ObjectCompilationEnv` env-trait split.** Explicitly deleted from the target state — no `CompilationEnv`, `ObjectCompilationEnv`, or `JitCompilationEnv` in Sprint 56 Phase 2.
3. **Move `got: GotTable` onto `SymbolTable` now** (G7). `symbol_tables[m].got.base_ptr()` is all the JIT `symbol_lookup_fn` needs. Fits the four-param signature cleanly. No env types, no wrappers, no side maps. *(Chosen.)*

`pipeline-v4-roadmap.md` §Phase 3 Step 3a originally scheduled G7 later ("collapse the intermediate DashMaps into the symbol table"). Pulling it into Wave 0 costs very little — `GotTable` is already an `Arc`-friendly atomic structure, the field is a no-op at serde boundaries (`#[serde(skip)]`), and the migration is mechanical. Deferring it, on the other hand, would force Step 2a to ship with a compromised `compile_to_module` signature, re-introduce an env trait, or carry a sixth parameter — each of which would have to be un-done in Phase 3 anyway.

#### 9.8.1 Data Movement

**Add to `crates/cranelisp-types/src/module.rs`** — `SymbolTable` gains a `got` field:

```rust
// crates/cranelisp-types/src/module.rs
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SymbolTable {
    pub path: ModuleFullPath,
    pub symbols: HashMap<Symbol, ModuleEntry>,
    #[serde(default)]
    pub next_got_slot: usize,

    // --- NEW (Wave 0 Step 4 / G7) ---
    /// Per-module Global Offset Table. Created when this SymbolTable is
    /// constructed (at module registration). Base address is stable for
    /// the lifetime of the SymbolTable. Slot indices are assigned by
    /// `allocate_got_slot()`; code pointers are written atomically by
    /// codegen workers and read by JIT-emitted call sites.
    ///
    /// Not serialized: cache reconstruction creates a fresh GotTable and
    /// re-populates slot pointers during cache-hit codegen.
    #[serde(skip, default)]
    pub got: GotTable,
}
```

`GotTable::default()` already exists (`crates/cranelisp-backend/src/got.rs:81`) and returns `GotTable::new()` with all slots null — which is exactly the desired behaviour for `#[serde(skip, default)]` on cache load. No custom deserialization needed.

**Crate-boundary concern:** `GotTable` currently lives in `cranelisp-backend`. `cranelisp-types` does NOT depend on `cranelisp-backend` (and must not — `cranelisp-types` is the most stable crate; Principle 3 in `design/arch/CLAUDE.md`). Resolution: **move `GotTable` into `cranelisp-types`** alongside `SymbolTable`. The type is pure data — `Box<[AtomicPtr<u8>; GOT_TABLE_SIZE]>` — with no backend-specific dependencies. `GOT_TABLE_SIZE` (currently in `cranelisp-backend/src/codegen_types.rs`) moves with it. `cranelisp-backend` re-exports `GotTable` from `cranelisp-types` for API compatibility during the migration; once all call sites in `cranelisp-backend` are updated, the re-export can be removed in a follow-up.

**Initialization site.** `GotTable` is allocated inside `SymbolTable::new()` — the existing constructor at `crates/cranelisp-types/src/module.rs:25`. Callers of `SymbolTable::new()` include `TypeChecker::register_module_symbol_table()` (the typecheck stage's module registration entry point). No new call site is needed; the GOT comes into existence exactly when the module first becomes known to the typechecker, which is the invariant required by `pipeline-v4.md` §9.2 ("created when the module is first registered (before typecheck begins) so that its base address is stable for the process lifetime").

**Delete from `src/session_v4.rs`:**

- Line 406 — the `pub got: std::sync::Arc<cranelisp_backend::got::GotTable>` field on `TypecheckProduct`.
- Line 804 — the `got: std::sync::Arc::new(...)` initializer in `ensure_typecheck_product`.

#### 9.8.2 Fate of `TypecheckProduct`

After `got` is removed, `TypecheckProduct` holds only:
- `file_path: Option<PathBuf>` — source path for error messages and cache keying.
- `source_text: Option<String>` — retained in `--repl` mode for `/source` introspection.

**Recommendation: dissolve `TypecheckProduct` into fields on `SymbolTable`.** Rationale:

1. Both surviving fields are per-module metadata that belongs with the rest of the module's state.
2. `file_path` is already deterministic from `module path + project root + lib search path` according to `pipeline-v4.md` §9.1 ("File paths are deterministic from module path + project root + lib search path"). The field exists only because the session caches the resolved path. That cache can live on `SymbolTable` or (better) be recomputed from a `PathResolver` utility in the integration layer.
3. `source_text` is REPL-only display data. `pipeline-v4.md` §9.1 lists `SymbolTable` as holding "symbol definitions, structural declarations, GOT, and compiled code" — source text is structural declarations-adjacent (the module's original text). Adding `#[serde(skip)] pub source_text: Option<String>` to `SymbolTable` keeps it with the rest of the module's per-module state.
4. The `typecheck_products: DashMap<ModuleFullPath, TypecheckProduct>` map on `SharedState` would be deleted entirely — 18 call sites in `src/worker.rs` and `src/session_v4.rs` (enumerated in the grep results that motivated this section) collapse into reads against `symbol_tables[m]`.

**Coordination with `/int`** (who owns `src/session_v4.rs`): `/int`'s Phase 2 plan (`design/int/phase2-codegen-convergence.md`) already schedules the deletion of `SessionCompilationEnv` at Step 2b. The `TypecheckProduct` dissolution is a companion cleanup: same PR or the immediately following PR. The decision tree is:

- **If Wave 0 ships with `TypecheckProduct` reduced to `{ file_path, source_text }`** (minimum viable Step 4): acceptable, but leaves the `typecheck_products` DashMap and all its call sites in place. Step 3b (G6) in `pipeline-v4-roadmap.md` would become a larger deletion PR.
- **If Wave 0 ships with `TypecheckProduct` fully dissolved** (recommended): `source_text` and `file_path` migrate to `SymbolTable` in the same PR that adds `got`. All `typecheck_products` references in `src/worker.rs` and `src/session_v4.rs` are rewritten to read from `symbol_tables`. This is mechanical — `tp.got` → `st.got`, `tp.file_path` → `st.file_path`, `tp.source_text` → `st.source_text` — but touches ~18 lines across 2 files.

**Recommendation**: ship the **fully dissolved** variant. The migration is small, the deletion is irrevocable, and it keeps Step 2b's `SessionCompilationEnv` deletion mechanical rather than conditional on a follow-up PR. `/int` owns the call-site rewrites in `src/session_v4.rs` and `src/worker.rs`; `/typecheck` owns the field moves in `crates/cranelisp-types/src/module.rs`. Neither change crosses a skill boundary in terms of logic — the DashMap lookups are a straight substitution.

A FIXME is filed on `src/session_v4.rs:401` (the `TypecheckProduct` struct definition) pointing to this section, so that `/int` picks up the dissolution work when actioning Wave 0 Step 4.

#### 9.8.3 Serde

`GotTable` contains `Box<[AtomicPtr<u8>; GOT_TABLE_SIZE]>` — a runtime pointer array. It is NOT serializable and MUST NOT round-trip through the cache. The `#[serde(skip, default)]` attribute on the `got` field ensures:

- **On serialize**: the field is omitted from the JSON/binary representation. Cache files stay pointer-free.
- **On deserialize**: `GotTable::default()` — which delegates to `GotTable::new()` — produces a fresh, all-null table. The deserialized `SymbolTable` has the same `next_got_slot` value it had when serialized (slot assignments are preserved as `usize` indices on individual `ModuleEntry::Def.got_slot` values), but every slot pointer starts null. Codegen re-fills slots as it compiles each function — either by JIT (worker writes ptr atomically) or by object-module relocation (`.o` linker resolves `__cranelisp_got_{module}` data symbol + slot offset).

This is the correct semantics: a cache hit means "I have pre-checked types and AST"; it does NOT mean "I have pre-compiled code". Code pointers live in the OS page tables of the current process — they cannot be persisted. The GOT re-initialization on cache load is a first-class behaviour, not a bug to work around.

**Consequence for `Linker` cache hits:** the `.o` code-region mapping path (Step 5b in `pipeline-v4-roadmap.md`, "cache serialization via symbol table") patches GOT slot pointers at module-load time using the freshly-constructed `GotTable`. The existing logic in `crates/cranelisp-backend/src/cache/mod.rs` (which currently reads `typecheck_product.got`) gets rewritten to `symbol_tables[m].got` — same operations, different source.

#### 9.8.4 Concurrency

`SymbolTable` already lives in `DashMap<ModuleFullPath, SymbolTable>`. After Step 4, GOT reads and writes happen via `&SymbolTable` (a shared reference held while a `DashMap` read guard is live). The safety argument:

- **`GotTable::store_slot(&self, slot, ptr)`** takes `&self` — atomic store through `AtomicPtr`. Safe to call from concurrent workers on disjoint slots. Already verified by `test_atomic_got_concurrent_writes` in `crates/cranelisp-backend/src/got.rs:117`.
- **`GotTable::load_slot(&self, slot) -> *const u8`** takes `&self` — atomic load. Safe from any thread.
- **`GotTable::base_ptr(&self) -> *const u8`** takes `&self` — returns `self.slots.as_ptr() as *const u8`. The `Box<[AtomicPtr<u8>; GOT_TABLE_SIZE]>` is never reallocated (`Box` is not `Vec`), so the address is stable for the `GotTable`'s entire lifetime. Safe from any thread.
- **`SymbolTable::allocate_got_slot(&mut self) -> usize`** takes `&mut self` — requires an exclusive `DashMap` write guard. Already single-writer in the current typecheck pipeline. Sprint 56 Wave 0 does not change this.

`SymbolTable` is already `Send + Sync` (its current fields are all `Send + Sync`: `ModuleFullPath`, `HashMap<Symbol, ModuleEntry>`, `usize`). Adding a `GotTable` field preserves this — `GotTable` is `Send + Sync` (see the existing `unsafe impl` at `crates/cranelisp-backend/src/got.rs:29–30`). The "nice-worker object-codegen path" (§4.2 of `pipeline-v4.md`) is already single-threaded-per-module-at-a-time, and its pattern of `let st = symbol_tables.get(&m)?; /* read-only */` continues to work.

**No lock is needed over `got.store_slot`** even when a slot is written during codegen — the atomic store is serialized against subsequent atomic loads by the `Release`/`Acquire` ordering (already verified in `got.rs`). The DashMap read guard simply keeps `st` alive; concurrent JIT workers writing to disjoint slots on the same table is already supported.

#### 9.8.5 Migration Impact

Cross-skill call-out of downstream work that touches code outside `design/typecheck/`. These are owned by the named skill; this section flags them but does not implement them.

1. **`/int` — `SessionCompilationEnv`** (`src/worker.rs:87, 96, 216, 607, 2169, 2555`; also `src/session_v4.rs:1450`). This env reads `typecheck_products[m].got` today. The env type is entirely deleted in Step 2b (per `/int`'s `phase2-codegen-convergence.md`) — not retrofitted to read `symbol_tables[m].got`. Rationale: `CompilationEnv` as a trait is the wrong abstraction shape for the four-param `compile_to_module` (see §9.8's rationale preamble). The env is replaced by direct `&DashMap<ModuleFullPath, SymbolTable>` lookups inside `compile_to_module` and by the JIT's `symbol_lookup_fn` closure. **Coordination point with `/int`.**

2. **`/backend` — `ObjectCompilationEnv`** (`crates/cranelisp-backend/src/cache/object.rs`; constructed at `crates/cranelisp-backend/src/lib.rs:81`). This env also reads GOT through the typecheck-products indirection. Deletion is scheduled in `/backend`'s Step 2a. After Step 4, the replacement code path inside `compile_to_module` reads GOT bases directly from `symbol_tables[target_module].got.base_ptr()` — no env needed. **Coordination point with `/backend`.**

3. **JIT `symbol_lookup_fn` closure** (new code, owned by `/backend` Step 2a). The closure captures `&DashMap<ModuleFullPath, SymbolTable>` (or an `Arc` of it) and resolves symbols of the form `__cranelisp_got_{module_name}` by:
   ```rust
   |name| -> Option<*const u8> {
       let module = name.strip_prefix("__cranelisp_got_")?;
       let st = symbol_tables.get(ModuleFullPath::from(module).as_ref())?;
       Some(st.got.base_ptr())
   }
   ```
   No reference to `typecheck_products`. This closure is the forcing function for Step 4: without G7, it cannot be expressed against the four-param `compile_to_module` signature.

4. **Object path `__cranelisp_got_{module}` data symbol** (owned by `/backend`). Declared as `Linkage::Import` in the `ObjectModule`. Resolved at link time from the per-module `.o` file that exports the corresponding data symbol. No change from the existing design — just documenting that the same data-symbol name is what the JIT closure resolves against, giving uniform GOT emission across JIT and object paths. Principle 11 again: the backend emits the same `global_value` load against the same `Linkage::Import` data symbol for both modes; only the `Module` implementation differs.

5. **Callers that inspect `typecheck_products` for non-GOT fields**: the ~18 call sites enumerated in the grep results at `src/worker.rs:225, 349, 614, 802, 1455, 1569, 1767, 1864, 2176, 2337, 2465, 2561, 2766, 2772` and `src/session_v4.rs:885, 970, 1679, 2480`. Each must be rewritten to read from `symbol_tables[m]` instead. Mechanical but wide. Owned by `/int`; FIXME filed on `src/session_v4.rs:401`.

#### 9.8.6 Sketch Comparison

The sketch has a `ModuleGotRegistry` that maps `ModuleFullPath` to `Arc<GotTable>` — a separate registry alongside `TypeChecker`'s symbol tables. This is the same structural debt the rest of Sprint 56 addresses: per-module state fragmented across parallel DashMaps. The sketch accreted the registry because GOT arrived mid-project when the symbol table already existed and the easiest delivery was a new map. The Cranelisp reimplementation does not have that constraint — G7 is a design decision, not a migration from the sketch. We diverge from the sketch's separate-registry model: one DashMap, one truth per module. Rationale: `design/arch/CLAUDE.md` Principle 7 (single source of truth — when a concept appears in two places, it will diverge) and Principle 1 (decoupling over convenience — the separate registry "worked" but added a synchronization invariant nobody needed).

#### 9.8.7 Wave 0 Exit Conditions for Step 4

In addition to the general Wave 0 exit gate (§9.7), Step 4 specifically requires:

- `cargo check -p cranelisp-types` passes — new `got` field and its `#[serde(skip, default)]` attribute compile cleanly.
- `cargo check -p cranelisp-backend` passes — GOT relocations in the object path continue to work; the `GotTable` re-export (if kept transitionally) resolves.
- `cargo check -p cranelisp` passes with `TypecheckProduct.got` deleted — this is the compile-time proof of completion.
- `cargo nextest run -p cranelisp-types` adds the four new unit tests from §9.7 (tests 7–11) and they pass.
- `cargo nextest run` full suite remains at the 1590 passed / 22 failed baseline.
- No references to `typecheck_products[m].got`, `tp.got`, `product.got`, or `Arc<GotTable>` remain in `src/` or `crates/` (grep-able check).

If `TypecheckProduct` is fully dissolved in the same PR (recommended per §9.8.2), add:

- `cargo check` fails if any code still references `TypecheckProduct`, `typecheck_products`, or `ensure_typecheck_product`. These names no longer exist.

---

## 10. Sprint 57 Wave 1 — Phase 3 G6 and `CheckResult` Slim-Down

**Status (Wave 2 step 4):** LANDED. `CheckResult` is now
`{ warnings: Vec<Warning>, display: Option<DisplayInfo> }`; the five legacy
fields (`method_resolutions`, `mono_defns`, `default_method_defns`,
`constrained_fn_names`, `expr_types`) are retired. See §10.3 for the
retrospective landing sequence.

Sprint 57 lands Phase 3 (Step 3b — G6, move `code: Option<Code>` onto `ModuleEntry::Def`) and Phase 4 (platform / persistent workers) of `pipeline-v4-roadmap.md`. Phase 3 G6 is the final carrier for all durable typecheck output onto `SymbolTable`: after G6, the `ast` and `code` fields on `ModuleEntry::Def` coexist on the same entry, with typecheck owning `ast` and backend owning `code`. `CheckResult` — which has survived Phase 1 and Phase 2 as a typecheck-internal working aggregate with legacy fields — has now slimmed to exactly the two boundary fields that `src/` actually reads: `warnings` and `display`.

This §10 extends §9 in two ways:

1. **§10.1 (G6 interaction, code-write path).** For every category in the §9.1 authoritative table, confirm the typecheck / backend ownership boundary on `ast` vs `code`. Typecheck never writes `code`; backend never writes `ast`. Both coexist on the same entry without coupling.
2. **§10.2 (`CheckResult` slim-down plan).** Audit every reader of the five legacy fields (`method_resolutions`, `mono_defns`, `default_method_defns`, `constrained_fn_names`, `expr_types`) across `src/`, `crates/cranelisp-backend/`, and `crates/cranelisp-typecheck/`. Classify each as `cfg(test)-only`, `typecheck-internal only`, or `LIVE BACKEND READER`. Propose the slimmed shape.
3. **§10.3 (migration order).** Specify the Wave 2 landing order so `/backend` and `/typecheck` changes ship together — no red build window.

### 10.1 G6 Interaction — Code-Write Path on `ModuleEntry::Def`

**Target shape (Decision 25, `design/arch/CLAUDE.md`):** `ModuleEntry::Def.code: Option<Code>` with `#[serde(skip)]`. Written by the priority worker after `compile_to_module` returns. Read by REPL eval, introspection (`/clif`, `/disasm`, `/source`), and the linker. Runtime-only state — cache-hit load restores `ast` from `.meta.json` and leaves `code` as `None` until codegen re-runs.

**Landed shape (Sprint 57 Wave 2 Step 1):** Shape 1 (thin handle) — `Code` lives in `crates/cranelisp-types/src/code.rs` as a minimal pointer-only struct (`pub struct Code { pub ptr: *const u8 }` with `Send + Sync` and `#[serde(skip, default)]` on the pointer), keeping `cranelisp-types` free of the `cranelift_jit::JITModule` / `Arc<Jit>` dependency that would otherwise reach from `cranelisp-backend`. The `Arc<Jit>` lifetime anchor remains in the integration layer (`src/session_v4.rs`) and is managed at the session level per Decision 28 — the session keeps its per-worker `Jit` set alive for as long as any `SymbolTable` holding `Code` entries into those pages is reachable.

**Ownership boundary (hard invariant):**

| Writer | Owns | Read by |
|---|---|---|
| `/typecheck` | `ast`, `scheme`, `param_names`, `kind`, `callees`, `got_slot`, `trait_origin` | `/typecheck` (downstream passes), `/backend` (`compile_to_module` reads `ast`), `/int` (introspection reads `scheme`, `docstring`, `callees`) |
| `/backend` | `code` | `/int` (priority worker stores returned `Code`; REPL eval calls `code.ptr`; introspection reads `code.jit` / `code.ptr` for `/clif` / `/disasm`) |

`/typecheck` MUST NOT touch `code`. `/backend` MUST NOT touch `ast`. The field layout on the struct is what enforces the boundary — no adapter function, no helper that reads or writes across the line.

**Per-category table** — extend §9.1 with the `code` disposition:

| # | Category (from §9.1) | `ast` writer | `code` writer | Both coexist on entry |
|---|----------------------|--------------|---------------|----------------------|
| 1 | Regular defn | typecheck (`check_form(CheckBody)`) | backend (priority worker after `compile_to_module`) | yes |
| 2 | Multi-sig internal variant (`foo__v0`) | N/A — removed before codegen; see §9.3 | N/A — not compiled under this name | no — entry is transient within typecheck |
| 3 | Multi-sig **mangled** variant (`add$Int+Int`) | typecheck (`register_mangled_variants`, §9.3) | backend (priority worker after `compile_to_module`) | yes |
| 4 | Mono specialisation (`add$Float+Float`) | typecheck (`register_mono_entry`, §9.4) | backend (priority worker after `compile_to_module`) | yes |
| 5 | Default method defn (trait decl default) | typecheck (`check_impl_method` default path) | backend (priority worker after `compile_to_module`) | yes |
| 6 | Trait-impl method (`Display.show$Option$Int`) | typecheck (`check_impl_method` / `check_hkt_impl_method`) | backend (priority worker after `compile_to_module`) | yes |
| 7 | REPL `__expr` synthetic | typecheck (`check_repl_input_inner`) | backend (one-shot codegen path in REPL eval) | yes (but the entry is typically discarded after eval — REPL additivity strategy per §8.4) |

Rows 1, 3, 4, 5, 6 are the durable Phase-3+4 carriers: typecheck writes `ast` during `check_form`; the priority worker reads `ast`, calls `compile_to_module`, and writes the returned `Code` back onto the same entry. Row 2 is a transient internal name that is removed before codegen (§9.3) — it never carries `code`. Row 7 may be materialised on the symbol table or handled off-table by the REPL eval path per `/int`'s convention (see `design/int/phase2-codegen-convergence.md` §6); either way the same ownership boundary applies.

**Cache-hit interaction.** `try_cache_hit_load` (`src/session_v4.rs`) deserialises a `SymbolTable` from the cache manifest. After Phase 1, `ast` is restored from `.meta.json` along with the rest of the `ModuleEntry::Def` fields. After Phase 3 G6, `code: Option<Code>` starts `None` on the loaded table (per `#[serde(skip)]`); codegen then runs against the restored `ast` to repopulate `code`. Typecheck's invariants do not depend on `code` being populated:

- A module may be typechecked without ever being codegen'd — e.g. if the user quits before running it, or if a dependency is imported but no call-site forces compilation. Typecheck's output is complete with `ast` alone.
- A module may be loaded from cache with `ast` restored and `code: None`. The priority worker compiles on demand; typecheck does NOT re-run against the cached `ast`.
- Introspection that needs `code` (e.g. `/disasm`) must either trigger codegen or return "not yet compiled" — it never needs typecheck to fill the gap.

**No typecheck-owned read of `code`.** Across `crates/cranelisp-typecheck/`, `code` MUST NEVER appear as a right-hand-side expression: no `entry.code.as_ref()`, no `st.symbols.get(x).and_then(|e| e.code())` or equivalent. The only legitimate typecheck-side operation on `code` is *not touching it* — leaving it `None` when the typechecker creates a new `ModuleEntry::Def`. This is enforced structurally by the struct field's visibility and by `/review`'s Wave 2 blocker list.

### 10.2 `CheckResult` Slim-Down Plan

Per `/arch` Condition 1 (Sprint 57 §Architecture Review): `CheckResult` slim-down to `{ warnings, display }` lands in Wave 2, paired with G6. The claim is that `method_resolutions`, `mono_defns`, `default_method_defns`, `constrained_fn_names`, and `expr_types` are no longer boundary data post-Phase-1; this section audits the claim by enumerating every reader.

#### 10.2.1 Audit methodology

For each field, `/typecheck` ran the following grep across the tree:

```
grep -rn '\.<field>' src/ crates/ tests/
```

Results were classified:

- **cfg(test)-only** — the read sits inside `#[cfg(test)] mod tests` in either `crates/cranelisp-backend/` or `crates/cranelisp-typecheck/`. These are test bridges that pre-date Phase-1 AST annotation and may be rewritten against a locally-defined `TestCheckResult` helper without affecting the boundary shape.
- **typecheck-internal** — the read is inside `crates/cranelisp-typecheck/` non-test code. These are valid reads — `CheckResult` is typecheck's own working aggregate (or more accurately, the pattern is reading from `CheckState` / `FormCheckResult` / `ModuleCheckAccumulator`, then writing a `CheckResult` at the end). The slim-down does not affect these reads; it only removes the legacy fields from the *outgoing boundary* struct.
- **LIVE BACKEND READER** — a read in `crates/cranelisp-backend/` non-test code or in `src/` that consumes the field at the typecheck → backend boundary. If any exist, the slim-down blocks on migrating them to AST-node / symbol-table lookups first.

#### 10.2.2 Field-by-field audit

**Field 1: `method_resolutions: HashMap<Span, ResolvedCall>`**

- `crates/cranelisp-backend/src/lib.rs:558, 618, 624, 629, 2394, 2430, 2642, 2648, 2654, 2663, 2846, 2953` — ALL inside `#[cfg(test)] mod tests` (the `mod tests` block starts at line 386). Verified by reading the surrounding context: 558 is inside `test_compile_expr_and_run`; 618/624/629 are inside `test_compile_program_and_run`; 2394+ are inside individual test functions. These reads are part of the `enrich_defn_from_side_maps` / `empty_check` / `test_compile_program_and_run` test scaffolding that bridges hand-built `Defn`s through a `CheckResult` side-map for tests that do NOT run production typecheck.
- `src/` — **zero** matches for `check_result.method_resolutions` or `check.method_resolutions`.
- `crates/cranelisp-typecheck/` — 50+ reads, all in non-test code. These are `state.method_resolutions` on `CheckState` (typecheck's internal side-map during inference), `accumulator.method_resolutions` on `ModuleCheckAccumulator` (typecheck's working aggregate across forms), and field reads on `FormCheckResult` (per-form intermediate). These are all typecheck-internal and survive the slim-down unchanged — they live on `CheckState`/`ModuleCheckAccumulator`/`FormCheckResult`, NOT on the outgoing `CheckResult`.

**Classification: cfg(test)-only (backend) + typecheck-internal.** No LIVE BACKEND READER. Safe to remove from `CheckResult`.

**Field 2: `mono_defns: Vec<MonoDefn>`**

- `crates/cranelisp-backend/src/lib.rs:627` — inside `#[cfg(test)]` (the `for mono in &check.mono_defns` loop in `test_compile_program_and_run`).
- `src/` — **zero** matches for `check.mono_defns` or `check_result.mono_defns`.
- `crates/cranelisp-typecheck/` — reads inside `finalize_check_result` and the mono-generation path. Typecheck-internal.

Post-Sprint 56, `/arch` Decision 22 and `ast-annotation.md` §9.4 established that each mono specialisation carries its own `ModuleEntry::Def { ast: Some(_), .. }` via `register_mono_entry` before `CheckResult` is constructed. The `CheckResult.mono_defns: Vec<MonoDefn>` field is a duplicate of what's now on the symbol table — preserved only because the Phase-2 PR kept it in place to stay additive (per §9.4 "Wave 0 retains `CheckResult.mono_defns` ... as-is for the dual-write period"). No production code outside test scaffolding reads it.

**Classification: cfg(test)-only (backend) + typecheck-internal.** No LIVE BACKEND READER. Safe to remove from `CheckResult`.

**Field 3: `default_method_defns: Vec<Defn>`**

- `crates/cranelisp-backend/src/lib.rs:622, 2494, 2543` — ALL inside `#[cfg(test)]`.
- `src/worker.rs:757, 813, 1829` — **these read `accumulator.default_method_defns`, NOT `check_result.default_method_defns`**. `accumulator` is a `ModuleCheckAccumulator` (a typecheck-internal type re-exported from `cranelisp-typecheck`). The reads are on the accumulator during Pass 1 / Pass 2 stitching, which is `/int`'s driving of the typecheck stages — not a backend-side consumption of a boundary field. Verified by `src/worker.rs:114: accumulator: &'a mut ModuleCheckAccumulator`.
- `crates/cranelisp-typecheck/` — reads inside `finalize_check_result` and the default-method generation path. Typecheck-internal.

Same reasoning as field 2: each default method has its own `ModuleEntry::Def { ast: Some(_), .. }` after Sprint 56 (per Decision 22 and §9.1 table row 5). The `CheckResult.default_method_defns` field duplicates what's on the symbol table.

**Classification: cfg(test)-only (backend) + typecheck-internal.** No LIVE BACKEND READER. Safe to remove from `CheckResult`.

**Field 4: `constrained_fn_names: HashSet<Symbol>`**

- `crates/cranelisp-backend/src/lib.rs:2482` — inside `#[cfg(test)]`.
- `src/` — **zero** matches.
- `crates/cranelisp-typecheck/` — reads/writes inside `finalize_check_result` and the `detect_constrained_fns` pass. Typecheck-internal.

Per Decision 22 (`SymbolTable::defined_symbols()`), the set of constrained fn templates is derivable by scanning `SymbolTable` for `ModuleEntry::Def { kind: UserFn { constrained_fn: Some(_) }, .. }`. The old inline scan at `crates/cranelisp-backend/src/lib.rs:95–109` (which computed `constrained_fn_names` from the symbol table directly, NOT from `CheckResult`) is the pattern — the `CheckResult` field is a duplicate source that no production code reads.

**Classification: cfg(test)-only (backend) + typecheck-internal.** No LIVE BACKEND READER. Safe to remove from `CheckResult`.

**Field 5: `expr_types: HashMap<Span, Type>`**

- `crates/cranelisp-backend/src/lib.rs:558, 618, 624, 629, 631, 632, 2663` — ALL inside `#[cfg(test)]`. Line 631/632 is inside the `for mono in &check.mono_defns` fallback (`if mono.expr_types.is_empty() { &check.expr_types } else { &mono.expr_types }`) — also test scaffolding.
- `src/` — **zero** matches.
- `crates/cranelisp-typecheck/` — reads/writes inside inference. Typecheck-internal.

Per Phase 1 (G3) and `design/backend/ast-sourced-codegen.md`, every `Expr` node now carries `inferred_type: Option<Box<Type>>`. The backend's heap classification and type-dependent codegen read from AST nodes directly; the `expr_types` side map is not consulted.

**Classification: cfg(test)-only (backend) + typecheck-internal.** No LIVE BACKEND READER. Safe to remove from `CheckResult`.

#### 10.2.3 Audit summary table

| Field | Backend non-test readers | `src/` readers | Typecheck-internal readers | LIVE BACKEND READER? |
|---|---|---|---|---|
| `method_resolutions` | 0 (all 12 hits in `mod tests`) | 0 | many (CheckState/FormCheckResult/accumulator) | **no** |
| `mono_defns` | 0 (1 hit in `mod tests`) | 0 | typecheck-internal | **no** |
| `default_method_defns` | 0 (3 hits in `mod tests`) | 0 (src reads `accumulator.default_method_defns`, not `CheckResult.default_method_defns`) | typecheck-internal | **no** |
| `constrained_fn_names` | 0 (1 hit in `mod tests`) | 0 | typecheck-internal | **no** |
| `expr_types` | 0 (7 hits in `mod tests`) | 0 | typecheck-internal | **no** |

**Verdict: `/arch` Condition 1 is satisfied in full.** All five slim-down targets have zero live backend readers outside `#[cfg(test)]` scaffolding. No field is a slim-down blocker. The slim-down ships in Wave 2 coupled with G6.

#### 10.2.4 Post-slim `CheckResult` shape

`/arch` proposed `{ warnings, display }`. Confirmed — this is the only `src/` reader surface across `src/worker.rs:828` (writes `display`), `src/session_v4.rs:1422, 1578, 1597, 1624, 1634, 2176` (read `warnings` / `display`). No other field on the current `CheckResult` is read outside typecheck.

```rust
// crates/cranelisp-types/src/check.rs — post-slim shape
//
// Transient output of TypeChecker::check. NOT a boundary type — the
// durable typecheck output lives on SymbolTable entries' `ast`, `scheme`,
// `callees`, `got_slot`, and `trait_origin` fields. This struct carries
// only diagnostics and optional REPL display payload.
#[derive(Debug)]
pub struct CheckResult {
    /// Non-fatal warnings accumulated during checking.
    pub warnings: Vec<Warning>,

    /// Display info for REPL output (last Expr or Defn in the input).
    /// `None` in batch / module-load mode.
    pub display: Option<DisplayInfo>,
}
```

Other types on `check.rs` to retain (they are independently used):

- `ResolvedCall` — still on `Expr::Apply.resolved_call` (AST annotation); serialised via AST; untouched by slim-down.
- `MethodResolutions = HashMap<Span, ResolvedCall>` — typecheck-internal type alias still used on `CheckState`; retain.
- `MonoDefn` — typecheck-internal working type still used in `monomorphise_call` before `register_mono_entry` lifts it to a `ModuleEntry::Def`; retain.
- `DisplayInfo` — referenced from `CheckResult.display`; retain unchanged.
- `TypeDefInfo`, `ConstructorInfo`, `FieldInfo` — used by `ModuleEntry::TypeDef` / `ModuleEntry::Constructor`; retain.
- `ReplSnapshot` — typecheck-owned snapshot/restore mechanism; retain.

**Name decision: keep `CheckResult`, do NOT rename to `CheckOutput`.** §6 previously proposed renaming to `CheckOutput` to signal "not a boundary type". `/arch`'s Sprint 57 review explicitly uses `CheckResult` in its condition statements ("`CheckResult` slim-down"), and `interfaces.md` §"TypeChecker Internal State" already documents the name as the residual typecheck-internal type. Renaming now would churn every `use cranelisp_types::CheckResult` site in `src/worker.rs` and `src/session_v4.rs` (three files, ~15 lines) without a behavioural payoff. The slim-down IS the semantic change; the name can remain. A follow-up rename can be filed as a cosmetic FIXME if desired.

#### 10.2.5 Backend test-scaffolding disposition

The 20+ `#[cfg(test)]` hits in `crates/cranelisp-backend/src/lib.rs` use the full `CheckResult` shape (with all 7 fields) to bridge hand-built `Defn`s through `enrich_defn_from_side_maps` into the post-Phase-2 symbol-table + `compile_to_module` API. After the slim-down, these tests cannot construct the old-shape `CheckResult` from `cranelisp-types` — it no longer has `method_resolutions`, `mono_defns`, etc.

**Resolution (per `/arch` Condition 1):** introduce a crate-internal `TestCheckResult` helper inside `crates/cranelisp-backend/src/lib.rs` under the `#[cfg(test)] mod tests` block:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{CheckResult, Defn, ...};  // still uses boundary CheckResult for warnings/display

    /// Test-only aggregate bridging hand-built Defns through side-map
    /// enrichment. Replaces the retired CheckResult fields that were
    /// removed from the boundary type in Sprint 57 Wave 2.
    struct TestCheckResult {
        method_resolutions: HashMap<Span, ResolvedCall>,
        mono_defns: Vec<MonoDefn>,
        default_method_defns: Vec<Defn>,
        constrained_fn_names: HashSet<Symbol>,
        expr_types: HashMap<Span, Type>,
        warnings: Vec<Warning>,
        display: Option<DisplayInfo>,
    }

    impl TestCheckResult {
        fn empty() -> Self { /* ... */ }
    }

    // enrich_defn_from_side_maps and test_compile_program_and_run
    // change their `check: &CheckResult` parameter to `check: &TestCheckResult`.
}
```

This is a purely internal-to-crate concern — no boundary impact. `/backend` executes the rewrite as part of Wave 2 (they own the test code). It is a mechanical rename: `CheckResult` → `TestCheckResult`, same field list, same field types. The slim-down of the public `CheckResult` and the introduction of the local `TestCheckResult` land in the same PR.

**Alternative considered: leave the legacy fields on `CheckResult` and file a follow-up FIXME.** Rejected. Deferring keeps the full shape alive for no architectural reason — the fields are already dead outside test scaffolding, and `/arch` Condition 1 explicitly scopes the slim-down to Wave 2. A `TestCheckResult` helper is the smaller, localised change; deferring would leave 5 unused fields on the boundary type indefinitely.

#### 10.2.6 `FormCheckResult` disposition

`FormCheckResult` (`crates/cranelisp-typecheck/src/program.rs:242`) is typecheck-internal (the `program.rs` module's per-form intermediate). Its fields `method_resolutions`, `expr_types` etc. are OK to keep — they are typecheck's own working state, not boundary data. `§3.8 FormCheckResult Field Disposition` in this doc already schedules these for eventual removal when annotation fully replaces side maps, but that is not a Sprint 57 deliverable. The slim-down touches ONLY the public `CheckResult` in `crates/cranelisp-types/`.

### 10.3 Migration Order — Wave 2 Contract (Landed in Wave 2 step 4)

**Status:** LANDED. Sprint 57 Wave 2 completed the slim-down in step 4, paired
with G6 per `/arch` Condition 1. Post-slim shape is `CheckResult { warnings,
display }` — the five legacy fields are gone from `crates/cranelisp-types/src/check.rs`.

The Wave 2 landing sequence (retrospective):

1. **`/typecheck` (step 1)**: added `code: Option<Code>` to `ModuleEntry::Def` with `#[serde(skip)]`. Additive — green on its own.
2. **`/backend` (step 2)**: landed `compile_to_module` write of `code` before returning. Relocated all 20+ `#[cfg(test)]` readers of the five legacy `CheckResult` fields into a local `TestCheckResult` helper at `crates/cranelisp-backend/src/lib.rs:537-547`. The helper mirrors the pre-slim shape field-for-field so the backend test suite compiled unchanged against the still-wide public `CheckResult`.
3. **`/int` (step 3)**: deleted `CodegenProduct` DashMap; priority worker / REPL eval / introspection all read `code` from the symbol table. Migrated 10 read sites.
4. **`/typecheck` (step 4 — THIS commit)**: deleted the five legacy fields from `CheckResult`. Updated the three construction sites in `crates/cranelisp-typecheck/src/program.rs` — `finalize_check_result_inner` (previously program.rs:1158), `check_program_inner` (previously program.rs:1893), and `build_repl_result` (previously program.rs:2758) — to emit only `warnings` + `display`. Also updated four satellite assignment sites (`result.mono_defns = ...`, `result.default_method_defns = ...`) in the REPL input path (`check_repl_input_inner`) and the multi-sig REPL path (`check_repl_multi_sig`). Removed the FIXME at `crates/cranelisp-types/src/check.rs:1`. Added two `TestFixture` accessors (`constrained_fn_names_set`, `mono_defn_names`, `state_method_resolutions`, `state_expr_types_resolved`, `annotated_resolutions`) plus a `collect_resolutions_from_expr` helper so the ~30 typecheck-crate test assertions that used to read the slim-target fields off `CheckResult` could read from `CheckState` / `SymbolTable` / annotated ASTs instead.

Step 4 landed atomically: `cranelisp-types`, `cranelisp-typecheck` built green in the same commit; workspace tests (`cargo check --workspace --tests`) compiled without touching `crates/cranelisp-backend/src/lib.rs` (the `TestCheckResult` helper was already in place from step 2). No red build window.

**Post-Wave-2 invariant (now enforced):** `CheckResult` on `crates/cranelisp-types/src/check.rs` carries only `warnings: Vec<Warning>` and `display: Option<DisplayInfo>`. The type name remains `CheckResult`; its role is documented on `interfaces.md` §"TypeChecker Internal State" as typecheck-owned transient output — not a backend input. Backend crates do not read `method_resolutions`, `mono_defns`, `default_method_defns`, `constrained_fn_names`, or `expr_types` from any `CheckResult`; all equivalent data is either on annotated AST nodes (`Expr::Apply.resolved_call`, `Expr.inferred_type`) or on `ModuleEntry::Def` entries (`ast`, `kind`, `callees`).

**Wave 2 exit verification (retrospective):**

- `grep -rn 'check\.method_resolutions\|check\.mono_defns\|check\.default_method_defns\|check\.constrained_fn_names\|check\.expr_types\|check_result\.method_resolutions\|check_result\.mono_defns\|check_result\.default_method_defns\|check_result\.constrained_fn_names\|check_result\.expr_types' src/ crates/` returns zero matches outside test scaffolding (`TestCheckResult` uses `test.<field>`, not `check.<field>`).
- `cargo check -p cranelisp-types`, `-p cranelisp-typecheck`, `cargo check --workspace --tests` all green.
- `cargo nextest run -p cranelisp-types` 59/59 passing; `-p cranelisp-typecheck` 312/312 passing.
- `cargo clippy -p cranelisp-types -- -D warnings` and `-p cranelisp-typecheck -- -D warnings` both clean.
- `src/worker.rs:836`, `src/session_v4.rs:1324, 1348, 1439, 1591, 1610, 1637, 1647, 2189` still compile — they only read `.warnings` / `.display`.

**Dead carriers retained for now:** `MonoDefn.resolutions` and `MonoDefn.expr_types` are still constructed inside `monomorphise_call` (they feed the in-place `annotate_defn_from_maps` call right before `register_mono_entry`). These can be retired in a later cleanup pass once the annotation path is fully collapsed onto `check_defn_body_and_annotate`-style helpers; they are no longer boundary data.

### 10.4 Cross-References (Sprint 57 Wave 1)

Other Wave 1 design docs that reference this §10:

- **`design/backend/compile-to-module.md` §9.x** (`/backend` owner) — the code-write path from `compile_to_module` returning a `CompilationResult` to the priority worker writing `Code` onto `ModuleEntry::Def.code`. This doc (§10.1 above) documents typecheck's non-involvement; the backend doc documents the write itself. // TODO cross-ref §9.x in `design/backend/compile-to-module.md` once `/backend`'s Wave 1 draft lands — `/arch` reconciles during design review.
- **`design/int/phase2-codegen-convergence.md` G6 extension** (`/int` owner) — read sites for `code` across priority worker, REPL eval, introspection (`/clif`, `/disasm`, `/source`). This doc (§10.1) states the no-typecheck-read-of-code invariant; `/int`'s doc enumerates the backend / int read sites. // TODO cross-ref `/int`'s G6 §9.x extension once drafted.

### 10.5 Sketch Comparison — Post-slim `CheckResult`

The sketch (`sketch/src/typechecker.rs`) has `CheckResult` as the boundary type between typecheck and codegen with equivalent fields: `method_resolutions`, `expr_types`, `mono_defns`, `default_method_defns`, `constrained_fn_names`, `warnings`. The sketch never slimmed it because:

1. The sketch is single-pipeline, single-threaded: aggregating everything into one struct per check was the simplest delivery.
2. The sketch never introduced per-AST-node annotations (`Expr.inferred_type`, `Expr::Apply.resolved_call`) — it kept Span-keyed side maps end-to-end.
3. The sketch never factored out `ModuleEntry::Def` with an `ast` field. Codegen read `Program` + `CheckResult`; there was no third source of truth on a symbol table.

The reimplementation diverges on all three: per-node annotations (Sprint 55), mangled/mono entries on `SymbolTable` (Sprint 56), and now the logical consequence — `CheckResult` carries only what didn't move (diagnostics and REPL display). Rationale: `design/arch/CLAUDE.md` Principle 2 (narrow interfaces — `CheckResult` is now minimum surface area) + Principle 7 (single source of truth — resolutions and types live on AST nodes only, not duplicated into a side map at the boundary).

Divergence is justified: the sketch's wider `CheckResult` was a coupling surface; the Phase-3 target shape eliminates it. No cache-serialisation or REPL-additivity concern from the sketch survives — the slim-down is an unambiguous simplification.

If `TypecheckProduct` is only reduced to `{ file_path, source_text }` (minimum viable Step 4), the above checks become Phase 3 Step 3b's gating conditions instead, and §9.8.2's FIXME on `src/session_v4.rs:401` remains open.

---

## 11. Sprint 58 Wave 1 — Phase 5 Step 5a: Structural Declarations on `SymbolTable`

Phase 5 Step 5a places four structural-declaration fields directly on `SymbolTable` so the cache reader, the `.cl` regenerator, and the import-resolver can reconstruct a module's *original specification* from one source. This is the §9.1 / Decision 33 normative shape — not interim. The Sprint-57 transitional `ModuleStructure` parallel store on `SharedState` (currently in `src/save.rs`) dissolves at this step.

This section is the typecheck-side observation of the change. `/typecheck` owns the field shape because `crates/cranelisp-types/src/module.rs` is in `/typecheck`'s ownership tree (per `cranelisp-types`'s data-only role and the §"Owns" entry in `.claude/commands/typecheck.md`); `/int` owns the *writer placement* in `src/worker.rs` form-handlers and the *reader migration* in `src/save.rs`.

### 11.1 Field shape — reused 1:1 from `cranelisp-types`

Decision 33 pins the four field types as already-existing `cranelisp-types` types, reused byte-for-byte. Verified against `crates/cranelisp-types/src/module.rs`:

| Field on `SymbolTable` | Type | Definition site | Verified-present |
|------------------------|------|-----------------|------------------|
| `imports: Vec<ImportSpec>` | `ImportSpec { module_path, alias, names: ImportNames, span }` | `crates/cranelisp-types/src/module.rs:369` | YES (line 369, Sprint 56-vintage) |
| `exports: Vec<ExportSpec>` | `ExportSpec { module_path, names: ImportNames, span }` | `crates/cranelisp-types/src/module.rs:378` | YES (line 378) |
| `platforms: Vec<PlatformSpec>` | `PlatformSpec { name: String, span }` | `crates/cranelisp-types/src/module.rs:396` | YES (line 396) |
| `submodules: Vec<ModDecl>` | `ModDecl { name: ModuleName, is_private: bool, inline_body: Option<Vec<Sexp>>, span }` | `crates/cranelisp-types/src/module.rs:405` | YES (line 405) |

The fields above all live on the `SymbolTable` struct after Step 5a; the `interfaces.md` §"Symbol Table" target shape (lines 858–931) shows the full layout. **No new `cranelisp-types` boundary types are introduced.**

The `interfaces.md` target shape adds these four fields with no `#[serde(default)]` annotation — they are required fields on the serialised `SymbolTable`. (Cache-shape-mismatch discipline is handled by `schema_version`, not by per-field defaults — see §12.5.) The `imports`, `exports`, `platforms`, `submodules` fields are populated by the writer (see §11.3); cache-restore deserialises them without re-typechecking.

### 11.2 Writer placement — `/int`-owned, not `/typecheck`-owned

The writer (the code that *appends* to these fields when the typechecker / form-classifier processes a `(import …)` / `(export …)` / `(platform …)` / `(mod …)` form) is **not** typecheck-crate code. Per /arch's Phase-2 finding 3 + the SPRINT.md §/typecheck task entry, the writer lives in `/int`'s `src/worker.rs` form-handlers — the same module that already handles per-form classification and the call into `tc.check_form(...)`. /typecheck's role on Step 5a ends at the field shape: as long as the four fields exist on `SymbolTable<C, L>` with the types in §11.1, /int is unblocked.

This is a clean split because the writer needs `SharedState`-level visibility (it mutates the `SymbolTable` for the *owning* module by following the form-by-form scheduler's per-module DashMap entry — `tc.symbol_tables.entry(module).or_default().imports.push(spec)` shape), and `cranelisp-typecheck` does not see `SharedState`. The typecheck crate's view of these fields is read-only — see §11.5.

### 11.3 Typecheck-side invariants on the four fields

Typecheck does not write `imports` / `exports` / `platforms` / `submodules`, but it must *honour* them in three places that already read import/export information today. The invariants below are the contract /typecheck commits to as the field-shape owner; they are conditions /int's writer must satisfy and conditions cache-restore must preserve (Step 5b cross-reference, §12.5).

1. **Source-order preservation.** The four `Vec<_>` fields are append-only during the form-by-form classification pass. Insertion order MUST equal the source order of the underlying forms. Rationale: `.cl` regeneration (spec §6.4) reproduces the original source; the import-resolver's diagnostics quote the offending form by index. `/typecheck` does not enforce this directly (the writer is /int's), but a /typecheck unit test on `cranelisp-types` SHOULD round-trip a small `SymbolTable` with non-trivial source ordering through serde-JSON and assert `imports[0].span.start < imports[1].span.start` (and the same for the other three fields).

2. **No deduplication.** Duplicate `(import [foo [*]])` forms within one module produce two entries in `imports`. Rationale: the spec treats duplicate imports as a warning the resolver issues based on the structural record (§8.5 import diagnostics); silently collapsing them at the writer would lose the second `span` and prevent the warning from pointing to the redundant form. Same rule for `exports`, `platforms`, `submodules`. *Negative invariant*: /int's writer MUST NOT call `imports.iter().any(|i| i == &spec)` before pushing.

3. **No cross-module mixing.** `SymbolTable` is per-module (keyed by `ModuleFullPath` in `tc.symbol_tables`). The `imports` field on module `A`'s symbol table contains *only* the `(import …)` forms that appeared lexically in `A`'s source (not in `A`'s parent or children). The writer's per-form-handler dispatch already routes by owning module; this invariant is the contract that no `(import …)` form is "promoted" to a different module's structural record.

4. **Coherence with `ModuleEntry::Import` chains is one-way.** The structural `imports: Vec<ImportSpec>` is the *original specification*; the per-symbol `ModuleEntry::Import { source: FQSymbol }` entries are the *resolved effects* (Decision 33's framing). The two MUST be related as follows:
   - For every `ImportSpec { module_path: M, names: ImportNames::Specific(syms), .. }` in `imports`, every `s` in `syms` either resolves to a `ModuleEntry::Import { source: FQSymbol { module: M, symbol: s } }` entry in `symbols`, OR the import resolver emitted a "name not exported" diagnostic. (Glob and `MemberGlob` imports produce a fan-out of `ModuleEntry::Import` entries, one per name `M` actually exports.)
   - The reverse is NOT required: not every `ModuleEntry::Import` chain corresponds to a single `ImportSpec` (e.g., the implicit `(import [prelude [*]])` injection from `interfaces.md` does not appear in `imports`).
   - **Resolution (Sprint 66, user-arbitrated)**: answer (b) — the implicit `(import [prelude [*]])` injection is NOT recorded in `imports`. Rationale: `imports` is the **user-authored form-level record** that drives `.cl` regeneration in `src/save.rs::generate_imports`; storing the synthetic prelude (option a) would force a shape-match filter at regen, which cannot distinguish synthetic from user-authored `(import [prelude [*]])` (a user who writes the same form explicitly is structurally indistinguishable from the synthetic injection). Consumers that need the **effective import set** (transitive impl-resolution; module-locality short-name lookups) walk both `imports` AND per-symbol `ModuleEntry::Import` / `Reexport` entries — these record different facets at different granularities; both contribute valid edges. Embodied by per-symbol `ModuleEntry::Import` / `ModuleEntry::Reexport` chain-follow (Principle 17's chain-follow primitive) in `crates/cranelisp-typecheck/src/checker.rs` (post-revert state — α's `transitive_import_closure` was retired with Decision 45 Pattern B). Closes FIXME 0034.

5. **Read-only after typecheck completes.** Once `tc.check_program(...)` returns for a module, that module's `imports` / `exports` / `platforms` / `submodules` are frozen. Cache-write (§12.5 / Step 5b) reads them; the resolver reads them; `.cl` regeneration reads them. There is no second pass that mutates them. This matches the pattern for `symbols` and `next_got_slot` already in place (§9 / §9.8 G7 land discipline).

6. **Serde round-trip identity.** A `SymbolTable<(), ()>` round-tripped through `serde_json::to_string` + `serde_json::from_str` MUST produce a structurally identical `SymbolTable<(), ()>` modulo runtime-only fields. Post-rollback (Decision 0035 S66 amendment + Decision 0041), the runtime-only fields are:
   - `SymbolTable.got: #[serde(skip)]` — `Arc<GotTable>`; the per-module GOT is re-allocated empty on deserialise and re-populated by codegen.
   - `SymbolTable.linker: #[serde(skip)]` — `Option<L>`; re-acquired by `/int` / `/backend` on cache-hit load.
   - `ModuleEntry::Def.code: #[serde(skip)]` — `Option<C>`; re-derived by re-codegen (§12.5 item 2).

   There is **no per-entry pointer field** on `ModuleEntry::Def` post-rollback. The runtime function pointer for a callable entry is not a separate `#[serde(skip)]` field — it lives in `SymbolTable.got`'s slot indexed by `ModuleEntry::Def.got_slot`, where `got_slot: Option<usize>` is a plain index field that **IS persisted** (no skip; cache-restore preserves the slot assignment so re-codegen writes into the same slot). The GOT itself is `#[serde(skip)]` and re-allocated empty on deserialise; the slot indices are stable across serialise/deserialise so the post-restore re-codegen converges to the same `(slot → ptr)` mapping the pre-serialise codegen produced.

   This is the fundamental cache-restore invariant for Step 5b (§12.5). /typecheck's contract is that the three new structural-decl fields (`imports`, `exports`, `platforms`, `submodules` per §11.1 — four `Vec<T>` fields collectively, all persisted) participate in serde without quirks — they are plain `Vec<T>` of `Serialize + Deserialize` types and the existing `#[derive(Serialize, Deserialize)]` on `SymbolTable` covers them. A /typecheck unit test in `crates/cranelisp-types/src/module.rs` SHOULD assert this round-trip on a fixture with non-empty values in all four structural-decl fields; runtime-only fields (`got`, `code`, `linker`) deserialise to default `Arc<GotTable>` / `None` / `None` respectively and are not part of the structural identity check.

   **Primitives carve-out (Decision 0048)**: primitives never round-trip through serde — they are statically constructed in-crate at `cranelisp-primitives` initialisation and never participate in cache-restore. The round-trip invariant scope is user-module symbol tables only.

### 11.4 What dissolves: `ModuleStructure` in `src/save.rs`

The Sprint-57 transitional `ModuleStructure` struct in `src/save.rs` (see SPRINT.md Step 5a description: "delete `ModuleStructure` from `SharedState`") is *not* `cranelisp-types` code, so /typecheck does not edit it. From the typecheck POV the dissolution is sound because:

- Every field on `ModuleStructure` (`import_specs`, `export_specs`, `mod_decls`, `platform_specs` per /arch finding) maps 1:1 onto one of the four new `SymbolTable` fields with identical element types.
- The `SharedState.module_structures: DashMap<ModuleFullPath, ModuleStructure>` parallel store is exactly the kind of duplication Decision 33 cites — Principle 7 violation (the same structural record in two places, where they can drift). Dissolving it is structurally sound regardless of the typecheck crate's involvement.
- After dissolution, `src/save.rs::generate_module_source` reads the four fields from the `SymbolTable` it already holds (it already calls `tc.symbol_tables.get(&module)` for `symbols`-side regeneration), so no new lookup path is introduced.

/typecheck's read-side observation: nothing in `cranelisp-typecheck` reads from `ModuleStructure` today (the struct is `/int`-side scaffolding). The dissolution is invisible to typecheck-crate code and tests.

### 11.5 Read-side from typecheck

`cranelisp-typecheck` itself has limited interest in the four new fields. Today, the import-resolver lives in `crates/cranelisp-typecheck/src/imports.rs` (and reads from `tc.imports[&module]`-style transitional structures); after Step 5a, that same resolver migrates to read from `symbol_table.imports` directly. The migration is local to the resolver — it does not change Algorithm W, unification, or any other part of the typecheck crate. Specifically:

- The resolver reads `imports` to enumerate the `(import [M [names]])` requests it must satisfy.
- The resolver reads `exports` to validate that names actually requested for re-export are in `symbols` (or are valid `ModuleEntry::Import` chains it can re-export).
- The resolver does *not* read `platforms` or `submodules` directly; those are consumed by `/int` and `/platform` respectively.

The migration is a Wave 2 task; this section commits to the read-shape so /int's writer matches.

### 11.6 Cosmetic plan: stale `infer.rs:828` doc-comment

`crates/cranelisp-typecheck/src/infer.rs:828` carries a doc-comment describing the retired `(run-tests init pass-fn fail-fn)` special form, but the function it annotates is `infer_annotate` (type ascription via `(:Type expr)`). The current text is verbatim:

```text
/// Infer the type of `(run-tests init pass-fn fail-fn)`.
///
/// - `init` determines the accumulator type `:a`
/// - `pass_fn :: (Fn [:a String Int] :a)`
```

The fix (Wave 2 implementation, plan-only here) is a one-block edit:

1. Delete the `// FIXME(/typecheck): ...` block (lines 828–833) — no longer needed once corrected.
2. Replace the `///` block (lines 834–837) with a one-line doc-comment matching `infer_annotate`'s actual behaviour:
   ```text
   /// Infer the type of an annotated expression `(:T e)` per spec §3.5.
   /// Resolves the type expression `T`, infers the body's type, unifies the two,
   /// and records the resolved type at `span`.
   ```

That accurately describes the body: `infer_annotate` resolves `annotation` to a concrete `Type` via `resolve_type_expr`, runs `infer_expr` on the inner expression, unifies the two types at `span`, applies the substitution, records the resolved type, and returns it. No behavioural change; comment-only edit.

The Wave 2 actual edit is one `Edit` call on one file. No tests are affected (doc-comments do not affect test outcomes), and there is no other `infer_annotate` documentation site to keep in sync.

---

## 12. Sprint 58 Wave 1 — Phase 5 Step 5c: `SymbolTable<C, L>` Generics Activation

Phase 5 Step 5c parameterises `SymbolTable` and `ModuleEntry` over two type parameters — `C: CodeStore` (the per-function compiled-code store) and `L: LinkerStore` (the per-module linker store). The generics are the DAG-compatible mechanism for placing `Arc<cranelisp_backend::jit::Jit>` directly on `ModuleEntry::Def.code` without inverting the `cranelisp-types → cranelisp-backend` dependency edge (Principle 3). This is the §9.1 normative shape and the gap G12 in `pipeline-v4-roadmap.md`. After Step 5c lands, Decision 31 Scenario 2 fires per redefinition (REPL `/mem` shows live-bytes drop on the redefinition, not just at session teardown).

This section is the typecheck-side observation. The structural change lives entirely in `cranelisp-types` (the trait definitions + parameterisation) and `src/session_v4.rs` (the concrete-type instantiation). /typecheck commits that the change does not alter Algorithm W, unification, constraint solving, monomorphisation, or any part of the inference engine — typecheck is genericity-blind.

### 12.1 Trait surface — empty markers in `cranelisp-types`

Per Decision 32, `CodeStore` and `LinkerStore` are empty marker traits with blanket impls:

```rust
// crates/cranelisp-types/src/module.rs (Step 5c additions)
pub trait CodeStore: Send + Sync + 'static {}
impl<T: Send + Sync + 'static> CodeStore for T {}

pub trait LinkerStore: Send + Sync + 'static {}
impl<T: Send + Sync + 'static> LinkerStore for T {}
```

Both default to `()`:

```rust
pub struct SymbolTable<C: CodeStore = (), L: LinkerStore = ()> { ... }
pub enum ModuleEntry<C: CodeStore = ()> { ... }
```

The defaults are load-bearing for /typecheck's invariant (§12.2): every typecheck-crate function signature continues to read `SymbolTable` (resolved as `SymbolTable<(), ()>` thanks to the defaults) without touching `<C, L>` annotations. This is the §"Coherence checklist" item — "Mode differences expressed as parameters" — applied to compile-time generics rather than function arguments.

**Why empty markers, not method-bearing traits.** Decision 32 records the rationale in full; the typecheck-side reason is narrow but compelling: a method-bearing `CodeStore` trait would have to declare `fn drop_code(&self)` or `fn code_ptr(&self) -> *const u8` (or similar), which forces `cranelisp-types` to know about Cranelift JIT pages. That inverts the dependency edge that Principle 3 protects (`cranelisp-types → cranelisp-backend` is forbidden). Empty markers add the necessary type-system handle — "this concrete type is the per-function code store" — without smuggling Cranelift types into the contract surface.

**Why a blanket impl.** `impl<T: Send + Sync + 'static> CodeStore for T {}` means any `Send + Sync + 'static` type the integration layer chooses for `C` automatically satisfies the bound — no per-call-site `impl CodeStore for Arc<Jit>` line. This avoids friction at the instantiation site (`src/session_v4.rs`) and at any future newtype the integration layer decides to wrap around `Arc<Jit>`. The `Send + Sync + 'static` requirement is the irreducible minimum for `SymbolTable` to be `Send + Sync` and live in the `DashMap<ModuleFullPath, SymbolTable<C, L>>` that backs `tc.symbol_tables` — `()` trivially satisfies it.

### 12.2 Typecheck never observes `C` or `L`

Typecheck's authoritative claim: every function signature in `cranelisp-typecheck/src/*` continues to read `SymbolTable` (i.e., `SymbolTable<(), ()>`) after Step 5c lands, with no `<C, L>` propagation into typecheck APIs. The justification:

1. **Decision 25 ownership boundary**: typecheck *writes* the `ast` field of `ModuleEntry::Def` (after `check_form(CheckBody)` succeeds — §3.4). Typecheck *never reads or writes* the `code` field — that is exclusively the backend's responsibility (`/backend` writes after `compile_to_module` returns; `/int` reads at JIT call sites and at `/clif` / `/disasm` introspection). The `code` field is the only place `C` appears on `ModuleEntry::Def`. Symmetrically, `linker: Option<L>` lives on `SymbolTable` itself and is exclusively `/int` / `/backend` territory.

2. **Default-`()` propagation**: when typecheck-crate code writes `&SymbolTable` in a signature, Rust's default-type-parameter resolution treats it as `&SymbolTable<(), ()>`. The `code: Option<C>` field is `Option<()>` — a one-byte zero-sized-option that is always `None` from typecheck's POV. Writing `entry.ast = Some(defn)` works irrespective of `C` (the field is `Option<Defn>`, not parameterised). Writing `entry.code = Some(...)` would require `C = ()` and would write `Some(())` — which typecheck never does, because typecheck never owns compiled code.

3. **Pattern-matching on `ModuleEntry`**: typecheck pattern-matches on `ModuleEntry::Def { ast, kind, scheme, .. }` etc. Pattern matching with `..` ignores the `code` field entirely — no annotation churn for typecheck patterns. (The unused `code` field is silently `Option<()>` from typecheck's POV; visits-via-`..`.) `got_slot` is a plain `Option<usize>` and pattern-matchable when needed, but typecheck typically ignores it (it's allocated by the registration site, read by codegen). Post-rollback (Decision 0035 S66 amendment + Decision 0041) there is no per-entry pointer field on `ModuleEntry::Def`; the runtime ptr lives in `SymbolTable.got` indexed by `got_slot` — never pattern-matched by typecheck.

4. **Constructing `ModuleEntry::Def`**: typecheck constructs `ModuleEntry::Def` in two places — `register_defn_signature` (Pass 1) and `register_mono_entry` (§9.4 helper). Both sites write `code: None` literally. After Step 5c, `code: None` becomes `code: Option::<()>::None` by default-`()` resolution; the literal `None` continues to work without annotation because Rust infers the type parameter from context (the surrounding `SymbolTable<(), ()>` the entry is being inserted into). For the `got_slot` field: `got_slot: Some(slot)` is allocated via `SymbolTable::allocate_got_slot()` at registration time for any addressable callable entry; for non-addressable kinds (TypeDef, TraitDecl, Macro, Overloaded base, constrained-fn templates) `got_slot: None`. There is no `platform_fn_ptr` / `fn_ptr` field to initialise — the S66 fn_ptr unification (`b09ec76`) was rolled back the same day (`1dc57ae`) as redundant with the per-module `GotTable` (Decision 0035 S66 amendment).

5. **Forward-flowing unit tests**: `crates/cranelisp-types/src/module.rs` test fixtures (e.g., `mk_def` at line 426 — see §9.5 reference) construct `ModuleEntry::Def` with `code: None`. These tests are `cranelisp-types`-internal and continue to compile because the `()` default applies. /typecheck's authority over these tests confirms: no test in `cranelisp-typecheck` requires updating to add `<(), ()>` annotations.

**Consequence for /typecheck's Wave 2 work**: zero implementation changes to `cranelisp-typecheck/src/*`. The changes to `cranelisp-types/src/module.rs` (trait additions, parameterisation) are owned by /typecheck and land alongside §11's structural-decl fields; the call-site sweep across `src/`, `crates/cranelisp-backend/`, `crates/cranelisp-frontend/` is /int + /backend territory. /typecheck's only Wave 2 implementation touches are:

- Add `pub trait CodeStore` + blanket impl + `pub trait LinkerStore` + blanket impl to `crates/cranelisp-types/src/module.rs`.
- Parameterise `SymbolTable` and `ModuleEntry` per the `interfaces.md` shape.
- Add `code: Option<C>` to `ModuleEntry::Def` (re-using the existing `code: Option<Code>` field by replacing the concrete `Code` with `C`; the `#[serde(skip)]` discipline carries over verbatim).
- Add `linker: Option<L>` to `SymbolTable` (new field, `#[serde(skip)]`).
- Update the `cranelisp-types` unit tests to match (the `mk_def` fixture and similar) — most should compile unchanged thanks to default-`()` resolution; if any need an explicit `SymbolTable::<(), ()>::new(...)` annotation, that is a one-line edit.

The `Code` type itself (currently `crates/cranelisp-types/src/code.rs` per the current `ModuleEntry::Def.code: Option<Code>` shape — confirmed via `crates/cranelisp-types/src/lib.rs` re-export at the top of `module.rs`) does not move. The current concrete `Code` becomes the integration layer's chosen `C` — likely `Code` directly, or a newtype wrapping `Arc<Jit>` + the existing fields, per /int's `symbol-table-generics.md` design doc (forthcoming Wave 1).

### 12.3 Why typecheck does not observe `Arc<Jit>` lifetime

Decision 31's Scenario 2 — per-redefinition JIT reclaim — is the headline behavioural payoff of Step 5c. The reclaim primitive is the `Arc<Jit>` refcount reaching zero on the *last* `ModuleEntry::Def.code` referencing it; the custom `Drop` on the `Jit` wrapper then calls `unsafe JITModule::free_memory()`. This entire mechanism is invisible to typecheck:

- /typecheck never holds an `Arc<Jit>`. Typecheck operates on `SymbolTable<(), ()>` so `code: Option<()>` is unconditionally `None` from typecheck's POV.
- /typecheck never causes `Arc<Jit>` clones or drops. The clones happen at `compile_to_module`'s code-write site (`/backend`-owned); the drops happen at `ModuleEntry::Def.code` overwrite (REPL redefinition, `/int`-owned) or at session teardown (the integration layer's session-drop, `/int`-owned).
- /typecheck's REPL additive strategy (§8.4) — redefining a function replaces the `ModuleEntry::Def` entry — is the *trigger* for Decision 31 Scenario 2, but the trigger fires at the *integration-layer write site*, not at the typecheck-crate write site. Typecheck constructs the new `ModuleEntry::Def` value (with `code: None`); /int swaps it into the symbol table and the old entry's `Arc<Jit>` clone drops as part of `HashMap::insert`'s overwrite semantics.

The safety invariant from Decision 31 (no `fn` pointer derived from a JIT reachable when the Arc refcount hits 0) holds at the `/int` + `/backend` boundary; /typecheck has no role in maintaining or weakening it.

### 12.4 Concrete-type instantiation site

Per Decision 32 + the SPRINT.md /int Step 5c Approach, the single concrete-type instantiation site is `src/session_v4.rs`. The integration layer chooses:

- `C = Arc<cranelisp_backend::jit::Jit>` (or a thin newtype `Code` wrapping `Arc<Jit>` plus the raw `*const u8` code pointer that the GOT slot needs — /int's `symbol-table-generics.md` design picks one).
- `L = cranelisp_backend::cache::Linker` (or equivalent thin wrapper, similarly /int's choice).

The session-level `tc.symbol_tables: DashMap<ModuleFullPath, SymbolTable<Code, Linker>>` at the session boundary, with `tc.symbol_tables_view()` (or equivalent) returning `&DashMap<ModuleFullPath, SymbolTable<(), ()>>` for typecheck-crate consumption — *if* typecheck-crate code needs to read entries from the session. (In practice, typecheck operates per-module on its own `SymbolTable<(), ()>` instance and merges results back via the worker's symbol-table-write path; it does not need a typed view of the integration-layer's parameterised store.)

The `SymbolTable<(), ()>` ↔ `SymbolTable<Code, Linker>` boundary is *not* a runtime cast — it is a compile-time view of the same data with different default-parameter resolution at different call sites. Typecheck's `SymbolTable` reads `code: Option<()>`; integration-layer's `SymbolTable<Code, Linker>` reads `code: Option<Code>`. Because `code` is `#[serde(skip)]`, the two views have an identical *serialised* representation, which is what makes cache-restore (§12.5) trivially work across the boundary.

/typecheck does not pre-empt /int's choice between `C = Arc<Jit>` directly versus `C = Code` (where `Code` newtype-wraps `Arc<Jit>` + fields). Either satisfies `CodeStore`'s `Send + Sync + 'static` blanket bound. Whichever /int picks, the typecheck-side observation is unchanged: typecheck sees `()` and never observes the choice.

### 12.5 Cache restore — Step 5b interaction

Step 5b serialises `SymbolTable` (with the Step 5a structural-decl fields populated and the Step 5c `code` and `linker` fields skipped, plus `SymbolTable.got` skipped) to `.meta.json`. Cache-restore deserialises it back. The typecheck-side observation:

1. **Cache-restore deserialises into `SymbolTable<(), ()>` directly**. The cache reader's deserialisation target is the typecheck-crate's view — `SymbolTable` with the default `<(), ()>` resolution. The `code: Option<()>` field is unconditionally `None` after deserialisation (it is `#[serde(skip)]`; `()` re-initialises trivially). `linker: Option<()>` is also `None` (`#[serde(skip)]`). `SymbolTable.got: Arc<GotTable>` is `#[serde(skip)]` and re-initialises to a fresh empty `GotTable`; the `got_slot` indices on `ModuleEntry::Def` ARE persisted (plain `Option<usize>`), so re-codegen re-populates the same slot positions. There is no `platform_fn_ptr` / `fn_ptr` field post-rollback (Decision 0035 S66 amendment + Decision 0041) — the runtime ptr lives in the GOT, not as a sibling field. **Cache-restore therefore produces a structurally complete typecheck-side view without any re-typechecking.**

2. **Code is re-derived by re-codegen, not deserialised**. After cache-restore, the priority worker walks `defined_symbols()` (§9.5) over each module's `SymbolTable` and runs `compile_to_module` over the entries that codegen needs to materialise. The new code populates `code: Option<C>` at the integration-layer's parameterised view (`C = Code` / `Arc<Jit>` per §12.4). This is the same code-write path used on a fresh build — no cache-specific code path.

3. **Platform fn ptrs are re-resolved from the manifest**. Per Decision 26's serialisation discipline, platform fn ptrs are re-derived on cache-hit load by re-opening the DLL referenced by the corresponding `PlatformDecl` entry and reading its manifest. This is `/platform`'s territory (the addendum to `design/platform/platform-registry-removal.md` per the SPRINT.md /platform task). Typecheck has no role in the re-resolution.

4. **`schema_version` discipline (Decision 34)**. The `schema_version: u32` field on the serialised `SymbolTable` (via `#[serde(default)]`, `interfaces.md` line 891) gates cache-restore: if the deserialised version does not match the current `CACHE_SCHEMA_VERSION` constant (owned by `/backend` in `crates/cranelisp-backend/src/cache/mod.rs`), the cache entry is treated as stale and the source is re-typechecked. /typecheck's commitment: every shape-changing field addition to `SymbolTable` or `ModuleEntry` (deletion, type change, or non-default field addition) MUST coordinate with `/backend` to bump `CACHE_SCHEMA_VERSION`. /typecheck is the field-shape owner for `cranelisp-types/src/module.rs`, so /typecheck triggers the bump request via FIXME(/backend) on `cache/mod.rs` when a shape-changing edit lands.

5. **Round-trip invariant (echoed from §11.3 item 6)**. A `SymbolTable<(), ()>` serialised via `serde_json::to_string` and deserialised via `serde_json::from_str` MUST be structurally identical modulo `#[serde(skip)]` fields. This is the fundamental contract Step 5b is built on. /typecheck's contribution to validating it is a unit test in `crates/cranelisp-types/src/module.rs` (see §11.3 item 6 — the same test covers both Step 5a and Step 5b).

**Typecheck-side invariants survive serialise→deserialise.** Specifically:
- `SymbolTable.symbols` round-trips: every `ModuleEntry::Def` with `ast: Some(defn)` retains the annotated `Defn` (the `inferred_type` and `resolved_call` annotations on AST nodes are `Box<Type>` / `Box<ResolvedCall>` and serialise via the `#[serde(default)]` discipline established in §3 / §8.5).
- `SymbolTable.next_got_slot` round-trips (it is a `usize` with `#[serde(default)]`; the GOT itself is `#[serde(skip)]` and re-initialises to a fresh empty `GotTable` — codegen re-populates).
- The four Step 5a structural-decl fields round-trip per §11.3 item 6.
- `schema_version` round-trips; mismatch triggers stale-cache treatment.

After cache-restore, typecheck's view of the module is *identical* to a fresh-typechecked view (modulo the runtime-only fields that fresh-typecheck would also leave empty pre-codegen). No re-typechecking is triggered by cache-restore for valid (`schema_version`-matching) cache entries; this is the convergence payoff of Step 5b.

### 12.6 Sketch comparison

The sketch (`sketch/src/typechecker.rs`) does not parameterise its symbol table. Compiled code lives on `CompiledModule` (the prototype's pre-decomposition shape) as a concrete `JitModule` field, and `cranelisp-types` (in the prototype) directly depends on Cranelift JIT — Principle 3 violation that the reimplementation explicitly corrects. The sketch had no `CodeStore` / `LinkerStore` traits, no `SymbolTable<C, L>` shape, and no per-redefinition reclaim mechanism — its REPL leaks JIT pages on every redefinition (the same Cranelift `Memory::drop` leak Decision 31 documents, with no mitigation).

**Divergence**: the reimplementation's empty-marker traits + default-`()` parameterisation gives the same data shape from typecheck's POV (typecheck operates on a concrete-`()` symbol table, never observes `C`) while keeping the integration layer free to choose the concrete `C` that delivers per-redefinition reclaim. This is the "narrow interface" rationale (Principle 2): typecheck sees the minimum surface area (`SymbolTable<(), ()>` is genericity-blind), while the integration layer sees the maximum (`SymbolTable<Code, Linker>` carries the JIT lifetime story).

The sketch's design works for a single-pipeline single-threaded prototype; the reimplementation's concurrent pipeline + per-redefinition reclaim require the parameterised shape. The divergence is justified by the audit findings that catalogue the prototype's lifecycle defects (the `JitModule` lifetime story is one of the 15 HIGH-severity findings in `sketch/audits/`).

### 12.7 Cross-references

- `design/arch/CLAUDE.md` Decision 32 — `CodeStore` / `LinkerStore` trait shape (canonical).
- `design/arch/CLAUDE.md` Decision 25 — `code` field placement on `ModuleEntry::Def` + Decision 31's Scenario 2 cross-reference.
- `design/arch/CLAUDE.md` Decision 31 — JIT lifetime + Scenario 2 reclaim (the behavioural payoff Step 5c delivers).
- `design/arch/CLAUDE.md` Decision 33 — structural decls on `SymbolTable` (companion to §11).
- `design/arch/CLAUDE.md` Decision 34 — cache schema versioning (companion to §12.5).
- `design/arch/interfaces.md` §"Symbol Table" — target shape (lines 858–931).
- `design/arch/interfaces.md` §"Module Entries" — `ModuleEntry<C>` parameterisation (lines 944–1064).
- `design/arch/pipeline-v4-roadmap.md` Phase 5 Step 5a / 5b / 5c — the migration plan this section observes.
- `design/int/symbol-table-cache.md` (forthcoming Wave 1) — /int's writer-side design for Step 5b.
- `design/int/symbol-table-generics.md` (forthcoming Wave 1) — /int's call-site sweep design for Step 5c, including the concrete-`C` choice.
- `design/backend/module-caching.md` (Wave 1 update) — /backend's cache-restore design for Step 5b.
