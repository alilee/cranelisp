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
