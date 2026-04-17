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

`TopLevel::TraitImpl` forms produce method entries via the existing trait impl registration path. Each method within a `TraitImpl` becomes a `ModuleEntry::Def` with a mangled name (e.g., `Display.show$Option$Int`). These entries get `ast: Some(method_defn)` after body checking, same as regular defns.

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

The current inference flow:

1. `check_form_body_single_defn(state, defn, accumulator)` calls `check_defn_body(state, defn, ...)`.
2. Inside `check_defn_body`, inference calls `record_expr_type(state, span, ty)` which writes to `state.expr_types`.
3. Trait/builtin resolution writes to `state.method_resolutions`.
4. After body checking, the method extracts new entries from `state.expr_types` and `state.method_resolutions` (delta from before/after snapshots) into `FormCheckResult`.

The new flow replaces side maps with direct AST annotation. Annotation happens in two stages: the initial `infer_expr` dual-write, and then post-pass AST updates that complete the annotation.

**Stage 1 — `infer_expr` dual-write:**

1. `check_form_body_single_defn` clones the `Defn` to get a mutable copy.
2. Body checking proceeds with `infer_expr` taking `&mut Expr`. When inference determines an expression's type, it writes `expr.set_inferred_type(Some(Box::new(ty)))` directly on the node in addition to `state.expr_types`.
3. For `Expr::Apply`, when method resolution determines the resolved call during inference, it writes `apply.resolved_call = Some(Box::new(resolution))` directly on the node.
4. At this point, AST annotations are **incomplete**: `inferred_type` fields contain pre-substitution types (may contain `Var(N)` type variables), and several categories of `resolved_call` are missing because they are determined by post-passes that run after `infer_expr` returns.

**Stage 2 — post-pass AST updates** (see Section 3.6 for details):

5. Post-passes (`resolve_deferred_trait_calls`, `resolve_pending_overloads`, `resolve_auto_curry`) run and update AST nodes directly, filling in the `resolved_call` fields that were left `None` during inference.
6. A final substitution walk applies `apply(&state.subst, ty)` to every `inferred_type` on every AST node, replacing `Var(N)` type variables with their concrete bindings.
7. After all post-passes and final substitution complete, the fully annotated `Defn` is written to `ModuleEntry::Def.ast`.

**Dual-write period (Step 1b)**: During the migration, both paths are populated — `state.expr_types` / `state.method_resolutions` (old) AND the AST node fields (new). This enables verification assertions. Once Step 1c switches all readers to AST nodes, the old side maps can be removed (Step 1d).

**`&mut Expr` threading**: `infer_expr` takes `&mut Expr`. Since the `Defn` is cloned at the start of body checking, all mutation is on the clone — the original AST is untouched. The clone becomes the annotated version stored on `ModuleEntry::Def.ast`.

**Helper method on Expr**: Add `fn set_inferred_type(&mut self, ty: Option<Box<Type>>)` that matches on self and sets the field. This keeps the mutation localized — callers don't need to match on every variant.

### 3.5 Dual-Write Verification

During Step 1b, both paths are populated:

- **Old path**: `FormCheckResult.method_resolutions` and `FormCheckResult.expr_types` flow into `ModuleCheckAccumulator`, then into `CheckResult`.
- **New path**: `Expr.inferred_type` and `Expr::Apply.resolved_call` on the annotated AST stored in `ModuleEntry::Def.ast`.

Verification assertions (debug-only, via `debug_assert!`) run **after all post-passes and final substitution** — not after `infer_expr` alone. This is critical because the AST is incomplete until the post-passes in Section 3.6 have run.

Verification assertions:

1. After `finalize_check_result_inner` completes (i.e., after all post-passes, final substitution walk, and AST write to `ModuleEntry::Def.ast`), walk each annotated `Defn` AST.
2. For every `Expr` node with `inferred_type.is_some()`, assert that the accumulated `expr_types` (after `apply(&state.subst, ty)`) has an entry for that span with the same type.
3. For every `Expr::Apply` with `resolved_call.is_some()`, assert that the accumulated `method_resolutions` has a matching entry for that span.
4. Assert completeness: every entry in the side maps has a corresponding AST annotation. This catches cases where a post-pass wrote to a side map but failed to update the AST node.

These assertions run in test builds and CI. They do not run in release builds (no performance impact). They are removed in Step 1d when the side maps are deleted.

### 3.6 Post-Pass AST Update

The initial `infer_expr` dual-write (Section 3.4, Stage 1) does NOT fully annotate the AST. The typecheck pipeline has multiple post-passes in `finalize_check_result_inner` that determine additional resolutions and apply final type substitutions. Each post-pass must update AST nodes directly — not just the side maps.

#### 3.6.1 Post-Passes That Add Resolutions

**Phase 3 — `resolve_deferred_trait_calls`** (`infer.rs:504`): Walks the AST to resolve trait method calls that were deferred during `infer_expr` because the concrete type was not yet known. Currently takes `&Expr` and writes only to `state.method_resolutions`. The change: take `&mut Expr`, and when a resolution is found for an `Expr::Apply` node, write `resolved_call = Some(Box::new(resolution))` on the node in addition to the side map. This pass already walks the AST recursively, so the structural change is minimal — it gains `&mut` access and sets the field alongside the existing `state.method_resolutions.insert()`.

**Pass 2.5 — `resolve_multi_sig_overloads`**: Resolves multi-sig function dispatch. Currently produces internal variant `Defn`s with `resolved_call` entries written to `state.method_resolutions`. The internal defns created here must have their AST nodes annotated with `resolved_call` before being written to `ModuleEntry::Def.ast`.

**Pass 5 — `resolve_pending_overloads`** (`program.rs:1395`): Resolves overloaded function calls from `state.pending_overload_resolutions`. Currently writes `ResolvedCall::SigDispatch` entries to `state.method_resolutions` keyed by span. The change: after writing to the side map, also locate the `Expr::Apply` node in the relevant `Defn`'s AST and set its `resolved_call`. Since this pass operates on spans rather than AST references, the implementation has two options:

- **(a) Deferred node update**: accumulate the set of `(span, resolution)` pairs from the post-pass, then do a single AST walk per defn to apply them. This is a targeted Span-keyed write (not a general-purpose enrichment) that runs inside the typecheck crate and is eliminated when side maps are removed.
- **(b) Mutable AST references**: thread `&mut Defn` references through the pass. This is cleaner but requires restructuring `pending_overload_resolutions` to store AST path information rather than spans.

Option (a) is acceptable for the migration period. Option (b) is the target for Step 1d.

**Pass 5 — `resolve_auto_curry`** (`program.rs:2382`): Resolves auto-curry call sites from `state.pending_auto_curry`. Currently writes `ResolvedCall::AutoCurry` entries to `state.method_resolutions`. Same approach as `resolve_pending_overloads`: accumulate resolutions, then walk and apply to AST nodes.

**REPL-path — `monomorphise_expr_calls`** (`program.rs:2141`): Called from `check_repl_input_inner` (lines 1555, 1573) after `resolve_auto_curry`. Scans an expression or defn body for call sites to constrained polymorphic functions, monomorphises them on demand, and writes `ResolvedCall::SigDispatch` entries to `state.method_resolutions` for each resolved call site. These entries must also be propagated to the corresponding `Expr::Apply.resolved_call` nodes. Same deferred-node-update approach as `resolve_pending_overloads`: accumulate `(span, resolution)` pairs, then walk the AST to apply them. This pass is REPL-only — the batch path handles monomorphisation via `pass4_monomorphise` in `finalize_check_result_inner`.

#### 3.6.2 Final Substitution Walk

After all post-passes complete, a final AST walk applies `apply(&state.subst, ty)` to every `inferred_type` on every `Expr` node in every annotated `Defn`. This replaces `Var(N)` type variables with their concrete bindings.

The walk is a simple recursive traversal:

```rust
fn apply_subst_to_ast(subst: &Substitution, defn: &mut Defn) {
    for variant in &mut defn.variants {
        apply_subst_to_expr(subst, &mut variant.body);
    }
}

fn apply_subst_to_expr(subst: &Substitution, expr: &mut Expr) {
    if let Some(ty) = expr.inferred_type_mut() {
        *ty = Box::new(apply(subst, ty));
    }
    // Recurse into children (Let bindings, Apply args, Match arms, etc.)
    // ... same recursive structure as resolve_deferred_trait_calls
}
```

This replaces the current bulk resolution in `finalize_check_result_inner` (lines 868-872 of `program.rs`) which builds a new `HashMap<Span, Type>` by applying substitution to the accumulated `expr_types`. After this change, the AST nodes contain the final resolved types directly.

#### 3.6.3 Ordering

The complete annotation pipeline within `finalize_check_result_inner`:

1. **Phase 2 — Generalize**: finalize function schemes (no AST changes).
2. **Phase 3 — `resolve_deferred_trait_calls`**: walk each defn's `&mut` AST, set `resolved_call` on newly-resolved `Apply` nodes.
3. **Pass 2.5 — `resolve_multi_sig_overloads`**: annotate internal variant ASTs.
4. **Pass 3 — `detect_constrained_fns`**: identify constrained functions (no AST changes).
5. **Pass 4 — `pass4_monomorphise`**: generate mono defns with annotated ASTs (see Section 3.6.4).
6. **Pass 5 — `resolve_pending_overloads`**: set `resolved_call` on overload call sites.
7. **Pass 5 — `resolve_auto_curry`**: set `resolved_call` on auto-curry call sites.
8. **Final substitution walk**: apply `subst` to all `inferred_type` fields on all annotated ASTs.
9. **Write to `ModuleEntry::Def.ast`**: the fully annotated `Defn` is stored.

After step 9, AST nodes are self-contained. No Span-keyed enrichment in the integration layer is needed.

**Critical implementation note — Phase 3 must iterate stored ASTs, not `working_program`**: The current `finalize_check_result_inner` receives `working_program: &[TopLevel]` and Phase 3 walks those input AST bodies via `resolve_deferred_trait_calls(state, defn.body())`. These are the *original* unannotated ASTs — not the annotated clones stored on `ModuleEntry::Def.ast` by `check_form_body_single_defn`. With the `&mut` approach, Phase 3 must instead iterate the annotated ASTs stored on `ModuleEntry::Def.ast`, so that deferred trait resolutions are written to the same `Defn` that codegen will later read. Concretely: instead of `for top in working_program`, Phase 3 must iterate over the symbol table entries for the current module, take `&mut` references to each `ModuleEntry::Def.ast`, and call `resolve_deferred_trait_calls` on those. The `working_program` parameter is still needed for other passes (Pass 2.5 multi-sig structure, Pass 3 constrained-fn detection) but NOT for Phase 3 AST mutation.

#### 3.6.4 Mono Defn Annotation

Monomorphised defns are generated in `pass4_monomorphise`, which calls `monomorphise_constrained_fn` in `traits.rs`. That function calls `recheck_body_for_mono` which:

1. Calls `check_defn_body_with_types(state, &mut defn, ...)` — this runs `infer_expr` on the mono body with `&mut Defn`, so the Stage 1 dual-write annotates `inferred_type` and initial `resolved_call` fields on the mono body's AST nodes.
2. Calls `resolve_auto_curry(state)` — resolves auto-curry sites generated during mono re-check.
3. Captures `state.method_resolutions` and builds `mono_expr_types` with substitution applied.

The change for mono defns:

- After `resolve_auto_curry` in `recheck_body_for_mono`, apply the deferred-node-update pattern (Section 3.6.1) to set `resolved_call` on any auto-curry `Apply` nodes in the mono defn's AST.
- `resolve_inner_constrained_calls` adds `SigDispatch` entries for self-recursive constrained calls. These must also be applied to AST nodes.
- Apply the final substitution walk (Section 3.6.2) to the mono defn's AST before constructing the `MonoDefn`.
- The `MonoDefn.defn` stored on `ModuleEntry::Def.ast` (per Section 5.3) then carries fully resolved `inferred_type` and `resolved_call` on all nodes.

The `MonoDefn` struct's `resolutions` and `expr_types` fields become redundant once the AST is self-contained. They are retained during the dual-write period for verification, then removed in Step 1d.

#### 3.6.5 REPL Path

The REPL has three distinct entry points, each with its own post-pass sequence:

**`check_repl_input_inner` for `TopLevel::Expr`**: Calls `infer_expr` (Stage 1 dual-write on the expression), then `resolve_auto_curry`, then `monomorphise_expr_calls`. No `resolve_deferred_trait_calls` call — REPL expressions are typically simple. After `monomorphise_expr_calls`, the `SigDispatch` entries it writes to `state.method_resolutions` must be propagated to `Expr::Apply.resolved_call` nodes on the annotated expression. The final substitution walk must run on the expression before `build_repl_result`.

**`check_single_defn` for single-sig `TopLevel::Defn`**: This method has its own self-contained flow, separate from `finalize_check_result_inner`. The sequence is:

1. `register_defn_signature` — register signature in symbol table.
2. Clone the `Defn` and call `check_defn_body(state, &mut defn_clone, ...)` — Stage 1 dual-write annotates the clone.
3. `resolve_deferred_trait_calls(state, defn_clone.body())` — currently takes `&Expr`. Must change to `&mut Expr` so deferred resolutions are written to `resolved_call` on the clone's `Apply` nodes.
4. `generalize` — finalize the scheme.
5. Back in `check_repl_input_inner`: `resolve_auto_curry` — must propagate to the clone's AST nodes.
6. `monomorphise_expr_calls(state, defn.body())` — generates mono defns and writes `SigDispatch` entries to `state.method_resolutions`. Must propagate to the clone's AST nodes.
7. **Final substitution walk** on the annotated `defn_clone` — apply `subst` to every `inferred_type`. Currently `build_repl_result` calls `resolve_expr_types` on the side map; the AST walk replaces this.
8. Write `defn_clone` to `ModuleEntry::Def.ast` — currently `check_single_defn` does not do this; it must be added.

Note: `check_single_defn` currently stores the *original* `defn` (not the annotated clone) in `ConstrainedFn.defn`. This is correct — the constrained-fn template stores the original for later monomorphisation. The annotated clone goes to `ModuleEntry::Def.ast`.

**`check_repl_multi_sig` for multi-sig `TopLevel::Defn`**: Calls `resolve_deferred_trait_calls` per variant, then `resolve_variant_types` (analogous to Pass 2.5), then `resolve_pending_overloads`, then `resolve_auto_curry`. Same pattern: each post-pass must propagate to AST nodes on the annotated internal variant defns, and the final substitution walk must run before writing to `ModuleEntry::Def.ast`.

The `build_repl_result` method currently calls `resolve_expr_types` (which applies substitution to the `expr_types` side map). The AST substitution walk replaces this for the annotation path — it must run before `build_repl_result` is called, not inside it.

#### 3.6.6 No Integration-Layer Enrichment

The current integration layer (`src/worker.rs`) contains `enrich_defn_from_side_maps` — a function that walks the AST post-hoc and fills in missing/stale annotations from `CheckResult`'s side maps. This function exists precisely because the typecheck post-passes did not update AST nodes. It uses Span-keyed lookup with a "overwrite if `contains_var`" heuristic that is fragile: span keys from one defn can match spans from another defn in module-scoped side maps, and the heuristic does not handle all cases (e.g., a `resolved_call` that was `None` after `infer_expr` but should have been set by a post-pass).

With the changes in this section, `enrich_defn_from_side_maps` is eliminated. The typecheck crate is solely responsible for producing fully annotated ASTs. The integration layer reads `ModuleEntry::Def.ast` and passes it to codegen without modification. This is the pipeline-v4.md target: typecheck writes, codegen reads, no intermediate enrichment layer.

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

The sketch's `resolve_expr_types()` method (line 661) applied the final substitution to all expr types in bulk. The reimplementation applies substitution per-form in `finalize_check_result` (line 849-853 of `program.rs`). Both achieve the same result; the per-form approach is necessary for form-by-form processing.

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
