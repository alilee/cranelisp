# Sprint 2 Wave 2 Review — Per-Crate Code Review

**Reviewer**: `/review`
**Date**: 2026-03-05
**Scope**: Four implementation crates from Wave 2 (frontend, typecheck, backend, platform) plus cranelisp-types heap additions
**Against**: `design/review/ring1-checklist.md` (12 sections) + `design/review/checklist.md` (10 sections)
**Test results**: 594 tests, 0 failures, 0 ignored, clippy clean

---

## Summary

Wave 2 delivers a solid Ring 1 implementation. The heap infrastructure, ADTs with fields, and closures are well-structured and demonstrate continued adherence to the architectural principles established in Ring 0. The representation containment strategy (heap.rs as sole layout importer), the string opacity principle, and the base-pointer convention are all correctly implemented.

**Findings**: 0 Blocker, 3 Important, 9 Suggestion

No blockers. The Important findings should be addressed before Ring 1 gate; all are bounded in scope.

---

## Tooling Results

### cargo clippy --workspace

**CLEAN.** Zero warnings on all library and binary crates.

### cargo test --workspace

**ALL PASS.** 594 tests across all crates. Breakdown:

| Crate / Suite | Passed |
|---|---|
| cranelisp-types (unit) | 21 |
| cranelisp-platform (unit) | 0 |
| cranelisp-frontend (unit) | 99 + 8 (reader + ast_builder) |
| cranelisp-typecheck (unit) | 102 |
| cranelisp-backend (unit) | 23 |
| cranelisp-runtime (unit) | 42 |
| cranelisp (binary, unit) | 146 |
| ring0 (integration) | 126 |
| examples (integration) | 27 |
| **TOTAL** | **594** |

---

## Findings

### F-1: `compile_apply` exceeds 100-line guideline (I — Important)

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/crates/cranelisp-backend/src/compiler/apply.rs:20-164`
**Lines**: 145
**Checklist**: ring1-checklist section 7, general checklist section 2

`compile_apply` is the longest non-test function in the codebase at 145 lines. It handles TCO detection, method resolutions (builtin, trait, sig-dispatch, auto-curry), data constructor calls, closure calls, and direct calls. While each branch is well-commented and the structure is a clear dispatch chain, the length exceeds the 100-line guideline from `src/CLAUDE.md`.

**Recommendation**: Extract the method-resolution handling (lines 42-94) into a private helper `compile_resolved_call`. This would bring `compile_apply` under 100 lines and make the dispatch structure more visible. The extracted helper naturally groups the four `ResolvedCall` variants.

---

### F-2: `HeapCategory::classify` for ADT is approximate, not authoritative (I — Important)

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/crates/cranelisp-types/src/heap.rs:57-68`
**Checklist**: ring1-checklist sections 2.9, 4.3

The current classification uses `args.is_empty()` as a heuristic: nullary types with no type parameters are `NeverHeap`, parameterized types are `Mixed`. This is incorrect for several valid ADT configurations:

1. A non-parameterized ADT with data constructors (e.g., `(deftype IPoint (IPoint [:Int x :Int y]))`) has `args = []` but IS heap-allocated. It would be classified as `NeverHeap`.
2. A parameterized ADT with only nullary constructors (e.g., `(deftype (Phantom a) PhantomVal)`) has `args = [a]` but is NOT heap-allocated. It would be classified as `Mixed`.

Since Ring 1 does not yet wire RC into the expression pipeline (RC fields are `#[allow(dead_code)]`), this bug has no observable effect today. However, when Ring 2 activates RC emission, incorrect classification would cause either leaks (heap value classified as NeverHeap, never decremented) or crashes (bare tag classified as Mixed, RC operations on non-pointer value).

**Recommendation**: `HeapCategory::classify` should accept a reference to the `TypeDefInfo` registry (or a callback) so it can check whether the ADT actually has data constructors, not just whether it has type arguments. This is the "sole authority" principle from the checklist -- the classification must be correct for ALL types, not just the ones currently exercised. Mark this as a prerequisite for Ring 2 RC activation.

---

### F-3: `compile_defn` has 8 parameters with `#[allow(clippy::too_many_arguments)]` (I — Important)

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/crates/cranelisp-backend/src/jit.rs:181-243`
**Checklist**: ring1-checklist section 7, general checklist section 2

`Jit::compile_defn` takes `self` + 7 parameters: `defn`, `check`, `mode`, `func_ids`, `func_arities`, `got_slots`, `got_base_ptr`. The `#[allow(clippy::too_many_arguments)]` annotation suppresses the clippy warning rather than fixing the structural issue.

The last four parameters (`func_ids`, `func_arities`, `got_slots`, `got_base_ptr`) all describe the compilation environment. They are already bundled inside `CompileContext` for the `FnCompiler` -- the duplication occurs because `Jit::compile_defn` constructs a `CompileContext` from these pieces.

**Recommendation**: Accept a `CompileContext` (or a builder for one) as a single parameter rather than passing the fields individually. This would reduce `compile_defn` to 4 parameters (self + defn + check + ctx) and remove the clippy suppression. The construction of `CompileContext` would move to the call site (`compile_program`, `compile_and_run_expr_with_got`), which is also a cleaner responsibility split.

---

### F-4: `Type::is_heap()` exists alongside `HeapCategory::classify()` (S — Suggestion)

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/crates/cranelisp-types/src/types.rs:55-58`
**Checklist**: general checklist section 7a, ring1-checklist section 2.9

`Type::is_heap()` is a convenience method that returns `true` for `String | ADT | Fn`. It does NOT consult `HeapCategory::classify()` and has a different (simpler) classification logic -- it treats ALL ADTs as heap, whereas `classify` distinguishes nullary/parameterized. Currently unused (grep confirms zero call sites outside the definition), but its existence creates divergence risk. A future developer might call `is_heap()` instead of `classify()`, bypassing the authoritative source.

**Recommendation**: Either remove `Type::is_heap()` since it is unused, or document it with a prominent comment directing callers to use `HeapCategory::classify()` for RC decisions. The general checklist explicitly warns: "do not also provide `Type::is_heap()` -- having both creates divergence risk."

---

### F-5: Closure capture ordering is non-deterministic (S — Suggestion)

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/crates/cranelisp-backend/src/compiler/control_flow.rs:124-127`
**Checklist**: ring1-checklist section 5.8

`find_free_vars` returns variables in encounter order (pre-order traversal), then the captures list is filtered to those present in `self.variables`. Since `self.variables` is a `HashMap`, the `.filter().collect()` chain preserves the order from `find_free_vars`, which IS deterministic (pre-order traversal order). However, the ring1-checklist specifically calls out: "Captures are stored in a consistent order (e.g., sorted by variable name)."

The current approach is deterministic within a single compilation, so correctness is not at risk. However, sorted-by-name ordering is easier to reason about and debug.

**Recommendation**: Add a `.sort()` call on the captures vector after filtering, or document the current ordering guarantee explicitly in a comment. The determinism relies on a subtle invariant (HashSet insertion order in `find_free_vars` via the `seen` set), which is worth making explicit.

---

### F-6: No `SAFETY` comments on `unsafe` blocks in backend test code (S — Suggestion)

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/crates/cranelisp-backend/src/lib.rs:256,300,383-392,478-490`
**Checklist**: ring1-checklist section 7

Several test functions in the backend's `lib.rs` use `unsafe` blocks to call `cranelisp_runtime::read_string_as_str` and read raw heap memory, without `// SAFETY:` comments. While the checklist focuses on non-test code, consistent documentation of unsafe reasoning even in tests improves maintainability.

The `execute()` method on `CompiledProgram` does have a proper `// SAFETY:` doc comment on its `unsafe fn` declaration, which is good.

**Recommendation**: Add brief `// SAFETY:` comments to the unsafe blocks in test code, documenting why the pointer is valid (e.g., "just-compiled expression returned a HeapString base pointer").

---

### F-7: Missing `#[must_use]` on several public Result-returning functions (S — Suggestion)

**Checklist**: ring1-checklist section 7, general checklist section 7a

`#[must_use]` is present on `cranelisp_frontend::parse`, `TypeChecker::check_program`, and `TypeChecker::check_repl_input`. However, the following public Result-returning functions lack it:

- `cranelisp_backend::compile_program`
- `cranelisp_backend::compile_and_run_expr_with_got`
- `cranelisp_backend::CompiledProgram::execute`
- `cranelisp_backend::Jit::new`

This was noted as a Sprint 1 deferred item (M-5) and should be addressed during Ring 1.

**Recommendation**: Add `#[must_use]` annotations to all public `Result`-returning functions in the backend crate.

---

### F-8: `compile_lambda_body` creates `FnCompiler` by struct literal (S — Suggestion)

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/crates/cranelisp-backend/src/compiler/control_flow.rs:249-264`
**Checklist**: ring1-checklist section 5.9

The `compile_lambda_body` method constructs `FnCompiler` with a 16-field struct literal. The `compile_fn_wrapper_body` method does not (it uses a different approach via raw `FunctionBuilder`). The ring1-checklist specifically warns: "A single `inner_compiler()` method or builder creates inner `FnCompiler` instances for lambda bodies, continuations, and drop glue. No copy-pasted struct literals with 20+ fields."

Currently there is only one struct literal construction site (in `compile_lambda_body`; the main `compile_body` also constructs one but with different semantics as the outermost function). When Ring 2 adds drop glue compilation, a second inner construction site will appear, at which point the duplication risk materializes.

**Recommendation**: Extract a `FnCompiler::inner(module, ctx, last_uses) -> Self` constructor that creates an inner compiler with default values for TCO, scope, and RC fields. This provides the single construction point that the checklist calls for, before the second use case arrives.

---

### F-9: `CompileContext` fields copied manually in `compile_lambda_body` (S — Suggestion)

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/crates/cranelisp-backend/src/compiler/control_flow.rs:233-247`
**Checklist**: general checklist section 6

The `CompileContext` is constructed field-by-field from `self.ctx` in `compile_lambda_body`:

```rust
let inner_compile_ctx = super::CompileContext {
    method_resolutions: self.ctx.method_resolutions,
    expr_types: self.ctx.expr_types,
    func_ids: self.ctx.func_ids,
    // ... 11 more fields
};
```

Since `CompileContext` holds only references (it's a `<'a>` struct), this is a shallow copy of all 14 reference fields. If a field is added to `CompileContext`, this site must be updated manually or the compile will fail (which is good), but the verbosity obscures the intent: "use the same context for the inner function."

**Recommendation**: Derive `Clone` on `CompileContext` (all fields are `Copy` since they're references and `Option<&_>`), or add a `CompileContext::reborrow(&self) -> CompileContext` method. Either approach reduces the 14-line construction to a single line.

---

### F-10: `collect_free_vars` in `control_flow.rs` duplicates logic from `heap.rs::collect_var_uses` (S — Suggestion)

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/crates/cranelisp-backend/src/compiler/control_flow.rs:507-585` and `/Users/alilee/Projects.nosync/rust/cranelisp/crates/cranelisp-backend/src/heap.rs:258-316`
**Checklist**: general checklist section 6

Both functions walk the expression tree recursively, handling the same set of Expr variants. `collect_var_uses` collects all variable references (for last-use analysis), while `collect_free_vars` collects unbound variable references (for capture analysis). The Expr-traversal scaffolding is ~80% identical between the two.

**Recommendation**: Extract a shared expression visitor (e.g., `walk_expr_vars(expr, callback)`) that invokes a callback at each `Expr::Var` and `Expr::Let`/`Expr::Lambda` binding site. Both `collect_var_uses` and `collect_free_vars` would be thin wrappers over this visitor with different accumulator logic. This eliminates the risk of one traversal missing a new Expr variant that the other handles.

---

### F-11: `fence()` in `emit_rc_dec` uses default memory ordering (S — Suggestion)

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/crates/cranelisp-backend/src/heap.rs:173`
**Checklist**: ring1-checklist section 2.3

The `emit_rc_dec` function emits `builder.ins().fence()` before reading object fields for drop glue. Per the ring1-checklist, this should be an Acquire fence to match `std::sync::Arc` semantics. Cranelift's `fence()` instruction emits a full memory barrier (SeqCst), which is stronger than needed.

This is correct for soundness (full barrier is a superset of Acquire), but overly conservative. When Ring 4 adds concurrency, the extra ordering may have measurable performance impact on hot RC-dec paths.

**Recommendation**: No change needed for Ring 1 correctness. Document with a comment that this is a full barrier and should be narrowed to Acquire ordering when Cranelift exposes fence ordering control (or when the performance impact is measured in Ring 4).

---

### F-12: `emit_rc_dec` does not emit the null/low-value guard (S — Suggestion)

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/crates/cranelisp-backend/src/heap.rs:142-190`
**Checklist**: ring1-checklist section 2.12

The ring1-checklist specifies: "The null/low-value guard, atomic subtract, underflow check, and old_rc == 1 branch should exist in one place." The current `emit_rc_dec` does NOT check whether the pointer is a valid heap pointer before performing the atomic subtract. If called on a nullary ADT tag (a small i64 value), the `atomic_rmw` instruction would corrupt arbitrary memory at address `tag + RC_OFFSET`.

Since RC emission is not yet wired into the expression pipeline (`#[allow(dead_code)]` scaffolding), this is not currently exploitable. However, when Ring 2 activates RC, the caller must guarantee `ptr` is a valid heap pointer, OR `emit_rc_dec` must include the guard internally.

**Recommendation**: Add a `NULLARY_TAG_THRESHOLD` guard at the top of `emit_rc_dec`: if `ptr < threshold`, skip the dec entirely. This makes `emit_rc_dec` safe to call on any i64 value (heap pointer or bare tag), which simplifies the caller's obligation and prevents a class of bugs when Mixed-category ADTs flow through RC paths.

---

## Design Doc Assessment

### `/frontend` — design/frontend/

**Files**: `CLAUDE.md`, `reader.md`, `ast-builder.md`

The frontend design docs exist and cover Ring 0 design. However, Ring 1 added string literal parsing and data constructor syntax to the AST builder, and these changes are not reflected in the design docs. The reader itself needed minimal changes (string literals were already parsed in Ring 0); the AST builder changes (constructor field definitions, shortcut syntax, TypeExpr::Applied) are documented in the code comments but not in `ast-builder.md`.

**Assessment**: **Adequate for Ring 1.** The frontend changes were incremental (no new algorithms, just new Sexp-to-Expr translation rules). A design doc update would be nice but is not blocking.

### `/typecheck` — design/typecheck/

**Files**: `CLAUDE.md`, `inference.md`, `adt.md`

**`adt.md`** is thorough and current: it documents the registration pipeline, constructor scheme generation, pattern matching inference, exhaustiveness checking, product type handling, arity validation, and per-ring evolution. It includes algorithm descriptions, rejected alternatives, and known limitations. This is the strongest design doc in the Wave 2 deliverables.

**`inference.md`** covers Ring 0 inference but does not appear to have been updated for Ring 1 changes (string type inference, polymorphic ADT constructor inference, match arm body inference with field bindings). These are documented in code comments in `infer.rs`.

**Assessment**: **Good.** `adt.md` is excellent. `inference.md` should be updated when convenient to cover the Ring 1 additions to expression inference.

### `/backend` — design/backend/

**Files**: `CLAUDE.md`, `ring1-codegen.md`

**`ring1-codegen.md`** is comprehensive and well-structured: it documents the module layout, heap layouts (HeapAdt, HeapClosure), representation containment, intrinsic registration, string codegen, ADT codegen (constructor calls, match compilation, mixed discrimination), closure codegen (lambda compilation, closure calls, named-function-as-value), batch vs. interactive mode, TCO, RC scaffolding, REPL value display, and rejected alternatives. This is the most detailed design doc in the project.

**Assessment**: **Excellent.** Current with the code, explains algorithms and trade-offs, includes rejected alternatives.

### `/platform` — design/platform/

**Files**: `CLAUDE.md`, `runtime.md`

**`runtime.md`** is thorough: it covers architectural context, base-pointer convention (with rationale and trade-off), heap layout, allocator design (allocation, deallocation, tracking, LIVE_ALLOCS, test strategy), RC infrastructure (inline vs extern decision, trace logging, underflow check), string runtime (HeapString layout, opacity principle, all 7 extern functions), type conversion primitives (including float bit pattern convention and parse_int Option ADT), module structure, JIT symbol registration table, and per-ring evolution.

**Assessment**: **Excellent.** Current, thorough, with clear rationale for design decisions.

---

## Checklist Walkthrough Summary

### Ring 1 Checklist (12 sections)

| Section | Status | Notes |
|---|---|---|
| 1. Heap Layout Adherence | PASS | Base-pointer, HeapHeader at 0, payload at 16, layout constants via offset_of!, compile-time assertions, alloc_size written correctly |
| 2. RC Correctness | PASS (scaffolding) | RC emitters exist with correct atomic_rmw pattern; not yet wired into pipeline. Findings F-2, F-12 for Ring 2 prep |
| 3. String Opacity | PASS | Backend never imports HeapString (grep confirmed). String codegen uses runtime/alloc_string. No istore8 loops. All primitives registered as extern |
| 4. ADT Codegen | PASS | Nullary = bare tags, data = heap-allocated. Mixed discrimination uses NULLARY_TAG_THRESHOLD. Tags consistent. Field offsets correct. Drop glue deferred to Ring 2 |
| 5. Closure Patterns | PASS | Layout correct. env_ptr always first. Non-capturing = minimal closure. call_indirect protocol correct. Drop via side-table (deferred). Finding F-5 on capture ordering, F-8 on construction |
| 6. JIT Symbol Names | PASS | No cranelisp_ prefix anywhere. runtime/ prefix for infrastructure. Spec kebab-case for primitives. |
| 7. Code Quality | PASS with findings | Finding F-1 (compile_apply length), F-3 (param count), F-7 (must_use). Zero unwrap/panic/expect in non-test code. |
| 8. String Newtypes | PASS | Constructor names use Symbol. Type params use Symbol. JIT names use string literals (JitSymbol not yet enforced at registration site, but naming is correct) |
| 9. Backend Specifics | PASS | Single ISA point. CompileContext carries shared state. All alloc through emit_alloc. Scope cleanup correct (push/pop). TCO + RC interaction deferred (scaffolding present) |
| 10. Runtime Crate | PASS | Allocator writes header correctly. Dealloc reads alloc_size. Panic uses extern "C-unwind". Underflow check debug-only. String edge cases tested (empty, null, unicode) |
| 11. Typecheck Specifics | PASS | Constructor registration correct with polymorphic schemes. Exhaustiveness covers mixed nullary/data. String type flows through inference |
| 12. REPL Display | Deferred | REPL display of heap values is a Wave 3 deliverable (Task 8) |

### General Checklist (10 sections)

| Section | Status | Notes |
|---|---|---|
| 1. Error Handling | PASS | Zero unwrap/expect/panic in pipeline code. Every error has Span. Warnings are data |
| 2. Code Structure | PASS with F-1 | One dispatch per Expr variant. Named structs for returns (CompileContext, MatchContext, IntrinsicIds). Finding F-1 on function length |
| 3. Naming | PASS with F-4 | String newtypes used. Named constants (NULLARY_TAG_THRESHOLD, GOT_TABLE_SIZE, MATCH_EXHAUSTION_TRAP). Finding F-4 on is_heap |
| 4. Scope Management | PASS | Push/pop pattern in both typechecker (ScopeStack) and backend (scope_stack Vec) |
| 5. Single Source of Truth | PASS | HeapCategory::classify is sole classifier (with finding F-2 caveat). Single ISA construction. Single primitive table. Single intrinsic registry |
| 6. Duplication | PASS with F-9, F-10 | Findings on CompileContext copy and expression walker duplication |
| 7. Architectural Boundaries | PASS | No circular deps. Backend depends on types+runtime, not on typecheck. String opacity maintained |
| 7a. Idiomatic Rust | PASS with F-7 | Display+Error on CranelispError. Borrow-splitting in TypeChecker. WarningKind enum. Finding F-7 on must_use |
| 8. Serialization | PASS | Serde derives on all boundary types in cranelisp-types. DefCodegen has #[serde(skip)] equivalent (raw pointers, Duration) |
| 9. Testing | PASS | Every new module has unit tests. Test names are behavioral. Backend has 23 unit tests including Ring 1 additions (string, ADT, closure) |
| 10. Performance | PASS | No O(n) scans where HashMap suffices. Constructor lookup via HashMap, not linear scan |

---

## Ring 1 Readiness Assessment

Wave 2 implementation is solid. The three Important findings (F-1, F-2, F-3) are all bounded refactoring tasks that can be addressed in Wave 3 before the Ring 1 gate:

- **F-1** (compile_apply length): ~30 min extract-method refactor
- **F-2** (HeapCategory ADT classification): Required before Ring 2 RC activation, not before Ring 1 gate
- **F-3** (compile_defn params): ~20 min refactor to accept CompileContext

The Suggestion findings (F-4 through F-12) are all quality improvements that would strengthen the codebase but do not block Ring 1 advancement.

## Re-Review (Sprint 2, Task 7c)

**Reviewer**: `/review`
**Date**: 2026-03-05
**Scope**: Confirm resolution of 3 Important findings (F-1, F-2, F-3) and 4 Suggestion findings (F-4, F-5, F-8, F-9)

### Tooling Results

- **cargo clippy --workspace**: CLEAN (zero warnings)
- **cargo test --workspace**: ALL PASS (601 tests, 0 failures, 0 ignored)

### F-1: `compile_apply` exceeded 100-line guideline — RESOLVED

**File**: `crates/cranelisp-backend/src/compiler/apply.rs:20-63`

The function has been decomposed from 145 lines into a 44-line dispatch function (`compile_apply`) plus three well-named helpers:

| Helper | Lines | Responsibility |
|---|---|---|
| `compile_resolved_call` | 67-110 | Handles `ResolvedCall` variant dispatch (builtin, trait, sig, curry) |
| `compile_var_apply` | 114-152 | Dispatches Var callees: data constructor, local closure, direct call |
| `compile_arg_list` | 155-159 | Compiles argument expressions into Cranelift values |

The decomposition is clean: `compile_apply` reads as a high-level dispatch overview, each helper handles a cohesive subset, and the `saved_tail` state is correctly threaded through. All helpers are `fn` (not `pub`), maintaining proper encapsulation. No new issues introduced.

### F-2: `HeapCategory::classify` misclassified ADTs — RESOLVED

**File**: `crates/cranelisp-types/src/heap.rs:55-104`

The function signature now accepts `type_defs: Option<&HashMap<TypeName, TypeDefInfo>>` and delegates ADT classification to a new private helper `classify_adt`. The fix is thorough:

1. **Without registry** (`None`): conservatively returns `Mixed` (safe fallback)
2. **With registry**: inspects actual constructor definitions:
   - All nullary constructors -> `NeverHeap` (bare tags)
   - All data constructors -> `AlwaysHeap` (heap-allocated)
   - Mixed nullary/data -> `Mixed`
   - No constructors -> `NeverHeap` (uninhabitable type)

The two misclassification cases from the original finding are now covered by dedicated tests:

- `test_data_only_adt_always_heap` (was incorrectly `NeverHeap` for non-parameterized ADTs with data constructors)
- `test_phantom_type_never_heap` (was incorrectly `Mixed` for parameterized ADTs with only nullary constructors)

The test suite for this module is comprehensive: 10 tests covering primitives, strings, functions, type variables, and all ADT categories (with and without registry). No new issues introduced.

### F-3: `compile_defn` had 8 parameters with clippy suppression — RESOLVED

**File**: `crates/cranelisp-backend/src/jit.rs:182-222`

`compile_defn` now takes 3 parameters (`&mut self`, `defn: &Defn`, `compile_ctx: CompileContext<'_>`) instead of the original 8. The `#[allow(clippy::too_many_arguments)]` suppression has been removed (grep confirms zero occurrences in the backend crate).

A new `build_compile_context` method (lines 228-252) provides a clean construction point for `CompileContext`, accepting the check result and environment parameters. This correctly moves the context assembly to the call site, which is the right responsibility split per the original recommendation.

### F-4: `Type::is_heap()` removed — RESOLVED

**File**: `crates/cranelisp-types/src/types.rs`

Grep confirms zero occurrences of `fn is_heap` or `is_heap()` in `types.rs`. The method has been removed entirely. `HeapCategory::classify()` remains the sole heap classification authority.

### F-5: Lambda capture ordering sorted — RESOLVED

**File**: `crates/cranelisp-backend/src/compiler/control_flow.rs:130`

Line 130 contains `captures.sort()` after the filter/collect. This satisfies the ring1-checklist section 5.8 requirement: "Captures are stored in a consistent order (e.g., sorted by variable name)." The comment on line 124 explicitly documents the sorted ordering and references the checklist.

### F-8: `FnCompiler::inner` constructor added — RESOLVED

**File**: `crates/cranelisp-backend/src/compiler/mod.rs:149-179`

A dedicated `FnCompiler::inner()` constructor now provides the single construction point for inner compilers. It takes 5 focused parameters (`builder`, `module`, `ctx`, `fn_param_count`, `last_uses`) and initializes all other fields with defaults:

- TCO disabled (`current_fn_name: None`, `tail_loop_block: None`, `in_tail_position: false`)
- Fresh scope and variable maps
- Empty RC state

The constructor is used in `compile_lambda_body` (control_flow.rs, line 236). The doc comment correctly references ring1-checklist section 5.9. No copy-pasted struct literals.

### F-9: `CompileContext` derives Clone + Copy — RESOLVED

**File**: `crates/cranelisp-backend/src/compiler/mod.rs:37`

Line 37 contains `#[derive(Clone, Copy)]` on `CompileContext`. Since all fields are references (`&'a T`), `Option<&'a T>`, `Option<FuncId>`, `Option<i64>`, or `CompileMode` (all `Copy`), this is sound. The 14-line field-by-field copy in `compile_lambda_body` has been replaced with a single `self.ctx` pass-through (line 239).

### New Issues Introduced by Refactoring

**None.** The refactoring is clean:

- No new clippy warnings
- No new `unwrap`/`panic`/`expect` in pipeline code
- No functions exceed 100 lines (longest non-test function in `apply.rs` is `compile_direct_call` at 70 lines)
- Parameter counts are within guidelines (max 6 on `compile_var_apply`, which groups naturally)
- All helpers maintain proper visibility (`fn` not `pub fn`)
- The `compile_var_apply` parameter `callee: &Expr` is passed through to `compile_expr` for closure calls -- slightly redundant since the callee is already destructured, but harmless and preserves the `compile_expr` interface uniformly

### Gate Decision

**PASS.** All 3 Important findings (F-1, F-2, F-3) are fully resolved. The 4 Suggestion findings reviewed (F-4, F-5, F-8, F-9) are also resolved. No new Blocker or Important issues were introduced by the refactoring. The codebase is cleaner than before the review, with 601 tests passing and zero clippy warnings.

---

## Next Skills

- `/qa` -- Wire up the integration test suite for Ring 1 acceptance criteria (Task 8): string eval, ADT construction/match, closure capture/call, RC trace balance verification
- `/backend` -- Address F-1 (compile_apply decomposition), F-3 (compile_defn params), F-8 (inner compiler constructor)
- `/arch` -- Address F-2 (HeapCategory::classify redesign) in cranelisp-types, as it crosses the types/backend boundary
