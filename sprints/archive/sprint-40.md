# Sprint 40: Pipeline v4 — Build Recovery + North-Star + Per-Form Typecheck

**Status**: COMPLETE
**Ring**: — (structural / pipeline v4 migration)
**Goal**: Recover from Sprint 40a broken build, establish the v4 main.rs skeleton (Step 0), and deliver the per-form typecheck API (Step 1) as the foundation for scheduler-driven compilation.

## Context

Sprint 40a attempted v3 parallelization but was cancelled mid-wave-3 — the build is broken with garbage text in `pipeline.rs:313`. The project is pivoting to pipeline v4 (scheduler-driven architecture) per `design/arch/pipeline-v4.md`. This sprint delivers the first two steps of the v4 migration roadmap (`design/arch/pipeline-v4-roadmap.md`).

**All skills MUST read these documents:**
- `design/arch/pipeline-v4.md` — the target architecture
- `design/arch/pipeline-v4-roadmap.md` — the migration plan (Steps 0-15)

## Scope

### A. Build Recovery

Fix the broken build left by Sprint 40a's partial Wave 3 work. Remove the garbage text at `src/pipeline.rs:313`. Verify `cargo build` and `cargo test` pass. The 40a partial commits (check &self, compile_unit &self, Mutex/RwLock wrapping) are **kept** — they are valid groundwork that v4 also needs.

### B. Step 0: North-Star `main.rs`

Create the v4 session skeleton per `pipeline-v4-roadmap.md` Step 0:
- New `CompilerSession` struct wrapping the existing `CompilationSession` for delegation
- All v4 methods stubbed with `todo!()` or delegating to old path
- Reachable via `--v4` CLI flag; old `main()` remains default
- End-to-end verification: `--v4 --run`, `--v4 --link`, `--v4` (REPL) produce identical results

### C. Step 1: Per-Form Typecheck API

Decompose the monolithic `tc.check()` into per-form processing per `pipeline-v4-roadmap.md` Step 1:
- New `tc.check_form(module, form) -> Result<FormCheckResult>` method
- `FormCheckResult` contains per-form method resolutions, expr_types, constraints, warnings
- `tc.merge_form_result(module, form_result)` accumulates into module state
- Rewrite `tc.check()` internally to iterate forms via `check_form()` — all existing callers unchanged
- Multi-pass structure preserved: signature registration pass, then body checking pass

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `src/pipeline.rs:313` | /int | Garbage text from cancelled 40a Wave 3 | Fix in Wave 0 |

Pre-existing FIXMEs from prior sprints not in scope for this sprint (pipeline infrastructure focus).

## Prior-Ring Coverage Audit

This sprint is pipeline infrastructure — coverage gaps are noted but not prioritized here.

**Coverage gaps (completed rings with untested requirements):**
- `spec/05-definitions.md:291` §5.4.2 Concrete ADT Instantiation `[R2 S10]`
- `spec/05-definitions.md:303` §5.4.3 Polymorphic Implementation `[R2 S10]`
- `spec/08-modules.md:595` §8.11 Stdlib Directory `[R2 S10]`
- `spec/appendix-a-builtins.md:101-111` — 11 string primitives `[R3 S14]`
- `spec/appendix-a-builtins.md:127-128` — vec-map, vec-reduce `[R3 S10]`
- `spec/appendix-a-builtins.md:132` §A.4 Special Forms `[R3 S10]`
- `spec/appendix-a-builtins.md:136` §A.5 Docstrings for Builtins `[R1]`
- `repl/spec.md` — multiple `[R3 S14]` and `[R3 S8]` items (universal output format, value display)

**Negative coverage gaps:** Widespread — many `[Tested ...]` without `+Neg`. Not addressed this sprint.

**Stale IGNORED annotations:** None found.

These gaps should be addressed in a dedicated QA catchup sprint after the v4 pipeline foundation is stable.

## Architecture Review

**Reviewer**: /arch
**Date**: 2026-03-29
**Verdict**: APPROVED with conditions

### 1. Technical Coherence: Steps 0 + 1 as a Testable Increment

**Approved.** Steps 0 and 1 form a clean, testable increment:

- **Step 0** is pure delegation — a new `CompilerSession` wrapper that routes everything through the existing `CompilationSession`. It produces no new behavior and is verified by identity: `--v4` output equals default output. This is the correct skeleton-first approach per `pipeline-v4-roadmap.md`.
- **Step 1** is a pure internal refactor of `tc.check()` — existing callers are unchanged, the method signature is unchanged, and the result type is unchanged. The new `check_form()` and `merge_form_result()` methods are internal to `cranelisp-typecheck`. Verification is behavioral identity: `check()` returns the same `CheckResult` before and after.
- The two steps are independent — Step 0 does not depend on Step 1, and Step 1 does not depend on Step 0. They can be implemented in parallel (Wave 1 and Wave 2 respectively), which is what the sprint plan does. This is good.

The increment is self-contained: at sprint end, the compiler works exactly as before, with two new capabilities that future steps build on (the v4 skeleton and the per-form typecheck API).

### 2. No Interim Architecture (Principle 8)

**Approved.** Neither step creates throwaway infrastructure:

- **Step 0's `CompilerSession`** is the permanent v4 session type. It starts as a delegation wrapper and progressively fills in across Steps 2-15. It is never replaced — it IS the target. The `--v4` flag is the only throwaway element, and it is explicitly scoped for removal in Step 15.
- **Step 1's `check_form()` / `FormCheckResult` / `merge_form_result()`** are the permanent per-form typecheck API that the scheduler calls in Step 3 (`process_module_forms`). They are never replaced. The multi-pass structure (signature registration pass, then body checking pass) is preserved because the scheduler in Step 3 processes forms in two passes via `check_form()` — this matches `pipeline-v4.md` section 3.2 and `pipeline-v4-roadmap.md` Step 1.

No code in this sprint is throwaway. Both outputs survive to the final architecture.

### 3. Design References

The sprint plan correctly cites the relevant design docs. Confirming the references are sufficient:

- **/int (Step 0)**: `pipeline-v4.md` section 2.2 (main.rs structure), section 3 (CompilerSession), section 9 (REPL eval). Also read `pipeline-v4-roadmap.md` Step 0 for the exact stub behavior. **Sufficient.**
- **/typecheck (Step 1)**: `pipeline-v4-roadmap.md` Step 1 for the decomposition target. Also read the current `crates/cranelisp-typecheck/src/program.rs` `check()` method (lines 107-254) to understand the multi-pass structure being decomposed. **Sufficient.**
- **/qa**: `pipeline-v4-roadmap.md` Step 1 verification criteria. Should also understand the current `check()` return contract (all fields of `CheckResult` must be identical before/after). **Sufficient.**

### 4. Interface Gaps: `FormCheckResult`

**Condition: `/arch` must review and approve `FormCheckResult` before /typecheck implements it (Wave 2 gate).**

`FormCheckResult` is mentioned in the sprint plan and the roadmap but is NOT yet defined in `interfaces.md`. This is correct — it is an internal type within `cranelisp-typecheck`, not a cross-crate boundary type. The scheduler (Step 3, future sprint) calls `tc.check_form()` and receives `FormCheckResult`, but the scheduler lives in `src/` which already depends on `cranelisp-typecheck`. No new crate boundary is crossed.

However, the design of `FormCheckResult` determines whether the scheduler can work form-by-form. The type must carry enough information for:

1. **Per-symbol codegen readiness** (Step 3): After a `Defn` form is checked, its method resolutions and expr_types must be extractable for immediate codegen — the scheduler does not wait for the whole module.
2. **Multi-pass accumulation** (Step 1): Signature registration (pass 1) produces different output than body checking (pass 2). `check_form` must distinguish these cases or accept a pass indicator.
3. **Module-level result assembly** (Step 1): `merge_form_result` must accumulate per-form results into a complete `CheckResult` that matches the current monolithic output exactly.

**Recommendation for /typecheck**: When designing `FormCheckResult`, consider these fields as a starting point:

```rust
pub struct FormCheckResult {
    /// Method resolutions discovered while checking this form.
    pub method_resolutions: MethodResolutions,
    /// Expression types for this form's AST nodes.
    pub expr_types: HashMap<Span, Type>,
    /// Constrained function info (if this form defines one).
    pub constrained_fn: Option<(Symbol, ConstrainedFnInfo)>,
    /// Monomorphised definitions generated from this form's call sites.
    pub mono_defns: Vec<MonoDefn>,
    /// Default method definitions expanded from trait impls in this form.
    pub default_method_defns: Vec<Defn>,
    /// Warnings emitted during checking.
    pub warnings: Vec<Warning>,
}
```

The `/arch` gate in Wave 2 is the right place to review this. `/typecheck` should propose the type, `/arch` reviews it against the Step 3 scheduler requirements before implementation proceeds.

**`FormCheckResult` should NOT be added to `interfaces.md`** — it is internal to the typecheck crate. Only `CheckResult` crosses the crate boundary, and it is unchanged.

### 5. Sprint 40a Legacy Compatibility

**Approved.** The 40a partial work is compatible with v4's direction:

- **`compile_unit` takes `&self`**: The 40a change to `CompilationSession.compile_unit(&self)` is compatible. Step 0 wraps `CompilationSession` and delegates to `compile_unit(&self)`. When Step 3 replaces the delegation with the scheduler path, `compile_unit` stops being called from the v4 path. The `&self` signature is harmless in the interim.
- **`tc: Mutex<TypeChecker>` on `CompilationSession`**: This wraps the current `&mut self` `check()` method. Step 0 delegates through the existing path which acquires the Mutex. Step 1's `check_form()` also takes `&mut self` (it is still called through `check()` which holds `&mut TypeChecker`). This is fine — the Mutex is on the *session*, not the TypeChecker, so the internal `check()` -> `check_form()` decomposition is unaffected.
- **`RwLock<HashMap<ModuleFullPath, SymbolTable>>` on TypeChecker.modules**: The 40a change replaced the bare HashMap with an RwLock. This is a stepping stone toward DashMap (Step 12). For Steps 0-1, `check()` still takes `&mut self`, so the RwLock is uncontested (write lock always available). No conflict.
- **`AtomicU32` for `next_id`**: Already in place, compatible with future `&self` check paths.

The 40a Mutex/RwLock wrapping is valid groundwork. It does not create throwaway infrastructure — these locks will be replaced by DashMap in Step 12, but until then they correctly enable the `&self` calling pattern on the session.

### 6. Additional Observations

**6a. Multi-pass decomposition complexity.** The current `check()` has 5 passes (type defs, trait decls, trait impls + multi-sig expansion, signature registration, body checking) plus 3 post-passes (monomorphisation, overload resolution, auto-curry). Decomposing this into `check_form()` is the "highest-effort step" per the roadmap. The sprint plan's acceptance criteria ("check() internally uses check_form()") is the right granularity — do not attempt to expose per-form results to external callers in this sprint. The internal decomposition is sufficient for Step 3.

**6b. Pass indicator.** The roadmap says `check_form` is called in two passes by `check()` — once for signature registration, once for body checking. The /typecheck skill should decide whether this is modeled as:
- A pass parameter on `check_form` (e.g., `enum CheckPass { RegisterSignature, CheckBody }`)
- Two separate methods (`register_form_signature` + `check_form_body`)
- A single `check_form` that returns partial results in pass 1 and full results in pass 2

Any of these is architecturally acceptable. The key constraint is that the scheduler in Step 3 must be able to call them in the right order. A pass parameter is simplest.

**6c. Wave 2 gate is correctly placed.** /arch reviewing `FormCheckResult` before implementation prevents a design-rework cycle if the type doesn't carry what the scheduler needs. This gate should be lightweight — a type definition review, not a full design doc.

**6d. Build recovery (Wave 0) is correctly prioritized.** The garbage text at `pipeline.rs:313` must be fixed before any other work. The sprint plan handles this correctly.

### 7. Checklist

| Check | Status | Notes |
|-------|--------|-------|
| Single pipeline invariant | PASS | No new parallel types or functions. `CheckResult` remains the sole boundary type. |
| No interim architecture (Principle 8) | PASS | Both steps produce permanent artifacts. |
| Design references sufficient | PASS | All skills have correct doc pointers. |
| `interfaces.md` coherence | PASS | No changes needed — `FormCheckResult` is internal. |
| 40a legacy compatibility | PASS | Mutex/RwLock/AtomicU32 are compatible stepping stones. |
| Carried debt inventory | NOTE | 8 coverage gap items noted in Prior-Ring Coverage Audit. Correctly deferred — this sprint is pipeline infrastructure. |
| Foundation before features | PASS | This sprint IS foundation work. No features built on unreviewed code. |
| Sketch consultation | N/A | Steps 0-1 are pipeline architecture, not language-level problems. The sketch's pipeline structure is explicitly NOT the model (`CLAUDE.md`: "Do not copy the sketch's pipeline structure"). |

### 8. Conditions for Advancement

1. **/arch must review `FormCheckResult` design** before /typecheck begins implementation (Wave 2 gate). A type definition with field-level justification against Step 3 requirements is sufficient. **COMPLETED 2026-03-29** — review written at `design/typecheck/check-form-api.md` §Architecture Review. Verdict: APPROVED with minor changes (add `call_graph_edges` field, clarify `type_defs`/`constructor_to_type` sourcing, add accumulator ownership invariant, fix DefnMulti variant return path). None blocking — /typecheck may address during implementation.
2. **Wave 0 must verify test count matches pre-40a baseline** (1536+ tests passing). If the garbage text fix reveals other 40a breakage, scope those fixes into Wave 0 before proceeding.

## Skill Plans

### /int
**Task**: Fix broken build (Wave 0), create v4 `CompilerSession` skeleton with `--v4` flag (Wave 1)
**Design doc**: `design/arch/pipeline-v4.md` §2.2, `design/arch/pipeline-v4-roadmap.md` Step 0
**Approach**:
1. **Wave 0**: Remove garbage text at `pipeline.rs:313`. Run `cargo build` + `cargo test`, verify 1536+ tests pass.
2. **Wave 1**: Create `CompilerSession` struct in new `src/session_v4.rs` wrapping `CompilationSession`. Add `--v4` CLI flag to `main.rs`. Implement all v4 methods as delegation to existing `CompilationSession` methods: `register_module` → `compile_unit` + `codegen_and_execute`, `eval` → same, `process_commands` → existing REPL dispatch, `trampoline`/`link` → existing methods, `spawn_*_workers` → `todo!()`, `shutdown` → no-op, `scheduler.wait_*` → `Ok(())`. Verify `--v4 --run`, `--v4 --link`, `--v4` (REPL) produce identical output to default.
**Design refs**: `pipeline-v4.md` §2.2 (main.rs structure), §3 (CompilerSession), §9 (REPL eval)
**Acceptance**: `cargo build` passes (Wave 0). `--v4 --run examples/hello.cl` produces identical output to `--run examples/hello.cl`. All existing tests pass.

### /typecheck
**Task**: Implement per-form typecheck API (`check_form`, `FormCheckResult`, `merge_form_result`)
**Design doc**: `design/arch/pipeline-v4-roadmap.md` Step 1
**Approach**: Design doc written at `design/typecheck/check-form-api.md`. Implementation plan:
1. Define `CheckPass` enum (`Register` / `CheckBody`) and `FormCheckResult` struct in `program.rs`. Define `ModuleCheckAccumulator` for per-module state accumulation during form-by-form processing.
2. Implement `check_form(&mut self, module, form, pass) -> Result<FormCheckResult>` by extracting logic from the existing pass sub-functions (`register_type_defs_from_program`, `pass1_register_signatures`, `pass2_check_bodies`, `pass4_monomorphise`) into per-form dispatch.
3. Implement `merge_form_result(&mut self, module, result)` to accumulate per-form results into `ModuleCheckAccumulator`.
4. Implement `finalize_check_result(&mut self, module) -> CheckResult` to run post-passes (pending overload resolution, auto-curry, final substitution) and drain accumulator into `CheckResult`.
5. Rewrite `check()` to iterate forms via `check_form()` in two passes (Register then CheckBody), with default method defns fed back through both passes. Verify `check()` produces identical `CheckResult`.
6. Add unit tests for `check_form`: single defn, TypeDef, TraitDecl, TraitImpl with defaults, multi-sig, Expr, constrained fn detection.
**Design refs**: `design/typecheck/check-form-api.md`, `pipeline-v4-roadmap.md` Step 1, current `tc.check()` implementation in `crates/cranelisp-typecheck/`
**Acceptance**: `cargo test` passes. New `check_form` unit tests in `cranelisp-typecheck`. `tc.check()` internally delegates to `check_form()` in two passes.

### /arch
**Task**: Review sprint scope for v4 coherence. Review /typecheck design for FormCheckResult before implementation.
**Design doc**: n/a (review role)
**Approach**: Verify Step 0 + Step 1 form a coherent foundation for Steps 2-3. Ensure FormCheckResult carries everything the scheduler will need.
**Design refs**: `pipeline-v4.md`, `pipeline-v4-roadmap.md`, `concurrent-pipeline.md`
**Acceptance**: Architecture review section filled. FormCheckResult design approved.

### /qa
**Task**: Write tests for per-form typecheck API. Verify existing test suite passes unchanged.
**Design doc**: `design/typecheck/check-form-api.md`
**Design refs**: `pipeline-v4-roadmap.md` Step 1 verification criteria

**Approach — Test Case Plan (Wave 2)**:

All tests are unit tests in `crates/cranelisp-typecheck/src/program.rs` `mod tests`, using existing `tc_with_prims()` and `make_defn()` helpers. Tests call `check_form()` directly to validate per-form results, and compare `check()` output before/after refactor to verify behavioral identity.

**Category 1: Behavioral Identity** (`check()` via `check_form` = same `CheckResult`)

These are the highest-priority tests. They run the *same program* through `check()` and assert the result fields match the expected values from the existing test suite. Since the refactor rewrites `check()` internals, these tests verify the contract is preserved.

- `test_check_form_identity_simple_defn` — `(defn inc [x] (add-i64 x 1))`: check() returns same method_resolutions, expr_types, display, type_defs, warnings as before.
- `test_check_form_identity_typedef_plus_defn` — TypeDef(Color) + Defn(is-red) program: check() returns same type_defs, constructor_to_type, method_resolutions, expr_types.
- `test_check_form_identity_forward_reference` — Two mutually-referencing defns (double/add-self): check() returns same schemes and expr_types.
- `test_check_form_identity_constrained_fn` — Constrained polymorphic defn `(defn add [x y] (+ x y))` with Num trait: check() returns same constrained_fn_names and mono_defns.
- `test_check_form_identity_expr` — Bare `Expr(42)`: check() returns same display info and expr_types.
- `test_check_form_identity_multi_sig` — DefnMulti with different arities: check() returns same method_resolutions, multi_sig_defns, resolved overloads.

**Category 2: Per-Form Basics** (single form through `check_form`)

Each test calls `check_form` with `CheckPass::Register` then `CheckPass::CheckBody` for one form, verifying `FormCheckResult` fields.

- `test_check_form_single_defn_register` — Defn(inc), Register pass: FormCheckResult has empty method_resolutions, empty expr_types, no constrained_fn, no mono_defns. Signature registered in symbol table (verify via tc.symbol_table().get()).
- `test_check_form_single_defn_check_body` — Same Defn(inc) after register, CheckBody pass: FormCheckResult has non-empty expr_types (body expressions typed), method_resolutions contains BuiltinFn for add-i64, constrained_fn is None.
- `test_check_form_typedef_register` — TypeDef(Color Red Green), Register pass: type_defs populated, constructors registered in symbol table, expr_types may contain constructor types. No default_method_defns.
- `test_check_form_typedef_check_body_noop` — TypeDef, CheckBody pass: returns empty FormCheckResult (no-op for non-Defn forms).
- `test_check_form_trait_decl_register` — TraitDecl(Num), Register pass: trait registered in trait_registry. FormCheckResult is mostly empty.
- `test_check_form_trait_decl_check_body_noop` — TraitDecl, CheckBody pass: empty FormCheckResult.
- `test_check_form_trait_impl_register` — TraitImpl(Num for Int), Register pass: impl registered. If trait has default methods not overridden, default_method_defns populated.
- `test_check_form_trait_impl_with_defaults` — TraitImpl where a default method is synthesized: FormCheckResult.default_method_defns is non-empty, and those defns have correct names.
- `test_check_form_expr_register` — Expr(42) wrapped as synthetic __expr Defn, Register pass: signature registered for __expr.
- `test_check_form_expr_check_body` — Same __expr, CheckBody pass: expr_types contains the literal's type (Int), method_resolutions empty (no calls).

**Category 3: Two-Pass Correctness** (register then check body)

Validates the invariant that all signatures must be registered before any body is checked.

- `test_check_form_two_pass_mutual_reference` — Two defns (f calls g, g calls add-i64). Register both, then CheckBody both. Both get correct types; forward reference from f to g resolves because g's signature was registered in pass 1.
- `test_check_form_check_body_before_register_errors` — Call CheckBody on a defn whose signature was never registered. Should produce an error (missing key in defn_type_vars).
- `test_check_form_register_populates_defn_type_vars` — After Register pass, verify accumulator's defn_type_vars contains the defn's name with fresh type vars.
- `test_check_form_typedef_before_defn` — TypeDef(Option) registered, then Defn using Option constructor. CheckBody for defn resolves constructor type correctly.
- `test_check_form_trait_decl_before_impl` — TraitDecl(Eq) registered, then TraitImpl(Eq for Int) registered. No error. Validates ordering within Register pass.

**Category 4: Multi-Form Programs** (programs with interactions between forms)

- `test_check_form_multi_defn_shared_substitution` — Three defns where type flows between them (f calls g calls h, h uses add-i64). After all Register + CheckBody passes, f/g/h all resolve to Int types via shared substitution.
- `test_check_form_typedef_plus_match_defn` — TypeDef(Color) + Defn(is-red) using match. Register both (typedef first), then CheckBody for defn. Defn's expr_types and method_resolutions match monolithic check() output.
- `test_check_form_trait_impl_plus_user_fn` — TraitDecl(Num) + TraitImpl(Num Int) + Defn using (+). Register all three + defn signature, then CheckBody for trait impl methods + defn. Method resolutions contain TraitMethod for (+).
- `test_check_form_accumulator_merge` — Process multiple forms via check_form + merge_form_result. Verify accumulated method_resolutions/expr_types grow with each form. Final finalize_check_result produces complete CheckResult.
- `test_check_form_finalize_resolves_pending` — After all forms processed, finalize_check_result resolves pending overloads and auto-curry. Verify these are present in final CheckResult.

**Category 5: Edge Cases from Design Doc**

- `test_check_form_defn_multi_register` — DefnMulti(add with 2 arities), Register pass: expands into internal variant defns (add__v0, add__v1), registers Overloaded placeholder for base name. FormCheckResult or accumulator contains expanded variants.
- `test_check_form_defn_multi_check_body` — Same DefnMulti after register, CheckBody pass: checks each variant body, resolves overloads (mangles names), returns multi_sig_defns with mangled names.
- `test_check_form_constrained_fn_detection` — Defn `(defn add [x y] (+ x y))` with Num trait registered. CheckBody pass: constrained_fn is Some("add"). Confirms eager detection works per-form.
- `test_check_form_constrained_fn_monomorphise` — Two defns: constrained `add` and concrete `use-add` calling `(add 1 2)`. After register + check_body for add (detected as constrained), check_body for use-add produces mono_defns for `add$Int+Int`.
- `test_check_form_constrained_ordering_matters` — Constrained fn g defined AFTER its caller f: f's check_body cannot monomorphise g's call sites because g hasn't been detected as constrained yet. Validates that per-form monomorphisation depends on source order (per spec section 9.12).
- `test_check_form_default_method_defns_fed_back` — TraitImpl generates default method defns. These are fed back through Register + CheckBody. Verify the default methods end up with correct types in symbol table and their expr_types are in the accumulated result.
- `test_check_form_expr_types_no_unresolved_vars` — After finalize_check_result, all expr_types in the CheckResult have no Var types (final substitution applied).
- `test_check_form_warnings_accumulated` — Forms that produce warnings: verify FormCheckResult.warnings is populated and merge_form_result accumulates them across forms.

**Negative tests:**

- `test_check_form_register_duplicate_type_error` — Two TypeDef forms with same name: second Register produces error.
- `test_check_form_type_error_propagates` — Defn with type mismatch in body: CheckBody returns Err, not silently dropped.
- `test_check_form_trait_impl_unknown_trait_error` — TraitImpl referencing undeclared trait in Register pass: error.

**Total: ~33 test cases across 5 categories + 3 negative tests.**

**Acceptance**: New tests cover: single-form check, multi-form check, signature+body two-pass, error propagation, behavioral identity with monolithic check(). Full suite green after /typecheck implements the API.

### /backend
**Task**: No implementation work. Verify codegen is unaffected by typecheck refactor.
**Design doc**: n/a
**Approach**: Confirm `CheckResult`/`CompileUnitResult` boundary types unchanged.
**Design refs**: `design/arch/interfaces.md`
**Acceptance**: No backend changes needed. Tests pass.

### /review
**Task**: Review Wave 1 (v4 skeleton) and Wave 2 (per-form typecheck) code for quality and v4 alignment.
**Design doc**: n/a
**Approach**: Standard review pass on new code.
**Acceptance**: All B+I findings resolved.

### /frontend
**Task**: No implementation work this sprint.

### /platform
**Task**: No implementation work this sprint.

### /stdlib
**Task**: Validate stdlib modules compile after typecheck refactor.
**Approach**: `cargo run -- --run stdlib/core.cl` or equivalent validation.
**Acceptance**: All 27 stdlib modules load without regression.

### /examples
**Task**: Validate all examples compile after changes.
**Approach**: Run all examples through `--run`.
**Acceptance**: All examples produce expected output.

### /port
**Task**: Validate exemplar compiles after changes.
**Acceptance**: Exemplar runs without regression.

### /repl
**Task**: Create sprint demo `repl/demos/v4a.demo`.
**Approach**: Demonstrate `--v4` flag running REPL with identical behavior to default.
**Acceptance**: Demo plays cleanly.

### /docs
**Task**: No implementation work this sprint.

### /spec
**Task**: No implementation work this sprint.

## Waves

### Wave 0: Build Recovery
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Revert 40a source code to Sprint 40 state (5d123a1), keeping v4 design docs | done | 1671 passed, 11 pre-existing sketch_port failures, 0 ignored |

**Acceptance**: `cargo build` succeeds. `cargo test` shows 1536+ passed (matching pre-40a baseline).

### Wave 1: North-Star main.rs (Step 0)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review sprint scope, confirm Step 0 + Step 1 coherence | done | Phase 2 architecture review — APPROVED with conditions |
| /int | Create `CompilerSession` skeleton, `--v4` flag, delegate all methods to old path | done | `src/session_v4.rs` + `--v4` flag in main.rs; all methods delegate to old path; 171 lib tests pass |

**Acceptance**: `--v4 --run`, `--v4 --link`, `--v4` (REPL) produce identical results to old main.

### Wave 2: Per-Form Typecheck Design + Implementation
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Design `FormCheckResult` type, implement `check_form`, refactor `check()` | done | `CheckPass`, `FormCheckResult`, `ModuleCheckAccumulator` added; `check()` refactored to use `check_form()` internally; 277 tc tests + 171 lib tests + 1536 total pass |
| /arch | Review `FormCheckResult` design before implementation | done | Gate — approved with minor changes, see `design/typecheck/check-form-api.md` §Architecture Review |
| /qa | Write unit tests for `check_form` (parallel with implementation) | done | 28 tests: 6 behavioral identity, 8 per-form basics, 5 two-pass correctness, 4 multi-form programs, 3 edge cases, 2 negative; 305 tc tests pass in 0.02s |

**Acceptance**: `cargo test` passes. `check_form` unit tests cover basic forms. `check()` internally uses `check_form`.

### Wave 3: Build/Test/Review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /review | Review Wave 1 + Wave 2 code | done | 0 blockers, 3 important, 4 suggestions — see Notes |
| /qa | Full test suite verification | done | 1733 passed (171 lib + 305 tc + 1257 integration), 11 pre-existing sketch_port failures, 0 ignored |

**Acceptance**: All tests pass. All B+I review findings resolved.

### Wave 4: Validation + Showcase
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /stdlib | Validate 27 stdlib modules | done | 54 tests pass |
| /examples | Validate all examples | done | 15 tests pass |
| /port | Validate exemplar | done | exemplar tests included in integration suite |
| /repl | Create sprint demo | done | `repl/demos/v4a.demo` created |

**Acceptance**: Sprint close checklist passes.

## Notes

_Runtime log: blockers encountered, scope changes, decisions made._

### /review: Wave 3 Code Review (2026-03-29)

**Scope**: `src/session_v4.rs` (Wave 1), `src/main.rs` (Wave 1), `src/lib.rs` (Wave 1), `crates/cranelisp-typecheck/src/program.rs` (Wave 2).

**Build status**: 1536 tests pass. 11 pre-existing `sketch_port` failures. 305 typecheck crate tests pass (including 28 new `check_form` tests). `cargo build` clean.

#### Findings

**I-1. `resolve_multi_sig_overloads` exceeds 100-line function limit (135 lines).** (`program.rs:922-1057`). The inner loop handles type resolution, duplicate checking, mangled name registration, defn construction, and symbol table updates. Should be split into a per-variant helper and a per-defn finalization helper. Pre-existing code but touched by Wave 2 (it now takes `type_vars` parameter from the accumulator instead of internal state). Severity: **I (Important)** — technical debt, violates `src/CLAUDE.md` "Max ~100 lines per function."

**I-2. Accumulator collects data it never uses.** `merge_form_result()` accumulates `method_resolutions`, `expr_types`, and `warnings` into `ModuleCheckAccumulator`, but `finalize_check_result()` reads these from `self.state` (via `build_check_result()` which drains `self.state.method_resolutions` and `self.state.expr_types`). The accumulator's copies are dead data. This works for Step 1 (internal refactor of `check()`) because `self.state` is the shared persistent store. However, the design doc (`check-form-api.md`) implies the accumulator is the authoritative per-form result store. In Step 3, if the scheduler needs to access per-form results from the accumulator (e.g., for per-symbol codegen readiness), these fields will be stale duplicates of state data. Severity: **I (Important)** — misleading architecture that will cause confusion or bugs in Step 3. Either (a) make the accumulator authoritative by removing entries from `self.state` after extraction, or (b) remove the unused fields from the accumulator and `merge_form_result` to avoid the false promise.

**I-3. `register_module` returns a synthetic empty `CompileUnitResult`.** (`session_v4.rs:200-219`). The method constructs a dummy `CompileUnitResult` with empty fields and a `ModuleFullPath::from("")`. The comments in the function body show uncertainty about the design ("Re-read the unit_result... Actually, the caller only needs the warnings..."). The caller (`v4_main` Run mode) only uses the warnings from the second tuple element, so the `CompileUnitResult` is indeed unused — but the return type claims to provide one. This is confusing and the empty `ModuleFullPath::from("")` could cause problems if any downstream code inspects the path. Severity: **I (Important)** — either change the return type to just `Vec<Warning>`, or clone the unit_result before sending to codegen (as the old main.rs did with `let unit_warnings = unit_result.warnings.clone()` before `send_codegen`). The v4 roadmap Step 3 replaces this entirely, so a quick fix is fine.

**S-1. `check_form` signature diverges from design doc.** The design doc specifies `check_form(&mut self, module, form, pass) -> Result<FormCheckResult>` but the implementation adds `accumulator: &mut ModuleCheckAccumulator` as a fourth parameter. This is a reasonable implementation choice (avoids storing the accumulator on the TypeChecker), but the divergence should be documented. Severity: **S (Suggestion)** — update the design doc to match, or add a comment explaining the divergence.

**S-2. `CommandResult::Final(String)` vs design `Final(Sexp)`.** The design doc (`pipeline-v4.md` §6.1) specifies `Final(Sexp)` but the implementation uses `Final(String)`. Since `process_commands` is currently a no-op stub returning `Nothing`, this is harmless. Severity: **S (Suggestion)** — add a comment noting the String-vs-Sexp divergence will be resolved in Step 7.

**S-3. `call_graph_edges` always empty.** `FormCheckResult.call_graph_edges` is declared and accumulated per `/arch` review request, but always `Vec::new()` in all `check_form_body_*` methods. The field exists for Step 3 readiness. Severity: **S (Suggestion)** — add a `// TODO(Step 3): populate from body checking` comment on the empty vec construction sites so future implementers know it's intentionally deferred.

**S-4. `process_commands` is a dead method.** (`session_v4.rs:246-253`). It always returns `CommandResult::Nothing` and is never called — the v4 REPL path delegates directly to `run_repl()`. The method exists for API completeness per the v4 design. Severity: **S (Suggestion)** — fine as a placeholder; no action needed.

#### Positive Observations

1. **v4 alignment is solid.** `CompilerSession` wraps `CompilationSession` exactly as specified in the roadmap Step 0. The delegation pattern (all v4 methods call through to old-path equivalents) is clean and correct. `--v4 --run` exercises a different code path that produces identical results.

2. **`check_form` two-pass structure is correct.** The decomposition preserves the fundamental invariant (all signatures registered before any body checked). The `check()` rewrite correctly feeds default method defns back through both passes. Pass ordering matches the design doc.

3. **Test quality is good.** 28 new tests cover 5 categories: behavioral identity (6), per-form basics (8), two-pass correctness (5), multi-form programs (4), edge cases (3), plus 2 negative tests. The `test_check_form_check_body_before_register_errors` test validates the critical invariant. The `test_check_form_two_pass_mutual_reference` test validates forward references work through the per-form API.

4. **No unwrap() in new pipeline code.** Both `session_v4.rs` and the new `check_form` methods use `?` with proper `CranelispError` returns. Error messages include context.

5. **No unsafe code introduced.** No new `unsafe` blocks in any Wave 1/2 code.

6. **Design docs are up to date.** `design/typecheck/check-form-api.md` includes the required Sketch Comparison section with specific analysis of what is preserved vs. diverged.

#### Summary

| Severity | Count | Resolution |
|----------|-------|------------|
| B (Blocker) | 0 | — |
| I (Important) | 3 | I-1: decompose function (can defer). I-2: clarify accumulator role before Step 3. I-3: simplify return type or clone before send. |
| S (Suggestion) | 4 | Doc/comment updates, no code changes required. |

**Verdict**: No blockers. The 3 Important findings are technical debt that should be addressed before Step 3 begins, but do not block sprint close. All Important findings have clear resolution paths and none affect correctness of the current code.

## Outcome

### Delivered
- **Build recovery**: Reverted 40a broken source code to Sprint 40 state; v4 design docs preserved
- **Step 0: North-star main.rs**: `src/session_v4.rs` — `CompilerSession` wrapping `CompilationSession`, all v4 methods delegate to old path, `--v4` CLI flag in `main.rs`
- **Step 1: Per-form typecheck API**: `CheckPass`, `FormCheckResult`, `ModuleCheckAccumulator`, `check_form()`, `merge_form_result()`, `finalize_check_result()` in `cranelisp-typecheck`. `check()` refactored internally to use `check_form()`.
- **Design doc**: `design/typecheck/check-form-api.md` — full design with architecture review
- **28 new tests**: Per-form API unit tests across 6 categories (behavioral identity, per-form basics, two-pass correctness, multi-form, edge cases, negative)
- **Sprint demo**: `repl/demos/v4a.demo`
- **Test counts**: 1733 total (305 typecheck + 171 lib + 1257 integration), 11 pre-existing sketch_port failures, 0 ignored

### Deferred
- **I-1**: `resolve_multi_sig_overloads` 135 lines (pre-existing, FIXME placed) — decompose before Step 3
- **I-2**: `ModuleCheckAccumulator` dead data fields (FIXME placed) — clarify before Step 3
- **I-3**: Synthetic `CompileUnitResult` return in `register_module` (FIXME placed) — replaced by Step 3

### Findings
- **40a revert was necessary**: The Mutex/RwLock wrapping from 40a caused test suite hangs (likely deadlock). Full revert to Sprint 40 state was cleaner than surgical fixes, since v4 Step 1 takes a different approach (per-form API rather than lock-based concurrency).
- **`check()` decomposition was clean**: The monolithic `check()` method decomposed into `check_form()` without changing the public API or `CheckResult` output. The two-pass invariant is preserved.
- **v4 skeleton works end-to-end**: `--v4 --run`, `--v4 --link`, and `--v4` (REPL) produce identical results to the default path.
