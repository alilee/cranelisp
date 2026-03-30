# Sprint 44: Pipeline v4 Step 7 — REPL Eval via Scheduler

**Status**: COMPLETE
**Ring**: — (structural / pipeline v4 migration)
**Goal**: REPL eval routes definitions through the v4 scheduler and compiles trailing expressions as temporary closures. The old `compile_unit` delegation in `session_v4.rs::eval()` is replaced.

## Context

Sprint 43 delivered Steps 5+6: lazy dependency discovery and MacroExpander removal. The v4 scheduler path (`--v4 --run`) handles all batch programs. The REPL is the last caller of the old `compile_unit` path.

This sprint delivers **Step 7** from `design/arch/pipeline-v4-roadmap.md`: REPL eval via the scheduler. The v4 roadmap identifies this as the **highest-risk step** because the REPL has accumulated interception points (defmacro, import, platform, trace, annotation, bare symbol introspection) that currently flow through `compile_unit`.

**Key simplification**: The v4 worker's `process_module_forms` already handles defmacro, import, platform, export, and mod forms via `classify_form` (delivered Sprint 43). REPL eval with `ModuleStrategy::Additive` should reuse the same worker path — the difference is that REPL input is appended to the current module, not replacing it.

**All skills MUST read:**
- `design/arch/pipeline-v4-roadmap.md` — Step 7 specification
- `design/arch/pipeline-v4.md` — target architecture, §6 REPL eval
- `src/session_v4.rs` — current `eval()` delegation and `process_commands()` stub
- `src/repl/mod.rs` — current REPL main loop, slash command dispatch, interceptions
- `src/repl/commands.rs` — slash command handlers
- `src/worker.rs` — `process_module_forms` (the v4 worker path that REPL eval should use)

## Scope

### A. REPL Eval via Scheduler

Replace `session_v4.rs::eval()` to process top-level forms serially:

1. Parse input into sexps.
2. For each sexp:
   a. If single bare symbol → introspect, display result.
   b. Otherwise → TC snapshot, send to `process_module_forms(Additive)` as a single form, codegen, execute, display result. On error: TC restore, display error, continue to next form.
3. After all forms: if definitions were made, regenerate REPL module source (session persistence).

Serial per-form processing is simpler and more correct than batching:
- Each form gets immediate feedback (definition acknowledged, expression result displayed).
- No need to separate definitions from trailing expressions — every form is processed the same way.
- Multiple expressions just work: `(+ 1 2)` displays, then `(+ 3 4)` displays.
- Error in one form doesn't prevent processing the next.
- Matches how a user thinks about REPL interaction — one thing at a time.

The persistent eval JIT (retained across evals) is an optimisation. Start with a fresh JIT per eval — the existing `Jit::new()` pattern works. Persistent JIT can come later if startup overhead is measurable.

### B. Additive Strategy for process_module_forms

`process_module_forms` currently processes a module from scratch. For REPL eval, it needs additive input: new forms appended to an existing module.

The arch review identified three concrete problems with running `process_module_forms` unchanged on REPL input:
- **A**: `clear_module_for_replace_public()` wipes existing symbols on fresh modules
- **B**: `finalize_check_result` hardcodes `Replace` strategy
- **C**: Primitive/prelude injection would re-inject on every eval

**Solution**: Add a `ModuleStrategy` parameter to `process_module_forms`. For `Additive`, skip the "fresh start" block (clear, primitive injection, prelude injection). Pass 1 runs for new definitions only (register their signatures). Pass 2 checks new bodies. Strategy flows through to `finalize_check_result`. This is a small conditional — not a redesign.

### C. Expression Compilation

When a form is an expression (not a definition), it is compiled as a temporary closure:

1. `process_module_forms(Additive)` handles it as a `TopLevel::Expr` — typechecked in the module's scope.
2. Codegen compiles it via `compile_and_execute_expr` (existing function) — NOT registered in GOT.
3. Execute and return the result for display.

### D. Simplified Eval Path (no "interceptions")

The old REPL accumulated special-case handling for annotations, trace, and bare symbols. The v4 eval eliminates these:

- **Annotation** (`:Int 42`): Not a special case. Wrap as `(fn [] :Int 42)` — the type annotation constrains inference, codegen produces the right value, display formats it. Just an expression.
- **Trace** (`(trace (fib 5))`): Not a special case. `trace` is already an `Expr::Trace` special form handled by the backend. The REPL's extra trace setup (traced_fns metadata, format overrides) is old-pipeline complexity — the codegen/runtime handles trace end-to-end.
- **Bare symbol** (`foo`): The one check. If input is a single bare symbol → introspect. Otherwise → compile and execute.

The eval path becomes:
```
parse input
if single bare symbol → introspect
else → compile and execute (definitions via worker + trailing expr as closure)
```

defmacro, import, platform, export, mod are already handled by `classify_form` in the v4 worker (Sprint 43).

### E. Slash Commands

Slash commands remain in `src/repl/mod.rs` and `src/repl/commands.rs`. They are dispatched before eval and don't go through the scheduler. The `process_commands()` stub in `session_v4.rs` either:
- Remains unused (REPL main loop dispatches commands directly, as it does now), OR
- Gets wired to call the existing dispatch functions.

Either way, slash commands are unchanged this sprint. The goal is eval migration, not command migration.

### F. Error Recovery

TC snapshot/restore wraps each form individually (per-form serial processing):
- Snapshot before each form
- On error: restore snapshot, display error, continue to next form
- On success: commit (no restore needed)

Note: TC snapshot doesn't restore type_defs/overloads/traits (F4 — pre-existing limitation, same as old REPL). Not Step 7 scope.

### Pause Condition

If the additive strategy requires significant changes to `process_module_forms` or the scheduler, we pause. The v4 worker should handle REPL input naturally — new forms are just more sexps. If it can't, the worker design needs revision.

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `src/worker.rs:545` | /int | design doc §7.2 vs implementation (handle_mod) | carried from S43, deferred: design doc drift, not a bug |
| `src/worker.rs:756` | /int | dep_module ignored in macro deps (same-module assumption) | carried from S43, deferred: cross-module macro deps are Step 11+ |

Both FIXMEs are first-time deferrals from Sprint 43, both for future steps. No escalation needed.

## Architecture Review

**Reviewer**: /arch
**Verdict**: PASS WITH RECOMMENDATIONS

### Coherence
"Eval via scheduler" is a clean boundary. After this sprint, old `compile_unit` delegation in eval() is replaced. Trailing expression as temporary closure is justified per `pipeline-v4.md` §6.2.

### Additive Strategy
The sprint's original option (b) was partially wrong — `process_module_forms` actively destroys existing module state on fresh invocation. Solution: add `ModuleStrategy` parameter, skip fresh-start block for `Additive`. Small change, not a redesign. Should not trigger pause condition.

### Simplified Eval Path
The user's simplification eliminates all "interceptions":
- Annotation: just an expression (wrap as closure)
- Trace: just a special form (backend handles it)
- Bare symbol: single check → introspect

This dramatically reduces Step 7 risk. The eval path is: parse → bare-symbol check → compile-and-execute.

### Slash Commands
Unchanged. Dispatch happens before eval in the REPL main loop. One coupling to watch: slash commands read from `inmem_worker.got_state` — must verify GOT entries are populated by the v4 codegen path.

### Design Review Findings Resolution

| ID | Sev | Finding | Resolution |
|----|-----|---------|------------|
| F1 | B | Annotation claim wrong — `build_program` doesn't fuse `:Type expr` | **Resolved**: Type annotation (§4.9) is a language feature, not a REPL trick. `Expr::Annotate` exists in AST but isn't implemented in the reader/AST builder yet. Not Step 7 scope — when implemented, it works as a normal expression everywhere. |
| F2 | B | `check_expr`/`build_expr` don't exist | **Resolved**: Serial per-form processing uses existing `process_module_forms` for all forms. No new APIs needed. |
| F3 | I | Multiple trailing expressions | **Resolved**: Serial per-form processing. Each form processed individually — expressions display results as they go. No separation logic needed. |
| F4 | I | TC snapshot doesn't restore type_defs/overloads/traits | **Acknowledged**: Pre-existing limitation, same as old REPL. Not Step 7 scope. |
| F5 | I | Double Pass 1 on Blocked retry | **Resolved**: Implementation uses existing resumption mechanism (stored form index, worker loop resumes). No recursion. |
| F8 | S | Scheduler notifications for unregistered module | Must verify — design doc should address. |

### Design Doc Requirements for /int
1. `process_module_forms` additive parameter (skip clear, skip injections, strategy to finalize)
2. Eval function structure (serial per-form: parse → for each sexp → bare-symbol check or compile-and-execute)
3. GOT consistency (slash commands read got_state — v4 codegen must populate it)
4. Session persistence (regenerate REPL module source after definitions)
5. Sketch comparison

## Skill Plans

### /int
**Task**: Replace `session_v4.rs::eval()` with v4 scheduler path. REPL definitions go through `process_module_forms` with additive strategy. Trailing expressions compiled as temporary closures. TC snapshot/restore for error recovery. Bare symbol → introspect, everything else → compile and execute.
**Design doc**: `design/int/step7-repl-eval.md` (to be written)
**Approach**: {to be filled by /int}
**Design refs**: `design/arch/pipeline-v4-roadmap.md` Step 7, `design/arch/pipeline-v4.md` §6, `src/session_v4.rs` (current eval delegation), `src/worker.rs` (process_module_forms — needs additive strategy: skip clear_module, skip primitive/prelude re-injection, pass ModuleStrategy through). **Arch review**: additive problems A/B/C (clear_module, finalize strategy, re-injection).
**Acceptance**: REPL eval works through v4 scheduler. All REPL demo files play cleanly. `(trace ...)`, `:Type expr`, bare symbol introspection all work. TC snapshot/restore recovers from errors. Old `compile_unit` delegation in eval() is deleted.

### /typecheck
**Task**: No changes expected. `check_form` already handles additive input (new forms appended to existing module state).
**Design doc**: n/a
**Approach**: Standby.
**Acceptance**: All existing typecheck tests pass.

### /arch
**Task**: Review sprint scope. Confirm additive eval composes with the scheduler. Confirm no interim architecture.
**Design doc**: n/a (reviewer role)
**Approach**: Phase 2 review.
**Acceptance**: Architecture review section filled.

### /qa
**Task**: Write REPL eval tests through the v4 path. Test: simple eval, definition + eval, multi-eval session, error recovery, trace, annotation, import in REPL, macro in REPL.
**Design doc**: n/a
**Approach**: Spec-first test design from `repl/spec.md` and Step 7 requirements.
**Acceptance**: Tests cover the cases above. All verify REPL correctness.

### /review
**Task**: Review implementation. Special attention to: snapshot/restore correctness, no leaked state on error, interception preservation.
**Design doc**: n/a
**Approach**: Standard review.
**Acceptance**: 0 Blockers, all Important findings resolved.

### /frontend
**Task**: No changes expected.
**Approach**: Standby.
**Acceptance**: n/a

### /backend
**Task**: No changes expected.
**Approach**: Standby.
**Acceptance**: n/a

### /stdlib
**Task**: No changes.
**Approach**: Standby.
**Acceptance**: n/a

### /examples
**Task**: No changes.
**Approach**: Standby.
**Acceptance**: n/a

### /repl
**Task**: No changes to REPL main loop or slash commands. Verify all demo files play cleanly after eval migration.
**Approach**: Validate existing demos.
**Acceptance**: All demo files play without errors.

### /port
**Task**: No changes.
**Approach**: Standby.
**Acceptance**: n/a

### /docs
**Task**: No changes.
**Approach**: Standby.
**Acceptance**: n/a

### /platform
**Task**: No changes.
**Approach**: Standby.
**Acceptance**: n/a

### /spec
**Task**: No changes.
**Approach**: Standby.
**Acceptance**: n/a

## Waves

### Wave 1: Design
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Write `design/int/step7-repl-eval.md` | done | Serial per-form, additive strategy, 5 arch items covered |

### Wave 2: Design Review + Test Planning
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review design doc | done | NEEDS REVISION → revised. F1-F5 resolved. |
| /qa | Derive test cases | done | 33 test cases across 10 categories |

### Wave 3: Implementation + Test + Review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Implement Step 7: additive strategy, serial per-form eval, bare-symbol check | done | ModuleStrategy param on process_module_forms, eval_v4 in repl/mod.rs, run_repl_v4, 7 unit tests |
| /qa | Write REPL eval tests | done | 8 E2E tests in tests/v4_repl_eval.rs, all passing |
| /review | Review new code | done | PASS WITH FINDINGS: 0B, 3I (R1+R2+R3), 4S |

### Wave 4: Build/Test/Review Cycle
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Fix R1 (dead code), R2 (unbounded recursion), R3 (scheduler leak) | done | ~250 lines dead code deleted from session_v4.rs. Retry loop with MAX_DEP_RETRIES=100. Guard in notify_typecheck_done. |
| /qa | Full suite verification | done | All suites pass. 8 v4_repl_eval + 31 v4_pipeline + all others. 11 pre-existing sketch_port only. |

## Notes

**Review findings:**

| ID | Sev | Finding | Resolution |
|----|-----|---------|------------|
| R1 | I | ~250 lines dead eval code in session_v4.rs (duplicated repl/mod.rs) | Fixed: deleted |
| R2 | I | Unbounded recursion on Blocked retry in process_single_form_v4 | Fixed: loop with MAX_DEP_RETRIES=100 |
| R3 | I | Scheduler typecheck_done deque grows unbounded (REPL module unregistered) | Fixed: guard in notify_typecheck_done |
| R4 | S | Repeated scheduler unwrap pattern | Deferred |
| R5 | S | Inconsistent error handling single vs multi form | Deferred |
| R6 | S | process_commands() stub still dead | Deferred |
| R7 | S | Definition display format minimal vs old path | Deferred |

## Outcome

### Delivered

- **Additive strategy for `process_module_forms`** (`src/worker.rs`): `ModuleStrategy` parameter added. For `Additive`: skips `clear_module_for_replace_public`, primitive/macros/prelude injection. All existing callers pass `Replace`. Strategy flows through to `finalize_check_result`.
- **Serial per-form REPL eval** (`src/repl/mod.rs`): `eval_v4()` processes each sexp individually — bare-symbol check or `process_module_forms(Additive)`. `eval_one_form_v4()`, `process_single_form_v4()`, `codegen_and_execute_v4()`, `compile_dep_inline_v4()`, `sync_type_defs()`. Error recovery via TC snapshot/restore per form.
- **`run_repl_v4()`** (`src/repl/mod.rs`): v4 REPL entry point, scheduler on ReplSession, wired from `v4_main` in `src/main.rs`.
- **Bare symbol introspection**: Single bare symbol → introspect (macros, special forms). Everything else → compile and execute.
- **Simplified eval path**: No annotation special case (language feature, not yet in parser). No trace special case (backend handles `Expr::Trace`). No interceptions.
- **Dead code deleted** (`src/session_v4.rs`): ~250 lines of unused duplicate eval chain removed (R1 fix).
- **Blocked retry safety** (`src/repl/mod.rs`): Loop with `MAX_DEP_RETRIES=100` replaces unbounded recursion (R2 fix).
- **Scheduler leak fix** (`src/scheduler.rs`): `notify_typecheck_done` guards against unregistered modules (R3 fix).
- **`compile_and_execute_expr` made public** (`src/pipeline.rs`): Needed by v4 REPL eval.
- **Design doc**: `design/int/step7-repl-eval.md` (9 sections, serial per-form, sketch comparison).
- **8 E2E REPL tests** (`tests/v4_repl_eval.rs`): simple expression, defn+call, multi-eval persistence, error recovery, import, bare symbol, trace, deftype.
- **7 unit tests** in `src/repl/mod.rs` for v4 eval path.

### Test Results

All suites pass except 11 pre-existing sketch_port failures. 0 ignored. 0 new failures.

### Deferred

- **R4/S**: Repeated scheduler unwrap pattern in repl/mod.rs — cosmetic
- **R5/S**: Inconsistent error handling single vs multi form — display edge case
- **R6/S**: `process_commands()` stub in session_v4.rs — reserved for future use
- **R7/S**: Definition display format minimal vs old path — display polish
- **Type annotation (`Expr::Annotate`)**: AST variant exists but parser doesn't construct it. Language feature (spec §4.9), not Step 7 scope. Will work as a normal expression once implemented.

### Findings

- **"Highest risk step" was dramatically simplified** by three user insights: annotation is just an expression, trace is just a special form, bare symbol is the only check. The original roadmap's risk assessment was based on replicating the old REPL's accumulated complexity — which turned out to be unnecessary.
- **Serial per-form processing** is simpler and more correct than the batch approach in the design doc's first draft. Each form gets immediate feedback, errors are isolated, no separation logic needed.
- **Additive strategy** required a modest `ModuleStrategy` parameter (not the "no changes needed" originally claimed). The arch review caught this before implementation.
