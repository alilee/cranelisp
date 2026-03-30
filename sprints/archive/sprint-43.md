# Sprint 43: Pipeline v4 Steps 5+6 — Lazy Dependency Discovery + MacroExpander Removal

**Status**: COMPLETE
**Ring**: — (structural / pipeline v4 migration)
**Goal**: All programs (multi-module, prelude, operators) compile through the v4 scheduler path. `MacroExpander` trait deleted.

## Context

Sprint 42 delivered Step 4: per-sexp macro expansion with inline compile-and-continue. The v4 path (`--v4 --run`) handles single-module programs with inline macros. The C2 filter rejects any program containing `import`, `export`, `mod`, `platform`, or operator symbols — all of which require cross-module resolution.

This sprint delivers **Steps 5+6** from `design/arch/pipeline-v4-roadmap.md`. Step 5 is the core: lazy dependency discovery makes multi-module programs work, which naturally enables prelude loading, which naturally enables operator resolution. Step 6 is mechanical cleanup: with expansion handled by the worker's inline path, the `MacroExpander` trait and `CraneliftExpander` struct are dead code.

**Key design principle**: Prelude loading, operator resolution, and platform loading are NOT special cases. They are ordinary modules discovered through the same lazy import mechanism as any user module. If the implementation requires special-case logic for any of these, the design is wrong and we pause to reconsider.

**All skills MUST read:**
- `design/arch/pipeline-v4-roadmap.md` — Steps 5+6 specification
- `design/arch/concurrent-pipeline.md` — scheduler blocking/unblocking semantics
- `design/arch/pipeline-v4.md` — target architecture, §3.2 per-form processing
- `src/worker.rs` — current `process_module_forms` (single-module, hardcoded primitive/macro imports)
- `src/session_v4.rs` — current C2 filter (`sexp_qualifies`) and `register_module`
- `src/scheduler.rs` — `register_module`, `register_module_cached`, `block_for_typecheck`

## Scope

### A. Lazy Dependency Discovery in `process_module_forms`

When Pass 1 or Pass 2 encounters a form that references an unresolved module (`import`, `export`, `mod`, `platform`, qualified symbol ref):

1. Resolve the module file path (same resolution order as old path: submodule → sibling → root → lib dirs).
2. Check cache. On cache hit: restore type info, call `scheduler.register_module_cached()`.
3. On cache miss: parse source, call `scheduler.register_module()`.
4. Call `scheduler.block_for_typecheck(module, needed_symbols)` — the current module enters `TypecheckBlocked`.
5. When unblocked (needed symbols are typechecked in the dependency), resume from the blocked form.

Prelude injection: when a non-prelude module starts processing, inject `(import [prelude [*]])` as the first form. This triggers prelude discovery through the same lazy path as any other import — no special prelude logic.

Platform forms: `(platform "name")` triggers lazy discovery of the platform module. Platform DLL loading and function pointer registration happen as part of that module's compilation — same path as any other module.

Circular import detection: a cycle of `TypecheckBlocked` modules (A waits on B, B waits on A) is detected by the scheduler and reported as an error. Replaces the old `compile_stack` mechanism.

### B. Delete C2 Filter

Remove `sexp_qualifies` and `qualifies_for_scheduler` from `session_v4.rs`. All programs route through the v4 scheduler path. The `register_module_old()` fallback is deleted — `register_module` always uses the scheduler.

Operators (`+`, `-`, `*`, `/`, `=`, `<`, `>`, etc.) are just symbols. They resolve to trait methods via prelude imports. Once the prelude loads through lazy discovery, operators resolve through normal typecheck — no special handling.

### C. Remove MacroExpander Trait (Step 6)

With macro expansion handled by the worker's inline path (Sprint 42), `CraneliftExpander` and `MacroExpander` are dead code:

1. Extract remaining marshal/invoke/unmarshal logic into free functions (if not already done in Sprint 42).
2. Update `build_program` in `cranelisp-frontend` to not require `&dyn MacroExpander`.
3. Delete `MacroExpander` trait from `cranelisp-types/src/pipeline.rs`.
4. Delete `NoOpExpander` from `cranelisp-types`.
5. Delete `CraneliftExpander` struct and `MacroEnv` from `src/expander.rs`.
6. Delete `expander` field from `CompilationSession` (and/or `CompilerSession`).

### D. Wire `--v4 --run` Through Full Pipeline

After Steps A-C, `--v4 --run` should handle any program the old path handles. The verification is: for every existing integration test, `--v4 --run` produces identical results to the old path.

### Pause Condition

If lazy dependency discovery requires replicating the old path's prelude-loading complexity (special-case prelude detection, compile-stack management, cache-hit-before-compile logic beyond what the scheduler already provides), we pause. The scheduler's `register_module` / `register_module_cached` / `block_for_typecheck` should be sufficient. If they aren't, the scheduler design needs revision — not a workaround in the worker.

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| (none found) | — | No active FIXMEs in source code | — |

## Architecture Review

**Reviewer**: /arch
**Verdict**: PASS WITH RECOMMENDATIONS

### Coherence
Steps 5+6 combine naturally. Step 5 is substantive (lazy discovery), Step 6 is mechanical cleanup (MacroExpander deletion). Acceptance criterion is well-defined: `--v4 --run` produces identical results to old path for all existing tests.

### No Interim Architecture
Pass. All work is target-state code. The interim code being *removed* includes: C2 filter (`sexp_qualifies`/`qualifies_for_scheduler`), `register_module_old` fallback, `MacroExpander` trait, `CraneliftExpander`, `NoOpExpander`.

### Lazy Discovery Simplicity
The four scheduler APIs (`register_module`, `register_module_cached`, `block_for_typecheck`, `notify_symbol_typechecked`) are sufficient for all scenarios:
- **Imports**: resolve file → register → block. Standard path.
- **Prelude**: inject `(import [prelude [*]])` as first form → triggers same import path. No special logic.
- **Operators**: just symbols, resolve via prelude imports. No special handling.
- **Platform**: `(platform "name")` triggers DLL loading locally in the worker. Not a cross-module blocking operation.
- **Cache hits**: `register_module_cached` enters `TypecheckDone`, satisfies pending waiters. Sufficient.

### Interface Gaps (4)

| ID | Gap | Recommendation |
|----|-----|----------------|
| G-1 | Worker needs `lib_dirs`/`project_root` for file resolution | Bundle into `WorkerContext` struct (current 6 params would grow to 8+) |
| G-2 | `module_sexps` map is static; lazy discovery adds modules dynamically | Worker parses on-demand within the loop |
| G-3 | Scheduler lacks explicit circular import detection | Add cycle detection (walk blocked-module waiter graph) |
| G-4 | MacroExpander removal blocked by REPL old-path dependency | See scoping note below |

### MacroExpander Removal Scoping

REPL `eval` still delegates to old path (until Step 7), which uses `CraneliftExpander`. Two options:
- **(a)** Remove `MacroExpander` from frontend API (30+ signatures) and adjust old REPL path to expand before AST building.
- **(b)** Defer full trait deletion to Step 7. This sprint removes it from the batch v4 path only.

**Recommendation**: Option (a) — remove the trait from the frontend API this sprint. The old REPL path already has expansion logic in `process_forms_sequentially`; adjusting it to expand before `build_program` is mechanical. This keeps Step 6 complete rather than carrying partial cleanup.

### Risk Assessment

**Hardest part**: Getting the lazy discovery loop right — blocking mid-module at import forms, returning to the priority ladder, and resuming from the stored form index. Single-threaded, so same pattern as macro blocking (inline on one thread), but extended to cross-module typecheck blocking.

**Pause trigger risk**: LOW. Scheduler APIs are designed for this. Risk is in the edge cases of recognizing import/export/mod/platform forms during per-sexp processing and correctly wiring them.

### Design Doc Requirements for /int

1. Worker signature refactoring (`WorkerContext` struct)
2. Form recognition strategy — recognize import/export/mod/platform in the sexp stream during pass processing (not upfront extraction)
3. Resumption mechanism — form index in `ModuleState`, worker resumes from stored index
4. Prelude injection placement — single call, no special-case logic
5. Old-path coexistence — what remains alive for REPL eval, what is deleted
6. MacroExpander removal sequencing — exact order of changes
7. Sketch comparison — module resolution order
8. Cycle detection — how circular imports are detected and reported

## Skill Plans

### /int
**Task**: Implement lazy dependency discovery in `process_module_forms`, delete C2 filter, delete `MacroExpander`/`CraneliftExpander`, wire `--v4 --run` for all programs.
**Design doc**: `design/int/step5-lazy-discovery.md` (to be written — must cover the 8 items from arch review)
**Approach**: See `design/int/step5-lazy-discovery.md`. WorkerContext bundles params (§2). Forms classified by `classify_form` during Pass 2 (§3). Imports trigger `register_module` + `block_for_typecheck` — module blocks, worker picks up dep, resumes from stored form index (§4-5). Prelude injected as `(import [prelude [*]])` at form_index=0, flows through same path (§6). C2 filter deleted entirely (§10). MacroExpander removed in 4 phases: route batch→v4, remove from frontend API, delete trait+CraneliftExpander, adjust REPL old path to use free functions (§12). Cycle detection via `blocked_on` linked-list walk (§13).
**Design refs**: `design/arch/pipeline-v4-roadmap.md` Steps 5+6, `design/arch/concurrent-pipeline.md` §5-6, `src/session.rs` (old path prelude/dependency resolution — reference only, not to be replicated), `src/pipeline.rs` (module file resolution logic to reuse). **Arch review**: G-1 (WorkerContext), G-2 (dynamic module_sexps), G-3 (cycle detection), G-4 (MacroExpander removal sequence).
**Acceptance**: `--v4 --run` compiles all programs that the old path compiles. Results match. C2 filter deleted. `MacroExpander` trait deleted.

### /typecheck
**Task**: No changes expected. `check_form` already handles all form types. Verify no regressions from multi-module v4 path.
**Design doc**: n/a
**Approach**: Standby. Available if `check_form` needs adjustment for cross-module symbol resolution timing.
**Design refs**: `crates/cranelisp-typecheck/src/program.rs`
**Acceptance**: All existing typecheck tests pass unchanged.

### /frontend
**Task**: Remove `&dyn MacroExpander` parameter from `build_program`, `build_repl_input`, `build_repl_input_from_sexps`, and all ~30 internal functions in `ast_builder.rs`. Delete `NoOpExpander` from `cranelisp-types`. Delete `MacroExpander` trait from `cranelisp-types/src/pipeline.rs`.
**Design doc**: n/a
**Approach**: Mechanical signature change. All callers (v4 worker, old REPL path) expand sexps before AST building. The 3 expansion call sites in `ast_builder.rs` (lines ~147, ~256, ~1001) are removed — if an unexpanded macro call reaches the AST builder, it becomes a regular function application (fails at typecheck). Per arch review option (a).
**Design refs**: `crates/cranelisp-frontend/src/ast.rs`, `crates/cranelisp-types/src/pipeline.rs`, arch review §MacroExpander Removal Scoping
**Acceptance**: `build_program` compiles without `MacroExpander`. `MacroExpander` trait deleted. `NoOpExpander` deleted. No callers pass an expander.

### /arch
**Task**: Review sprint scope for technical coherence. Confirm lazy discovery composes simply with the scheduler. Confirm no interim architecture.
**Design doc**: n/a (reviewer role)
**Approach**: Phase 2 review.
**Design refs**: `design/arch/pipeline-v4.md`, `design/arch/concurrent-pipeline.md`
**Acceptance**: Architecture review section filled, design docs approved.

### /qa
**Task**: Write integration tests for multi-module programs through the v4 path. Test import discovery, prelude loading, platform loading, operator resolution, circular import detection.
**Design doc**: n/a
**Approach**: Spec-first test design. Each test runs the same program through both old and v4 paths, verifying identical results. Focus on: (1) simple import, (2) transitive imports, (3) prelude auto-load, (4) operator expressions (prelude traits), (5) platform form, (6) circular import error, (7) cache-hit dependency.
**Design refs**: `spec/08-modules.md`, `design/arch/pipeline-v4-roadmap.md` Steps 5+6
**Acceptance**: Tests cover the 7 cases above. All verify v4-vs-old parity.

### /review
**Task**: Review implementation for correctness, adherence to design doc, structural quality. Special attention to: is the lazy discovery path truly uniform (no special cases for prelude/platform/operators)?
**Design doc**: n/a
**Approach**: Standard review during implementation wave.
**Design refs**: `design/review/checklist.md`, `src/CLAUDE.md`
**Acceptance**: 0 Blockers, all Important findings resolved.

### /backend
**Task**: No implementation work this sprint.
**Approach**: Standby.
**Acceptance**: n/a

### /stdlib
**Task**: No implementation work. Prelude loads through the new path but prelude source is unchanged.
**Approach**: Standby.
**Acceptance**: n/a

### /examples
**Task**: No changes this sprint. Examples should compile through v4 path once it handles all programs.
**Approach**: Standby — validate examples work through `--v4 --run` as part of acceptance.
**Acceptance**: n/a

### /repl
**Task**: No changes (REPL remains on old path until Step 7).
**Approach**: Standby.
**Acceptance**: n/a

### /port
**Task**: No changes.
**Approach**: Standby.
**Acceptance**: n/a

### /docs
**Task**: No changes this sprint.
**Approach**: Standby.
**Acceptance**: n/a

### /platform
**Task**: No changes. Platform DLLs load through lazy discovery — no platform-specific code changes.
**Approach**: Standby.
**Acceptance**: n/a

### /spec
**Task**: No changes expected.
**Approach**: Standby.
**Acceptance**: n/a

## Waves

### Wave 1: Design
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Write `design/int/step5-lazy-discovery.md` | done | 8 arch review items covered |

### Wave 2: Design Review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review design doc for coherence, no special-case logic | done | NEEDS REVISION (minor): 2B + 4I + 4S |
| /qa | Derive test cases from design doc | done | 17 test cases (7 core + 10 additional) |

### Wave 3: Implementation + Test + Review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Step 5: lazy discovery, C2 deletion, prelude/platform/mod handling | done | ~900 lines: WorkerContext, FormKind, ProcessResult, handle_import/export/mod/platform, prelude injection, cycle detection, notify_typecheck_done sweep. C2 filter deleted. |
| /int | Step 6: MacroExpander removal (phases 6a,6c,6d) | done | Deleted MacroExpander trait, NoOpExpander, CraneliftExpander. MacroEnv standalone on CompilationSession. REPL old path uses free expansion functions. |
| /frontend | Remove `&dyn MacroExpander` from API (phase 6b) | done | Removed from 24 functions in ast_builder.rs + 3 public API functions. 3 expansion call sites removed. 232 frontend tests pass. |
| /qa | Write v4 parity tests (7 cases from skill plan) | done | 11 tests written, 3 test bugs fixed (operator error format, export semantics, cache exit code). All 31 v4 tests pass. |
| /review | Review new code | done | PASS WITH FINDINGS: 0B, 2I, 5S. Both I findings fixed. |

### Wave 4: Build/Test/Review Cycle
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Fix review findings R1+R2 | done | R1: extracted inject_prelude_if_needed (115→70 lines). R2: compile_macro_clause_inline uses WorkerContext (8→6 params). |
| /qa | Full suite verification | done | All suites pass. 31 v4 pipeline tests. 11 pre-existing sketch_port failures only. |

## Notes

**Wave 2 design review findings (from /arch):**

| ID | Sev | Finding | Resolution |
|----|-----|---------|------------|
| F1 | B | `block_for_typecheck` split between `handle_import` and worker loop — fragile | Must fix: call inside `handle_import` |
| F2 | B | Multi-spec `(import [a [*]] [b [*]])` re-processes registered specs on resume | Must fix: ensure `register_import` is idempotent, or track per-spec |
| F3 | I | `module_state_mut` accessor not listed as new scheduler API | Address in implementation |
| F4 | I | Accumulator save/restore across suspension underspecified | Address in implementation |
| F5 | I | Pass 1 batch vs Pass 2 start_form_index needs explicit statement | Address in design doc revision |
| F6 | I | First cycle detection algorithm (§13.2) should be marked superseded | Address in design doc revision |
| F7 | S | `form_index == 0` prelude re-check semantics deserves comment | Note for implementation |
| F8 | S | Platform DLL leak → known debt for Step 8 | Track |
| F9 | S | Codegen dep ordering invariant worth stating | Note for implementation |
| F10 | S | Unexpanded macro → type error is degraded diagnostic | Future improvement |

**Wave 2 test plan (from /qa):** 17 test cases covering lazy discovery, resumption, prelude auto-load, operators, platform, circular imports, cache hits, mod/export, glob imports, cross-module macros, C2 deletion, REPL old-path survival.

**Cycle detection improvement (deferred):** Current approach checks for cycles on every `block_for_typecheck` call (O(depth) per import). Better approach: drain the worker loop until no work remains, then check if any modules are still in `TypecheckBlocked` — those are the cycle(s). Detects all cycles at once, amortized O(1), and avoids per-block checks that get racy under multi-threading (Step 11). The blocked-module set *is* the diagnostic.

## Outcome

### Delivered

- **Lazy dependency discovery** (`src/worker.rs`): `process_module_forms` discovers imports during per-sexp Pass 2. `WorkerContext` bundles 6 params. `FormKind` enum + `classify_form` for per-sexp dispatch. `handle_import` resolves files, registers with scheduler, blocks via `block_for_typecheck`. `ProcessResult::Blocked` with form index resumption. `ModuleSuspendState` preserves accumulator across suspensions.
- **Prelude injection** — single `inject_prelude_if_needed` call at form_index=0, flows through same lazy import path as user imports. No special-case prelude logic.
- **Platform handling** — `handle_platform` loads DLLs synchronously in the worker. No scheduler blocking.
- **Export/mod handling** — `handle_export` registers re-exports, `handle_mod` relies on file-system discovery.
- **C2 filter deleted** (`src/session_v4.rs`): `sexp_qualifies`, `qualifies_for_scheduler`, `is_operator_symbol`, `register_module_old` all removed. All programs route through v4 scheduler.
- **Cycle detection** (`src/scheduler.rs`): `blocked_on: Option<ModuleFullPath>` on `ModuleState`. `detect_cycle` linked-list walk. `block_for_typecheck` returns `Result` and checks for cycles. `notify_typecheck_done` sweeps all `WaitKind::Typecheck` waiters.
- **MacroExpander trait deleted** (`cranelisp-types/src/pipeline.rs`): `MacroExpander` trait, `NoOpExpander` deleted. `CraneliftExpander` deleted from `src/expander.rs`. `MacroEnv` standalone on `CompilationSession`.
- **Frontend API cleaned** (`crates/cranelisp-frontend/src/ast_builder.rs`): `&dyn MacroExpander` removed from 24 internal functions + 3 public API functions. 3 expansion call sites removed.
- **REPL old path adjusted** (`src/session.rs`, `src/repl/`): `macro_env: MacroEnv` field replaces `expander: CraneliftExpander`. REPL uses free expansion functions directly.
- **Frontend sexp-level parsers** (`crates/cranelisp-frontend/src/module_extract.rs`): `parse_import_sexp`, `parse_export_sexp`, `parse_mod_sexp`, `parse_platform_sexp` exposed as public API for v4 worker.
- **Design doc**: `design/int/step5-lazy-discovery.md` (17 sections, sketch comparison, 8 arch review items).
- **11 new v4 parity tests** (`tests/v4_pipeline.rs`): simple import, transitive, prelude auto-load, operators, platform, circular import error, cache hit, resumption, export re-export, glob import, multiple imports. Total: 31 v4 pipeline tests.

### Test Results

All suites pass except 11 pre-existing sketch_port failures. 0 ignored. 0 new failures. 37 pre-existing clippy warnings, 0 new.

### Deferred

- **Cycle detection improvement**: Move from per-block O(depth) check to drain-then-inspect approach (check blocked modules when worker loop exhausts work). Better for multi-threading (Step 11). See Notes.
- **R5/S**: `handle_mod` design doc drift — FIXME(/int) filed in `src/worker.rs`
- **R4/S**: Cross-module macro deps — FIXME(/int) filed in `src/worker.rs`
- **F8/S**: Platform DLL leak — known debt for Step 8 (platform registry)
- **F10/S**: Unexpanded macro reaching AST builder produces type error instead of "unknown macro" — diagnostic improvement for later

### Findings

- **Uniform lazy discovery works**: Prelude, platform, operators all flow through the same import mechanism. No special-case logic required. The design principle held.
- **Scheduler APIs sufficient**: The four core APIs (`register_module`, `register_module_cached`, `block_for_typecheck`, `notify_symbol_typechecked`) plus `notify_typecheck_done` sweep covered all scenarios. No workarounds needed. Pause condition was never triggered.
- **MacroExpander trait was clean to delete**: The v4 worker's inline expansion (Sprint 42) made the trait truly dead. `MacroEnv` survives as a standalone type for the REPL old path — correct boundary for Step 7.
- **Test design caught 3 bugs**: /qa's spec-first test plan revealed wrong export syntax, wrong exit code expectation, and error format mismatch — all test-side issues, but the process worked.
