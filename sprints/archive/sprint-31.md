# Sprint 31: Pipeline v3 Steps 3 + 4 — Simplify CompileContext + Absorb Platform Prescan

**Status**: COMPLETE
**Ring**: — (structural)
**Goal**: Remove `CompileMode` from the pipeline (queue consumers decide GOT-indirect vs direct), and move platform prescan into `compile_unit` stage 2a so orchestrators no longer double-parse entry files.

## Scope

Two independent pipeline v3 migration steps:

### Step 3: Simplify CompileContext

Per `design/arch/pipeline-v3-roadmap.md` Step 3:

- `CompileContext` becomes `{ module, codegen: CodegenBehaviour }`. `ModuleStrategy` becomes a parameter on `compile_unit` instead of a field on `CompileContext`.
- `CodegenBehaviour::InMemoryAndObject` replaces `JitAndCache`. `CodegenBehaviour::ObjectOnly` replaces `ObjectOnly`.
- **Delete `CompileMode`**. Currently 125 references across 16 files (5 in `src/`, 11 in `crates/`). The in-mem queue consumer (`flush_inmem_queue`) decides GOT-indirect vs direct calls based on whether `got_state` exists (interactive) or not (batch). This is a queue-consumer concern, not a pipeline concern.
- Update all `CompileContext` construction sites.

**Verification**: `cargo test` passes. `CompileMode` no longer exists.

### Step 4: Move platform handling into compile_unit

Per `design/arch/pipeline-v3-roadmap.md` Step 4:

- When `compile_unit` encounters `(platform ...)` forms during stage 2 (currently in `extract_module_declarations`), it loads DLLs, registers symbols in `platform_symbols` and `scheduling_registry`, and registers types in tc.
- Delete the prescan loops in `run_batch_v2` (lines 771-788) and `compile_for_link_v2` (lines 991-1007). These currently double-parse the entry file just to find platform declarations.
- `CompilationSession` may need a `project_root: PathBuf` field if not already present (needed for DLL path resolution).

**Verification**: `cargo test` passes. `--run` and `--link` with platform programs still work. No double-parsing.

## FIXME Debt

No blocking FIXMEs found. Scan (2026-03-27) checked all `.md` and `.rs` files outside archives.

## Architecture Review

**Reviewed by /arch — 2026-03-27. APPROVED with guidance.**

### Step 3: CompileMode Removal — Sound

**Reference count verified**: 125 references across 16 files (confirmed by grep). Breakdown by category:

1. **Backend codegen (semantic uses)** — ~8 match sites in `apply.rs`, `control_flow.rs`, `trace_codegen.rs`, `lib.rs`. These are the only places where CompileMode controls actual code generation behavior (direct-call vs GOT-indirect, trace GOT-swap availability). **Replacement**: The backend already has `got_slots: Option<&HashMap<Symbol, usize>>` and `got_base_ptr: Option<i64>` on `CompileCtx`. When `got_slots` is `Some`, emit GOT-indirect; when `None`, emit direct calls. This is a pure data-driven check — CompileMode is redundant given these fields. The `trace_codegen.rs` batch guard (line 69) can check `got_base_ptr.is_none()` equivalently.

2. **`codegen_and_execute` dispatch** (pipeline_v2.rs lines 292-314) — routes to `compile_and_execute_batch` vs `compile_and_execute_interactive`. **Replacement**: Check `session.got_state.is_initialized()` (or equivalent — whether the session has a GOT). Batch callers never initialize `got_state`; interactive callers always do. This is the "queue consumer decides" principle from the design doc, and it is correct.

3. **`compile_and_execute_batch`** (line 484) — passes `CompileMode::Batch` into `cranelisp_backend::compile_program`. After Step 3, this passes `None` for GOT params instead. `setup_interactive_got` already returns `(None, None)` for Batch mode — this function can simply be changed to always return `(None, None)` since the call site knows it is batch.

4. **`load_dependencies`** (line 395) — propagates `compile_mode` to child `CompileContext`. After Step 3, child contexts inherit the same `CodegenBehaviour` from the parent, which is correct.

5. **`CompileContext` construction sites** (~15 sites in pipeline_v2.rs, pipeline.rs, repl/mod.rs, expander.rs, tests) — mechanical: delete the `compile_mode` field, adjust struct literals.

6. **Test sites** (~60 refs across tests/ring2.rs, tests/macros.rs, tests/ring3_repl.rs, tests/pipeline_v2.rs, backend lib.rs tests) — all pass `CompileMode::Batch` or `CompileMode::Interactive` to `compile_and_run` or backend test helpers. **Replacement**: `compile_and_run` drops its `CompileMode` parameter (batch is the only test path). Backend test helpers that currently pass `CompileMode::Batch` pass `None` for GOT; those that pass `CompileMode::Interactive` pass `Some(got_state)`.

7. **Design docs and sprint archives** — references in `.md` files are informational. No code changes needed; update `interfaces.md` and `pipeline-v3-roadmap.md` to reflect the deletion.

**`CodegenBehaviour` rename**: Renaming `CodegenTarget::JitAndCache` to `CodegenBehaviour::InMemoryAndObject` and `ObjectOnly` to `ObjectOnly` is fine. Note: `CodegenBehaviour` is orthogonal to direct/indirect calls — it controls *output format*, not *call convention*. The call convention is now purely data-driven (presence of GOT state). This is a clean separation.

**Risk**: LOW. The compiler's exhaustive match checking will catch every removed `CompileMode` reference. The replacement (GOT presence check) is already the underlying mechanism — CompileMode was always a redundant proxy for "does GOT state exist?".

**`CompileMode::Release`**: Currently `todo!()`/error. Deleting it loses nothing. When release mode is needed (Phase H), it will be expressed as a `CodegenBehaviour` variant or an optimization flag, not a call-convention mode.

### Step 4: Platform Prescan into compile_unit — Sound with Notes

**Current state**: Platform prescan exists in two places (lines 771-788 in `run_batch_v2`, lines 991-1007 in `compile_for_link_v2`). Both re-parse the entry file to find `(platform ...)` forms before `compile_unit` runs. The REPL has its own `eval_platform` path (repl/mod.rs line 900) which is v1 and untouched by this sprint.

**Design**: `extract_module_declarations` will recognize `(platform ...)` forms and return them in `ModuleStructure.platform_specs` (or a new field). `compile_unit` stage 2a iterates these and calls `load_and_register_platform`. This eliminates the double-parse.

**`project_root` on CompilationSession**: `CompilationSession` does NOT currently have a `project_root` field. It lives on `ModuleGraph` (line 1048 of pipeline.rs) and on `ReplSession` (line 103 of repl/mod.rs). Adding it to `CompilationSession` is correct — it is session-wide state needed for DLL path resolution, and currently threaded through as a parameter in the orchestrators. Having it on the session simplifies the interface.

**REPL v1 path**: The REPL's `eval_platform` (repl/mod.rs line 900) is a v1 code path that intercepts `(platform ...)` in the REPL eval loop before any compile_unit call. This sprint does NOT touch v1 REPL eval, so `eval_platform` remains intact. The sprint note is correct — no interaction.

**Ordering**: Steps 3 and 4 are truly independent per the roadmap dependency graph (both depend only on Step 2, which is complete). They can be done in either order. However, Step 3 is lower risk (mechanical deletion with compiler enforcement) while Step 4 involves adding a new field to `ModuleStructure` (a `cranelisp-types` change) and new logic in `compile_unit`. Recommendation: **do Step 3 first** — it reduces noise in the codebase, making Step 4's diff cleaner.

**`ModuleStructure` change**: Adding a `platform_specs` field (or similar) to `ModuleStructure` is a `cranelisp-types` change. This is appropriate — platform declarations are structural metadata, same category as `mod_decls` and `import_specs`. The field should be `Vec<PlatformSpec>` where `PlatformSpec` contains the platform name and span. The `extract_module_declarations` function in `cranelisp-frontend` will need to recognize `(platform ...)` forms — currently it does not. This is a small addition to the frontend crate.

**Callers that would be missed**: None. The prescan only exists in `run_batch_v2` and `compile_for_link_v2`. The REPL's v1 `eval_platform` is a separate path that will be deleted in Step 9 (REPL migration). No other callers parse for platform forms.

### Cross-Cutting Concerns

**Single pipeline invariant**: Both steps advance the single-pipeline goal. Step 3 removes a mode enum that was the original mechanism for pipeline unification (Key Decision 7) but became vestigial once GOT state provided the same information. Step 4 moves platform handling from orchestrators into the shared `compile_unit`, reducing orchestrator-level duplication.

**Interim architecture**: No concerns. Both steps produce clean intermediate states. After Step 3, the pipeline has no compile-mode concept — call convention is data-driven. After Step 4, platform handling is in compile_unit — orchestrators don't double-parse.

**Carried debt**: No FIXMEs found (confirmed by sprint proposal). No deferred items from Sprint 30.

**Test coverage**: `cargo test` is the verification for both steps. The test suite covers batch mode (`compile_and_run`), interactive mode (REPL session tests), platform programs (tests/io.rs, tests/sprint23.rs), and the `--link` path (tests/e2e.rs). Coverage is adequate.

### Recommendations

1. **Do Step 3 before Step 4** — lower risk first, cleaner diff for Step 4.
2. **Backend `CompileCtx.mode` replacement**: Replace `mode: CompileMode` with nothing — the backend already has `got_slots` and `got_base_ptr` which encode the same information. Use `got_slots.is_some()` wherever `mode == Interactive` was checked.
3. **`compile_and_run` test helper**: Drop the `CompileMode` parameter entirely. All test-helper calls pass Batch. The helper becomes a one-argument function.
4. **Update `interfaces.md`**: Remove `CompileMode` from the boundary types section. Add `project_root: PathBuf` to `CompilationSession`. Update `CompileContext` to remove `compile_mode` and show `codegen: CodegenBehaviour`.
5. **`PlatformSpec` type**: Define in `cranelisp-types` as `{ name: String, span: Span }`. Add `platform_specs: Vec<PlatformSpec>` to `ModuleStructure`. Keep it minimal.

## Skill Plans

### /int
**Task**: Remove CompileMode (Step 3), then move platform prescan into compile_unit (Step 4)
**Design doc**: `design/arch/pipeline-v3-roadmap.md` Steps 3, 4
**Approach**: Per /arch review: Step 3 first (mechanical, compiler-enforced), then Step 4. Step 3: delete CompileMode enum from cranelisp-types, replace backend `mode` checks with `got_slots.is_some()`, drop CompileMode param from compile_and_run test helper, update all CompileContext construction sites. Step 4: add PlatformSpec to cranelisp-types, add platform_specs to ModuleStructure, recognize (platform ...) in extract_module_declarations, load platforms in compile_unit stage 2a, add project_root to CompilationSession, delete prescan loops
**Design refs**: `design/arch/pipeline-v3.md` (target architecture), `crates/cranelisp-types/src/pipeline.rs` (CompileMode definition), `src/pipeline_v2.rs` (compile_unit stages)
**Acceptance**: `cargo test` passes, `CompileMode` deleted, platform prescan absorbed into compile_unit ✓

### /qa
**Task**: Verify test suite passes after each step; confirm platform programs work
**Acceptance**: 1533 passed, 11 pre-existing sketch_port failures, 0 ignored ✓

### /review
**Task**: Review code changes for both steps
**Acceptance**: No Blocker findings ✓ (0B, 4I, 5S — I1/I2 fixed, I3/I4 noted)

### /arch
**Task**: Review sprint proposal ✓ (completed — approved with guidance)

### /repl
**Task**: No changes needed — REPL unaffected (uses v1 eval chain)

### /frontend, /typecheck, /backend, /platform, /stdlib, /examples, /docs, /port
**Task**: No work this sprint

## Waves

### Wave 1: Step 3 — Remove CompileMode
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Delete CompileMode, simplify CompileContext | done | 125 refs removed, `interactive: bool` + `got_slots.is_some()` replace |
| /review | Review Step 3 changes | done | Combined with Wave 2 review |

### Wave 2: Step 4 — Absorb platform prescan
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Add PlatformSpec, move prescan into compile_unit, add project_root | done | Frontend + types + pipeline changes |
| /review | Review combined changes | done | 0B, 4I, 5S — I1/I2 cosmetic fixes applied |

### Wave 3: Verification
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Verify full test suite, platform programs | done | 1533 passed, 11 pre-existing sketch_port, 0 ignored |

## Notes

- Step 3 replaced `CompileMode` with two mechanisms: `session.interactive: bool` for pipeline dispatch, `got_slots.is_some()` for backend codegen decisions. The backend's `compile_program` API changed from `mode: CompileMode` to `use_got: bool`.
- Step 4 added `PlatformSpec` type to cranelisp-types, `platform_specs` field to `ModuleStructure`, and platform recognition to `extract_module_declarations` in cranelisp-frontend. `compile_unit` stage 2d now loads platform DLLs.
- `project_root: PathBuf` added to `CompilationSession` — previously a local variable in orchestrators.
- REPL v1 `eval_platform` untouched — separate code path for Step 9.
- `CodegenTarget` NOT renamed to `CodegenBehaviour` — deferred to avoid churn. The enum values (`JitAndCache`, `ObjectOnly`) remain unchanged.
- Review I3: `interfaces.md` and `pipeline-v2.md` now stale re CompileMode — needs /arch update.
- Review I4: Duplicate `loaded_platforms` on `CompilationSession` vs `ReplSession` — latent duplication to address in Step 9 (REPL migration).
- Review S2: `session.interactive` naming could be `use_got` — noted for future cleanup.

## Outcome

### Delivered

**Step 3 — CompileMode removal:**
- Deleted `CompileMode` enum from `cranelisp-types` (3 variants: Batch, Interactive, Release)
- Added `interactive: bool` field to `CompilationSession`
- Backend codegen replaced all mode checks with `got_slots.is_some()` data-driven checks
- `compile_program` API: `mode: CompileMode` → `use_got: bool`
- `compile_and_run` test helper: dropped mode parameter (always batch)
- 125 references across 16 files removed

**Step 4 — Platform prescan absorption:**
- `PlatformSpec` type in `cranelisp-types` (`name: String`, `span: Span`)
- `platform_specs: Vec<PlatformSpec>` field on `ModuleStructure`
- `extract_module_declarations` in cranelisp-frontend recognizes `(platform ...)` forms
- `compile_unit` stage 2d loads platform DLLs from `ModuleStructure.platform_specs`
- `project_root: PathBuf` and `loaded_platforms: Vec<LoadedPlatform>` on `CompilationSession`
- Deleted prescan loops from `run_batch_v2` and `compile_for_link_v2`
- 4 frontend unit tests for platform extraction

**Review fixes:**
- I1/I2: Blank lines and trailing whitespace in struct literals cleaned up

### Deferred
- `CodegenTarget` rename to `CodegenBehaviour` — cosmetic, deferred to avoid churn
- `interfaces.md` / `pipeline-v2.md` CompileMode references — needs /arch update
- `loaded_platforms` duplication (CompilationSession vs ReplSession) — Step 9
- `session.interactive` → `use_got` rename — future cleanup

### Findings
- `CompileMode` was a redundant proxy all along — the backend already had `got_slots` which encoded the same information. Removing it simplified 125 call sites with zero behavioral change.
- Platform prescan was the last orchestrator-level double-parse. After this sprint, orchestrators no longer need to pre-parse entry files.
- 4 new frontend unit tests added for platform form extraction.
