# Sprint 33: Pipeline v3 Step 6 — Collapse Orchestration into main

**Status**: COMPLETE
**Ring**: — (structural)
**Goal**: Delete `run_batch_v2` and `compile_for_link_v2` from `pipeline_v2.rs`. Main calls `compile_unit` directly.

## Scope

One pipeline v3 migration step:

### Step 6: Collapse orchestration into main

Per `design/arch/pipeline-v3-roadmap.md` Step 6:

After Steps 3-5 stripped CompileMode, platform prescan, and prelude pre-loading from the orchestrators, `run_batch_v2` and `compile_for_link_v2` are now thin wrappers around session setup + `compile_unit` + codegen + post-processing. Inlined into `main.rs`.

## FIXME Debt

No blocking FIXMEs found.

## Architecture Review

**Verdict: APPROVED** — mechanically sound, low risk. No visibility changes needed. `LinkCompileResult` can be deleted. `CompiledModuleGraph` stays (59 test call sites).

## Skill Plans

### /int
**Task**: Inline orchestrators into main.rs, delete from pipeline_v2.rs
**Design doc**: `design/arch/pipeline-v3-roadmap.md` Step 6
**Approach**: Per /arch: inline run_batch_v2 into run_file_inner(), inline compile_for_link_v2 into link_file_inner(), delete both from pipeline_v2.rs, delete LinkCompileResult
**Acceptance**: `cargo test` passes, orchestrators deleted, `--run` and `--link` work ✓

### /qa
**Task**: Verify test suite passes
**Acceptance**: 1533 passed, 11 pre-existing sketch_port failures, 0 ignored ✓

### /review
**Task**: Review implementation
**Acceptance**: No Blocker findings ✓ (0B, 3I, 3S — I2/I3/S2 fixed, I1 noted)

### /arch
**Task**: Review sprint proposal ✓

### /repl, /frontend, /typecheck, /backend, /platform, /stdlib, /examples, /docs, /port
**Task**: No work this sprint

## Waves

### Wave 1: Implementation + Review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Inline orchestrators, delete from pipeline_v2.rs | done | run_file_inner + link_file_inner, ~200 lines deleted |
| /review | Review implementation | done | 0B, 3I, 3S — I2+I3+S2 fixed |

### Wave 2: Verification
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Verify full test suite | done | 1533 passed, 11 pre-existing sketch_port, 0 ignored |

## Notes

- `run_batch_v2` (~112 lines) inlined into `run_file_inner()`, `compile_for_link_v2` (~93 lines) inlined into `link_file_inner()`. Both return `Result<(), CranelispError>` for `?` propagation.
- `LinkCompileResult` deleted from pipeline.rs — no remaining consumers.
- `CompiledModuleGraph` kept — still used by 59 v1 test call sites (Step 14).
- `pipeline_v2.rs` now contains only `compile_unit` and its stage helpers (compile_unit_inner, load_dependencies, resolve_module_path, codegen_and_execute, queue_background_cache_write, and internal helpers).
- Review I2 fixed: file-not-found errors now return `Err(CranelispError)` instead of `process::exit(1)` bypass.
- Review I3 fixed: stale `compile_for_link_v2` reference in cache_writer.rs doc comment updated.
- Review S2 fixed: `expect()` replaced with `unreachable!("invariant: ...")` for consistency.
- Review I1 noted: `run_file_inner` (105 lines) and `link_file_inner` (114 lines) slightly over 100-line guideline. Session setup duplication could be extracted to a shared helper.

## Outcome

### Delivered

**Step 6 — Collapse orchestration into main:**
- `run_batch_v2` inlined into `run_file_inner()` in main.rs
- `compile_for_link_v2` inlined into `link_file_inner()` in main.rs
- Both use `Result<(), CranelispError>` + `?` propagation with outer `match` for error display
- `run_batch_v2` and `compile_for_link_v2` deleted from `pipeline_v2.rs` (~205 lines removed)
- `LinkCompileResult` deleted from `pipeline.rs`
- Stale doc comment in `cache_writer.rs` updated
- `expect()` → `unreachable!("invariant: ...")` for consistency

**`pipeline_v2.rs` is now just `compile_unit` and its stage helpers.** The v3 roadmap's goal for Steps 1-6 is achieved: orchestration logic lives in main.rs, the pipeline module is a pure compilation engine.

### Deferred
- Function length (I1): `run_file_inner` / `link_file_inner` slightly over 100-line guideline — session setup duplication could be extracted
- `CompiledModuleGraph` type → Step 14

### Findings
- The orchestrators were thin enough that inlining was purely mechanical — no logic changes needed.
- `pipeline_v2.rs` went from ~1,425 lines (Sprint 30) to ~750 lines after Steps 1-6, with a clear single responsibility: `compile_unit` and its stages.
