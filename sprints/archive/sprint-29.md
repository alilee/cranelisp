# Sprint 29: Pipeline v3 Step 1 — Decouple Codegen from compile_unit

**Status**: COMPLETE
**Ring**: — (structural)
**Goal**: `compile_unit()` returns after stage 5 (typecheck). Codegen moves to callers via a new `codegen_and_execute()` function.

## Scope

Step 1 of the pipeline v3 migration roadmap (`design/arch/pipeline-v3-roadmap.md`). This is a mechanical refactoring that separates *what* (typecheck) from *where* (memory vs .o vs disk). After this sprint:

- `compile_unit()` returns `CompileUnitResult` containing `program`, `module_structure`, `source`, and `check_result` — but no `value` or `result_type`
- New `codegen_and_execute()` function takes a `&CompileUnitResult` and performs stages 6-7 (codegen, execute, module aliases, cache write, func_sigs)
- All callers of `compile_unit()` add a `codegen_and_execute()` call after it
- Dead transitional code (`compile_unit_from_sexps`, `compile_unit_from_program`) deleted
- `cargo test` passes with no behaviour change

## FIXME Debt

No FIXMEs block this sprint. This is a structural refactoring that doesn't touch owned files of other skills.

## Architecture Review

**Reviewer**: /arch
**Date**: 2026-03-26
**Verdict**: APPROVED with notes

### Technical Coherence

The scope forms a complete, testable increment. After this sprint, `compile_unit` returns at stage 5 and codegen is the caller's responsibility. This is exactly the separation described in `design/arch/pipeline-v3.md` invariant 2 ("No codegen in `compile_unit`") and `pipeline-v3-roadmap.md` Step 1. The verification criterion (`cargo test` passes, no behaviour change) is sufficient and compiler-enforced: changing `CompileUnitResult`'s fields will produce compile errors at every use site, making it impossible to miss a caller.

The dead code deletion (`compile_unit_from_sexps`, `compile_unit_from_program`) is confirmed safe — grep shows zero call sites outside their own definitions.

### No Interim Architecture

Correct. The extracted `codegen_and_execute()` function is permanent v3 structure. It is the precursor to Step 2's queue-based `CodegenItem`, not throwaway scaffolding. The function signature should accept `&CompileUnitResult` (borrow, not consume) so that callers can still inspect `check_result` and `warnings` after codegen — this matches Step 2 where the same data is cloned into `CodegenItem`.

### Type Placement: `CodegenResult`

The sprint proposal mentions a new `CodegenResult` struct. This type should live in `pipeline_v2.rs`, NOT in `cranelisp-types`. Rationale:

- `CodegenResult` is consumed only within the binary crate — no downstream crate needs it.
- It holds execution output (`value: Option<i64>`, `result_type: Option<Type>`) which are runtime artefacts, not pipeline boundary data.
- `cranelisp-types` is for cross-crate boundary types (Principle 2: narrow interfaces). Adding runtime-only types inflates the shared contract.
- When Step 2 introduces `CodegenItem` (which also lives in the session/pipeline layer), `CodegenResult` will be its natural companion.

Similarly, the modified `CompileUnitResult` (gaining `program` and `module_structure`, losing `value` and `result_type`) should remain in `pipeline_v2.rs` for now. It crosses no crate boundary today. If Step 9 (REPL refactor) or Step 6 (collapse orchestration) needs it in a shared location, that migration is a later step's concern.

### Interface Considerations

1. **`program` field ownership.** `CompileUnitResult.program: Vec<TopLevel>` — `codegen_and_execute` will need to borrow this, not consume it, because Step 2 will clone it into `CodegenItem`. Use `&[TopLevel]` in the `codegen_and_execute` signature rather than moving out of the result.

2. **`pre_existing` GOT snapshot.** Lines 108-116 of `compile_unit_inner` snapshot pre-existing GOT entries for `register_module_aliases_filtered` (line 242). This snapshot is a codegen concern (it gates alias registration after Interactive-mode compilation). It must move into `codegen_and_execute`, not remain in `compile_unit`. Verify this is included in the extraction scope.

3. **`check_ctx` override.** Lines 202-211 override `ModuleStrategy::Replace` to `Additive` for the typecheck call. This stays in `compile_unit` (it is a stage 5 concern). Confirm it is NOT extracted.

4. **`module_structure` lifetime.** Currently `structure` is a local in `compile_unit_inner` and is consumed by `session.compiled_module_structures.push(...)` at line 252. After extraction, `compile_unit` must return it in `CompileUnitResult` and `codegen_and_execute` must push it. This is noted in the scope but worth highlighting: the `module_structure` field serves both display (callers may inspect it) and codegen (the cache write at line 248 and link tracking at line 252).

### Design Doc Coverage

`design/arch/pipeline-v3-roadmap.md` Step 1 is sufficient as the design reference. No additional design doc is needed for a mechanical extraction. The pipeline-v3.md target architecture (sections 3.5, 12) already describes the end state where `compile_unit` returns `CompileUnitResult` without `value`/`result_type`.

### Single Pipeline Invariant

Maintained. This sprint does not create parallel paths — it splits one sequential function into two sequential functions called at the same sites.

### Carried Debt

No FIXMEs block this sprint. The REPL remains on v1 (deferred to Step 9) — this is by design, not debt accumulation.

### Risk Assessment

LOW. Mechanical refactoring with compiler-enforced correctness at every call site. The only subtlety is ensuring the `pre_existing` GOT snapshot and post-codegen bookkeeping (module aliases, cache write, func_sigs, compiled_module_structures) all move correctly into `codegen_and_execute`.

## Skill Plans

### /int
**Task**: Refactor `compile_unit` and create `codegen_and_execute`
**Design doc**: `design/arch/pipeline-v3-roadmap.md` Step 1
**Approach**: Per `/arch` review notes — all items implemented as specified.
**Acceptance**: `cargo test` passes, no behaviour change — VERIFIED

### /qa
**Task**: Verify test suite passes after refactoring; confirm no behaviour change
**Acceptance**: PASS — 1,533 passing, same 11 pre-existing sketch_port failures, 0 ignored, 0 new regressions

### /review
**Task**: Review extracted code for quality
**Acceptance**: No Blockers. I1 (compile_unit_inner length) fixed via `empty_check_result()` extraction. I2/I3 pre-existing function length issues noted for follow-up. S1-S4 suggestions documented.

### /arch
**Task**: Architecture review — APPROVED with notes (see above)

### /repl
**Task**: Verify existing demos play cleanly — VERIFIED (REPL untouched, smoke test passed)

### /frontend, /typecheck, /backend, /platform, /stdlib, /examples, /docs, /port
**Task**: No work this sprint (structural refactoring in `/int` scope only)

## Waves

### Wave 1: Implementation + Test + Review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Refactor types, extract codegen, update callers, delete dead code | complete | All /arch notes addressed |
| /qa | Verify test suite post-refactoring | complete | PASS |
| /review | Review code changes | complete | 0B, 1I fixed, 2I pre-existing, 4S |

### Wave 2: Verification
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /repl | Verify existing demos play cleanly | complete | Smoke test passed |

## Notes

- Sprint 28 deferred REPL migration (Step 9). This sprint does not touch the REPL — the REPL still uses v1 eval chain.
- Pre-existing state: 11 sketch_port failures (triaged Sprint 26), 0 ignored tests.
- `/review` S1: `source: String` in `CompileUnitResult` deviates from v3 design doc (which doesn't include it). Kept for simplicity — revisit in Step 2 when `CodegenItem` is introduced.
- `/arch` analysis on pulling Step 14 forward: REPL uses 6 `pipeline.rs` functions (`load_prelude_into_session`, `load_module_into_session`, `compile_module_graph_for_cache`, `write_module_cache`, `build_file_to_module_map`, `build_module_dependency_map`). A partial cleanup (delete dead code, keep REPL-used functions) is feasible for Sprint 30.

## Outcome

### Delivered

**Pipeline v3 Step 1 — codegen decoupled from compile_unit:**
- `compile_unit()` now returns after stage 5 (typecheck) with `CompileUnitResult { program, module_structure, check_result, source, warnings }`
- New `codegen_and_execute()` performs stages 6-7: codegen dispatch (batch/interactive), GOT snapshot, module alias registration, background .o cache write, module structure recording, func_sigs accumulation
- New `CodegenResult { value, result_type, warnings }` returned by `codegen_and_execute()`
- `codegen_and_execute` borrows `&CompileUnitResult` (not consuming) per `/arch` guidance
- `pre_existing` GOT snapshot correctly moved into `codegen_and_execute` (codegen concern)
- `check_ctx` strategy override correctly stays in `compile_unit` (stage 5 concern)

**Callers updated (13 call sites):**
- `load_dependencies` — recursive dep loading
- `run_batch_v2` — prelude deps (loop), prelude, entry file
- `compile_for_link_v2` — each module in topo order
- `load_prelude_for_link` — prelude deps (loop), prelude
- `compile_and_run` — test helper (pipeline.rs)
- `tests/pipeline_v2.rs` — 2 test helpers (`compile_v2_batch`, `compile_v2_interactive`)
- 4 inline unit tests in pipeline_v2.rs

**Dead code deleted:**
- `compile_unit_from_sexps` — unused transitional entry point
- `compile_unit_from_program` — unused transitional entry point

**/review I1 fix:**
- Extracted `empty_check_result()` helper to reduce `compile_unit_inner` below 100-line limit

**Test results**: 1,533 passing, 11 pre-existing sketch_port failures (unchanged), 0 ignored, 0 warnings, 0 clippy errors

### Deferred

- **/review I2/I3**: `run_batch_v2` (176 lines) and `compile_for_link_v2` (124 lines) exceed the 100-line limit. Pre-existing — not introduced by this sprint. Will be addressed in Steps 4-6 (platform/prelude/orchestration collapse).
- **/review S1**: `source: String` in `CompileUnitResult` — revisit alignment with v3 design doc in Step 2.
- **Partial pipeline.rs cleanup**: ~2,000 lines of dead v1 code remain. REPL uses 6 pipeline.rs functions. A partial cleanup is feasible for Sprint 30.

### Findings

- The v3 roadmap's Step 14 placement (second-to-last) carries unnecessary legacy debt through 13 steps. A partial cleanup after Step 1 would remove ~1,500 lines of dead code while keeping the 6 REPL-used functions alive until Step 9.
- One flaky test (`sketch_rc_nested_let_inner_scope_freed`) occasionally fails under parallel execution but passes in isolation. Pre-existing RC tracing race condition.
