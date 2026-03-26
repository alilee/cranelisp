# Sprint 30: Pipeline v3 Step 2 — CodegenItem Queues

**Status**: COMPLETE
**Ring**: — (structural)
**Goal**: Introduce `CodegenItem` and synchronous codegen queues as the foundation for concurrent compilation.

## Scope

One pipeline v3 migration step:

### Step 2: Introduce CodegenItem and synchronous queues

Per `design/arch/pipeline-v3-roadmap.md` Step 2:

- Define `CodegenItem { module, program, check_result, module_structure, source }`
- Add `inmem_queue: Vec<CodegenItem>` and `object_queue: Vec<CodegenItem>` to `CompilationSession`
- Replace direct `codegen_and_execute` calls with queue push + flush
- New `flush_inmem_queue()` and `flush_object_queue()` drain queues synchronously
- `run_batch_v2`: queue push + `flush_inmem_queue`
- `compile_for_link_v2`: queue push + `flush_object_queue`

**Design clarification (per /arch review)**: The caller-side function (`codegen_and_execute` or its callers) pushes to queues, NOT `compile_unit`. This preserves the Step 1 decoupling where `compile_unit` returns after stage 5.

**Verification**: `cargo test` passes. Same behaviour, but codegen goes through queues.

### Step 1.5: DROPPED

/arch review found the dead code list was incorrect — all listed functions have live callers (41+ test sites via `compile_module_graph`). Dead code deletion deferred to Step 14 per the original v3 roadmap.

## FIXME Debt

No blocking FIXMEs found. FIXME scan (2026-03-26) checked all `.md` and `.rs` files outside archives.

## Architecture Review

**Reviewer**: /arch
**Date**: 2026-03-26
**Verdict**: APPROVED (Step 2 only, after dropping Step 1.5)

### Step 1.5: Dead Code List — ERRORS FOUND

The dead code list conflated functions in other crates with functions that have live test callers. None of the listed functions were genuinely dead. Dropped from sprint scope. See full analysis in sprint notes.

### Step 2: CodegenItem Queues — SOUND

- Queue abstraction before concurrency follows mechanical refactoring principles
- Synchronous draining = zero behaviour change, verified by existing tests
- Two queues (`inmem_queue` for JIT, `object_queue` for .o files) map to Step 11's concurrent workers
- Fields: `module`, `program`, `check_result`, `module_structure`, `source` — captures everything needed
- CodegenItem survives to Step 11+ — no interim architecture
- Caller pushes to queues (not `compile_unit`) preserving Step 1 decoupling
- Risk: LOW — mechanical refactoring

## Skill Plans

### /int
**Task**: Implement CodegenItem queues (Step 2)
**Design doc**: `design/arch/pipeline-v3-roadmap.md` Step 2
**Approach**: Define `CodegenItem` struct, add queue fields to `CompilationSession`, replace direct `codegen_and_execute` calls in `run_batch_v2` and `compile_for_link_v2` with queue push + flush. Callers push to appropriate queue(s) based on `CodegenTarget`, then call `flush_inmem_queue()` or `flush_object_queue()`.
**Acceptance**: `cargo test` passes, codegen flows through queues ✓

### /qa
**Task**: Verify test suite passes — same results as Sprint 29
**Acceptance**: 1533 passed, 11 pre-existing sketch_port failures, 0 ignored ✓

### /review
**Task**: Review CodegenItem implementation
**Acceptance**: No Blocker findings ✓ (0B, 3I, 4S — I1+S2 fixed, I3 noted for future)

### /arch
**Task**: Review sprint proposal ✓ (completed above)

### /repl
**Task**: No changes needed — REPL unaffected (uses v1 eval chain, not pipeline_v2)

### /frontend, /typecheck, /backend, /platform, /stdlib, /examples, /docs, /port
**Task**: No work this sprint

## Waves

### Wave 1: Implementation + Review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Implement CodegenItem queues | done | CodegenItem struct + queue fields + flush methods + all call sites converted |
| /review | Review implementation | done | 0B, 3I, 4S — I1 (flush duplication doc'd), I3 (queue naming noted), S2 (mem::take applied) |

### Wave 2: Verification
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Verify full test suite | done | 1533 passed, 11 pre-existing sketch_port failures, 0 ignored, 9 pre-existing clippy warnings |

## Notes

- Step 1.5 was proposed during Sprint 29 as cleanup. /arch review found the dead code list was incorrect — functions listed as dead have 41+ live test callers via `compile_module_graph`. Correctly deferred to Step 14 per the original v3 roadmap.
- /arch clarified: callers push to queues (not `compile_unit`), preserving Step 1's decoupling.
- `CodegenItem` has two fields: `ctx: CompileContext` and `unit_result: CompileUnitResult` — simpler than the roadmap's five-field design since `CompileUnitResult` already contains `program`, `check_result`, `module_structure`, and `source`.
- `compile_and_run` (test helper, 449+ call sites) also converted to queue pattern for consistency.
- `load_dependencies` inside `compile_unit` still calls `codegen_and_execute` directly — intentional, as this pre-existing coupling is a separate concern for a later step.
- Review finding I1 (flush duplication) addressed with doc comments explaining intentional separation for Step 11 divergence.
- Review finding S2 (unnecessary collect) fixed — `std::mem::take` replaces `drain(..).collect()`.
- Review finding I3 (object_queue naming mismatch with JitAndCache target) noted for future — naming reflects intended evolution, not current state.

## Outcome

### Delivered
- `CodegenItem` struct in `pipeline_v2.rs` — captures `CompileContext` + `CompileUnitResult` for deferred codegen
- `inmem_queue` and `object_queue` fields on `CompilationSession`
- `flush_inmem_queue()` and `flush_object_queue()` methods — synchronous queue draining
- All v2 pipeline call sites converted: `run_batch_v2` (3 sites), `compile_for_link_v2` (1 site), `load_prelude_for_link` (2 sites), `compile_and_run` test helper (1 site)
- Review findings I1 and S2 addressed

### Deferred
- Step 1.5 (dead code cleanup) → Step 14 per original v3 roadmap
- Review finding I3 (queue naming) → future cleanup when queues diverge

### Findings
- The Sprint 29 dead code list was based on incorrect analysis — /arch review caught that all listed functions have live test callers. Lesson: verify dead code claims with grep before planning deletion sprints.
- `CodegenItem` is simpler than originally designed (2 fields vs 5) because `CompileUnitResult` already aggregates the needed data.
