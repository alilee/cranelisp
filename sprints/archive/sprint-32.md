# Sprint 32: Pipeline v3 Step 5 — Prelude Auto-Loading

**Status**: COMPLETE
**Ring**: — (structural)
**Goal**: Prelude loads via the normal dependency resolution path inside `compile_unit`. No pre-loading by orchestrators.

## Scope

One pipeline v3 migration step:

### Step 5: Move prelude loading into compile_unit

Per `design/arch/pipeline-v3-roadmap.md` Step 5:

- Currently, `run_batch_v2` (lines 768-828) and `load_prelude_for_link` (lines 1024-1099) manually: resolve prelude path, read source, parse to find export specs, pre-load export target modules, compile prelude — all before calling `compile_unit` on the entry file. This duplicates 60+ lines across two call sites.
- After this sprint: when `compile_unit` encounters a non-prelude module and the prelude isn't loaded yet, it resolves and compiles the prelude via recursive `compile_unit` — the same mechanism used for any other dependency.
- The prelude's own dependencies (the core modules it re-exports) load via the prelude's `load_dependencies` call during its own `compile_unit` invocation.

**Key challenge**: The prelude uses `(export [module [*]])` to re-export modules. The current `load_dependencies` only handles `import_specs`. Export target modules must also be loaded before the prelude's exports can be registered. This means `load_dependencies` (or a new `load_export_dependencies`) must also load modules referenced by export specs.

**Changes**:
1. **Extend `load_dependencies`** (or add `load_export_dependencies`) to also load modules referenced by `export_specs` that aren't yet compiled. This ensures the prelude's re-exported modules are available.
2. **Add auto-prelude loading** in `compile_unit`: at stage 2b, before loading import dependencies, check if prelude is needed (not yet loaded, current module is not prelude, lib_dirs is non-empty). If so, resolve prelude path, read source, compile via recursive `compile_unit`.
3. **Delete prelude pre-loading** from `run_batch_v2` (lines 768-828).
4. **Delete `load_prelude_for_link`** function entirely (lines 1024-1099).
5. **Delete the `load_prelude_for_link` call** from `compile_for_link_v2`.

**Verification**: `cargo test` passes. Prelude loads automatically on first `compile_unit` call for a non-prelude module. `--run` and `--link` with stdlib-using programs still work.

## FIXME Debt

No blocking FIXMEs found. Scan (2026-03-27) checked all `.md` and `.rs` files outside archives.

## Architecture Review

**Verdict: APPROVED with design guidance.**

### Single Pipeline Coherence

This sprint directly advances Principle 11 (single pipeline, mode parameters). Two call sites (`run_batch_v2` lines 768-828, `load_prelude_for_link` lines 1024-1099) duplicate ~60 lines of prelude pre-loading logic with minor variations (inmem queue vs object queue). Absorbing this into `compile_unit` eliminates the duplication and ensures every module — prelude included — loads through the same recursive `compile_unit` path. This is the right direction.

### Key Design Decision: Extend `load_dependencies` to cover export targets

**Recommendation: Extend `load_dependencies`, do not add a separate function.**

The v1 pipeline (`pipeline.rs` line 1305-1309) already solved this correctly: `discover_import_dependencies` chains `import_specs` and `export_specs` module paths together into a single dependency set. The v2 `load_dependencies` should follow the same pattern.

Concretely, `load_dependencies` should accept `&ModuleStructure` (or both `&[ImportSpec]` and `&[ExportSpec]`) instead of only `&[ImportSpec]`. It iterates the union of import and export module paths, skipping already-loaded modules, and recursively `compile_unit`s each one. This is a one-line signature change and a two-line body change (chain the iterators). No new function needed.

**Rationale**: Export-target loading is semantically identical to import-target loading — resolve path, read source, recursive `compile_unit`. A separate `load_export_dependencies` function would be a near-duplicate, violating Principle 7 (single source of truth). Any future module declaration that references another module (e.g., hypothetical `(re-export ...)`) should also route through this same function.

### Ordering: Where prelude auto-load goes in compile_unit_inner

The sprint proposal says "at stage 2b, before loading import dependencies." This is almost right but the precise insertion point matters. The recommended sequence for `compile_unit_inner` stages 2-2c:

1. **Stage 2a**: `extract_module_declarations` (unchanged)
2. **Stage 2b (new)**: Auto-prelude trigger — if `!tc.has_module("prelude") && module != "prelude" && !lib_dirs.is_empty()`, resolve prelude path, read source, `compile_unit(session, &prelude_source, &prelude_ctx)`, then `codegen_and_execute` for the prelude result. After this returns, the prelude and all its export-target modules are compiled (because the prelude's own `compile_unit` call will hit `load_dependencies` which now loads export targets too).
3. **Stage 2c (was 2b)**: `load_dependencies` for this module's imports+exports (now extended).
4. **Stage 2d (was 2c)**: `set_current_module`, `inject_prelude_import`, `register_imports`, `register_exports`.

The prelude auto-load MUST happen before `load_dependencies` for the entry module. Reason: the entry module's imports may reference modules that the prelude also imports (e.g., `compare.eq`). If the prelude loads first, those modules are already compiled when the entry module's `load_dependencies` runs, so they get the `has_module` fast path. If the prelude loads after, the entry module loads them, and then the prelude's `load_dependencies` skips them. Either order is correct, but prelude-first is cleaner because `inject_prelude_import` at stage 2d needs the prelude to exist.

### Codegen for auto-loaded prelude

The sprint proposal does not explicitly address codegen for the prelude when auto-loaded. Currently, `run_batch_v2` pushes the prelude `CompileUnitResult` to `inmem_queue` and flushes. When `compile_unit` auto-loads the prelude recursively, the prelude's codegen must also happen. This is already handled by `load_dependencies` which calls `codegen_and_execute` after each recursive `compile_unit` (line 428). The auto-prelude trigger should do the same: call `codegen_and_execute` on the prelude result immediately after `compile_unit` returns. `/int` should verify this works for both `--run` (JitAndCache) and `--link` (ObjectOnly) codegen targets — the prelude should inherit the caller's `codegen_target`.

### Cycle safety

The compile stack already prevents cycles. The prelude cannot import itself (it has no `(import [prelude ...])` — it only has `(export ...)` forms whose targets are domain modules). Domain modules do not import the prelude either (they import `primitives` and peer modules). No new cycle risk.

### No `lib_dirs` edge case

When `lib_dirs` is empty (test mode with no stdlib), the prelude path won't resolve and auto-loading correctly does nothing. The `inject_prelude_import` guard (`tc.has_module("prelude")`) already handles this — if prelude didn't load, no import is injected. No change needed here.

### Carried debt

No blocking FIXMEs. This is a clean mechanical refactoring step. Approved.

### Sketch comparison

The v1 pipeline's `discover_import_dependencies` (pipeline.rs line 1302-1309) chains import and export module paths — this sprint's approach follows the same proven pattern. The sketch's approach of pre-loading export targets before compiling the prelude is exactly what's being absorbed. No divergence concerns.

## Skill Plans

### /int
**Task**: Move prelude loading into compile_unit (Step 5)
**Design doc**: `design/arch/pipeline-v3-roadmap.md` Step 5
**Approach**: Per /arch review: (1) Extend `load_dependencies` to accept `&ModuleStructure` and iterate union of import+export module paths, (2) Add auto-prelude trigger in compile_unit_inner after stage 2a — resolve prelude, compile_unit recursively, codegen_and_execute, (3) Delete prelude pre-loading from run_batch_v2 and load_prelude_for_link entirely
**Design refs**: `src/pipeline_v2.rs` (compile_unit stages, load_dependencies, run_batch_v2, load_prelude_for_link)
**Acceptance**: `cargo test` passes, no prelude pre-loading in orchestrators, `load_prelude_for_link` deleted ✓

### /qa
**Task**: Verify test suite passes; confirm prelude programs work
**Acceptance**: 1533 passed, 11 pre-existing sketch_port failures, 0 ignored ✓

### /review
**Task**: Review implementation
**Acceptance**: No Blocker findings ✓ (0B, 3I, 3S — I1/I2 fixed, I3 pre-existing)

### /arch
**Task**: Review sprint proposal ✓ (approved with design guidance)

### /repl
**Task**: No changes — REPL uses v1 prelude loading path

### /frontend, /typecheck, /backend, /platform, /stdlib, /examples, /docs, /port
**Task**: No work this sprint

## Waves

### Wave 1: Implementation + Review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Implement prelude auto-loading | done | load_dependencies extended, auto-prelude trigger, ~135 lines deleted |
| /review | Review implementation | done | 0B, 3I, 3S — I1 comment fixed, I2 stale doc fixed, I3 function length pre-existing |

### Wave 2: Verification
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Verify full test suite | done | 1533 passed, 11 pre-existing sketch_port, 0 ignored |

## Notes

- `load_dependencies` extended from `&[ImportSpec]` to `&ModuleStructure` — now iterates union of import+export module paths. This is the key enabler: the prelude's export targets auto-load during its recursive `compile_unit`.
- Auto-prelude trigger has 4 guards: not compiled, not current module, not on compile stack, lib_dirs non-empty. The compile-stack guard prevents re-entry when prelude's own export targets recurse through `compile_unit`.
- ~135 lines of duplicated prelude-loading logic deleted from two call sites.
- Review I3: `compile_unit_inner` is now ~241 lines (over 100-line guideline). Pre-existing issue worsened by ~30 lines. Extraction into helper function deferred — will be addressed naturally during Step 6 (collapse orchestration) or Step 9 (REPL migration).
- REPL v1 prelude loading path untouched.

## Outcome

### Delivered

**Step 5 — Prelude auto-loading:**
- Extended `load_dependencies` to accept `&ModuleStructure` and iterate union of import+export module paths
- New auto-prelude trigger in `compile_unit_inner` (stage 2b) — resolves prelude, compiles via recursive `compile_unit` + `codegen_and_execute`, inherits caller's `codegen_target`
- Deleted prelude pre-loading from `run_batch_v2` (~60 lines)
- Deleted `load_prelude_for_link` function entirely (~75 lines) and its call from `compile_for_link_v2`
- Updated stage numbering: 2a (extract) → 2b (auto-prelude) → 2c (load deps) → 2e (register imports/exports) → 2f (platform DLLs)

**Review fixes:**
- I1: Misleading "unique" comment fixed
- I2: Stale "compile mode" in doc comment fixed

### Deferred
- `compile_unit_inner` function length (241 lines > 100 guideline) — pre-existing, will shrink as Steps 6-9 restructure

### Findings
- The prelude's dependency chain works naturally through `load_dependencies` once export targets are included. No special prelude-specific logic needed beyond the auto-trigger.
- The compile-stack guard (checking if prelude is already being compiled) was essential — without it, prelude export targets that recurse through `compile_unit` would re-trigger prelude auto-loading.
