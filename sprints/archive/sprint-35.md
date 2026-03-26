# Sprint 35: Pipeline v3 Step 8 — ModuleDependencyGraph

**Status**: COMPLETE
**Ring**: — (structural)
**Goal**: Populate a module dependency graph during `compile_unit` stage 2, preparing for file watcher cascade (Step 10). Move `file_to_module` and `module_dependencies` from `ReplSession` to `CompilationSession`.

## Scope

One pipeline v3 migration step:

### Step 8: Add ModuleDependencyGraph

Per `design/arch/pipeline-v3-roadmap.md` Step 8:

- Define `ModuleDependencyGraph { imports, dependents, file_to_module }` as a new struct
- Add it as a field on `CompilationSession` (pipeline core, since it's populated during stage 2)
- `compile_unit` stage 2c (`load_dependencies`) registers import edges in the graph before loading each dependency. This happens even if later stages fail.
- Move `file_to_module` and `module_dependencies` from `ReplSession` fields to `CompilationSession.module_deps`
- REPL code that reads `session.file_to_module` / `session.module_dependencies` changes to `session.core.module_deps.*`

**Key design points**:
- `imports: HashMap<ModuleFullPath, Vec<ModuleFullPath>>` — forward edges (module → its dependencies)
- `dependents: HashMap<ModuleFullPath, Vec<ModuleFullPath>>` — reverse edges (module → modules that depend on it)
- `file_to_module: HashMap<PathBuf, ModuleFullPath>` — filesystem path → module name mapping
- The `dependents` map is the reverse of `imports` — populated automatically when import edges are registered
- Registration happens in `load_dependencies` when it resolves a module file and before the recursive `compile_unit` call

**Verification**: `cargo test` passes. Dependency graph populated but not yet consumed by anything new (Step 10 will wire the file watcher to it).

## FIXME Debt

No blocking FIXMEs found.

## Architecture Review

**Verdict: Approved with guidance.**

The proposal is architecturally sound. `ModuleDependencyGraph` belongs on `CompilationSession` — it is pipeline-core data populated during stage 2 and consumed by the file watcher (Step 10) and future parallel compilation (Step 13). Placing it here maintains the single-pipeline invariant: batch, REPL, and module-loading all populate the same graph through the same `compile_unit` path.

### Q1: Pipeline core or separate field?

Pipeline core. The graph is populated during `compile_unit` stage 2 (which only has access to `CompilationSession`), and consumed by callers (REPL file watcher, future `recompile_module_and_dependents`). This matches the existing pattern where `compile_stack` and `tc` are pipeline-core fields that `compile_unit` reads and writes. Add `module_deps: ModuleDependencyGraph` alongside `compile_stack` and `lib_dirs`.

### Q2: Keep `build_file_to_module_map` for `/reload`?

**No.** After this sprint, `file_to_module` is populated incrementally as modules compile. The `/reload` (`/reset`) handler already recompiles the prelude from source (lines 2196-2212 of `repl/mod.rs`), which triggers recursive `compile_unit` calls that will populate the graph. The upfront filesystem scan (`build_file_to_module_map` and `build_module_dependency_map`) becomes redundant. Remove the calls at lines 2216-2219 of `repl/mod.rs` and replace with nothing — the graph will already be populated by the prelude compilation above. Same for the initial population at lines 204-209. Mark the two `build_*` functions as candidates for deletion in Step 14 (v1 dead code cleanup) — they may still have v1 callers.

### Q3: Where exactly to register edges?

In `load_dependencies` (pipeline_v2.rs line 432), register edges **after resolving the file path but before the recursive `compile_unit` call**. Specifically, between lines 464 and 466 (after `read_to_string` succeeds, before the `CompileContext` is built). This is the point where you know both:
- The parent module (from `structure.path`)
- The dependency module (`dep_module`)
- The resolved file path (`dep_source_path`)

Register all three facts at once:
```
session.module_deps.register_edge(&structure.path, dep_module);
session.module_deps.register_file(dep_source_path.canonicalize()?, dep_module.clone());
```

Registering before the recursive call ensures the graph is populated even if the dependency fails to compile (the sprint proposal correctly identifies this requirement). Do NOT register inside `compile_unit_inner` — `load_dependencies` is the right place because it owns the dependency resolution logic.

Also register `file_to_module` for the **current** module being compiled. This should happen in `compile_unit_inner` after `extract_module_declarations` succeeds (line 165), since `structure.file_path` is known at that point. But only if the module was loaded from a file (not from inline source in tests). Check: if `resolve_module_path` was used to find the file, register the mapping. A simple approach: have `compile_unit` (the outer function) register the file mapping when `ctx.module` has a resolvable file path.

### Additional guidance

1. **Struct definition**: Define `ModuleDependencyGraph` in `pipeline.rs` (near `CompilationSession`) or in a new `src/module_deps.rs`. It is pipeline-internal, not a boundary type — it does NOT belong in `cranelisp-types`. It should have `pub(crate)` visibility.

2. **Prelude loading edges**: The prelude auto-load at stage 2b (lines 173-199 of `compile_unit_inner`) also creates dependency edges. Register `structure.path → prelude` when the prelude is auto-loaded. This can be done right after line 198 (after `codegen_and_execute` for the prelude succeeds).

3. **Deduplication**: `register_edge` should deduplicate — calling it twice with the same `(parent, dep)` pair should not create duplicate entries. Use a `HashSet` internally or check before pushing.

4. **`clear()` method**: `ModuleDependencyGraph` needs a `clear()` method for `/reset`. The REPL's reset handler (line 2162) currently clears `file_to_module` — after migration, it should call `session.core.module_deps.clear()`.

5. **Export dependencies**: `load_dependencies` already iterates both `import_specs` and `export_specs` (line 442). Both should produce edges in the graph. The `dependents` reverse map will correctly reflect that a re-exporting module depends on its export source.

6. **Single wave**: This is a single-skill mechanical migration. One wave is sufficient.

## Skill Plans

### /int
**Task**: Define ModuleDependencyGraph, add to CompilationSession, populate in compile_unit, migrate REPL fields
**Design doc**: `design/arch/pipeline-v3-roadmap.md` Step 8
**Approach**: Per /arch: define ModuleDependencyGraph in pipeline.rs (pub(crate)), add to CompilationSession, register edges in load_dependencies after file resolution before recursive compile_unit, register file_to_module for current module in compile_unit_inner, register prelude edges after stage 2b auto-load, migrate REPL file_to_module/module_dependencies to module_deps, add clear() for /reset
**Acceptance**: `cargo test` passes, dependency graph populated during compilation ✓

### /qa
**Task**: Verify test suite passes
**Acceptance**: 1533 passed, 11 pre-existing sketch_port failures ✓

### /review
**Task**: Review implementation
**Acceptance**: 2B (dead code — fixed), 1I, 2S ✓

### /arch
**Task**: Review proposal
**Acceptance**: Review written

### /repl, /frontend, /typecheck, /backend, /platform, /stdlib, /examples, /docs, /port
**Task**: No work this sprint

## Waves

### Wave 1: Implementation + Review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Define ModuleDependencyGraph, populate in compile_unit, migrate REPL | done | Graph populated incrementally, REPL fields migrated |
| /review | Review implementation | done | 2B fixed (dead code deleted), 1I (pub fields), 2S |

### Wave 2: Verification
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Verify full test suite | done | 1533 passed, 11 pre-existing sketch_port |

## Notes

- Graph populated incrementally during compile_unit: file_to_module in compile_unit_inner (stage 2a), prelude edge after stage 2b, import/export edges in load_dependencies (before recursive compile_unit).
- REPL's `file_to_module` and `module_dependencies` fields removed. All access migrated to `session.core.module_deps.*`.
- `build_file_to_module_map` and `build_module_dependency_map` deleted (review B1/B2) — no callers after REPL migration.
- `find_transitive_dependents` simplified: now uses pre-built reverse map (`dependents`) for O(1) lookup per step, replacing O(n) scan of forward map.
- Review I1: `ModuleDependencyGraph` fields are all `pub` — could be narrowed with accessor methods. Deferred.

## Outcome

### Delivered

**Step 8 — ModuleDependencyGraph:**
- `ModuleDependencyGraph` struct in pipeline.rs: `imports` (forward), `dependents` (reverse), `file_to_module` — all using `HashSet` for dedup
- Methods: `register_edge()`, `register_file()`, `clear()`, `new()`
- Added as `module_deps` field on `CompilationSession` (pipeline core)
- Edge registration in 3 locations: compile_unit_inner (file mapping + prelude edge), load_dependencies (import/export edges + file mapping)
- Migrated REPL from own fields to `module_deps`: removed `file_to_module` and `module_dependencies` from ReplSession, updated all access sites
- Simplified `find_transitive_dependents` to use reverse map directly
- Deleted dead `build_file_to_module_map` and `build_module_dependency_map` functions (review B1/B2)

### Deferred
- `ModuleDependencyGraph` field visibility narrowing (review I1)

### Findings
- Incremental population during compile_unit is architecturally cleaner than the old upfront filesystem scan — it's automatically correct for any module loaded through the pipeline, regardless of how it was discovered.
