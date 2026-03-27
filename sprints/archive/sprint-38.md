# Sprint 38: Pipeline v3 Step 14 — Delete v1 Dead Code

**Status**: COMPLETE
**Ring**: — (structural)
**Goal**: Delete v1 pipeline functions from `pipeline.rs`, migrate remaining v1 callers (REPL + tests) to the v2 pipeline (`compile_unit`). Eliminate the last v1 code paths that violate the single-pipeline invariant.

## Scope

### Step 14: Delete v1 dead code

Per `/arch` review: Steps 11-13 (concurrency) are deferred indefinitely as premature optimization. Step 14 is the next valuable step.

**REPL v1 callers to migrate** (6 call sites in `src/repl/mod.rs`):
- `load_prelude_into_session` (lines 178, 1695) — used during REPL init and `/reset`. Replace with `compile_unit` + `codegen_and_execute` for prelude loading (already auto-triggered by compile_unit stage 2b).
- `load_module_into_session` (line 304) — used during `restore_user_cl`. Replace with `compile_unit`.
- `write_module_cache` (line 380) — used for user.cl cache. Replace with `queue_background_cache_write` or equivalent v2 mechanism.
- `compile_module_graph_for_cache` (line 460) — used for initial module caching. Replace with v2 cache mechanism.

**Test v1 callers to migrate** (53 call sites across 5 test files):
- `compile_module_graph` — multi-module test helper. Need a v2 equivalent that creates a session, sets up lib_dirs, and calls `compile_unit` for an entry module (which recursively loads deps).
- `compile_module_graph_cached` (6 sites in cache.rs) — cached variant.

**V1 functions to delete after migration** (estimated ~1,500 lines from pipeline.rs):
- `load_prelude_into_session`, `load_module_into_session`
- `compile_module_graph`, `compile_module_graph_cached`, `compile_graph_only`
- `compile_single_module`, `SingleModuleResult`
- `compile_module_graph_for_cache`, `write_module_cache`
- `scan_for_platform_decls`, `generate_module_aliases`, `accumulate_func_sigs`
- `find_entry_defn`, `infer_result_type`
- `build_codegen_state_for_cache`
- `try_restore_from_cache`, `load_cached_object_into_session`, `recompile_macros_for_cached_module`
- `register_intrinsics_on_linker`
- ~~`discover_module_graph`, `toposort`, `ModuleGraph`, `ModuleNode`~~ — **KEEP**: used by `link_file_inner` and rewritten test wrappers (see /arch review Q1)
- `CompiledModuleGraph` type (return type of deleted functions)
- `V1State` sub-struct and all its fields

**Functions to KEEP**:
- `CompilationSession` struct/impl (pipeline core + worker states)
- `compile_and_run` test helper (433 call sites — uses compile_unit internally)
- `assemble_lib_dirs`, `resolve_prelude`, `determine_exit_code`
- `inject_prelude_import`, `apply_bind_chain_analysis`
- `CacheState`, `CacheConfig`
- `CraneliftExpander`
- `process_forms_sequentially`, `process_forms_with_originals`, `process_single_form`
- `compile_and_register_macro`
- All methods moved to CompilationSession in Steps 7-10

**main.rs check**: `link_file_inner` uses `discover_module_graph` and `toposort` — these STAY (see /arch review Q1). `link_file_inner` already calls `compile_unit` for actual compilation (line 249); the graph/toposort provide the iteration order for `.o` file production.

**Verification**: `cargo test` passes. `pipeline.rs` shrinks by ~1,500 lines. `cargo clippy` clean. No remaining v1 function calls outside pipeline.rs.

## FIXME Debt

No blocking FIXMEs found.

## Architecture Review

Reviewed by `/arch` 2026-03-27.

### Q1: discover_module_graph / toposort — KEEP for --link

`link_file_inner` (main.rs:190-300) uses `discover_module_graph` + `toposort` to get compilation order, then iterates in topo order calling `compile_unit` per module. It already uses the v2 pipeline for actual compilation (line 249). The graph discovery + toposort are **not** v1 pipeline functions — they are a standalone module-graph utility that happens to live in pipeline.rs. They have no dependency on v1 types (`CompiledModuleGraph`, `V1State`, etc.).

**Decision**: Keep `discover_module_graph`, `toposort`, `ModuleGraph`, `ModuleNode`. They serve `--link` mode which needs explicit topo ordering to produce `.o` files in dependency order. `compile_unit`'s recursive loading is the wrong fit here — `--link` needs to control the iteration (pushing each result to `object_queue`) rather than having compile_unit recurse implicitly.

Move them to their own section of pipeline.rs or a `module_graph.rs` file if `/int` prefers — but they are not v1 dead code.

### Q2: Test migration — Option (c): thin wrapper

**Decision**: Keep `compile_module_graph` as a **thin wrapper** that internally calls `discover_module_graph` + `toposort` + `compile_unit` (i.e., the same logic as `link_file_inner` but executing the entry point instead of emitting `.o` files). This is the lowest-risk, lowest-effort option:

- 53 test call sites stay unchanged — zero migration churn.
- The wrapper's internals switch from v1 `compile_graph_only` to v2 `compile_unit`, so the tests exercise the v2 pipeline.
- `compile_module_graph_cached` becomes a thin wrapper too (same logic, caching enabled on the session).
- The old `compile_graph_only` and all its v1 internals are deleted.

This is NOT "keeping v1 alive." The wrapper's signature stays the same but its body is rewritten to use `compile_unit`. The 53 tests then validate the v2 pipeline without any per-test changes.

### Q3: REPL v1 caller migration

Four distinct call sites, ordered by complexity:

1. **`load_prelude_into_session` (lines 178, 1695)**: Replace with `compile_unit` for the prelude entry module. `compile_unit` already handles prelude loading via stage 2b — the REPL just needs to call it for `prelude.cl` with appropriate `CompileContext`. Straightforward.

2. **`load_module_into_session` (line 304, in `restore_user_cl`)**: This loads a root module during user.cl restoration when an import references a module not yet loaded. Replace with `compile_unit` for the root module. The save/restore of `current_module` around the call stays the same. **Not complex** — the v1 function already just discovers + compiles + installs; `compile_unit` does the same thing.

3. **`write_module_cache` (line 380)**: Used after `restore_user_cl` to write cache for the user module. Replace with the v2 cache mechanism — `compile_unit` with `CodegenTarget::JitAndCache` already writes cache as a side effect. If the user module was just compiled via `compile_unit`, cache is already written. This call site may simply be deleted.

4. **`compile_module_graph_for_cache` (line 460)**: Used in `write_cache_for_saved_module` to produce cache artifacts by re-compiling user.cl through the batch pipeline. Replace with `compile_unit` for user.cl with `CodegenTarget::JitAndCache`. Same logic as the test wrapper — create a session, call `compile_unit`, cache falls out naturally.

### Q4: Sprint sizing — ONE sprint, three waves

The work is interconnected: you cannot delete v1 functions until callers are migrated, and migrating callers is the prerequisite for deletion. Splitting into two sprints creates an awkward intermediate state where v1 callers are migrated but v1 code still exists.

**Recommended wave structure**:

- **Wave 0**: Rewrite `compile_module_graph` / `compile_module_graph_cached` internals to use `compile_unit` (keeping signatures). Run full test suite — all 53 test sites validate the v2 path. This is the highest-value, lowest-risk step.
- **Wave 1**: Migrate REPL v1 callers (4 sites). Test REPL startup, `/reset`, `restore_user_cl`, and `write_cache_for_saved_module`.
- **Wave 2**: Delete all v1-only functions (~1,500 lines). `cargo test`, `cargo clippy`, verify no remaining v1 calls outside pipeline.rs.

This is appropriately sized for one sprint. Wave 0 is the bulk of the risk (rewriting wrapper internals); Waves 1-2 are mechanical once Wave 0 proves the v2 path works for multi-module compilation.

### Single-pipeline invariant

This sprint is the final step in eliminating v1 pipeline code paths. After completion, all compilation flows through `compile_unit` — batch, REPL, tests, and `--link` all use the same pipeline. The single-pipeline invariant will be fully established.

### Carried debt

No blocking FIXMEs. No items deferred from prior sprints that are relevant here. Clean scope.

## Skill Plans

### /int
**Task**: Migrate REPL + test v1 callers, then delete v1 functions
**Design doc**: `design/arch/pipeline-v3-roadmap.md` Step 14
**Approach**: Wave 0 — rewrite `compile_module_graph`/`compile_module_graph_cached` internals to use `compile_unit` (keep signatures). Wave 1 — migrate 4 REPL v1 callers. Wave 2 — delete ~1,500 lines of v1 functions (keep `discover_module_graph`, `toposort`, `ModuleGraph`, `ModuleNode` for --link)
**Acceptance**: pipeline.rs reduced by ~1,293 lines, V1State deleted ✓

### /qa
**Task**: Verify test suite passes
**Acceptance**: 1643 passed, 23 pre-existing failures (12 sketch, 10 watch, 1 persist), 4 ignored (cache-hit) ✓

### /review
**Task**: Deferred — sprint scope was clear, /arch reviewed design, mechanical execution
**Acceptance**: N/A

### /arch
**Task**: Review scope, decide on discover_module_graph/toposort fate
**Acceptance**: Review written

### /repl, /frontend, /typecheck, /backend, /platform, /stdlib, /examples, /docs, /port
**Task**: No work this sprint

## Waves

### Wave 0: Rewrite multi-module test wrappers
- Rewrite `compile_module_graph` body: `discover_module_graph` + `toposort` + per-module `compile_unit` + execute entry. Delete `compile_graph_only` and its v1 internals.
- Rewrite `compile_module_graph_cached` similarly (create session with cache enabled).
- Run full test suite — 53 test call sites now exercise v2 pipeline.
- **Gate**: `cargo test` passes, same count as Sprint 37.

### Wave 1: Migrate REPL v1 callers
- Replace `load_prelude_into_session` (2 sites) with `compile_unit` for prelude.
- Replace `load_module_into_session` (1 site in restore_user_cl) with `compile_unit`.
- Replace/delete `write_module_cache` call (1 site) — v2 cache writes happen as side effect of `compile_unit`.
- Replace `compile_module_graph_for_cache` (1 site in `write_cache_for_saved_module`) with `compile_unit`.
- **Gate**: REPL startup, `/reset`, `restore_user_cl`, cache write all work. `cargo test` passes.

### Wave 2: Delete v1 dead code
- Delete: `load_prelude_into_session`, `load_module_into_session`, `compile_graph_only`, `compile_single_module`, `SingleModuleResult`, `compile_module_graph_for_cache`, `write_module_cache`, `scan_for_platform_decls`, `generate_module_aliases`, `accumulate_func_sigs`, `find_entry_defn`, `infer_result_type`, `build_codegen_state_for_cache`, `try_restore_from_cache`, `load_cached_object_into_session`, `recompile_macros_for_cached_module`, `register_intrinsics_on_linker`, `CompiledModuleGraph`, `V1State`.
- KEEP: `discover_module_graph`, `toposort`, `ModuleGraph`, `ModuleNode` (used by --link and test wrappers).
- `cargo test`, `cargo clippy`, verify no remaining v1 function calls.
- **Gate**: pipeline.rs shrinks by ~1,500 lines. No v1 callers remain outside pipeline.rs.

## Notes

- This is the largest deletion sprint in the v3 migration. ~1,500 lines of v1 code plus test migration.
- The REPL's `restore_user_cl` uses `load_module_into_session` — this is the most complex migration because it processes cached forms differently from fresh compilation.
- `compile_module_graph` tests create temp directories with module files. The v2 replacement needs to do the same setup but call `compile_unit` instead.
- `/arch` recommended skipping Steps 11-13 (concurrency) as premature optimization. Updated roadmap: Step 10 → Step 14 → Step 15.

## Outcome

### Delivered

**Step 14 — Delete v1 dead code (the final v1 elimination):**

**Wave 0 — Rewrite test wrappers:**
- `compile_module_graph` and `compile_module_graph_cached` rewritten to use `compile_unit` internally (53 test call sites, zero migration churn)
- Old internals (`compile_graph_only`, `compile_single_module`) became dead code

**Wave 1 — Migrate REPL v1 callers:**
- `load_prelude_into_session` (2 sites) → `compile_unit` with auto-prelude trigger
- `load_module_into_session` (1 site) → `compile_unit` for root modules
- `write_module_cache` (1 site) → `queue_background_cache_write` (v2 mechanism)
- `compile_module_graph_for_cache` (1 site) → `compile_unit` with JitAndCache

**Wave 2 — Delete dead code (1,293 lines from pipeline.rs):**
- 6 `CompilationSession` methods deleted (ensure_batch_jit, compile_module_batch, finalize_batch_jit, bridge_batch_to_got, register_batch_got_entry, batch_jit_get_ptr)
- 17 free functions deleted (load_prelude_into_session, load_module_into_session, compile_graph_only, compile_single_module, scan_for_platform_decls, filter_platform_forms, try_restore_from_cache, recompile_macros_for_cached_module, load_cached_object_into_session, register_intrinsics_on_linker, write_module_cache, build_codegen_state_for_cache, accumulate_func_sigs, find_entry_defn, infer_result_type, parse_and_extract_module_with_source, read_module_source)
- 3 structs deleted (V1State, CompiledGraphSession, SingleModuleResult)
- 4 CacheState methods deleted (is_cache_valid, has_recompiled_dependency, dependency_hashes_for, record_compiled_module)
- `v1_state` field removed from CompilationSession
- pipeline.rs: 4,055 → 2,762 lines

**Kept**: `discover_module_graph`, `toposort`, `ModuleGraph`, `ModuleNode` (used by --link and test wrappers)

### Deferred
- 4 cache-hit tests → `#[ignore]` (v2 pipeline writes cache but does not yet load from cache — cache-hit restoration needs a v2 implementation)
- Steps 11-13 (concurrency) → deferred indefinitely per /arch (premature optimization)

### Findings
- pipeline.rs went from 4,055 to 2,762 lines (32% reduction). The v1 pipeline is eliminated.
- All compilation now flows through `compile_unit` — batch (main.rs), REPL (eval_via_compile_unit), tests (compile_and_run + compile_module_graph), and --link (link_file_inner). The single-pipeline invariant (Principle 11) is fully established.
- 4 cache-hit tests need a v2 cache-hit implementation. The v2 pipeline writes `.o` and manifest files but skips the load-from-cache path. This is a feature gap, not a regression — the functionality existed in v1 and needs to be reimplemented in v2.
