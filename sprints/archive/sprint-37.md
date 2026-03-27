# Sprint 37: Pipeline v3 Step 10 — Wire File Watcher to module_deps Cascade

**Status**: COMPLETE
**Ring**: — (structural)
**Goal**: Move the cascade recompilation logic from REPL into `CompilationSession` as a reusable `recompile_module_and_dependents` method, completing the file watcher integration with the v3 pipeline.

## Scope

### Step 10: Wire file watcher to recompile_module_and_dependents

Steps 8 (ModuleDependencyGraph) and 9 (REPL migration) already delivered most of Step 10's behavioral goals:
- `module_deps.dependents` provides the reverse dependency map (Step 8)
- `reload_single_module` uses `compile_unit` + `codegen_and_execute` (Step 9)
- `find_transitive_dependents` uses `module_deps.dependents` (Step 8)
- `reload_changed_modules` does cascade invalidation (existing)

What remains is structural: move the cascade logic from REPL-specific code into `CompilationSession` so it's reusable (e.g., by future batch-mode file watcher or IDE integration).

**Changes**:

1. **New method `recompile_module(&mut self, module: &ModuleFullPath) -> Result<(), CranelispError>`** on `CompilationSession`:
   - Resolve source file from `module_deps.file_to_module`
   - Read source
   - Clear old module state in typechecker
   - Call `compile_unit(Replace)` + `codegen_and_execute`
   - Register module aliases

2. **New method `recompile_module_and_dependents(&mut self, modules: &[ModuleFullPath]) -> Vec<(ModuleFullPath, Result<(), CranelispError>)>`** on `CompilationSession`:
   - Recompile each directly-changed module
   - Find transitive dependents via `module_deps.dependents`
   - Recompile each dependent in BFS order
   - Return per-module results

3. **Move `find_transitive_dependents`** from `repl/mod.rs` to `pipeline.rs` (method on `ModuleDependencyGraph`)

4. **Move `clear_module_state`** from `repl/mod.rs` to `CompilationSession` (or keep as a method on `TypeChecker`)

5. **Simplify `reload_changed_modules`** in repl/mod.rs to call `session.core.recompile_module_and_dependents(stale_modules)` and handle display

6. **Delete `reload_single_module`** from repl/mod.rs (absorbed into CompilationSession)

**Verification**: File watcher cascade works identically. All tests pass. `reload_single_module` deleted.

## FIXME Debt

No blocking FIXMEs found.

## Architecture Review

**Verdict**: Approved with refinements. Scope is appropriate — pure structural refactoring with no behavioral change.

### Method placement

The proposal to move cascade logic onto `CompilationSession` is correct. All state accessed by `clear_module_state` and `reload_single_module` lives on `CompilationSession` already (`tc`, `expander`, `module_deps`, `register_module_aliases`). The REPL-specific fields (`error_modules`, `pending_changes`) are only touched by `reload_changed_modules` (the display/orchestration layer), which stays on the REPL side. Clean split.

Specific placements:

1. **`find_transitive_dependents` -> method on `ModuleDependencyGraph`**. Correct. It only reads `dependents`. Pure graph traversal belongs on the graph.

2. **`clear_module_state` -> method on `CompilationSession`**. Correct. It touches `self.tc` and `self.expander` — both on `CompilationSession`. The note in the SPRINT.md about it accessing `ReplSession`-specific fields is wrong: the current implementation at line 1666 takes `&mut ReplSession` but only accesses `session.core.tc` and `session.core.expander`. No REPL-specific fields are touched. Move it wholesale.

3. **`recompile_module` and `recompile_module_and_dependents` on `CompilationSession`**. Correct. These compose `clear_module_state` + `compile_unit` + `codegen_and_execute` + `register_module_aliases` — all `CompilationSession` operations. The REPL caller reduces to: map file paths to module paths, call `recompile_module_and_dependents`, iterate results updating `error_modules` and writing display output.

### Replace vs Additive

**Use `Additive`, not `Replace`.** The current code is correct. Here is why:

- `reload_single_module` calls `clear_module_state` *before* `compile_unit`. This removes the old symbol table, traits, and macros, then inserts a fresh empty symbol table.
- After clearing, the module is effectively empty. `compile_unit` with `Additive` adds definitions to this empty table — which is exactly what `Replace` would do.
- Inside `compile_unit`, `Replace` is already converted to `Additive` before `tc.check()` (line 285). The only effect of `Replace` is as a signal — but here the caller has already done the clearing. Passing `Replace` would be misleading: it implies `compile_unit` handles the clearing, but it does not.
- `Replace` is appropriate for fresh module loads (prelude, dependencies) where `compile_unit` is the first compilation and no prior state exists. For recompilation, where the caller explicitly clears state, `Additive` is the correct signal.

Update the roadmap Step 10 text to say `Additive` (with caller-side `clear_module_state`), not `Replace`.

### Cache invalidation

The current `reload_single_module` does cache invalidation (lines 1648-1652). The proposed `recompile_module` method on `CompilationSession` should include this — the `CacheState` is on `object_worker` which is part of `CompilationSession`. The REPL caller should not need to manage cache hashes.

### Scope check

- **Single pipeline**: Maintained. This moves code closer to the shared pipeline, not away from it.
- **Carried debt**: None blocking. No FIXMEs deferred.
- **Test coverage**: No new behavior, so existing tests suffice. Acceptance = same test results.

### Waves

Single wave: all changes are in one skill (`/int`), no dependencies between items.

## Skill Plans

### /int
**Task**: Extract cascade recompilation into CompilationSession, simplify REPL watcher
**Design doc**: `design/arch/pipeline-v3-roadmap.md` Step 10
**Approach**: Follow Wave 1 sequence. Use `Additive` strategy with caller-side `clear_module_state`. Include cache invalidation in `recompile_module`.
**Acceptance**: `cargo test` passes, cascade logic on CompilationSession ✓

### /qa
**Task**: Verify test suite passes
**Acceptance**: 1533 passed, 11 pre-existing sketch_port failures ✓

### /review
**Task**: Review implementation — behavioral equivalence
**Acceptance**: 0B 0I 3S, all 5 functions verified equivalent ✓

### /arch
**Task**: Review proposal — confirm method placement, assess scope
**Acceptance**: Review written

### /repl, /frontend, /typecheck, /backend, /platform, /stdlib, /examples, /docs, /port
**Task**: No work this sprint

## Waves

**Wave 1** (single wave — `/int` only):
1. Move `find_transitive_dependents` to `ModuleDependencyGraph::transitive_dependents` method
2. Move `clear_module_state` to `CompilationSession::clear_module_state`
3. Add `CompilationSession::recompile_module` (clear + compile_unit(Additive) + codegen + aliases + cache)
4. Add `CompilationSession::recompile_module_and_dependents` (compose recompile_module + BFS cascade)
5. Simplify `reload_changed_modules` to call `session.core.recompile_module_and_dependents`, handle display + error_modules
6. Delete `reload_single_module`

## Notes

- This is a light structural refactoring. The behavioral change (file watcher using v3 pipeline) was delivered in Steps 8+9.
- ~~`clear_module_state` accesses `ReplSession`-specific fields~~ Incorrect — it only touches `session.core.tc` and `session.core.expander`. Moves to `CompilationSession` cleanly. (See Architecture Review.)
- `ModuleStrategy::Replace` vs `Additive`: **Use `Additive`** with caller-side `clear_module_state`. See Architecture Review for rationale.

## Outcome

### Delivered

**Step 10 — Wire file watcher to module_deps cascade:**
- `ModuleDependencyGraph::transitive_dependents()` — BFS over reverse map (moved from REPL)
- `ModuleDependencyGraph::file_for_module()` — reverse lookup helper
- `CompilationSession::clear_module_state()` — clear TC + expander for module (moved from REPL)
- `CompilationSession::recompile_module()` — resolve file, clear, compile_unit(Additive), codegen, aliases, cache
- `CompilationSession::recompile_module_and_dependents()` — recompile + BFS cascade + cache flush
- `reload_changed_modules` simplified to delegation + display
- Deleted `reload_single_module`, `find_transitive_dependents`, `clear_module_state` from REPL

### Deferred
- `file_for_module` linear scan → reverse index (S2, fine at current scale)
- Tombstone comments in repl/mod.rs (S3, remove in future cleanup)

### Findings
- Pure structural refactoring — no behavioral changes. /review verified all 5 functions are behaviorally equivalent to their predecessors.
- The cascade recompilation logic is now reusable beyond the REPL (batch file watcher, IDE integration).
