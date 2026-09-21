# Cache-Hit Loading + File Watcher Migration — Steps 13+14 Design

## 0. Restoration parity — a restored world is not a second kind of world

A cache-restored module must hold every relationship the freshly built module
holds. Each restore step is the **same call** the fresh path makes, at the
equivalent lifecycle point (Principle 11); a cache-only parallel path must not be
added. `src/process_form/cache_restore.rs::try_cache_hit_load` is the one
composition, returning `Result<bool, CranelispError>` so an ordinary miss
(`false`, fall through to a fresh build) stays distinct from malformed metadata
or conflicting live state (`Err`).

| Relationship | Fresh path | Restore rule |
|---|---|---|
| Declared children | `dependency.rs::enrol_declared_submodule` after the parent's cluster commits | The same registrar, over the persisted `submodules`, after the parent table installs. Private and public children take one path; an existing child is an idempotent no-op; parent metadata installs first so a child's `super` import sees it. |
| Trait impls the module wrote | The typecheck producer appends `WrittenTraitImpl` records (`design/arch/trait-impl-cache-carrier.md`) | Preload each foreign trait home, then after the writer table installs re-enrol every record into its home through the types-owned `enrol_written_trait_impl`. `Enrolled` and `AlreadyEnrolled` both succeed; a divergence is an error, never a silent pick. An empty record vector is trusted as written: no `serde(default)` read, rescan of the trait home, or reconstruction from mangled method names. |
| Module aliases | Session `ModuleAliases`, keyed by `cranelisp_types::module_alias_key(owner, name)` (`design/arch/module-alias-scoped-lookup.md`) | Rebuilt from the persisted `imports`/`submodules` by the same writers with the same key mint. The map is unserialized session state, so aliases add no cache field. Two import-alias writers still spell the key through an int-private copy of the mint (`int.md` §16.0). |
| Monomorphic instances | Ordinary `Concrete` entries in the demanding module's table, each carrying its `minted_from` link | Restored with that table; no separate step. |
| Platform functions | Platform load wraps the DLL's GOT (`design/arch/platform-interface.md` §6.4) | The persisted platform declarations re-run the same load; a load failure is a cache miss. |

Lifecycle legality of a decoded table is the types crate's to define. At
present the backend decoder (`crates/cranelisp-backend/src/cache/serialize.rs`)
maps only `LifecycleError::InstanceKeyMismatch` from `validate_lifecycle` to
`CacheStale`, and the int restore seams add no further call. Whether every other
lifecycle refusal is also treated as a stale cache is therefore **asserted, not
measured** (`int.md` §16.0); the falsifier is a decoded table with any other
invalid lifecycle state that restores instead of regenerating. The restore path
must not grow an int-private copy of a lifecycle rule to close that gap.

## 1. Overview

Step 13 adds cache-hit loading to the v4 scheduler-driven pipeline: when `handle_import` discovers a dependency, it checks the disk cache before falling through to full typecheck. Cache-hit modules enter the scheduler at `TypecheckDone` via `register_module_cached`, skipping all parsing and typechecking. In-memory code is loaded on demand via Linker when a worker needs callable symbols.

Step 14 migrates the REPL file watcher from the v3 `CompilationSession::recompile_module_and_dependents` path to the v4 scheduler. Changed modules are re-registered with the scheduler; cascade invalidation walks `tc.modules` for reverse dependencies.

Both steps use existing scheduler infrastructure (`register_module_cached`, `notify_inmem_codegen_batch_complete`) designed for these exact use cases.

## 2. Step 13: Cache-Hit Loading

### 2.1 Dependency Discovery Cache Check

The insertion point is `handle_import` in `worker.rs`. Currently, when a module is not yet loaded in the TypeChecker, `handle_import` resolves the file, reads source, parses it, and unconditionally calls `scheduler.register_module()`. The cache check inserts between file resolution and parsing:

```
handle_import(ctx, module, specs):
  for spec in specs:
    dep = spec.module_path
    if tc.has_module(dep):      # already loaded
      tc.register_imports(spec)
      continue

    dep_file = resolve_module_file(dep)

    # --- NEW: cache check ---
    if try_cache_hit_load(ctx, dep, &dep_file):
      tc.register_imports(spec)
      continue
    # --- END cache check ---

    source = read(dep_file)
    dep_sexps = parse(source)
    scheduler.register_module(dep, delays_other=true)
    scheduler.block_for_typecheck(module, dep, "*")
    return Block { dep_module, dep_sexps }
```

The `try_cache_hit_load` function returns `Result<bool, CranelispError>` so an
ordinary cache miss remains distinct from conflicting live state:

1. **Check cache validity.** Read source, compute SHA-256. Check against the cache manifest. If invalid (hash mismatch or no manifest entry), return false.
2. **Load metadata.** Call `cache::try_load_cached_module(cache_dir, dep)` to read `.meta.json`. If missing or malformed, return false.
3. **Check .o exists.** If `cached.has_object` is false, return false.
4. **Restore type info.** Call `tc.restore_cached_module(symbol_table)` and `tc.restore_cached_impls(mangled_names)`. These must work with the DashMap `&self` API (see section 2.5).
5. **Register with scheduler.** Extract symbol names from the symbol table, call `scheduler.register_module_cached(dep, symbols)`. The module enters `TypecheckDone` with `object_done = true`, `inmem_done = false`.
6. **Wire GOT slots.** Call `pre_register_got_slots` for the cached module's symbols so GOT slot indices are allocated. Do NOT load code yet — that is deferred to on-demand Linker loading (section 2.2).
7. **Record cache hit.** Store the source hash in the cache state so downstream modules can validate their dep hashes.
8. **Return `Ok(true)`.** The caller registers the import and continues without
   blocking. A validity/staleness miss is `Ok(false)`; a divergent live
   publication is `Err`, never silently downgraded to a miss.

After a successful cache hit, `tc.has_module(dep)` returns true, so subsequent import specs referencing the same module skip to the fast path.

### 2.2 On-Demand Linker Loading for Cached Modules

When a worker needs callable code from a cached module (either priority codegen for macro deps, or background JIT codegen sweep), it loads the entire `.o` file via Linker in one operation.

Detection: when `codegen_module_symbols` or priority codegen encounters a symbol from a module that was loaded from cache, the module's `object_done` flag is true but `inmem_done` is false, and no JIT compilation has been performed. The worker detects this by checking whether the module was registered via `register_module_cached` (tracked by a `cached_modules: HashSet<ModuleFullPath>` on the session — see section 3).

Loading path:

1. Read the `.o` file from the cache directory.
2. Create a `Linker` instance. Register all known external symbols (intrinsics, platform functions, previously-compiled code pointers from `def_codegen`).
3. Call `linker.load_object()` to map the `.o` into executable memory and resolve relocations.
4. Extract function name to code pointer mappings.
5. Wire each code pointer into the GOT via `shared_codegen.got_table.store_slot()`.
6. Update `shared_codegen.def_codegen` entries with code pointers.
7. Store the `Linker` in `worker_jit.cache_linkers` (drained to `shared_codegen.kept_linkers` at module completion) — the Linker must stay alive because its `code_regions` hold mmap'd executable memory.
8. Notify the scheduler: `scheduler.notify_inmem_codegen_batch_complete(module, symbols)`.

This batch load is O(1) per module regardless of symbol count (one mmap + relocation pass), compared to O(n) individual JIT compilations.

### 2.3 Priority Codegen for Cached Macro Dependencies

When a module's typecheck blocks on a macro whose dependencies include symbols from a cached module, the priority codegen queue receives entries for those symbols. The priority worker handling a `BlockingJitCodegen` item checks whether the module is in `cached_modules`. If so, instead of JIT-compiling the single symbol, it loads the entire `.o` via Linker (section 2.2). All symbols in the module become callable at once, satisfying not just the immediate dependency but potentially unblocking other entries in the priority queue.

After loading, the worker calls `notify_priority_codegen_complete` for each loaded symbol that has a priority queue entry. The resolution cascade (section 4.3 of `concurrent-pipeline.md`) handles unblocking.

### 2.4 Cache Invalidation

Cache invalidation is source-hash based:

- If the source file has changed (hash mismatch), `try_cache_hit_load` returns false and the module falls through to full typecheck.
- If the `.meta.json` or `.o` file is missing or corrupt, the cache check returns false.
- Dependency hash checking is deferred — the current implementation uses source hash only (matching the v3 approach in `pipeline.rs:499`).

No special invalidation logic is needed for the scheduler path. Invalid cache simply means the module is registered via `register_module` instead of `register_module_cached`.

### 2.5 TypeChecker Cache Restoration with DashMap

Sprint 47 migrated the TypeChecker to DashMap. The cache restoration methods (`restore_cached_module`, `restore_cached_impls`) were originally `&mut self`. They must work with `&self` for concurrent access:

- `restore_cached_module(symbol_table)`: inserts entries into `tc.modules` (a `DashMap<ModuleFullPath, CompiledModule>`). This is a single DashMap `insert` — safe with `&self`.
- `restore_cached_impls(mangled_names)`: registers trait impl lookups. Must use the `&self` API added in Sprint 47.

Both methods are called from the priority worker thread during `handle_import`. Other workers may be reading from different modules' symbol tables concurrently — this is safe because DashMap uses per-shard locking. The restored module has its own shard; no other worker writes to it.

**Verification**: `restore_cached_module` and `restore_cached_impls` must be tested with concurrent reads from other modules (Sprint 48 Wave 3 test scope).

## 3. Data Structures

### 3.1 New Fields on SharedCodegenState

```rust
// No new fields needed. The existing kept_linkers Mutex<Vec<Linker>>
// handles Linker lifetime (T-5 resolution).
```

### 3.2 New Fields on CompilerSession / SharedState

```rust
/// Set of modules loaded from cache (vs. compiled from source).
/// Used by workers to detect cache-hit modules for Linker fast path.
/// Populated by try_cache_hit_load, read by workers during codegen.
pub cached_modules: Mutex<HashSet<ModuleFullPath>>,

/// File path to module path mapping. Populated during handle_import
/// when modules are first discovered. Used by the file watcher to
/// identify which module changed. (T-2 resolution)
pub file_to_module: Mutex<HashMap<PathBuf, ModuleFullPath>>,
```

### 3.3 Cache Validity State (T-4 Resolution)

The v3 path uses `session.object_worker.cache_state` (`CacheState` with manifest data) for cache validity checking. The v4 path needs equivalent functionality accessible to workers.

Place cache state on `SharedState`:

```rust
/// Cache validity state. Holds the manifest, cache directory, and
/// source hash records. Behind Mutex because workers update it
/// (record_cache_hit) during handle_import.
pub cache_state: Mutex<Option<CacheState>>,
```

Workers lock `cache_state` briefly during `try_cache_hit_load`:
1. Lock, read `cache_dir` and check `is_cache_valid`, unlock.
2. Load metadata from disk (no lock held).
3. Lock, call `record_cache_hit`, unlock.

Contention is low: cache checks happen once per module during dependency discovery. The lock is held for hash comparison and map insertion only, not during disk I/O.

### 3.4 Linker Ownership (T-5 Resolution)

Linkers from cache-hit loads must outlive the worker's current task. The existing `WorkerJitState.cache_linkers: Vec<Linker>` already handles this:

1. Worker loads `.o` via Linker.
2. Worker stores Linker in `worker_jit.cache_linkers`.
3. At module completion, `drain_to_shared()` moves it to `shared_codegen.kept_linkers: Mutex<Vec<Linker>>`.
4. `kept_linkers` lives on `SharedCodegenState`, which lives on `CompilerSession`, which lives for the session's lifetime.

No new data structures needed — the worker-local/shared split already
anticipates this use case.

## 4. Step 14: File Watcher Migration

### 4.1 Current v3 Watcher Path

```
poll_and_reload(session):
  paths = watcher.poll_changes()
  session.pending_changes.extend(paths)
  if pending_changes not empty:
    reload_changed_modules(session)

reload_changed_modules(session):
  for path in pending:
    module = session.core.module_deps.file_to_module[path]  # v3 mapping
  session.core.recompile_module_and_dependents(modules)     # v3 path
```

### 4.2 Target v4 Watcher Path

```
poll_and_reload(session):
  paths = watcher.poll_changes()
  for path in paths:
    module = session.file_to_module[path]           # v4 mapping (T-2)
    scheduler.re_register_module(module)            # T-1: scheduler re-registration
    cascade_dependents(session, module)             # T-3: TC-based cascade
```

### 4.3 Re-Registration Strategy (T-1 Resolution)

The scheduler's `register_module` is idempotent — it skips modules already registered. For file watcher re-registration, we need to reset a module's state and re-process it. Add a new method:

```rust
impl CompileScheduler {
    /// Re-register a module after its source file has changed.
    ///
    /// Clears the module's scheduler state and re-inserts it at
    /// TypecheckFirst for priority processing. Only modules in
    /// TypecheckDone or Complete may be re-registered — modules
    /// currently being typechecked (TypecheckWorking) are skipped
    /// (the watcher will catch the change on the next poll).
    ///
    /// Returns true if the module was re-registered, false if skipped.
    pub fn re_register_module(&self, module: &ModuleFullPath) -> bool;
}
```

Implementation:

1. Lock scheduler state.
2. Check current pool. If `TypecheckWorking` or `TypecheckBlocked`, return false — a worker is mid-typecheck. The watcher's next poll will catch this file again (content hash will still differ).
3. If `TypecheckFirst` or `TypecheckNext`, the module hasn't been claimed yet — remove from its queue and re-insert (effectively a no-op, but reset its ModuleState).
4. If `TypecheckDone`, `Complete`, or `Failed`:
   - Remove from `typecheck_done` deque if present.
   - Reset `ModuleState`: clear `inmem_done`, `object_done`, `jit_reserved`, `error`, `resume_from_form`. Keep `waiters` (other modules may still be waiting).
   - Set pool to `TypecheckFirst` (re-registration implies urgency — something depends on it, namely the user at the REPL).
   - Push to `typecheck_first` deque.
5. Wake priority workers.

**Race condition (T-1)**: The main concern is a worker being mid-typecheck when a file change arrives. The resolution is simple: skip the re-registration. The watcher polls before each REPL prompt. If the file was being typechecked during the previous poll, it will be in `TypecheckDone` or `Complete` by the next poll, and re-registration will succeed. The user sees a one-prompt delay at worst.

### 4.4 file_to_module Mapping (T-2 Resolution)

The v3 path uses `session.core.module_deps.file_to_module`. For v4, add `file_to_module: Mutex<HashMap<PathBuf, ModuleFullPath>>` on `SharedState` (section 3.2).

Population: in `handle_import`, after resolving the file path:

```rust
// After dep_file = resolve_module_file(dep, lib_dirs):
if let Ok(canonical) = dep_file.canonicalize() {
    session.file_to_module.lock().insert(canonical, dep.clone());
}
```

This is populated incrementally as modules are discovered, matching the v3 `ModuleDependencyGraph.register_file` pattern.

The file watcher also needs to register files it watches. In `try_cache_hit_load`, the same mapping is populated after resolving the file path.

### 4.5 Cascade Strategy for Dependents (T-3 Resolution)

Dependency edges are not held as an authored reverse index: they are implicit in the
modules' import specs, and the reverse direction is derived on demand.

Walk `tc.modules` to find dependents:

```rust
fn find_dependents(
    tc: &TypeChecker,
    changed: &ModuleFullPath,
) -> Vec<ModuleFullPath> {
    let mut dependents = Vec::new();
    // tc.modules is a DashMap — iterate with concurrent reads.
    for entry in tc.module_iter() {
        let (module_path, compiled_module) = entry.pair();
        if module_path == changed {
            continue;
        }
        // Check if this module imports from the changed module.
        for (_, module_entry) in compiled_module.symbols.iter() {
            if let ModuleEntry::Import { source_module, .. } = module_entry {
                if source_module == changed {
                    dependents.push(module_path.clone());
                    break;
                }
            }
        }
    }
    dependents
}
```

This is O(modules * symbols) per changed module. For typical project sizes (tens of modules), this is negligible. A reverse index optimization can be added later if profiling shows it matters.

**This section designs the watcher's *dependent discovery* only. What happens to a
dependent once the changed module's ABI surface moves is no longer decided here.**

The original rule was: re-register the changed module alone, because dependents call through
the GOT and pick up new code pointers, and a changed exported *type* was simply declared an
error with the user told to restart the REPL. The first half survives for an ABI-preserving
change; the second half was superseded by the S101 redefinition transaction, which
classifies the change at the commit gate and drives dependent recompilation — with BROKEN
marking and a cascade report — instead of leaving stale dependents behind. The watcher path
joins that same discipline at module grain
(`design/int/session-transaction.md` §7.3). Read it before changing anything here.

### 4.6 Watcher Integration with v4 REPL

The REPL already has the `watcher_paused` gate for GOT stability. The v4 watcher path:

1. `poll_and_reload` is called before each REPL prompt (unchanged timing).
2. For each changed path, map to module via `file_to_module`.
3. Clear the module's type info from TC (`tc.clear_module_for_replace_public()` — already exists).
4. Call `scheduler.re_register_module(module)` to re-enter it at `TypecheckFirst`.
5. Store the module's source sexps in the shared sexp map for workers.
6. Re-run the inline worker loop (or wake spawned workers) to process the changed module.
7. After processing, display `[updated: path]` or `[errors: path]`.

The `watcher_paused` gate prevents priority worker JIT writes during REPL eval. This is unchanged from the current design — typecheck can continue while eval runs, only code pointer writes are deferred.

### 4.7 Clearing Stale Module State

Before re-registration, the module's stale state must be cleared:

- **TypeChecker**: `tc.clear_module_for_replace_public()` removes the module's symbol table entries. This uses the DashMap `&self` API.
- **SharedCodegenState**: Stale GOT slots are overwritten in-place when new code is compiled. Old code pointers in `def_codegen` are overwritten. No explicit cleanup needed.
- **Cached modules set**: Remove the module from `cached_modules` (it is being recompiled from source, not loaded from cache).

### 4.8 Delete v3 Reload Path

After the watcher is migrated, the following become dead code:

- `CompilationSession::recompile_module_and_dependents`
- `CompilationSession::recompile_module`
- `CompilationSession::clear_module_state`
- `ModuleDependencyGraph` (the `file_to_module` mapping is replaced by the v4 `SharedState.file_to_module`)

These are deleted in Step 15, not in this sprint. Step 14 stops using them; Step 15 removes them.

## 5. Edge Cases and Invariants

### 5.1 Prelude Cache-Hit

The prelude is the most common cache-hit candidate. On second run:

1. `inject_prelude_if_needed` triggers `handle_import` for the prelude module.
2. `handle_import` resolves the prelude file, calls `try_cache_hit_load`.
3. Cache hit: type info is restored, module enters `TypecheckDone`, worker continues without blocking.
4. When macro expansion needs prelude macros (e.g., `list`, `do`), the priority codegen path loads the prelude `.o` via Linker, making all prelude symbols callable.

This is the critical performance path — prelude typecheck is the dominant cost on first compilation.

### 5.2 Multiple Workers Discovering the Same Cache-Hit Module

Two workers processing different modules may both encounter an import of the same dependency at roughly the same time. The first worker to call `try_cache_hit_load` succeeds; the second finds `tc.has_module(dep)` is already true (fast path).

The `scheduler.register_module_cached()` call is idempotent — if the module is already registered, it is a no-op (same as `register_module`). The TC restoration is also idempotent — `restore_cached_module` inserts into a DashMap, and a duplicate insert overwrites with identical data.

### 5.3 Cache Hit for Module Currently Being Typechecked

If worker A is typechecking module X (discovered via another import), and worker B discovers the same module X via a cache hit, there is a conflict. This is prevented by the scheduler's idempotency: `register_module_cached` checks `state.modules.contains_key(&module)` and skips if already registered.

The order of operations in `handle_import` ensures this is safe:
1. First check: `tc.has_module(dep)` — true if the module is loaded (either from cache or typecheck).
2. If not loaded: attempt cache hit, which calls `scheduler.register_module_cached`.
3. `register_module_cached` is idempotent — skips if the module is already in the scheduler (e.g., registered via `register_module` by another worker).

If the module is being typechecked (not yet loaded into TC), `tc.has_module(dep)` returns false. The cache check may succeed and try to register. But `register_module_cached` will find the module already registered (via `register_module` by the earlier worker) and skip. The current worker then falls through to `block_for_typecheck` and waits.

### 5.4 Cache Metadata Written by Nice Workers

Nice workers write `.o` and `.meta.json` files. On the next run, the priority worker reads them during `try_cache_hit_load`. There is no concurrent access conflict because nice workers only write during the current session, and cache reads only happen on subsequent sessions (or after the watcher triggers a reload, but the module is re-registered and re-typechecked in that case, not loaded from cache).

### 5.5 Watcher Fires During Eval

The `watcher_paused` gate prevents the watcher from processing changes during REPL eval. Changes accumulate in the watcher's event buffer and are drained on the next poll. This is unchanged from v3.

### 5.6 Watcher Fires for a Cached Module

If the watcher detects a change to a file whose module was loaded from cache (not typechecked from source), the re-registration path handles it correctly:
1. `file_to_module` maps the file to the module path (populated during `try_cache_hit_load`).
2. `re_register_module` finds the module in `TypecheckDone` or `Complete`, resets it to `TypecheckFirst`.
3. `cached_modules` is updated to remove the module (it will be recompiled from source).
4. The worker processes the module normally (full typecheck, JIT codegen).

### 5.7 Invariant: register_module_cached Must Be Called After TC Restoration

The sequence in `try_cache_hit_load` is:
1. Restore type info into TC.
2. Register with scheduler via `register_module_cached`.

This order is important: `register_module_cached` satisfies pending typecheck waiters. If called before TC restoration, a waiting worker would unblock and try to read type info that isn't yet available.
