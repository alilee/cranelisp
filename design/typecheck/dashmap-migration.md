# DashMap Migration: TypeChecker Concurrent Module Tables

Sprint 47, Step 12. Design document for migrating `TypeChecker.modules` from `HashMap` to `DashMap`, enabling concurrent module table access from multiple priority worker threads.

## 1. Problem Statement

The TypeChecker currently stores per-module symbol tables in a `HashMap<ModuleFullPath, SymbolTable>`. All access requires `&mut self` on `TypeChecker`, which means the pipeline wraps it in `Mutex<TypeChecker>`. When Sprint 47 Step 11 spawns multiple priority worker threads, they would serialize on this mutex — defeating the purpose of parallelism.

The contention pattern is:

- **Writer**: one worker typechecks module A, writing to `modules["A"]`.
- **Readers**: simultaneously, other workers typecheck modules B and C, reading from `modules["A"]` for import resolution and macro lookup.

This is the classic concurrent-HashMap use case: multiple readers, one writer per key, different keys active concurrently. DashMap's per-shard locking gives fine-grained access: writing to shard X does not block reading from shard Y.

Without this migration, Step 11's multi-threaded workers gain no parallelism. With it, workers operating on independent modules proceed without contention.

## 2. Scope of Changes

### Fields that change

| Field | Current type | Target type | Rationale |
|-------|-------------|-------------|-----------|
| `modules` | `HashMap<ModuleFullPath, SymbolTable>` | `DashMap<ModuleFullPath, SymbolTable>` | Core contention point. Multiple workers read (import resolution, macro lookup) and write (one writer per module). |

### Fields that do NOT change

| Field | Current type | Rationale for no change |
|-------|-------------|------------------------|
| `next_id` | `AtomicU32` | Already lock-free. No change needed. |
| `type_defs` | `RwLock<TypeDefRegistry>` | Already behind `RwLock` (Sprint 40 Phase 3). Rare writes, many reads. `RwLock` is appropriate. |
| `trait_registry` | `RwLock<TraitRegistry>` | Same as `type_defs`. |
| `impl_registry` | `RwLock<ImplRegistry>` | Same as `type_defs`. |
| `module_locks` | `HashMap<ModuleFullPath, Arc<AtomicBool>>` | Mutated only during module registration (serialized by the scheduler). The `AtomicBool` values are already atomic. If needed, a small `Mutex` wrapper can be added, but this is unlikely to be contended. |
| `state` | `CheckState` | Per-check transient state. Does NOT go into DashMap. Each worker gets its own `CheckState` on the stack (see section 5). |

### New dependency

`dashmap` is added to `crates/cranelisp-typecheck/Cargo.toml`.

## 3. API Signature Changes

### 3.1 `check_form` — the primary worker entry point

**Before:**
```rust
pub fn check_form(
    &mut self,
    _module: &ModuleFullPath,
    form: &TopLevel,
    pass: CheckPass,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<FormCheckResult, CranelispError>
```

**After:**
```rust
pub fn check_form(
    &self,
    module: &ModuleFullPath,
    form: &TopLevel,
    pass: CheckPass,
    state: &mut CheckState,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<FormCheckResult, CranelispError>
```

Key changes:
- `&mut self` becomes `&self`.
- `state: &mut CheckState` is threaded explicitly (previously accessed via `self.state`).
- The `module` parameter (previously unused `_module`) becomes the authoritative module path, replacing `self.state.current_module`.

### 3.2 `finalize_check_result`

**Before:**
```rust
pub fn finalize_check_result(
    &mut self,
    _module: &ModuleFullPath,
    accumulator: &mut ModuleCheckAccumulator,
    working_program: &[TopLevel],
    strategy: ModuleStrategy,
) -> Result<CheckResult, CranelispError>
```

**After:**
```rust
pub fn finalize_check_result(
    &self,
    module: &ModuleFullPath,
    state: &mut CheckState,
    accumulator: &mut ModuleCheckAccumulator,
    working_program: &[TopLevel],
    strategy: ModuleStrategy,
) -> Result<CheckResult, CranelispError>
```

### 3.3 `check` — unified entry point (used by old pipeline callers)

**Before:**
```rust
pub fn check(
    &mut self,
    program: &[TopLevel],
    ctx: &CompileContext,
    strategy: ModuleStrategy,
) -> Result<CheckResult, CranelispError>
```

**After:**
```rust
pub fn check(
    &self,
    program: &[TopLevel],
    ctx: &CompileContext,
    strategy: ModuleStrategy,
) -> Result<CheckResult, CranelispError>
```

`check()` creates a stack-local `CheckState` internally (replacing `self.state`). Existing callers are unchanged — the `&mut` to `&` change is source-compatible at call sites (callers with `&mut` can pass `&`).

### 3.4 Methods that remain `&mut self`

These methods perform structural mutations that are not called from worker threads during concurrent typechecking. They run during setup, teardown, or REPL-specific paths where single-threaded access is guaranteed:

| Method | Rationale for `&mut self` |
|--------|--------------------------|
| `new()` | Constructor — only called once. |
| `register_builtins()` | Setup — called from `new()`, before any workers. |
| `set_current_module()` | Only used by `check()` (which creates its own `CheckState`) and REPL paths. Workers do not call this — they pass the module path explicitly. |
| `remove_module()` | Hot-reload (REPL only). Single-threaded. |
| `insert_module()` | Hot-reload (REPL only). Single-threaded. |
| `restore_cached_module()` | Cache path — called before workers start on the module. |
| `restore_cached_impls()` | Cache path — called before workers start. |
| `restore()` / `snapshot()` | REPL error recovery. Single-threaded. |
| `register_imports()` / `register_exports()` | Called during `check_form` Pass 1. See section 4 for how these work with DashMap. |

### 3.5 Methods that change to `&self`

All methods called from worker threads during form-by-form checking must become `&self`. Each receives `state: &mut CheckState` explicitly for transient state access. Key methods:

| Method | Notes |
|--------|-------|
| `check_form()` | See 3.1. |
| `check_form_register()` / `check_form_body()` | Internal dispatch — same change. |
| `check_form_register_single_defn()` | Writes to `self.modules` via `current_symbol_table_mut()` — uses DashMap guard. |
| `check_form_body_single_defn()` | Reads/writes `self.modules` — uses DashMap guards. |
| `finalize_check_result()` | See 3.2. |
| `merge_form_result()` | Writes call graph edges to `self.modules`. |
| `infer_expr()` and all `infer_*` helpers | Currently `&mut self` for `self.state` access. Become `&self` with explicit `&mut CheckState`. |
| `lookup()` | Reads `self.modules`. Already `&self`. Reads `state.env` and `state.module_aliases`. |
| `resolve_qualified()` | Reads `self.modules`. Already `&self` except for `state.current_module` and `state.module_aliases` access. |
| `unify()` | Uses `self.state.subst` — receives `state` explicitly. |
| `fresh_var()` / `fresh_var_id()` | Already use `AtomicU32` — trivially `&self`. |
| `instantiate()` | Uses `self.state` — receives `state`. |
| `generalize()` | Uses `self.state` — receives `state`. |
| `push_scope()` / `pop_scope()` / `bind_local()` | Operate on `state.env` — receive `state`. |
| `record_expr_type()` | Operates on `state.expr_types` — receives `state`. |
| `apply_subst()` | Reads `state.subst` — receives `state`. |

### 3.6 The `self.state` field

After migration, `self.state` is retained for backward compatibility with:
- `check()` — creates a stack-local `CheckState`, then passes it through. The `self.state` field is unused by `check()`.
- REPL additive mode — `snapshot()`/`restore()` operate on `self.state` for the REPL's single-threaded eval path.

Workers never touch `self.state`. The field exists only for the REPL's serial path. A future cleanup could gate it behind `#[cfg(feature = "repl")]` or similar.

## 4. Guard Lifetime Audit

With DashMap, `self.modules.get(key)` returns a `Ref<K, V>` guard that holds a shard lock. `self.modules.get_mut(key)` returns a `RefMut<K, V>`. Holding a guard while acquiring another guard on a key in the same shard causes deadlock. This section audits every code path that accesses `self.modules`.

### 4.1 `current_symbol_table()` / `current_symbol_table_mut()`

**Current**: Returns `&SymbolTable` / `&mut SymbolTable` by borrowing from the HashMap. Lifetime is tied to `&self` / `&mut self`.

**Problem**: With DashMap, these would return guards. Any caller that holds the result while calling another method that accesses `self.modules` risks deadlock.

**Solution**: These methods are eliminated. Replace with explicit DashMap guard acquisition at each call site:

```rust
// Before:
let table = self.current_symbol_table();
table.get("foo");

// After:
let guard = self.modules.get(&state.current_module).unwrap();
let entry = guard.get("foo");
// ... use entry, then drop guard before any other modules access.
```

For mutation patterns, callers use `self.modules.get_mut()`:

```rust
let mut guard = self.modules.get_mut(&state.current_module).unwrap();
guard.insert(name, entry);
// guard dropped here or explicitly
```

### 4.2 `lookup_in_current_module()` — reads current module only

**Current code path**: `self.current_symbol_table().get(name)` -> `extract_scheme_from_entry`.

**Guard pattern**: Acquires one guard on `current_module`. `extract_scheme_from_entry` may follow Import/Reexport chains to other modules (via `resolve_fq_symbol`), acquiring additional guards.

**Deadlock risk**: YES. If `current_module` and the import source module hash to the same DashMap shard, holding the current module guard while acquiring the source module guard deadlocks.

**Solution**: Clone the entry from the current module guard, drop the guard, then follow the chain:

```rust
fn lookup_in_current_module(&self, state: &CheckState, name: &str) -> Option<Scheme> {
    let entry = {
        let guard = self.modules.get(&state.current_module)?;
        guard.get(name)?.clone()  // Clone and drop guard
    };
    self.extract_scheme_from_entry_owned(&entry, 0)
}
```

### 4.3 `resolve_fq_symbol()` — reads another module

**Current**: `self.modules.get(&fq.module)` -> reads an entry -> `extract_scheme_from_entry`.

**Guard pattern**: Acquires a guard on `fq.module`. If the entry is an Import/Reexport pointing to yet another module, follows the chain (recursive).

**Deadlock risk**: YES. Recursive chain following holds a guard while acquiring another.

**Solution**: Clone-and-drop at each step. `resolve_to_terminal_entry()` already does this pattern — it clones the entry and calls `drop(source_table)` explicitly. Apply the same pattern to `resolve_fq_symbol`:

```rust
fn resolve_fq_symbol(&self, fq: &FQSymbol, depth: usize) -> Option<Scheme> {
    let entry = {
        let guard = self.modules.get(&fq.module)?;
        guard.get(fq.symbol.as_ref())?.clone()
    };
    self.extract_scheme_from_entry_owned(&entry, depth)
}
```

### 4.4 `resolve_qualified()` — reads another module + visibility check

**Current**: Reads `self.modules.get(&resolved_path)`, gets entry, checks visibility, calls `extract_scheme_from_entry`.

**Guard pattern**: One guard on the resolved module. Calls `extract_scheme_from_entry` which may follow chains.

**Deadlock risk**: Same as 4.3.

**Solution**: Clone entry from guard, drop guard, then process:

```rust
fn resolve_qualified(&self, state: &CheckState, module_path: &ModuleFullPath, name: &str)
    -> Result<Option<Scheme>, CranelispError>
{
    let (entry, resolved_path) = {
        // ... alias resolution from state.module_aliases ...
        let guard = match self.modules.get(&resolved_path) {
            Some(g) => g,
            None => return Ok(None),
        };
        match guard.get(name) {
            Some(e) => (e.clone(), resolved_path),
            None => return Ok(None),
        }
    };
    // Guard dropped. Visibility check and chain following use owned data.
    // ...
}
```

### 4.5 `register_imports()` — reads source module, writes current module

**Current**: For each import spec, reads `self.modules.get(&spec.module_path)` to collect import entries, then writes to `self.current_symbol_table_mut()`.

**Guard pattern**: Holds a read guard on the source module while collecting entries, then acquires a write guard on the current module. Two guards from potentially different shards.

**Deadlock risk**: YES, if the source module and current module hash to the same shard.

**Solution**: Already correct in spirit — the current code collects entries into a `Vec<(Symbol, ModuleEntry)>` first, then inserts. The fix is to ensure the source guard is dropped before the write guard is acquired:

```rust
let imports_to_add = {
    let source_guard = self.modules.get(&spec.module_path)
        .ok_or_else(|| /* error */)?;
    collect_glob_imports(&source_guard, &spec.module_path)
    // source_guard dropped here
};
// Now safe to get_mut on current module
let mut current_guard = self.modules.get_mut(&state.current_module).unwrap();
insert_imports_detecting_ambiguity(&mut current_guard, imports_to_add);
```

### 4.6 `register_exports()` — same pattern as imports

**Solution**: Same as 4.5. Clone-collect from source, drop source guard, then write to current module.

### 4.7 `set_current_module()` — reads primitives/user, writes new module

**Current**: Reads `self.modules.get("primitives")` and `self.modules.get("user")` to seed the new module, then inserts with `self.modules.insert()`.

**Guard pattern**: May hold up to two read guards while building the new table, then inserts.

**Deadlock risk**: YES, if any of the three modules hash to the same shard.

**Solution**: Collect entries to copy into a `Vec`, drop all read guards, then insert:

```rust
fn set_current_module(&self, state: &mut CheckState, path: ModuleFullPath) {
    if self.modules.contains_key(&path) {
        state.current_module = path;
        return;
    }
    let mut table = SymbolTable::new(path.clone());

    // Collect primitives imports
    let prims_entries: Vec<_> = {
        let prims_path = ModuleFullPath::from("primitives");
        self.modules.get(&prims_path)
            .map(|guard| guard.all_symbols()
                .map(|(n, _)| (n.clone(), prims_path.clone()))
                .collect())
            .unwrap_or_default()
    };
    for (name, source_module) in prims_entries {
        table.insert(name.clone(), ModuleEntry::Import {
            source: FQSymbol { module: source_module, symbol: name },
        });
    }

    // ... same pattern for user module seeding ...

    self.modules.insert(path.clone(), table);
    state.current_module = path;
}
```

### 4.8 `remove_module()` / `insert_module()` / `restore_cached_module()`

These are single-threaded (REPL or setup). With `&mut self`, DashMap's `get_mut()` returns `&mut V` directly (no guard needed via `get_mut()` on a `&mut DashMap` — but DashMap does not support this pattern). Instead, these methods use the DashMap entry API or `remove()`. Since they hold `&mut self`, no other thread is accessing the map. No deadlock risk.

**Note**: `&mut self` on these methods means we have exclusive access. DashMap operations are still valid — they just acquire and release shard locks internally. Since no other thread holds any guards, no contention or deadlock.

### 4.9 `module_table()` — public read accessor

**Current**: Returns `Option<&SymbolTable>`.

**Problem**: With DashMap, must return a guard or owned data.

**Solution**: Two options:

1. Return `Option<dashmap::mapref::one::Ref<'_, ModuleFullPath, SymbolTable>>` — callers must handle the guard type.
2. Return owned `Option<SymbolTable>` via clone — simpler but more allocation.

**Chosen**: Option 1 for internal callers (they can handle the guard). For the public API (used by `/int` workers), provide a helper that clones specific entries:

```rust
/// Look up a symbol in a specific module. Returns an owned clone.
pub fn lookup_in_module(&self, path: &ModuleFullPath, name: &str) -> Option<ModuleEntry> {
    let guard = self.modules.get(path)?;
    guard.get(name).cloned()
}
```

### 4.10 Summary: the clone-and-drop discipline

All cross-module lookup paths must follow this discipline:

1. Acquire a DashMap guard on one module.
2. Clone the needed data out of the guard.
3. Drop the guard (explicitly or via scope exit).
4. Only then access another module or acquire a write guard.

Never hold two DashMap guards simultaneously. This is the primary safety invariant.

## 5. CheckState / Transient State Handling

### 5.1 Current situation

`CheckState` is stored on `TypeChecker` as `self.state`. All inference methods access it via `self.state.subst`, `self.state.env`, etc. This requires `&mut self`.

### 5.2 Target model

Each worker creates a stack-local `CheckState` and passes it explicitly to all inference methods:

```rust
// In the worker thread:
let mut state = CheckState::new(module_path.clone());
let result = tc.check_form(&module_path, &form, pass, &mut state, &mut accumulator)?;
```

The `ModuleCheckAccumulator` (already per-worker, per-module) continues to accumulate results across forms. `CheckState` carries the live inference state (subst, scope stack, resolutions). Both are stack-local — no sharing between workers.

### 5.3 Impact on internal methods

Every `impl TypeChecker` method that currently accesses `self.state` must gain a `state: &mut CheckState` parameter. This is a mechanical, high-volume change affecting approximately 30-40 methods. The methods fall into categories:

**Category A — inference methods** (infer.rs): `infer_expr`, `infer_var`, `infer_let`, `infer_if`, `infer_lambda`, `infer_apply`, `infer_match`, `infer_annotate`, `infer_trace`, `infer_vec_lit`, `infer_string_lit`, `infer_int_lit`, `infer_float_lit`, `infer_bool_lit`, `infer_run_tests`. These all read/write `state.subst`, `state.env`, `state.expr_types`, `state.method_resolutions`.

**Category B — unification** (unify.rs): `unify()` on TypeChecker delegates to the free function `unify::unify(&mut state.subst, t1, t2)`. The wrapper gains `state`.

**Category C — scheme operations** (checker.rs): `instantiate()`, `generalize()`, `instantiate_constrained()`. Access `state.active_constraints`, `state.subst`, `state.env`.

**Category D — scope operations** (checker.rs): `push_scope()`, `pop_scope()`, `bind_local()`. Operate on `state.env`.

**Category E — lookup** (checker.rs): `lookup()`, `lookup_in_current_module()`, `resolve_qualified()`. Read `state.env`, `state.module_aliases`, `state.current_module`. Also read `self.modules` (see section 4).

**Category F — recording** (checker.rs): `record_expr_type()`, `apply_subst()`. Operate on `state.expr_types`, `state.subst`.

**Category G — program passes** (program.rs): `check_form_register()`, `check_form_body()`, `finalize_check_result()`, `detect_constrained_fns()`, `pass4_monomorphise()`, `resolve_pending_overloads()`, `resolve_auto_curry()`, `resolve_deferred_trait_calls()`. Mix of state and modules access.

**Category H — trait operations** (traits.rs): `register_trait_decl()`, `register_trait_impl()`, `resolve_trait_method()`, `is_trait_method()`. Access `self.trait_registry` (via `RwLock`), `self.impl_registry`, sometimes `state` for constraint tracking.

### 5.4 The `check()` compatibility layer

The existing `check()` method (unified entry point) creates a stack-local `CheckState` and calls `check_form()` with it. The signature changes from `&mut self` to `&self`, but callers with `&mut TypeChecker` can still call it (Rust coerces `&mut T` to `&T`):

```rust
pub fn check(&self, program: &[TopLevel], ctx: &CompileContext, strategy: ModuleStrategy)
    -> Result<CheckResult, CranelispError>
{
    let mut state = CheckState::new(ctx.module.clone());
    // ... existing logic using &mut state instead of self.state ...
}
```

### 5.5 REPL state persistence

The REPL additive mode requires `CheckState` to persist across evaluations (e.g., the substitution grows, module aliases accumulate). This is handled by having the REPL's eval path maintain a `CheckState` in the `ReplSession` (or equivalent). The REPL passes this persistent state into `check()` via a new overload or by calling `check_form()` directly:

```rust
// Option: check_with_state() for REPL callers who supply persistent state
pub fn check_with_state(
    &self,
    program: &[TopLevel],
    ctx: &CompileContext,
    strategy: ModuleStrategy,
    state: &mut CheckState,
) -> Result<CheckResult, CranelispError>
```

The existing `self.state` field is retained as the default for `snapshot()`/`restore()` in the REPL path. Workers never touch it.

## 6. Migration Strategy

The migration is done in a specific order to minimize breakage at each step. Each step results in a compilable, passing test suite.

### Step A: Add `dashmap` dependency

Add `dashmap` to `cranelisp-typecheck/Cargo.toml`. No code changes.

### Step B: Thread `CheckState` through all internal methods

This is the largest mechanical change. Replace every `self.state.X` access with `state.X` access, adding `state: &mut CheckState` to ~40 method signatures. The `self.state` field remains; `check()` passes `&mut self.state` as the `state` parameter. All methods remain `&mut self` during this step.

**Validation**: `cargo test` passes. Behavior is identical — the same `CheckState` is being used, just accessed via a parameter instead of a field.

### Step C: Change `check_form` and related methods to `&self`

With `state` threaded explicitly, the only remaining `&mut self` requirement is `self.modules` mutation. Convert the methods that workers will call:

1. Change `check_form()`, `check_form_register()`, `check_form_body()`, `merge_form_result()`, `finalize_check_result()` from `&mut self` to `&self`.
2. Change all `infer_*` methods from `&mut self` to `&self`.
3. Change `unify()`, `instantiate()`, `generalize()`, etc. from `&mut self` to `&self`.
4. Change scope operations (`push_scope`, `pop_scope`, `bind_local`) to operate on `state` directly (they already do — just remove `&mut self`).
5. Change `fresh_var()` / `fresh_var_id()` to `&self` (they already use atomic operations).

**At this point, `self.modules` is still HashMap.** Methods that mutate `self.modules` (like `register_imports`, `set_current_module`) are called from within `check()` which still has `&mut self`. Interior methods that read `self.modules` work fine with `&self` on HashMap.

**Validation**: `cargo test` passes.

### Step D: Switch `modules` to `DashMap`

1. Change the field type from `HashMap<ModuleFullPath, SymbolTable>` to `DashMap<ModuleFullPath, SymbolTable>`.
2. Update every access site per the guard lifetime audit (section 4):
   - `.get()` returns `Option<Ref<K, V>>` — add `.clone()` + drop where needed.
   - `.get_mut()` returns `Option<RefMut<K, V>>`.
   - `.contains_key()` — no change needed (same API).
   - `.insert()` — no change needed (same API, takes owned key+value).
   - `.remove()` — returns `Option<(K, V)>` instead of `Option<V>`.
   - `.iter()` — returns guards. Clone data out before dropping.
3. Eliminate `current_symbol_table()` and `current_symbol_table_mut()` — replace call sites with explicit DashMap guard acquisition.
4. Apply the clone-and-drop discipline at every cross-module lookup (section 4.10).

**Validation**: `cargo test` passes.

### Step E: Change `check()` to `&self`

With `modules` behind DashMap and `state` threaded, `check()` no longer needs `&mut self`:

1. `set_current_module()` — either becomes `&self` (DashMap handles interior mutation) or is replaced by directly setting `state.current_module`.
2. `clear_module_for_replace()` — uses DashMap `get_mut()` guard.
3. `register_imports()` / `register_exports()` — use DashMap guards.

**Validation**: `cargo test` passes. `WorkerContext` can now hold `&TypeChecker` instead of `&mut TypeChecker`.

### Step F: Update `WorkerContext` in `/int` code

This step is owned by `/int` but depends on the `/typecheck` API changes:

1. `WorkerContext.tc` changes from `&mut TypeChecker` to `&TypeChecker`.
2. Worker threads call `tc.check_form(&self, module, form, pass, &mut state, &mut acc)`.
3. `state` is stack-local to each worker thread.

## 7. Edge Cases and Invariants

### 7.1 Deadlock scenarios

**Scenario 1: Same-shard cross-module lookup.** Worker holds a guard on module A's shard, then tries to read module B which hashes to the same shard. DashMap uses fair read-write locks per shard — two read guards on the same shard are fine. A read guard + a write guard on the same shard will deadlock. The clone-and-drop discipline (section 4.10) prevents this: never hold a guard while acquiring another.

**Scenario 2: Import chain following.** Module A imports from B, B re-exports from C. Following the chain requires accessing three modules. Without clone-and-drop, this holds three simultaneous guards. With clone-and-drop, each step clones the entry, drops the guard, then proceeds. No deadlock.

**Scenario 3: `register_imports` + `finalize_check_result` interleaving.** Worker 1 calls `register_imports` on module X (reads module Y, writes module X). Worker 2 calls `finalize_check_result` on module Y (reads and writes module Y). If Worker 1 holds a read guard on Y while Worker 2 holds a write guard on Y — this can't happen because Worker 1 drops the Y guard before writing to X (per section 4.5).

### 7.2 Ordering assumptions

**Invariant: No two workers typecheck the same module.** The scheduler guarantees this via `module_locks` and pool assignment. DashMap does not enforce this — the scheduler does.

**Invariant: Pass 1 before Pass 2 within a module.** The worker processes forms sequentially within a module. Multiple workers process different modules. A worker running Pass 2 on module A may read module B which is in Pass 1 (signatures being registered). This is correct — Pass 2 only reads already-registered signatures from other modules, and the scheduler ensures a module's symbols are available before unblocking waiters.

**Invariant: `notify_symbol_typechecked` happens after the symbol is written to the SymbolTable.** The write to `self.modules` (via DashMap guard) must complete and the guard must be dropped before the scheduler notification. Workers reading the symbol after being unblocked will see the written data because DashMap guards enforce happens-before ordering.

### 7.3 `RwLock` interaction with DashMap

The `type_defs`, `trait_registry`, and `impl_registry` fields use `RwLock`. Methods that hold an `RwLock` read/write guard AND access `self.modules` must not hold both simultaneously for longer than necessary. In practice, the access patterns are disjoint: trait registration reads/writes the registry but does not access `self.modules` for cross-module lookups in the same critical section. The audit found no methods that hold both an `RwLock` write guard and a DashMap guard simultaneously.

If this assumption proves wrong during implementation, the fix is the same clone-and-drop discipline: acquire the `RwLock` guard, extract what's needed, drop it, then access `self.modules`.

### 7.4 `module_locks` map

Currently `HashMap<ModuleFullPath, Arc<AtomicBool>>`. The `try_lock_module()` method uses `entry().or_insert_with()` which requires `&mut self`. Options:

1. Wrap in a small `Mutex<HashMap<...>>` — acceptable because contention is minimal (one insertion per module, at registration time).
2. Change to `DashMap<ModuleFullPath, Arc<AtomicBool>>` — heavier dependency for a low-contention map.
3. Pre-populate during module registration (which runs on one thread before workers start) — then `try_lock_module` only reads, which works with `&self` on a `HashMap` behind an `RwLock`.

**Chosen**: Option 1. Wrap in `Mutex`. The lock is held only for the `entry()` call — O(1), no contention.

### 7.5 Performance considerations

DashMap has slightly higher per-access overhead than HashMap (shard selection + lock acquisition). For the typechecker, `self.modules` accesses are far less frequent than `state.subst` accesses (which are untouched by this migration). The parallelism gain from concurrent multi-module typechecking vastly outweighs the per-access overhead.

The clone-and-drop discipline adds allocation for cloned `ModuleEntry` values. These are small (a few strings and an enum variant). If profiling shows this matters, frequently-accessed entries (e.g., import chain targets) can be cached in the `CheckState` for the duration of a form's checking.

## 8. Sketch Comparison

The sketch does not have concurrent typechecking. Its `TypeChecker` uses `HashMap` throughout and is single-threaded. This migration has no sketch precedent to follow or diverge from. The design is driven entirely by the concurrent pipeline architecture (`design/arch/concurrent-pipeline.md` §7.3) and the Sprint 47 architecture review.

## 9. Rejected Alternatives

### 9.1 `Mutex<HashMap>` instead of DashMap

A single `Mutex<HashMap>` is simpler but defeats the purpose: workers would serialize on the mutex, providing no parallelism. DashMap's per-shard locking is the minimum complexity needed for concurrent access to independent modules.

### 9.2 `RwLock<HashMap>` instead of DashMap

Better than `Mutex` — multiple readers can proceed concurrently. But a single writer blocks all readers, and during typechecking, one worker is always writing (registering symbols in its module). DashMap allows one writer to module A while readers access module B — true per-key concurrency.

### 9.3 Immutable snapshots (clone the entire modules map per worker)

Each worker gets a cloned snapshot of all module tables at the start of typechecking. Writers write to a local copy and merge back. This avoids shared mutable state entirely but has prohibitive cost: cloning all module tables for every module typecheck, plus a complex merge protocol.

### 9.4 Channel-based architecture (workers send mutations to a coordinator)

Workers send `RegisterSymbol(module, name, entry)` messages to a coordinator thread that owns the HashMap. This avoids shared state but adds latency (round-trip to coordinator) and complexity (async message protocol). DashMap is simpler and lower latency.
