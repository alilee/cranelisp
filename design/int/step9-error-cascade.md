# Step 9: Failed State and Error Cascade — Implementation Design

Sprint 45. Owned by `/int`. Reviewed by `/arch`.

## 1. Problem Statement

The v4 scheduler has `notify_module_failed` and `cascade_failure` methods that move modules to Failed and cascade to dependents. However, the error paths are not wired end-to-end:

1. **Batch mode**: `wait_inmem_complete()` returns `SchedulerError` which is converted to `CranelispError` via an ad-hoc `.map_err` in `session_v4.rs:178`. There is no `impl From` and the conversion discards error structure.
2. **REPL mode**: `eval_one_form_v4` handles per-form errors with TC snapshot/restore, but if a *dependency module* fails (not the REPL module itself), the scheduler has no method to clear the Failed state. Subsequent evals hit the stale Failed record.
3. **Cascade errors lack chaining**: `cascade_failure` creates `"dependency 'X' failed"` messages without including the original error that caused X to fail.
4. **No REPL recovery path**: the scheduler has no `reset_module` or equivalent. After a failed eval, the REPL module is stuck in Failed.

## 2. Two Error Paths

Step 9 handles two distinct error paths. They are separate mechanisms that must not be conflated.

### 2.1 Per-Form Error (REPL only)

**Current state**: already working in `eval_one_form_v4` (repl/mod.rs lines 602-620).

A single form fails during typecheck or codegen. The REPL module itself is the source of the error. The scheduler is *not* involved in tracking this failure because the REPL module ("user") is not registered with the scheduler for Additive evals. The error path is:

1. `process_module_forms(Additive)` returns `Err(e)`.
2. `eval_one_form_v4` catches the error.
3. TC is restored from snapshot.
4. Error is returned to the caller for display.
5. Next eval proceeds normally against the restored TC state.

**No changes needed** for this path. The TC snapshot/restore is the complete recovery mechanism.

### 2.2 Scheduler-Level Failure (Batch and REPL dependency resolution)

A module registered with the scheduler fails. This can be:

- **Batch**: the entry module or any of its file-based dependencies fails during `priority_worker_loop`. The worker calls `scheduler.notify_module_failed(module, error)`. Cascade propagates to all modules waiting on the failed module.
- **REPL dependency**: during `compile_dep_inline_v4`, a file-based dependency is registered and compiled via `priority_worker_loop`. If it fails, the scheduler records it as Failed. `wait_inmem_complete()` returns `Err`.

The difference from per-form errors: scheduler-level failures involve modules the scheduler is tracking. Recovery requires clearing scheduler state, not just TC state.

## 3. `SchedulerError` to `CranelispError` Conversion

### 3.1 `impl From<SchedulerError> for CranelispError`

Replace the ad-hoc `.map_err` at `session_v4.rs:178` with a formal conversion:

```rust
impl From<SchedulerError> for CranelispError {
    fn from(e: SchedulerError) -> Self {
        match e {
            SchedulerError::ModuleFailed { module, message } => {
                CranelispError::ModuleError {
                    message: format!("module '{}' failed: {}", module, message),
                    file: None,
                    span: Span::SYNTHETIC,
                }
            }
            SchedulerError::InmemIncomplete { module } => {
                CranelispError::ModuleError {
                    message: format!(
                        "in-memory codegen incomplete for '{}'", module
                    ),
                    file: None,
                    span: Span::SYNTHETIC,
                }
            }
            SchedulerError::ObjectIncomplete { module } => {
                CranelispError::ModuleError {
                    message: format!(
                        "object codegen incomplete for '{}'", module
                    ),
                    file: None,
                    span: Span::SYNTHETIC,
                }
            }
        }
    }
}
```

**Location**: `src/scheduler.rs`, after the `SchedulerError` definition. This keeps the conversion next to the source type.

After this, `session_v4.rs` call sites can use `?` directly:

```rust
self.scheduler.wait_inmem_complete()?;  // SchedulerError -> CranelispError via From
```

### 3.2 `SchedulerError` Enrichment

`SchedulerError::ModuleFailed` currently stores a bare `message: String`. To support error chaining (section 5), change this to carry the original `CranelispError`:

```rust
pub enum SchedulerError {
    ModuleFailed {
        module: ModuleFullPath,
        cause: Box<CranelispError>,
    },
    InmemIncomplete { module: ModuleFullPath },
    ObjectIncomplete { module: ModuleFullPath },
}
```

The `Box` avoids recursive size issues. `Display` for `ModuleFailed` formats as `"module '{module}' failed: {cause}"`. The `From` conversion preserves the chain by embedding the cause in the `ModuleError` message.

## 4. Error Chain Display

### 4.1 Cascade Error Construction

Currently `cascade_failure` creates:
```
"dependency 'foo' failed"
```

This discards the original error. Change to embed the cause:

```rust
fn cascade_failure(&mut self, failed_module: &ModuleFullPath) {
    let waiting_modules = self.collect_waiters_for_module(failed_module);

    // Clone the original error for each cascade target.
    let original_error = self.state.modules.get(failed_module)
        .and_then(|ms| ms.error.clone());

    for waiter_module in waiting_modules {
        let error = CranelispError::ModuleError {
            message: format!(
                "dependency '{}' failed: {}",
                failed_module,
                original_error
                    .as_ref()
                    .map(|e| e.to_string())
                    .unwrap_or_else(|| "unknown error".to_string()),
            ),
            file: None,
            span: Span::SYNTHETIC,
        };
        self.notify_module_failed(&waiter_module, error);
    }
}
```

### 4.2 User-Visible Error Messages

**Batch mode** (type error in `math.cl` cascades to `main.cl`):
```
error: module 'math' failed: Type error at 12..15: expected Int, found String
error: module 'main' failed: dependency 'math' failed: Type error at 12..15: expected Int, found String
```

Only the first error (the root cause) is actionable. The batch path should print the root cause prominently and the cascade chain as context:

```
error: Type error at 12..15: expected Int, found String
  in module 'math'
  (dependency of 'main')
```

Implementation: `wait_inmem_complete` already returns the first Failed module it encounters. The batch main prints `e` via `Display`. The `SchedulerError::ModuleFailed` Display implementation provides the chain. The batch error formatting (in `main.rs`) can strip the outermost wrapper to present the root cause first.

**REPL mode**: the REPL already wraps errors in `"Error: {e}"` display text. The chain embeds naturally.

### 4.3 Non-Deterministic Iteration

`wait_inmem_complete` iterates `HashMap` keys, so the "first error" varies between runs. This is acceptable for single-threaded operation. For a stable user experience, the implementation should prefer the root-cause module (the one with no `"dependency"` prefix in its error message) when scanning. This is a low-priority refinement, not a blocker.

## 5. REPL Recovery: `reset_module` API

### 5.1 The Problem

After a failed REPL eval that triggers dependency compilation, the dependency module may be left in the scheduler as Failed. The REPL module itself is not registered with the scheduler (Additive evals bypass `register_module`), so it is not directly affected. However, the failed dependency remains registered. If the user corrects their code and re-evals, the dependency may need to be recompiled. The stale Failed record blocks this: `register_module` is idempotent and skips already-registered modules (scheduler.rs line 236).

### 5.2 API Definition

```rust
impl CompileScheduler {
    /// Reset a module from Failed back to an unregistered state.
    ///
    /// Used by the REPL after a failed dependency compilation. Removes
    /// the module from the scheduler entirely so it can be re-registered
    /// and recompiled on the next attempt.
    ///
    /// Preconditions:
    /// - Module must be in the Failed pool.
    /// - TC state for the module has already been rolled back by the caller.
    ///
    /// Postconditions:
    /// - Module is removed from `state.modules`.
    /// - Module is removed from all deques (typecheck_first, typecheck_next,
    ///   typecheck_done).
    /// - Any priority queue entries for this module are removed.
    /// - Waiters on this module's symbols are already drained by
    ///   cascade_failure, so no cleanup is needed there.
    pub fn reset_module(&mut self, module: &ModuleFullPath) {
        let Some(ms) = self.state.modules.get(module) else { return };
        if ms.pool != ModulePool::Failed {
            return; // Only reset Failed modules.
        }

        self.state.modules.remove(module);

        // Clean deques (defensive — Failed modules should not be in deques,
        // but guard against inconsistency).
        self.state.typecheck_first.retain(|m| m != module);
        self.state.typecheck_next.retain(|m| m != module);
        self.state.typecheck_done.retain(|m| m != module);

        // Remove any priority queue entries for this module.
        self.state.priority_queue.retain(|e| &e.module != module);
    }
}
```

### 5.3 Why Remove, Not Reset-in-Place

Three options were considered:

1. **Reset pool to TypecheckDone**: incorrect — the module's type info was rolled back. It is not "done".
2. **Reset pool to TypecheckNext**: tempting, but the module's sexps, accumulator, and expanded_program are gone. Re-registration with fresh source is needed.
3. **Remove entirely**: cleanest. The next `compile_dep_inline_v4` call will `register_module` again, re-parse, and recompile from scratch. This matches the principle that failed compilation leaves no residue.

Option 3 is selected.

### 5.4 Integration with REPL eval

The recovery sequence in `compile_dep_inline_v4` (repl/mod.rs):

```rust
fn compile_dep_inline_v4(
    &mut self,
    dep_module: &ModuleFullPath,
    dep_sexps: &[Sexp],
) -> Result<(), CranelispError> {
    let scheduler = self.scheduler.as_mut().ok_or_else(/* ... */)?;

    scheduler.register_module(dep_module.clone(), false);

    let mut module_sexps = HashMap::new();
    module_sexps.insert(dep_module.clone(), dep_sexps.to_vec());

    let mut ctx = WorkerContext { /* ... */ };

    crate::worker::priority_worker_loop(&mut ctx, &mut module_sexps)?;

    // Check for failures. If the dep failed, reset it so the next
    // eval attempt can re-register and retry.
    match scheduler.wait_inmem_complete() {
        Ok(()) => Ok(()),
        Err(e) => {
            scheduler.reset_module(dep_module);
            Err(CranelispError::from(e))
        }
    }
}
```

Note: TC state for the dependency module is cleaned up by the caller's TC snapshot/restore in `eval_one_form_v4`. The `reset_module` call only clears scheduler state.

## 6. Batch Error Propagation

### 6.1 Current Path

In `session_v4.rs::register_module`:
1. `priority_worker_loop` runs. On error, `notify_module_failed` is called inside the loop (worker.rs:1492).
2. The loop itself returns `Ok(())` — individual module failures do not abort the loop (other modules may still complete).
3. `wait_inmem_complete()` finds the Failed module and returns `Err(SchedulerError::ModuleFailed { ... })`.
4. The `map_err` converts to `CranelispError::ModuleError`.

### 6.2 Changes

1. Replace `map_err` with `?` using the new `impl From`.
2. In `main.rs`'s `v4_main` function, the `?` propagates to the top level where the error is printed and the process exits with status 1.
3. The error message includes the cascade chain (see section 4.2).

### 6.3 Priority Worker Loop Error Handling

The `priority_worker_loop` (worker.rs:1491) currently catches `process_module_forms` errors and calls `notify_module_failed`. The loop then continues to process other modules. This is correct: in a multi-module build, one module's failure should not prevent other modules from compiling (they will cascade-fail only if they depend on the failed module).

No changes needed to the loop's error handling. The cascade is already handled by `notify_module_failed` calling `cascade_failure`.

## 7. Failed Module Lifecycle

### 7.1 Batch Mode

Failed modules are never cleaned up. The process exits after reporting the error. The scheduler, TC, and all other state are dropped.

Lifecycle:
```
register_module -> TypecheckNext -> TypecheckWorking -> [error] -> Failed
                                                                      |
                                    wait_inmem_complete returns Err ---+
                                                                      |
                                    main prints error, exits ----------+
```

### 7.2 REPL Mode — Dependency Failure

A file-based dependency fails during `compile_dep_inline_v4`.

Lifecycle:
```
register_module -> TypecheckNext -> TypecheckWorking -> [error] -> Failed
                                                                      |
                   wait_inmem_complete returns Err -------------------+
                                                                      |
                   reset_module removes from scheduler ---------------+
                                                                      |
                   TC snapshot/restore rolls back type state ----------+
                                                                      |
                   eval_one_form_v4 returns Err to user --------------+
                                                                      |
                   [next eval] -> register_module (fresh) -> retry ---+
```

### 7.3 REPL Mode — Per-Form Error (No Scheduler Involvement)

A REPL form itself has a type error. The "user" module is not registered with the scheduler.

Lifecycle:
```
process_module_forms(Additive) returns Err
    |
    eval_one_form_v4 catches Err, restores TC snapshot
    |
    returns Err to eval_v4 for display
    |
    [next eval] proceeds against restored TC state
```

No scheduler cleanup needed.

### 7.4 REPL Mode — Cascaded Dependency Failure

Module A depends on module B. B fails. A is cascade-failed.

Lifecycle:
```
B: register_module -> Working -> [error] -> Failed
   cascade_failure -> A: Failed (with "dependency 'B' failed" error)

wait_inmem_complete returns Err (first Failed module found)

reset_module(B) — removes B from scheduler
reset_module(A) — removes A from scheduler
TC snapshot/restore rolls back both modules' type state

[next eval] -> register_module for both -> retry
```

Implementation note: the REPL needs to reset all Failed modules, not just the one reported by `wait_inmem_complete`. After the `Err` from `wait_inmem_complete`, scan all registered modules and reset any in the Failed pool:

```rust
fn reset_all_failed_modules(scheduler: &mut CompileScheduler) {
    let failed: Vec<ModuleFullPath> = scheduler
        .all_modules()  // new query method returning module paths
        .filter(|m| scheduler.module_pool(m) == Some(ModulePool::Failed))
        .cloned()
        .collect();
    for m in failed {
        scheduler.reset_module(&m);
    }
}
```

This requires a new query method:

```rust
impl CompileScheduler {
    /// Iterate over all registered module paths.
    pub fn all_modules(&self) -> impl Iterator<Item = &ModuleFullPath> {
        self.state.modules.keys()
    }
}
```

## 8. Summary of Changes

| File | Change | Section |
|------|--------|---------|
| `src/scheduler.rs` | `SchedulerError::ModuleFailed` carries `Box<CranelispError>` instead of `message: String` | 3.2 |
| `src/scheduler.rs` | `impl From<SchedulerError> for CranelispError` | 3.1 |
| `src/scheduler.rs` | `cascade_failure` embeds original error in cascade message | 4.1 |
| `src/scheduler.rs` | `reset_module(&mut self, module: &ModuleFullPath)` | 5.2 |
| `src/scheduler.rs` | `all_modules()` query method | 7.4 |
| `src/session_v4.rs` | Replace `.map_err` with `?` on `wait_inmem_complete()` | 6.2 |
| `src/repl/mod.rs` | `compile_dep_inline_v4` resets failed deps + uses `From` conversion | 5.4 |
| `src/repl/mod.rs` | After `priority_worker_loop` error in dep path, reset all failed modules | 7.4 |

## 9. Sketch Comparison

### 9.1 How the Sketch Handles Errors

The sketch has no scheduler — it uses direct `compile_unit` calls. Error handling is simpler:

- **Batch** (`sketch/src/batch.rs`): errors from `compile_unit` propagate via `?` to `main`. No cascade concept because modules are compiled sequentially and synchronously. A dependency error during recursive `compile_unit` (stage 2c) unwinds the call stack.
- **REPL** (`sketch/src/repl.rs`): GOT snapshot/restore (`save_got_entries` / `restore_got_entries`) plus module table restoration. The REPL catches errors and restores both type state and codegen state to pre-eval state. There is no TC-level snapshot mechanism; instead, the sketch saves and restores the module's `CompiledModule` entry directly.

The sketch has no concept of cascade failure because there is no concurrent module compilation. If module B fails during A's compilation, the error propagates up the recursive call stack and A's `compile_unit` call returns `Err`. No separate cascade mechanism is needed.

### 9.2 Reimplementation Divergence

The reimplementation diverges from the sketch in three ways:

1. **Scheduler-based cascade vs call-stack unwinding.** The sketch relies on Rust's `?` operator to propagate errors up the recursive `compile_unit` call chain. The reimplementation uses the scheduler's waiter graph to cascade failures to all dependents simultaneously. This is necessary because the v4 pipeline compiles modules in parallel (even if single-threaded now), so there is no call stack to unwind.

2. **TC snapshot/restore vs CompiledModule save/restore.** The sketch saves entire `CompiledModule` values. The reimplementation uses the TC's `snapshot()` / `restore()` mechanism, which is more surgical — it captures just the state needed for rollback without copying the entire module table.

3. **Scheduler state cleanup.** The sketch has no scheduler, so there is nothing to clean up after an error. The reimplementation must explicitly remove Failed modules from the scheduler via `reset_module`. This is the genuinely new mechanism that has no sketch analog.

### 9.3 Rationale for Divergence

All three divergences are justified by the scheduler-driven architecture. The sketch's approach (recursive compile_unit + stack unwinding) cannot work in a scheduler-driven pipeline because modules are not compiled in a call stack — they are work items dispatched by the scheduler. The cascade mechanism is the scheduler-native equivalent of stack unwinding. The `reset_module` API is the scheduler-native equivalent of the sketch's "do nothing, it was never registered."
