# Module failure and error cascade

How a failed module's error reaches the user and how the REPL recovers from it.
The scheduler protocol is [concurrency-architecture.md](concurrency-architecture.md);
cluster staging, where a failure drops the stack-local staging and leaves the
live tables unchanged, is [int.md §6.2](int.md#62-cluster-orchestration). Error
formatting is [int.md §9](int.md#9-error-formatting-decisions-39--42).

## 1. Two failure paths

- **A REPL form fails.** A typecheck or codegen error in the form being
  evaluated returns to the eval thread as that turn's error. The scheduler
  does not track it.
- **A module fails in the scheduler.** A dependency, or any module under
  `--run` or `--link`, fails its typecheck or codegen. The scheduler marks it
  `Failed` and cascades the failure (§4.1).

## 2. Surfacing a scheduler failure

- `SchedulerError::ModuleFailed` carries the failed module, the failing
  error's text and its span.
- `impl From<SchedulerError> for CranelispError` wraps it as a `ModuleError`
  whose text is `module '<m>' failed: <text>`, located at the inner error's
  span.
- `wait_inmem_complete` returns the first `Failed` module found. Iteration
  order is unspecified, so the reported module may be a cascade victim rather
  than the root. The root cause survives either way (§4.1).

## 3. Batch propagation

Under `--run` and `--link`, the error propagates to `main`. There it is
formatted with the entry file's location and printed to stderr, and the process
exits 1.

A REPL start-up failure does not exit. It degrades to the form-by-form entry
load (`recover_startup_failure`).

## 4. Error chain

### 4.1 Cascade construction

When a module fails, `notify_module_failed_locked` records its error, and
`cascade_failure_locked` fails every module waiting on one of its symbols with:

```text
dependency '<failed>' failed: <failed module's error text>
```

The cascade recurses, so each level embeds the full text below it and the
root-cause error survives to the top.

The cascade drains the failed module's waiters once. A waiter registered on it
afterwards would never be woken, because `Failed` is not a terminal typecheck
pool and nothing notifies it again.

- **Fail fast before registering.** Every path that would wait on a module
  checks for `Failed` first, under the same lock, and returns that module's
  error instead: `block_for_typecheck`, the worker's signature barrier
  (`block_on_first_unready_closure_member`) and the eval thread's
  `await_signature_barrier`. The two barriers share one predicate. The worker
  fails its own module with the returned error, which wakes the completion
  waits.
- **Why it is load-bearing.** `wait_inmem_complete_blocking` and
  `wait_object_complete` stop scanning at the first incomplete module. A
  stranded waiter therefore hangs the foreground only when it is scanned
  before the failed module. That is why the REPL hang after an imported
  module failed to reload was intermittent. That order dependence
  remains, and QA holds it as a residual. Falsifier: a hang whose scheduler
  state shows a waiter on a `Failed` module, or a stranded module with no
  `Failed` dependency.
- **Guards.** The unit guard is
  `scheduler::tests::atomic_barrier_gate_fails_importer_of_already_failed_member`.
  The end-to-end guard is
  `tests/repl_watch.rs::watch_type_error_reload_of_imported_module_blocks_without_hanging`.

### 4.2 User-visible message

The user sees the top module's `module '<m>' failed:` wrapper followed by the
embedded chain. It names the failing dependency, keeps the root error, and does
not repeat the root error at every level of a deep chain.

Unimplemented: presenting the root cause first and stripping the outer
wrappers.

## 5. REPL recovery

After a failed dependency wait, the eval thread calls
`CompilerSession::reset_failed_modules`.

- It removes every `Failed` module from the scheduler
  (`reset_all_failed_modules`), so a later reference re-registers and
  recompiles it from source.
- It drops the live table of a reset module that never reached a terminal
  state, so a later fully qualified reference cannot read a half-installed
  table as loaded.
- A module that was once terminal and failed only as a cascade victim keeps its
  table.

Start-up recovery and redefinition use the same reset.

## 6. Evidence

The spec-traced end-to-end cells are:

- `tests/spec_09_macros.rs::cross_module_macro_dependency_type_error_cascades_neg`
  (§4.1);
- `tests/spec_12_runtime.rs::dependency_type_error_cascades_with_module_context_neg`
  (§4.1 and §4.2);
- `tests/spec_12_runtime.rs::dependency_type_error_cascade_preserves_root_cause_neg`
  (§4.1);
- `tests/spec_12_runtime.rs::three_level_cascade_does_not_duplicate_error_output_neg`
  (§4.2).
