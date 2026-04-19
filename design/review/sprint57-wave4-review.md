# Sprint 57 Wave 4 Review — G9 (Persistent Priority Workers)

**Sprint**: 57 Wave 4
**Date**: 2026-04-19
**Reviewer**: `/review`
**Scope**: `/int` persistent-worker lifecycle (`CompilerSession::new` spawns priority + nice pools; workers park on condvar; `shutdown()` / `Drop` join), `PriorityWorkerRefs` deletion, `SharedState.module_sexps` / `SharedState.suspend_states` / `SharedState.lib_dirs` / `SharedState.platform_dirs` migration, `register_module_with_source` / `reload_module` routed through scheduler, scoped `thread::scope` confined to `#[cfg(test)]`, macro-clause `is_last=false` race fix, `/qa` 4 G9 integration tests (`tests/wave4_g9.rs`) plus 4 `/int` unit tests in `src/session_v4.rs::persistent_worker_tests`.

## Verdict

**PASS with Importants.** Wave 4 delivers the G9 core — persistent priority + nice worker pools spawned at session init, joined at shutdown, with `thread::scope` confined to test code. Shutdown-race handling is sound; worker count clamping is correct; pre-existing `is_last=true` race was correctly identified and fixed. The material concerns are two partial deliveries that diverge from the design contract: (I-1) Decision 28's "one JIT per priority worker, reused across work items" target shape is **not** implemented — each `inline_jit_codegen_for_names` call still constructs a fresh `Jit`, which is the interim per-function shape Decision 28 explicitly rejects ("NOT a stepping stone"). (I-2) §4.4's "REPL eval submits through scheduler" target is not implemented — `process_single_form` + `compile_and_execute_expr` run inline on the REPL main thread, bypassing the persistent pool. Both are latent Principle-8 violations rather than showstoppers because the persistent-worker infrastructure IS in place; the fresh-JIT pattern is not load-bearing; and the eval path works end-to-end. Neither blocks close for Wave 6 showcase, but they should not be re-deferred without explicit user acceptance.

**Baseline statement**: 14 → 15 full-suite failures. `/qa`'s attribution (tally drift: 4 `sprint23_*` failures in reality vs 3 documented at close of Sprint 56) is accepted — spot-checked the failing tests list is compatible with the "+1 cache/link Phase-5-dependent" category and not traced to a Wave 4 regression. Persistent-worker unit + integration tests all pass.

## Focus area findings

### Focus 1 — `thread::scope` absence outside tests: **PASS**

**Verdict**: Clean. `/qa`'s `wave4_g9_thread_scope_absent_outside_cfg_test` (`tests/wave4_g9.rs:397`) is the structural gate; I spot-checked the full `src/` tree and found exactly two remaining `thread::scope` occurrences, both correctly gated:

1. **`src/session_v4.rs:3403`** — inside `#[cfg(test)] pub fn spawn_nice_workers` (guard at line 3393). Doc explicitly states "`cfg(test)` gates this so `thread::scope` does not appear in any non-test build per `design/int/persistent-workers.md` §11 acceptance criterion 2." Retained as a test-only helper for `nice_worker_lifecycle_spawn_and_shutdown` (a pre-existing Sprint 46 test that relied on scope-based spawn).

2. **`src/scheduler.rs:1673`** — inside `#[cfg(test)] mod tests` (guard at line 1539). Tests the scheduler-worker wiring via one-shot scoped spawn.

No other `thread::scope` / `spawn_scoped` in `src/` or `crates/`. Acceptance criterion §11 item 2 met.

### Focus 2 — Worker lifecycle vs `persistent-workers.md` §4: **PASS with one Important**

Walked §4 (spawn/park/wake/drain/shutdown) against the implemented code.

| §4 requirement | Impl location | Status |
|---|---|---|
| Spawn at `CompilerSession::new` via `std::thread::Builder::spawn` (not scoped) | `src/session_v4.rs:735-745` | PASS — priority pool; `:751-761` nice pool. |
| Workers take `&SharedState` (via `Arc::clone`) | `src/worker.rs:2943` `priority_worker_loop_shared(shared: &SharedState)` | PASS. `PriorityWorkerRefs` deleted (grep: zero references in `src/`). |
| Park on scheduler condvar via `take_priority_work_blocking` | `src/worker.rs:2945` | PASS. Condvar-based park, not busy-loop. |
| `None` from `take_priority_work_blocking` = shutdown | `src/worker.rs:2963` | PASS. |
| Worker count derived as `available_parallelism()-1`, clamp `[1,8]` | `src/session_v4.rs:610-619 resolve_priority_worker_count` | PASS. `0` → auto-detect; non-zero clamped. Tests pass `priority_workers: 1` for determinism. |
| `module_sexps` + `suspend_states` on `SharedState` | `src/session_v4.rs:492, 498` | PASS. Moved from per-call locals. Workers read/mutate under `Mutex` for clone + insert/remove. |
| `shutdown()` signals scheduler then joins priority then nice | `src/session_v4.rs:2838-2853` | PASS. Exact sequence from §5.2. |
| `Drop` calls `shutdown()` defensively | `src/session_v4.rs:3362-3375` | PASS. Idempotent shutdown documented. |
| Mid-codegen worker finishes current item, then exits | §5.2 description | PASS by construction — worker checks shutdown flag at loop top only; a worker past that point naturally completes its work before re-entering `take_priority_work_blocking` which returns `None`. `/qa`'s `shutdown_under_load_no_panic` (`src/session_v4.rs:4000`) exercises this. |

**I-1 — persistent-workers.md §4.4 divergence (REPL eval)**: §4.4 states "eval submits through the scheduler … `register_module_additive` + `wait_module_complete`." Implementation at `src/session_v4.rs:1436 process_single_form` runs `worker::process_module_forms` *inline* on the REPL thread, then `codegen_and_execute` calls `inline_jit_codegen_for_module` + `compile_and_execute_expr` inline. The persistent priority pool is **not** used for REPL eval; it sits idle while the REPL thread drives the compilation itself. This is a divergence from the design contract worth flagging because:
- The whole point of Decision 28 + §4.5 "persistent eval JIT" is to route `__expr` codegen through the worker's reused JIT.
- Today's REPL eval path builds *two* fresh JITs per eval (`inline_jit_codegen_for_module` → new Jit, then `compile_and_execute_expr` → another new Jit), which is worse than the §4.4 target and even worse than what Decision 28 rejects as an interim.
- Integration `register_module_with_source` (batch) and `reload_module` (file-watcher) DO route through the scheduler (`src/session_v4.rs:1207, 1134-1143`) and exercise the persistent workers properly.

Not a Blocker because REPL eval works end-to-end and the persistent-worker infrastructure IS in place for future routing. But: this is the second area of Wave 4 where the implementation stops short of the design target, and the pair (I-1 + I-2 below) is large enough that Wave 4's stated "§4.4 eval submits through scheduler" and "§4.5 persistent eval JIT" are not delivered. The gate wording ("workers persistent") is literally met; the design-contract wording is not.
- **Owner**: `/int`.
- **Severity**: Important. **Timing**: Sprint 58 follow-on; do not re-defer without user acceptance.

### Focus 3 — Per-worker JIT per Decision 28: **Important divergence**

**Verdict**: Decision 28's target shape — "one Cranelift `JITModule` per priority worker as thread-local state, lazily created on the worker's first codegen work item and reused across subsequent items" — is **not** implemented. Each `inline_jit_codegen_for_names` call builds a fresh `Jit` (`src/worker.rs:2474 Jit::new_with_symbols`) and pushes the finalised `Arc<Jit>` onto `SharedState.kept_jits` for lifetime retention.

**What IS correct**:
- `JITModule` is never shared across threads. There is no `Arc<JITModule>` or `Mutex<JITModule>` used for codegen dispatch — grep for `Arc<Jit>` / `Mutex<Jit` confirms all usage is session-level retention, never cross-thread invocation.
- Each worker that picks up a codegen work item creates its own `Jit` on that worker's stack (`inline_jit_codegen_for_names` runs on the worker thread; the `Jit` is local until the `Arc::clone` push to `kept_jits` at line 2506). This preserves the `JITModule`-not-`Sync` invariant — the `Jit` is never seen by a second thread.
- `KeptJit` has `unsafe impl Send + Sync` (`src/session_v4.rs:417-438`) with a SAFETY comment that accurately reflects "push-only, never-mutate after finalize."

**What's missing**:
- Decision 28 says "per-worker" (thread-local), "reused across subsequent items" — current shape is "per-compile-call" (fresh every batch).
- There is no `thread_local!` holding a worker-local `Jit`. Grep confirms zero `thread_local` / `RefCell<Jit>` / `LocalKey.*Jit` in `src/worker.rs`.
- Decision 28's rationale ("serialising codegen calls across N workers defeats parallelism") is not violated by the current shape, but the MEMORY-GROWTH rationale (§4.5 "long-running REPL session accumulates many `Code` entries … one JIT instance stays alive for all N") is strictly worse: every compile allocates a fresh JIT, so `kept_jits` grows by one per batch compile. Decision 28's rotation FIXME at `persistent-workers.md:206` addresses the "one JIT per worker for session" shape — the current shape has no rotation policy at all because it has no per-worker JIT to rotate.

**I-2 — Decision 28 target shape not delivered**: This is a direct Principle-8 concern. Decision 28 explicitly rejects the "per-function JIT" (Sprint 56 shape) as interim: "There is NO per-function JIT either (the Sprint 56 shape); that was the interim bridge. The per-worker shape is the G10 target, not a stepping stone." Wave 4 kept the Sprint 56 per-function shape. That is exactly the scaffolding Decision 28 ruled out.

**Mitigation observations**:
- The `Arc<Jit>` on `kept_jits` provides the lifetime invariant Decision 25 requires; no observable correctness bug.
- The FIXME at `persistent-workers.md:206` (Wave 4+1) exists but its preamble ("Wave 4 ships with a one-JIT-per-worker-for-session shape") does NOT match what landed. Either the FIXME text should be rewritten to reflect the actual landed state (per-function-per-session), or the implementation should be revised to match. As written, the FIXME is now misleading.
- `/qa`'s `wave4_g9_per_worker_jit_isolation_across_sessions` (`tests/wave4_g9.rs:270`) tests *cross-session* isolation, which IS honoured. It does NOT test *per-worker reuse* within a session — that test in `tests/plan/ring4.md:676` (`per_worker_jit_reused_across_work_items`, asserting `Arc::ptr_eq` across two compiles on the same worker) was planned but not written. Its absence is consistent with the fact that the property isn't actually upheld.

- **Owner**: `/int`. **Severity**: Important.
- **Proposed resolutions** (any of):
  1. Implement the §4.5 shape: `thread_local! { static WORKER_JIT: RefCell<Option<Jit>> }` in `src/worker.rs`, create on first codegen, reuse across calls; Sprint 58.
  2. Accept the current per-function shape and formally retract Decision 28 as a design choice; update `persistent-workers.md:204-206` to describe the landed shape.
  3. File tracking FIXME against the current `inline_jit_codegen_for_names` call site with an explicit "Decision 28 divergence — Sprint 58 rework" note.

**Timing**: Not a Wave-4 gate blocker (infrastructure is in place; divergence is incremental), but do NOT defer again without explicit user sign-off. Two waves of "partial Decision 28" would be the second deferral per `/sprint` deferral principles.

### Focus 4 — Shutdown-race handling: **PASS**

Walked §5.2 end-to-end.

- `shutdown()` (`src/session_v4.rs:2838`) calls `scheduler.shutdown()` first (wakes condvars) then joins handles in priority-then-nice order. Handles are drained, so double-shutdown is a no-op. `join()` ignores errors via `let _ =`, matching §5.2 panic-tolerant spec. **PASS**.
- `Drop` (`src/session_v4.rs:3362`) calls `shutdown()` unconditionally. Doc explicitly states idempotency. **PASS**.
- Mid-codegen worker: `shutdown()` sets flag, then `join()` waits. The worker mid-`compile_to_module` does not observe the flag until it re-enters `take_priority_work_blocking` at the loop top (`src/worker.rs:2945`). This means `shutdown()` blocks on the **current codegen completing** — matches §5.2 "bounded wait by codegen duration, tens of ms typically." No data race observed (workers read `SharedState` through `Arc` only; scheduler flag is atomic).
- Enqueued-but-unprocessed work at Drop time: workers finish current item (if any) then park; next `take_priority_work_blocking` returns `None` because scheduler was shut down; the enqueued items are silently dropped. No panic, no leak of thread handles. `/qa`'s `shutdown_under_load_no_panic` + `/int`'s `persistent_worker_park_and_wake` + `concurrent_register_module_two_modules_complete` unit tests cover this.

**S-1**: `persistent-workers.md §9.1` also lists `shutdown_race_mid_codegen` as a target unit test asserting "workers join after the work completes; bounded wait < 500ms." The landed unit-test list has `shutdown_under_load_no_panic` (no explicit bounded-wait assertion) but no explicit bounded-wait timer test. Not a Blocker — the `join()`-returns-at-all behaviour implicitly asserts boundedness, and test runtime < 5s per test suggests the wait is well under 500ms. Consider adding a timed-wait assertion in a Sprint 58 follow-on.
- **Owner**: `/int` (Sprint 58). **Severity**: Suggestion.

### Focus 5 — G10 partial delivery: **Already covered by I-2**

Covered at Focus 3. Summary: G10 design §4.5 says "persistent eval JIT" = "per-worker JIT, reused across eval and non-eval codegen." Implementation delivers neither per-worker reuse nor eval-via-scheduler (see also Focus 2's I-1). Whether this counts as "reduced" per §7 deletion #8 or a Principle-8 violation: in combination they are the latter. The "legitimate reduced" path would be either (a) per-worker JIT reused but eval still inline — acceptable; (b) eval routed through scheduler but fresh JIT per compile — acceptable; (c) both — the actual target. Landing neither is a Principle-8 concern.

Not escalating to Blocker because: infrastructure is in place, no correctness regression, `/qa`'s gate tests pass, cross-session isolation is verified. Escalating to Important because this is a clear design divergence from the canonical reference (`persistent-workers.md` + Decision 28). Folded into I-1 and I-2 above.

### Focus 6 — Macro-clause `is_last=true` race fix: **PASS — correct fix**

Reviewed `compile_macro_with_state` (`src/worker.rs:248-256`) and `compile_macro_if_needed` (`src/worker.rs:1616-1620`). Both now pass `is_last: false` to `notify_inmem_codegen_complete`.

**Why this is a real bug, not a structural hack**:
- `is_last: true` tells the scheduler "this was the last symbol for the module — set `inmem_done` on the module." Under scoped workers (pre-Wave 4), the main thread waited on `scope` exit, not on `inmem_done`, so an erroneously-early `inmem_done` was masked.
- Under persistent workers, the main thread waits on `scheduler.wait_inmem_complete_blocking()` (`src/session_v4.rs:1214`). If a macro clause compile erroneously flips `inmem_done` on the owning module, the main thread unblocks before the module's actual main/defn codegen completes — observable as a "symbol X not found" at the next eval, or subtle ordering bugs.
- The fix correctly identifies that macro-clause compilation is *ancillary* work for the module — the module's own codegen happens at the end of `handle_typecheck_work_shared` via `inline_jit_codegen_for_module`, which is the one site that should own the `inmem_done` notification. The final notification's `is_last=true` flows from `inline_jit_codegen_for_names` at `src/worker.rs:2398` (`let is_last = i + 1 == total;`).

**Scope check**: The comment at `src/worker.rs:248-254` explicitly states this is a Wave-4 fix surfaced by persistent workers, not a drive-by refactor. The fix is minimal (two `false` flag changes + explanatory comments). No other scheduler notifications touched. **Correct fix, appropriate scope.**

**S-2**: The `is_last` concept is now split across two call-site patterns: "last in the batch" (`inline_jit_codegen_for_names` sets it correctly based on batch position) and "intermediate work item, never last" (macro-clause compiles always pass `false`). Consider renaming the parameter to `completes_module` or adding a doc note on `notify_inmem_codegen_complete` explaining the two roles — currently a reader must infer from usage that ancillary compiles always pass `false`. Cosmetic.
- **Owner**: `/int`. **Severity**: Suggestion. **Timing**: cosmetic.

### Focus 7 — `SharedState.lib_dirs` / `platform_dirs` in `Mutex`: **PASS**

**Verdict**: Snapshot-clone pattern is correct; no lock leakage into production paths.

- `lib_dirs: Mutex<Vec<PathBuf>>` (`src/session_v4.rs:481`) and `platform_dirs: Mutex<Vec<PathBuf>>` (`src/session_v4.rs:486`) are read by workers via `.lock().clone()` at the start of each work item (`src/worker.rs:3015-3018`). The lock is held only for the duration of the `clone()` (microseconds for a handful of `PathBuf`s); the subsequent per-compile code uses the local snapshot without re-locking.
- Doc-comment at `session_v4.rs:477-481` accurately describes the contract: "workers hold the lock only for the duration of a single read (rare per compile)."
- Main-thread mutators `set_lib_dirs` / `set_platform_dirs` / `push_platform_dir` (`src/session_v4.rs:796, 803, 810`) take `&mut self` — so they are called from the owning thread only, with the `Mutex` protecting against torn reads from workers mid-snapshot. The mutators hold the lock briefly to swap the vec; workers block on the next `.lock()` and observe the new snapshot. Correct by construction.
- Tests use these paths: `tests/wave4_g9.rs:65` + `tests/helpers/mod.rs` call `set_lib_dirs(vec![])` after `CompilerSession::new` returns but before any `register_module_with_source`. In production CLI code, these are called once at startup, zero times during the hot compile loop.

**Lock contention in production**: zero. The `Mutex` exists to make *tests* able to override dirs after workers have spawned — the `&mut self` mutator path is called from the main thread, workers never compete for the write lock, and the read lock (snapshot clone) is held only for a `Vec<PathBuf>::clone()` that touches O(lib_dirs.len()) heap allocations — typically 1-3 dirs. No measurable impact on the hot path.

**PASS with no follow-up.**

### Focus 8 — Decisions 25/26 cross-check: **PASS**

Grep confirms no Wave 4 changes to the Decision 25/26 serialisation fields:

- `ModuleEntry::Def.code: Option<Code>` with `#[serde(skip)]` — `crates/cranelisp-types/src/module.rs:152` unchanged from Wave 2.
- `ModuleEntry::Def.platform_fn_ptr: Option<*const u8>` with `#[serde(skip, default)]` — `:170` unchanged from Wave 3.
- `PrimitiveKind::PlatformEffect { scheduling_class }` variant-internal field — unchanged; `scheduling_class` serialises as Decision 26 asymmetry requires.
- `Code` type at `crates/cranelisp-types/src/code.rs` — pointer-only Shape 1, unchanged from Wave 2.
- `Code::ptr` default is `default_ptr()` returning `std::ptr::null()` — cache-hit loads re-initialise to `None`/null and codegen repopulates.

Wave 4 touched these types only indirectly (pushing `Arc<Jit>` to `kept_jits` on every compile; not mutating `code` field shape).

**PASS.**

### Focus 9 — FIXME hygiene: **PASS**

Grep for FIXMEs touched by Wave 4:

- `design/int/persistent-workers.md:206` — `FIXME(/int): Wave 4 + 1 — JIT rotation policy` — **valid forward-pointer; retained. However, the text preamble ("Wave 4 ships with a one-JIT-per-worker-for-session shape") is stale per Focus 3 / I-2** — the landed shape is per-compile-call, not per-worker. Needs update when I-2 resolves (either `/int` implements per-worker JIT, or the FIXME text gets rewritten to reflect per-compile-call reality).
- `design/int/persistent-workers.md:370` — `FIXME(/repl): measure REPL eval latency with 4 priority workers mid-compile` — valid forward measurement task.
- `src/session_v4.rs` — zero FIXMEs (grep-verified).
- `src/worker.rs` — zero FIXMEs (grep-verified).

No new unassigned FIXMEs filed. **PASS.**

## General findings

### Blocker findings

None.

### Important findings

**I-1** (see Focus 2): `process_single_form` + `compile_and_execute_expr` bypass the persistent worker pool for REPL eval; `persistent-workers.md §4.4` "eval submits through scheduler" not implemented. Owner: `/int`. Severity: Important. Timing: Sprint 58 follow-on; do not re-defer without user acceptance.

**I-2** (see Focus 3): Each `inline_jit_codegen_for_names` call builds a fresh `Jit`; `persistent-workers.md §4.5` / Decision 28's per-worker-thread-local JIT target not delivered. The landed shape IS the "Sprint 56 per-function JIT" that Decision 28 explicitly rejects ("the interim bridge … NOT a stepping stone"). Owner: `/int`. Severity: Important. Proposed resolutions: (a) implement thread-local reused JIT; (b) retract Decision 28 and update `persistent-workers.md:204-206`; (c) file tracking FIXME with "Sprint 58 rework" rationale.

### Suggestion findings

**S-1** (see Focus 4): Add `shutdown_race_mid_codegen` bounded-wait assertion (`< 500ms`) per `persistent-workers.md §9.1` target. Owner: `/int`. Severity: Suggestion. Timing: Sprint 58.

**S-2** (see Focus 6): Rename or doc-clarify the `is_last` parameter on `notify_inmem_codegen_complete` — the flag means "completes the module," not "last iteration of a loop." Owner: `/int` or `/arch`. Severity: Cosmetic.

**S-3**: `design/int/persistent-workers.md:204` preamble ("Wave 4 ships with a one-JIT-per-worker-for-session shape") is stale relative to the landed per-compile-call shape. Resolve when I-2 resolves (either update the preamble, or the implementation matches). Owner: `/int`. Severity: Tracking.

**S-4**: `tests/plan/ring4.md:676` lists `per_worker_jit_reused_across_work_items` as a target unit test (`Arc::ptr_eq` across two compiles on the same worker). Not written. If I-2 resolves via path (a), add this test; if via path (b), strike it from the plan. Owner: `/qa`. Severity: Tracking.

**S-5**: `src/worker.rs:1905 compile_dep_inline` runs `priority_worker_loop` (the inline variant with `ModuleCompiler`, not the persistent-worker variant) on the REPL main thread. This is the "REPL thread drives blocked-dep compile" path. Consistent with `process_single_form`'s inline style (I-1), so not a new divergence, but worth noting as a second call site that bypasses the persistent pool. Would also benefit from I-1's resolution.
- Owner: `/int`. Severity: Tracking.

## Pre-existing issues noted

**Clippy errors** (unchanged from Wave 2 and Wave 3 reports; per-crate verified):

| Crate | Status | Notes |
|---|---|---|
| `cranelisp-types` | clean ✓ | Decision 25/26 serialisation guards stable. |
| `cranelisp-typecheck` | clean ✓ | — |
| `cranelisp-backend` | 1 error ✗ | `compiler/mod.rs:569` (`collapsible_if`) — Sprint 55 origin. Unchanged by Wave 4. |
| `cranelisp` (binary, lib) | 4 warnings ✗ | `src/watch.rs:70, 71` (two), `src/worker.rs:1938` (one `collapsible_if`) — pre-existing per Wave 2 and Wave 3 reports. No new Wave 4 warnings. |

**Strict-reading interpretation of Wave 4 gate `cargo clippy clean`**: the backend pre-existing error fails the gate under `-D warnings`. Per Wave 2's recommendation, sweep all pre-existing clippy in Wave 6 or a dedicated cleanup sprint. No new clippy debt from Wave 4.

**Full-suite failure composition** (`/qa`'s report: 14 → 15):
- `/qa` attributes the +1 to tally drift: Sprint 56 close documented "3 sprint23 failures" but there were 4 in reality; Sprint 57 Wave 4 now surfaces the correct count of 4 rather than a +1 regression.
- I did not re-run the full suite per review guidance (one agent, one test run). Trust `/qa`'s attribution; the sprint23 tests are legitimately Phase-5-dependent per SPRINT.md §Wave 2 gate criterion.
- If it turns out to be a Wave-4 regression upon closer inspection, the most likely candidate is a race on `module_sexps` / `suspend_states` under persistent-pool concurrency that only manifests under the full-suite pressure — but no such race was observed during Wave 4 unit/integration tests, and the implementation's `.lock()` discipline is straightforward (lock-clone-release, never hold across compile).

## Verification spot-checks

Per review guidance, no `cargo nextest run` this review — trust `/qa`'s most-recent full-suite run. I verified the key structural assertions via grep and file read only:

| Check | Result |
|---|---|
| `thread::scope` outside `#[cfg(test)]` in `src/`, `crates/` | **Zero** (two `#[cfg(test)]`-gated survivors documented above). |
| `PriorityWorkerRefs` residual references in `src/` | **Zero** in production code; only historical references in `sprints/archive/`, `design/`. |
| `Jit::new_with_symbols` call sites in `src/` (production) | **Three** (`src/worker.rs:2474`, `src/pipeline.rs:107`, `src/pipeline.rs:189`) — all per-call, no thread-local reuse. Confirms Focus 3 / I-2. |
| `priority_worker_handles: Vec<JoinHandle<()>>` on `CompilerSession` | Present at `src/session_v4.rs:648`. Drained in `shutdown()` at `:2845`. |
| `resolve_priority_worker_count` clamping | Present at `src/session_v4.rs:610-619`; tests via `/int` unit tests (`test_session` helpers). |
| `SharedState.module_sexps`, `SharedState.suspend_states` | Present at `src/session_v4.rs:492, 498`. |
| `Code::code: Option<Code>` `#[serde(skip)]` | Unchanged from Wave 2 at `crates/cranelisp-types/src/module.rs:152`. |
| `platform_fn_ptr: Option<*const u8>` `#[serde(skip, default)]` | Unchanged from Wave 3 at `crates/cranelisp-types/src/module.rs:170`. |
| `cargo clippy -p cranelisp --lib` | 4 pre-existing warnings only. |
| `cargo clippy -p cranelisp-backend --lib` | 1 pre-existing error only. |

## Checklist walkthrough

Against `design/review/checklist.md`:

- **§1 Error Handling**: Worker-path code uses `?` + `CranelispError::ModuleError` consistently. `shutdown()` ignores `join()` errors via `let _ =` (documented as panic-tolerant). No new `unwrap()` in pipeline code. PASS.
- **§2 Code Structure**: `priority_worker_loop_shared` is 24 lines; `handle_typecheck_work_shared` is 124 lines (borderline but linear: snapshot → ctx → process → notify). Under the 100-line guideline, but the body is structurally simple (match-on-ProcessResult, three arms). Acceptable — decomposing further would introduce more parameter-threading. PASS.
- **§3 Naming**: Functions, structs follow Rust conventions. `SharedState.module_sexps` / `.suspend_states` / `.lib_dirs` / `.platform_dirs` use typed `HashMap<ModuleFullPath, …>` / `Vec<PathBuf>`. No bare `String` identifier regressions. PASS.
- **§5 Single Source of Truth**: `module_sexps` / `suspend_states` now exist in exactly ONE place (`SharedState`). Per-call local `Mutex<HashMap<…>>` constructions deleted per §7 deletion list. PASS.
- **§6 Duplication**: `priority_worker_loop` (inline variant, REPL-thread-driven) and `priority_worker_loop_shared` (persistent variant) coexist. This is the "two call sites, one conceptual loop" duplication that I-1 (REPL eval via inline loop) is rooted in. If I-1 resolves via routing REPL through scheduler, the inline variant can retire. Until then, two variants is the Wave-4 state. Documented in `src/worker.rs:2925-2933` comment. Acceptable with I-1 tracking.
- **§7 Architectural Boundaries**: No crate-boundary changes this wave. `Jit` construction remains in `cranelisp-backend`; session retains `Arc<Jit>`. PASS.
- **§7a Idiomatic Rust**: `std::thread::Builder::new().name("priority-worker-{i}").spawn(…)` pattern matches `std::thread` idiom. `JoinHandle` drained on shutdown, not on drop of individual handles (which would deadlock). `unsafe impl Send + Sync` on `KeptJit` (Wave 2) + `LoadedPlatform` (Wave 3) unchanged. PASS.
- **§8 Serialization**: Decision 25/26 serde-skip fields untouched. `#[serde(skip)]` on `code` and `platform_fn_ptr` preserved. PASS.
- **§9 Testing**: 4 `/int` unit tests (`persistent_worker_park_and_wake`, `shutdown_under_load_no_panic`, `concurrent_register_module_two_modules_complete`, `reload_during_compile_race_completes`) in `src/session_v4.rs:3979-4083`. 4 `/qa` integration tests in `tests/wave4_g9.rs` (concurrent register, reload during compile, per-worker JIT isolation cross-session, thread::scope absence). Unit-tests-with-dev principle honored. PASS for coverage; see S-1 for missing bounded-wait assertion.

## Unsafe code audit

Wave 4 introduces no new `unsafe` blocks. Pre-existing unsafe sites from Waves 2/3 remain:

| Site | Wave introduced | Status |
|---|---|---|
| `crates/cranelisp-types/src/code.rs:62-63` — `unsafe impl Send + Sync for Code` | Wave 2 | Unchanged. SAFETY comment accurate. |
| `crates/cranelisp-types/src/module.rs:229-240` — `unsafe impl Send + Sync for ModuleEntry` | Wave 2+3 | Unchanged. SAFETY comment accurate. |
| `src/session_v4.rs:437-438` — `unsafe impl Send + Sync for KeptJit` | Wave 2 | Unchanged. SAFETY comment accurate. |
| `src/platform.rs:39-40` — `unsafe impl Send + Sync for LoadedPlatform` | Wave 3 | Unchanged. SAFETY comment accurate. |

**Scattering risk**: unchanged. Unsafe surface remains contained to the four sites identified in Wave 2/3 reviews.

**Overall unsafe audit**: clean — no Wave 4 expansion.

## Design doc assessment

- **`design/int/persistent-workers.md`**: Comprehensive (12 sections). §4.1, §4.3, §4.6, §5.1, §5.2 correctly describe the landed code. §4.4, §4.5 describe a target shape **not fully delivered** — this is the content that I-1 + I-2 + S-3 flag. Update when resolutions land.
- **`design/int/phase2-codegen-convergence.md`** §13: unchanged by Wave 4; remains current per Wave 2 resolution.
- **`design/arch/CLAUDE.md` Decisions 25–29**:
  - Decision 25 (Code on entry, serde-skip): stable, no Wave 4 drift.
  - Decision 26 (platform placement): stable, no Wave 4 drift.
  - Decision 27 (G8 before G9): honored — Wave 3 (G8) landed before Wave 4 (G9), and the `PlatformRegistry` deletion's Mutex-swap removal WAS the precondition that made the persistent-worker refactor mechanical. **PASS**.
  - Decision 28 (per-worker JIT): **Not fully honored per Focus 3 / I-2.** The current shape is the "per-function JIT" that Decision 28 explicitly rejects.
  - Decision 29 (`rc::dec_shallow_io`): unchanged by Wave 4; remains current per Wave 3.

## Gate assessment

Wave 4 gate criterion (`sprints/SPRINT.md:552`):

- ✓ Workers persistent — `priority_worker_handles` + `nice_worker_handles` persist across the session; joined in `shutdown()` / `Drop`.
- ✓ No `thread::scope` for workers outside tests — Focus 1 verified; both survivors `#[cfg(test)]`-gated.
- △ "All cache + sprint23 cache/link failures either passing or clearly Phase 5-dependent" — 14 → 15 per `/qa`; attributed to Sprint 56 close's miscount (+1 pre-existing sprint23 failure surfaced). Accept pending `/sprint` pinning the exact failing test list.
- ✗ `cargo clippy` clean — strict reading fails due to 1 pre-existing backend error + 4 pre-existing binary warnings, none introduced by Wave 4. Same pre-existing gap Wave 2 and Wave 3 carried.

**Gate verdict**: Wave 4 is **cleared for close from the code-review perspective** on the persistent-worker correctness axis. The Important findings (I-1, I-2) are design-contract divergences that do not affect runtime correctness and the infrastructure is in place for follow-on work. The gate's strict clippy-clean reading has been pre-existingly violated since Sprint 55; Wave 6 should sweep.

## Summary

| Severity | Count |
|---|---|
| Blocker | 0 |
| Important | 2 (I-1 REPL eval bypasses persistent pool; I-2 per-worker JIT not delivered per Decision 28) |
| Suggestion | 5 |

Wave 4 may proceed to close (Wave 6 showcase) **with user acknowledgement that I-1 and I-2 are deferred once and cannot be deferred again without explicit sign-off**. The persistent-worker structural change landed cleanly; the remaining work is the per-worker JIT + REPL-via-scheduler that Decision 28 + §4.4/§4.5 specified but Wave 4 stopped short of. Headline recommendation: add both to Sprint 58 as explicit carry-overs rather than filing additional FIXMEs against the current state.
