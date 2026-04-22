# Observability: scheduler and IO trampoline event logs

**Owner**: `/int` + `/backend` (co-authored per Sprint 61 Slice 0)
**Status**: DESIGN (Sprint 61 Phase 3, 2026-04-22)
**Reviewers**: `/arch` (boundary-type hygiene, crate placement)

## 1. Purpose

Sprint 61 closes four defects serially. Two of them — the scheduler/worker
publish-vs-flag heisenbug (Slice 3) and the intermittent `21-hello-io` exit
201 (Slice 4) — are concurrency-shape failures that will not yield to
hypothesis-driven investigation. They need structured, merge-sortable event
logs across threads. Slice 0 lands the two logs before race-diagnosis work
starts.

Ad hoc `eprintln!` is insufficient: persistent-worker concurrency interleaves
events across threads, the output is not merge-sortable by a consistent
clock, and stderr contention distorts timing. Slices 3 and 4 need evidence,
not traces that need careful reading to disambiguate.

## 2. Existing trace infrastructure (inventory)

The project already publishes an env-var-gated trace pattern. Canonical list
in `tests/CLAUDE.md §"Diagnostic Logging"`. One line each:

| Variable | Observes | Code site |
|---|---|---|
| `CRANELISP_RC_TRACE=1` | Every alloc, inc, dec, free with pointer + type | `crates/cranelisp-runtime/src/rc.rs` |
| `CRANELISP_INFER_TRACE=1` | Unification steps, constraint generation | `crates/cranelisp-typecheck/` |
| `CRANELISP_CODEGEN_TRACE=1` | CLIF IR before/after optimisation (per-fn) | `crates/cranelisp-backend/src/` |
| `CRANELISP_CODEGEN_DUMP=1` | Full CLIF dump to file | `crates/cranelisp-backend/src/` |
| `CRANELISP_MODULE_TRACE=1` | Module discovery, compile order, cache hits | `src/session_v4.rs`, `src/worker.rs` |
| `CRANELISP_MACRO_TRACE=1` | Macro expansion steps (per-clause) | `crates/cranelisp-frontend/src/expander.rs` |

Shape in common: each reads the env var **once** at session start (or module
load) and stores a parsed filter. Per-event env-var parse is forbidden —
it is O(events) work on the fast path and `std::env::var` takes the process
env lock. Sprint 61 adds two new variables consistent with this discipline.

## 3. New variables

### 3.1 `CRANELISP_SCHEDULER_TRACE=1|<module_name>|*`

Observes: scheduler/worker state transitions. Event taxonomy:

- `ModuleState` pool transitions: `Unregistered → TypecheckNext`,
  `TypecheckNext → TypecheckWorking`, `TypecheckWorking → TypecheckBlocked`,
  `TypecheckBlocked → TypecheckWorking`, `TypecheckWorking → TypecheckDone`,
  `TypecheckDone → Complete`, `* → Failed`, `Failed → (removed)`.
- `register_dep publish` — publish-before-register ordering guard
  (`src/worker.rs:1342 register_dep`, Sprint 58 W6 Defect 1 and S59
  Workstream A §7).
- `register_module register` — module first enters the scheduler.
- `register_module_cached register` — cached-module fast path
  (`src/scheduler.rs:329`).
- `is_typechecked` fast-path: hit (returns true), miss (returns false).
  Payload records the `ModulePool` value observed.
- `clear_module_state`, `re_register_module`, `reset_module`,
  `reset_all_failed_modules` — the four scheduler mutations that resurface
  modules.
- `recompile_module` — REPL-side trigger (`src/session_v4.rs`).

**Filter values**:
- `1` — enable for all modules.
- `<module_name>` (e.g., `user`, `prelude`, `user.test`) — only events
  whose `module` payload matches.
- `*` — alias for `1`.

**Code site**: `src/` (binary crate). Thread-local ring buffer. New module
`src/observability.rs` (preferred) or an inline submodule of
`src/session_v4.rs`. The scheduler and worker are `src/`-owned; their
event log is an observation of integration-layer state that does not cross
any crate boundary.

### 3.2 `CRANELISP_IO_TRACE=1|*`

Observes: IO trampoline state transitions. Event taxonomy is owned by
`/backend` in `design/backend/io-trampoline-trace.md` (authored in
parallel). Covered classes: `Pure` / `Bind` / `Par` node transitions,
platform-fn invocations with scheduling class, continuation push/pop,
process exit code. Refer to that doc for the full event struct.

This doc owns the **env-var name** and **the crate-placement decision**;
the full event taxonomy is in the runtime-side design.

**Code site**: `cranelisp-runtime`. Thread-local ring buffer. New module
`crates/cranelisp-runtime/src/io_trace.rs` — not `trace.rs`, which is
already occupied by the `(trace ...)` special form runtime. The IO
trampoline is runtime-owned; its event taxonomy matches the runtime's
state machine. See `design/backend/io-trampoline-trace.md` §Crate
Placement for the /backend-side decision record.

## 4. Crate placement — architectural decision (MANDATORY)

Locked in by `/arch` Phase 2 review. Recorded here so the implementation
cannot drift.

| Log | Crate | Rationale |
|---|---|---|
| Scheduler/worker events | `src/` | Scheduler is `src/`-owned (`src/scheduler.rs`, `src/worker.rs`). Event taxonomy follows scheduler state machine. |
| IO trampoline events | `cranelisp-runtime` | Trampoline is runtime-owned (`crates/cranelisp-runtime/src/io.rs`). Event taxonomy follows runtime state machine. |

**Hard constraints (enforced by `/arch` review):**

- **Neither log appears in any boundary type.** Not in `cranelisp-shared`,
  not in `cranelisp-types`, not as a field on `SymbolTable<C, L>` or
  `ModuleEntry` or any other cross-crate struct. Event types are
  runtime-only. `#[serde(skip)]` does not need to apply because these types
  never appear on any serialised struct.
- **Neither log appears in any serialised format.** Not in `.meta.json`
  (cache), not in on-disk artifacts, not in module bundles. Events are
  in-memory only, process-lifetime only.
- **Neither log allocates on the Cranelisp heap.** No calls to
  `cranelisp_alloc`. Host allocator only. Mixing RC-traced allocations
  into a trace that observes RC-traced allocations risks infinite
  recursion (the trace observing its own allocations observing its own
  allocations…). `std::sync::Mutex<VecDeque<Event>>` or a lock-free ring
  (e.g., `crossbeam-queue`) is correct.
- **`Send + Sync` explicit.** Event structs derive or manually implement
  `Send + Sync`. Thread-local ring buffers are the default emission path;
  cross-thread merge-sort happens at dump time, not during recording.

Neither log is a `cranelisp-shared` concern. `cranelisp-shared` is stable
(Principle 3); the scheduler and IO trampoline are integration-layer state
machines whose event shape will evolve with the scheduler/runtime, not
with the shared-types surface.

## 5. Env-var parse-once pattern

Mandatory. Per-event parse is forbidden.

```rust
use std::sync::OnceLock;

static FILTER: OnceLock<TraceFilter> = OnceLock::new();

pub fn filter() -> &'static TraceFilter {
    FILTER.get_or_init(|| TraceFilter::from_env("CRANELISP_SCHEDULER_TRACE"))
}

pub enum TraceFilter {
    Off,
    All,
    Module(ModuleFullPath),
}

impl TraceFilter {
    fn from_env(var: &str) -> Self {
        match std::env::var(var).as_deref() {
            Ok("1") | Ok("*") => TraceFilter::All,
            Ok(s) if !s.is_empty() => TraceFilter::Module(ModuleFullPath::from(s)),
            _ => TraceFilter::Off,
        }
    }
}
```

The IO trace uses an identical pattern on its own static. Zero-cost when
off: `filter()` returns a `&'static TraceFilter::Off` after the first
call; the recording call sites are `if !matches!(filter(), Off) { … }`
and the branch predicts well.

## 6. Event struct shape

Both logs share a common shape (each crate owns its own type — not a
shared type in `cranelisp-types`). Fields:

- `timestamp: u64` — monotonic nanoseconds from a per-process origin
  (`std::time::Instant::now().duration_since(ORIGIN).as_nanos()`).
- `thread_id: u64` — `std::thread::current().id().as_u64().get()`.
- `tag: EventTag` — enum naming the event (per §3.1 and §3.2 taxonomies).
- `payload: EventPayload` — tag-dependent data. Scheduler: module path,
  pool transition, or flag value. IO: node type, scheduling class, or
  exit code.

`Send + Sync` derivable because all fields are plain data. No references,
no locks, no JIT handles.

**Why monotonic ns (not wall-clock)**: the merge-sort across threads must
be stable. Wall-clock time can skew. `Instant::now()` is monotonic and
sufficient for ordering.

## 7. Dump format

Per-thread ring buffer, merged at dump time.

- **Scheduler log**: dumped at **process exit + panic hook**, via the
  RAII + panic-hook pair landed in `src/observability.rs` and consumed
  by `src/main.rs` (see §7.1). Dump goes to stderr, preceded by a
  marker line `=== CRANELISP_SCHEDULER_TRACE DUMP ===`.

- **IO log**: dumped **continuously to stderr**, one line per event, as
  events occur. Rationale: IO exit 201 is a subprocess-termination
  failure; by the time the parent detects exit 201, the subprocess is
  gone and its ring buffer with it. Streaming is necessary. Format: one
  event per line, `[ns=..., tid=..., tag=..., payload=...]`.

**Merge-sort across threads (scheduler log)**: at dump time, drain each
thread-local ring into a `Vec<Event>`, then `sort_by_key(|e| (e.timestamp,
e.thread_id))`. Tie-break on thread_id ensures stable output. Emit sorted
sequence to stderr.

**Thread-local storage**: `thread_local! { static BUF: RefCell<VecDeque<Event>> = … }`
with a bounded capacity (say 8192). On overflow, drop oldest (ring
semantics) and increment a per-thread drop counter reported at dump time.
Bounded capacity matters for long test runs.

### 7.1 Process-exit and panic wiring (Sprint 61 Wave 1 follow-on)

`flush_to_stderr()` is not self-triggering — something has to call it.
Three primitives land in `src/observability.rs` and are consumed by
`src/main.rs`:

1. **`SchedulerTraceFlushGuard`** — RAII. `main()` holds one at the top
   of `fn main()`; its `Drop` calls `flush_to_stderr()` on normal
   return. Zero cost when the filter is `None` (flush short-circuits).
2. **`install_panic_hook()`** — idempotent `std::panic::set_hook`
   installer. Chains `flush_to_stderr()` in front of the previously
   registered hook so a panic reaches the trace dump before the stack
   unwinds and the thread-local ring buffers are dropped. Guarded by
   an `AtomicBool` so repeated calls from tests / multiple main
   entry points are safe.
3. **Worker-side `publish_thread_buffer()` on shutdown** — the
   priority-worker and nice-worker loops each publish their thread-
   local ring buffer into the process-wide registry when they exit,
   so the main thread's `dump_all_buffers` (invoked from
   `flush_to_stderr`) can merge worker events into the dump. Without
   this the dump shows only main-thread events (worker-thread
   `ModuleStateTypechecking` etc. would be dropped when those threads
   terminate).

This mirrors the `/backend`-side pattern in
`crates/cranelisp-runtime/src/io_trace.rs` (see
`design/backend/io-trampoline-trace.md §6.1`) — one RAII guard, one
idempotent panic hook, documented at the same shape so a consumer sees
a uniform API across both traces.

**`main.rs` consumption pattern.**

```rust
fn main() {
    // Observability — flush scheduler + IO traces on normal exit AND panic.
    cranelisp_runtime::io_trace_install_panic_hook();
    observability::install_panic_hook();
    let _io_flush = cranelisp_runtime::IoTraceFlushGuard::new();
    let _sched_flush = observability::SchedulerTraceFlushGuard::new();
    // ... existing main body ...
}
```

**Scenarios covered:**

| Path | Mechanism |
|---|---|
| `main()` returns normally (Repl, Link modes) | Guard `Drop` |
| Panic reaches the top-level hook | Chained panic hook |
| Run-mode `process::exit(exit_code)` (spec §12.6) | Explicit `flush_traces()` call immediately before `process::exit` |
| `run()` returned `Err(_)` → `process::exit(1)` | Explicit `flush_traces()` call immediately before `process::exit` |

**Scenarios NOT covered** (documented for parity with
`io-trampoline-trace.md §6.1`):

- **`std::process::exit` from argv-parse error paths** — fires before
  any scheduler event is emitted. The ring buffers are empty, so
  flushing would be a no-op anyway; the call sites are left as
  unconditional `process::exit(1)` for clarity.
- **`std::process::abort()`** — no hook runs. Not used by the binary
  but possible through stdlib panics under `panic=abort`.
- **SIGKILL / SIGABRT before the hook runs** — kernel-terminated; no
  user-space flush is possible. The 21-hello-io Slice 4 defect falls
  under this category (subprocess aborts before flush), so IO-trace
  tests for that example continue to fail for orthogonal reasons.

## 8. Sketch comparison

`CLAUDE.md §"Sketch Oracle"` requires this section. The sketch's session
(`sketch/src/session.rs`) uses ad hoc `eprintln!` scattered at
investigation points — no structured event log, no thread-awareness, no
merge-sort support. Events interleave randomly with other stderr output.

**Reimplementation diverges because persistent-worker concurrency makes
ad hoc tracing useless.** The sketch is single-threaded; sequential
stderr output is readable there. Our scheduler (Decision 27, G9) runs a
persistent worker pool; events from 4–8 threads interleave in stderr and
cannot be reconstructed into a causal sequence. The structured log with
monotonic-ns timestamps + per-thread rings + dump-time merge-sort is
necessitated by the concurrent topology.

Divergence rationale: sketch's pattern does not scale to the target
concurrent shape. Sketch also has no IO trampoline (IO is synchronous in
the sketch, see `sketch/audits/`), so no precedent for the IO log exists.

## 9. Performance

Off-path regression budget: **< 1%** on `cargo nextest run`. Verified by:

1. Measure baseline: 3 × `cargo nextest run --no-fail-fast` wall-clock
   median.
2. Measure post-Slice-0: 3 × `cargo nextest run --no-fail-fast`
   (CRANELISP_*_TRACE unset) wall-clock median.
3. Regression = (post − baseline) / baseline. Must be < 1%.

Achieved by:
- `OnceLock` filter check is ~5ns.
- Disabled path is `if cold_branch { … }` with LLVM cold hint.
- No atomic writes on the disabled path.
- Event struct construction is only on the enabled path.

## 10. Testing

Acceptance criterion (Sprint 61 Slice 0):

```bash
CRANELISP_SCHEDULER_TRACE=1 cargo nextest run \
  sprint23::cache_repl_loads_heisenbug_parallel_stress
```

Produces, on failure, a dump to stderr with events from at least two
threads, merge-sortable (ordering is stable), covering at least one
failing iteration and at least one passing iteration if the harness
iterates.

```bash
CRANELISP_IO_TRACE=1 cargo run -- --run examples/21-hello-io.cl
```

Produces a full trampoline event sequence ending at process exit. Events
include `Pure` / `Bind` transitions and `exit` with an exit code.

Unit tests inside `src/` and `cranelisp-runtime`: each crate owns tests
for its own ring buffer — enable/disable via env-var, bounded-capacity
drop counter, `Send + Sync` compile-time check, parse-once assertion
(the second call to `filter()` must not re-read the env).

## 11. References

- `tests/CLAUDE.md §"Diagnostic Logging"` — existing env-var naming pattern.
- `design/int/concurrent-workers.md`, `design/int/persistent-workers.md` —
  scheduler/worker topology whose transitions are being observed.
- `design/backend/io-trampoline-trace.md` (parallel authorship,
  `/backend`-owned) — IO trampoline event taxonomy.
- `crates/cranelisp-runtime/src/io.rs` + `spec/10-effects.md §10.12` —
  IO trampoline state machine.
- `design/arch/concurrent-pipeline.md §7` — form-by-form scheduler's
  pool-state-transition protocol (what Slice 3 observes via this log).
- Sprint 60 Wave 2 Round 4 — publish-vs-flag race precedent that
  motivated `is_typechecked` and the publish-before-register discipline
  recorded in `src/worker.rs::register_dep`.

## 12. Sprint 62+ durability

The two logs are durable infrastructure, not Sprint 61 scaffolding:

- Scheduler event taxonomy tracks the persistent-worker topology. Per
  `pipeline-v4.md §3` and Decision 27 (G9 complete), this topology is
  stable Ring 4 onwards. The scheduler-log event shape does not churn
  with ring progression.
- IO event taxonomy tracks spec-frozen surface (`spec/10-effects.md
  §10.12 bind!`, §10.10 platforms). Spec stability implies event-shape
  stability.

Both logs become standing inspection instruments after Sprint 61. Future
race investigations reach for them directly instead of starting with
ad hoc traces.
