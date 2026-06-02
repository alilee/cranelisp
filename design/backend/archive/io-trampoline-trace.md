# IO Trampoline Event Log (Slice 0)

**Owner**: `/backend`
**Sprint**: 61, Slice 0 (Foundational observability)
**Status**: IMPLEMENTED (Wave 1, 2026-04-22) — see `crates/cranelisp-runtime/src/io_trace.rs` + instrumentation in `crates/cranelisp-runtime/src/io.rs`. Wave 1 follow-on (2026-04-22): `FlushGuard` + `install_panic_hook` wiring primitives added to `io_trace.rs`; `/int`'s binary-crate hookup in `src/main.rs` lands separately. See §6.1 for the mode-A wiring mechanism.

**Post-implementation note (Wave 1)**: the `PlatformEffect.scheduling_class` payload field is emitted as `0` at call sites in `io.rs` because the `SchedulingClass` is registered on the platform symbol's `PlatformFn` manifest (see `cranelisp-platform::PlatformFn.scheduling_class`) and is not carried on the Effect IO node itself at runtime. FIXME(/backend) filed in `io.rs` at the `PlatformEffect` emit site: consider threading `SchedulingClass` into the Effect node payload (extra field) so trampoline events carry the real class without needing cross-trace correlation. Deferred pending Slice 4 evidence — if Slice 4 needs the class, correlate via `/int`'s scheduler trace (which does carry it on the scheduler side) or land the node-payload change then.
**Companion doc**: `design/int/observability.md` (owned by `/int`, authored in parallel). That doc is the overall trace-var inventory and methodology. **This doc is the `/backend`-owned IO-specific sibling** and is NOT duplicated there; `/int`'s doc cross-references this one.

## 1. Problem Statement

Sprint 60 closed with Defect #2 still open: `examples_run::every_example_file_runs_under_examples_prelude` fails intermittently when `examples/21-hello-io.cl` exits with code 201. The failure rate is sensitive to concurrent-subprocess load and nextest scheduling. Hypothesis-driven investigation has not converged because the IO trampoline's state machine — `Pure` → `Bind` → `Par` → `PlatformEffect` transitions, continuation stack moves, trampoline entry/exit — is entirely opaque at runtime.

Without per-event observability we cannot distinguish among Slice 4's three candidate hypotheses:

1. Continuation-state leak inside `run_io_trampoline` (runtime-owned).
2. Stdio platform DLL buffer ordering under concurrent subprocess load (`/platform`).
3. nextest subprocess-environment crosstalk (`/qa` + `/int`).

This doc specifies the observability that lets Slice 4 pin the correct hypothesis before any fix lands.

## 2. Env Var and Gating

- **`CRANELISP_IO_TRACE=1`** — flush per-event to stderr.
- **`CRANELISP_IO_TRACE=*`** — same as `1` for Sprint 61; reserved for future per-component filter syntax (e.g. `bind,par`) without re-parse cost.
- **Unset** — zero overhead: each event site is gated on `Option<&'static TraceFilter>` (single pointer load + null check), the filter is `None`.

**Parse-once discipline (resolves `FIXME(/backend)` from `/arch` Phase 2 review):** the env var is parsed **once** at runtime init into a `OnceLock<Option<TraceFilter>>`. Per-event string parsing is forbidden. This mirrors the established pattern documented in `tests/CLAUDE.md §"Diagnostic Logging"` alongside `CRANELISP_RC_TRACE`, `CRANELISP_INFER_TRACE`, `CRANELISP_CODEGEN_TRACE`, `CRANELISP_MODULE_TRACE`, `CRANELISP_MACRO_TRACE`.

```rust
// Shape (specification only — not implementation):
static IO_TRACE: OnceLock<Option<TraceFilter>> = OnceLock::new();
fn io_trace() -> Option<&'static TraceFilter> {
    IO_TRACE.get_or_init(|| parse_env("CRANELISP_IO_TRACE")).as_ref()
}
```

## 3. Event Taxonomy

Grounded in `crates/cranelisp-runtime/src/io.rs` (`run_io_trampoline`, `call_continuation`, `dispatch_par_branches`) and `spec/10-effects.md §10.12 bind!`, §10.10 platforms.

| Tag | Emitted at | Payload |
|---|---|---|
| `TrampolineEnter` | top of `cranelisp_run_io` | `io_ptr: i64` (root) |
| `TrampolineExit` | return from `cranelisp_run_io` | `result: i64`, `exit_cause: Ok \| PanicTag(u64)` |
| `PureStep` | `IO_TAG_PURE` match arm | `value: i64`, `is_fresh: bool` |
| `BindEnter` | `IO_TAG_BIND` arm on push-cont | `inner_ptr: i64`, `cont_ptr: i64`, `is_fresh: bool` |
| `BindExit` | continuation has been invoked | `new_current: i64` |
| `PlatformEffect` | `IO_TAG_EFFECT` just before `call_effect_thunk` | `thunk_ptr: i64`, `resource_token: i64`, `scheduling_class: u8` |
| `ContPush` | cont_stack.push | `cont_ptr: i64`, `is_fresh: bool`, `new_depth: u32` |
| `ContPop` | cont_stack.pop | `cont_ptr: i64`, `is_fresh: bool`, `new_depth: u32` |
| `ParSpark` | `dispatch_par_branches` — each rayon work item launched | `parent_ptr: i64`, `branch_idx: u32`, `token: i64` |
| `ParSerialGroupEnter` | serial-group WorkItem start | `token: i64`, `branch_count: u32` |
| `ParJoin` | `dispatch_par_branches` collected all results | `parent_ptr: i64`, `count: u32` |
| `ParBarrierForce` | *reserved* — resource-token barrier hit (if/when per-token forced ordering is added) | `token: i64` |

**Not in Sprint 61 scope**: `ParBind` independence-analysis edges. `io.rs` as it stands does not carry independence metadata across the Par boundary; the independence analysis lives upstream in `/backend` codegen, not in the runtime trampoline. A future sprint may emit codegen-side `IndepEdge` events; Sprint 61 does not.

## 4. Event Struct Shape

```rust
// Specification only.
pub struct IoTraceEvent {
    pub timestamp_ns: u64,        // std::time::Instant::elapsed from a process-start anchor
    pub thread_id: ThreadId,      // std::thread::current().id()
    pub tag: IoTraceTag,          // repr(u8) enum
    pub payload: IoTracePayload,  // inline enum; no heap allocation per event
}
```

- `IoTracePayload` is an inline `enum` — the largest variant (`PlatformEffect`, 3 × i64 + u8) fits in ≤32 bytes. **No `Box`, no `String`** per event. Static string labels for tag names are resolved at dump time.
- `IoTraceEvent: Send + Sync` — enforced by the field types. The struct crosses thread boundaries only at dump time (merge-sort across per-thread ring buffers).
- `IoTraceEvent` is **never** serialised: no `Serialize`, no appearance in `.meta.json`, no inclusion in any `CacheEntry`, `Code`, `SymbolTable`, or other `cranelisp-shared` / `cranelisp-types` boundary type.

## 5. Crate Placement (pinned by `/arch` Phase 2 review)

- **Module**: new file `crates/cranelisp-runtime/src/io_trace.rs` (name chosen to avoid conflict with the existing `crates/cranelisp-runtime/src/trace.rs`, which implements the `(trace ...)` special-form call-stack recorder and is unrelated).
- **Crate**: `cranelisp-runtime` only. The IO trampoline is runtime-owned; the event taxonomy mirrors the runtime's state machine and has no reason to exist in any other crate.
- **State**: thread-local ring buffer (`thread_local! { static IO_TRACE_BUF: RefCell<VecDeque<IoTraceEvent>> }`).
- **Forbidden**: events MUST NOT appear in `cranelisp-shared`, `cranelisp-types`, or any serialised format (`.meta.json`, cache entry, any on-disk artefact).
- **Allocator**: events allocate via the host allocator (std's `VecDeque`). They **must not** go through `cranelisp_alloc` — observing RC-traced heap allocations from a log whose own storage is RC-traced would create unbounded recursion inside `rc::inc`/`rc::dec` trace paths.

## 6. Dump Format

**Two modes, one flag** (Sprint 61 ships mode A only; mode B reserved by syntax):

- **Mode A (`CRANELISP_IO_TRACE=1`)**: **accumulate in per-thread ring buffers, flush at subprocess exit.** Registered via `std::panic::set_hook` + a RAII guard held in `main()`. Events are merge-sorted by `(timestamp_ns, thread_id)` at flush time and written to stderr as one line per event (tab-separated fields, human-readable tag names, hex pointers). See §6.1 for the wiring mechanism.

- **Mode B (`CRANELISP_IO_TRACE=*`, reserved)**: **flush per-event to stderr.** Higher interleave noise, higher overhead, but survives process crash (kernel flushes the FD buffer on SIGSEGV / SIGABRT). Reserved for Slice 4 investigation of exit-201 if mode A's end-of-process flush turns out to be lost.

**Trade-off recorded**: mode A gives clean, merge-sorted output but loses the tail on process crash. Mode B gives crash-resilient output at the cost of interleaved stderr and higher runtime cost. Slice 4 picks the mode per evidence need; the default (`=1`) is A.

## 6.1 Mode A Wiring Mechanism (Sprint 61 Wave 1 follow-on)

`flush_to_stderr()` alone is inert — something has to call it at process teardown. Options considered:

1. **`libc::atexit`** — platform-specific `unsafe`; fragile across macOS / Linux / Windows.
2. **Drop of a `main()`-owned RAII guard** — fires on normal return; does NOT fire on `std::process::exit()`.
3. **Panic hook** — fires on panic; does NOT fire on normal return.
4. **Explicit `flush_to_stderr()` at end of `main`** — fires on normal return; redundant once (2) exists.
5. **Static destructor (`ctor`/`dtor` crate)** — new dependency; Rust statics are not guaranteed to `Drop`.

**Chosen mechanism: combine (2) + (3) — `FlushGuard` RAII + `install_panic_hook` chained flush.** This matches the mode A spec (mode A = "flush at subprocess exit"), uses no `unsafe` beyond what Rust's own panic hook already provides, adds no dependency, and is mirrored by `/int`'s scheduler-trace wiring so the two logs drain in a consistent pattern.

Exported primitives live in `crates/cranelisp-runtime/src/io_trace.rs`:

```rust
pub struct FlushGuard(());               // Drop impl calls flush_to_stderr()
impl FlushGuard { pub fn new() -> Self; }
pub fn install_panic_hook();             // Idempotent (AtomicBool guard).
                                         // Chains flush BEFORE the prior hook.
```

Both are re-exported at the `cranelisp-runtime` crate root as `IoTraceFlushGuard` and `io_trace_install_panic_hook`. `/int`'s binary `main.rs` consumes the API in a follow-on wave; this `/backend` slice lands the primitives only — it does NOT touch `src/main.rs`.

### Scenarios covered

- **(A) Normal `main()` return (including non-zero exit).** `FlushGuard::drop` runs on scope exit. The `examples/21-hello-io.cl` happy path returns a sum-of-passes from `main`, which is the exit shape Slice 0's AC exercises.
- **(B) Panic reaching the hook.** `install_panic_hook` chains `flush_to_stderr` **before** the previously-registered hook (typically the default unwinder printing the panic payload + backtrace). The chain order is important: the default unwinder terminates the thread, dropping thread-local ring buffers in the process, so we must drain first.

### Scenarios NOT covered

- **`std::process::exit(code)`** — Rust `Drop` does not run on this path. If Slice 4 observes that the exit-201 failure uses `process::exit` rather than returning from `main`, mode B (per-event flush, currently reserved) is the fallback. For Slice 0's AC (`examples/21-hello-io.cl`), this does not matter: the example returns from `main` normally.
- **`std::process::abort()`** — no hook runs.
- **Process killed by SIGKILL / SIGABRT before the hook executes** — kernel-terminated; no user-space flush is possible. Mode B's per-event stderr writes are the only mitigation and are reserved for future evidence need.
- **Thread-local buffers on worker threads that outlive `main`** — Rust drops TLS as part of thread teardown. The `dump_all_buffers` path the guard calls publishes the main-thread buffer + any previously-`publish_thread_buffer`'d worker buffers. Worker threads that never explicitly publish their buffer before `main` returns lose their events. This matches the existing behaviour and is documented rather than fixed — the instrumented code path (`run_io_trampoline`) is single-threaded on a given Par branch; worker-thread events are captured by the per-branch `publish` calls in `dispatch_par_branches` (Slice 4 will verify this end-to-end).

### Idempotency

`install_panic_hook` uses an `AtomicBool` compare-exchange. The second and subsequent calls return without installing. This lets tests, libraries, and multiple `main` entry points call unconditionally — stacking duplicate hooks would produce N flushes per panic.

### Boundary compliance

`FlushGuard` and `install_panic_hook` are runtime-internal helpers. They do NOT appear in `cranelisp-shared`, `cranelisp-types`, any serialised format, or any cache entry. They exist at the `cranelisp-runtime` crate boundary only to let the binary crate (`src/main.rs`, /int-owned) consume them.

## 7. Performance

- **Acceptance gate**: off-path regression `< 1%` on `cargo nextest run`, measured as wall-clock delta on 5 consecutive runs of the full suite with `CRANELISP_IO_TRACE` unset vs baseline.
- **Gate cost**: each event site compiles to `if IO_TRACE.get().and_then(...).is_some() { … }`. After `OnceLock` init, the hot path is a single relaxed-load + null check. No formatting, no allocation when disabled.
- **On-path cost**: when enabled, each event is a `VecDeque::push_back` of a ≤32-byte struct into a thread-local buffer. No locks on the hot path; the merge-sort lock is acquired only at flush.

## 8. Sketch Comparison

Per `CLAUDE.md §"Sketch Oracle"`.

- **What the sketch does**: the sketch's `cranelisp-runtime/src/intrinsics.rs` contains the ancestor trampoline. IO tracing in the sketch is **ad hoc**: a single `eprintln!("cranelisp_run_io: unknown IO tag {}", tag);` on the panic-shape error path (line 301) and nothing else. There is no structured event log, no env-var gate, no per-transition observation.
- **Follow or diverge**: **diverge.** The reimplementation runs the IO trampoline under `rayon` inside `dispatch_par_branches` and under persistent-worker subprocess concurrency via nextest. Ad-hoc `eprintln!` at a single error site is useless for the intermittent races Sprint 61 is closing — events from concurrent subprocesses would interleave unreadably and the happy path would produce no evidence at all. Structured events with explicit `(timestamp_ns, thread_id)` and merge-sortable dump are required.
- **Rationale for divergence**: the sketch predates (a) `rayon`-backed `Par` dispatch (Decision 26), (b) the persistent-worker topology (Decision 27), and (c) the exit-201 race that motivates this instrumentation. The sketch's observability surface is not a design choice; it is an absence. Adopting it would recreate the opacity this slice is installing observability to eliminate.

## 9. Acceptance Criteria

1. `CRANELISP_IO_TRACE=1 cargo run -- --run examples/21-hello-io.cl` produces a full trampoline event sequence from `TrampolineEnter` through at least one `PlatformEffect` to `TrampolineExit`, ending at process exit code. Output is merge-sorted by `(timestamp_ns, thread_id)`.
2. Off-path performance regression `< 1%` on `cargo nextest run` (5-run wall-clock median, unset vs baseline).
3. Events are merge-sortable with `/int`'s scheduler trace (`CRANELISP_SCHEDULER_TRACE`) at debug time. **Shared timestamp domain**: both traces use the same monotonic-nanosecond anchor (`Instant::now()` at process start, stored in a runtime-exported `OnceLock<Instant>`). `thread_id` values come from `std::thread::ThreadId` in both traces. This lets Slice 4 correlate IO events with `/int`-side scheduler state changes by interleaving the two dumps on timestamp.
4. `cargo check -p cranelisp-runtime` zero warnings. `cargo nextest run -p cranelisp-runtime --no-fail-fast` passes. (Slice 0 implementation gate, not this design gate.)

## 10. Slice 4 Outlook

This event log is the instrument. No investigation doc (`design/backend/example-21-hello-io.md` or similar) is authored until the log produces evidence.

The three hypotheses from `sprints/SPRINT.md §Slice 4` that this infrastructure discriminates:

1. **Trampoline continuation-state leak** (`/backend`-owned if confirmed): a `ContPush` without matching `ContPop` across a `TrampolineEnter`/`TrampolineExit` span, or a `BindEnter` whose `is_fresh=true` closure never shows up in a subsequent `ContPop`-with-consumed-dec.
2. **Stdio DLL buffer ordering** (`/platform`-owned if confirmed): `PlatformEffect` events with `scheduling_class` indicating stdio, timing-correlated with exit 201 across concurrent subprocesses. Signature: same thunk invoked, different outcomes.
3. **Nextest subprocess crosstalk** (`/qa` + `/int` if confirmed): IO trace looks identical between passing and failing runs — exit 201 originates outside the trampoline. Signature: `TrampolineExit { result: …, exit_cause: Ok }` in a subprocess that nonetheless exits 201 at the OS level.

Slice 4 readout names the hypothesis by citing specific event-log dumps. Until then, this doc's job is to specify the instrument; no further design commitment is made.

## 11. Cross-References

- `design/int/observability.md` — `/int`-owned companion; overall trace-var inventory, scheduler/worker event log, merge-sort methodology. Consult for the non-IO half.
- `tests/CLAUDE.md §"Diagnostic Logging"` — env-var parse-once pattern; existing `CRANELISP_*_TRACE` conventions.
- `crates/cranelisp-runtime/src/io.rs` — state machine whose transitions this doc instruments. Line references: `run_io_trampoline` (l.91), `call_continuation` (l.240), `dispatch_par_branches` (l.283).
- `spec/10-effects.md §10.12 bind!`, `§10.10 platforms` — spec-level definition of Pure/Bind/Par/PlatformEffect.
- `design/backend/io-trampoline.md` — existing trampoline design (instrumented by this doc, not replaced).
- `design/backend/io-scheduling.md §5.2` — Par branch dispatch algorithm; `ParSpark` / `ParSerialGroupEnter` / `ParJoin` events shadow its phases.
