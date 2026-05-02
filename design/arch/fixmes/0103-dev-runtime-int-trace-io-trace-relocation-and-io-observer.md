---
number: 0103
target: /dev
filed_by: /arch
filed_at: 2026-05-02
sprint_filed: 64
refers_to: design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md, design/arch/facades/runtime.md §"IO observation (extension point)", design/runtime/runtime.md §10, crates/cranelisp-runtime/src/trace.rs, crates/cranelisp-runtime/src/io_trace.rs, crates/cranelisp-runtime/src/io.rs, src/
status: open
---

# Decision 40 implementation: relocate `trace.rs` + `io_trace.rs` from runtime to int; runtime exposes `IoObserver` contract

## Issue

Decision 40 commits to two coordinated changes:

1. **Relocate** `crates/cranelisp-runtime/src/trace.rs` (~740 LOC) and `crates/cranelisp-runtime/src/io_trace.rs` (~952 LOC) from `cranelisp-runtime` to `src/` (int). These files implement per-thread `VecDeque` ring buffers for diagnostics — they are int's observability concern, not the runtime's BC. Their current residence in runtime is the BC-vs-implementation drift identified in S64.
2. **Replace** the in-runtime call sites in `io.rs` (~17 invocations of `io_trace::record_event`) and elsewhere with a callback-driven `IoObserver` contract per `facades/runtime.md` §"IO observation (extension point)". Runtime exposes `register_io_observer(Option<IoObserver>)`; int's session startup registers when REPL/trace mode is on or `CRANELISP_IO_TRACE=1`. Production batch (`--link`, non-trace `--run`) does not register and pays one relaxed null-check load per call site.

The contract is fully designed (`facades/runtime.md` carries `IoEvent`, `IoObserver`, `register_io_observer`); the implementation has not yet caught up.

This is distinct from FIXME 0098 (multi-crate `ResolutionGap`/`CheckError`/`ExpansionError` migration — types-and-signatures work) and from FIXME 0099 (GotObserver implementation — backend's parallel observer contract). Three observability-pattern FIXMEs that share architectural shape but are independent work units.

## Proposed resolution

**Phase 1 — `cranelisp-runtime`** (`/dev` narrow to runtime):

1. Land the observer contract in `crates/cranelisp-runtime/src/io_observer.rs`:
   - `IoEventTag` enum (variants per `facades/runtime.md` — `EffectInvoke`, `EffectComplete`, `BindStart`, `BindComplete`, `ParStart`, `ParComplete`, `IvarSpark`, `IvarForce`, `#[non_exhaustive]`).
   - `IoEvent` struct carrying the event payload (resource token, scheduling class, depth, etc.).
   - `IoObserver` fn type.
   - `register_io_observer(observer: Option<IoObserver>)` with relaxed-load null-check pattern.
2. Wire `io.rs`'s ~17 `io_trace::record_event` call sites to invoke the observer (with relaxed-load null check; no-op if unregistered) emitting the corresponding `IoEvent`. Remove the `io_trace::*` direct dependency from `io.rs`.
3. Wire the existing `consume_trace_call` and other trace.rs touch points similarly — replace direct `trace::record_*` calls with observer dispatch.
4. Strip the `pub use io_trace::{IoTraceEvent, IoTracePayload, IoTraceTag, ...}` and `pub use trace::{cranelisp_trace_*, ...}` blocks from `crates/cranelisp-runtime/src/lib.rs`. Add `pub use io_observer::{IoEventTag, IoEvent, IoObserver, register_io_observer}` per facade.
5. Delete `crates/cranelisp-runtime/src/trace.rs` and `crates/cranelisp-runtime/src/io_trace.rs` from runtime — their content moves to int (Phase 2).

**Phase 2 — `src/` (int)** (`/dev` narrow to int):

1. Create `src/io_trace/` (parallel to `src/scheduler_trace/`):
   - Per-thread `VecDeque<IoEvent>` ring buffer with FIFO overflow (matching the existing capacity convention).
   - Env-var activation: `CRANELISP_IO_TRACE=1` enables the observer. Also enabled when REPL/trace mode is on.
   - `flush_to_stderr` formatter for end-of-session dump.
   - `record(tag, event)` is the registered observer fn.
2. Create `src/trace/` for the broader scheduler-trace machinery currently in `crates/cranelisp-runtime/src/trace.rs`. Most of `trace.rs`'s content is already int-side concerns (scheduler-cadence trace events from `src/observability.rs`); the runtime-side functions (`cranelisp_trace_*` extern fns called from JIT-emitted code) become observer-driven and the file's int-side content moves over.
3. Int's session startup registers the observer when activated:
   ```rust
   if shared.introspection.is_some() || env::var("CRANELISP_IO_TRACE").is_ok() {
       cranelisp_runtime::register_io_observer(Some(int::io_trace::record));
   }
   ```
4. Production batch (`--link`, non-trace `--run`) does NOT register and pays one relaxed null-check load per IO call site.

## Sequencing notes

- Phase 1 (runtime) is prerequisite for Phase 2 (int) — int needs the `IoEvent` type from runtime to populate the ring buffer.
- Bundles naturally with FIXME 0099 (GotObserver) — both establish observability extension points following the same pattern. Could land in the same wave under one `/dev` triad if scope permits, or sequentially.
- Independent of FIXME 0098 (the typed-error migration) and FIXME 0100 (Principle 15 type relocation).
- After Phase 1, `crates/cranelisp-runtime/src/` shrinks from ~6700 LOC to ~4990 LOC (~25% reduction). The runtime's BC §4 statement aligns with implementation reality for the first time since Sprint 26.

## Operational implication / Context

This closes the largest remaining BC-vs-implementation drift in the workspace. Runtime's BC §4 ("primitive operations and runtime services for compiled Cranelisp code") is correct as written; the `trace.rs`/`io_trace.rs` residence is the drift. Decision 40 chose relocation over BC revision because the diagnostic ring buffer pattern is unambiguously an integration-layer concern (parallel to int's existing `src/observability.rs`).

The post-relocation runtime is consistent with Principle 15 (runtime owns its types — `IoEvent`, `IoObserver`, etc.) and consistent with the project's three-instance observability pattern (alongside `io_trace` already partially in int, `scheduler_trace` in int, and the GOT observer per FIXME 0099).
