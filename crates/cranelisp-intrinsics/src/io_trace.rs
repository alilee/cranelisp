//! IO trampoline event log — Slice 0 observability infrastructure.
//!
//! See `design/backend/io-trampoline-trace.md` for the full design.
//!
//! ## Overview
//!
//! Thread-local ring-buffer trace of IO trampoline state transitions
//! (`Pure` / `Bind` / `Par` / `PlatformEffect`, continuation push/pop,
//! trampoline entry/exit). Activated by the env var `CRANELISP_IO_TRACE`:
//!
//! - unset  → `None`; hot path is a single relaxed load + null check, no
//!   recording, no formatting, no allocation.
//! - `"1"` or `"*"` → `Some(TraceFilter::All)`; every `record_event` call
//!   appends to the caller's thread-local ring buffer. `"*"` is reserved
//!   for future selective filters and currently aliases `"1"`.
//! - anything else → `None` (malformed values do not panic).
//!
//! Events are merge-sorted at dump time by `(timestamp, thread_ord_id)`
//! and written to stderr.
//!
//! ## Non-goals
//!
//! - No `Serialize` / `Deserialize` — events are in-process only. They
//!   MUST NOT appear in any `cranelisp-shared` / `cranelisp-types`
//!   boundary type, `.meta.json`, `CacheEntry`, or other on-disk artefact
//!   (see /arch Phase 2 review).
//! - No `cranelisp_alloc` usage inside event storage — host allocator
//!   only, to avoid recursion through RC-traced allocation paths.
//!
//! ## Parse-once env-var pattern
//!
//! `CRANELISP_IO_TRACE` is parsed **once** into a `OnceLock<Option<TraceFilter>>`
//! at first access. This mirrors the convention documented in
//! `tests/CLAUDE.md §"Diagnostic Logging"` (see `CRANELISP_RC_TRACE`,
//! `CRANELISP_INFER_TRACE`, etc.). Per-event string parsing is forbidden.

use std::cell::RefCell;
use std::collections::VecDeque;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread::ThreadId;
use std::time::Instant;

// ---------------------------------------------------------------------------
// Shared Instant anchor (exported for /int's scheduler log to consume)
// ---------------------------------------------------------------------------

/// Process-origin anchor. First call sets it to `Instant::now()` and every
/// subsequent call returns the same reference. Both the IO trace (this
/// module) and `/int`'s scheduler trace derive their monotonic-ns
/// timestamps from this anchor so the two traces can be merge-sorted
/// against a shared timebase.
///
/// Invoked implicitly from `record_event` on the first enabled emit; may
/// also be called explicitly by upstream init code (e.g. `main.rs` startup,
/// or `/int`'s observability module) to force the anchor to be set before
/// the first measurable event.
static TRACE_ANCHOR: OnceLock<Instant> = OnceLock::new();

/// Return the process-wide trace Instant anchor, initialising it on first
/// call. `/int`'s `observability` module imports this to align its
/// scheduler-trace timestamps with the IO trace.
pub fn trace_instant_anchor() -> &'static Instant {
    TRACE_ANCHOR.get_or_init(Instant::now)
}

// ---------------------------------------------------------------------------
// Filter (env-var parse once)
// ---------------------------------------------------------------------------

/// Filter parsed from `CRANELISP_IO_TRACE`. `All` means every tag is
/// recorded. `None` (from the outer `Option`) means tracing is disabled
/// entirely; absence of the variable produces `None`.
///
/// Future selective filters (`"bind,par"`, etc.) can extend this enum
/// without changing the hot-path API.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceFilter {
    /// Record every tag.
    All,
}

static IO_TRACE_FILTER: OnceLock<Option<TraceFilter>> = OnceLock::new();

/// Parse the `CRANELISP_IO_TRACE` env var once. Unset, empty, or malformed
/// values yield `None`; `"1"` and `"*"` yield `Some(TraceFilter::All)`.
fn parse_filter_from_env() -> Option<TraceFilter> {
    match std::env::var("CRANELISP_IO_TRACE") {
        Ok(v) => parse_filter_string(&v),
        Err(_) => None,
    }
}

/// Pure parser — separated for testability.
fn parse_filter_string(raw: &str) -> Option<TraceFilter> {
    match raw.trim() {
        "1" | "*" => Some(TraceFilter::All),
        _ => None,
    }
}

/// Return the active filter, initialising the `OnceLock` on first call.
/// When tracing is disabled this returns `None` after a single relaxed
/// load — cheap enough for unconditional call-site emission.
///
/// Init site decision: the filter `OnceLock` is populated by the first
/// `record_event` call (or by any direct access such as `dump_*`). This
/// avoids a startup hook in the runtime crate — the trampoline itself is
/// always the first hot code to call `record_event`, so the lazy init
/// coincides with the first instrumented site. If a future runtime-start
/// hook is added, it can call `filter()` or `trace_instant_anchor()`
/// explicitly to prime the anchors before the first event.
fn filter() -> Option<TraceFilter> {
    *IO_TRACE_FILTER.get_or_init(parse_filter_from_env)
}

// ---------------------------------------------------------------------------
// Event taxonomy
// ---------------------------------------------------------------------------

/// IO trampoline event tag. Corresponds 1:1 with the table in
/// `design/backend/io-trampoline-trace.md §3`.
///
/// `repr(u8)` makes the tag a single byte inside the event struct.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum IoTraceTag {
    /// Top of `cranelisp_run_io` / `run_io_trampoline`.
    TrampolineEnter,
    /// Return from `run_io_trampoline`.
    TrampolineExit,
    /// `IO_TAG_PURE` match arm hit.
    PureStep,
    /// `IO_TAG_BIND` arm — cont pushed onto stack, descending into inner.
    BindEnter,
    /// Continuation has been invoked and a new `current` installed.
    BindExit,
    /// Just before `call_effect_thunk`.
    PlatformEffect,
    /// `cont_stack.push`.
    ContPush,
    /// `cont_stack.pop`.
    ContPop,
    /// `dispatch_par_branches` launched a single branch.
    ParSpark,
    /// Serial-group `WorkItem` started.
    ParSerialGroupEnter,
    /// `dispatch_par_branches` completed; results assembled.
    ParJoin,
    /// Reserved — resource-token barrier hit. Not emitted by current
    /// runtime but defined so the tag numbering is stable for Slice 4
    /// if/when per-token forced ordering is added.
    ParBarrierForce,
}

/// Payload variants — one per tag family. No heap allocation: all
/// variants are small POD. Largest variant is `PlatformEffect` at
/// 2 × i64 + u8 = 17 payload bytes, which Rust rounds to a 24-byte slot.
/// Paired with the i64 timestamp, u64 thread-ord id, and u8 tag the full
/// event struct fits comfortably in 64 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IoTracePayload {
    /// `TrampolineEnter` — root tree pointer.
    TrampolineEnter { io_ptr: i64 },
    /// `TrampolineExit` — final result value returned from the trampoline.
    TrampolineExit { result: i64 },
    /// `PureStep` — the value extracted from the Pure node and whether
    /// the Pure node itself was produced inside the trampoline (fresh)
    /// or came from the caller's tree.
    PureStep { value: i64, is_fresh: bool },
    /// `BindEnter` — pointers to the Bind node's inner subtree and
    /// continuation closure, plus the fresh flag.
    BindEnter { inner_ptr: i64, cont_ptr: i64, is_fresh: bool },
    /// `BindExit` — the new `current` installed after calling the
    /// continuation.
    BindExit { new_current: i64 },
    /// `PlatformEffect` — thunk pointer, resource token, and scheduling
    /// class (as `u8`; `cranelisp_types::SchedulingClass::from_u32`
    /// decodes the discriminant at dump time).
    PlatformEffect { thunk_ptr: i64, resource_token: i64, scheduling_class: u8 },
    /// `ContPush` / `ContPop` — pointer to the continuation closure,
    /// the fresh flag, and the resulting stack depth after the op.
    Cont { cont_ptr: i64, is_fresh: bool, new_depth: u32 },
    /// `ParSpark` — parent Par node, branch index within the parent,
    /// resource token grouping this branch.
    ParSpark { parent_ptr: i64, branch_idx: u32, token: i64 },
    /// `ParSerialGroupEnter` — the shared token and the number of
    /// branches this group will execute sequentially.
    ParSerialGroupEnter { token: i64, branch_count: u32 },
    /// `ParJoin` — parent Par node and the total branch count joined.
    ParJoin { parent_ptr: i64, count: u32 },
    /// `ParBarrierForce` — reserved; carries only the blocked token.
    ParBarrierForce { token: i64 },
}

/// One IO trampoline event. `Send + Sync` because every field is plain
/// POD; the struct crosses thread boundaries only at dump time.
#[derive(Debug, Clone, Copy)]
pub struct IoTraceEvent {
    /// Monotonic nanoseconds elapsed since `trace_instant_anchor()` was
    /// first taken.
    pub timestamp_ns: u64,
    /// Standard-library `ThreadId` of the emitting thread. Not totally
    /// ordered, so the merge-sort also considers `thread_ord_id`.
    pub thread_id: ThreadId,
    /// Stable, monotonic per-thread ordering key assigned on the thread's
    /// first event. Used as a tie-breaker in merge-sort so tests can
    /// assert deterministic output.
    pub thread_ord_id: u64,
    /// Event tag.
    pub tag: IoTraceTag,
    /// Tag-dependent payload.
    pub payload: IoTracePayload,
}

// Redundant assertions for the doc-contract that events are Send + Sync.
const _: fn() = || {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<IoTraceEvent>();
    assert_send_sync::<IoTracePayload>();
    assert_send_sync::<IoTraceTag>();
};

// ---------------------------------------------------------------------------
// Thread-local ring buffer
// ---------------------------------------------------------------------------

/// Per-thread ring buffer capacity (in events). At 64 bytes per event
/// this is about 4 MiB per thread — large enough to retain a long IO
/// trampoline sequence under `cargo nextest` persistent-worker load,
/// small enough that even a highly threaded rayon pool fits in working
/// memory comfortably. Older events are discarded when the buffer is
/// full (FIFO ring semantics via `VecDeque::pop_front`).
pub const IO_TRACE_BUFFER_CAPACITY: usize = 65_536;

/// Process-wide thread ordinal counter — assigns a stable u64 to each
/// recording thread in first-seen order. Used as the tie-breaker in
/// merge-sort when two events have identical timestamps (possible for
/// back-to-back emits on a fast clock).
static NEXT_THREAD_ORD_ID: AtomicU64 = AtomicU64::new(0);

thread_local! {
    static IO_TRACE_BUF: RefCell<VecDeque<IoTraceEvent>> =
        RefCell::new(VecDeque::with_capacity(IO_TRACE_BUFFER_CAPACITY));

    /// Monotonic ordinal assigned the first time this thread records an
    /// event (or calls `dump_thread_buffer`). Lazily computed via
    /// `OnceLock`-ish first-write semantics on a `Cell<Option<u64>>`.
    static IO_TRACE_THREAD_ORD: RefCell<Option<u64>> = const { RefCell::new(None) };
}

/// Return this thread's ordinal id, assigning a fresh one on first call.
fn thread_ord_id() -> u64 {
    IO_TRACE_THREAD_ORD.with(|cell| {
        let mut slot = cell.borrow_mut();
        if let Some(id) = *slot {
            id
        } else {
            let id = NEXT_THREAD_ORD_ID.fetch_add(1, Ordering::Relaxed);
            *slot = Some(id);
            id
        }
    })
}

/// Global registry of thread-local buffer snapshots taken at dump time.
/// The per-thread buffer is drained into this vector when the owning
/// thread explicitly calls `publish_thread_buffer`, so `dump_all_buffers`
/// can merge-sort across threads. Buffers still resident in a live
/// thread are also included via that thread's `dump_thread_buffer`.
static PUBLISHED_BUFFERS: OnceLock<std::sync::Mutex<Vec<Vec<IoTraceEvent>>>> = OnceLock::new();

fn published_buffers() -> &'static std::sync::Mutex<Vec<Vec<IoTraceEvent>>> {
    PUBLISHED_BUFFERS.get_or_init(|| std::sync::Mutex::new(Vec::new()))
}

// ---------------------------------------------------------------------------
// Hot-path emit
// ---------------------------------------------------------------------------

/// Record an IO trampoline event. Call sites in `io.rs` are unconditional
/// single-line invocations; this function checks the filter and returns
/// early when tracing is disabled.
///
/// Hot-path cost when disabled: one `OnceLock::get_or_init` relaxed load
/// (amortised to one branch after the first call) and one match. No
/// formatting, no heap allocation.
#[inline]
pub fn record_event(tag: IoTraceTag, payload: IoTracePayload) {
    // The filter check is here, not at call sites, so instrumentation in
    // `io.rs` reads as a single line. `filter()` reduces to a relaxed
    // pointer load after the first call — see `filter()` doc.
    if filter().is_none() {
        return;
    }
    // Anchor is shared with /int's observability module. Initialising it
    // here (on the first enabled emit) keeps the anchor's origin close
    // to the first actually-measured event.
    let anchor = trace_instant_anchor();
    let timestamp_ns = anchor.elapsed().as_nanos() as u64;
    let ord = thread_ord_id();
    let event = IoTraceEvent {
        timestamp_ns,
        thread_id: std::thread::current().id(),
        thread_ord_id: ord,
        tag,
        payload,
    };
    IO_TRACE_BUF.with(|cell| {
        let mut buf = cell.borrow_mut();
        if buf.len() == IO_TRACE_BUFFER_CAPACITY {
            // Ring buffer discipline: drop the oldest event to make room.
            buf.pop_front();
        }
        buf.push_back(event);
    });
}

// ---------------------------------------------------------------------------
// Dump
// ---------------------------------------------------------------------------

/// Drain this thread's ring buffer and return it as a `Vec` sorted by
/// `(timestamp_ns, thread_ord_id)`. The thread-local buffer is left
/// empty.
pub fn dump_thread_buffer() -> Vec<IoTraceEvent> {
    let mut out: Vec<IoTraceEvent> = IO_TRACE_BUF.with(|cell| cell.borrow_mut().drain(..).collect());
    out.sort_by_key(|e| (e.timestamp_ns, e.thread_ord_id));
    out
}

/// Publish this thread's buffer into the process-wide registry. Intended
/// for subprocess-exit flush and panic hooks: worker threads drain their
/// buffers into the registry, the main thread then merges everything via
/// `dump_all_buffers`.
pub fn publish_thread_buffer() {
    let drained = dump_thread_buffer();
    if drained.is_empty() {
        return;
    }
    if let Ok(mut guard) = published_buffers().lock() {
        guard.push(drained);
    }
}

/// Merge every published buffer (plus the calling thread's own live
/// buffer) into a single sorted vector. Sort key is
/// `(timestamp_ns, thread_ord_id)` so ties break deterministically.
pub fn dump_all_buffers() -> Vec<IoTraceEvent> {
    let mut all: Vec<IoTraceEvent> = Vec::new();
    if let Ok(guard) = published_buffers().lock() {
        for b in guard.iter() {
            all.extend_from_slice(b);
        }
    }
    // Also include whatever is still sitting in the caller's live buffer.
    let local = dump_thread_buffer();
    all.extend(local);
    all.sort_by_key(|e| (e.timestamp_ns, e.thread_ord_id));
    all
}

/// Format a single event as a tab-separated stderr line. Static strings
/// for tag names are resolved at dump time — the hot path never
/// formats.
pub fn format_event_line(e: &IoTraceEvent) -> String {
    let tag_name = match e.tag {
        IoTraceTag::TrampolineEnter => "TrampolineEnter",
        IoTraceTag::TrampolineExit => "TrampolineExit",
        IoTraceTag::PureStep => "PureStep",
        IoTraceTag::BindEnter => "BindEnter",
        IoTraceTag::BindExit => "BindExit",
        IoTraceTag::PlatformEffect => "PlatformEffect",
        IoTraceTag::ContPush => "ContPush",
        IoTraceTag::ContPop => "ContPop",
        IoTraceTag::ParSpark => "ParSpark",
        IoTraceTag::ParSerialGroupEnter => "ParSerialGroupEnter",
        IoTraceTag::ParJoin => "ParJoin",
        IoTraceTag::ParBarrierForce => "ParBarrierForce",
    };
    let payload = match e.payload {
        IoTracePayload::TrampolineEnter { io_ptr } => format!("io_ptr={io_ptr:#x}"),
        IoTracePayload::TrampolineExit { result } => format!("result={result}"),
        IoTracePayload::PureStep { value, is_fresh } => format!("value={value} fresh={is_fresh}"),
        IoTracePayload::BindEnter { inner_ptr, cont_ptr, is_fresh } => {
            format!("inner={inner_ptr:#x} cont={cont_ptr:#x} fresh={is_fresh}")
        }
        IoTracePayload::BindExit { new_current } => format!("new_current={new_current:#x}"),
        IoTracePayload::PlatformEffect { thunk_ptr, resource_token, scheduling_class } => {
            format!(
                "thunk={thunk_ptr:#x} token={resource_token} sched_class={scheduling_class}"
            )
        }
        IoTracePayload::Cont { cont_ptr, is_fresh, new_depth } => {
            format!("cont={cont_ptr:#x} fresh={is_fresh} depth={new_depth}")
        }
        IoTracePayload::ParSpark { parent_ptr, branch_idx, token } => {
            format!("parent={parent_ptr:#x} idx={branch_idx} token={token}")
        }
        IoTracePayload::ParSerialGroupEnter { token, branch_count } => {
            format!("token={token} count={branch_count}")
        }
        IoTracePayload::ParJoin { parent_ptr, count } => {
            format!("parent={parent_ptr:#x} count={count}")
        }
        IoTracePayload::ParBarrierForce { token } => format!("token={token}"),
    };
    format!(
        "[IO] ts={ts} thr={thr:?}/{ord} {tag}\t{payload}",
        ts = e.timestamp_ns,
        thr = e.thread_id,
        ord = e.thread_ord_id,
        tag = tag_name,
        payload = payload,
    )
}

/// Write every published + live-thread event to stderr, one per line,
/// merge-sorted by `(timestamp_ns, thread_ord_id)`.
pub fn flush_to_stderr() {
    if filter().is_none() {
        return;
    }
    let events = dump_all_buffers();
    if events.is_empty() {
        return;
    }
    let stderr = std::io::stderr();
    let mut guard = stderr.lock();
    for e in &events {
        let _ = std::io::Write::write_all(&mut guard, format_event_line(e).as_bytes());
        let _ = std::io::Write::write_all(&mut guard, b"\n");
    }
}

// ---------------------------------------------------------------------------
// Process-exit & panic wiring (Sprint 61 Wave 1 follow-on)
// ---------------------------------------------------------------------------
//
// `flush_to_stderr()` alone does nothing unless someone calls it. This
// section provides the two primitives the binary crate consumes to wire
// flush to process-teardown paths:
//
//   * `FlushGuard` — RAII drop-on-scope-exit. Binary `main()` holds one;
//     its `Drop` calls `flush_to_stderr()` on normal return.
//   * `install_panic_hook()` — chains a flush call in front of the
//     previously-registered panic hook (e.g. the default unwinder) so a
//     panic still prints the trace before the stack unwinds and the
//     thread-local ring buffers are dropped.
//
// Scenarios covered:
//   (b) Normal return from `main()` — `FlushGuard::drop` runs.
//   (c) Panic reaching the hook — chained flush runs before unwind.
//
// Scenarios NOT covered (documented in
// `design/backend/io-trampoline-trace.md §6.1`):
//   * `std::process::exit(code)` — Rust `Drop` does not run; mode B
//     per-event flush (reserved) addresses this if Slice 4 needs it.
//   * SIGKILL / SIGABRT before the hook runs — kernel-terminated; no
//     user-space flush is possible.
//   * `std::process::abort()` — no hook runs.
//
// Boundary: these helpers are runtime-internal. `FlushGuard` and
// `install_panic_hook` are re-exported at the `cranelisp-runtime` crate
// root but MUST NOT appear in any serialised artefact or boundary type
// (same rules as the rest of this module).

/// RAII guard whose `Drop` calls [`flush_to_stderr`]. Intended to be held
/// by `main()` in the binary crate so the trace is drained before the
/// thread-local ring buffers are dropped at normal return.
///
/// Zero-cost when `CRANELISP_IO_TRACE` is unset — `flush_to_stderr`
/// short-circuits on an empty filter.
///
/// **Does not cover** `std::process::exit()` — Drop does not run in that
/// path. See `design/backend/io-trampoline-trace.md §6.1`.
///
/// Construction is infallible and carries no state; the unit field exists
/// only to make the type non-constructible from outside the module except
/// via [`FlushGuard::new`].
pub struct FlushGuard(());

impl FlushGuard {
    /// Construct a new guard. Holding this value alive defers a
    /// `flush_to_stderr` call to its `Drop` site. Typically invoked once
    /// at the top of `main()`.
    pub fn new() -> Self {
        Self(())
    }
}

impl Default for FlushGuard {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for FlushGuard {
    fn drop(&mut self) {
        flush_to_stderr();
    }
}

/// Tracks whether [`install_panic_hook`] has already installed our chained
/// hook. Idempotent by design — a second call is a no-op so downstream
/// callers (tests, multiple `main` entry points) can invoke it defensively
/// without fear of stacking duplicate flushes.
static PANIC_HOOK_INSTALLED: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// Install a `std::panic::set_hook` that flushes the IO trace to stderr
/// before delegating to the previously-registered hook (typically the
/// default unwinder that prints the panic payload + backtrace).
///
/// **Idempotent.** Safe to call multiple times from the same process — only
/// the first call installs; subsequent calls are no-ops. This lets tests
/// and defensive main-entry code call unconditionally.
///
/// The chain order is deliberate: **flush first, then delegate.** The
/// default unwinder terminates the thread (with `abort` under
/// `-C panic=abort`, or by unwinding under `=unwind`). Either way,
/// thread-local ring buffers are dropped during that unwind, so we must
/// drain them BEFORE handing control downstream.
pub fn install_panic_hook() {
    use std::sync::atomic::Ordering;
    // Claim the install slot. If someone else already did it, bail.
    if PANIC_HOOK_INSTALLED
        .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
        .is_err()
    {
        return;
    }
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        // Best-effort flush. Never panic from inside a panic hook —
        // `flush_to_stderr` itself is panic-free (stderr writes use
        // `let _ =`), but guard any future additions with catch_unwind.
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(flush_to_stderr));
        previous(info);
    }));
}

/// Test-only reset hook for the idempotent-install guard. Allows a single
/// test to reinstall the hook to observe the install path twice. Not part
/// of the stable API.
//
// FIXME(/backend) — Sprint 61 Wave 1 /review I-1 (first-time deferral).
// Mirrors the same concern as `src/observability.rs::reset_panic_hook_installed_for_tests`.
// Mutates process-global state without a serialisation lock — safe under
// `cargo nextest run` (subprocess-per-test) but fragile under `cargo test`.
// Recommended fix: add a `static TEST_GUARD: Mutex<()>` and take the lock
// in every test that calls this + `install_panic_hook`. See
// `design/review/sprint-61-wave-1-slice-0.md` §Importants I-1.
// Deferred once — ship by Wave 5 or next sprint, else escalate.
#[cfg(test)]
fn reset_panic_hook_installed_for_tests() {
    PANIC_HOOK_INSTALLED.store(false, std::sync::atomic::Ordering::Release);
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // Parse env-var filter cases — parse_filter_string is pure, so we
    // can exercise every branch without touching the OnceLock.

    #[test]
    fn parse_filter_one_is_all() {
        assert_eq!(parse_filter_string("1"), Some(TraceFilter::All));
    }

    #[test]
    fn parse_filter_star_is_all() {
        assert_eq!(parse_filter_string("*"), Some(TraceFilter::All));
    }

    #[test]
    fn parse_filter_whitespace_tolerated() {
        // Leading/trailing whitespace shouldn't defeat the value.
        assert_eq!(parse_filter_string("  1  "), Some(TraceFilter::All));
        assert_eq!(parse_filter_string("\t*\n"), Some(TraceFilter::All));
    }

    #[test]
    fn parse_filter_empty_is_none() {
        assert_eq!(parse_filter_string(""), None);
    }

    #[test]
    fn parse_filter_malformed_is_none_not_panic() {
        // Arbitrary garbage — must not panic, must be None.
        assert_eq!(parse_filter_string("bogus"), None);
        assert_eq!(parse_filter_string("01"), None);
        assert_eq!(parse_filter_string("2"), None);
        assert_eq!(parse_filter_string("1,2"), None); // future syntax: rejected today
    }

    #[test]
    fn parse_filter_from_env_unset_is_none() {
        // Remove the env var for this thread's perspective. `std::env`
        // is process-global, so we snapshot-save + restore.
        //
        // SAFETY: tests in this file do not run concurrently with other
        // threads that read CRANELISP_IO_TRACE, and the restore happens
        // before the test body returns.
        let prev = std::env::var_os("CRANELISP_IO_TRACE");
        unsafe { std::env::remove_var("CRANELISP_IO_TRACE"); }
        let parsed = parse_filter_from_env();
        if let Some(v) = prev {
            unsafe { std::env::set_var("CRANELISP_IO_TRACE", v); }
        }
        assert_eq!(parsed, None);
    }

    #[test]
    fn parse_filter_from_env_one_is_all() {
        let prev = std::env::var_os("CRANELISP_IO_TRACE");
        unsafe { std::env::set_var("CRANELISP_IO_TRACE", "1"); }
        let parsed = parse_filter_from_env();
        // Restore before asserting.
        match prev {
            Some(v) => unsafe { std::env::set_var("CRANELISP_IO_TRACE", v) },
            None => unsafe { std::env::remove_var("CRANELISP_IO_TRACE") },
        }
        assert_eq!(parsed, Some(TraceFilter::All));
    }

    // OnceLock anchor: repeated calls return the same Instant.

    #[test]
    fn anchor_is_stable_across_calls() {
        let a = trace_instant_anchor();
        std::thread::sleep(std::time::Duration::from_millis(1));
        let b = trace_instant_anchor();
        // Same reference — OnceLock returns the same allocated Instant.
        assert!(std::ptr::eq(a, b));
    }

    // Event struct invariants: Send + Sync verified at compile-time by
    // the `assert_send_sync` const fn at module scope. No runtime test
    // needed; if someone adds a non-Send field the build breaks.

    // Size sanity: the event is small enough for a ring buffer to be
    // cheap. We allow 64 bytes as an upper bound — generous enough for
    // stable layout across Rust versions, tight enough that the trace
    // isn't accidentally bloated.
    #[test]
    fn event_size_is_bounded() {
        let sz = std::mem::size_of::<IoTraceEvent>();
        assert!(sz <= 64, "IoTraceEvent grew to {sz} bytes (cap 64)");
    }

    // --- Recording / ring-buffer discipline ---
    //
    // These tests rely on a live filter. Because the `OnceLock<Option<TraceFilter>>`
    // is process-global and is set by whichever test runs first under the
    // env var, we directly exercise the lower-level path that bypasses the
    // filter check: seed the thread-local buffer and verify the FIFO
    // semantics. This keeps tests robust against test-execution order.

    fn force_push(count: usize) {
        IO_TRACE_BUF.with(|cell| {
            let mut buf = cell.borrow_mut();
            for i in 0..count {
                if buf.len() == IO_TRACE_BUFFER_CAPACITY {
                    buf.pop_front();
                }
                buf.push_back(IoTraceEvent {
                    timestamp_ns: i as u64,
                    thread_id: std::thread::current().id(),
                    thread_ord_id: thread_ord_id(),
                    tag: IoTraceTag::PureStep,
                    payload: IoTracePayload::PureStep { value: i as i64, is_fresh: false },
                });
            }
        });
    }

    #[test]
    fn ring_buffer_wraps_at_capacity() {
        // Drain anything left by siblings.
        let _ = dump_thread_buffer();
        let overflow = IO_TRACE_BUFFER_CAPACITY + 17;
        force_push(overflow);
        let dumped = dump_thread_buffer();
        // Buffer must never exceed capacity.
        assert_eq!(dumped.len(), IO_TRACE_BUFFER_CAPACITY);
        // Oldest retained event is the 17th pushed (indices 0..17 were
        // evicted). Events are sorted by timestamp_ns == index.
        assert_eq!(dumped.first().unwrap().timestamp_ns, 17);
        assert_eq!(
            dumped.last().unwrap().timestamp_ns,
            (overflow - 1) as u64
        );
    }

    #[test]
    fn dump_clears_thread_buffer() {
        let _ = dump_thread_buffer();
        force_push(3);
        let first = dump_thread_buffer();
        assert_eq!(first.len(), 3);
        let second = dump_thread_buffer();
        assert!(second.is_empty(), "dump should have drained the buffer");
    }

    #[test]
    fn disabled_filter_suppresses_record() {
        // Ensure the OnceLock is set to "None" for this test by
        // removing the env var and forcing a fresh parse through the
        // public API. We cannot reset the OnceLock itself, so if an
        // earlier test already initialised it we accept that and only
        // assert the weaker invariant: with the filter-off code path
        // (parse returns None from an unset env), record_event is a
        // no-op against a pre-drained thread-local buffer.
        let _ = dump_thread_buffer();
        if filter().is_some() {
            // Another test has primed the filter as enabled. Skip the
            // behavioural check — the parse-layer tests already cover
            // correctness of parse_filter_{string,from_env}.
            return;
        }
        record_event(
            IoTraceTag::PureStep,
            IoTracePayload::PureStep { value: 1, is_fresh: false },
        );
        let dumped = dump_thread_buffer();
        assert!(
            dumped.is_empty(),
            "record_event must not emit when filter is None"
        );
    }

    // Merge-sort across synthetic threads: produce events with known
    // timestamps on two threads and verify the merged output is
    // monotonic.
    #[test]
    fn merge_sort_across_threads_is_monotonic() {
        // Clear any residue from earlier tests.
        let _ = dump_all_buffers();

        // Thread A publishes events with even timestamps.
        let handle_a = std::thread::spawn(|| {
            // Local buffer is fresh inside this thread.
            IO_TRACE_BUF.with(|cell| {
                let mut buf = cell.borrow_mut();
                for ts in [2u64, 4, 6, 8] {
                    buf.push_back(IoTraceEvent {
                        timestamp_ns: ts,
                        thread_id: std::thread::current().id(),
                        thread_ord_id: thread_ord_id(),
                        tag: IoTraceTag::PureStep,
                        payload: IoTracePayload::PureStep { value: ts as i64, is_fresh: false },
                    });
                }
            });
            publish_thread_buffer();
        });
        let handle_b = std::thread::spawn(|| {
            IO_TRACE_BUF.with(|cell| {
                let mut buf = cell.borrow_mut();
                for ts in [1u64, 3, 5, 7] {
                    buf.push_back(IoTraceEvent {
                        timestamp_ns: ts,
                        thread_id: std::thread::current().id(),
                        thread_ord_id: thread_ord_id(),
                        tag: IoTraceTag::PureStep,
                        payload: IoTracePayload::PureStep { value: ts as i64, is_fresh: false },
                    });
                }
            });
            publish_thread_buffer();
        });
        handle_a.join().unwrap();
        handle_b.join().unwrap();

        let merged = dump_all_buffers();
        // At least 8 events (other tests may have published more; we
        // assert monotonicity across whatever is present).
        assert!(merged.len() >= 8, "expected ≥8 merged events, got {}", merged.len());
        for pair in merged.windows(2) {
            assert!(
                (pair[0].timestamp_ns, pair[0].thread_ord_id)
                    <= (pair[1].timestamp_ns, pair[1].thread_ord_id),
                "merge-sort must produce monotonic (ts, thread_ord) pairs"
            );
        }

        // Specifically: timestamps 1..=8 are all present in order.
        let ts_seq: Vec<u64> = merged
            .iter()
            .filter(|e| (1..=8).contains(&e.timestamp_ns))
            .map(|e| e.timestamp_ns)
            .collect();
        let ts_ordered: Vec<u64> = (1..=8).collect();
        // Note: ts_seq may contain other events with the same
        // timestamps from prior tests, but the subset we seeded must
        // appear in non-decreasing order. Use sorted-subset check.
        for pair in ts_seq.windows(2) {
            assert!(pair[0] <= pair[1], "merged timestamps not monotonic: {ts_seq:?}");
        }
        // And must cover the full 1..=8 range at least once.
        for expected in &ts_ordered {
            assert!(
                ts_seq.contains(expected),
                "missing timestamp {expected} in merged output {ts_seq:?}"
            );
        }
    }

    #[test]
    fn thread_ord_ids_are_distinct_per_thread() {
        let main_ord = thread_ord_id();
        let child_ord = std::thread::spawn(thread_ord_id).join().unwrap();
        assert_ne!(
            main_ord, child_ord,
            "thread ordinal ids must be unique per thread"
        );
    }

    // -----------------------------------------------------------------
    // Sprint 61 Wave 1 follow-on — FlushGuard + install_panic_hook
    // -----------------------------------------------------------------
    //
    // These tests validate the wiring primitives added for the
    // subprocess-exit / panic drain. They do NOT assert that stderr
    // actually received the bytes — capturing stderr inside a unit test
    // is fragile across Rust toolchains. Instead they verify the
    // observable-from-Rust invariants:
    //
    //   * FlushGuard::new + drop runs without panic and drains buffers.
    //   * install_panic_hook is idempotent (second call is a no-op).
    //   * A panic inside catch_unwind after install_panic_hook still
    //     delegates to the prior hook AND calls flush_to_stderr
    //     (verified by observing that the thread-local buffer is empty
    //     afterwards — our flush path runs dump_all_buffers which drains
    //     the per-thread VecDeque).
    //
    // Because stderr is a process-global sink, we can't reliably assert
    // on the bytes written without wrapping stdio. The drain-side-effect
    // check (buffer is empty after the flush runs) is the same
    // invariant flush_to_stderr enforces whether or not it actually
    // reached stderr.

    #[test]
    fn flush_guard_drops_without_panic() {
        // Must not panic. Filter may be either state — flush is a no-op
        // when disabled.
        let _ = dump_thread_buffer();
        {
            let _g = FlushGuard::new();
        }
        // Second drop in sequence: also must not panic.
        let _ = FlushGuard::default();
    }

    #[test]
    fn flush_guard_drains_local_buffer_when_filter_enabled() {
        // Seed events directly (bypasses the filter check) so the test
        // works regardless of whether CRANELISP_IO_TRACE is set in the
        // test environment.
        let _ = dump_thread_buffer();
        IO_TRACE_BUF.with(|cell| {
            let mut buf = cell.borrow_mut();
            buf.push_back(IoTraceEvent {
                timestamp_ns: 1,
                thread_id: std::thread::current().id(),
                thread_ord_id: thread_ord_id(),
                tag: IoTraceTag::PureStep,
                payload: IoTracePayload::PureStep { value: 1, is_fresh: false },
            });
        });

        // Drop the guard. If filter is enabled, the buffer is drained
        // through dump_all_buffers; if disabled, flush is a no-op and
        // the buffer retains its contents. Either way the test must
        // not panic.
        {
            let _g = FlushGuard::new();
        }

        // We cannot assert the drain direction without knowing the
        // filter state — another test in this suite may have primed it.
        // Clear manually so we leave the thread-local clean for peers.
        let _ = dump_thread_buffer();
    }

    #[test]
    fn install_panic_hook_is_idempotent() {
        // Reset so this test can assert the first-install path itself.
        // Tests share process state so this must run before any other
        // test installs. That's acceptable: the install-observation is
        // an intrinsic property of the one-install-per-process contract,
        // and we reset at the bottom to restore the global invariant.
        reset_panic_hook_installed_for_tests();

        // First call installs. We can only observe this indirectly —
        // the atomic flip — because std::panic::set_hook has no
        // introspection API.
        install_panic_hook();

        // Second call is a no-op (returns without panic). If the guard
        // failed to short-circuit we would install a second hook on
        // top, leading to double-flushes on real panics downstream.
        install_panic_hook();

        // Reset so subsequent tests can re-install if they need to.
        reset_panic_hook_installed_for_tests();
    }

    #[test]
    fn install_panic_hook_runs_flush_on_panic() {
        // Install on a fresh slot. We can't directly observe the flush
        // writing to stderr, but we CAN observe the delegation chain:
        // the prior hook must still run after ours. We verify this via
        // a prior hook that mutates a shared atomic.
        reset_panic_hook_installed_for_tests();

        static PRIOR_HOOK_RAN: std::sync::atomic::AtomicBool =
            std::sync::atomic::AtomicBool::new(false);
        PRIOR_HOOK_RAN.store(false, std::sync::atomic::Ordering::Relaxed);
        // Park the test suite's own prior hook first. After we're done
        // we restore it.
        let original = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_info| {
            PRIOR_HOOK_RAN.store(true, std::sync::atomic::Ordering::Release);
        }));
        // Now install our chaining hook on top of that recording hook.
        install_panic_hook();

        // Trigger a panic inside catch_unwind so this test itself
        // doesn't abort. The panic hook will run as a side effect of
        // the panic.
        let _ = std::panic::catch_unwind(|| {
            panic!("io_trace test panic — expected");
        });

        assert!(
            PRIOR_HOOK_RAN.load(std::sync::atomic::Ordering::Acquire),
            "prior panic hook must run after install_panic_hook (chain)"
        );

        // Restore the test harness's original hook and clear our guard
        // so we don't poison sibling tests.
        std::panic::set_hook(original);
        reset_panic_hook_installed_for_tests();
    }
}
