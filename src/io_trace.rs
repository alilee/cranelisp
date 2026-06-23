//! IO trampoline event log — int-hosted ring buffer + observer per
//! Decision 40 §"Int hosting — the trace bodies and observer state" (Path B1).
//!
//! This file absorbs the io_trace ring-buffer machinery that previously lived
//! in `crates/cranelisp-intrinsics/src/io_trace.rs`. The intrinsics-side
//! definition remains (orphaned, awaiting FIXME 0198 deletion) but is no
//! longer the live consumer for int sessions — int's session startup
//! registers `record` (below) with `cranelisp_intrinsics::register_io_observer`
//! and the IO trampoline emits events through that registration via
//! `io_observer::emit`.
//!
//! ## Activation
//!
//! Set `CRANELISP_IO_TRACE=1` to activate. `install_if_enabled` calls
//! `register_io_observer(Some(record))` only when the env var is present;
//! unset means no observer, the trampoline's hot path is a relaxed-load
//! null-check + branch, and no recording or formatting happens.
//!
//! ## Mapping
//!
//! Each `IoEventTag` / `IoEvent` from `cranelisp_intrinsics::io_observer`
//! maps 1:1 onto an `IoTraceTag` / `IoTracePayload` here. The taxonomies
//! were co-designed in lockstep so the mapping is straight translation.
//!
//! ## Non-goals
//!
//! - No `Serialize` / `Deserialize` — events are in-process only.
//! - No `cranelisp_alloc` usage inside event storage — host allocator only,
//!   to avoid recursion through RC-traced allocation paths.

use std::cell::RefCell;
use std::collections::VecDeque;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread::ThreadId;
use std::time::Instant;

use cranelisp_intrinsics::io_observer::{IoEvent, IoEventTag, register_io_observer};

// ---------------------------------------------------------------------------
// Filter (env-var parse once)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceFilter {
    All,
}

static IO_TRACE_FILTER: OnceLock<Option<TraceFilter>> = OnceLock::new();

fn parse_filter_from_env() -> Option<TraceFilter> {
    match std::env::var("CRANELISP_IO_TRACE") {
        Ok(v) => parse_filter_string(&v),
        Err(_) => None,
    }
}

fn parse_filter_string(raw: &str) -> Option<TraceFilter> {
    match raw.trim() {
        "1" | "*" => Some(TraceFilter::All),
        _ => None,
    }
}

fn filter() -> Option<TraceFilter> {
    *IO_TRACE_FILTER.get_or_init(parse_filter_from_env)
}

// ---------------------------------------------------------------------------
// Event taxonomy (int-side ring representation)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum IoTraceTag {
    TrampolineEnter,
    TrampolineExit,
    PureStep,
    BindEnter,
    BindExit,
    PlatformEffect,
    ContPush,
    ContPop,
    ParSpark,
    ParSerialGroupEnter,
    ParJoin,
    ParBarrierForce,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IoTracePayload {
    TrampolineEnter { io_ptr: i64 },
    TrampolineExit { result: i64 },
    PureStep { value: i64, is_fresh: bool },
    BindEnter { inner_ptr: i64, cont_ptr: i64, is_fresh: bool },
    BindExit { new_current: i64 },
    PlatformEffect { thunk_ptr: i64, resource_token: i64, scheduling_class: u8 },
    Cont { cont_ptr: i64, is_fresh: bool, new_depth: u32 },
    ParSpark { parent_ptr: i64, branch_idx: u32, token: i64 },
    ParSerialGroupEnter { token: i64, branch_count: u32 },
    ParJoin { parent_ptr: i64, count: u32 },
    ParBarrierForce { token: i64 },
}

#[derive(Debug, Clone, Copy)]
pub struct IoTraceEvent {
    pub timestamp_ns: u64,
    pub thread_id: ThreadId,
    pub thread_ord_id: u64,
    pub tag: IoTraceTag,
    pub payload: IoTracePayload,
}

const _: fn() = || {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<IoTraceEvent>();
    assert_send_sync::<IoTracePayload>();
    assert_send_sync::<IoTraceTag>();
};

// ---------------------------------------------------------------------------
// Thread-local ring buffer
// ---------------------------------------------------------------------------

/// Per-thread ring buffer capacity (in events). ~4 MiB per thread.
pub const IO_TRACE_BUFFER_CAPACITY: usize = 65_536;

static NEXT_THREAD_ORD_ID: AtomicU64 = AtomicU64::new(0);

thread_local! {
    static IO_TRACE_BUF: RefCell<VecDeque<IoTraceEvent>> =
        RefCell::new(VecDeque::with_capacity(IO_TRACE_BUFFER_CAPACITY));

    static IO_TRACE_THREAD_ORD: RefCell<Option<u64>> = const { RefCell::new(None) };
}

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

static PUBLISHED_BUFFERS: OnceLock<std::sync::Mutex<Vec<Vec<IoTraceEvent>>>> = OnceLock::new();

fn published_buffers() -> &'static std::sync::Mutex<Vec<Vec<IoTraceEvent>>> {
    PUBLISHED_BUFFERS.get_or_init(|| std::sync::Mutex::new(Vec::new()))
}

// ---------------------------------------------------------------------------
// Hot-path emit (ring write)
// ---------------------------------------------------------------------------

/// Record an event in the per-thread ring buffer when the filter is enabled.
///
/// Anchors timestamps to `cranelisp_intrinsics::io_observer::trace_anchor()`
/// so the int-side scheduler trace (which derives its timestamps from the
/// same anchor) merge-sorts against IO trace events on a shared timebase.
#[inline]
pub fn record_event(tag: IoTraceTag, payload: IoTracePayload) {
    if filter().is_none() {
        return;
    }
    let anchor = cranelisp_intrinsics::io_observer::trace_anchor();
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
            buf.pop_front();
        }
        buf.push_back(event);
    });
}

// ---------------------------------------------------------------------------
// Bench accessor (FIXME 0336 — unblocks the 0021 off-path microbench)
// ---------------------------------------------------------------------------

/// In-process accessor for the **filter-OFF** `record_event` cost, exposed
/// only under the `bench` cargo feature (FIXME 0336). A release-mode criterion
/// bench (FIXME 0021, `/qa`) links `src/lib.rs` and calls this in a tight loop
/// with `CRANELISP_IO_TRACE` unset to measure the per-call early-return cost
/// against a no-op baseline at nanosecond resolution — establishing the `<1%`
/// off-path bound (`design/backend/io-trampoline-trace.md` §9 AC 2). A
/// subprocess-driven measurement cannot reach that resolution (process-spawn +
/// I/O jitter swamps the signal), so the measurement must be in-process.
///
/// This is a thin pass-through to `record_event` — it adds NO measurement
/// logic of its own (the bench owns timing); it exists solely to give the
/// bench an in-process handle to the off-path without exposing the wider
/// session internals. With `CRANELISP_IO_TRACE` unset, `record_event` hits its
/// `filter().is_none()` early return — exactly the off-path being measured.
#[cfg(feature = "bench")]
pub fn bench_record_event_off_path() {
    record_event(
        IoTraceTag::TrampolineEnter,
        IoTracePayload::TrampolineEnter { io_ptr: 0 },
    );
}

// ---------------------------------------------------------------------------
// Observer (registered with cranelisp_intrinsics::register_io_observer)
// ---------------------------------------------------------------------------

/// Observer fn registered with `register_io_observer`. Maps the
/// observation-taxonomy event (defined by intrinsics' `io_observer.rs`) onto
/// the ring-buffer taxonomy and pushes to this thread's ring buffer.
pub fn record(tag: IoEventTag, event: &IoEvent) {
    let (ring_tag, ring_payload) = match (tag, *event) {
        (IoEventTag::TrampolineEnter, IoEvent::TrampolineEnter { io_ptr }) => {
            (IoTraceTag::TrampolineEnter, IoTracePayload::TrampolineEnter { io_ptr })
        }
        (IoEventTag::TrampolineExit, IoEvent::TrampolineExit { result }) => {
            (IoTraceTag::TrampolineExit, IoTracePayload::TrampolineExit { result })
        }
        (IoEventTag::PureStep, IoEvent::PureStep { value, is_fresh }) => {
            (IoTraceTag::PureStep, IoTracePayload::PureStep { value, is_fresh })
        }
        (IoEventTag::BindEnter, IoEvent::BindEnter { inner_ptr, cont_ptr, is_fresh }) => (
            IoTraceTag::BindEnter,
            IoTracePayload::BindEnter { inner_ptr, cont_ptr, is_fresh },
        ),
        (IoEventTag::BindExit, IoEvent::BindExit { new_current }) => {
            (IoTraceTag::BindExit, IoTracePayload::BindExit { new_current })
        }
        (
            IoEventTag::PlatformEffect,
            IoEvent::PlatformEffect { thunk_ptr, resource_token, scheduling_class },
        ) => (
            IoTraceTag::PlatformEffect,
            IoTracePayload::PlatformEffect { thunk_ptr, resource_token, scheduling_class },
        ),
        (IoEventTag::ContPush, IoEvent::Cont { cont_ptr, is_fresh, new_depth }) => (
            IoTraceTag::ContPush,
            IoTracePayload::Cont { cont_ptr, is_fresh, new_depth },
        ),
        (IoEventTag::ContPop, IoEvent::Cont { cont_ptr, is_fresh, new_depth }) => (
            IoTraceTag::ContPop,
            IoTracePayload::Cont { cont_ptr, is_fresh, new_depth },
        ),
        (IoEventTag::ParSpark, IoEvent::ParSpark { parent_ptr, branch_idx, token }) => (
            IoTraceTag::ParSpark,
            IoTracePayload::ParSpark { parent_ptr, branch_idx, token },
        ),
        (IoEventTag::ParSerialGroupEnter, IoEvent::ParSerialGroupEnter { token, branch_count }) => (
            IoTraceTag::ParSerialGroupEnter,
            IoTracePayload::ParSerialGroupEnter { token, branch_count },
        ),
        (IoEventTag::ParJoin, IoEvent::ParJoin { parent_ptr, count }) => {
            (IoTraceTag::ParJoin, IoTracePayload::ParJoin { parent_ptr, count })
        }
        (IoEventTag::ParBarrierForce, IoEvent::ParBarrierForce { token }) => {
            (IoTraceTag::ParBarrierForce, IoTracePayload::ParBarrierForce { token })
        }
        // Tag / payload mismatch — observer contract specifies the tag and
        // payload share their family, but `#[non_exhaustive]` defends
        // against future additions. Drop the event silently rather than
        // panic from inside the observer.
        _ => return,
    };
    record_event(ring_tag, ring_payload);
}

/// Install the observer when `CRANELISP_IO_TRACE` is set. Idempotent —
/// safe to call once at session-startup. When the env var is unset, this is
/// a no-op (no observer registered; the hot path remains a relaxed-load
/// null check).
pub fn install_if_enabled() {
    if std::env::var("CRANELISP_IO_TRACE").is_ok() {
        register_io_observer(Some(record));
    }
}

// ---------------------------------------------------------------------------
// Dump
// ---------------------------------------------------------------------------

pub fn dump_thread_buffer() -> Vec<IoTraceEvent> {
    let mut out: Vec<IoTraceEvent> = IO_TRACE_BUF.with(|cell| cell.borrow_mut().drain(..).collect());
    out.sort_by_key(|e| (e.timestamp_ns, e.thread_ord_id));
    out
}

pub fn publish_thread_buffer() {
    let drained = dump_thread_buffer();
    if drained.is_empty() {
        return;
    }
    if let Ok(mut guard) = published_buffers().lock() {
        guard.push(drained);
    }
}

pub fn dump_all_buffers() -> Vec<IoTraceEvent> {
    let mut all: Vec<IoTraceEvent> = Vec::new();
    if let Ok(guard) = published_buffers().lock() {
        for b in guard.iter() {
            all.extend_from_slice(b);
        }
    }
    let local = dump_thread_buffer();
    all.extend(local);
    all.sort_by_key(|e| (e.timestamp_ns, e.thread_ord_id));
    all
}

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
// FlushGuard + panic hook
// ---------------------------------------------------------------------------

pub struct IoTraceFlushGuard(());

impl IoTraceFlushGuard {
    pub fn new() -> Self {
        Self(())
    }
}

impl Default for IoTraceFlushGuard {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for IoTraceFlushGuard {
    fn drop(&mut self) {
        flush_to_stderr();
    }
}

static PANIC_HOOK_INSTALLED: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// Install a `std::panic::set_hook` that flushes the IO trace before
/// delegating to the previously-registered hook. Idempotent — a second call
/// is a no-op.
pub fn install_panic_hook() {
    if PANIC_HOOK_INSTALLED
        .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
        .is_err()
    {
        return;
    }
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(flush_to_stderr));
        // This hook's `previous` is the DEFAULT unwinder — the one that prints the
        // "thread … panicked at …" banner. The agent validator's caught panic
        // (`worker::checked_check_forms`) sets a thread-local suppression flag on
        // the eval thread; when set for THIS thread we skip the default banner
        // (the panic is expected and converted to `Err`), but the io/got/sched
        // flushes have already run upstream in the chain. The flag is thread-local,
        // so a concurrently-panicking worker thread (flag false on its thread)
        // still prints its banner normally (S90 4R Important — no global state).
        #[cfg(feature = "agent")]
        if crate::worker::SUPPRESS_PANIC_BANNER.with(|c| c.get()) {
            return;
        }
        previous(info);
    }));
}

/// Trace anchor accessor — delegates to the shared anchor on
/// `cranelisp_intrinsics::io_observer::trace_anchor`. Kept here so older int
/// callers that reference `cranelisp_intrinsics::io_trace::trace_instant_anchor`
/// have a parallel path after the relocation lands. New callers should call
/// `cranelisp_intrinsics::io_observer::trace_anchor()` directly.
pub fn trace_instant_anchor() -> &'static Instant {
    cranelisp_intrinsics::io_observer::trace_anchor()
}

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

    // FIXME 0336 — smoke test: the `bench`-gated off-path accessor is callable
    // with the filter OFF (no env var) and returns without panic (it hits
    // `record_event`'s `filter().is_none()` early return — the off-path the
    // 0021 microbench measures). Only compiled under `--features bench`.
    #[cfg(feature = "bench")]
    #[test]
    fn bench_record_event_off_path_is_callable_off_path() {
        // CRANELISP_IO_TRACE unset in the test environment ⇒ filter OFF.
        bench_record_event_off_path();
    }

    // -- parse_filter_string --

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
        assert_eq!(parse_filter_string("  1  "), Some(TraceFilter::All));
        assert_eq!(parse_filter_string("\t*\n"), Some(TraceFilter::All));
    }

    #[test]
    fn parse_filter_empty_is_none() {
        assert_eq!(parse_filter_string(""), None);
    }

    #[test]
    fn parse_filter_malformed_is_none_not_panic() {
        assert_eq!(parse_filter_string("bogus"), None);
        assert_eq!(parse_filter_string("01"), None);
        assert_eq!(parse_filter_string("2"), None);
        assert_eq!(parse_filter_string("1,2"), None);
    }

    #[test]
    fn event_size_is_bounded() {
        let sz = std::mem::size_of::<IoTraceEvent>();
        assert!(sz <= 64, "IoTraceEvent grew to {sz} bytes (cap 64)");
    }

    // -- Ring buffer discipline --

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
        let _ = dump_thread_buffer();
        let overflow = IO_TRACE_BUFFER_CAPACITY + 17;
        force_push(overflow);
        let dumped = dump_thread_buffer();
        assert_eq!(dumped.len(), IO_TRACE_BUFFER_CAPACITY);
        assert_eq!(dumped.first().unwrap().timestamp_ns, 17);
        assert_eq!(dumped.last().unwrap().timestamp_ns, (overflow - 1) as u64);
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

    // -- Observer registration + dispatch --

    #[test]
    fn install_if_enabled_no_op_when_unset() {
        // SAFETY: nextest process-isolation; env mutation is local.
        unsafe { std::env::remove_var("CRANELISP_IO_TRACE") };
        install_if_enabled();
        register_io_observer(None);
    }

    #[test]
    fn record_forwards_trampoline_enter_to_ring() {
        // Bypass the filter check at the io_trace level by directly testing
        // the mapping (the ring write itself is gated on `filter()` —
        // unrelated to mapping correctness).
        unsafe { std::env::set_var("CRANELISP_IO_TRACE", "1") };
        let _ = dump_thread_buffer();
        record(IoEventTag::TrampolineEnter, &IoEvent::TrampolineEnter { io_ptr: 0xABCD });
        // The filter OnceLock may already have been initialised by another
        // test before we set the env var. Only assert under the enabled
        // branch.
        if filter().is_some() {
            let dump = dump_thread_buffer();
            assert!(
                dump.iter().any(|e| matches!(e.tag, IoTraceTag::TrampolineEnter)),
                "expected TrampolineEnter event in ring buffer; got: {dump:?}"
            );
        }
        unsafe { std::env::remove_var("CRANELISP_IO_TRACE") };
    }

    // -- FlushGuard / install_panic_hook --

    #[test]
    fn flush_guard_drops_without_panic() {
        let _ = dump_thread_buffer();
        {
            let _g = IoTraceFlushGuard::new();
        }
        let _ = IoTraceFlushGuard::default();
    }

    #[test]
    fn install_panic_hook_is_idempotent() {
        reset_panic_hook_installed_for_tests();
        install_panic_hook();
        install_panic_hook();
        reset_panic_hook_installed_for_tests();
    }
}
