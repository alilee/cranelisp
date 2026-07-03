//! GOT-population observer consumer — registers an observer with
//! `cranelisp_backend::register_got_observer` and writes events into a
//! per-thread ring buffer that flushes to stderr at session end.
//!
//! Per FIXME 0099 Phase 2 / Decision 40 + 41: the consumer-side machinery
//! (ring buffer, env-var activation, panic-safe formatter, flush-to-stderr
//! dump) lives in int. Backend emits `JitWrite` (`compile_to_module`
//! post-finalize) and `LinkerWrite` (`Linker::load_object` symbol-resolution
//! loop) events. The `Redefinition` tag is emitted from int's own
//! symbol-table-write site (`worker::inline_jit_codegen_for_names`) when an
//! existing `Code::Jit` is overwritten — see that function for the call.
//!
//! Activation: `CRANELISP_GOT_TRACE=1` enables the observer at session start.
//! When unset, no observer is registered; backend's emit hot path is a
//! relaxed-load null check.

use std::cell::RefCell;
use std::collections::VecDeque;
use std::sync::Mutex;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread::ThreadId;

use cranelisp_backend::got_observer::{
    GotEvent, GotEventTag, GotObserver, GotProvenance, register_got_observer,
};

// ---------------------------------------------------------------------------
// Event taxonomy (consumer-side; mirrors backend's GotEvent for storage)
// ---------------------------------------------------------------------------

/// Consumer-side event tag: the backend-emitted tags plus the two int-owned
/// redefinition-machinery kinds (S101, `design/int/session-transaction.md`
/// §9.3) that backend's `GotEventTag` does not carry — **slot-freeze** (an
/// ABI-changing redefinition froze the old slot and allocated a fresh one)
/// and **trap-patch** (a BROKEN symbol's slot was patched to a trap stub).
#[derive(Debug, Clone, Copy)]
pub enum StoredTag {
    Backend(GotEventTag),
    SlotFreeze,
    TrapPatch,
}

/// Stored event with timestamp + thread-ordering metadata for merge-sort.
#[derive(Debug, Clone)]
pub struct StoredGotEvent {
    pub timestamp_ns: u64,
    pub thread_id: ThreadId,
    pub thread_ord_id: u64,
    pub tag: StoredTag,
    pub module: String,
    pub symbol: String,
    pub slot: usize,
    pub ptr: usize,
    pub provenance: GotProvenance,
}

// ---------------------------------------------------------------------------
// Ring buffer
// ---------------------------------------------------------------------------

const GOT_TRACE_BUFFER_CAPACITY: usize = 16_384;

static NEXT_THREAD_ORD_ID: AtomicU64 = AtomicU64::new(0);

thread_local! {
    static GOT_TRACE_BUF: RefCell<VecDeque<StoredGotEvent>> =
        RefCell::new(VecDeque::with_capacity(GOT_TRACE_BUFFER_CAPACITY));
    static GOT_TRACE_THREAD_ORD: RefCell<Option<u64>> = const { RefCell::new(None) };
}

fn thread_ord_id() -> u64 {
    GOT_TRACE_THREAD_ORD.with(|cell| {
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

// Published per-thread snapshots (cross-thread merge at flush time).
static PUBLISHED_BUFFERS: OnceLock<Mutex<Vec<Vec<StoredGotEvent>>>> = OnceLock::new();

fn published_buffers() -> &'static Mutex<Vec<Vec<StoredGotEvent>>> {
    PUBLISHED_BUFFERS.get_or_init(|| Mutex::new(Vec::new()))
}

// ---------------------------------------------------------------------------
// Filter (env-var parse once)
// ---------------------------------------------------------------------------

static GOT_TRACE_ENABLED: OnceLock<bool> = OnceLock::new();

fn filter_enabled() -> bool {
    *GOT_TRACE_ENABLED.get_or_init(|| match std::env::var("CRANELISP_GOT_TRACE") {
        Ok(v) => matches!(v.trim(), "1" | "*"),
        Err(_) => false,
    })
}

// ---------------------------------------------------------------------------
// Observer fn (registered with backend)
// ---------------------------------------------------------------------------

/// Backend invokes this through the registered observer slot. Pushes the
/// event into the thread-local ring buffer (FIFO overflow on capacity).
pub fn record(tag: GotEventTag, event: &GotEvent) {
    if !filter_enabled() {
        return;
    }
    // Build the timestamp from the shared anchor so cross-trace merge-sort
    // works (intrinsics's IO trace and our GOT trace share the same anchor).
    let anchor = cranelisp_intrinsics::trace_anchor();
    let timestamp_ns = anchor.elapsed().as_nanos() as u64;
    let ord = thread_ord_id();
    let stored = StoredGotEvent {
        timestamp_ns,
        thread_id: std::thread::current().id(),
        thread_ord_id: ord,
        tag: StoredTag::Backend(tag),
        module: event.module.to_string(),
        symbol: event.symbol.to_string(),
        slot: event.slot,
        ptr: event.ptr as usize,
        provenance: event.provenance,
    };
    GOT_TRACE_BUF.with(|cell| {
        let mut buf = cell.borrow_mut();
        if buf.len() == GOT_TRACE_BUFFER_CAPACITY {
            buf.pop_front();
        }
        buf.push_back(stored);
    });
}

// ---------------------------------------------------------------------------
// Registration
// ---------------------------------------------------------------------------

/// Install the observer when `CRANELISP_GOT_TRACE` is set. Idempotent —
/// safe to call once at session-startup. When the env var is unset, no
/// observer is registered.
pub fn install_if_enabled() {
    if filter_enabled() {
        let obs: GotObserver = record;
        register_got_observer(Some(obs));
    }
}

// ---------------------------------------------------------------------------
// Dump / flush
// ---------------------------------------------------------------------------

fn dump_thread_buffer() -> Vec<StoredGotEvent> {
    let mut out: Vec<StoredGotEvent> =
        GOT_TRACE_BUF.with(|cell| cell.borrow_mut().drain(..).collect());
    out.sort_by_key(|e| (e.timestamp_ns, e.thread_ord_id));
    out
}

/// Publish this thread's buffer to the cross-thread registry.
pub fn publish_thread_buffer() {
    let drained = dump_thread_buffer();
    if drained.is_empty() {
        return;
    }
    if let Ok(mut guard) = published_buffers().lock() {
        guard.push(drained);
    }
}

fn dump_all_buffers() -> Vec<StoredGotEvent> {
    let mut all: Vec<StoredGotEvent> = Vec::new();
    if let Ok(guard) = published_buffers().lock() {
        for b in guard.iter() {
            all.extend(b.iter().cloned());
        }
    }
    let local = dump_thread_buffer();
    all.extend(local);
    all.sort_by_key(|e| (e.timestamp_ns, e.thread_ord_id));
    all
}

fn format_event_line(e: &StoredGotEvent) -> String {
    let tag_name = match e.tag {
        StoredTag::Backend(GotEventTag::JitWrite) => "JitWrite",
        StoredTag::Backend(GotEventTag::LinkerWrite) => "LinkerWrite",
        StoredTag::Backend(GotEventTag::Redefinition) => "Redefinition",
        StoredTag::Backend(_) => "Unknown",
        StoredTag::SlotFreeze => "SlotFreeze",
        StoredTag::TrapPatch => "TrapPatch",
    };
    let prov = match e.provenance {
        GotProvenance::Jit { jit_addr } => format!("jit_addr={jit_addr:#x}"),
        GotProvenance::Linker { linker_addr } => format!("linker_addr={linker_addr:#x}"),
        _ => "unknown".to_string(),
    };
    format!(
        "[GOT] ts={ts} thr={thr:?}/{ord} {tag}\tmodule={module} symbol={symbol} slot={slot} ptr={ptr:#x} {prov}",
        ts = e.timestamp_ns,
        thr = e.thread_id,
        ord = e.thread_ord_id,
        tag = tag_name,
        module = e.module,
        symbol = e.symbol,
        slot = e.slot,
        ptr = e.ptr,
        prov = prov,
    )
}

/// Drain every published + live-thread event to stderr, merge-sorted by
/// `(timestamp_ns, thread_ord_id)`. No-op when tracing is disabled.
pub fn flush_to_stderr() {
    if !filter_enabled() {
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

/// RAII guard: `Drop` calls `flush_to_stderr`. Held by `main()` to drain on
/// normal return.
pub struct GotTraceFlushGuard(());

impl GotTraceFlushGuard {
    pub fn new() -> Self {
        Self(())
    }
}

impl Default for GotTraceFlushGuard {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for GotTraceFlushGuard {
    fn drop(&mut self) {
        flush_to_stderr();
    }
}

static PANIC_HOOK_INSTALLED: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// Chain a `flush_to_stderr` call in front of the existing panic hook.
/// Idempotent; safe to call defensively.
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
        previous(info);
    }));
}

// ---------------------------------------------------------------------------
// Redefinition emit helper
// ---------------------------------------------------------------------------

/// Emit a `Redefinition` event from int's symbol-table-write site. Called by
/// `worker::inline_jit_codegen_for_names` when the entry's `code` field was
/// already populated before the JitWrite. Backend publishes the
/// `Redefinition` tag but does not emit it (FIXME 0099 — int owns the
/// detection because the prior `code` field lives in int's
/// `SessionSymbolTable`).
///
/// `prior_ptr` is the address that was about to be overwritten; passed so
/// the trace can correlate with the corresponding `JitWrite` /
/// `LinkerWrite` event that originally populated the slot.
pub fn emit_redefinition(
    module: &cranelisp_types::ModuleFullPath,
    symbol: &cranelisp_types::Symbol,
    slot: usize,
    new_ptr: *const u8,
    prior_ptr: *const u8,
) {
    if !filter_enabled() {
        return;
    }
    // Backend's `GotEvent` is `#[non_exhaustive]` — int cannot construct one
    // directly via struct-expression syntax, and the facade publishes the
    // `Redefinition` tag for int to emit but provides no constructor. Record
    // directly into our consumer-side ring buffer instead of routing
    // through `backend::got_observer::emit` (we are the only registered
    // observer; this is observationally equivalent).
    //
    // FIXME(/arch backend FIXME 0099) — backend should expose a public
    // constructor for `GotEvent` (e.g., `GotEvent::new(module, symbol, slot,
    // ptr, provenance)`) so int's Redefinition emission can use the same
    // `emit(tag, &event)` dispatch path as the backend-internal JitWrite +
    // LinkerWrite sites. Today we record directly into the consumer ring.
    record_int_event(
        StoredTag::Backend(GotEventTag::Redefinition),
        module,
        symbol,
        slot,
        new_ptr as usize,
        GotProvenance::Jit {
            jit_addr: prior_ptr as usize,
        },
    );
}

/// Emit a `SlotFreeze` event (S101 §9.3): an ABI-changing redefinition froze
/// `old_slot` (never written again; its code retained in the session pool)
/// and allocated `new_slot` for the new world. `slot` = old slot; `ptr`
/// carries the new slot index for correlation.
pub fn emit_slot_freeze(
    module: &cranelisp_types::ModuleFullPath,
    symbol: &cranelisp_types::Symbol,
    old_slot: usize,
    new_slot: usize,
) {
    if !filter_enabled() {
        return;
    }
    record_int_event(
        StoredTag::SlotFreeze,
        module,
        symbol,
        old_slot,
        new_slot,
        GotProvenance::Jit { jit_addr: 0 },
    );
}

/// Emit a `TrapPatch` event (S101 §9.3): a BROKEN symbol's slot was patched
/// in place to a trap stub (`ptr` = the stub's code address).
pub fn emit_trap_patch(
    module: &cranelisp_types::ModuleFullPath,
    symbol: &cranelisp_types::Symbol,
    slot: usize,
    stub_ptr: *const u8,
) {
    if !filter_enabled() {
        return;
    }
    record_int_event(
        StoredTag::TrapPatch,
        module,
        symbol,
        slot,
        stub_ptr as usize,
        GotProvenance::Jit { jit_addr: 0 },
    );
}

/// Shared int-side ring-buffer push for events the backend observer does not
/// emit (Redefinition / SlotFreeze / TrapPatch — see `emit_redefinition`'s
/// rustdoc for why these record directly into the consumer ring).
fn record_int_event(
    tag: StoredTag,
    module: &cranelisp_types::ModuleFullPath,
    symbol: &cranelisp_types::Symbol,
    slot: usize,
    ptr: usize,
    provenance: GotProvenance,
) {
    let anchor = cranelisp_intrinsics::trace_anchor();
    let timestamp_ns = anchor.elapsed().as_nanos() as u64;
    let ord = thread_ord_id();
    let stored = StoredGotEvent {
        timestamp_ns,
        thread_id: std::thread::current().id(),
        thread_ord_id: ord,
        tag,
        module: module.to_string(),
        symbol: symbol.to_string(),
        slot,
        ptr,
        provenance,
    };
    GOT_TRACE_BUF.with(|cell| {
        let mut buf = cell.borrow_mut();
        if buf.len() == GOT_TRACE_BUFFER_CAPACITY {
            buf.pop_front();
        }
        buf.push_back(stored);
    });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{ModuleFullPath, Symbol};

    #[test]
    fn record_no_op_when_filter_disabled() {
        // SAFETY: nextest process-per-test.
        unsafe { std::env::remove_var("CRANELISP_GOT_TRACE") };
        // Can't construct `GotEvent` directly (non_exhaustive); exercise the
        // filter via `emit_redefinition` which builds its own stored event.
        emit_redefinition(
            &ModuleFullPath::from("user"),
            &Symbol::from("foo"),
            0,
            0xDEAD_BEEF as *const u8,
            0xCAFE_BABE as *const u8,
        );
        // Buffer should be empty because the filter parsed `false` and
        // returned early.
        let dump = dump_thread_buffer();
        assert!(dump.is_empty(), "buffer should be empty when filter disabled");
    }
}
