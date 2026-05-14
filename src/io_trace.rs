//! IO observer consumer — registers an observer with
//! `cranelisp_intrinsics::register_io_observer` and forwards events into the
//! existing ring buffer in `cranelisp-intrinsics::io_trace`.
//!
//! Per FIXME 0103 Phase 2 / Decision 40: the consumer-side ring buffer +
//! flush-guard machinery lives in int. The intrinsics crate defines the
//! `IoObserver` extension point and (still) the underlying ring-buffer
//! implementation (relocated in Phase 1). The IO trampoline currently in
//! `cranelisp-runtime::io` continues to call `io_trace::record_event` directly
//! — the observer pathway is dormant until the trampoline is rewired to
//! `io_observer::emit` (out of Wave 3b-2b scope).
//!
//! Activation: `CRANELISP_IO_TRACE=1` enables the observer at session start.
//! When unset, no observer is registered; the trampoline's relaxed-load null
//! check makes the emit hot path a no-op.
//!
//! FlushGuard + install_panic_hook delegate to the intrinsics-side machinery
//! so `main.rs` can stop reaching across to `cranelisp_runtime::...` (the
//! pre-Wave-3b path) and instead consume the int-local surface.

use cranelisp_intrinsics::io_observer::{IoEvent, IoEventTag, register_io_observer};
use cranelisp_intrinsics::io_trace as ring;

/// Observer fn registered with `cranelisp_intrinsics::register_io_observer`.
/// Forwards each typed `IoEvent` from the `io_observer` taxonomy onto the
/// existing thread-local ring buffer via `io_trace::record_event`.
///
/// Mapping is 1:1 with `IoEventTag` / `IoEvent` — the two enums were designed
/// in lock-step so this is a straight translation.
pub fn record(tag: IoEventTag, event: &IoEvent) {
    use ring::{IoTracePayload, IoTraceTag};

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
        // payload share their family, but `#[non_exhaustive]` defends against
        // future additions. Drop the event silently rather than panic from
        // inside the observer (panicking from an observer is UB per the
        // facade).
        _ => return,
    };
    ring::record_event(ring_tag, ring_payload);
}

/// Install the observer when `CRANELISP_IO_TRACE` is set. Idempotent —
/// safe to call once at session-startup. When the env var is unset, this is
/// a no-op (no observer registered; the hot path remains a relaxed-load null
/// check).
pub fn install_if_enabled() {
    if std::env::var("CRANELISP_IO_TRACE").is_ok() {
        register_io_observer(Some(record));
    }
}

/// Flush the IO trace ring buffer to stderr. Delegates to the intrinsics-side
/// flusher which short-circuits when tracing is disabled.
pub fn flush_to_stderr() {
    ring::flush_to_stderr();
}

/// Install a panic hook that flushes the IO trace before unwinding. Delegates
/// to the intrinsics-side hook (idempotent).
pub fn install_panic_hook() {
    ring::install_panic_hook();
}

/// RAII flush guard — calls `flush_to_stderr` on drop. Mirrors the
/// intrinsics-side `FlushGuard`; held by `main()` to drain on normal return.
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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // Observer is process-global; nextest's process-per-test isolates these.

    #[test]
    fn install_if_enabled_no_op_when_unset() {
        // SAFETY: tests run process-isolated under nextest; env mutation is local.
        unsafe { std::env::remove_var("CRANELISP_IO_TRACE") };
        // Should not panic, should be a no-op.
        install_if_enabled();
        // Defensive cleanup.
        register_io_observer(None);
    }

    #[test]
    fn record_forwards_trampoline_enter_to_ring() {
        // SAFETY: nextest process-per-test isolation.
        unsafe { std::env::set_var("CRANELISP_IO_TRACE", "1") };
        // Direct call to record bypasses the global observer slot; this
        // tests the mapping logic only. The forwarded event must appear in
        // the ring (verified by dumping the per-thread buffer).
        record(
            IoEventTag::TrampolineEnter,
            &IoEvent::TrampolineEnter { io_ptr: 0xABCD },
        );
        let dump = ring::dump_thread_buffer();
        assert!(
            dump.iter().any(|e| matches!(e.tag, ring::IoTraceTag::TrampolineEnter)),
            "expected TrampolineEnter event in ring buffer; got: {dump:?}"
        );
        unsafe { std::env::remove_var("CRANELISP_IO_TRACE") };
    }
}
