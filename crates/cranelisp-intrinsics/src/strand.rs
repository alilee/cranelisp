//! Strand identity + the trampoline observability event stream
//! (effect-concurrency track, slice 2 — `design/arch/effect-concurrency.md` §11).
//!
//! Observability is a **first-class, load-bearing commitment** of the
//! effect-concurrency model: the concurrency is *written by nobody* (§1), so the
//! suspensions, sparks, token-parks, and supervisor drops never appear in the
//! source — you cannot debug what you did not write unless the trampoline
//! surfaces it. The single indispensable primitive is **strand identity**
//! ([`StrandId`]), the `turn`-correlation-id precedent (S90 log↔trace) threaded
//! through every suspend / spawn / cancel. It is **expensive to retrofit** —
//! threading a correlation id through the continuation/spawn machinery touches
//! every path — so the newtype + the event-hook surface land **with** the async
//! substrate, not after (§11, §14 "observability is groundwork").
//!
//! This module lands the **plumbing types only**, gated behind the off-by-default
//! `concurrency` feature: byte-identical-when-off (§11 scope guard — reuse the
//! agentic-repl feature-gated discipline so observability costs nothing in
//! `--link` / `--release`). The sink (a dev-facing, REPL-visible stream, sibling
//! to `trace` / `io_observer`) and the trampoline hooks that emit these events
//! are the slice-2 reactor implementation (`/dev`). It extends — does not replace
//! — the existing observability machinery (`trace`, `io_observer` / `IoObserver`,
//! the S90 `turn` correlation).

/// A strand correlation id — the unit of observable concurrency identity.
///
/// A *strand* is one logical line of effect execution: a request handler fanned
/// out by launch-and-continue, a spark forced on rayon, an effect suspended on
/// the reactor. Threading a [`StrandId`] through every suspend / spawn / cancel
/// is what lets a debugging user reconstruct *"this request fanned out into these
/// effects; this one was cancelled by a race; that one panicked and the
/// supervisor dropped it"* (§11). It is the `turn` id's successor at the
/// concurrency layer and is carried alongside it.
///
/// `#[repr(transparent)]` over `u64` — a plain correlation id, cheap to copy and
/// to thread through the continuation machinery; no allocation, no contention.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StrandId(pub u64);

impl StrandId {
    /// The root strand — the top-level program, before any fan-out.
    pub const ROOT: StrandId = StrandId(0);

    /// The raw correlation value (for joining with the `turn` log↔trace stream).
    pub const fn get(self) -> u64 {
        self.0
    }
}

/// A structured event emitted by the trampoline, correlated by [`StrandId`].
///
/// **Only the slice-2 kinds are present.** The stream accrues kinds per capability
/// as the track lands them (§11 "Events the stream carries") — token
/// acquire/release with the pool slice, supervisor action with slice 4,
/// cancellation with the combinator slice. `#[non_exhaustive]` so those staged
/// kinds join without breaking consumers. Payloads are deliberately minimal and
/// dev-facing (§11 scope guard — build the plumbing, not gold-plated sinks).
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StrandEvent {
    /// An effect was dispatched into the trampoline.
    EffectDispatched {
        /// The strand this effect belongs to.
        strand: StrandId,
    },
    /// An effect parked on the reactor (an fd / timer it is waiting on).
    EffectSuspended {
        /// The strand that parked.
        strand: StrandId,
    },
    /// A parked effect was woken and resumed.
    EffectResumed {
        /// The strand that resumed.
        strand: StrandId,
    },
    /// A lenient/CPU spark was created (forked onto rayon).
    SparkCreated {
        /// The strand the spark belongs to.
        strand: StrandId,
    },
    /// A spark was forced (its value demanded / joined).
    SparkForced {
        /// The strand whose spark was forced.
        strand: StrandId,
    },
}

impl StrandEvent {
    /// The strand this event is correlated to.
    pub fn strand(&self) -> StrandId {
        match self {
            StrandEvent::EffectDispatched { strand }
            | StrandEvent::EffectSuspended { strand }
            | StrandEvent::EffectResumed { strand }
            | StrandEvent::SparkCreated { strand }
            | StrandEvent::SparkForced { strand } => *strand,
        }
    }
}

// ===========================================================================
// The strand-event SINK — slice-2 reactor implementation (gated
// `concurrency-runtime`; sibling to `io_observer`).
//
// `design/arch/effect-concurrency.md` App. B "Strand observability hook":
// "A thread-safe `StrandEvent` sink … The trampoline emits via
// `emit_strand_event(ev)` that compiles to a no-op when off." Per the spill
// marker the minimal sink is "a registration-API + in-memory buffer with a
// test-only reader, no REPL command" — that is exactly this: a process-global
// recording buffer the async trampoline / reactor push into, drained by the
// gated tests. The dev-facing `/strand` REPL dump is the deferred (`src/`) sink
// surface, out of scope for this crate.
//
// It is gated `concurrency-runtime` (a strict superset of `concurrency`, so the
// module — `#[cfg(feature = "concurrency")]` in lib.rs — is present), keeping it
// byte-identical-when-off: with `concurrency-runtime` off there is no buffer, no
// emit, no cost (§11 scope guard).
// ===========================================================================

#[cfg(feature = "concurrency-runtime")]
mod sink {
    use super::StrandEvent;
    use std::sync::Mutex;

    /// The process-global recording buffer. `None` = not recording (the steady
    /// state — emit is a cheap lock + `is_none` check); `Some(vec)` once a
    /// consumer calls [`start_strand_recording`]. A `Mutex` (not the
    /// `AtomicUsize`-fn-ptr slot `io_observer` uses) because a `StrandEvent`
    /// carries a payload — a buffer captures the events directly without forcing
    /// the consumer to thread state through a non-capturing `fn` pointer.
    ///
    /// M3: this is process-global single-buffer state. Concurrent recordings
    /// would clobber each other; correctness relies on nextest's
    /// process-per-test isolation (each `#[test]` is its own process, so each
    /// gets a private `BUFFER`). Do not record from two threads in one process.
    static BUFFER: Mutex<Option<Vec<StrandEvent>>> = Mutex::new(None);

    /// Begin recording strand events into the global buffer (clearing any prior
    /// recording). The minimal dev-facing sink: a test (or a future `/strand`
    /// REPL surface) starts recording, drives the reactor, then drains.
    pub fn start_strand_recording() {
        *BUFFER.lock().expect("strand buffer poisoned") = Some(Vec::new());
    }

    /// Emit a strand event. A no-op (one lock + `is_none`) when not recording —
    /// and compiled out entirely when `concurrency-runtime` is off (the call
    /// sites are themselves gated). Thread-safe: the reactor executor is
    /// single-threaded today, but `Par`-async branches and the rayon spark path
    /// may emit from worker threads, so the buffer is a `Mutex`.
    pub fn emit_strand_event(ev: StrandEvent) {
        if let Some(buf) = BUFFER.lock().expect("strand buffer poisoned").as_mut() {
            buf.push(ev);
        }
    }

    /// Stop recording and return the captured events in emission order. Returns
    /// an empty vec if recording was never started.
    pub fn drain_strand_events() -> Vec<StrandEvent> {
        BUFFER
            .lock()
            .expect("strand buffer poisoned")
            .take()
            .unwrap_or_default()
    }
}

#[cfg(feature = "concurrency-runtime")]
pub use sink::{drain_strand_events, emit_strand_event, start_strand_recording};

/// Mint a fresh non-root [`StrandId`], monotonic across the process. The async
/// `Par` fork mints one per branch so the demo's two reads are distinguishable
/// (App. B "Strand identity"); [`StrandId::ROOT`] (0) is the top-level program,
/// so minted ids start at 1.
#[cfg(feature = "concurrency-runtime")]
pub fn next_strand() -> StrandId {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(1);
    StrandId(NEXT.fetch_add(1, Ordering::Relaxed))
}

// This module is itself `#[cfg(feature = "concurrency")]` (see lib.rs), so the
// whole test mod runs only under `cargo nt-concurrency` (the FIXME-0449 lane).
#[cfg(test)]
mod tests {
    use super::*;

    // spec: design/arch/effect-concurrency.md §11 — `StrandId` is the
    // `#[repr(transparent)]` correlation-id newtype threaded through every
    // suspend/spawn/cancel. The ROOT strand (the top-level program, before any
    // fan-out) MUST be `StrandId(0)`, and the slice-2 `StrandEvent` kinds MUST
    // construct (the observability plumbing landed with the async substrate).
    #[test]
    fn strand_id_root_is_zero_and_event_kinds_present() {
        assert_eq!(StrandId::ROOT, StrandId(0));
        assert_eq!(StrandId::ROOT.get(), 0);
        // repr(transparent) over u64 — same size as the raw correlation value.
        assert_eq!(core::mem::size_of::<StrandId>(), core::mem::size_of::<u64>());

        // The slice-2 kinds all construct and correlate back to their strand.
        let s = StrandId(7);
        for ev in [
            StrandEvent::EffectDispatched { strand: s },
            StrandEvent::EffectSuspended { strand: s },
            StrandEvent::EffectResumed { strand: s },
            StrandEvent::SparkCreated { strand: s },
            StrandEvent::SparkForced { strand: s },
        ] {
            assert_eq!(ev.strand(), s);
        }
    }
}
