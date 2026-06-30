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
//! This module lands the **plumbing types + the recording sink**. The
//! single-ABI / single-trampoline cutover (`platform-interface.md` §6.8.0a)
//! retired the former `concurrency` / `concurrency-runtime` feature gates — the
//! strand machinery is now **unconditional**, costing nothing at steady state
//! (emit is a cheap lock + `is_none` check when not recording). The dev-facing,
//! REPL-visible dump (a `/strand` surface, sibling to `trace` / `io_observer`)
//! is the deferred `src/` (int) consumer; the buffer + emit hooks land here. It
//! extends — does not replace — the existing observability machinery (`trace`,
//! `io_observer` / `IoObserver`, the S90 `turn` correlation).

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
    ///
    /// `#[allow(dead_code)]`: part of the strand vocabulary for the deferred `src/`
    /// `/strand` dev surface + the turn-log join; no in-crate non-test caller yet.
    #[allow(dead_code)]
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
    /// A lenient/CPU spark was created (forked onto rayon). Present in the enum;
    /// emit is deferred to the CPU-spark slice (§11), so it is not yet constructed.
    #[allow(dead_code)]
    SparkCreated {
        /// The strand the spark belongs to.
        strand: StrandId,
    },
    /// A spark was forced (its value demanded / joined). Present in the enum; emit
    /// is deferred to the CPU-spark slice (§11), so it is not yet constructed.
    #[allow(dead_code)]
    SparkForced {
        /// The strand whose spark was forced.
        strand: StrandId,
    },
    /// A token-capacity permit was granted (the effect was admitted to the
    /// token's `Semaphore(capacity)` pool — slice 3, §2.8 / arch §8.1).
    TokenAcquired {
        /// The strand the admitted effect belongs to.
        strand: StrandId,
        /// The resource token whose pool granted the permit.
        token: u64,
    },
    /// An effect parked on a full token pool — the (capacity+1)th effect on a
    /// token, blocked until a permit frees (the user-observable capacity-N park,
    /// FIXME 0447). Followed by a [`StrandEvent::TokenAcquired`] when a permit
    /// frees and this strand is woken from the FIFO waiter queue.
    TokenParked {
        /// The strand that parked on the full pool.
        strand: StrandId,
        /// The resource token whose pool was full.
        token: u64,
    },
    /// A token-capacity permit was returned to the pool (the effect completed),
    /// possibly waking a parked waiter (§2.8).
    TokenReleased {
        /// The strand whose permit was released.
        strand: StrandId,
        /// The resource token whose pool the permit returned to.
        token: u64,
    },
    /// A same-token capacity disagreement, recorded under first-writer-wins
    /// reconciliation (§2.8 / arch §8.1): a later effect declared a `capacity`
    /// different from the value that first sized the token's pool. The pool is
    /// **not** resized (the first value stands, never exceeding a declared
    /// ceiling); this event surfaces the platform bug to the dev sink rather
    /// than aborting.
    TokenCapacityMismatch {
        /// The strand whose effect declared the disagreeing capacity.
        strand: StrandId,
        /// The resource token with conflicting capacity declarations.
        token: u64,
        /// The capacity that first sized the pool (the value that stands).
        first_capacity: u32,
        /// The disagreeing capacity this effect declared (ignored, recorded).
        requested_capacity: u32,
    },
    /// A detached strand was spawned into the supervisor by the
    /// `IO_TAG_LAUNCH` launch-and-continue arm (slice 5, §2.11). The `parent`
    /// ties the handler strand to the accept-loop root strand so the `/strand`
    /// dump reconstructs *"this request fanned out into this handler."*
    StrandLaunched {
        /// The freshly-minted detached strand.
        strand: StrandId,
        /// The strand that launched it (the accept-loop / launching context).
        parent: StrandId,
    },
    /// A supervised detached strand finished cleanly (§2.12).
    StrandCompleted {
        /// The strand that completed.
        strand: StrandId,
    },
    /// A supervised detached strand panicked or produced a runtime error; the
    /// supervisor caught it (`catch_unwind` + the `take_runtime_error` capture)
    /// and applied the §10 log/drop policy. **The load-bearing event of §11
    /// point 2: supervisor drops vanish without it** — the only trace a dropped
    /// (500'd) request leaves. Never re-raised, never aborts the drive (§2.12).
    StrandFailed {
        /// The strand that failed.
        strand: StrandId,
        /// The caught failure message (`"<panicked>"` for a Rust panic, or the
        /// ferried runtime-error message).
        message: String,
    },
    /// The accept-loop launch parked on a full global admission budget — the
    /// (D+1)th detached strand under global degree D blocked until an in-flight
    /// strand completes (backpressure on accept, §2.13). Followed by a
    /// [`StrandEvent::GlobalBudgetAcquired`] when a slot frees.
    GlobalBudgetParked {
        /// The strand whose launch parked on the full global budget.
        strand: StrandId,
    },
    /// A global admission permit was granted — the launch proceeded (§2.13).
    GlobalBudgetAcquired {
        /// The strand whose launch was admitted.
        strand: StrandId,
    },
    /// A completing detached strand freed its global admission permit, possibly
    /// waking a parked launch (§2.13).
    GlobalBudgetReleased {
        /// The strand whose global permit was released.
        strand: StrandId,
    },
    /// A strand was **cancelled** — the cancellation counterpart to
    /// [`StrandEvent::StrandFailed`] (slice 7, §2.15 step 5 / §2.18 / §2.19). A
    /// branch future was dropped because it **lost a race**, **timed out**, or was
    /// **cleared by graceful shutdown**. Cancellation is the *consequence* of
    /// losing a race or exiting a scope (§9 — there is no `cancel` primitive), so
    /// this event is the only trace a dropped (cancelled) strand leaves in the
    /// `/strand` dump (the cancellation half of §11 point 2). The drop itself runs
    /// the four §2.15 release paths (permit, fd/timer interest, FIFO waker,
    /// unconsumed sub-tree); this event records *that* it happened and *why*.
    ///
    /// `#[allow(dead_code)]`: the production constructor is the C3 combinator
    /// runtime (`run_io_trampoline`'s race/select loser-drop) + the C4 shutdown
    /// hook; until those land its only constructor is the in-crate tests (the
    /// event plumbing lands with the C2 foundations, ahead of its emitters).
    #[allow(dead_code)]
    StrandCancelled {
        /// The strand that was cancelled.
        strand: StrandId,
        /// Why it was cancelled.
        reason: CancelReason,
    },
}

/// Why a [`StrandEvent::StrandCancelled`] fired (slice 7, §2.15 / §2.19).
///
/// `#[non_exhaustive]` so the later kinds (`Timeout`, `Disconnect` — both reduce to
/// a race-loser drop, §2.18/§2.19) join without breaking consumers.
/// `#[allow(dead_code)]`: see [`StrandEvent::StrandCancelled`] — no production
/// constructor until the C3/C4 combinator + shutdown emitters land.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
pub enum CancelReason {
    /// The strand lost a `race` / `select` (or a derived `timeout`) — the §2.15
    /// loser-drop. Also covers cancel-on-disconnect (the handler loses the race to
    /// the disconnect-watch leaf, §2.19).
    RaceLost,
    /// The strand was cleared by graceful/hard shutdown (`Supervisor::clear`,
    /// §2.19).
    Shutdown,
}

impl StrandEvent {
    /// The strand this event is correlated to.
    ///
    /// `#[allow(dead_code)]`: a strand-vocabulary accessor for the deferred `src/`
    /// `/strand` dev surface; only the in-crate tests call it today.
    #[allow(dead_code)]
    pub fn strand(&self) -> StrandId {
        match self {
            StrandEvent::EffectDispatched { strand }
            | StrandEvent::EffectSuspended { strand }
            | StrandEvent::EffectResumed { strand }
            | StrandEvent::SparkCreated { strand }
            | StrandEvent::SparkForced { strand }
            | StrandEvent::TokenAcquired { strand, .. }
            | StrandEvent::TokenParked { strand, .. }
            | StrandEvent::TokenReleased { strand, .. }
            | StrandEvent::TokenCapacityMismatch { strand, .. }
            | StrandEvent::StrandLaunched { strand, .. }
            | StrandEvent::StrandCompleted { strand }
            | StrandEvent::StrandFailed { strand, .. }
            | StrandEvent::GlobalBudgetParked { strand }
            | StrandEvent::GlobalBudgetAcquired { strand }
            | StrandEvent::GlobalBudgetReleased { strand }
            | StrandEvent::StrandCancelled { strand, .. } => *strand,
        }
    }
}

// ===========================================================================
// The strand-event SINK — the reactor observability sink (sibling to
// `io_observer`).
//
// `design/arch/effect-concurrency.md` App. B "Strand observability hook":
// "A thread-safe `StrandEvent` sink … The trampoline emits via
// `emit_strand_event(ev)` that compiles to a no-op when not recording." Per the
// spill marker the minimal sink is "a registration-API + in-memory buffer with a
// test-only reader, no REPL command" — that is exactly this: a process-global
// recording buffer the async trampoline / reactor push into, drained by the
// in-crate tests. The dev-facing `/strand` REPL dump is the deferred (`src/`)
// sink surface, out of scope for this crate.
//
// Unconditional under the single-trampoline cutover (`platform-interface.md`
// §6.8.0a — the former `concurrency` / `concurrency-runtime` gates are retired):
// at steady state `emit` is a cheap lock + `is_none` check, so it costs nothing
// until a consumer starts recording (§11 scope guard).
// ===========================================================================

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
    /// recording). The minimal dev-facing sink: a test (or the deferred `src/`
    /// `/strand` REPL surface) starts recording, drives the reactor, then drains.
    ///
    /// `#[allow(dead_code)]`: a `pub(crate)` recording-control entry awaiting the
    /// deferred `src/` `/strand` dev surface; until that lands its only callers
    /// are the in-crate reactor/io tests.
    #[allow(dead_code)]
    pub fn start_strand_recording() {
        *BUFFER.lock().expect("strand buffer poisoned") = Some(Vec::new());
    }

    /// Emit a strand event. A no-op (one lock + `is_none`) when not recording, so
    /// it costs nothing until a consumer calls [`start_strand_recording`].
    /// Thread-safe: the reactor executor is single-threaded today, but
    /// `Par`-async branches and the rayon spark path may emit from worker
    /// threads, so the buffer is a `Mutex`.
    pub fn emit_strand_event(ev: StrandEvent) {
        if let Some(buf) = BUFFER.lock().expect("strand buffer poisoned").as_mut() {
            buf.push(ev);
        }
    }

    /// Stop recording and return the captured events in emission order. Returns
    /// an empty vec if recording was never started.
    ///
    /// `#[allow(dead_code)]`: see [`start_strand_recording`] — the deferred
    /// `src/` consumer is its production caller; tests are the current ones.
    #[allow(dead_code)]
    pub fn drain_strand_events() -> Vec<StrandEvent> {
        BUFFER
            .lock()
            .expect("strand buffer poisoned")
            .take()
            .unwrap_or_default()
    }
}

pub use sink::emit_strand_event;
// The recording-control surface for the deferred `src/` `/strand` dev dump (§3).
// No non-test consumer yet (A4c #2 — downgraded to `pub(crate)` via the module),
// so the re-export is unused outside the in-crate tests.
#[cfg_attr(not(test), allow(unused_imports))]
pub use sink::{drain_strand_events, start_strand_recording};

/// Mint a fresh non-root [`StrandId`], monotonic across the process. The async
/// `Par` fork mints one per branch so the demo's two reads are distinguishable
/// (App. B "Strand identity"); [`StrandId::ROOT`] (0) is the top-level program,
/// so minted ids start at 1.
pub fn next_strand() -> StrandId {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(1);
    StrandId(NEXT.fetch_add(1, Ordering::Relaxed))
}

// The strand machinery is unconditional under the single-trampoline cutover
// (`platform-interface.md` §6.8.0a), so this test mod runs in the default
// `cargo nextest run` lane.
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

    // spec: design/int/reactor.md §2.15 / §2.18 / §2.19 — `StrandCancelled` is the
    // cancellation counterpart to `StrandFailed`: a strand dropped because it lost a
    // race / timed out / was cleared by shutdown. It constructs with a
    // `CancelReason`, correlates back to its strand (so the `/strand` dump shows the
    // cancellation), and records through the recording sink like every other kind.
    #[test]
    fn strand_cancelled_constructs_carries_reason_and_correlates() {
        let s = StrandId(11);
        let lost = StrandEvent::StrandCancelled { strand: s, reason: CancelReason::RaceLost };
        let shut = StrandEvent::StrandCancelled { strand: s, reason: CancelReason::Shutdown };
        assert_eq!(lost.strand(), s);
        assert_eq!(shut.strand(), s);
        assert_ne!(lost, shut, "the reason distinguishes a race-loss from a shutdown cancel");

        // It flows through the recording sink like the other kinds.
        start_strand_recording();
        emit_strand_event(StrandEvent::StrandCancelled { strand: s, reason: CancelReason::RaceLost });
        let events = drain_strand_events();
        assert_eq!(
            events,
            vec![StrandEvent::StrandCancelled { strand: s, reason: CancelReason::RaceLost }],
            "StrandCancelled records through the strand sink"
        );
    }
}
