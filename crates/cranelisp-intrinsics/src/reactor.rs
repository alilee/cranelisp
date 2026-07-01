//! The slice-2 host reactor — the load-bearing new artifact of the
//! effect-concurrency track (`design/arch/effect-concurrency.md` §12, App. B).
//!
//! This is the **host side of the A2 model**: the host owns the reactor;
//! platforms are C-ABI async *leaves*. A platform poll-fn does its non-blocking
//! syscall (it owns the *what*); on `WouldBlock` it registers interest through
//! the [`cranelisp_platform::HostCtx`] vtable + a C-ABI [`cranelisp_platform::Waker`],
//! and this reactor (a single [`mio::Poll`] loop) owns the *when* and re-polls
//! (the host owns the *when*).
//!
//! ## Why it lives in `cranelisp-intrinsics`, not `src/` (int)
//!
//! The C-ABI entry [`crate::io::cranelisp_run_io`] that drives the trampoline
//! lives here and cannot depend on int (`int → intrinsics`, never the inverse);
//! and decisively a `--link`'d program does not contain `src/` at runtime, so a
//! reactor in int could never drive a linked program's effects. Hosting it here
//! (runtime-feature-gated, linkable into `--link` output) serves `--run`/REPL now
//! and is the only placement that can serve `--link` concurrency later. This
//! mirrors the `io_observer` split: int owns the *policy* (the dev sink,
//! construction parameters); intrinsics hosts the *mechanism*.
//!
//! ## The pieces
//!
//! - [`Reactor`] — a single `mio::Poll` loop + a timer min-heap, implementing the
//!   three `HostCtx` `register_*` callbacks over raw fds / monotonic-deadline
//!   timers.
//! - the **C-ABI waker** ([`make_cabi_waker`]) — the projection of a
//!   `std::task::Waker` into the `cranelisp_platform::Waker` `(data, vtable)`
//!   pair the platform hands to `register_*`.
//! - [`EffectPoll`] — the **one await boundary** (App. B): an `async` leaf future
//!   whose `poll` calls the platform poll-fn and maps `Poll::Ready` → the value,
//!   `Poll::Pending` → park on the reactor. It emits the strand observability
//!   events (`EffectDispatched` / `EffectSuspended` / `EffectResumed`).
//! - [`block_on_reactor`] — a custom single-threaded executor that drives a future
//!   to completion, turning the mio reactor between polls. This is the canonical
//!   "hand-written executor loop that calls `Future::poll`" — NOT a fiber (the
//!   suspension is a real compiler-generated `async` state machine; App. B
//!   substrate rationale, Principle 8).
//! - the fixture **`async-read`** poll-fn (`async_read_pollfn`) + a timer-driven
//!   feeder (`timer_write_pollfn`) — the hand-written demo leaves (App. B "Demo
//!   leaf"), now `#[cfg(test)]` test-only fixtures. No `declare_platform!` /
//!   backend change is needed to demo the mechanism.
//!
//! Single-ABI cutover (S96, `platform-interface.md` §6.8.0a): the reactor + its
//! `mio`/`futures` deps are **unconditional** in every build (the former
//! `concurrency-runtime` feature is retired). Lean-default is preserved as a
//! RUNTIME property — a pure-blocking program constructs no mio `Poll` (the
//! reactor is lazily initialised per drive), not via a `#[cfg]` split.

use core::ffi::c_void;
use std::cell::{Cell, RefCell};
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::future::Future;
use std::os::fd::RawFd;
use std::pin::Pin;
use std::rc::Rc;
use std::sync::Arc;
use std::task::{Context, Poll as TaskPoll, Wake, Waker};
use std::time::Duration;

use futures::future::FutureExt; // catch_unwind on the supervised strand body
use futures::stream::{FuturesUnordered, StreamExt}; // the supervisor JoinSet-equivalent

use mio::unix::SourceFd;
use mio::{Events, Interest, Token};

use cranelisp_platform::{
    Acquire as CAcquire, HostCtx, Poll as CPoll, PollFn, Waker as CWaker, WakerVTable,
};

use crate::strand::{emit_strand_event, StrandEvent, StrandId};

/// The reserved mio `Token` for the reactor's cross-thread wakeup
/// ([`Reactor::bridge_waker`]). fd registrations hand out tokens from
/// `next_fd_token = 1`, so token `0` never collides with an fd waiter and a
/// `Token(0)` event in [`Reactor::turn`] simply finds no `fd_waiters` entry and
/// is ignored (it served only to unblock the `mio::poll`).
const BRIDGE_WAKE_TOKEN: Token = Token(0);

// ===========================================================================
// Monotonic clock — the one clock shared by the reactor's timer wheel and the
// fixture poll-fns. `HostCtx::register_timer` takes a monotonic-nanos deadline,
// so both sides read CLOCK_MONOTONIC through this helper (no Instant/u64 skew).
// ===========================================================================

/// Current `CLOCK_MONOTONIC` time in nanoseconds.
pub fn monotonic_nanos() -> u64 {
    let mut ts = libc::timespec { tv_sec: 0, tv_nsec: 0 };
    // SAFETY: `ts` is a valid out-param for `clock_gettime`.
    unsafe { libc::clock_gettime(libc::CLOCK_MONOTONIC, &mut ts) };
    (ts.tv_sec as u64) * 1_000_000_000 + (ts.tv_nsec as u64)
}

// ===========================================================================
// The C-ABI waker — projecting a `std::task::Waker` across the platform C-ABI.
//
// The platform receives a `*const cranelisp_platform::Waker` (a `(data, vtable)`
// pair). `data` is a boxed `std::task::Waker`; the four vtable callbacks
// wake/clone/drop it. This is the "C-ABI projection of `std::task::Context`"
// the ABI commits to (§12).
// ===========================================================================

unsafe extern "C" fn cwaker_wake(data: *const c_void) {
    // Consume: reconstitute the boxed waker and `wake()` it (frees the box).
    // SAFETY: `data` is the live, exclusively-owned `Box<std::task::Waker>`
    // payload `make_cabi_waker` produced. `wake` is a consuming vtable entry —
    // it is called exactly once for this payload, so reconstituting the box and
    // dropping it (via `wake()`) frees it exactly once (no double-free, no UAF).
    let waker = unsafe { Box::from_raw(data as *mut std::task::Waker) };
    waker.wake();
}

unsafe extern "C" fn cwaker_wake_by_ref(data: *const c_void) {
    // SAFETY: `data` is the live `Box<std::task::Waker>` payload from
    // `make_cabi_waker`. `wake_by_ref` only BORROWS the payload (no consume), so
    // the box stays owned by its holder; the shared reborrow here does not alias
    // any `&mut` (the payload is never mutated through the box).
    let waker = unsafe { &*(data as *const std::task::Waker) };
    waker.wake_by_ref();
}

unsafe extern "C" fn cwaker_clone(data: *const c_void) -> CWaker {
    // SAFETY: `data` is the live `Box<std::task::Waker>` payload from
    // `make_cabi_waker`. `clone` only BORROWS the payload; the cloned
    // `std::task::Waker` is rewrapped into a fresh, independently-owned C-ABI
    // waker box, so the original box's single-ownership is preserved.
    let waker = unsafe { &*(data as *const std::task::Waker) };
    make_cabi_waker(waker.clone())
}

unsafe extern "C" fn cwaker_drop(data: *const c_void) {
    // SAFETY: `data` is the live, exclusively-owned `Box<std::task::Waker>` from
    // `make_cabi_waker`. `drop` is a consuming vtable entry called exactly once
    // for this payload, so reconstituting and dropping the box frees it exactly
    // once (paired with `make_cabi_waker`'s `Box::into_raw`).
    drop(unsafe { Box::from_raw(data as *mut std::task::Waker) });
}

static CWAKER_VTABLE: WakerVTable = WakerVTable {
    wake: cwaker_wake,
    wake_by_ref: cwaker_wake_by_ref,
    clone: cwaker_clone,
    drop: cwaker_drop,
};

/// Project a `std::task::Waker` into a C-ABI [`cranelisp_platform::Waker`]. The
/// returned waker OWNS a heap box holding `w`; the owner must eventually either
/// hand it to a `register_*` (which clones it) and then free this one via
/// [`drop_cabi_waker`], or pass ownership to the reactor.
pub fn make_cabi_waker(w: std::task::Waker) -> CWaker {
    let data = Box::into_raw(Box::new(w)) as *const c_void;
    CWaker {
        data,
        vtable: &CWAKER_VTABLE as *const WakerVTable,
    }
}

/// Free a C-ABI waker produced by [`make_cabi_waker`] (calls its vtable `drop`).
fn drop_cabi_waker(w: CWaker) {
    // SAFETY: `w` was produced by `make_cabi_waker`, so its vtable is `CWAKER_VTABLE`.
    unsafe { ((*w.vtable).drop)(w.data) };
}

/// An owned clone of a C-ABI waker the reactor stashes until the resource is
/// ready. RAII: dropping it (an un-fired registration the reactor tears down)
/// calls the vtable `drop`; [`OwnedCWaker::wake`] consumes it and fires.
struct OwnedCWaker {
    w: CWaker,
}

impl OwnedCWaker {
    /// Clone an owned waker from a borrowed `*const Waker` the platform handed in.
    ///
    /// # Safety
    /// `src` must be a valid C-ABI waker (a live `(data, vtable)` pair).
    unsafe fn clone_from_ref(src: *const CWaker) -> Self {
        let src = unsafe { &*src };
        // SAFETY: `src.vtable` points at a live `WakerVTable`; `clone` returns a
        // fresh owned waker over a cloned payload.
        let w = unsafe { ((*src.vtable).clone)(src.data) };
        OwnedCWaker { w }
    }

    /// Fire the waker, consuming it (the reactor calls this when the registered
    /// fd / timer is ready).
    fn wake(self) {
        // SAFETY: `self.w` is a live waker; `wake` consumes its payload.
        unsafe { ((*self.w.vtable).wake)(self.w.data) };
        std::mem::forget(self); // payload consumed by `wake`; skip the Drop free.
    }
}

impl Drop for OwnedCWaker {
    fn drop(&mut self) {
        // SAFETY: `self.w` is a live waker whose payload was never consumed.
        unsafe { ((*self.w.vtable).drop)(self.w.data) };
    }
}

// ===========================================================================
// The reactor — one mio::Poll loop + a timer min-heap.
// ===========================================================================

/// A registrant tag (finding #3, §2.16): identifies the [`EffectPoll`] that armed a
/// given fd/timer interest, so the leaf's `ReactorInterest::drop` can actively
/// deregister exactly its own entries on cancel. `0` is the reserved "untagged"
/// sentinel (see [`Reactor::next_reg`]).
type RegId = u64;

/// A registered timer waiter.
struct TimerEntry {
    deadline_nanos: u64,
    id: u64,
}

// Ordered by deadline for the min-heap (via `Reverse`); ties broken by id.
impl PartialEq for TimerEntry {
    fn eq(&self, o: &Self) -> bool {
        self.deadline_nanos == o.deadline_nanos && self.id == o.id
    }
}
impl Eq for TimerEntry {}
impl PartialOrd for TimerEntry {
    fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for TimerEntry {
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        self.deadline_nanos
            .cmp(&o.deadline_nanos)
            .then(self.id.cmp(&o.id))
    }
}

/// The host reactor: a single [`mio::Poll`] driving fd readiness + a timer wheel.
///
/// Single-threaded by construction — [`block_on_reactor`] owns it and never hands
/// out a `&mut` across a `Future::poll` (the poll-fns mutate it through the raw
/// `HostCtx::host` pointer; `turn` mutates it only *between* polls). This is the
/// "two slow reads overlap on ONE reactor thread, no thread-per-read" guarantee
/// at its root: there is exactly one reactor and one thread.
pub struct Reactor {
    poll: mio::Poll,
    events: Events,
    /// Next mio `Token` value to hand out for an fd registration.
    next_fd_token: usize,
    /// Live fd registrations: `token → (fd, waker-to-fire-on-ready, registrant)`.
    /// The `RegId` tag (finding #3, §2.16) records which [`EffectPoll`] armed the
    /// entry, so its `ReactorInterest::drop` can actively deregister it on cancel.
    fd_waiters: HashMap<usize, (RawFd, OwnedCWaker, RegId)>,
    /// Pending timers, soonest-deadline first.
    timer_heap: BinaryHeap<Reverse<TimerEntry>>,
    /// Live timer waiters: `id → (waker-to-fire-on-expiry, registrant)` (finding
    /// #3 tag — see [`Reactor::fd_waiters`]).
    timer_waiters: HashMap<u64, (OwnedCWaker, RegId)>,
    next_timer_id: u64,
    /// Monotonic source of [`RegId`] registrant tags (finding #3, §2.16). Allocated
    /// per [`EffectPoll`] in `EffectPoll::new`; `0` is the reserved "untagged"
    /// sentinel (an entry armed with no current registrant — e.g. a fixture leaf
    /// built with a null host — which `deregister` never targets). Starts at 1.
    next_reg: RegId,
    /// The leaf currently being polled (finding #3, §2.16): set by
    /// `EffectPoll::poll`'s bracket around the poll-fn call, so every fd/timer the
    /// poll-fn arms during THIS poll is stamped with that leaf's `RegId`. `None`
    /// between polls (and during `turn()`), so a registration that somehow reached
    /// the reactor outside a bracket is stamped `0` (untagged) rather than
    /// mis-attributed.
    current_registrant: Option<RegId>,
    /// The cross-thread wakeup (slice 6): a `mio::Waker` on the reserved
    /// [`BRIDGE_WAKE_TOKEN`] that unblocks a `mio::poll` in [`Reactor::turn`]
    /// from another thread. This is what lets the **wakeable rayon→reactor
    /// bridge** (the blocking partition of [`crate::io::run_par_node_async`])
    /// wake the reactor when a `rayon`-offloaded branch completes — without it a
    /// blocking-only `Par` (no fd/timer waiters) would block in `turn` for the
    /// full `MAX_TURN_BLOCK` instead of resuming on completion. It backs the
    /// executor's task `Waker` ([`ExecutorWaker`]) so a `futures` `oneshot` send
    /// from a `rayon` worker wakes the reactor through the normal waker path.
    bridge_waker: Arc<mio::Waker>,
    /// **v9 ctx-vtable (§7.2).** The host-owned token-capacity permit map the
    /// platform poll-fns acquire against via [`host_acquire`]. Wired by
    /// [`block_on_reactor`] after the [`TokenPool`] is constructed (`None` for a
    /// fixture reactor with no pool — `acquire` then resolves unrestricted). Shared
    /// (`Rc`) with [`ReactorEnv`], whose blocking-branch / global-budget acquires use
    /// the SAME pool.
    pool: Option<Rc<TokenPool>>,
    /// **v9 ctx-vtable (§7.2).** The per-effect **held-permit ledger** keyed by the
    /// in-flight effect's identity (its [`RegId`], the registrant the poll-fn bracket
    /// stamps): which tokens each effect currently holds a permit on. Makes `acquire`
    /// idempotent per effect (a re-poll re-`acquire`s without double-counting) and is
    /// what `release_all` consults on `Ready`/cancel. Reactor-thread only (§2.8).
    held: HashMap<RegId, Vec<u64>>,
}

impl Reactor {
    /// Build a fresh reactor (one `mio::Poll`).
    ///
    /// Single-trampoline cutover, Stage-2 (`design/arch/platform-interface.md`
    /// §6.8.0a): this is the **eager-cheap** reactor — `epoll_create` + one eventfd
    /// per top-level drive (~2 syscalls), constructed unconditionally. It is the
    /// blessed fallback (a permanently-valid behaviour, NOT an interim). A
    /// pure-blocking program drives to `Ready` on the first poll and never calls
    /// `turn()`, so it pays only these two syscalls and never blocks the `Poll`.
    /// The truly-lazy `Poll` (construct nothing for a pure-blocking program) is the
    /// follow-up refinement deferred here for its capacity-park-release lost-wake
    /// soundness obligation.
    pub fn new() -> std::io::Result<Self> {
        let poll = mio::Poll::new()?;
        // The cross-thread wakeup on the reserved token (slice 6 — the wakeable
        // rayon→reactor bridge). Registered once here; `wake()` is thread-safe.
        let bridge_waker = Arc::new(mio::Waker::new(poll.registry(), BRIDGE_WAKE_TOKEN)?);
        Ok(Reactor {
            poll,
            events: Events::with_capacity(64),
            next_fd_token: 1,
            fd_waiters: HashMap::new(),
            timer_heap: BinaryHeap::new(),
            timer_waiters: HashMap::new(),
            next_timer_id: 1,
            next_reg: 1,
            current_registrant: None,
            bridge_waker,
            pool: None,
            held: HashMap::new(),
        })
    }

    /// Wire the host-owned [`TokenPool`] into the reactor so the v9 `ctx` vtable's
    /// [`host_acquire`] can take/return token permits (§7.2). Called once by
    /// [`block_on_reactor`] after the pool is constructed, before any poll-fn runs.
    fn set_pool(&mut self, pool: Rc<TokenPool>) {
        self.pool = Some(pool);
    }

    /// **v9 ctx-vtable `acquire`** (`reactor.md §7.2`): take a permit on `token`'s
    /// capacity-`N` pool for the currently-polling effect (its [`RegId`] =
    /// [`Reactor::current_registrant`]). Returns [`CAcquire::Acquired`] if a permit is
    /// held (idempotent per effect — a re-acquire on a token already held does NOT
    /// consume a second permit) or [`CAcquire::Parked`] if the slot is full (the
    /// `waker` is enqueued identity-tagged so a cancel can remove it). `token == 0`
    /// and a fixture reactor with no pool both resolve `Acquired` (unrestricted).
    ///
    /// Runs on the reactor thread inside the poll-fn call (the B1 reborrow window), so
    /// the `RefCell` permit map + the `held` ledger stay lock-free (§2.8).
    ///
    /// # Safety
    /// `waker` is the live C-ABI waker the platform passed; its `data` is the boxed
    /// `std::task::Waker` [`make_cabi_waker`] produced.
    unsafe fn acquire_permit(&mut self, token: u64, capacity: u32, waker: *const CWaker) -> CAcquire {
        if token == 0 {
            return CAcquire::Acquired; // commutative — never touches map/ledger.
        }
        let effect = self.current_registrant.unwrap_or(0);
        // Idempotent per in-flight effect: a token already held ⇒ Acquired, no 2nd permit.
        if let Some(tokens) = self.held.get(&effect)
            && tokens.contains(&token)
        {
            return CAcquire::Acquired;
        }
        let Some(pool) = self.pool.clone() else {
            return CAcquire::Acquired; // no pool wired (fixture reactor) ⇒ unrestricted.
        };
        let degree = pool.degree;
        let sized = capacity.max(1).min(degree).max(1);
        let mut slots = pool.slots.borrow_mut();
        let slot = slots.entry(token).or_insert_with(|| TokenSlot {
            permits: sized,
            capacity: sized,
            waiters: VecDeque::new(),
        });
        if slot.permits > 0 {
            slot.permits -= 1;
            drop(slots);
            self.held.entry(effect).or_default().push(token);
            CAcquire::Acquired
        } else {
            // Park: enqueue an identity-tagged std `Waker` recovered from the C-ABI
            // waker (its `data` is a boxed `std::task::Waker`). A later `release_all`
            // pops the front (FIFO ⇒ capacity-1 source order, §8.2).
            let id = pool.next_waiter.get();
            pool.next_waiter.set(id + 1);
            // SAFETY: caller obligation — `waker` is a live C-ABI waker whose `data`
            // is the boxed `std::task::Waker` (make_cabi_waker).
            let std_waker = unsafe { (*((*waker).data as *const Waker)).clone() };
            slot.waiters.push_back((id, std_waker));
            CAcquire::Parked
        }
    }

    /// **v9 ctx-vtable `retire`** (`reactor.md §7.2`): drop `token`'s permit pool and
    /// wake any parked waiters so they re-poll and observe the gone resource. Called
    /// by a Retire/`close` leaf after `close(r)`. Idempotent (remove-if-present);
    /// `token == 0` / no pool ⇒ no-op.
    fn retire_token(&mut self, token: u64) {
        if token == 0 {
            return;
        }
        let Some(pool) = self.pool.clone() else {
            return;
        };
        let wakers: Vec<Waker> = {
            let mut slots = pool.slots.borrow_mut();
            match slots.remove(&token) {
                Some(slot) => slot.waiters.into_iter().map(|(_, w)| w).collect(),
                None => Vec::new(),
            }
        };
        for w in wakers {
            w.wake();
        }
    }

    /// **v9 trampoline-owned release** (`reactor.md §7.3`): release every permit the
    /// effect `reg` holds — incrementing each token's slot + FIFO-waking its front
    /// parked waiter — and clear the ledger entry. Called eagerly on the effect's
    /// `Ready` (before `TaskPoll::Ready`) AND on its drop = cancellation (via
    /// [`ReactorInterest::drop`]); the first call removes the ledger entry, so the
    /// second is a no-op (no double-release — Principle 20). Reactor-thread only.
    fn release_all(&mut self, reg: RegId) {
        let Some(tokens) = self.held.remove(&reg) else {
            return;
        };
        let Some(pool) = self.pool.clone() else {
            return;
        };
        for token in tokens {
            // Detach the front waiter UNDER the borrow, drop the borrow, THEN wake
            // (the `Drop for Permit` S2 hardening — wake outside the `slots` borrow).
            let waker = {
                let mut slots = pool.slots.borrow_mut();
                match slots.get_mut(&token) {
                    Some(slot) => {
                        slot.permits += 1;
                        slot.waiters.pop_front().map(|(_, w)| w)
                    }
                    None => None,
                }
            };
            if let Some(w) = waker {
                w.wake();
            }
        }
    }

    /// A clone of the cross-thread wakeup handle ([`Reactor::bridge_waker`]) for
    /// the executor's task `Waker` ([`ExecutorWaker`]).
    fn bridge_waker(&self) -> Arc<mio::Waker> {
        Arc::clone(&self.bridge_waker)
    }

    /// `true` while any fd or timer waiter is outstanding (the executor must keep
    /// turning).
    fn has_waiters(&self) -> bool {
        !self.fd_waiters.is_empty() || !self.timer_waiters.is_empty()
    }

    /// Register read/write readiness on a raw fd (the `register_readable` /
    /// `register_writable` callback body). **Idempotent** (I2/M1): a poll-fn
    /// re-registers interest on EVERY `Pending` (the v7 poll-fn contract), so
    /// this is reached repeatedly for the same fd:
    ///
    /// - **fd not currently registered** (first registration, or re-arming after
    ///   the reactor's one-shot deregister fired) → `mio::register` succeeds; we
    ///   stash a fresh waker clone. This is the path that prevents the lost
    ///   wakeup: after a fire+deregister, the next `Pending` re-arms interest.
    /// - **fd still registered** (a sibling leaf woke this poll while THIS leaf's
    ///   registration is still live) → mio returns `EEXIST`; the existing
    ///   registration + its stashed waker stand and will fire on readiness, so we
    ///   keep them and drop this redundant re-register. The poll-fn's own fresh
    ///   waker is freed by its caller (`EffectPoll::poll`). No double-registration,
    ///   no lost wakeup either way.
    ///
    /// Any other error is a genuine reactor bug — surface it.
    ///
    /// # Safety
    /// `waker` is a live C-ABI waker the platform handed in (borrowed); this
    /// clones it to own a copy.
    unsafe fn register_fd(&mut self, fd: RawFd, waker: *const CWaker, interest: Interest) {
        let token = self.next_fd_token;
        self.next_fd_token += 1;
        let mut src = SourceFd(&fd);
        match self.poll.registry().register(&mut src, Token(token), interest) {
            Ok(()) => {
                let owned = unsafe { OwnedCWaker::clone_from_ref(waker) };
                // Stamp the entry with the leaf currently being polled (finding #3,
                // §2.16) — `0` (untagged) if armed outside a poll bracket.
                let reg = self.current_registrant.unwrap_or(0);
                self.fd_waiters.insert(token, (fd, owned, reg));
            }
            Err(e) if e.raw_os_error() == Some(libc::EEXIST) => {
                // Already registered (sibling re-poll while still parked): keep
                // the live registration; this re-register is a no-op.
                self.next_fd_token -= 1; // token unused
            }
            Err(e) => panic!("reactor: fd register failed: {e}"),
        }
    }

    /// Register a monotonic-deadline timer (the `register_timer` callback body).
    ///
    /// # Safety
    /// `waker` is a live C-ABI waker the platform handed in (borrowed).
    unsafe fn register_timer(&mut self, deadline_nanos: u64, waker: *const CWaker) {
        let id = self.next_timer_id;
        self.next_timer_id += 1;
        let owned = unsafe { OwnedCWaker::clone_from_ref(waker) };
        // Stamp with the current registrant (finding #3, §2.16).
        let reg = self.current_registrant.unwrap_or(0);
        self.timer_heap.push(Reverse(TimerEntry { deadline_nanos, id }));
        self.timer_waiters.insert(id, (owned, reg));
    }

    /// Allocate a fresh [`RegId`] for an [`EffectPoll`] (finding #3, §2.16). Called
    /// once per leaf in `EffectPoll::new` (through the `host.host` raw-`*mut Reactor`
    /// reborrow, the B1 provenance invariant). Monotonic; never returns `0`.
    fn alloc_reg(&mut self) -> RegId {
        let reg = self.next_reg;
        self.next_reg += 1;
        reg
    }

    /// Actively tear down every fd/timer interest tagged `reg` (finding #3, §2.16) —
    /// the body of [`ReactorInterest::drop`]. A cancelled in-flight [`EffectPoll`]
    /// (race loser, timed-out / disconnected / shutdown-cleared strand) calls this
    /// so its armed `fd_waiters` / `timer_waiters` entries + `mio` registrations do
    /// not leak until the fd next readies (or for the whole drive). Without it the
    /// maps + mio registrations accumulate unboundedly under volume cancellation in
    /// a long-running reactor (the §2.16 leak this fixes).
    ///
    /// fd entries are `mio`-deregistered; timer entries are dropped from the map
    /// (their `timer_heap` slot becomes a tombstone `turn()` already tolerates — the
    /// `remove` guard finds nothing and skips). Scanning by tag is O(live waiters);
    /// cancellation is rarer than steady-state and the maps are bounded by in-flight
    /// leaves — acceptable (Principle 6). `reg == 0` (untagged) is a no-op.
    ///
    /// Runs on the reactor thread between polls/turns (never concurrently with a
    /// poll-fn or `turn()`), so the `&mut self` reborrow is sound (B1).
    fn deregister(&mut self, reg: RegId) {
        if reg == 0 {
            return;
        }
        // fd waiters tagged `reg`: mio-deregister + drop from the map.
        let fd_tokens: Vec<usize> = self
            .fd_waiters
            .iter()
            .filter(|(_, (_, _, r))| *r == reg)
            .map(|(t, _)| *t)
            .collect();
        for token in fd_tokens {
            if let Some((fd, _waker, _reg)) = self.fd_waiters.remove(&token) {
                let mut src = SourceFd(&fd);
                let _ = self.poll.registry().deregister(&mut src);
            }
        }
        // timer waiters tagged `reg`: drop from the map (heap entries tombstone).
        self.timer_waiters.retain(|_, (_, r)| *r != reg);
    }

    /// Total live fd + timer waiters — the finding-#3 leak witness for the unit
    /// tests (a dropped in-flight leaf must bring this back to its pre-arm value).
    #[cfg(test)]
    pub(crate) fn waiter_count(&self) -> usize {
        self.fd_waiters.len() + self.timer_waiters.len()
    }

    /// Drive one reactor turn: block in `mio::poll` until the soonest timer
    /// deadline (or a registered fd becomes ready), then fire every ready fd /
    /// expired-timer waker. Bounded — never blocks indefinitely (the timeout is
    /// always finite, capped at `max_block`).
    fn turn(&mut self, max_block: Duration) {
        // Timeout = min(soonest timer deadline − now, max_block); if no timer,
        // just `max_block` (an fd may still become ready first). Never `None`.
        let now = monotonic_nanos();
        let timeout = match self.timer_heap.peek() {
            Some(Reverse(t)) => {
                let remaining = t.deadline_nanos.saturating_sub(now);
                Duration::from_nanos(remaining).min(max_block)
            }
            None => max_block,
        };

        // Block for readiness. (A spurious early return just means another turn.)
        let _ = self.poll.poll(&mut self.events, Some(timeout));

        // 1. Fire ready fd waiters (and tear down their registration — one-shot).
        let ready_tokens: Vec<usize> = self.events.iter().map(|e| e.token().0).collect();
        for token in ready_tokens {
            if let Some((fd, waker, _reg)) = self.fd_waiters.remove(&token) {
                let mut src = SourceFd(&fd);
                let _ = self.poll.registry().deregister(&mut src);
                waker.wake();
            }
        }

        // 2. Fire expired timers.
        let now = monotonic_nanos();
        while let Some(Reverse(t)) = self.timer_heap.peek() {
            if t.deadline_nanos > now {
                break;
            }
            let Reverse(t) = self.timer_heap.pop().unwrap();
            if let Some((waker, _reg)) = self.timer_waiters.remove(&t.id) {
                waker.wake();
            }
        }
    }

}

// --- The three `HostCtx` register callbacks (C-ABI) ------------------------

// B1 provenance invariant (shared by all three callbacks): `host` is the raw
// `*mut Reactor` the executor handed to `make_host_ctx` — NOT a pointer derived
// from any `&Reactor`. Each callback reborrows `&mut *(host as *mut Reactor)`
// for the duration of its body ONLY and mutates the reactor through it. Because
// `host` carries raw-pointer (not shared-reference) provenance, writing through
// this reborrow is sound under Stacked/Tree Borrows. The reborrow does not alias
// `block_on_reactor`'s between-poll `&mut *reactor_ptr` (the `turn()` reborrow):
// both reborrow the SAME raw pointer over non-overlapping lifetimes — a poll-fn
// runs only *inside* `Future::poll`, `turn()` only *between* polls, never
// concurrently — so no two `&mut Reactor` ever coexist.

unsafe extern "C" fn host_register_readable(host: *const c_void, fd: i32, waker: *const CWaker) {
    // SAFETY: see the B1 provenance invariant above — `host` is the raw
    // `*mut Reactor`; this transient `&mut` does not overlap the `turn()` `&mut`.
    let r = unsafe { &mut *(host as *mut Reactor) };
    unsafe { r.register_fd(fd as RawFd, waker, Interest::READABLE) };
}

unsafe extern "C" fn host_register_writable(host: *const c_void, fd: i32, waker: *const CWaker) {
    // SAFETY: see the B1 provenance invariant above.
    let r = unsafe { &mut *(host as *mut Reactor) };
    unsafe { r.register_fd(fd as RawFd, waker, Interest::WRITABLE) };
}

unsafe extern "C" fn host_register_timer(host: *const c_void, deadline_nanos: u64, waker: *const CWaker) {
    // SAFETY: see the B1 provenance invariant above.
    let r = unsafe { &mut *(host as *mut Reactor) };
    unsafe { r.register_timer(deadline_nanos, waker) };
}

/// The v9 `ctx` vtable `acquire` callback (`reactor.md §7.2`): the platform poll-fn
/// asks for a permit on its projected `(token, capacity)`. Reborrows the reactor
/// (B1 provenance — transient, inside the poll-fn call) and delegates to
/// [`Reactor::acquire_permit`], which keys held permits by the currently-polling
/// effect's identity (idempotent per effect).
unsafe extern "C" fn host_acquire(
    host: *const c_void,
    token: u64,
    capacity: u32,
    waker: *const CWaker,
) -> CAcquire {
    // SAFETY: B1 provenance invariant — `host` is the raw `*mut Reactor`; transient
    // `&mut`, no overlap with `turn()` (we are inside a poll-fn call).
    let r = unsafe { &mut *(host as *mut Reactor) };
    // SAFETY: `waker` is the live C-ABI waker the host projected for this poll.
    unsafe { r.acquire_permit(token, capacity, waker) }
}

/// The v9 `ctx` vtable `retire` callback (`reactor.md §7.2`): a Retire/`close` leaf
/// ends a token's scheduling identity. B1 reborrow; idempotent.
unsafe extern "C" fn host_retire(host: *const c_void, token: u64) {
    // SAFETY: B1 provenance invariant — see [`host_acquire`].
    let r = unsafe { &mut *(host as *mut Reactor) };
    r.retire_token(token);
}

/// Build the `HostCtx` vtable over a reactor, given its raw `*mut Reactor`.
///
/// **B1 provenance invariant.** `host` is set to `reactor_ptr` directly — the
/// raw pointer the executor (`block_on_reactor`) also uses for `turn()`. It is
/// deliberately NOT derived from a `&Reactor`: the three `register_*` callbacks
/// reborrow `&mut *(host as *mut Reactor)` and MUTATE the reactor, and a `host`
/// carrying shared-reference provenance would make every such write Undefined
/// Behaviour under Stacked/Tree Borrows (a `&mut` reborrow of a tag derived from
/// `&T`, and — worse — `turn()`'s unique reborrow would invalidate that shared
/// tag from the 2nd turn on). Routing both the poll-fn path and the `turn()`
/// path through the same raw pointer means they share one provenance and are
/// sound precisely because their `&mut` lifetimes never overlap (poll-fns run
/// inside `Future::poll`; `turn()` runs only between polls — `block_on_reactor`
/// never holds a `&mut reactor` across a poll).
///
/// The `Waker` pointer types differ only nominally between the
/// `cranelisp_platform` and `cranelisp_types` projections — both are the same
/// C-ABI — so the `register_*` signatures match the vtable field types exactly.
fn make_host_ctx(reactor_ptr: *mut Reactor) -> HostCtx {
    HostCtx {
        register_readable: host_register_readable,
        register_writable: host_register_writable,
        register_timer: host_register_timer,
        acquire: host_acquire,
        retire: host_retire,
        host: reactor_ptr as *const c_void,
    }
}

// ===========================================================================
// EffectPoll — the one await boundary (App. B).
// ===========================================================================

/// The reactor-registration handle an [`EffectPoll`] OWNS (finding #3, §2.16): a
/// RAII binding of the *reactor interest's* lifetime to the future, exactly as
/// `Option<Permit>` binds the *permit's* (§2.9). Its `Drop` actively deregisters
/// every fd/timer interest this leaf armed — the active-deregistration that the
/// §2.9 Chunk-A permit-only path deferred to Chunk C. **No hand-written
/// `Drop for EffectPoll`**: this field's own drop glue IS the deregistration path
/// (the structural minimum — Principle 18).
///
/// Lifecycle parity with the permit:
/// - **drop-while-`Pending`** (cancellation) → `Drop` deregisters the live fd/timer
///   interest. This is the leak fix.
/// - **`Ready`** → the fd entry was already removed by `turn()`'s one-shot
///   deregister and a timer self-clears at its deadline, so the eventual
///   future-drop `deregister` is a safe no-op (no eager dereg is added — unlike the
///   permit, reactor interest has no `join_all`-style hold that would starve a
///   sibling; §2.16 documents this deliberate asymmetry).
struct ReactorInterest {
    /// The raw `*mut Reactor` (the B1 provenance pointer — the `host.host` handle).
    /// May be **null** for a leaf built with a no-reactor fixture `HostCtx` (the
    /// permit-lifecycle unit tests), in which case there is nothing to deregister.
    reactor: *mut Reactor,
    /// This leaf's registrant tag (finding #3). `0` ⇒ no interest to tear down.
    reg: RegId,
}

/// Scope-guard that clears [`Reactor::current_registrant`] when dropped — the
/// panic-safe bracket for the finding-#3 poll-fn tagging (S96 Chunk C, C2-review
/// forward item #2, §2.16). A poll-fn that panics mid-[`EffectPoll::poll`] would
/// otherwise skip the explicit `current_registrant = None` clear, leaving a stale
/// `Some(reg)` that mis-tags the NEXT leaf's fd/timer registrations. Binding the
/// clear to this guard's `Drop` runs it on BOTH a normal return and an unwind.
/// Cheap: one nullable pointer + a single field write on drop.
struct RegistrantGuard(*mut Reactor);

impl Drop for RegistrantGuard {
    fn drop(&mut self) {
        if self.0.is_null() {
            return;
        }
        // SAFETY: B1 provenance — `self.0` is the raw `*mut Reactor` (`host.host`).
        // The guard drops inside `EffectPoll::poll` (normal return) or during its
        // unwind, on the reactor thread between polls/turns — no overlap with a
        // concurrent `turn()` or poll-fn reborrow.
        unsafe { (*self.0).current_registrant = None };
    }
}

impl Drop for ReactorInterest {
    fn drop(&mut self) {
        if self.reactor.is_null() || self.reg == 0 {
            return; // no live reactor / never armed under a tag — nothing to do.
        }
        // SAFETY: B1 provenance invariant — `reactor` is the raw `*mut Reactor`
        // (the `host.host` handle), NOT derived from a `&Reactor`. This `Drop` runs
        // on the reactor thread when the future is dropped — between polls/turns,
        // never concurrently with a poll-fn's reborrow or `turn()`'s reborrow — so
        // this transient `&mut` does not alias any other `&mut Reactor`.
        let r = unsafe { &mut *self.reactor };
        // v9 ctx-vtable (`reactor.md §7.3`): on a cancellation drop (the future never
        // reached `Ready`), release every permit this effect holds AND deregister its
        // reactor interest — keyed by the same identity, both from the host's ledger,
        // without ever re-entering the poll-fn. On the `Ready` path `release_all` was
        // already called (ledger entry gone) so this release is a no-op (Principle 20).
        r.release_all(self.reg);
        r.deregister(self.reg);
    }
}

/// RAII holder of a reactor-deferred poll effect's **state-closure keep-alive ref**
/// — the runtime-owned keep-alive mandated by `bounded-contexts.md §4b`
/// **invariant 15** (FIXME 0486 bug #2). A poll-shape effect's baked heap arguments
/// live in the host-built state-closure at the `IO_TAG_EFFECT_POLL` node's field-0;
/// those args must stay live from establish (`io::await_poll_node` →
/// [`EffectPoll::new_owning`]) until the reactor resolves the effect. Under the
/// **net-zero-inc** variant, `await_poll_node` takes ONE extra RC ref on the
/// state-closure (`rc_inc`) and hands it here — the node's field-0 is left UNTOUCHED
/// (no sentinel), so the sub-tree's own `consume_io_tree` / `dec_shallow_io` tag-4
/// arm still dec's the node's ref exactly as before. This guard releases the
/// keep-alive ref **exactly once** at resolve:
///
/// - on `Poll::Ready` — [`EffectPoll::poll`] calls [`StateClosure::consume`] AFTER
///   reading the result slot;
/// - on cancel (the future drops while `Pending`) — this guard's `Drop` runs
///   `consume` on the still-held ref.
///
/// Each `consume` is one `consume_closure` (an RC dec that runs the backend drop
/// glue + deallocs ONLY on the closure's true last ref). So the closure is freed at
/// the LATER of {node-release, effect-resolve}: on the normal path resolve precedes
/// node-release (node-release frees — byte-identical timing to pre-fix); on the
/// launched path the early node-release only dec's (this keep-alive ref survives the
/// teardown so the deferred send reads live args), and resolve frees. The
/// zero-after-consume makes "this ref released exactly once" *representable*
/// (Principle 20): once `consume` has run on either path the handle is `0` and the
/// other path is a no-op. `0` is also the constructor default (fixture/test leaves
/// that hold no keep-alive ref), so the guard is inert there; `consume_closure`
/// itself no-ops on the `0`/sub-`NULLARY_THRESHOLD` handle, double-safe.
struct StateClosure(i64);

impl StateClosure {
    /// Release the keep-alive ref NOW (one `consume_closure` — an RC dec, running
    /// drop glue + dealloc only on the closure's true last ref), if still held.
    /// Idempotent — zeroes the handle so a later `consume`/`Drop` is a no-op. The
    /// exactly-once release keyed to whichever resolve path fires first (invariant 15).
    fn consume(&mut self) {
        let clo = self.0;
        if clo != 0 {
            // Zero FIRST so a re-entrant / subsequent path cannot double-release.
            self.0 = 0;
            // `consume_closure` atomically dec's the closure RC and, on last ref,
            // invokes the embedded drop glue (dec'ing the baked args) + deallocs.
            crate::drop::consume_closure(clo);
        }
    }
}

impl Drop for StateClosure {
    fn drop(&mut self) {
        // Cancellation path (future dropped while Pending): release the still-held
        // keep-alive ref. On the `Ready` path `consume` already ran (handle == 0) so
        // this is a no-op — the exactly-once guarantee (invariant 15, Principle 20).
        self.consume();
    }
}

/// Byte offset of the reserved **result slot** within a poll-fn `state` — the
/// generic env-offset result read (S94 R1 seam decision 3, FIXME 0457). `state`
/// is the env base of the host-built state-closure (`closure + 32`), and the
/// result slot is the FIRST env slot, so the result is at `state + 0`. The S93
/// per-effect `ResultReader` fn-pointer collapses to this one offset read.
/// (`design/int/reactor.md §2.5`, `design/backend/io-trampoline.md §12.2`.)
const RESULT_SLOT_OFFSET: isize = 0;

/// The async leaf future: `poll` calls the platform poll-fn, maps `Ready` → the
/// value (read generically from the env result slot at [`RESULT_SLOT_OFFSET`])
/// and `Pending` → a park on the reactor, and emits the strand observability
/// events.
///
/// `EffectPoll: Unpin` — every field is a pointer / `Copy` scalar or the RAII
/// `ReactorInterest` (pointer + scalar) — so it polls through a plain `&mut`. The
/// lifetime ties the borrowed `HostCtx` to the future.
///
/// **v9 ctx-vtable release (`reactor.md §7.3`).** The future no longer OWNS an
/// `Option<Permit>` it acquired up-front — under the ctx-vtable model the *platform
/// poll-fn* acquires its token permit itself via `ctx.acquire`, and the host tracks
/// every held permit by this effect's identity (`reg`) in its per-effect ledger
/// ([`Reactor::held`]). Release is **trampoline-owned**, keyed by `reg`, fired on
/// exactly one of two mutually-exclusive paths:
///
/// - **eagerly on `Poll::Ready`** — [`EffectPoll::poll`] calls
///   [`Reactor::release_all`]`(reg)` BEFORE returning `TaskPoll::Ready`, freeing every
///   permit this effect holds the instant its result is available. NOT deferred to
///   future-drop: in a `join_all` an individual leaf is not dropped until the whole
///   join completes, so deferring would starve same-token waiters until the slowest
///   sibling finishes (§2.9 rationale, unchanged).
/// - **on future-drop = cancellation** — [`ReactorInterest::drop`] calls
///   `release_all(reg)` (and `deregister(reg)`) if the future was dropped before
///   `Ready` (cancelled / timed-out / race-lost / disconnected — the A→C contract).
///   **No `Drop for EffectPoll` is hand-written**; the `_interest` field's drop glue
///   IS the cancellation release/dereg path (Principle 18).
///
/// "released exactly once" is *representable* (Principle 20): `release_all` removes
/// the ledger entry on its first call, so the eager-on-`Ready` release leaves nothing
/// for the subsequent field-drop to release (a no-op).
pub struct EffectPoll<'h> {
    state: *mut c_void,
    poll_fn: PollFn,
    host: &'h HostCtx,
    strand: StrandId,
    /// Number of times `poll` has run — distinguishes dispatch (0) from a resume
    /// (>0) for the strand events.
    polls: u32,
    /// This leaf's registrant tag (finding #3, §2.16) — allocated in
    /// [`EffectPoll::new`], stamped onto every fd/timer this leaf arms (via the
    /// poll-bracket below), and used by `_interest`'s drop to deregister them.
    /// `0` for a no-reactor fixture leaf.
    reg: RegId,
    /// The RAII reactor-registration handle (finding #3, §2.16). Underscore-prefixed
    /// because it is **drop-only** — the future never reads it; its `Drop` actively
    /// deregisters this leaf's reactor interest when the future drops (the
    /// cancellation leak fix), paralleling the `Option<Permit>` drop-release.
    _interest: ReactorInterest,
    /// The runtime-owned keep-alive ref on this reactor-deferred effect's
    /// state-closure (`bounded-contexts.md §4b` invariant 15; FIXME 0486). Holds an
    /// extra net-zero-inc RC ref on the state-closure (baked heap args) across the
    /// effect's suspend arc and releases it **exactly once** at resolve — on
    /// `Poll::Ready` (via [`StateClosure::consume`] after the result read) or on
    /// cancel-drop (this field's own `Drop`). `0` for a fixture/test leaf that holds
    /// no keep-alive ref (constructed via the [`EffectPoll::new`] convenience
    /// wrapper). See [`StateClosure`] for the exactly-once discipline.
    _state_closure: StateClosure,
}

impl<'h> EffectPoll<'h> {
    /// Build an effect leaf over a poll-fn + its state, charged to `strand`. **v9
    /// ctx-vtable (`reactor.md §7.5`):** the future is **scheduling-blind** — it does
    /// NO pre-poll acquire and reads NO `(token, capacity)`/`role` off the node. The
    /// *platform poll-fn* acquires its own token permit via `ctx.acquire`; the host
    /// tracks held permits by this leaf's identity (`reg`) and releases them on
    /// `Ready` (eager, [`EffectPoll::poll`]) or on drop ([`ReactorInterest::drop`]).
    ///
    /// `pub(crate)`, not `pub`: the only construction sites are this crate's
    /// trampoline (`io::await_poll_node`) and unit tests — no external crate builds an
    /// `EffectPoll`.
    ///
    /// This convenience wrapper owns **no** state-closure keep-alive (invariant 15) —
    /// it delegates to [`EffectPoll::new_owning`] with a `0` closure handle. It is the
    /// constructor for fixture/test leaves whose `state` is a stack/heap fixture the
    /// caller owns, NOT a moved-out backend state-closure the runtime must consume.
    /// The real trampoline path (`io::await_poll_node`) uses [`EffectPoll::new_owning`].
    ///
    /// # Safety
    /// `state` must be valid for the poll-fn for the future's lifetime, and must
    /// point at an env whose first `i64` slot ([`RESULT_SLOT_OFFSET`]) is the
    /// reserved result slot the poll-fn writes before returning `Ready`;
    /// `poll_fn` must obey the v9 poll-fn contract.
    ///
    /// `#[cfg(test)]`: the production trampoline always owns a state-closure and so
    /// calls [`EffectPoll::new_owning`] directly; this zero-keep-alive wrapper has
    /// only unit-test callers (fixture leaves).
    #[cfg(test)]
    pub(crate) unsafe fn new(
        state: *mut c_void,
        poll_fn: PollFn,
        host: &'h HostCtx,
        strand: StrandId,
    ) -> Self {
        // No runtime-owned state-closure (fixture/test leaf): `state_closure = 0`.
        unsafe { Self::new_owning(state, poll_fn, host, strand, 0) }
    }

    /// Build an effect leaf that holds a **keep-alive ref** on the state-closure —
    /// the runtime-owned keep-alive of `bounded-contexts.md §4b` **invariant 15**
    /// (FIXME 0486 bug #2). `state_closure` is the backend-built state-closure base
    /// pointer (the `IO_TAG_EFFECT_POLL` node's field-0) on which `io::await_poll_node`
    /// has just taken ONE extra net-zero-inc RC ref (`rc_inc`); the node's field-0 is
    /// left untouched. The returned [`EffectPoll`] holds that ref across the effect's
    /// suspend arc and releases it exactly once at resolve (see [`StateClosure`]).
    /// `state` is the poll-fn env base (`state_closure + 32`), the same pointer
    /// [`EffectPoll::new`] takes; passing `state_closure == 0` gives the
    /// no-keep-alive fixture behaviour.
    ///
    /// # Safety
    /// Same obligations as [`EffectPoll::new`] on `state`/`poll_fn`, plus: if
    /// `state_closure != 0` it must be a valid closure heap pointer carrying the
    /// caller's `rc_inc` keep-alive ref, which the runtime releases via
    /// `crate::drop::consume_closure` at resolve, and `state` must remain valid until
    /// that release (it points INTO `state_closure`, kept live by the ref).
    pub(crate) unsafe fn new_owning(
        state: *mut c_void,
        poll_fn: PollFn,
        host: &'h HostCtx,
        strand: StrandId,
        state_closure: i64,
    ) -> Self {
        // Mint this leaf's registrant tag from the reactor (finding #3, §2.16),
        // alongside the §2.9 permit acquire. The reactor is the `host.host` raw
        // `*mut Reactor` handle (B1). A no-reactor fixture `HostCtx` (the
        // permit-lifecycle unit tests) carries a NULL `host`, so there is no reactor
        // to tag against — `reg = 0`, an inert interest whose drop is a no-op.
        let reactor = host.host as *mut Reactor;
        let reg = if reactor.is_null() {
            0
        } else {
            // SAFETY: B1 — `host.host` is the raw `*mut Reactor`; `new` runs once,
            // inside a `Future::poll` on the reactor thread (the same window a
            // poll-fn reborrows in), so this transient `&mut` does not overlap
            // `turn()`'s reborrow.
            unsafe { (*reactor).alloc_reg() }
        };
        EffectPoll {
            state,
            poll_fn,
            host,
            strand,
            polls: 0,
            reg,
            _interest: ReactorInterest { reactor, reg },
            _state_closure: StateClosure(state_closure),
        }
    }
}

impl Future for EffectPoll<'_> {
    type Output = i64;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> TaskPoll<i64> {
        let this = self.get_mut();

        if this.polls == 0 {
            emit_strand_event(StrandEvent::EffectDispatched {
                strand: this.strand,
            });
        } else {
            emit_strand_event(StrandEvent::EffectResumed {
                strand: this.strand,
            });
        }
        this.polls += 1;

        // Project the executor's waker across the C-ABI; the poll-fn clones it if
        // it registers interest. Freed unconditionally after the call.
        let cwaker = make_cabi_waker(cx.waker().clone());
        // Bracket the poll-fn call (finding #3, §2.16): set `current_registrant` to
        // this leaf's tag so every fd/timer it arms during THIS poll is stamped with
        // `this.reg`, then clear it. A no-reactor fixture leaf (`reg == 0` / null
        // host) is not bracketed. The reborrow is the B1 pattern — transient, on the
        // reactor thread, non-overlapping with `turn()` and with the poll-fn's own
        // `register_*` reborrows (which run sequentially after this set).
        let reactor = this.host.host as *mut Reactor;
        let bracketed = !reactor.is_null() && this.reg != 0;
        // Panic-safe bracket (forward item #2, §2.16): the guard clears
        // `current_registrant` on the way out — normal return AND poll-fn panic
        // unwind — so a panicking poll-fn cannot leak a stale tag onto the next
        // leaf's registrations.
        let _reg_guard = if bracketed {
            // SAFETY: B1 — `host.host` is the raw `*mut Reactor`; transient `&mut`,
            // no overlap with `turn()` (we are inside `Future::poll`).
            unsafe { (*reactor).current_registrant = Some(this.reg) };
            Some(RegistrantGuard(reactor))
        } else {
            None
        };
        // SAFETY: `state`/`host`/`poll_fn` honour the v7 contract (constructor
        // safety obligation); `&cwaker` is a live C-ABI waker.
        let result = unsafe { (this.poll_fn)(this.state, this.host as *const HostCtx, &cwaker as *const CWaker) };
        // Clear the registrant bracket now (the guard's drop is the panic-path
        // backstop; this explicit drop keeps the common-path timing unchanged).
        drop(_reg_guard);
        drop_cabi_waker(cwaker);

        match result {
            CPoll::Ready => {
                // Generic env-offset result read (S94 R1 seam decision 3): the
                // poll-fn has written its i64 result into the reserved result
                // slot at `state + RESULT_SLOT_OFFSET`.
                // SAFETY: `state` points at the env whose first `i64` slot is the
                // result slot (constructor obligation).
                let value = unsafe {
                    *((this.state as *const i64).byte_offset(RESULT_SLOT_OFFSET))
                };
                // Keep-alive release (`bounded-contexts.md §4b` invariant 15; FIXME
                // 0486): the effect has resolved, so the runtime releases its
                // net-zero-inc keep-alive ref on the state-closure NOW — after the
                // result read above (which reads INTO `this.state`, a pointer inside
                // the closure, so the read must precede any last-ref free). This is
                // one `consume_closure` dec; it frees + runs the backend drop glue
                // only if this was the closure's true last ref (on the normal path
                // the node still holds its ref, so this dec does not free). `consume`
                // zeroes the handle so the subsequent field-drop is a no-op —
                // released exactly once (Principle 20). A fixture leaf holds no ref
                // (handle == 0) so this is inert. Ordering vs. the permit release
                // below is independent (closure heap vs. reactor ledger).
                this._state_closure.consume();
                // v9 eager release (`reactor.md §7.3`): release every permit this
                // effect (identity `reg`) holds BEFORE returning `Ready`. In a
                // `join_all` an individual leaf is not dropped until the whole join
                // completes, so deferring release to future-drop would starve
                // same-token waiters. `release_all` removes the ledger entry, so the
                // subsequent `_interest` drop's `release_all` is a no-op (no
                // double-release). A null-host fixture leaf (`reg == 0`) holds nothing.
                if !reactor.is_null() && this.reg != 0 {
                    // SAFETY: B1 — `host.host` is the raw `*mut Reactor`; transient
                    // `&mut`, inside `Future::poll` on the reactor thread, no overlap
                    // with `turn()` or the (already-returned) poll-fn reborrow.
                    unsafe { (*reactor).release_all(this.reg) };
                }
                TaskPoll::Ready(value)
            }
            CPoll::Pending => {
                emit_strand_event(StrandEvent::EffectSuspended {
                    strand: this.strand,
                });
                TaskPoll::Pending
            }
        }
    }
}

// ===========================================================================
// The token-capacity `Semaphore` pool (slice 3) — §2.8 / arch §8.1/§8.2.
//
// A host-owned permit map that bounds how many of a token's effects are in
// flight at once. It generalizes the rayon dispatcher's capacity-1 `SerialGroup`
// to an arbitrary pool size: *every effect acquires its token's permit before
// dispatch and releases on completion.*
//
// **Single-threaded, no atomics, no `Mutex`.** Admission runs on the ONE reactor
// thread for both partitions (a blocking branch is admitted *before* its
// `rayon::spawn`, the permit held across the wakeable bridge — see
// `io::run_par_node_async`), so the map is a plain `RefCell<HashMap<…>>`,
// mirroring the reactor's own `fd_waiters` map.
// ===========================================================================

/// One token's permit slot: `permits` free of `capacity`, plus a FIFO queue of
/// parked waiters' wakers. Created on the token's first acquire, sized to that
/// first `capacity` (first-writer-wins, §2.8) and never resized.
struct TokenSlot {
    /// Free permits remaining (`0..=capacity`).
    permits: u32,
    /// The capacity the FIRST acquirer sized this slot to (the value that
    /// stands under first-writer-wins reconciliation).
    capacity: u32,
    /// Parked waiters in FIFO order — the (capacity+1)th and beyond. A permit
    /// release wakes the FRONT (source order for capacity 1, §8.2). Each waiter
    /// carries a monotonic `WaiterId` (finding #4, §2.17) so a cancelled
    /// `AcquirePermit` can `retain`-remove its OWN stale waker by identity on drop —
    /// keeping the single-front-`pop` FIFO (and its source-order guarantee) intact
    /// while never waking a stranded waker.
    waiters: VecDeque<(u64, Waker)>,
}

/// The reserved well-known token for the **global admission budget** (§2.13) —
/// the single program-wide `Semaphore` bounding total in-flight detached strands
/// (the launch-and-continue memory bound). `u64::MAX` is a sentinel that is never
/// a real resource token, so its slot in the shared pool never collides with a
/// resource token's. Pre-sized (via the pool's `degree`) at construction.
pub(crate) const GLOBAL_BUDGET_TOKEN: u64 = u64::MAX;

/// The host-owned token-capacity pool: `token → TokenSlot`. Keyed on the
/// **node-read** `(token, capacity)` (`io::read_resource_token` / `read_capacity`).
/// Constructed single-sited in [`block_on_reactor`] alongside the [`Reactor`]
/// (§6.2 — divergence-proof by the intrinsics-hosting argument; int grows no
/// parallel pool builder).
///
/// **`degree` (slice 4, §2.13).** A program-chosen in-flight throttle that
/// composes with each token's platform-asserted capacity: a token's slot is sized
/// `min(node_capacity, degree)` (degree can only *tighten*, never loosen past the
/// capacity ceiling — spec §10.12.4.2). `degree == u32::MAX` (the default) is "no
/// throttle" — every slot is sized to its node capacity, preserving the
/// pre-slice-4 behaviour. The same `degree` pre-sizes the global-budget slot
/// ([`GLOBAL_BUDGET_TOKEN`]).
pub(crate) struct TokenPool {
    slots: RefCell<HashMap<u64, TokenSlot>>,
    /// The program degree throttle (§2.13). `u32::MAX` ⇒ no throttle.
    degree: u32,
    /// Monotonic source of parked-waiter identities (finding #4, §2.17). A `Cell`
    /// (not an atomic) — every acquire/park/drop runs on the ONE reactor thread
    /// (§2.8 single-thread invariant), so no synchronisation is needed. Starts at 1
    /// so `0` is never a live waiter id (a free `parked_id` sentinel is `None`, not
    /// `Some(0)`, but keeping `0` reserved is defensive).
    next_waiter: Cell<u64>,
}

impl TokenPool {
    /// A fresh empty pool with **no degree throttle** (`degree = u32::MAX`) — the
    /// pre-slice-4 behaviour, where each token slot is sized to its full node
    /// capacity. Slots are created lazily on first acquire.
    ///
    /// `#[cfg(test)]`: a test convenience for the pool/permit unit tests.
    /// Production drives construct the pool via [`with_degree`] (the degree knob).
    #[cfg(test)]
    pub(crate) fn new() -> Rc<Self> {
        Self::with_degree(u32::MAX)
    }

    /// A fresh empty pool with a program `degree` throttle (§2.13): every token
    /// slot is sized `min(node_capacity, degree)`, and the global-budget slot is
    /// pre-sized to `degree`. `degree == u32::MAX` ⇒ no throttle (see [`new`]).
    pub(crate) fn with_degree(degree: u32) -> Rc<Self> {
        Rc::new(TokenPool {
            slots: RefCell::new(HashMap::new()),
            degree: degree.max(1),
            next_waiter: Cell::new(1),
        })
    }

    /// Acquire a permit on `token` (sized `min(capacity, degree)` on first sight),
    /// charged to `strand`. `token == 0` ⇒ no acquire (unrestricted — full
    /// overlap). The returned [`AcquirePermit`] future resolves to a [`Permit`]
    /// whose drop releases the permit and wakes the front waiter.
    fn acquire(self: &Rc<Self>, token: u64, capacity: u32, strand: StrandId) -> AcquirePermit {
        AcquirePermit {
            pool: Rc::clone(self),
            token,
            capacity,
            strand,
            parked: false,
            is_global: false,
            parked_id: None,
        }
    }

    /// `true` if ANY token slot has a parked waiter (finding for the §8 armed-ness
    /// deadlock detector). A parked permit-waiter means the reactor is legitimately
    /// waiting (its holder is in-flight — §2.9 non-re-entry guarantees no permit
    /// cycle), so it counts as "armed" and must NOT trip the deadlock detector.
    /// Redundant-but-faithful: a permit holder is itself armed (fd/timer), so a
    /// parked waiter implies `has_waiters()` too — but the design lists this source
    /// explicitly (`reactor.md §8.2`), so it is checked directly.
    pub(crate) fn any_waiter_parked(&self) -> bool {
        self.slots.borrow().values().any(|s| !s.waiters.is_empty())
    }

    /// Acquire a permit on the reserved [`GLOBAL_BUDGET_TOKEN`] — the global
    /// admission gate the `IO_TAG_LAUNCH` arm takes before spawning a detached
    /// strand (§2.13). Sized to the pool's `degree` (the global bound); exhaustion
    /// parks the launch (the accept loop) until an in-flight strand completes and
    /// frees a permit. Emits the `GlobalBudget*` strand events (not `Token*`).
    fn acquire_global(self: &Rc<Self>, strand: StrandId) -> AcquirePermit {
        AcquirePermit {
            pool: Rc::clone(self),
            token: GLOBAL_BUDGET_TOKEN,
            capacity: self.degree,
            strand,
            parked: false,
            is_global: true,
            parked_id: None,
        }
    }
}

/// The await boundary for a token permit (§2.8). `poll`: if a permit is free,
/// decrement + `Ready(Permit)` (emitting `TokenAcquired`); else enqueue
/// `cx.waker()` (FIFO) + `Pending` (emitting `TokenParked` once). `token == 0`
/// resolves immediately with an inert permit (no map entry).
pub(crate) struct AcquirePermit {
    pool: Rc<TokenPool>,
    token: u64,
    capacity: u32,
    strand: StrandId,
    /// `true` once this future has emitted `TokenParked` / `GlobalBudgetParked` —
    /// so a re-poll that is still blocked does not re-emit the park event.
    parked: bool,
    /// `true` for an acquire on the reserved [`GLOBAL_BUDGET_TOKEN`] — emits the
    /// `GlobalBudget*` strand events instead of `Token*` (§2.13 / §3).
    is_global: bool,
    /// This future's own parked-waiter identity in the slot's FIFO (finding #4,
    /// §2.17). `None` until it parks; `Some(id)` while its waker sits in
    /// `slot.waiters`; cleared back to `None` on acquire (the releaser already
    /// popped it). [`Drop for AcquirePermit`] uses it to `retain`-remove ONLY this
    /// future's stale waker if it is cancelled while parked — no lost-wakeup, FIFO
    /// order preserved. `token == 0` never parks ⇒ stays `None` ⇒ drop is a no-op.
    parked_id: Option<u64>,
}

impl Future for AcquirePermit {
    type Output = Permit;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> TaskPoll<Permit> {
        let this = self.get_mut();

        // token 0 ⇒ unrestricted: resolve immediately with an inert permit.
        if this.token == 0 {
            return TaskPoll::Ready(Permit {
                pool: Rc::clone(&this.pool),
                token: 0,
                strand: this.strand,
                is_global: false,
            });
        }

        // Slot sizing = min(node_capacity, degree) (§2.13 part 1). For the global
        // token, `capacity` is already the degree, so min is idempotent.
        let degree = this.pool.degree;
        let sized = this.capacity.max(1).min(degree).max(1);
        let mut slots = this.pool.slots.borrow_mut();
        let slot = slots.entry(this.token).or_insert_with(|| TokenSlot {
            // First-writer-wins: this acquirer sizes the slot (degree-throttled).
            permits: sized,
            capacity: sized,
            waiters: VecDeque::new(),
        });

        // First-writer-wins reconciliation: a later, disagreeing capacity is
        // recorded (dev-facing) but does NOT resize the pool (§2.8 / arch §8.1).
        // (Compared against the degree-throttled effective capacity, since that is
        // what the slot is sized to.) The global token never disagrees with
        // itself, so this only fires for resource tokens.
        if !this.is_global && sized != slot.capacity {
            emit_strand_event(StrandEvent::TokenCapacityMismatch {
                strand: this.strand,
                token: this.token,
                first_capacity: slot.capacity,
                requested_capacity: sized,
            });
        }

        if slot.permits > 0 {
            slot.permits -= 1;
            // Acquired: the releaser already popped our waker (or we never parked),
            // so clear our parked identity (finding #4 — so the eventual drop is a
            // no-op, not a spurious `retain`).
            this.parked_id = None;
            emit_strand_event(if this.is_global {
                StrandEvent::GlobalBudgetAcquired { strand: this.strand }
            } else {
                StrandEvent::TokenAcquired { strand: this.strand, token: this.token }
            });
            TaskPoll::Ready(Permit {
                pool: Rc::clone(&this.pool),
                token: this.token,
                strand: this.strand,
                is_global: this.is_global,
            })
        } else {
            // Park: enqueue our waker in FIFO order, tagged with our own identity
            // (finding #4, §2.17). A permit release wakes the front (capacity-1 ⇒
            // source order, since first-poll enqueue order = source order, §8.2).
            let waker = cx.waker().clone();
            match this.parked_id {
                // Still parked from an earlier poll AND our entry is still queued
                // (rare under the single executor — the releaser normally pops+wakes
                // us before any re-poll): REPLACE our waker in place rather than
                // pushing a duplicate. This also closes the latent
                // push-on-every-`Pending` duplication the pre-finding-#4 code had.
                Some(id) if slot.waiters.iter().any(|(wid, _)| *wid == id) => {
                    for entry in slot.waiters.iter_mut() {
                        if entry.0 == id {
                            entry.1 = waker;
                            break;
                        }
                    }
                }
                // First park, or a re-park after our prior entry was popped (a
                // release woke us but a competitor re-took the permit): allocate a
                // fresh identity and enqueue at the back (FIFO).
                _ => {
                    let id = this.pool.next_waiter.get();
                    this.pool.next_waiter.set(id + 1);
                    slot.waiters.push_back((id, waker));
                    this.parked_id = Some(id);
                }
            }
            if !this.parked {
                this.parked = true;
                emit_strand_event(if this.is_global {
                    StrandEvent::GlobalBudgetParked { strand: this.strand }
                } else {
                    StrandEvent::TokenParked { strand: this.strand, token: this.token }
                });
            }
            TaskPoll::Pending
        }
    }
}

/// An acquired permit. Dropping it returns the permit to the token's pool and
/// wakes the front (FIFO) parked waiter. An inert permit (`token == 0`) is a
/// no-op on drop. A global-budget permit (`is_global`) emits `GlobalBudgetReleased`.
pub(crate) struct Permit {
    pool: Rc<TokenPool>,
    token: u64,
    strand: StrandId,
    /// `true` for a [`GLOBAL_BUDGET_TOKEN`] permit — emits `GlobalBudgetReleased`
    /// on drop instead of `TokenReleased` (§2.13).
    is_global: bool,
}

impl Drop for Permit {
    fn drop(&mut self) {
        if self.token == 0 {
            return; // unrestricted: nothing to release.
        }
        // Return the permit and detach the front waiter UNDER the borrow, then
        // DROP the borrow before `wake()` (S2 hardening). The `ExecutorWaker` only
        // writes an eventfd today, but waking outside the `slots` borrow keeps this
        // sound against any future re-entrant waker that might re-enter the pool.
        let waker = {
            let mut slots = self.pool.slots.borrow_mut();
            let Some(slot) = slots.get_mut(&self.token) else {
                return;
            };
            slot.permits += 1;
            emit_strand_event(if self.is_global {
                StrandEvent::GlobalBudgetReleased { strand: self.strand }
            } else {
                StrandEvent::TokenReleased { strand: self.strand, token: self.token }
            });
            // Detach the front waiter (FIFO). It will re-poll, find a free permit,
            // and acquire (re-establishing exclusion). Finding #4 (§2.17): the
            // front is now guaranteed LIVE — a cancelled-while-parked waiter
            // `retain`-removed its own entry on drop, so we never pop+wake a stale
            // waker (which would strand the freed permit + the next live waiter).
            slot.waiters.pop_front().map(|(_, w)| w)
        }; // `slots` borrow dropped here.
        if let Some(waker) = waker {
            waker.wake();
        }
    }
}

/// Finding #4 (§2.17) — an `AcquirePermit` dropped **while parked** (a future
/// cancelled before it acquired its permit: a race loser, a timed-out / shutdown-
/// cleared branch queued behind a full token or a full global budget) removes its
/// OWN stale waker from the slot's FIFO by identity. Without this, a later
/// [`Drop for Permit`] would `pop_front()` that stale waker and wake it (a no-op —
/// the future is gone) while the freed permit goes unclaimed and the next LIVE
/// waiter behind it is never woken ⇒ lost-wakeup / a free permit nobody can take.
///
/// `retain`-by-identity keeps the rest of the FIFO (and its source-order guarantee,
/// §8.2) intact — the rejected "pop-until-live" / "wake-all" alternatives cannot
/// (a `Waker` carries no liveness/identity signal; wake-all is a thundering herd
/// that destroys capacity-1 source order). `token == 0` never parks (`parked_id`
/// stays `None`) ⇒ this is a no-op. The global-budget acquire shares this machinery,
/// so a shutdown-cancelled accept-loop launch parked on a full global budget is
/// co-covered. Runs on the ONE reactor thread (§2.8), so the plain `RefCell`
/// borrow needs no synchronisation; `retain` is O(slot waiters) per cancel —
/// acceptable (cancellation is rarer than steady-state; Principle 6).
impl Drop for AcquirePermit {
    fn drop(&mut self) {
        let Some(id) = self.parked_id else {
            return; // never parked (acquired, or token 0) — nothing to remove.
        };
        // Detach the forward-target waker UNDER the borrow, drop the borrow, THEN
        // wake (the S2 hardening `Drop for Permit` uses — keep `wake()` outside the
        // `slots` borrow against a re-entrant waker).
        let forward = {
            let mut slots = self.pool.slots.borrow_mut();
            let Some(slot) = slots.get_mut(&self.token) else {
                return;
            };
            let before = slot.waiters.len();
            slot.waiters.retain(|(wid, _)| *wid != id);
            if slot.waiters.len() < before {
                // Our entry was still queued — we were parked, not yet woken.
                // Removing it is the whole of finding #4; no permit was freed for
                // us, so there is nothing to forward.
                None
            } else {
                // **Woken-then-cancelled permit-forwarding (S96 Chunk C, C2-review
                // forward item #1).** Our FIFO entry was already popped — a
                // `Drop for Permit` woke us (incrementing `permits`) but we are
                // dropped (cancelled: a race loser, a timed-out / shutdown-cleared
                // branch) BEFORE re-polling to claim that freed permit. The permit
                // is now claimable but the NEXT parked sibling behind us was never
                // pinged: under a `FuturesUnordered`-style "only-woken-re-poll"
                // executor (the supervisor, §2.12) that sibling is STRANDED
                // (lost-wakeup). Forward the permit by popping + waking the next
                // front waiter — the FIFO/source-order guarantee is preserved (we
                // wake the front, the same waiter a `Drop for Permit` would).
                // `select_all`-driven combinators re-poll all branches each turn so
                // they are unaffected, but this makes the fix substrate-wide
                // (supervisor + any future only-woken consumer).
                slot.waiters.pop_front().map(|(_, w)| w)
            }
        }; // `slots` borrow dropped here.
        if let Some(waker) = forward {
            waker.wake();
        }
    }
}

// ===========================================================================
// The supervisor — a single-threaded `JoinSet`-equivalent (§2.12).
//
// A `FuturesUnordered` of supervised detached-strand futures, owned by the
// reactor. The `IO_TAG_LAUNCH` arm (`io::launch_continue`) `spawn`s into it; the
// executor `drive`s it each loop iteration. Every member future is wrapped so
// EVERY termination is caught (`catch_unwind` + the reused `take_runtime_error`
// capture) and the §10 policy applied INSIDE the future — so a panic never
// unwinds into the executor and aborts the drive (§2.12). The set's item type is
// `()`: the executor only has to drain it.
// ===========================================================================

/// The per-effect-kind failure policy for a supervised detached strand (§2.12).
/// A reactor-construction config (gate (b): a scheduler-declared default, so it
/// stays out of the pure language). The minimal default is [`SupervisorPolicy::LogAndDrop`];
/// the web "500-on-dropped-connection" mapping is the serve-loop's job, layered
/// on top of the `StrandFailed` event this policy emits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub(crate) enum SupervisorPolicy {
    /// Catch + record (`StrandFailed`) + drop the strand. Never re-raises (no
    /// parent), never aborts the drive. The minimal default.
    #[default]
    LogAndDrop,
}

/// Apply the §10 supervisor policy at the intrinsics layer: **catch + record +
/// drop**. Emits `StrandFailed` to the strand sink (the `/strand` dev surface +
/// `/qa`'s panic-survival assertion read it). It NEVER re-raises and NEVER aborts
/// the drive — the "500 to the client" is the application/platform mapping
/// layered on top (§2.12).
fn apply_policy(policy: SupervisorPolicy, strand: StrandId, message: String) {
    match policy {
        SupervisorPolicy::LogAndDrop => {
            emit_strand_event(StrandEvent::StrandFailed { strand, message });
        }
    }
}

/// The supervisor: a single-threaded set of supervised detached-strand futures.
/// `push` is `&self` (interior mutability via `RefCell`) so the `IO_TAG_LAUNCH`
/// arm can add a strand while the set is being driven; draining removes each
/// member as it completes. Constructed single-sited in [`block_on_reactor`]
/// alongside the [`Reactor`]/[`TokenPool`] and reached through [`ReactorEnv`].
pub(crate) struct Supervisor<'h> {
    strands: RefCell<FuturesUnordered<Pin<Box<dyn Future<Output = ()> + 'h>>>>,
    policy: SupervisorPolicy,
}

impl<'h> Supervisor<'h> {
    /// A fresh empty supervisor with the given failure policy.
    pub(crate) fn new(policy: SupervisorPolicy) -> Rc<Self> {
        Rc::new(Supervisor {
            strands: RefCell::new(FuturesUnordered::new()),
            policy,
        })
    }

    /// `true` while no detached strand is in flight (the executor's "supervisor is
    /// progress / a non-empty supervisor is busy" predicate — §2.12).
    pub(crate) fn is_empty(&self) -> bool {
        self.strands.borrow().is_empty()
    }

    /// Spawn a detached strand: wrap `sub_tree` in the [`supervised`] catch+policy
    /// wrapper (owning the launched sub-tree, the cloned [`ReactorEnv`], and the
    /// global-budget `permit` for its whole lifetime — RAII release on
    /// completion/drop), and push it into the set (§2.11 step 3 / §2.12).
    pub(crate) fn spawn(
        &self,
        sub_tree: i64,
        env: ReactorEnv<'h>,
        strand: StrandId,
        permit: Permit,
    ) {
        let policy = self.policy;
        let fut = supervised(sub_tree, env, strand, permit, policy);
        self.strands.borrow_mut().push(Box::pin(fut));
    }

    /// Drive every member strand once, removing each as it completes (a completed
    /// strand has already run its policy + released its permit + freed its sub-tree
    /// inside its own body). Called by the executor each loop iteration (§2.12).
    ///
    /// The `RefCell` borrow is held only for the synchronous `poll_next` calls.
    /// (A *nested* launch — a launched strand that itself launches — would re-enter
    /// `spawn`'s `borrow_mut` here and panic; not reachable by the Chunk-B
    /// acceptance shapes, which launch only from the top accept loop. Active
    /// support for nested launch is a Chunk-C concern.)
    pub(crate) fn drive(&self, cx: &mut Context<'_>) {
        loop {
            let mut strands = self.strands.borrow_mut();
            match strands.poll_next_unpin(cx) {
                TaskPoll::Ready(Some(())) => {
                    drop(strands); // release before the next iteration
                }
                TaskPoll::Ready(None) | TaskPoll::Pending => return,
            }
        }
    }

    /// Drop all in-flight strands (drive-end / shutdown). Each dropped strand's
    /// owned `EffectPoll`(s) release their per-token permits (§2.9) and its global
    /// `Permit` releases — RAII, no leak. Breaks the `Rc` cycle the supervised
    /// futures form (they own a cloned `ReactorEnv` holding an `Rc<Supervisor>`).
    pub(crate) fn clear(&self) {
        self.strands.borrow_mut().clear();
    }
}

/// The supervised-strand wrapper (§2.12): run the launched sub-tree, catching
/// EVERY termination — `catch_unwind` (a Rust panic → the server lives) + the
/// reused S95 `take_runtime_error` capture at the completion boundary — then apply
/// the §10 policy, free the detached sub-tree (`consume_io_tree` — the strand owns
/// it, §2.11), and release the global-budget `permit` (RAII drop at scope end →
/// frees a global slot → wakes a parked launch, §2.13).
async fn supervised(
    sub_tree: i64,
    env: ReactorEnv<'_>,
    strand: StrandId,
    global_permit: Permit,
    policy: SupervisorPolicy,
) {
    // catch_unwind around the strand body so a Rust-level panic (bad tag, RC
    // mid-panic, a handler `(panic …)`) is caught, NOT propagated into the
    // executor. The `take_runtime_error` capture is SYNCHRONOUS with the resolve
    // (no `.await` between), so no other strand interposes on the shared slot.
    let body = std::panic::AssertUnwindSafe(async {
        let r = crate::io::run_io_trampoline_inner_async(sub_tree, &env, strand).await;
        let err = crate::panic::take_runtime_error();
        (r, err)
    });
    let outcome = body.catch_unwind().await;

    match outcome {
        Ok((_r, None)) => emit_strand_event(StrandEvent::StrandCompleted { strand }),
        Ok((_r, Some(msg))) => apply_policy(policy, strand, msg), // runtime error
        Err(_panic) => apply_policy(policy, strand, "<panicked>".to_string()),
    }

    // The strand owns its detached sub-tree (§2.11) — free it exactly once.
    crate::drop::consume_io_tree(sub_tree);
    // `global_permit` drops HERE (scope end) → frees a global-budget slot →
    // FIFO-wakes a parked launch (§2.13). Explicit to document the release point.
    drop(global_permit);
}

// ===========================================================================
// The executor — block_on over the reactor.
// ===========================================================================

/// The executor's task `Waker`, backed by the reactor's cross-thread
/// [`mio::Waker`]. Waking it unblocks a `mio::poll` in [`Reactor::turn`] — so a
/// `futures` `oneshot` send from a `rayon` worker (the wakeable rayon→reactor
/// bridge) resumes the reactor, and a [`Permit`]-release wake of a parked
/// `AcquirePermit` is observed on the next poll. (Both `Future::poll` calls and
/// `turn()` run on the reactor thread; this waker is the ONE thing the rayon
/// pool touches, and `mio::Waker::wake` is explicitly cross-thread-safe.)
///
/// **Load-bearing invariant — DO NOT BREAK (S4).** Both *no-lost-wake* and
/// *no-spin* on the bridge eventfd path depend on TWO things holding together:
///
/// 1. `mio` registers its `Waker`'s eventfd **edge-triggered** (`EPOLLET`) — its
///    documented Linux implementation; and
/// 2. the reactor **never drains** the bridge eventfd — a `Token(0)`
///    ([`BRIDGE_WAKE_TOKEN`]) event in [`Reactor::turn`] finds no `fd_waiters`
///    entry and is deliberately ignored (it served only to unblock `mio::poll`);
///    `mio::Waker` itself resets the eventfd counter on the next `wake()`.
///
/// A future switch to **level-triggered** registration, OR adding an explicit
/// drain/read of the bridge eventfd, breaks this: level-triggered + undrained
/// would **spin** (every `mio::poll` returns the still-signalled token), and
/// adding a drain under edge-triggered risks a **lost edge** (a `wake()` racing
/// the drain is swallowed, parking the reactor forever). The next maintainer must
/// not introduce either.
struct ExecutorWaker {
    mio: Arc<mio::Waker>,
    /// A pending-wake flag the executor loop reads to distinguish a *genuinely
    /// stuck* top future (Pending with nothing that could ever wake it — the
    /// `would hang` panic guard) from one that was **just woken but not yet
    /// re-polled** (§2.13). The decisive case: the launcher parks on
    /// `acquire_global` (degree exhausted); the in-flight detached strands then
    /// complete during `supervisor.drive()`, each dropping its global-budget
    /// `Permit` and waking the parked acquire — but that wake fires AFTER this
    /// iteration's top-future poll, so at the guard the supervisor is empty and no
    /// fd/timer waiter remains. Without this flag the guard would misfire as a
    /// hang; with it the guard sees the pending wake and re-polls (the `mio::wake`
    /// already made the next `turn()` non-blocking, so the launcher resumes at
    /// once). Set on every wake; cleared by the loop right before each top poll
    /// (the poll services the wake).
    woken: Arc<std::sync::atomic::AtomicBool>,
}

impl Wake for ExecutorWaker {
    fn wake(self: Arc<Self>) {
        self.woken.store(true, std::sync::atomic::Ordering::SeqCst);
        let _ = self.mio.wake();
    }
    fn wake_by_ref(self: &Arc<Self>) {
        self.woken.store(true, std::sync::atomic::Ordering::SeqCst);
        let _ = self.mio.wake();
    }
}

/// The host-side context threaded through the async trampoline: the reactor's
/// [`HostCtx`] (for poll-fns), the token-capacity [`TokenPool`] (for the
/// per-branch permit acquire), and the in-flight blocking-bridge counter (so the
/// executor knows a `rayon`-offloaded branch is outstanding even when no fd/timer
/// waiter is registered). Constructed single-sited in [`block_on_reactor`].
///
/// **Clone (§2.11/§2.12).** A supervised detached strand OWNS its own
/// `ReactorEnv` clone (rather than borrowing the launching frame's), so the
/// supervisor's futures do not self-borrow the env that reaches the supervisor.
/// The clone is cheap — the `host`/`pool`/`pending_bridges` fields are copied
/// borrows and `supervisor` is one `Rc` clone. (The `Rc<Supervisor>` makes the
/// supervised future + supervisor an `Rc` cycle while a strand is in flight;
/// completed strands self-remove and drive-end [`Supervisor::clear`] breaks it.)
#[derive(Clone)]
pub(crate) struct ReactorEnv<'h> {
    /// The reactor host vtable the platform poll-fns register against.
    pub host: &'h HostCtx,
    /// The shared token-capacity pool (§2.8).
    pub pool: &'h Rc<TokenPool>,
    /// Count of `rayon`-offloaded blocking branches currently in flight. The
    /// async `Par` arm bumps it before `rayon::spawn` and drops it on completion
    /// (see `io::run_par_node_async`); [`block_on_reactor`] treats a positive
    /// count as "keep turning" so a blocking-only `Par` is not mistaken for a
    /// hung future with no waiters.
    pub pending_bridges: &'h Rc<Cell<usize>>,
    /// The supervisor that owns each detached strand (§2.12). An `Rc` (not a
    /// borrow) so a supervised future can own a cloned `ReactorEnv` to reach it
    /// for a nested launch without the env self-borrowing the supervisor.
    pub supervisor: Rc<Supervisor<'h>>,
}

impl ReactorEnv<'_> {
    /// Acquire a permit on `(token, capacity)` charged to `strand` (the §2.8
    /// gate). `token == 0` ⇒ no acquire.
    pub(crate) fn acquire(&self, token: u64, capacity: u32, strand: StrandId) -> AcquirePermit {
        self.pool.acquire(token, capacity, strand)
    }

    /// Acquire the global admission budget (the `IO_TAG_LAUNCH` arm's gate, §2.13)
    /// charged to `strand`. Resolves once a global slot is free; parks (the accept
    /// loop) on a full budget. The resulting `Permit` is moved into the supervised
    /// strand (owned for its lifetime, RAII-released on completion/drop).
    pub(crate) fn acquire_global(&self, strand: StrandId) -> AcquirePermit {
        self.pool.acquire_global(strand)
    }
}

/// Default upper bound on a single `mio::poll` block — a liveness backstop so a
/// misbehaving leaf can never wedge the reactor (acceptance: no deadlock/hang).
const MAX_TURN_BLOCK: Duration = Duration::from_secs(5);

/// Default `OneShot` wall-clock **backstop** for one `block_on_reactor` — a
/// liveness guard catching an **armed-but-never-readies** poll leaf (a leaf armed
/// on an fd/timer that never fires — a hung peer, a wrong fd) under a one-shot
/// `--run`/REPL drive. FIXME 0479 (`reactor.md §8`): the primary liveness rule is
/// now the **structural armed-ness deadlock detector** ([`reactor_is_armed`]) which
/// trips the instant a `Pending` top future has NOTHING armed — it fires
/// immediately, not after this wall-clock delay. This backstop is the SECONDARY
/// guard the detector cannot cover (an armed leaf that never readies), retained
/// only in [`DriveMode::OneShot`]; a [`DriveMode::Server`] drive disables it so a
/// legitimately-idle armed `accept` loop runs indefinitely.
///
/// **This is NOT a cap on total drive time.** It measures only time during which
/// NO blocking branch is in flight (`pending_bridges == 0`) and the supervisor is
/// empty. A legitimately slow blocking I/O branch on rayon (the wakeable bridge)
/// holds the no-progress deadline off for as long as the branch runs, so blocking
/// I/O is **uncapped by design** — matching the feature-off sync stepper.
const MAX_TOTAL_BLOCK: Duration = Duration::from_secs(30);

/// How `block_on_reactor` treats the wall-clock backstop (FIXME 0479 / `reactor.md
/// §8.2` mode knob). The structural armed-ness deadlock detector
/// ([`reactor_is_armed`]) is ALWAYS active in both modes; the mode governs ONLY the
/// secondary wall-clock backstop for an armed-but-never-readies hang.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DriveMode {
    /// `--run` / `--link` exe entry / REPL per-form eval: the armed-ness detector
    /// PLUS the wall-clock backstop (a batch program that arms an fd and hangs is a
    /// real hang worth a guard).
    OneShot,
    /// A long-running accept-loop drive: the armed-ness detector ONLY, no wall-clock
    /// cap — an idle-but-armed server runs forever (production-shaped).
    Server,
}

/// The structural armed-ness predicate (`reactor.md §8.2`): the reactor is *armed*
/// (legitimately waiting, can be woken) when any of the five readiness sources is
/// live. A `Pending` top future with NONE of these armed is a true deadlock — no
/// event can ever wake it — and trips the detector immediately (no wall-clock wait).
/// This generalizes the piecemeal `pending_bridges`/supervisor exemptions into one
/// predicate (Principle 7 — one liveness rule).
fn reactor_is_armed(
    reactor: &Reactor,
    pending_bridges: &Rc<Cell<usize>>,
    supervisor: &Supervisor<'_>,
    pool: &TokenPool,
) -> bool {
    reactor.has_waiters()
        || pending_bridges.get() > 0
        || !supervisor.is_empty()
        || pool.any_waiter_parked()
}

/// Read the `OneShot`/`Server` drive-mode knob from the `CRANELISP_DRIVE_MODE`
/// reactor-construction surface (FIXME 0479 / `reactor.md §8.3`). `server` ⇒
/// [`DriveMode::Server`]; anything else (incl. unset / `oneshot`) ⇒
/// [`DriveMode::OneShot`] (the default — no batch program loses its hang guard).
fn read_drive_mode_env() -> DriveMode {
    match std::env::var("CRANELISP_DRIVE_MODE").ok().as_deref() {
        Some(s) if s.trim().eq_ignore_ascii_case("server") => DriveMode::Server,
        _ => DriveMode::OneShot,
    }
}

/// Read the scaled `OneShot` wall-clock backstop from `CRANELISP_REACTOR_BACKSTOP_MS`
/// (FIXME 0479 / `reactor.md §8.3`). Unset / unparsable / zero ⇒ [`MAX_TOTAL_BLOCK`]
/// (30s default). The /qa suite sets a low value so the OneShot-backstop witness
/// fits the suite-time budget instead of waiting the real 30s.
fn read_backstop_env() -> Duration {
    std::env::var("CRANELISP_REACTOR_BACKSTOP_MS")
        .ok()
        .and_then(|s| s.trim().parse::<u64>().ok())
        .filter(|&ms| ms > 0)
        .map(Duration::from_millis)
        .unwrap_or(MAX_TOTAL_BLOCK)
}

/// Drive `make_future` to completion on a fresh reactor, turning the mio loop
/// between polls. Single-threaded: the future (and every leaf poll-fn it awaits)
/// runs on THIS thread; the reactor blocks on THIS thread. No work is ever moved
/// to another thread — the "no thread-per-read" invariant.
///
/// `make_future` receives the borrowed [`HostCtx`] so the leaves it builds
/// register against this reactor. The closure indirection is what lets the
/// future borrow the `HostCtx` (which borrows the reactor) without a
/// self-referential struct.
pub(crate) fn block_on_reactor<F, T>(make_future: F) -> std::io::Result<T>
where
    F: AsyncFnOnce(&ReactorEnv<'_>) -> T,
{
    // FIXME 0479 (`reactor.md §8.3`): the drive mode + the scaled backstop are read
    // from the reactor-construction env surface (the same channel as
    // `CRANELISP_DEGREE`). `Server` disables the wall-clock backstop so an idle-but-
    // armed `accept` loop runs indefinitely; `OneShot` (default) keeps it as a hang
    // guard for `--run`/REPL.
    block_on_reactor_capped(make_future, read_drive_mode_env(), read_backstop_env())
}

/// [`block_on_reactor`] with an injectable drive-mode + wall-clock backstop — the
/// seam the liveness unit tests drive with a lowered cap. The structural armed-ness
/// deadlock detector ([`reactor_is_armed`]) is ALWAYS active; `drive_mode` governs
/// only the secondary wall-clock backstop (a **no-progress** guard held off while a
/// blocking branch is in flight, so a slow blocking I/O branch is uncapped —
/// matching feature-off — and firing only for an armed-but-never-readies leaf under
/// [`DriveMode::OneShot`]).
fn block_on_reactor_capped<F, T>(
    make_future: F,
    drive_mode: DriveMode,
    max_total_block: Duration,
) -> std::io::Result<T>
where
    F: AsyncFnOnce(&ReactorEnv<'_>) -> T,
{
    let mut reactor = Reactor::new()?;
    // The mio-backed task waker: a `oneshot` send from a rayon worker (the
    // wakeable bridge) or a `Permit`-release wake of a parked acquire wakes this,
    // which unblocks `turn()`'s `mio::poll`. (Replaces the former noop waker; the
    // turn-loop still re-polls after every turn, so the fd/timer path is
    // unchanged — this only ADDS the ability for cross-thread/park wakeups to
    // shorten a blocking `mio::poll`.)
    // The pending-wake flag the executor loop reads to suppress the false-hang
    // panic when a parked top future (e.g. the launcher on `acquire_global`) was
    // just woken by a Permit release but not yet re-polled (§2.13). Shared between
    // the waker (sets it) and the loop (clears it before each top poll).
    let woken = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let task_waker: Waker = Arc::new(ExecutorWaker {
        mio: reactor.bridge_waker(),
        woken: Arc::clone(&woken),
    })
    .into();

    // The program degree throttle (§2.13). Provisional reactor-construction
    // surface: the `CRANELISP_DEGREE` env var (the carrier the Chunk-B acceptance
    // rows read; `design/int/reactor.md §2.13` — int `src/` supplies it as a
    // reactor-construction config when the policy surface lands). Unset / invalid
    // / zero ⇒ `u32::MAX` (no throttle), preserving the pre-slice-4 behaviour.
    let degree = read_degree_env();

    // The token-capacity pool + the in-flight blocking-bridge counter, single-
    // sited here alongside the reactor (§2.8 / §6.2). Single-threaded: every
    // mutation runs on THIS reactor thread. (The supervisor is declared AFTER
    // `host_ctx` below so it — and the detached strands it owns, which borrow
    // `host_ctx` through their cloned `ReactorEnv` — drops BEFORE `host_ctx`.)
    let pool = TokenPool::with_degree(degree);
    // v9 ctx-vtable (§7.2): wire the pool into the reactor so the `host_acquire`/
    // `host_retire` callbacks take/return token permits against it. The poll-leaf
    // path acquires through the reactor's `ctx` vtable (the platform poll-fn calls
    // `ctx.acquire`); the blocking-branch / global-budget paths acquire the SAME
    // pool directly through `ReactorEnv` (the `Future`-based `AcquirePermit`).
    reactor.set_pool(Rc::clone(&pool));
    let pending_bridges: Rc<Cell<usize>> = Rc::new(Cell::new(0));

    // Raw self pointer for the poll-fns. Discipline: after this we touch the
    // reactor ONLY through `reactor_ptr` (in `turn`) or through the `HostCtx`
    // host handle (in the poll-fns) — never as a live `&mut reactor` across a
    // `Future::poll`, so the two never alias.
    let reactor_ptr: *mut Reactor = &mut reactor;
    // B1: the `HostCtx` host handle is the RAW `reactor_ptr` — never a
    // `&reactor`. The poll-fns reborrow `&mut` through it (mutation), `turn`
    // reborrows `&mut` through `reactor_ptr` directly; same provenance,
    // non-overlapping lifetimes (see `make_host_ctx`).
    let host_ctx = make_host_ctx(reactor_ptr);

    // The supervisor (§2.12) — declared AFTER `host_ctx` so it (and the detached
    // strands it owns, which borrow `host_ctx`/`pool`/`pending_bridges` through
    // their cloned `ReactorEnv`) drops before those borrowed locals.
    let supervisor = Supervisor::new(SupervisorPolicy::default());

    let env = ReactorEnv {
        host: &host_ctx,
        pool: &pool,
        pending_bridges: &pending_bridges,
        supervisor: Rc::clone(&supervisor),
    };
    let mut future = Box::pin(make_future(&env));
    let mut cx = Context::from_waker(&task_waker);

    // The no-progress deadline anchor. It is RESET to "now" on every iteration in
    // which a blocking branch is in flight (`pending_bridges > 0`), so the cap
    // never accumulates time against a legitimately-slow blocking I/O branch on
    // rayon — blocking I/O is uncapped by design (matching feature-off). The cap
    // therefore measures only contiguous no-bridge time and fires solely for a
    // genuinely-stuck poll leaf (I1; `reactor.md` §2.6).
    let mut no_progress_since = std::time::Instant::now();
    // The top future's value once it completes. Once `Some`, we STOP polling the
    // top future (polling a completed future panics) but keep DRAINING the
    // supervisor — a finite program's detached strands must run to completion
    // (drained before exit, §2.12; the §B4 launch-and-continue acceptance), not be
    // discarded the instant `main` returns.
    let mut top_result: Option<T> = None;
    loop {
        // Clear the pending-wake flag right before polling: the poll SERVICES any
        // wake delivered up to this point, so a wake that arrives during this poll
        // or the supervisor drive below re-sets it and the guard re-polls (§2.13).
        woken.store(false, std::sync::atomic::Ordering::SeqCst);

        // Poll the top future (until it completes). The leaf poll-fns mutate the
        // reactor through the `HostCtx` host handle during this call; no
        // `&mut reactor` is held here.
        if top_result.is_none()
            && let TaskPoll::Ready(v) = future.as_mut().poll(&mut cx)
        {
            top_result = Some(v);
        }

        // Drain the supervisor (§2.12): drive every detached strand concurrently
        // with the top future, removing each as it completes (a completed strand
        // has already run its policy + released its permit + freed its sub-tree).
        supervisor.drive(&mut cx);

        // Return only when the top future is done AND every detached strand has
        // drained — so launched effects genuinely run before exit (§2.12 / §B4).
        if supervisor.is_empty()
            && let Some(v) = top_result
        {
            return Ok(v);
        }

        // A blocking branch in flight OR a non-empty supervisor is legitimate
        // progress — hold the no-progress deadline off (a slow blocking I/O branch on
        // rayon is uncapped, matching feature-off, §2.6; a server with live handler
        // strands is busy, not stuck, §2.12). The backstop resumes measuring once both
        // are quiescent.
        //
        // FIXME 0479 (`reactor.md §8.2`): the wall-clock cap is the SECONDARY guard
        // (an armed-but-never-readies leaf), retained ONLY in `OneShot` mode. A
        // `Server`-mode drive disables it, so a legitimately-idle armed `accept` loop
        // (listener fd in `fd_waiters`) runs indefinitely — the production shape. The
        // PRIMARY liveness rule is the armed-ness detector below.
        if pending_bridges.get() > 0 || !supervisor.is_empty() {
            no_progress_since = std::time::Instant::now();
        } else if drive_mode == DriveMode::OneShot
            && no_progress_since.elapsed() > max_total_block
        {
            // OneShot backstop: no bridge, empty supervisor, no progress for the
            // backstop window — an armed-but-never-readies (or genuinely-stuck) leaf
            // under a one-shot drive. Drop in-flight strands (none here) and bail.
            supervisor.clear();
            panic!("block_on_reactor: OneShot backstop exceeded {max_total_block:?} — leaf never completed");
        }

        // Turn the reactor BETWEEN polls (the only place a `&mut reactor` is
        // live). SAFETY: the future is not being polled here, so the host-handle
        // raw alias is dormant; no two `&mut` coexist.
        let r = unsafe { &mut *reactor_ptr };
        // The PRIMARY liveness rule (FIXME 0479 / `reactor.md §8.2`): the structural
        // armed-ness deadlock detector. A `Pending` top future with NOTHING armed
        // (no fd/timer waiter, no rayon bridge, no detached strand, no parked permit
        // waiter) can NEVER be woken — a true deadlock, detectable the instant it
        // occurs (no wall-clock wait). This fires in BOTH modes (it is not a
        // wall-clock cap): an idle server is *armed* (its listener fd is a waiter),
        // so it never trips here; only a genuinely-stuck reactor does. The `!woken`
        // guard excludes a parked launcher just satisfied by a Permit release (§2.13
        // — it must re-poll, not panic).
        if top_result.is_none()
            && !woken.load(std::sync::atomic::Ordering::SeqCst)
            && !reactor_is_armed(r, &pending_bridges, &supervisor, &pool)
        {
            supervisor.clear();
            panic!(
                "reactor suspended with no armed interest — a poll leaf is stuck / a deadlock \
                 (block_on_reactor: future Pending with nothing registered to wake it)"
            );
        }
        // Cap the per-turn mio block so the OneShot backstop check can fire at its
        // deadline, not `MAX_TURN_BLOCK` later (FIXME 0479): without this a 2s
        // backstop with a 5s turn block would only be checked every 5s. In `Server`
        // mode there is no wall-clock backstop, so the full `MAX_TURN_BLOCK` re-check
        // cadence applies. The reactor's own timer wheel further clamps this to the
        // soonest armed timer, so a poll leaf's deadline is never overshot.
        let turn_block = if drive_mode == DriveMode::OneShot {
            max_total_block
                .saturating_sub(no_progress_since.elapsed())
                .min(MAX_TURN_BLOCK)
        } else {
            MAX_TURN_BLOCK
        };
        r.turn(turn_block);
    }
}

/// Read the program degree throttle (§2.13) from the provisional `CRANELISP_DEGREE`
/// reactor-construction surface. Unset / unparsable / zero ⇒ `u32::MAX` (no
/// throttle). See [`block_on_reactor_capped`] for why this lives here for now.
fn read_degree_env() -> u32 {
    std::env::var("CRANELISP_DEGREE")
        .ok()
        .and_then(|s| s.trim().parse::<u32>().ok())
        .filter(|&d| d > 0)
        .unwrap_or(u32::MAX)
}

// ===========================================================================
// Fixture demo leaves — `async-read` (fd + register_readable) + a timer feeder.
//
// Hand-written poll-shape effects (App. B "Demo leaf"). NO `declare_platform!` /
// backend change — the macro poll-emission is a later slice.
// ===========================================================================

/// State for the `async-read` demo leaf: a non-blocking raw fd + the recv result.
///
/// **`result` is the FIRST field (offset 0)** so it sits at the generic
/// [`RESULT_SLOT_OFFSET`] `EffectPoll` reads on `Ready` (S94 R1 seam decision 3,
/// FIXME 0457) — the same env-result-slot convention the real backend-built
/// state-closure obeys. The S93 per-effect `ResultReader` is gone; this fixture
/// proves the reactor + `EffectPoll` substrate against the generic offset read.
///
/// Test-only fixture (`#[cfg(test)]`) — exercised solely by the in-crate reactor
/// unit tests; it is not part of the crate's public surface (the real poll-shape
/// leaves live in the `platforms/` DLLs, not here).
#[cfg(test)]
#[repr(C)]
pub(crate) struct AsyncReadState {
    /// Bytes received (the leaf's `i64` result), or `-1` on a hard error. FIRST
    /// field ⇒ at the generic result-slot offset `EffectPoll` reads.
    pub(crate) result: i64,
    /// The non-blocking fd to read from.
    pub(crate) fd: i32,
    /// Observability flag: `true` once interest has been registered at least
    /// once. **Not** a re-registration gate — the poll-fn re-registers on EVERY
    /// `Pending` (the v7 poll-fn contract); the reactor's one-shot deregister
    /// means a fire can leave the read unsatisfied (short read / spurious
    /// readiness), and the next `Pending` MUST re-arm interest or the wakeup is
    /// lost (I2). `register_fd` is idempotent (EEXIST), so re-registering while
    /// still parked is a safe no-op.
    pub(crate) registered: bool,
}

/// The `async-read` poll-fn (hand-written fixture). `recv` the fd non-blocking;
/// on bytes → write the count + `Ready`; on `EWOULDBLOCK` → `register_readable`
/// + `Pending`. The exact poll-shape App. B specifies.
///
/// **Re-registration obligation (I2).** The reactor's fd waiters are one-shot:
/// on readiness it fires the waker AND deregisters. A re-poll after a fire that
/// does NOT satisfy the read (a short read, or a spurious readiness that
/// re-`EWOULDBLOCK`s) therefore finds NO live registration — so it MUST re-arm
/// interest, or that wakeup is lost forever (stuck strand / the
/// `block_on_reactor` "Pending with no waiters" panic). Hence we call
/// `register_readable` on EVERY `Pending`, not just the first. `register_fd` is
/// idempotent (the EEXIST arm), so re-registering while still parked is a no-op.
///
/// # Safety
/// C-ABI poll-fn: `state` is a live `AsyncReadState`; `host` / `waker` are live.
#[cfg(test)]
pub(crate) unsafe extern "C" fn async_read_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const CWaker,
) -> CPoll {
    let st = unsafe { &mut *(state as *mut AsyncReadState) };
    let mut buf = [0u8; 64];
    // SAFETY: `st.fd` is a valid non-blocking fd; `buf` is a valid out-buffer.
    let n = unsafe {
        libc::recv(
            st.fd,
            buf.as_mut_ptr() as *mut c_void,
            buf.len(),
            0,
        )
    };
    if n >= 0 {
        st.result = n as i64; // n == 0 ⇒ EOF, still a completed read.
        return CPoll::Ready;
    }
    // n < 0: would-block ⇒ park; any other errno ⇒ hard error result.
    let err = unsafe { *libc::__errno_location() };
    if err == libc::EWOULDBLOCK || err == libc::EAGAIN {
        // Re-register interest on EVERY Pending (the v7 contract — see the
        // re-registration obligation above). `register_fd` is idempotent, so a
        // re-poll while still registered is a safe no-op; a re-poll after a
        // one-shot fire re-arms — no lost wakeup.
        st.registered = true; // observability only; NOT a gate.
        let hc = unsafe { &*host };
        unsafe { (hc.register_readable)(hc.host, st.fd, waker) };
        CPoll::Pending
    } else {
        st.result = -1;
        CPoll::Ready
    }
}

/// State for the timer-driven feeder: after `deadline_nanos`, write one byte to
/// `peer_fd` (waking the corresponding `async-read`). Drives the feed off the
/// host reactor's timer wheel, so the whole demo stays single-reactor with NO
/// per-read OS thread.
///
/// Test-only fixture (`#[cfg(test)]`) — see [`AsyncReadState`]; exercised solely
/// by the in-crate reactor unit tests, not part of the public surface.
#[cfg(test)]
#[repr(C)]
pub(crate) struct TimerWriteState {
    /// Unit result (`0`) at the generic [`RESULT_SLOT_OFFSET`] — the feeder
    /// produces no meaningful value, but `EffectPoll` reads `state + 0` on `Ready`
    /// (the generic env-offset read), so the slot is reserved first and left `0`.
    pub(crate) result: i64,
    /// The fd to send a wake-byte to once the timer fires.
    pub(crate) peer_fd: i32,
    /// Monotonic-nanos deadline at which to perform the write.
    pub(crate) deadline_nanos: u64,
    /// Re-registration gate. Unlike the fd path (I2), this latch is SOUND for the
    /// timer leaf and is deliberately kept: a timer leaf transitions to `Ready`
    /// the moment `now >= deadline` (its fire), so it NEVER returns `Pending`
    /// after its registration fires — there is no lost-wakeup case to re-arm
    /// against. The latch instead serves correctness the other way: it stops a
    /// sibling-driven re-poll (this leaf re-polled before its deadline because
    /// another leaf woke) from pushing a DUPLICATE timer-heap entry on every such
    /// poll. `register_timer` has no natural dedup key, so the per-leaf latch is
    /// the idempotency guard here.
    pub(crate) registered: bool,
}

/// The timer-feeder poll-fn. Before the deadline → `register_timer` + `Pending`;
/// once the reactor re-polls us at/after the deadline → `send` one byte + `Ready`.
///
/// Unlike `async_read_pollfn`, this keeps the `registered` latch (it goes `Ready`
/// on its fire and never re-`Pending`s, so there is no lost-wakeup to re-arm; the
/// latch prevents duplicate timer-heap entries on sibling re-polls — see
/// [`TimerWriteState::registered`]).
///
/// # Safety
/// C-ABI poll-fn: `state` is a live `TimerWriteState`; `host` / `waker` are live.
#[cfg(test)]
pub(crate) unsafe extern "C" fn timer_write_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const CWaker,
) -> CPoll {
    let st = unsafe { &mut *(state as *mut TimerWriteState) };
    let now = monotonic_nanos();
    if now >= st.deadline_nanos {
        let byte = [1u8];
        // SAFETY: `peer_fd` is a valid socket fd; sending 1 byte.
        unsafe { libc::send(st.peer_fd, byte.as_ptr() as *const c_void, 1, 0) };
        return CPoll::Ready;
    }
    if !st.registered {
        st.registered = true;
        let hc = unsafe { &*host };
        unsafe { (hc.register_timer)(hc.host, st.deadline_nanos, waker) };
    }
    CPoll::Pending
}

// ===========================================================================
// `sleep` — the runtime-provided timer poll leaf (slice 7, §2.18).
//
// `sleep : Duration -> IO Unit` arms the reactor timer and resumes when it fires.
// It is a **tokenless** poll leaf (`token = 0, capacity = 1` ⇒ unrestricted overlap
// — many `sleep`s race concurrently) reusing the ENTIRE `EffectPoll` / acquire-
// around-poll / timer-`turn()` machinery. Unlike the platform poll-shape effects it
// is an **intrinsics** poll-fn, NOT a `declare_platform!` DLL export — the control
// vocabulary is runtime-hosted, platforms never see it (§9). It is the one new leaf
// `timeout = race (map Some io) (map (const None) (sleep d))` needs (§2.18); the
// race-loser drop (C3) cancels whichever arm loses.
//
// This also gives the marquee overlap wall-clock witness a real parking delay (the
// flaky sub-ms timing ratio in `web_server_fans_out_concurrent_requests_overlap`).
// ===========================================================================

/// State for the `sleep` timer leaf (§2.18). `result` is the FIRST field (the
/// generic [`RESULT_SLOT_OFFSET`] `EffectPoll` reads on `Ready`) and holds `Unit`
/// (`0`) once the timer fires. `deadline_nanos == 0` is the "not yet armed"
/// sentinel; the first poll computes + stores the absolute deadline.
#[repr(C)]
pub(crate) struct SleepState {
    /// Unit result (`0`) at the generic result-slot offset.
    pub(crate) result: i64,
    /// The sleep duration in nanoseconds (the env-baked argument).
    pub(crate) duration_nanos: i64,
    /// Absolute monotonic deadline, `0` until armed (the first-poll sentinel).
    pub(crate) deadline_nanos: u64,
}

/// The `sleep` poll-fn (§2.18). First poll → compute `deadline = now + duration`,
/// `register_timer`, return `Pending`. Re-poll → `now >= deadline` ⇒ write `Unit`
/// and `Ready`, else `Pending`. The `deadline_nanos != 0` latch means it never
/// re-arms a duplicate timer on a sibling-driven re-poll before its deadline (the
/// same idempotency the `timer_write_pollfn` fixture's `registered` latch provides —
/// a timer leaf goes `Ready` on its fire and never re-`Pending`s after, so there is
/// no lost-wakeup to re-arm against, §2.7).
///
/// Published as the runtime symbol `runtime/sleep_pollfn` ([`crate::catalog`]):
/// the backend's C4 `sleep` lowering (`compile_sleep`) resolves it as a
/// `Linkage::Import` and `func_addr`-bakes it as the `IO_TAG_EFFECT_POLL`
/// state-closure `code_ptr` — the non-GOT runtime-symbol path (a well-known
/// runtime symbol the node's `code_ptr` resolves to, §2.18; distinct from a
/// `declare_platform!` effect's GOT slot). The leaf + its reactor timer
/// registration landed in C2 (with the unit test); the backend lowering is C4.
///
/// # Safety
/// C-ABI poll-fn: `state` is a live [`SleepState`]; `host` / `waker` are live.
///
/// JIT name: "runtime/sleep_pollfn" — exported via `export_name` so `--link`
/// mode resolves it (the system linker needs a real symbol of this exact
/// slash-name, not just the catalog pointer the JIT in-memory linker uses).
/// Mirrors `runtime/vec_new` / `runtime/alloc`.
#[unsafe(export_name = "runtime/sleep_pollfn")]
pub(crate) unsafe extern "C" fn sleep_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const CWaker,
) -> CPoll {
    let st = unsafe { &mut *(state as *mut SleepState) };
    if st.deadline_nanos == 0 {
        // First poll: arm the reactor timer at now + duration.
        st.deadline_nanos = monotonic_nanos() + st.duration_nanos.max(0) as u64;
        let hc = unsafe { &*host };
        unsafe { (hc.register_timer)(hc.host, st.deadline_nanos, waker) };
        return CPoll::Pending;
    }
    if monotonic_nanos() >= st.deadline_nanos {
        st.result = 0; // Unit
        CPoll::Ready
    } else {
        // A sibling-driven re-poll before our deadline: keep waiting WITHOUT
        // re-arming (the timer is already in the heap — no duplicate entry).
        CPoll::Pending
    }
}

// ===========================================================================
// Par-async overlap (App. B step 2d) — concurrent I/O leaves on the ONE reactor.
// ===========================================================================

/// Join a batch of effect leaves concurrently on the single reactor — the
/// `Par`-async overlap path. Two slow `async-read`s handed here complete in
/// ≈max(delay) not sum, because both register with the same reactor and progress
/// as their fds/timers fire — with NO thread-per-read (every leaf polls on the
/// `block_on_reactor` thread). This is the leaf-granularity realization of the
/// trampoline's `Par` arm lowering to `futures::future::join_all` (vs. the rayon
/// dispatcher, which stays the CPU-spark / feature-off path). Results are
/// returned in branch order.
///
/// `#[cfg(test)]`: a substrate-regression test helper. Production `Par` overlap
/// runs through `io::run_par_node_async` → `run_poll_partition` (which calls
/// `join_all` directly); this convenience wrapper has no non-test consumer.
#[cfg(test)]
pub(crate) async fn join_io_leaves(leaves: Vec<EffectPoll<'_>>) -> Vec<i64> {
    futures::future::join_all(leaves).await
}

#[cfg(test)]
mod tests;
