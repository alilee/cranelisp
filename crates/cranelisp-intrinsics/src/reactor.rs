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
//! - the fixture **`async-read`** poll-fn ([`async_read_pollfn`]) + a timer-driven
//!   feeder ([`timer_write_pollfn`]) — the hand-written demo leaves (App. B "Demo
//!   leaf"). No `declare_platform!` / backend change is needed to demo the
//!   mechanism; the macro poll-emission is a later slice.
//!
//! Gated `concurrency-runtime`: byte-identical-when-off (the deps `mio`/`futures`
//! are `dep:`-gated, so with the feature off cargo links neither).

use core::ffi::c_void;
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::future::Future;
use std::os::fd::RawFd;
use std::pin::Pin;
use std::task::{Context, Poll as TaskPoll};
use std::time::Duration;

use mio::unix::SourceFd;
use mio::{Events, Interest, Token};

use cranelisp_platform::{HostCtx, Poll as CPoll, PollFn, Waker as CWaker, WakerVTable};

use crate::strand::{emit_strand_event, StrandEvent, StrandId};

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
    /// Live fd registrations: `token → (fd, waker-to-fire-on-ready)`.
    fd_waiters: HashMap<usize, (RawFd, OwnedCWaker)>,
    /// Pending timers, soonest-deadline first.
    timer_heap: BinaryHeap<Reverse<TimerEntry>>,
    /// Live timer waiters: `id → waker-to-fire-on-expiry`.
    timer_waiters: HashMap<u64, OwnedCWaker>,
    next_timer_id: u64,
}

impl Reactor {
    /// Build a fresh reactor (one `mio::Poll`).
    pub fn new() -> std::io::Result<Self> {
        Ok(Reactor {
            poll: mio::Poll::new()?,
            events: Events::with_capacity(64),
            next_fd_token: 1,
            fd_waiters: HashMap::new(),
            timer_heap: BinaryHeap::new(),
            timer_waiters: HashMap::new(),
            next_timer_id: 1,
        })
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
                self.fd_waiters.insert(token, (fd, owned));
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
        self.timer_heap.push(Reverse(TimerEntry { deadline_nanos, id }));
        self.timer_waiters.insert(id, owned);
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
            if let Some((fd, waker)) = self.fd_waiters.remove(&token) {
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
            if let Some(waker) = self.timer_waiters.remove(&t.id) {
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
        host: reactor_ptr as *const c_void,
    }
}

// ===========================================================================
// EffectPoll — the one await boundary (App. B).
// ===========================================================================

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
/// All fields are `Copy`/pointer ⇒ `EffectPoll: Unpin`, so it polls through a
/// plain `&mut`. The lifetime ties the borrowed `HostCtx` to the future.
pub struct EffectPoll<'h> {
    state: *mut c_void,
    poll_fn: PollFn,
    host: &'h HostCtx,
    strand: StrandId,
    /// Number of times `poll` has run — distinguishes dispatch (0) from a resume
    /// (>0) for the strand events.
    polls: u32,
}

impl<'h> EffectPoll<'h> {
    /// Build an effect leaf over a poll-fn + its state, charged to `strand`.
    ///
    /// # Safety
    /// `state` must be valid for the poll-fn for the future's lifetime, and must
    /// point at an env whose first `i64` slot ([`RESULT_SLOT_OFFSET`]) is the
    /// reserved result slot the poll-fn writes before returning `Ready`;
    /// `poll_fn` must obey the v7 poll-fn contract.
    pub unsafe fn new(
        state: *mut c_void,
        poll_fn: PollFn,
        host: &'h HostCtx,
        strand: StrandId,
    ) -> Self {
        EffectPoll {
            state,
            poll_fn,
            host,
            strand,
            polls: 0,
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
        // SAFETY: `state`/`host`/`poll_fn` honour the v7 contract (constructor
        // safety obligation); `&cwaker` is a live C-ABI waker.
        let result = unsafe { (this.poll_fn)(this.state, this.host as *const HostCtx, &cwaker as *const CWaker) };
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
// The executor — block_on over the reactor.
// ===========================================================================

/// Default upper bound on a single `mio::poll` block — a liveness backstop so a
/// misbehaving leaf can never wedge the reactor (acceptance: no deadlock/hang).
const MAX_TURN_BLOCK: Duration = Duration::from_secs(5);

/// Default upper bound on total wall-clock for one `block_on_reactor` — bounds the
/// whole drive (acceptance #5: bounded test timeouts; a leaf that never completes
/// surfaces as a panic, not a hang).
const MAX_TOTAL_BLOCK: Duration = Duration::from_secs(30);

/// Drive `make_future` to completion on a fresh reactor, turning the mio loop
/// between polls. Single-threaded: the future (and every leaf poll-fn it awaits)
/// runs on THIS thread; the reactor blocks on THIS thread. No work is ever moved
/// to another thread — the "no thread-per-read" invariant.
///
/// `make_future` receives the borrowed [`HostCtx`] so the leaves it builds
/// register against this reactor. The closure indirection is what lets the
/// future borrow the `HostCtx` (which borrows the reactor) without a
/// self-referential struct.
pub fn block_on_reactor<F, T>(make_future: F) -> std::io::Result<T>
where
    F: AsyncFnOnce(&HostCtx) -> T,
{
    let mut reactor = Reactor::new()?;
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

    let mut future = Box::pin(make_future(&host_ctx));
    let waker = futures::task::noop_waker();
    let mut cx = Context::from_waker(&waker);

    let start = std::time::Instant::now();
    loop {
        // Poll the future. The leaf poll-fns mutate the reactor through the
        // `HostCtx` host handle during this call; no `&mut reactor` is held here.
        match future.as_mut().poll(&mut cx) {
            TaskPoll::Ready(v) => return Ok(v),
            TaskPoll::Pending => {}
        }

        if start.elapsed() > MAX_TOTAL_BLOCK {
            panic!("block_on_reactor: exceeded {MAX_TOTAL_BLOCK:?} — leaf never completed");
        }

        // Turn the reactor BETWEEN polls (the only place a `&mut reactor` is
        // live). SAFETY: the future is not being polled here, so the host-handle
        // raw alias is dormant; no two `&mut` coexist.
        let r = unsafe { &mut *reactor_ptr };
        if !r.has_waiters() {
            // Pending with nothing registered would spin forever. With our
            // re-poll-every-turn model this should not happen for a well-formed
            // leaf; treat it as a bug rather than a silent hang.
            panic!("block_on_reactor: future Pending with no reactor waiters (would hang)");
        }
        r.turn(MAX_TURN_BLOCK);
    }
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
#[repr(C)]
pub struct AsyncReadState {
    /// Bytes received (the leaf's `i64` result), or `-1` on a hard error. FIRST
    /// field ⇒ at the generic result-slot offset `EffectPoll` reads.
    pub result: i64,
    /// The non-blocking fd to read from.
    pub fd: i32,
    /// Observability flag: `true` once interest has been registered at least
    /// once. **Not** a re-registration gate — the poll-fn re-registers on EVERY
    /// `Pending` (the v7 poll-fn contract); the reactor's one-shot deregister
    /// means a fire can leave the read unsatisfied (short read / spurious
    /// readiness), and the next `Pending` MUST re-arm interest or the wakeup is
    /// lost (I2). `register_fd` is idempotent (EEXIST), so re-registering while
    /// still parked is a safe no-op.
    pub registered: bool,
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
pub unsafe extern "C" fn async_read_pollfn(
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
#[repr(C)]
pub struct TimerWriteState {
    /// Unit result (`0`) at the generic [`RESULT_SLOT_OFFSET`] — the feeder
    /// produces no meaningful value, but `EffectPoll` reads `state + 0` on `Ready`
    /// (the generic env-offset read), so the slot is reserved first and left `0`.
    pub result: i64,
    /// The fd to send a wake-byte to once the timer fires.
    pub peer_fd: i32,
    /// Monotonic-nanos deadline at which to perform the write.
    pub deadline_nanos: u64,
    /// Re-registration gate. Unlike the fd path (I2), this latch is SOUND for the
    /// timer leaf and is deliberately kept: a timer leaf transitions to `Ready`
    /// the moment `now >= deadline` (its fire), so it NEVER returns `Pending`
    /// after its registration fires — there is no lost-wakeup case to re-arm
    /// against. The latch instead serves correctness the other way: it stops a
    /// sibling-driven re-poll (this leaf re-polled before its deadline because
    /// another leaf woke) from pushing a DUPLICATE timer-heap entry on every such
    /// poll. `register_timer` has no natural dedup key, so the per-leaf latch is
    /// the idempotency guard here.
    pub registered: bool,
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
pub unsafe extern "C" fn timer_write_pollfn(
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
pub async fn join_io_leaves(leaves: Vec<EffectPoll<'_>>) -> Vec<i64> {
    futures::future::join_all(leaves).await
}

#[cfg(test)]
mod tests;
