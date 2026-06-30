//! `poll_support` — the `concurrency`-gated ergonomics suite for poll-shape
//! platform leaves (S96 Chunk A item 2, `design/platform/poll-support.md §2`).
//!
//! A poll-shape leaf is an `unsafe extern "C" fn(state, *HostCtx, *Waker) -> Poll`
//! (the [`crate::PollFn`] contract). Three things are repeated, error-prone, and
//! `unsafe` in every such leaf — the `async-demo` and `poll-pool` in-tree leaves
//! paid the cost by hand, and this module codifies the converged idiom:
//!
//! 1. **Reading args / writing the result out of `state`.** `state` IS the
//!    host-built state-closure env (`io-trampoline.md §12.2`): a result slot at
//!    `state + 0`, then the marshaled i64 leaf args at `state + 8 + 8*i`. Every
//!    leaf re-derives those offsets by hand. [`PollEnv`] is the single home for
//!    the R1 env-layout convention — if the backend bake ever moves a slot, this
//!    is the one edit, not every leaf.
//! 2. **Registering fd/timer readiness on would-block.** Every leaf calls
//!    `(*host).register_*(host, …, waker)` through the vtable with the `*Waker`
//!    plumbing repeated. [`Reactor`] turns each into a one-verb call.
//! 3. **Distinguishing first-poll setup from re-poll resume.** The host re-polls
//!    the same `PollFn` after each wake; the leaf must remember "have I armed
//!    yet?" across polls. [`PollState`] / [`PollStep`] / [`PollState::drive`]
//!    encode that phase branch once, over the env's result slot reused as the
//!    zero-initialised phase sentinel (the `async-demo`/`poll-pool` trick).
//!
//! What this module deliberately does NOT own (`poll-support.md §2.4`): the
//! descriptor (the platform's trust assertion), the syscall + result meaning (the
//! platform's domain), the reactor/pool/permit (all host/intrinsics-side), and
//! the codegen operand injection (the backend `inject_poll_leading_pair` pass).
//! It locates and registers; it does not interpret or schedule.

use core::ffi::c_void;

use crate::{HostCtx, Poll, Waker, HEAP_HEADER_SIZE, STRING_HEADER_BYTES};

/// Typed accessor over the host-built **state-closure env** — the single home for
/// the R1 env-layout convention (`io-trampoline.md §12.2`):
///
/// ```text
/// state (= env base) →
///   +0   result_slot : i64   (the poll-fn writes its i64 result here; the host
///                             `EffectPoll` reads it on Ready. Also reusable as a
///                             phase scratch sentinel while parked — see PollState.)
///   +8   arg_0 : i64         (marshaled leaf arg 0 — e.g. a re-passed fd, or `ms`)
///   +16  arg_1 : i64
///   ...                      (one slot per leaf arg)
/// ```
///
/// The leading `(token, capacity)` operands are peeled to the IO node's reserved
/// fields by the backend and are NOT in this env — `arg(0)` is the first LEAF arg
/// (`io-trampoline.md §14.2` / `poll-support.md §2.1`).
pub struct PollEnv {
    base: *mut i64,
}

impl PollEnv {
    /// # Safety
    /// `state` must be the host-built state-closure env base the poll-fn receives
    /// (`result_slot` at `+0`, marshaled leaf args from `+8`).
    pub unsafe fn new(state: *mut c_void) -> Self {
        PollEnv { base: state as *mut i64 }
    }

    /// Marshaled leaf arg `i` as a raw i64 (scalar value or heap base pointer).
    ///
    /// # Safety
    /// `i` must be within the leaf's declared arg count (the env reserves
    /// `result + leaf_count` slots). Reads `*(base + 1 + i)`.
    pub unsafe fn arg(&self, i: usize) -> i64 {
        // SAFETY: caller asserts `i` is within the marshaled leaf-arg region.
        unsafe { *self.base.add(1 + i) }
    }

    /// Read leaf arg `i` as a borrowed `&str`, interpreting the i64 as a
    /// `CLString` base pointer (`[alloc_size | rc | len | bytes…]`, payload at
    /// `base + HEAP_HEADER_SIZE`, `len` then UTF-8 bytes at
    /// `payload + STRING_HEADER_BYTES`). Returns `None` for a null pointer or
    /// non-UTF-8 bytes. The leaf only borrows — RC is owned by the env's
    /// `drop_glue_ptr`, so no inc/dec here.
    ///
    /// # Safety
    /// `i` must index a leaf arg that is a live `CLString` base pointer.
    pub unsafe fn arg_str(&self, i: usize) -> Option<&str> {
        // SAFETY: caller asserts arg `i` is a live CLString base pointer.
        let base = unsafe { self.arg(i) };
        if base == 0 {
            return None;
        }
        // SAFETY: `base` is a CLString base; payload + len + bytes per the
        // `CLString::as_str` heap-layout contract.
        unsafe {
            let payload = base + HEAP_HEADER_SIZE;
            let len = *(payload as *const i64) as usize;
            let bytes = std::slice::from_raw_parts(
                (payload + STRING_HEADER_BYTES as i64) as *const u8,
                len,
            );
            std::str::from_utf8(bytes).ok()
        }
    }

    /// Read the result slot (`state + 0`). Backend-initialised to `0`; a leaf may
    /// reuse it as a phase scratch sentinel while parked (see [`PollState`]).
    pub fn result(&self) -> i64 {
        // SAFETY: the env always reserves the result slot at `+0`.
        unsafe { *self.base }
    }

    /// Write the single i64 result the host `EffectPoll` reads on Ready
    /// (`state + 0`).
    pub fn set_result(&self, v: i64) {
        // SAFETY: the env always reserves the result slot at `+0`.
        unsafe { *self.base = v }
    }
}

/// A thin, safe wrapper over the host reactor's `register_*` vtable callbacks +
/// the `*Waker` — turning the raw `(*host).vtable_fn(host, …, waker)` indirection
/// into one named verb per readiness kind (`poll-support.md §2.2`). It owns no
/// reactor state: the host owns the *when*; this is the platform-side projection
/// of "register interest." It only registers — it never blocks.
pub struct Reactor {
    host: *const HostCtx,
    waker: *const Waker,
}

impl Reactor {
    /// # Safety
    /// `host`/`waker` must be the live pointers the poll-fn received for this call.
    pub unsafe fn new(host: *const HostCtx, waker: *const Waker) -> Self {
        Reactor { host, waker }
    }

    /// Ask the host reactor to re-poll this effect when `fd` is readable.
    pub fn wake_on_readable(&self, fd: i32) {
        // SAFETY: `host`/`waker` are the live pointers from `new`.
        unsafe {
            let hc = &*self.host;
            (hc.register_readable)(hc.host, fd, self.waker);
        }
    }

    /// Ask the host reactor to re-poll this effect when `fd` is writable.
    pub fn wake_on_writable(&self, fd: i32) {
        // SAFETY: `host`/`waker` are the live pointers from `new`.
        unsafe {
            let hc = &*self.host;
            (hc.register_writable)(hc.host, fd, self.waker);
        }
    }

    /// Ask the host reactor to re-poll this effect at `deadline_nanos` (monotonic).
    pub fn wake_on_timer(&self, deadline_nanos: u64) {
        // SAFETY: `host`/`waker` are the live pointers from `new`.
        unsafe {
            let hc = &*self.host;
            (hc.register_timer)(hc.host, deadline_nanos, self.waker);
        }
    }
}

/// What a phase step decided: done with an i64 result, or parked on a readiness
/// the leaf registered via [`Reactor`].
pub enum PollStep {
    /// The effect completed; write this i64 to the result slot and return Ready.
    Ready(i64),
    /// The leaf registered a readiness (timer/fd) and wants to be re-polled.
    Park,
}

/// The first-poll / re-poll phase scaffold (`poll-support.md §2.3`).
///
/// The host re-invokes the same `PollFn` after every wake, so a leaf must carry
/// "which phase am I in" across polls. `PollState` uses the env **result slot**
/// (`state + 0`) as the phase sentinel — backend-initialised to `0` (= unstarted),
/// so `0` falls out for free on the first poll; `drive` stashes a non-zero
/// `established` marker there while parked and overwrites it with the real result
/// on Ready. (The `async-demo`/`poll-pool` timer leaves use the absolute deadline
/// as that non-zero marker; the generic scaffold uses a caller-supplied marker.)
///
/// `drive` never dispatches another effect — it is pure phase logic over the
/// result slot (the gate-(a) non-re-entry property, `poll-support.md §3.2`).
pub struct PollState<'e> {
    env: &'e PollEnv,
}

impl<'e> PollState<'e> {
    pub fn new(env: &'e PollEnv) -> Self {
        PollState { env }
    }

    /// `true` on the first poll (result slot still the `0` sentinel), `false` on a
    /// re-poll (the slot carries the `established` marker `drive` stashed).
    pub fn is_first_poll(&self) -> bool {
        self.env.result() == 0
    }

    /// Run `setup` exactly once (first poll), then `resume` on each subsequent
    /// poll. `established` is the non-zero marker stashed in the result slot while
    /// parked (MUST be non-zero so it never collides with the `0` unstarted
    /// sentinel — `drive` maps `0` to `1` defensively). On `PollStep::Ready(v)` the
    /// result slot is overwritten with `v` and `Poll::Ready` is returned; on
    /// `PollStep::Park` the slot keeps its marker and `Poll::Pending` is returned.
    pub fn drive(
        &self,
        established: i64,
        setup: impl FnOnce() -> PollStep,
        resume: impl FnOnce() -> PollStep,
    ) -> Poll {
        let step = if self.is_first_poll() {
            // Stash the established marker BEFORE running setup so a Park leaves a
            // non-zero sentinel (re-poll takes the `resume` arm).
            let marker = if established == 0 { 1 } else { established };
            self.env.set_result(marker);
            setup()
        } else {
            resume()
        };
        match step {
            PollStep::Ready(v) => {
                self.env.set_result(v);
                Poll::Ready
            }
            PollStep::Park => Poll::Pending,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{HostCtx, Waker, WakerVTable};
    use core::ffi::c_void;
    use std::sync::atomic::{AtomicU64, AtomicI32, Ordering};

    // -----------------------------------------------------------------------
    // §4A — PollEnv typed env accessor round-trip.
    // design: design/platform/poll-support.md §2.1 — the R1 env-layout
    // convention (result @ +0, leaf arg i @ +8+8i) lives in ONE place; a
    // write-then-read round-trip pins the offsets so the poll leaves are
    // offset-safe. (tests/plan/sprint-96.md §4A)
    // -----------------------------------------------------------------------
    #[test]
    fn poll_state_env_accessor_arg_scratch_set_result_round_trip() {
        // A fixture env: [result | arg0 | arg1].
        let mut env_slots: [i64; 3] = [0, 111, 222];
        let pe = unsafe { PollEnv::new(env_slots.as_mut_ptr() as *mut c_void) };

        // args read at +8 (arg0) and +16 (arg1).
        assert_eq!(unsafe { pe.arg(0) }, 111, "arg(0) must read state+8");
        assert_eq!(unsafe { pe.arg(1) }, 222, "arg(1) must read state+16");

        // result slot starts at the 0 sentinel; set_result writes state+0.
        assert_eq!(pe.result(), 0, "result slot starts at the 0 sentinel");
        pe.set_result(777);
        assert_eq!(pe.result(), 777, "set_result must write/read the result slot at state+0");
        assert_eq!(env_slots[0], 777, "set_result lands at env[0] (state+0)");
        // The args are undisturbed by writing the result.
        assert_eq!(env_slots[1], 111);
        assert_eq!(env_slots[2], 222);
    }

    // A capturing fixture HostCtx: each register_* records its argument so the
    // test can assert the Reactor wrapper called through the vtable correctly.
    static TIMER_DEADLINE: AtomicU64 = AtomicU64::new(0);
    static READABLE_FD: AtomicI32 = AtomicI32::new(-1);
    static WRITABLE_FD: AtomicI32 = AtomicI32::new(-1);

    unsafe extern "C" fn rec_readable(_h: *const c_void, fd: i32, _w: *const Waker) {
        READABLE_FD.store(fd, Ordering::SeqCst);
    }
    unsafe extern "C" fn rec_writable(_h: *const c_void, fd: i32, _w: *const Waker) {
        WRITABLE_FD.store(fd, Ordering::SeqCst);
    }
    unsafe extern "C" fn rec_timer(_h: *const c_void, deadline: u64, _w: *const Waker) {
        TIMER_DEADLINE.store(deadline, Ordering::SeqCst);
    }
    unsafe extern "C" fn noop_wake(_d: *const c_void) {}
    unsafe extern "C" fn noop_wake_by_ref(_d: *const c_void) {}
    unsafe extern "C" fn noop_clone(_d: *const c_void) -> Waker {
        Waker { data: std::ptr::null(), vtable: std::ptr::null() }
    }
    unsafe extern "C" fn noop_drop(_d: *const c_void) {}

    static WAKER_VTABLE: WakerVTable = WakerVTable {
        wake: noop_wake,
        wake_by_ref: noop_wake_by_ref,
        clone: noop_clone,
        drop: noop_drop,
    };

    // -----------------------------------------------------------------------
    // §4B — fd-readiness / timer poll scaffold over the host/waker vtable.
    // design: design/platform/poll-support.md §2.2 — the Reactor wrapper hides
    // the (*host).register_*(host, …, waker) vtable indirection behind one named
    // verb per readiness kind. (tests/plan/sprint-96.md §4B)
    // -----------------------------------------------------------------------
    #[test]
    fn poll_support_fd_readiness_timer_scaffold_over_waker_vtable() {
        TIMER_DEADLINE.store(0, Ordering::SeqCst);
        READABLE_FD.store(-1, Ordering::SeqCst);
        WRITABLE_FD.store(-1, Ordering::SeqCst);

        let host = HostCtx {
            register_readable: rec_readable,
            register_writable: rec_writable,
            register_timer: rec_timer,
            host: std::ptr::null(),
        };
        let waker = Waker { data: std::ptr::null(), vtable: &WAKER_VTABLE };
        let reactor = unsafe { Reactor::new(&host, &waker) };

        reactor.wake_on_timer(123_456);
        reactor.wake_on_readable(7);
        reactor.wake_on_writable(9);

        assert_eq!(TIMER_DEADLINE.load(Ordering::SeqCst), 123_456, "wake_on_timer must register the deadline via the vtable");
        assert_eq!(READABLE_FD.load(Ordering::SeqCst), 7, "wake_on_readable must register the fd via the vtable");
        assert_eq!(WRITABLE_FD.load(Ordering::SeqCst), 9, "wake_on_writable must register the fd via the vtable");
    }

    // -----------------------------------------------------------------------
    // §4B — first-poll / re-poll phase scaffold.
    // design: design/platform/poll-support.md §2.3 — PollState distinguishes the
    // establish step (first poll: arm/register, stash a non-zero marker) from the
    // resume step (re-poll: read-result), over the env result slot reused as the
    // 0-initialised phase sentinel. (tests/plan/sprint-96.md §4B)
    // -----------------------------------------------------------------------
    #[test]
    fn poll_state_phase_first_poll_then_re_poll() {
        let mut env_slots: [i64; 2] = [0, 60]; // [result(sentinel) | arg0=ms]
        let pe = unsafe { PollEnv::new(env_slots.as_mut_ptr() as *mut c_void) };
        let ps = PollState::new(&pe);

        // First poll: is_first_poll() true; drive runs `setup`, which Parks.
        assert!(ps.is_first_poll(), "result==0 ⇒ first poll");
        let p1 = ps.drive(0xDEAD, || PollStep::Park, || panic!("resume must not run on first poll"));
        assert!(matches!(p1, Poll::Pending), "Park ⇒ Pending");
        assert_eq!(pe.result(), 0xDEAD, "drive stashes the established marker while parked");
        assert!(!ps.is_first_poll(), "after setup-park the slot carries the marker ⇒ not first poll");

        // Re-poll: drive runs `resume`, which completes with the result.
        let p2 = ps.drive(0xDEAD, || panic!("setup must not run on re-poll"), || PollStep::Ready(99));
        assert!(matches!(p2, Poll::Ready), "Ready ⇒ Ready");
        assert_eq!(pe.result(), 99, "drive overwrites the marker with the real result on Ready");
    }
}
