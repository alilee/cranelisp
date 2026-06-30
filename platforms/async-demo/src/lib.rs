//! `async-demo` — an in-tree async-capable (poll-shape) platform (S94 R2/R6,
//! FIXME 0457).
//!
//! The single effect `async-read` is the load-bearing real leaf the reactor e2e
//! rows drive end-to-end: a `declare_platform!`-emitted poll-shape
//! [`cranelisp_platform::PollFn`] (`descriptor: blocking = 0`, NOT a blocking
//! `CLIO` thunk) that suspends on
//! the host reactor's timer and resumes to `Ready`. It exists to exercise the
//! whole real-node-await chain (macro -> backend poll-construction arm -> loader
//! -> `cranelisp_run_io` reactor), in-tree, with no separate cdylib fixture.
//!
//! ## `async-read N`
//!
//! Semantically: "after ~N milliseconds, produce N". It is the minimal poll-shape
//! effect that both (a) carries an i64 arg + i64 result through the host-built
//! state-closure env, and (b) genuinely SUSPENDS on the reactor (so two of them in
//! a `Par` overlap in ≈max(delay) not sum on one reactor thread). A timer leaf
//! (vs the fixture's socketpair `recv`) needs no peer/feeder — one poll-fn, one
//! `register_timer`, single-reactor.
//!
//! ## State-closure env contract (the R1 seam, host-built by the backend)
//!
//! The backend builds the state-closure `[header | code_ptr=this poll-fn |
//! drop_glue_ptr | env = result_slot + i64 args]` and passes `state = env base` to
//! the poll-fn. So, relative to `state`:
//!   - `state + 0`  = the reserved **result slot** (`EffectPoll` reads it on Ready)
//!   - `state + 8`  = arg 0 = `N` (the delay-ms / result value)
//!
//! The result slot is backend-initialised to `0` (the sentinel). This leaf uses
//! it as scratch — needing NO extra scratch slots — by stashing the absolute
//! monotonic deadline there while parked (a huge value, never `0`), then
//! overwriting it with `N` on completion:
//!   - first poll (slot == 0): compute `deadline = now + N ms`, store it in the
//!     slot, `register_timer(deadline)`, return `Pending`.
//!   - re-poll (slot != 0 = the deadline): if `now >= deadline` -> write `N` to the
//!     slot, return `Ready`; else (a sibling-driven re-poll before our deadline)
//!     return `Pending` WITHOUT re-registering — the one-shot timer is still parked
//!     in the reactor heap and will fire, so there is no lost wakeup to re-arm.

use core::ffi::c_void;

use cranelisp_platform::{ConcurrencyDescriptor, HostCtx, Poll, Waker};

static HOST: cranelisp_platform::HostContext = cranelisp_platform::HostContext::new();

/// Current `CLOCK_MONOTONIC` time in nanoseconds — the same clock the host
/// reactor's timer wheel reads (`HostCtx::register_timer` takes a monotonic-nanos
/// deadline). The platform computes it itself (it cannot depend on the reactor
/// crate); both sides reading `CLOCK_MONOTONIC` keeps the deadline skew-free.
fn monotonic_nanos() -> u64 {
    let mut ts = libc::timespec { tv_sec: 0, tv_nsec: 0 };
    // SAFETY: `ts` is a valid out-param for `clock_gettime`.
    unsafe { libc::clock_gettime(libc::CLOCK_MONOTONIC, &mut ts) };
    (ts.tv_sec as u64) * 1_000_000_000 + (ts.tv_nsec as u64)
}

/// The `async-read` poll-fn — a poll-shape timer leaf. See the module doc for the
/// state-closure env contract.
///
/// # Safety
/// C-ABI poll-fn (`PollFn`): `state` is the host-built state-closure env base
/// (`result_slot` at +0, arg `N` at +8); `host` / `waker` are live for the call.
pub unsafe extern "C" fn async_read_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const Waker,
) -> Poll {
    let result_ptr = state as *mut i64; // env + 0 = result slot (also our scratch)
    // SAFETY: the env reserves result + N args; arg 0 is at env + 8 (one i64).
    let arg_ptr = unsafe { (state as *mut i64).add(1) }; // env + 8 = arg 0 = N
    // SAFETY: both pointers are within the host-built env (constructor obligation).
    let n = unsafe { *arg_ptr };
    let slot = unsafe { *result_ptr };

    if slot == 0 {
        // First poll: arm the timer, stash the absolute deadline in the slot.
        let delay_ns = (n.max(0) as u64).saturating_mul(1_000_000);
        let mut deadline = monotonic_nanos().saturating_add(delay_ns);
        if deadline == 0 {
            deadline = 1; // never collide with the `0` sentinel (cannot happen, defensive).
        }
        // SAFETY: `result_ptr` is the live result slot.
        unsafe { *result_ptr = deadline as i64 };
        // SAFETY: `host` is a live `HostCtx`; `waker` is a live C-ABI waker the
        // host clones to own (the reactor fires it at the deadline).
        let hc = unsafe { &*host };
        unsafe { (hc.register_timer)(hc.host, deadline, waker) };
        Poll::Pending
    } else {
        let deadline = slot as u64;
        if monotonic_nanos() >= deadline {
            // Fired: write the result `N` (overwriting the stashed deadline).
            // SAFETY: `result_ptr` is the live result slot.
            unsafe { *result_ptr = n };
            Poll::Ready
        } else {
            // Sibling-driven re-poll before our deadline: the one-shot timer is
            // still parked in the reactor and will fire, so do NOT re-register
            // (no duplicate heap entry) — just stay parked. No lost wakeup.
            Poll::Pending
        }
    }
}

cranelisp_platform::declare_platform! {
    name: "async-demo",
    version: "0.1.0",
    host: HOST,
    functions: [
        async_read_pollfn {
            cl_name: "async-read",
            sig: "(Fn [primitives/Int] (primitives/IO primitives/Int))",
            doc: "Suspend on the reactor for ~N milliseconds, then produce N (poll-shape async demo leaf)",
            params: [n],
            descriptor: ConcurrencyDescriptor {
                token: 0,
                cardinality: 0,
                global_budget: 0,
                blocking: 0, // poll-shape -> the backend's poll-construction arm
                _reserved: [0; 3],
            },
        },
    ]
}
