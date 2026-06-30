//! `poll-pool` — the S96 Chunk-A poll-shape **capacity** test leaf (Gap G1).
//!
//! The poll-carrier analogue of the S95 BLOCKING `pool-demo`. Three
//! `declare_platform!`-emitted poll-shape effects (`descriptor: blocking = 0`),
//! each `ResourceSerial`, each declaring its `(token, capacity)` as the **two leading
//! cranelisp args** (the S95 `pool-demo` convention, now on the poll carrier —
//! `design/platform/poll-support.md §3.4.2/§3.4.6`). Each routes to the host
//! reactor via an armed monotonic timer (mirroring the S94 `async-demo` leaf) so
//! the token-capacity `Semaphore` pool's admit/park behaviour is wall-clock
//! observable when the reactor drives N overlapping polls and parks the (N+1)th.
//!
//! - `poll-read  : (Int token, Int capacity, Int ms) -> IO Int` — suspend ~`ms`
//!   on the reactor, return `ms`.
//! - `poll-write : (Int token, Int capacity, Int ms) -> IO Int` — a DISTINCT poll
//!   effect kind on the SAME token (the token-sharing case), return `ms`.
//! - `poll-log   : (Int token, Int capacity, Int ms, String tag) -> IO Int` —
//!   suspend ~`ms`, then print `tag` to real stdout (the within-token source-order
//!   witness), return `ms`.
//!
//! ## The leading-pair operand convention (S96 A2/A4)
//!
//! The cranelisp call `(poll-read token capacity ms)` lowers, via the backend's
//! `ResourceSerial`-keyed leading-pair convention (the producer pass does NOT
//! inject for a `ResourceSerial` leaf — the source already supplies the pair), to
//! `arg_vals = [token, capacity, ms]`. The backend peels `token` → node
//! `field_offset(1)` (abs 32), `capacity` → `field_offset(2)` (abs 40, node-only
//! admission metadata), and marshals the LEAF args (`arg_vals[2..]` = `[ms]`,
//! plus `tag` for `poll-log`) into the host-built state-closure env at
//! `capture(1+i)`. So, relative to the `state` the poll-fn receives:
//!   - `state + 0`  = the reserved **result slot** (also used here as scratch for
//!     the parked deadline, exactly like `async-demo`)
//!   - `state + 8`  = leaf arg 0 = `ms`
//!   - `state + 16` = leaf arg 1 = `tag` (CLString base pointer — `poll-log` only)
//!
//! The poll-fn never sees `token`/`capacity` — those are node-only admission
//! metadata the host reactor reads for acquire-around-poll (the thin-platform
//! thesis: the platform registers readiness and returns `Poll`; the host owns the
//! pool/permit).

use core::ffi::c_void;

use cranelisp_platform::poll_support::{PollEnv, Reactor};
use cranelisp_platform::{ConcurrencyDescriptor, HostCtx, Poll, Waker};

static HOST: cranelisp_platform::HostContext = cranelisp_platform::HostContext::new();

/// Current `CLOCK_MONOTONIC` time in nanoseconds — the same clock the host
/// reactor's timer wheel reads (`HostCtx::register_timer` takes a monotonic-nanos
/// deadline). Both sides reading `CLOCK_MONOTONIC` keeps the deadline skew-free.
fn monotonic_nanos() -> u64 {
    let mut ts = libc::timespec { tv_sec: 0, tv_nsec: 0 };
    // SAFETY: `ts` is a valid out-param for `clock_gettime`.
    unsafe { libc::clock_gettime(libc::CLOCK_MONOTONIC, &mut ts) };
    (ts.tv_sec as u64) * 1_000_000_000 + (ts.tv_nsec as u64)
}

/// The shared armed-timer poll body: read `ms` at `state + 8`, arm a one-shot
/// reactor timer for `ms` ms on first poll (stashing the absolute deadline in the
/// result slot as scratch), and resume to `Ready` once the deadline passes,
/// writing `ms` as the result. Mirrors the `async-demo` leaf — the suspension is
/// what lets N same-token polls overlap on the one reactor thread while the host's
/// acquire-around-poll permit enforces the `(token, capacity)` pool.
///
/// # Safety
/// `state` is the host-built state-closure env base (`result_slot` at +0, `ms` at
/// +8); `host`/`waker` are live for the call.
unsafe fn arm_timer_poll(state: *mut c_void, host: *const HostCtx, waker: *const Waker) -> Poll {
    // poll_support codifies the two repeated idioms: the typed env accessor (the
    // R1 offset convention — result @ +0, leaf arg 0 @ +8) and the reactor
    // readiness registration over the host/waker vtable. The deadline-as-phase
    // logic (stash in the result slot, read back) stays hand-written here — it is
    // the leaf's syscall/result interpretation, not a poll_support concern.
    // SAFETY: `state` is the host-built env base; `host`/`waker` are live.
    let env = unsafe { PollEnv::new(state) };
    let reactor = unsafe { Reactor::new(host, waker) };
    // SAFETY: leaf arg 0 (`ms`) is in the env (the effect declares it).
    let ms = unsafe { env.arg(0) };
    let slot = env.result();

    if slot == 0 {
        // First poll: arm the timer, stash the absolute deadline in the result
        // slot (reused as phase scratch — `0` = unstarted, non-zero = armed).
        let delay_ns = (ms.max(0) as u64).saturating_mul(1_000_000);
        let mut deadline = monotonic_nanos().saturating_add(delay_ns);
        if deadline == 0 {
            deadline = 1; // never collide with the `0` sentinel (defensive).
        }
        env.set_result(deadline as i64);
        reactor.wake_on_timer(deadline);
        Poll::Pending
    } else {
        let deadline = slot as u64;
        if monotonic_nanos() >= deadline {
            // Fired: write the result `ms` (overwriting the stashed deadline).
            env.set_result(ms);
            Poll::Ready
        } else {
            // Sibling-driven re-poll before our deadline: the one-shot timer is
            // still parked in the reactor and will fire, so do NOT re-register.
            Poll::Pending
        }
    }
}

/// `poll-read` — a `ResourceSerial` poll-shape armed-timer leaf. Suspends ~`ms`
/// on the reactor, returns `ms`.
///
/// # Safety
/// C-ABI poll-fn (`PollFn`); see [`arm_timer_poll`].
pub unsafe extern "C" fn poll_read_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const Waker,
) -> Poll {
    // SAFETY: forwarded C-ABI poll-fn args.
    unsafe { arm_timer_poll(state, host, waker) }
}

/// `poll-write` — a DISTINCT poll effect kind drawing from the SAME token's pool
/// (the token-sharing case). Identical armed-timer body; the distinctness is the
/// effect identity (a separate GOT slot / manifest entry), not the behaviour.
///
/// # Safety
/// C-ABI poll-fn (`PollFn`); see [`arm_timer_poll`].
pub unsafe extern "C" fn poll_write_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const Waker,
) -> Poll {
    // SAFETY: forwarded C-ABI poll-fn args.
    unsafe { arm_timer_poll(state, host, waker) }
}

/// `poll-log` — armed-timer leaf that additionally prints its `tag` (leaf arg 1,
/// a `CLString` base pointer at `state + 16`) to **real stdout** on the Ready
/// phase (the within-token source-order witness — at capacity 1 the effects
/// serialise AND land in source order, observable via the emitted tags).
///
/// The `tag` is a heap `CLString` whose RC'd reference rides the state-closure
/// env (the host glue frees it via the node's `drop_glue_ptr`); this leaf only
/// READS it (never consumes/frees), so it does no RC work. It is read with the
/// public heap-layout constants — `[alloc_size | rc | len | bytes…]`, payload at
/// `base + HEAP_HEADER_SIZE`, `len` then bytes at `payload + STRING_HEADER_BYTES`.
///
/// # Safety
/// C-ABI poll-fn (`PollFn`); `state` is the host-built env (`result` at +0,
/// `ms` at +8, `tag` base pointer at +16). `host`/`waker` live for the call.
pub unsafe extern "C" fn poll_log_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const Waker,
) -> Poll {
    // SAFETY: forwarded C-ABI poll-fn args; the armed-timer body reads result@+0
    // and ms@+8 and parks/resumes. On Ready it returns Poll::Ready below.
    let poll = unsafe { arm_timer_poll(state, host, waker) };
    if matches!(poll, Poll::Ready) {
        // Read the tag (leaf arg 1) as a borrowed &str via poll_support and print
        // it to stdout. `arg_str` codifies the CLString heap-layout read; the leaf
        // only borrows (RC is owned by the env's drop_glue_ptr).
        // SAFETY: leaf arg 1 (`tag`) is a live CLString base pointer (the effect
        // declares it as a String param).
        let env = unsafe { PollEnv::new(state) };
        if let Some(s) = unsafe { env.arg_str(1) } {
            use std::io::Write;
            let mut out = std::io::stdout();
            let _ = out.write_all(s.as_bytes());
            let _ = out.flush();
        }
    }
    poll
}

// The host-exported runtime-error-slot setter (`runtime/panic`,
// `crates/cranelisp-intrinsics/src/panic.rs`). A poll-fn CANNOT signal a fault by
// `panic!`ing: `PollFn` is `extern "C"`, so a Rust panic ABORTS at the FFI
// boundary (`(this.poll_fn)(…)` in `reactor.rs::EffectPoll::poll`) BEFORE the
// supervisor's `catch_unwind` could see it. Instead a faulting leaf SETS the
// runtime-error slot, which the supervisor captures with `take_runtime_error()`
// at the strand's completion boundary (`reactor.rs::supervised`) — this is the
// exact mechanism the unit-proven supervisor tests use
// (`io/tests.rs::supervisor_catches_runtime_error_strand_records_failed…`, which
// drives a strand via `set_runtime_error`). Resolved against the host at dlopen
// (RTLD_GLOBAL / `-rdynamic`), exactly like the synthetic `macros`-module
// primitive externs the cache `Linker` dlsym-resolves.
unsafe extern "C" {
    #[link_name = "runtime/panic"]
    fn runtime_panic(msg_ptr: *const u8, msg_len: usize);
}

/// The fault message the runtime-error slot carries.
const POLL_FAULT_MSG: &str =
    "poll-fault: deliberate fault for the supervisor panic-survival e2e (FIXME 0468)";

/// Signal a deliberate fault via the runtime-error slot (no unwind — see the
/// `runtime_panic` extern above). Factored so the unit test can provide a stub
/// `runtime/panic` symbol and witness the call.
fn signal_poll_fault() {
    // SAFETY: `runtime/panic` is host-exported and resolved at dlopen; it sets a
    // thread-local slot and returns without unwinding.
    unsafe { runtime_panic(POLL_FAULT_MSG.as_ptr(), POLL_FAULT_MSG.len()) };
}

/// `poll-fault` — a `ResourceSerial` poll-shape armed-timer leaf that, once its
/// timer fires, deliberately FAULTS by setting the runtime-error slot (then
/// returns `Poll::Ready` with the armed-timer result). The supervisor's
/// "catch + drop, the launch loop lives" policy (`reactor.rs`
/// `supervised`/`apply_policy`) is then witnessable end-to-end without any
/// web/HTTP machinery: three launched-and-not-joined `poll-fault`s on distinct
/// tokens each fault, the supervisor captures each via `take_runtime_error()` +
/// emits `StrandFailed` + drops the strand, and the launching strand survives to
/// reach `(Pure 42)`
/// (`tests/concurrency_fanout.rs::detached_faulting_effect_does_not_abort_the_launch_loop`,
/// FIXME 0468).
///
/// # Safety
/// C-ABI poll-fn (`PollFn`); see [`arm_timer_poll`].
pub unsafe extern "C" fn poll_fault_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const Waker,
) -> Poll {
    // SAFETY: forwarded C-ABI poll-fn args; the armed-timer body parks until the
    // deadline, then resolves Ready — at which point we set the runtime-error slot.
    let poll = unsafe { arm_timer_poll(state, host, waker) };
    if matches!(poll, Poll::Ready) {
        signal_poll_fault();
    }
    poll
}

/// A process-lifetime never-readable fd — the read end of a pipe whose write end
/// is never written (and intentionally leaked alongside it). A single shared fd
/// pair is created lazily and reused by every `poll-block` instance: the
/// cancellation e2e drives `poll-block` SEQUENTIALLY (one in flight at a time —
/// each loses a race, is cancelled, deregistered, then the next iteration
/// re-arms), so the read end is registered, deregistered, and re-registered with
/// no overlap. Bounded to ONE fd pair for the whole process (a test platform), so
/// there is no fd exhaustion despite the leak.
fn never_readable_fd() -> i32 {
    use std::sync::OnceLock;
    static FD: OnceLock<i32> = OnceLock::new();
    *FD.get_or_init(|| {
        let mut fds = [0i32; 2];
        // SAFETY: `fds` is a valid 2-int out array for `pipe(2)`.
        let rc = unsafe { libc::pipe(fds.as_mut_ptr()) };
        if rc != 0 {
            // pipe(2) failed (fd exhaustion etc.) — fall back to a definitely-invalid
            // fd; the host's mio register will surface the error. Not expected on a
            // test host.
            return -1;
        }
        // fds[1] (write end) is never written and never closed — the read end
        // (fds[0]) stays perpetually not-readable. Both are leaked for the process
        // lifetime.
        fds[0]
    })
}

/// `poll-block` — a never-readying fd-arming poll leaf (S96 Chunk C, slice 7).
/// On the first poll it registers READABLE interest on a never-readable fd
/// ([`never_readable_fd`]) and returns `Pending`; it NEVER reaches `Ready`. Its
/// sole purpose is to be a guaranteed race LOSER whose **fd interest must be
/// actively deregistered on `EffectPoll` drop** (finding #3, `reactor.md §2.16`):
/// the cancellation volume e2e
/// (`tests/concurrency_cancellation.rs::volume_cancellation_does_not_leak_fd_waiters_bounded`)
/// races a `poll-block` against a short deadline `poll-read` VOLUME_N times and
/// asserts bounded wall-clock — i.e. that the host's `fd_waiters` map + mio
/// registrations do not grow unboundedly across the cancelled losers.
///
/// The result slot doubles as a one-shot armed sentinel (`0` = unarmed, non-zero =
/// armed): a sibling-driven re-poll before any readiness does NOT re-register (the
/// mio registration is still live; the `arm_timer_poll` idempotency pattern).
///
/// # Safety
/// C-ABI poll-fn (`PollFn`): `state` is the host-built env (`result`/armed sentinel
/// at +0); `host`/`waker` are live for the call.
pub unsafe extern "C" fn poll_block_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const Waker,
) -> Poll {
    // SAFETY: `state` is the host-built env base; `host`/`waker` are live.
    let env = unsafe { PollEnv::new(state) };
    let reactor = unsafe { Reactor::new(host, waker) };
    if env.result() == 0 {
        // First poll: arm READABLE interest on the never-readable fd, mark armed.
        env.set_result(1);
        reactor.wake_on_readable(never_readable_fd());
    }
    // Never readies — always Pending (the guaranteed race loser).
    Poll::Pending
}

/// The `ResourceSerial` descriptor every poll-pool effect carries: `token 0`
/// (the static conflict identity — the DYNAMIC per-resource token rides the
/// leading `token` operand at the call site), `cardinality 1`, `blocking 0`
/// (poll-shape ⇒ the reactor carrier). `nearest_scheduling_class` maps
/// `token 0, cardinality 1` ⇒ `ResourceSerial`, so the backend leaves the
/// source-supplied `(token, capacity)` leading pair intact (no `(0,1)` inject).
const RESOURCE_SERIAL: ConcurrencyDescriptor = ConcurrencyDescriptor {
    token: 0,
    cardinality: 1,
    global_budget: 0,
    blocking: 0,
    _reserved: [0; 3],
};

cranelisp_platform::declare_platform! {
    name: "poll-pool",
    version: "0.1.0",
    host: HOST,
    functions: [
        poll_read_pollfn {
            cl_name: "poll-read",
            sig: "(Fn [primitives/Int primitives/Int primitives/Int] (primitives/IO primitives/Int))",
            doc: "Suspend ~ms on the reactor's (token, capacity) pool and return ms (poll-shape capacity carrier, for testing)",
            params: [token, capacity, ms],
            descriptor: RESOURCE_SERIAL,
        },
        poll_write_pollfn {
            cl_name: "poll-write",
            sig: "(Fn [primitives/Int primitives/Int primitives/Int] (primitives/IO primitives/Int))",
            doc: "A distinct poll effect kind sharing the same token's pool: suspend ~ms and return ms (poll-shape capacity carrier, for testing token sharing)",
            params: [token, capacity, ms],
            descriptor: RESOURCE_SERIAL,
        },
        poll_log_pollfn {
            cl_name: "poll-log",
            sig: "(Fn [primitives/Int primitives/Int primitives/Int primitives/String] (primitives/IO primitives/Int))",
            doc: "Suspend ~ms then print tag to stdout and return ms (poll-shape capacity carrier, witnesses within-token source order)",
            params: [token, capacity, ms, tag],
            descriptor: RESOURCE_SERIAL,
        },
        poll_fault_pollfn {
            cl_name: "poll-fault",
            sig: "(Fn [primitives/Int primitives/Int primitives/Int] (primitives/IO primitives/Int))",
            doc: "Suspend ~ms then deliberately FAULT (panic) on the Ready phase -- the supervisor panic-survival witness (FIXME 0468)",
            params: [token, capacity, ms],
            descriptor: RESOURCE_SERIAL,
        },
        poll_block_pollfn {
            cl_name: "poll-block",
            sig: "(Fn [primitives/Int primitives/Int] (primitives/IO primitives/Int))",
            doc: "Arm READABLE interest on a never-readable fd and park forever -- a guaranteed race loser whose fd interest must be deregistered on cancel (finding #3 witness)",
            params: [token, capacity],
            descriptor: RESOURCE_SERIAL,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::sync::atomic::{AtomicBool, Ordering};
    use cranelisp_platform::{Waker, WakerVTable};

    // A minimal fixture HostCtx/Waker: the poll-fault Ready path never touches the
    // register_* callbacks (it faults after the timer fires, before parking), so
    // they are noops.
    unsafe extern "C" fn noop_readable(_h: *const c_void, _fd: i32, _w: *const Waker) {}
    unsafe extern "C" fn noop_writable(_h: *const c_void, _fd: i32, _w: *const Waker) {}
    unsafe extern "C" fn noop_timer(_h: *const c_void, _deadline: u64, _w: *const Waker) {}
    unsafe extern "C" fn noop_wake(_d: *const c_void) {}
    unsafe extern "C" fn noop_wake_by_ref(_d: *const c_void) {}
    unsafe extern "C" fn noop_clone(_d: *const c_void) -> Waker {
        Waker { data: core::ptr::null(), vtable: core::ptr::null() }
    }
    unsafe extern "C" fn noop_drop(_d: *const c_void) {}

    static WAKER_VTABLE: WakerVTable = WakerVTable {
        wake: noop_wake,
        wake_by_ref: noop_wake_by_ref,
        clone: noop_clone,
        drop: noop_drop,
    };

    // Test-only stub for the host-exported `runtime/panic` slot setter (the real
    // host provides it; this test binary does not link cranelisp-intrinsics). It
    // records that poll-fault signalled the runtime-error slot — the unit witness
    // that the leaf faults via the slot (the supervisor-catchable path), NOT via a
    // boundary-aborting Rust panic.
    static FAULT_SIGNALLED: AtomicBool = AtomicBool::new(false);

    #[unsafe(export_name = "runtime/panic")]
    extern "C" fn test_runtime_panic_stub(_msg_ptr: *const u8, _msg_len: usize) {
        FAULT_SIGNALLED.store(true, Ordering::SeqCst);
    }

    // design: design/arch/fixmes/0468-platform-poll-fault-leaf-for-supervisor-e2e.md
    // -- poll-fault faults on the Ready phase by SETTING the runtime-error slot
    // (via the host-exported `runtime/panic`), so the supervisor's
    // take_runtime_error -> StrandFailed -> drop -> survive policy is witnessable
    // (a poll-fn cannot `panic!`: extern "C" aborts at the FFI boundary). The
    // fixture env seeds the result slot with a past deadline (non-zero => already
    // fired) so arm_timer_poll takes the Ready branch on this single call.
    #[test]
    fn poll_fault_signals_runtime_error_on_ready_phase() {
        let host = HostCtx {
            register_readable: noop_readable,
            register_writable: noop_writable,
            register_timer: noop_timer,
            host: core::ptr::null(),
        };
        let waker = Waker { data: core::ptr::null(), vtable: &WAKER_VTABLE };
        // env: [result_slot = 1 (a past deadline => fired), ms = 0].
        let mut env_slots: [i64; 2] = [1, 0];
        FAULT_SIGNALLED.store(false, Ordering::SeqCst);
        // SAFETY: env_slots is a valid [result | ms] env; host/waker are live.
        let poll = unsafe {
            poll_fault_pollfn(env_slots.as_mut_ptr() as *mut c_void, &host, &waker)
        };
        assert!(matches!(poll, Poll::Ready), "a fired timer => Ready");
        assert!(
            FAULT_SIGNALLED.load(Ordering::SeqCst),
            "poll-fault must SET the runtime-error slot on the Ready phase \
             (the supervisor-catchable fault path), not abort via panic"
        );
    }
}
