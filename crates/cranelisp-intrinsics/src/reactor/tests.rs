//! Reactor spine + Par-async overlap tests (slice-2 reactor; gated
//! `concurrency-runtime`, run under `cargo nt-concurrency-runtime`).
//!
//! These prove the load-bearing artifact of the effect-concurrency track
//! (`design/arch/effect-concurrency.md` App. B acceptance):
//!   1. the **spine** — a single effect leaf suspends (`Pending` → parks on the
//!      reactor) and resumes (`wake` → `Ready`) through the mio reactor + the
//!      `HostCtx` / C-ABI `Waker`, emitting `EffectDispatched`/`Suspended`/
//!      `Resumed`;
//!   2. the **overlap** — two slow `async-read`s complete in ≈max(d1,d2), NOT
//!      d1+d2, on ONE reactor thread (no thread-per-read).

use super::*;
use crate::strand::{drain_strand_events, next_strand, start_strand_recording, StrandEvent};
use std::collections::HashSet;
use std::sync::Mutex;
use std::time::{Duration, Instant};

// ---------------------------------------------------------------------------
// socketpair helpers
// ---------------------------------------------------------------------------

/// A connected pair of AF_UNIX stream fds; `read_end` is set non-blocking so the
/// `async-read` poll-fn observes `EWOULDBLOCK` and parks rather than blocking.
struct SockPair {
    read_end: i32,
    write_end: i32,
}

impl SockPair {
    fn new() -> Self {
        let mut fds = [0i32; 2];
        // SAFETY: standard socketpair call with a valid 2-element out array.
        let rc = unsafe { libc::socketpair(libc::AF_UNIX, libc::SOCK_STREAM, 0, fds.as_mut_ptr()) };
        assert_eq!(rc, 0, "socketpair failed");
        // Make the read end non-blocking.
        // SAFETY: fds[0] is a valid fd just returned by socketpair.
        let flags = unsafe { libc::fcntl(fds[0], libc::F_GETFL) };
        unsafe { libc::fcntl(fds[0], libc::F_SETFL, flags | libc::O_NONBLOCK) };
        SockPair {
            read_end: fds[0],
            write_end: fds[1],
        }
    }
}

impl Drop for SockPair {
    fn drop(&mut self) {
        // SAFETY: both fds are owned by this pair and closed exactly once.
        unsafe {
            libc::close(self.read_end);
            libc::close(self.write_end);
        }
    }
}

/// Build an `async-read` leaf reading from `state.fd`.
unsafe fn read_leaf<'h>(
    state: *mut AsyncReadState,
    host: &'h HostCtx,
    strand: StrandId,
) -> EffectPoll<'h> {
    unsafe {
        EffectPoll::new(
            state as *mut c_void,
            async_read_pollfn,
            host,
            strand,
        )
    }
}

/// Build a timer-feeder leaf that writes to `state.peer_fd` after its deadline.
unsafe fn feeder_leaf<'h>(
    state: *mut TimerWriteState,
    host: &'h HostCtx,
    strand: StrandId,
) -> EffectPoll<'h> {
    unsafe {
        EffectPoll::new(
            state as *mut c_void,
            timer_write_pollfn,
            host,
            strand,
        )
    }
}

// ---------------------------------------------------------------------------
// 1. Spine — a single leaf suspends + resumes through the reactor (timer path).
// ---------------------------------------------------------------------------

// spec: design/arch/effect-concurrency.md App. B "Strand observability hook" +
// spill marker (1) — the single-leaf suspend/resume proves the spine: async
// trampoline + mio reactor + the `HostCtx`/`Waker` C-ABI + one `StrandId` path.
// A timer leaf registers a `register_timer` interest (Pending → parks), the
// reactor blocks in `mio::poll` until the deadline, fires the waker, and the
// leaf resumes to `Ready`.
#[test]
fn single_leaf_suspend_resume_through_reactor() {
    start_strand_recording();
    let strand = next_strand();
    let pair = SockPair::new();
    let delay_ms = 40u64;
    let deadline = monotonic_nanos() + delay_ms * 1_000_000;

    let start = Instant::now();
    let result = block_on_reactor(async |env| {
        let host = env.host;
        let mut fstate = TimerWriteState {
            result: 0,
            peer_fd: pair.write_end,
            deadline_nanos: deadline,
            registered: false,
        };
        let leaf = unsafe { feeder_leaf(&mut fstate, host, strand) };
        leaf.await
    })
    .expect("reactor");
    let elapsed = start.elapsed();

    assert_eq!(result, 0, "feeder leaf returns unit (0)");
    // It genuinely PARKED on the reactor timer — not a busy spin.
    assert!(
        elapsed.as_millis() as u64 >= delay_ms - 10,
        "leaf should suspend until ≈deadline, got {elapsed:?}"
    );

    let events = drain_strand_events();
    assert_eq!(
        events,
        vec![
            StrandEvent::EffectDispatched { strand },
            StrandEvent::EffectSuspended { strand },
            StrandEvent::EffectResumed { strand },
        ],
        "single-leaf strand trace must be Dispatched → Suspended → Resumed"
    );
}

// ---------------------------------------------------------------------------
// 2. The `async-read` fd path — suspend on register_readable, resume on the byte.
// ---------------------------------------------------------------------------

// spec: design/arch/effect-concurrency.md App. B "Demo leaf — async-read" — the
// `recv` → `EWOULDBLOCK` → `register_readable` + `Pending`, then resume on the
// fed byte. One read + one timer feeder, both on the single reactor.
#[test]
fn async_read_suspends_on_ewouldblock_and_resumes_on_byte() {
    start_strand_recording();
    let read_strand = next_strand();
    let feed_strand = next_strand();
    let pair = SockPair::new();
    let deadline = monotonic_nanos() + 40 * 1_000_000;

    let results = block_on_reactor(async |env| {
        let host = env.host;
        let mut rstate = AsyncReadState {
            fd: pair.read_end,
            result: 0,
            registered: false,
        };
        let mut fstate = TimerWriteState {
            result: 0,
            peer_fd: pair.write_end,
            deadline_nanos: deadline,
            registered: false,
        };
        let read = unsafe { read_leaf(&mut rstate, host, read_strand) };
        let feed = unsafe { feeder_leaf(&mut fstate, host, feed_strand) };
        join_io_leaves(vec![read, feed]).await
    })
    .expect("reactor");

    assert_eq!(results[0], 1, "the async-read received the 1 fed byte");

    let events = drain_strand_events();
    // The read strand must have parked on the fd and resumed.
    assert!(events.contains(&StrandEvent::EffectDispatched { strand: read_strand }));
    assert!(events.contains(&StrandEvent::EffectSuspended { strand: read_strand }));
    assert!(events.contains(&StrandEvent::EffectResumed { strand: read_strand }));
}

// ---------------------------------------------------------------------------
// 3. Overlap — two slow reads complete in ≈max(d1,d2), on ONE reactor thread.
// ---------------------------------------------------------------------------

/// Thread ids every fixture poll-fn ran on, for the "no thread-per-read"
/// assertion. The recording wrappers below push into this; the overlap test
/// asserts the set is a single thread.
///
/// M3: process-global state — correctness relies on nextest's process-per-test
/// isolation (each `#[test]` runs in its own process, so this static is private
/// to the one overlap test that uses it).
static POLL_THREADS: Mutex<Option<HashSet<std::thread::ThreadId>>> = Mutex::new(None);

fn record_thread() {
    if let Some(set) = POLL_THREADS.lock().unwrap().as_mut() {
        set.insert(std::thread::current().id());
    }
}

unsafe extern "C" fn rec_read_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const CWaker,
) -> CPoll {
    record_thread();
    unsafe { async_read_pollfn(state, host, waker) }
}

unsafe extern "C" fn rec_timer_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const CWaker,
) -> CPoll {
    record_thread();
    unsafe { timer_write_pollfn(state, host, waker) }
}

// spec: design/arch/effect-concurrency.md App. B acceptance #1 — two `async-read`s
// with delays d1, d2 complete in ≈max(d1,d2), NOT d1+d2, on ONE reactor thread
// (assert no thread-per-read). The feeds are driven by the host reactor's timer
// wheel, so the whole demo is single-reactor with no per-read OS thread.
#[test]
fn two_async_reads_overlap_max_not_sum_one_thread() {
    *POLL_THREADS.lock().unwrap() = Some(HashSet::new());
    start_strand_recording();

    let d1_ms = 100u64;
    let d2_ms = 200u64;
    let s_read1 = next_strand();
    let s_read2 = next_strand();
    let s_feed1 = next_strand();
    let s_feed2 = next_strand();
    let p1 = SockPair::new();
    let p2 = SockPair::new();
    let now = monotonic_nanos();
    let dl1 = now + d1_ms * 1_000_000;
    let dl2 = now + d2_ms * 1_000_000;

    let start = Instant::now();
    let results = block_on_reactor(async |env| {
        let host = env.host;
        let mut r1 = AsyncReadState { result: 0, fd: p1.read_end, registered: false };
        let mut r2 = AsyncReadState { result: 0, fd: p2.read_end, registered: false };
        let mut f1 = TimerWriteState { result: 0, peer_fd: p1.write_end, deadline_nanos: dl1, registered: false };
        let mut f2 = TimerWriteState { result: 0, peer_fd: p2.write_end, deadline_nanos: dl2, registered: false };
        // Reads use the thread-recording wrappers so the test can prove no
        // read ran on a thread other than the reactor's.
        let read1 = unsafe {
            EffectPoll::new(&mut r1 as *mut _ as *mut c_void, rec_read_pollfn, host, s_read1)
        };
        let read2 = unsafe {
            EffectPoll::new(&mut r2 as *mut _ as *mut c_void, rec_read_pollfn, host, s_read2)
        };
        let feed1 = unsafe {
            EffectPoll::new(&mut f1 as *mut _ as *mut c_void, rec_timer_pollfn, host, s_feed1)
        };
        let feed2 = unsafe {
            EffectPoll::new(&mut f2 as *mut _ as *mut c_void, rec_timer_pollfn, host, s_feed2)
        };
        join_io_leaves(vec![read1, read2, feed1, feed2]).await
    })
    .expect("reactor");
    let elapsed_ms = start.elapsed().as_millis() as u64;

    // Both reads got their byte.
    assert_eq!(results[0], 1, "read1 received its byte");
    assert_eq!(results[1], 1, "read2 received its byte");

    // OVERLAP: completed in ≈max(d1,d2)=200ms, strictly under the d1+d2=300ms a
    // sequential (thread-per-read serialized, or non-overlapping) run would take.
    assert!(
        elapsed_ms >= d2_ms - 40,
        "must wait for the slower read (~{d2_ms}ms), got {elapsed_ms}ms"
    );
    assert!(
        elapsed_ms < d1_ms + d2_ms - 40,
        "two reads must OVERLAP (≈max {d2_ms}ms, NOT sum {}ms): got {elapsed_ms}ms",
        d1_ms + d2_ms
    );

    // NO thread-per-read: every poll-fn ran on exactly one thread (the reactor's).
    let threads = POLL_THREADS.lock().unwrap().take().unwrap();
    assert_eq!(
        threads.len(),
        1,
        "all leaf polls must run on ONE reactor thread (no thread-per-read), saw {}",
        threads.len()
    );
    assert!(
        threads.contains(&std::thread::current().id()),
        "the single reactor thread is the calling (block_on) thread"
    );

    // STRAND TRACE: both reads dispatched, suspended, and resumed — and the two
    // strands are interleaved (join_all dispatches all leaves in the first poll).
    let events = drain_strand_events();
    for s in [s_read1, s_read2] {
        assert!(events.contains(&StrandEvent::EffectDispatched { strand: s }), "dispatched {s:?}");
        assert!(events.contains(&StrandEvent::EffectSuspended { strand: s }), "suspended {s:?}");
        assert!(events.contains(&StrandEvent::EffectResumed { strand: s }), "resumed {s:?}");
    }
    // Interleaving: read2's dispatch lands before read1's resume (the strands are
    // in flight concurrently, not run one-after-the-other).
    let read2_dispatch = events
        .iter()
        .position(|e| *e == StrandEvent::EffectDispatched { strand: s_read2 })
        .unwrap();
    let read1_resume = events
        .iter()
        .position(|e| *e == StrandEvent::EffectResumed { strand: s_read1 })
        .unwrap();
    assert!(
        read2_dispatch < read1_resume,
        "the two read strands must be interleaved (concurrent), not sequential"
    );
}

// ---------------------------------------------------------------------------
// 4. I2 — re-registration after a one-shot fire (no lost wakeup).
// ---------------------------------------------------------------------------

/// State for a leaf that needs TWO separate fires to complete: it consumes one
/// byte per poll and only returns `Ready` once it has seen two bytes. The first
/// fire delivers byte 1 and does NOT satisfy it, so it returns `Pending` a second
/// time — and must re-arm interest to receive the second byte's wakeup.
#[repr(C)]
struct TwoFireReadState {
    /// FIRST field ⇒ at the generic [`super::RESULT_SLOT_OFFSET`] `EffectPoll`
    /// reads on `Ready` (S94 generic env-offset result read).
    result: i64,
    fd: i32,
    bytes_seen: i64,
}

/// Poll-fn that recv's ONE byte at a time and needs two bytes (two distinct
/// fires) to complete. It re-registers interest on EVERY `Pending` — the I2
/// contract. With the old `registered`-latch gate this second registration would
/// be skipped after the first fire's one-shot deregister, and the second byte's
/// wakeup would be lost (the leaf would never re-poll, or `block_on_reactor`
/// would trip its "Pending with no reactor waiters" panic). With the fix it
/// re-arms and completes.
unsafe extern "C" fn two_fire_read_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const CWaker,
) -> CPoll {
    let st = unsafe { &mut *(state as *mut TwoFireReadState) };
    // ONE byte per recv so two fed bytes genuinely require two fires.
    let mut buf = [0u8; 1];
    // SAFETY: `st.fd` is a valid non-blocking fd; `buf` is a valid 1-byte out-buf.
    let n = unsafe { libc::recv(st.fd, buf.as_mut_ptr() as *mut c_void, 1, 0) };
    if n > 0 {
        st.bytes_seen += n as i64;
        if st.bytes_seen >= 2 {
            st.result = st.bytes_seen;
            return CPoll::Ready;
        }
        // Got a byte but NOT done — fall through to re-register + Pending.
    }
    // Re-register interest on every Pending (the I2 re-registration obligation):
    // after the first fire the reactor has one-shot-deregistered us, so this is
    // the ONLY thing that re-arms the wakeup for the second byte.
    let hc = unsafe { &*host };
    unsafe { (hc.register_readable)(hc.host, st.fd, waker) };
    CPoll::Pending
}

// spec: design/arch/effect-concurrency.md App. B "Demo leaf" + reactor
// one-shot-deregister contract — a leaf that returns `Pending` a SECOND time
// (its first fire did not satisfy it: a short read) must still be re-woken and
// complete. Proves I2: the poll-fn re-registers on every `Pending` and the
// reactor's idempotent `register_fd` re-arms the one-shot waiter, so the second
// byte's readiness is delivered — no lost wakeup.
#[test]
fn leaf_pending_twice_re_registers_and_completes_no_lost_wakeup() {
    start_strand_recording();
    let strand = next_strand();
    let pair = SockPair::new();
    let write_fd = pair.write_end;

    // A peer that feeds two bytes with a gap, so the read leaf observes two
    // DISTINCT fd-readiness fires (byte 1, then — after the leaf has already
    // re-parked — byte 2). This simulates the foreign peer; it is NOT a
    // per-read worker (the reactor is still single-threaded — the read leaf
    // polls only on the block_on thread).
    let feeder = std::thread::spawn(move || {
        std::thread::sleep(Duration::from_millis(30));
        // SAFETY: `write_fd` is the live write end of the socketpair.
        unsafe { libc::send(write_fd, [1u8].as_ptr() as *const c_void, 1, 0) };
        std::thread::sleep(Duration::from_millis(70));
        unsafe { libc::send(write_fd, [1u8].as_ptr() as *const c_void, 1, 0) };
    });

    let result = block_on_reactor(async |env| {
        let host = env.host;
        let mut st = TwoFireReadState {
            result: 0,
            fd: pair.read_end,
            bytes_seen: 0,
        };
        let leaf = unsafe {
            EffectPoll::new(
                &mut st as *mut _ as *mut c_void,
                two_fire_read_pollfn,
                host,
                strand,
            )
        };
        leaf.await
    })
    .expect("reactor");

    feeder.join().expect("feeder thread");

    assert_eq!(result, 2, "the leaf completed only after BOTH bytes (two fires)");

    // The leaf must have SUSPENDED at least twice (it returned `Pending` after
    // the first fire too) and RESUMED each time — the direct evidence that the
    // second wakeup was not lost.
    let events = drain_strand_events();
    let suspends = events
        .iter()
        .filter(|e| **e == StrandEvent::EffectSuspended { strand })
        .count();
    let resumes = events
        .iter()
        .filter(|e| **e == StrandEvent::EffectResumed { strand })
        .count();
    assert!(
        suspends >= 2,
        "leaf must park at least twice (Pending after the first fire), saw {suspends}"
    );
    assert!(
        resumes >= 2,
        "leaf must be re-woken at least twice (no lost wakeup), saw {resumes}"
    );
}

// ===========================================================================
// Slice 3 — the token-capacity `Semaphore` pool (§2.8 / arch §8.1/§8.2).
//
// These drive the `TokenPool` / `AcquirePermit` / `Permit` directly (the test
// module sees the parent module's private items), manually polling with a noop
// context so a parked acquire can be observed WITHOUT hanging.
// ===========================================================================

use std::future::Future as _Future;
use std::pin::Pin as _Pin;
use std::task::{Context as _Context, Poll as _Poll};

/// Poll an `Unpin` future once with a noop waker — `Ready(v)` or `Pending`.
fn poll_once<F: _Future + Unpin>(f: &mut F) -> _Poll<F::Output> {
    let waker = futures::task::noop_waker();
    let mut cx = _Context::from_waker(&waker);
    _Pin::new(f).poll(&mut cx)
}

// spec: design/int/reactor.md §2.8 / §2.9 (the `AcquirePermit` seam) — a pool
// keyed by token, each slot sized from the node-read `capacity`: capacity-N ⇒ N
// acquires return `Ready`, the (N+1)th `Pending` until a `Permit` drops. Distinct
// tokens have independent slots.
#[test]
fn semaphore_pool_keyed_by_token_sized_from_node_capacity() {
    let pool = TokenPool::new();

    // Token 7, capacity 2: two acquires succeed, the third parks.
    let mut a1 = pool.acquire(7, 2, StrandId(1));
    let mut a2 = pool.acquire(7, 2, StrandId(2));
    let mut a3 = pool.acquire(7, 2, StrandId(3));
    let p1 = match poll_once(&mut a1) {
        _Poll::Ready(p) => p,
        _Poll::Pending => panic!("1st acquire on a capacity-2 token must be Ready"),
    };
    let _p2 = match poll_once(&mut a2) {
        _Poll::Ready(p) => p,
        _Poll::Pending => panic!("2nd acquire on a capacity-2 token must be Ready"),
    };
    assert!(
        matches!(poll_once(&mut a3), _Poll::Pending),
        "the 3rd (capacity+1) acquire on a full token must PARK (Pending)"
    );

    // A DISTINCT token has its own slot — not blocked by token 7 being full.
    let mut b1 = pool.acquire(9, 1, StrandId(4));
    assert!(
        matches!(poll_once(&mut b1), _Poll::Ready(_)),
        "a distinct token's pool is independent — acquire must be Ready"
    );

    // Release one permit on token 7 ⇒ the parked 3rd acquires.
    drop(p1);
    assert!(
        matches!(poll_once(&mut a3), _Poll::Ready(_)),
        "after a permit frees, the parked acquire must become Ready"
    );

    // token 0 ⇒ unrestricted: always Ready, regardless of any pool state.
    let mut z = pool.acquire(0, 1, StrandId(5));
    assert!(
        matches!(poll_once(&mut z), _Poll::Ready(_)),
        "token 0 is unrestricted — acquire is always immediately Ready"
    );
}

// spec: design/int/reactor.md §2.8 / §3 (token-pool strand events) — capacity-N
// parking is observable in the strand stream: the (N+1)th effect emits
// `TokenParked`, then `TokenAcquired` when a permit frees (the resume), and the
// releaser emits `TokenReleased`.
#[test]
fn capacity_n_park_resume_recorded_in_strand_stream() {
    start_strand_recording();
    let pool = TokenPool::new();

    // Capacity 1 on token 5: the 2nd acquire parks, then resumes on release.
    let mut a1 = pool.acquire(5, 1, StrandId(1));
    let mut a2 = pool.acquire(5, 1, StrandId(2));
    let p1 = match poll_once(&mut a1) {
        _Poll::Ready(p) => p,
        _Poll::Pending => panic!("1st acquire must be Ready"),
    };
    assert!(matches!(poll_once(&mut a2), _Poll::Pending), "2nd must park");
    drop(p1); // release ⇒ wake the parked waiter
    assert!(
        matches!(poll_once(&mut a2), _Poll::Ready(_)),
        "parked acquire resumes after release"
    );

    let events = drain_strand_events();
    let strand2 = StrandId(2);
    // The parked strand parked then acquired (resumed); the releaser released.
    let parked_at = events
        .iter()
        .position(|e| *e == StrandEvent::TokenParked { strand: strand2, token: 5 });
    let acquired_at = events
        .iter()
        .position(|e| *e == StrandEvent::TokenAcquired { strand: strand2, token: 5 });
    assert!(parked_at.is_some(), "the (N+1)th effect must record TokenParked: {events:?}");
    assert!(
        acquired_at.is_some(),
        "the parked effect must record TokenAcquired on resume: {events:?}"
    );
    assert!(
        parked_at < acquired_at,
        "TokenParked must precede the resuming TokenAcquired: {events:?}"
    );
    assert!(
        events.contains(&StrandEvent::TokenReleased { strand: StrandId(1), token: 5 }),
        "the releaser must record TokenReleased: {events:?}"
    );
}

// spec: design/int/reactor.md §2.8 (reconciliation) / arch §8.1 — same token,
// different capacity ⇒ FIRST-WRITER-WINS: the slot is sized by the value that
// created it (never resized), and a `TokenCapacityMismatch` strand event records
// the disagreement (NOT an abort, NOT a max).
#[test]
fn same_token_conflicting_capacity_first_writer_wins_and_records_event() {
    start_strand_recording();
    let pool = TokenPool::new();

    // First writer sizes token 3 to capacity 1.
    let mut a1 = pool.acquire(3, 1, StrandId(1));
    let p1 = match poll_once(&mut a1) {
        _Poll::Ready(p) => p,
        _Poll::Pending => panic!("first acquire sizes + grants"),
    };

    // A later, DISAGREEING capacity (5) must NOT resize the pool: the slot is
    // still capacity 1, so this second acquire PARKS (it would be Ready if the
    // pool had been resized to 5).
    let mut a2 = pool.acquire(3, 5, StrandId(2));
    assert!(
        matches!(poll_once(&mut a2), _Poll::Pending),
        "first-writer-wins: capacity stays 1, so the 2nd acquire parks (NOT resized to 5)"
    );

    let events = drain_strand_events();
    assert!(
        events.contains(&StrandEvent::TokenCapacityMismatch {
            strand: StrandId(2),
            token: 3,
            first_capacity: 1,
            requested_capacity: 5,
        }),
        "a same-token capacity disagreement must record TokenCapacityMismatch \
         (first=1, requested=5): {events:?}"
    );

    drop(p1);
    let _ = poll_once(&mut a2); // drain (now Ready) — no assertion needed.
}

// ===========================================================================
// I1 — the no-progress cap is held off while a blocking branch is in flight.
//
// `MAX_TOTAL_BLOCK` is a no-progress backstop for a genuinely-stuck poll leaf,
// NOT a cap on total drive time. A legitimately slow blocking I/O branch on
// rayon (the wakeable bridge) must run UNCAPPED — matching feature-off — because
// `pending_bridges > 0` holds the deadline off. The backstop is still preserved
// for a never-completing poll leaf with no bridge pending.
// ===========================================================================

/// A poll-fn that NEVER completes but re-arms a short timer on every `Pending`,
/// so the reactor turns quickly (a few ms per turn) and the no-progress cap is
/// reached promptly. Used to prove the backstop still fires for a stuck leaf
/// WITHOUT a 5s `MAX_TURN_BLOCK` wait.
#[repr(C)]
struct NeverReadyState {
    /// FIRST field ⇒ the generic result slot (never written — this leaf never
    /// returns `Ready`).
    result: i64,
}

unsafe extern "C" fn never_ready_short_timer_pollfn(
    _state: *mut c_void,
    host: *const HostCtx,
    waker: *const CWaker,
) -> CPoll {
    // Re-arm a ~5ms timer on every poll and always park. A fresh heap entry per
    // poll is fine for a bounded test run (cap/5ms ≈ a handful of entries).
    let hc = unsafe { &*host };
    let deadline = monotonic_nanos() + 5 * 1_000_000;
    unsafe { (hc.register_timer)(hc.host, deadline, waker) };
    CPoll::Pending
}

// spec: design/int/reactor.md §2.6 — blocking I/O is uncapped by design. A
// blocking branch whose rayon work OUTLASTS the no-progress cap still completes
// (no panic), because `pending_bridges > 0` resets the no-progress deadline on
// every turn while the bridge is outstanding. This is the feature-on ≥
// feature-off thesis: feature-off runs such a branch uncapped, so feature-on must
// too.
#[test]
fn cap_held_off_while_blocking_bridge_in_flight() {
    // A cap far SHORTER than the branch's rayon work: with the old fixed-anchor
    // cap this would panic at ~80ms; with the I1 fix it completes at ~240ms.
    let cap = Duration::from_millis(80);
    let work = Duration::from_millis(240); // ~3× the cap

    let start = Instant::now();
    let result = block_on_reactor_capped(
        async |env| {
            // Mirror `run_blocking_branch`: bump the bridge counter, offload to
            // rayon across the wakeable `oneshot`, await, then drop the counter.
            let (tx, rx) = futures::channel::oneshot::channel::<i64>();
            env.pending_bridges.set(env.pending_bridges.get() + 1);
            rayon::spawn(move || {
                std::thread::sleep(work);
                let _ = tx.send(42);
            });
            let v = rx.await.unwrap_or(-1);
            env.pending_bridges.set(env.pending_bridges.get() - 1);
            v
        },
        cap,
    )
    .expect("reactor");

    assert_eq!(
        result, 42,
        "a blocking branch outlasting the cap must still complete (uncapped while a bridge is pending)"
    );
    assert!(
        start.elapsed() >= work - Duration::from_millis(40),
        "the drive genuinely waited for the slow branch (~{work:?}), not the cap"
    );
}

// spec: design/int/reactor.md §2.6 — the backstop is PRESERVED. A poll leaf that
// never completes with NO blocking bridge pending still trips the no-progress cap
// (panics), so a genuine hang surfaces as a panic rather than wedging forever.
#[test]
#[should_panic(expected = "leaf never completed")]
fn cap_still_trips_for_stuck_poll_leaf_no_bridge() {
    let cap = Duration::from_millis(80);
    let strand = next_strand();
    let _ = block_on_reactor_capped(
        async |env| {
            let host = env.host;
            let mut st = NeverReadyState { result: 0 };
            // pending_bridges stays 0 throughout: this is the genuinely-stuck
            // case the backstop exists for.
            let leaf = unsafe {
                EffectPoll::new(
                    &mut st as *mut _ as *mut c_void,
                    never_ready_short_timer_pollfn,
                    host,
                    strand,
                )
            };
            leaf.await
        },
        cap,
    );
}
