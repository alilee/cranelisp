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

// spec: design/int/reactor.md §2.17 + S96 Chunk-C C2-review forward item #1 — a
// parked `AcquirePermit` that was WOKEN (its FIFO entry popped by a `Drop for
// Permit`, which incremented `permits`) but then CANCELLED before re-polling must
// FORWARD the freed permit: pop+wake the NEXT front waiter. Without it the freed
// permit is claimable but the next parked sibling is never pinged → stranded under
// a `FuturesUnordered`-style "only-woken-re-poll" executor (the supervisor, §2.12).
// RED on revert: the pre-fix `Drop` only `retain`-removed its own entry; with the
// entry already popped that is a no-op and B is never woken.
#[test]
fn woken_then_cancelled_acquire_forwards_permit_to_next_waiter() {
    use std::future::Future;
    use std::pin::Pin;
    use std::sync::atomic::{AtomicUsize, Ordering as O};
    use std::sync::Arc;
    use std::task::{Context, Poll, Wake, Waker};

    struct CountWaker(AtomicUsize);
    impl Wake for CountWaker {
        fn wake(self: Arc<Self>) {
            self.0.fetch_add(1, O::SeqCst);
        }
        fn wake_by_ref(self: &Arc<Self>) {
            self.0.fetch_add(1, O::SeqCst);
        }
    }
    fn poll_with<F: Future + Unpin>(f: &mut F, w: &Waker) -> Poll<F::Output> {
        let mut cx = Context::from_waker(w);
        Pin::new(f).poll(&mut cx)
    }

    let pool = TokenPool::new();
    // Capacity 1 on token 5: the holder takes the only permit.
    let mut holder = pool.acquire(5, 1, StrandId(1));
    let permit = match poll_once(&mut holder) {
        _Poll::Ready(p) => p,
        _Poll::Pending => panic!("the first acquire on a capacity-1 token must be Ready"),
    };

    // Park A (front) then B (behind), each with its OWN counting waker.
    let a_w = Arc::new(CountWaker(AtomicUsize::new(0)));
    let b_w = Arc::new(CountWaker(AtomicUsize::new(0)));
    let a_waker = Waker::from(a_w.clone());
    let b_waker = Waker::from(b_w.clone());
    let mut a = pool.acquire(5, 1, StrandId(2));
    let mut b = pool.acquire(5, 1, StrandId(3));
    assert!(
        matches!(poll_with(&mut a, &a_waker), Poll::Pending),
        "A parks on the full token"
    );
    assert!(
        matches!(poll_with(&mut b, &b_waker), Poll::Pending),
        "B parks behind A"
    );

    // Release the holder ⇒ pop+wake the FRONT waiter A (permits → 1). A is woken
    // but NOT re-polled.
    drop(permit);
    assert_eq!(
        a_w.0.load(O::SeqCst),
        1,
        "the release wakes the front waiter A"
    );
    assert_eq!(b_w.0.load(O::SeqCst), 0, "B is not yet woken");

    // A is CANCELLED (dropped) before claiming the freed permit ⇒ the forwarding
    // fix pops+wakes B.
    drop(a);
    assert_eq!(
        b_w.0.load(O::SeqCst),
        1,
        "a woken-then-cancelled acquire must FORWARD the freed permit to the next \
         waiter B (lost-wakeup otherwise)"
    );

    // B can now acquire the forwarded (freed) permit.
    assert!(
        matches!(poll_with(&mut b, &b_waker), Poll::Ready(_)),
        "B acquires the forwarded permit"
    );
}

// spec: design/int/reactor.md §2.16 + S96 Chunk-C C2-review forward item #2 — the
// `RegistrantGuard` clears `Reactor::current_registrant` on drop, so a poll-fn
// panic mid-`EffectPoll::poll` cannot leak a stale registrant tag onto the next
// leaf's fd/timer registrations. A null guard is a no-op (no deref).
#[test]
fn registrant_guard_clears_current_registrant_on_drop() {
    let mut reactor = Reactor::new().expect("reactor construction");
    let r_ptr: *mut Reactor = &mut reactor;
    // SAFETY: `r_ptr` is the live local reactor; single-threaded test.
    unsafe { (*r_ptr).current_registrant = Some(7) };
    drop(RegistrantGuard(r_ptr));
    assert_eq!(
        unsafe { (*r_ptr).current_registrant },
        None,
        "the guard's Drop must clear current_registrant (the panic-safe bracket)"
    );
    // A null guard must be an inert no-op (it must not dereference null).
    drop(RegistrantGuard(std::ptr::null_mut()));
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
        crate::reactor::DriveMode::OneShot,
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
        crate::reactor::DriveMode::OneShot,
        cap,
    );
}

// ===========================================================================
// FIXME 0479 (§8.3) — the structural armed-ness deadlock detector vs the backstop.
//
// The pre-existing liveness units above cover only the SECONDARY wall-clock backstop
// (an armed-but-never-readies leaf). These two cover the PRIMARY structural predicate
// (`reactor_is_armed`, §8.2): the §8.3-mandated pair — an unarmed `Pending` trips it
// immediately; an armed fd does NOT (it falls through to the backstop instead).
// ===========================================================================

/// A poll-fn that returns `Pending` and arms NOTHING (no fd, no timer) — the
/// structural-deadlock shape the §8.2 armed-ness detector must catch immediately.
unsafe extern "C" fn unarmed_pending_pollfn(
    _state: *mut c_void,
    _host: *const HostCtx,
    _waker: *const CWaker,
) -> CPoll {
    CPoll::Pending
}

// spec: design/int/reactor.md §8.3 — the structural armed-ness deadlock detector
// (`reactor_is_armed`, §8.2) trips IMMEDIATELY on a `Pending` top future that armed
// NOTHING (no fd/timer waiter, no bridge, no supervised strand, no parked permit) — a
// true deadlock nothing can ever wake. It fires WITHOUT waiting the wall-clock
// backstop: the 30s backstop below would hang the test if the detector did not fire
// first, so a fast panic proves the immediate structural trip. This is the PRIMARY
// liveness rule, distinct from the secondary armed-but-never-readies backstop the
// units above cover.
#[test]
#[should_panic(expected = "no armed interest")]
fn armed_ness_detector_trips_immediately_on_unarmed_pending() {
    let strand = next_strand();
    let _ = block_on_reactor_capped(
        async |env| {
            let host = env.host;
            let mut st = NeverReadyState { result: 0 };
            let leaf = unsafe {
                EffectPoll::new(
                    &mut st as *mut _ as *mut c_void,
                    unarmed_pending_pollfn,
                    host,
                    strand,
                )
            };
            leaf.await
        },
        crate::reactor::DriveMode::OneShot,
        Duration::from_secs(30),
    );
}

// spec: design/int/reactor.md §8.3 — an ARMED leaf (an fd waiter) must NOT trip the
// structural armed-ness detector: `reactor_is_armed` is true (`has_waiters`), so the
// drive keeps turning and the leaf falls through to the SECONDARY wall-clock backstop
// (a short one here) instead. This proves the detector distinguishes "armed but not
// ready" (a legitimate park) from "armed nothing" (immediate deadlock) — the pairing
// §8.3 mandates. Contrast the unarmed leaf above (panics `no armed interest`); this
// armed one reaches the `OneShot backstop`. RED contrast: were the armed-ness
// predicate wrong (always-false), this would flip to the `no armed interest` panic.
#[test]
#[should_panic(expected = "OneShot backstop exceeded")]
fn armed_fd_leaf_does_not_trip_detector_reaches_backstop() {
    let strand = next_strand();
    // A non-blocking read end that is never fed: the leaf arms `register_readable`
    // and parks (armed, but never readies). `pair` (has a `Drop`) stays alive to the
    // end of scope, so the fd is valid across the whole drive.
    let pair = SockPair::new();
    let read_fd = pair.read_end;
    let _ = block_on_reactor_capped(
        async |env| {
            let host = env.host;
            let mut st = AsyncReadState { result: 0, fd: read_fd, registered: false };
            let leaf = unsafe {
                EffectPoll::new(
                    &mut st as *mut _ as *mut c_void,
                    async_read_pollfn,
                    host,
                    strand,
                )
            };
            leaf.await
        },
        crate::reactor::DriveMode::OneShot,
        Duration::from_millis(60),
    );
}

// ===========================================================================
// S97 ABI v9 — the ctx-vtable handle model: the platform poll-fn acquires its own
// token permit via `ctx.acquire`; the host keys held permits by the effect's
// identity (its RegId) and OWNS release (eager on `Ready`, on drop = cancel). These
// tests exercise the host-side `acquire_permit` / `release_all` / `retire_token`
// mechanism (`reactor.md §7.2/§7.3`) directly, plus an end-to-end Consume leaf that
// drives `ctx.acquire` through `EffectPoll`.
// design: design/int/reactor.md §7
// ===========================================================================

/// A v9 reactor wired to a fresh `TokenPool` (the `host_acquire`/`host_retire`
/// callbacks take/return permits against it) + the pool handle for slot inspection.
fn v9_reactor_with_pool() -> (Reactor, std::rc::Rc<TokenPool>) {
    let mut r = Reactor::new().expect("reactor");
    let pool = TokenPool::new();
    r.set_pool(std::rc::Rc::clone(&pool));
    (r, pool)
}

/// A reusable C-ABI waker over a std no-op waker (its `data` is a boxed
/// `std::task::Waker`, exactly what `acquire_permit`'s park path recovers + clones).
fn v9_cabi_waker() -> CWaker {
    make_cabi_waker(futures::task::noop_waker())
}

/// Free permits remaining on `token`'s slot (`None` ⇒ the slot was never created or
/// was retired). Reads the host pool's private map directly (child-module access).
fn slot_permits(pool: &std::rc::Rc<TokenPool>, token: u64) -> Option<u32> {
    pool.slots.borrow().get(&token).map(|s| s.permits)
}

/// A v9 **Consume** poll leaf: it reads its own `(token, capacity)` from the env and
/// calls `ctx.acquire(token, capacity, waker)` ITSELF (the ctx-vtable skeleton) —
/// `Parked` ⇒ `Pending`; then parks `polls_left` times before writing its result and
/// returning `Ready`. The host releases the permit on `Ready` / drop.
#[repr(C)]
struct CtxAcquireState {
    result: i64,
    token: i64,
    capacity: i64,
    polls_left: i64,
}

unsafe extern "C" fn ctx_acquire_pollfn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const CWaker,
) -> CPoll {
    let st = unsafe { &mut *(state as *mut CtxAcquireState) };
    let hc = unsafe { &*host };
    // Skeleton step 1: acquire the projected token permit (idempotent per re-poll).
    if st.token != 0
        && matches!(
            unsafe { (hc.acquire)(hc.host, st.token as u64, st.capacity as u32, waker) },
            CAcquire::Parked
        )
    {
        return CPoll::Pending;
    }
    if st.polls_left > 0 {
        st.polls_left -= 1;
        return CPoll::Pending;
    }
    st.result = 99;
    CPoll::Ready
}

/// Acquire a permit from `pool` synchronously (poll once with a noop waker — the
/// first acquire on a free slot resolves `Ready` immediately). Used by the
/// `TokenPool`-direct pool tests + the backpressure section below.
fn acquire_now(pool: &std::rc::Rc<TokenPool>, token: u64, capacity: u32, strand: StrandId) -> Permit {
    let mut a = pool.acquire(token, capacity, strand);
    match poll_once(&mut a) {
        _Poll::Ready(p) => p,
        _Poll::Pending => panic!("acquire on a free slot must be Ready"),
    }
}

// spec: design/int/reactor.md §7.2/§7.3 — a v9 Consume leaf acquires its OWN token
// permit via `ctx.acquire`, the host HOLDS it across the whole establish→Pending→
// …→Ready arc (a re-poll's re-`acquire` is idempotent — no 2nd permit), and the host
// RELEASES it eagerly on `Ready`. Observed by the token's slot permit count.
#[test]
fn v9_consume_leaf_acquires_holds_releases_on_ready() {
    let (mut reactor, pool) = v9_reactor_with_pool();
    let rptr: *mut Reactor = &mut reactor;
    // SAFETY: single-threaded test; `host` holds the raw ptr, no live `&mut reactor`.
    let host = make_host_ctx(rptr);

    // Token 7, capacity 1; parks twice (establish + one resume) before Ready.
    let mut st = CtxAcquireState { result: 0, token: 7, capacity: 1, polls_left: 2 };
    let mut leaf =
        unsafe { EffectPoll::new(&mut st as *mut _ as *mut c_void, ctx_acquire_pollfn, &host, StrandId(1)) };

    // Poll #1: the leaf acquires token 7 → the slot's single permit is held (0 free).
    assert!(matches!(poll_once(&mut leaf), _Poll::Pending), "establish (Pending)");
    assert_eq!(slot_permits(&pool, 7), Some(0), "the Consume leaf acquired its token permit");
    // Poll #2: a re-poll re-`acquire`s — idempotent, NO second permit consumed.
    assert!(matches!(poll_once(&mut leaf), _Poll::Pending), "resume (still Pending)");
    assert_eq!(slot_permits(&pool, 7), Some(0), "re-acquire is idempotent — still exactly one permit held");
    // Poll #3 → Ready: the host releases the permit eagerly (before TaskPoll::Ready).
    assert!(matches!(poll_once(&mut leaf), _Poll::Ready(99)), "leaf reaches Ready");
    assert_eq!(slot_permits(&pool, 7), Some(1), "permit released eagerly on Ready");
}

// spec: design/int/reactor.md §7.3 — cancellation = future drop. A still-Pending
// Consume leaf that acquired its permit and is DROPPED mid-flight (race-lost /
// timed-out) has the host release that permit via the `EffectPoll`'s identity-keyed
// release-guard (`ReactorInterest::drop` → `release_all(reg)`) — no leak, and cancel
// never re-enters the poll-fn.
#[test]
fn v9_dropping_inflight_consume_releases_permit() {
    let (mut reactor, pool) = v9_reactor_with_pool();
    let rptr: *mut Reactor = &mut reactor;
    let host = make_host_ctx(rptr);

    {
        // Never-Ready leaf (huge polls_left) that acquires token 11.
        let mut st = CtxAcquireState { result: 0, token: 11, capacity: 1, polls_left: i64::MAX };
        let mut leaf =
            unsafe { EffectPoll::new(&mut st as *mut _ as *mut c_void, ctx_acquire_pollfn, &host, StrandId(1)) };
        assert!(matches!(poll_once(&mut leaf), _Poll::Pending), "leaf parked, holding the permit");
        assert_eq!(slot_permits(&pool, 11), Some(0), "permit held while parked");
        // DROP the future mid-flight (no Ready) — the release-guard fires.
    }
    assert_eq!(
        slot_permits(&pool, 11),
        Some(1),
        "dropping the in-flight Consume released its permit via the identity-keyed guard (no leak)"
    );
}

// spec: design/int/reactor.md §7.2 — `acquire` is idempotent per in-flight effect
// (a re-acquire on a token the effect already holds does NOT consume a 2nd permit),
// and a DIFFERENT effect on a full capacity-1 token PARKS. A later `release_all`
// frees it so the parked effect can acquire.
#[test]
fn v9_acquire_idempotent_per_effect_and_parks_second() {
    let (mut reactor, pool) = v9_reactor_with_pool();
    let w = v9_cabi_waker();
    let wp = &w as *const CWaker;

    // Effect 1 acquires token 7 (cap 1), then re-acquires — idempotent.
    reactor.current_registrant = Some(1);
    assert!(matches!(unsafe { reactor.acquire_permit(7, 1, wp) }, CAcquire::Acquired), "effect 1 acquires");
    assert!(matches!(unsafe { reactor.acquire_permit(7, 1, wp) }, CAcquire::Acquired), "idempotent re-acquire");
    assert_eq!(slot_permits(&pool, 7), Some(0), "exactly one permit consumed (idempotent)");

    // Effect 2 on the same full token → Parked.
    reactor.current_registrant = Some(2);
    assert!(matches!(unsafe { reactor.acquire_permit(7, 1, wp) }, CAcquire::Parked), "2nd effect parks on a full token");

    // token 0 is unrestricted (no map entry).
    assert!(matches!(unsafe { reactor.acquire_permit(0, 1, wp) }, CAcquire::Acquired), "token 0 unrestricted");

    // Release effect 1 → frees the slot; effect 2 re-acquires.
    reactor.release_all(1);
    assert_eq!(slot_permits(&pool, 7), Some(1), "released by effect 1");
    reactor.current_registrant = Some(2);
    assert!(matches!(unsafe { reactor.acquire_permit(7, 1, wp) }, CAcquire::Acquired), "the parked effect now acquires");
}

// spec: design/int/reactor.md §7.6 / §3.1 — the SINGLETON resource (`read-line`)
// acquires a manifest-static token at capacity 1, so a SECOND concurrent acquirer on
// that token PARKS — single-in-flight by construction (no value, no header).
#[test]
fn v9_singleton_token_single_in_flight() {
    let (mut reactor, _pool) = v9_reactor_with_pool();
    let w = v9_cabi_waker();
    let wp = &w as *const CWaker;
    const STDIN_TOKEN: u64 = 0x5144_4E49_5453; // any fixed non-zero manifest-static token

    reactor.current_registrant = Some(1);
    assert!(matches!(unsafe { reactor.acquire_permit(STDIN_TOKEN, 1, wp) }, CAcquire::Acquired), "first read-line acquires");
    reactor.current_registrant = Some(2);
    assert!(
        matches!(unsafe { reactor.acquire_permit(STDIN_TOKEN, 1, wp) }, CAcquire::Parked),
        "a second concurrent read-line parks — single-in-flight stdin by construction"
    );
}

// spec: design/int/reactor.md §7.2 — `retire` drops the token's permit pool (a
// Retire/`close` leaf calls `ctx.retire` after `close(r)`). Idempotent; a later
// acquire on that token re-creates a fresh slot.
#[test]
fn v9_retire_drops_token_pool() {
    let (mut reactor, pool) = v9_reactor_with_pool();
    let w = v9_cabi_waker();
    let wp = &w as *const CWaker;

    reactor.current_registrant = Some(1);
    assert!(matches!(unsafe { reactor.acquire_permit(9, 1, wp) }, CAcquire::Acquired), "acquire token 9");
    assert!(slot_permits(&pool, 9).is_some(), "slot exists after acquire");

    reactor.retire_token(9);
    assert_eq!(slot_permits(&pool, 9), None, "retire dropped the token's pool");
    reactor.retire_token(9); // idempotent — a double-close is a no-op.

    // A later acquire on the retired token re-creates a fresh slot.
    reactor.current_registrant = Some(2);
    assert!(matches!(unsafe { reactor.acquire_permit(9, 1, wp) }, CAcquire::Acquired), "fresh slot after retire");
}

// spec: design/int/reactor.md §7.3 — release-exactly-once: after an eager `Ready`
// release removed the effect's ledger entry, the drop-path `release_all` is a no-op
// (no double-release). Modelled directly: `release_all` twice for one effect credits
// the slot exactly once.
#[test]
fn v9_release_exactly_once_no_double_release() {
    let (mut reactor, pool) = v9_reactor_with_pool();
    let w = v9_cabi_waker();
    let wp = &w as *const CWaker;

    reactor.current_registrant = Some(1);
    assert!(matches!(unsafe { reactor.acquire_permit(17, 1, wp) }, CAcquire::Acquired), "acquire token 17");
    assert_eq!(slot_permits(&pool, 17), Some(0), "permit held");

    reactor.release_all(1); // the eager-on-Ready release
    assert_eq!(slot_permits(&pool, 17), Some(1), "released once");
    reactor.release_all(1); // the drop-path release — a NO-OP (ledger entry already gone)
    assert_eq!(slot_permits(&pool, 17), Some(1), "no double-release: the slot was credited exactly once");
}

// spec: design/int/reactor.md §2.9 §1A — two distinct poll-shape effect "kinds"
// on the SAME token of capacity N draw from ONE `Semaphore(N)` (capacity attaches
// to the token, not the effect kind): N acquire, the (N+1)th parks. `token == 0`
// ⇒ no acquire (the inert permit, no map entry). (`TokenPool`-direct; carrier-agnostic.)
// design: design/int/reactor.md §2.8
#[test]
fn poll_effects_sharing_one_token_draw_from_one_pool() {
    let pool = TokenPool::new();

    // Two distinct poll effect kinds (modelled as two acquires) on token 4,
    // capacity 2: both succeed from the ONE shared slot.
    let _k1 = acquire_now(&pool, 4, 2, StrandId(1));
    let _k2 = acquire_now(&pool, 4, 2, StrandId(2));

    // A third on the same token — regardless of "kind" — parks (sum-in-flight ≤ N
    // across both kinds; a per-kind pool would wrongly admit it).
    let mut k3 = pool.acquire(4, 2, StrandId(3));
    assert!(matches!(poll_once(&mut k3), _Poll::Pending), "the 3rd on a shared capacity-2 token parks (one shared pool, not per-kind)");

    // token 0 ⇒ unrestricted: no acquire, always Ready, independent of any slot.
    let mut z = pool.acquire(0, 2, StrandId(4));
    assert!(matches!(poll_once(&mut z), _Poll::Ready(_)), "token 0 is unrestricted on the poll carrier — no acquire");
}

// spec: design/int/reactor.md §2.8 / arch §8.1 — first-writer-wins on the shared
// pool: two effects on one token declaring different capacities ⇒ the slot is sized
// by the FIRST writer (never resized, never silent-max), and a `TokenCapacityMismatch`
// strand event records the disagreement.
// design: design/int/reactor.md §2.8
#[test]
fn poll_same_token_conflicting_capacity_first_writer_wins_and_records_event() {
    start_strand_recording();
    let pool = TokenPool::new();

    // First effect sizes token 6 to capacity 2.
    let _p1 = acquire_now(&pool, 6, 2, StrandId(1));
    let _p2 = acquire_now(&pool, 6, 2, StrandId(2)); // 2nd permit of the 2 — slot now full

    // A second effect declares a DISAGREEING capacity (5). First-writer-wins: the
    // slot stays capacity 2 (full), so this acquire PARKS (it would be Ready if the
    // pool had been resized to 5).
    let mut p3 = pool.acquire(6, 5, StrandId(3));
    assert!(matches!(poll_once(&mut p3), _Poll::Pending), "first-writer-wins: capacity stays 2 (not resized to 5), so the 3rd parks");

    let events = drain_strand_events();
    assert!(
        events.contains(&StrandEvent::TokenCapacityMismatch {
            strand: StrandId(3),
            token: 6,
            first_capacity: 2,
            requested_capacity: 5,
        }),
        "a same-token capacity disagreement must record TokenCapacityMismatch (first=2, requested=5): {events:?}"
    );
}

// ===========================================================================
// S96 Chunk B §2.13 — backpressure: degree throttle + global admission budget.
// design: design/int/reactor.md §2.13
// ===========================================================================

// spec: design/int/reactor.md §2.13 part 1 / spec/10-io.md §10.12.4.2 item 1 — the
// program `degree` throttles a token's effective in-flight limit to
// `min(node_capacity, degree)`: under degree d < N a capacity-N token admits only
// d (the (d+1)th parks). It can only TIGHTEN.
// design: design/int/reactor.md §2.13
#[test]
fn degree_throttles_token_slot_to_min_capacity_degree() {
    // degree 2 < node capacity 5 ⇒ effective 2: two acquire, the 3rd parks.
    let pool = TokenPool::with_degree(2);
    let mut a1 = pool.acquire(5, 5, StrandId(1));
    let mut a2 = pool.acquire(5, 5, StrandId(2));
    let mut a3 = pool.acquire(5, 5, StrandId(3));
    let _p1 = match poll_once(&mut a1) {
        _Poll::Ready(p) => p,
        _Poll::Pending => panic!("1st acquire under degree 2 must be Ready"),
    };
    let _p2 = match poll_once(&mut a2) {
        _Poll::Ready(p) => p,
        _Poll::Pending => panic!("2nd acquire under degree 2 must be Ready"),
    };
    assert!(
        matches!(poll_once(&mut a3), _Poll::Pending),
        "degree 2 throttles a capacity-5 token to 2 in flight — the 3rd parks (min(5,2)=2)"
    );
}

// spec: design/int/reactor.md §2.13 part 1 / spec/10-io.md §10.12.4.2 item 2 — a
// degree ABOVE a token's capacity has no extra effect: capacity still binds
// (`min(N, D) = N`). Degree never loosens past the platform ceiling.
// design: design/int/reactor.md §2.13
#[test]
fn degree_above_capacity_capacity_still_binds() {
    // degree 5 > node capacity 2 ⇒ effective 2: capacity binds, the 3rd parks.
    let pool = TokenPool::with_degree(5);
    let mut a1 = pool.acquire(9, 2, StrandId(1));
    let mut a2 = pool.acquire(9, 2, StrandId(2));
    let mut a3 = pool.acquire(9, 2, StrandId(3));
    let _p1 = match poll_once(&mut a1) {
        _Poll::Ready(p) => p,
        _Poll::Pending => panic!("1st on capacity-2 token must be Ready"),
    };
    let _p2 = match poll_once(&mut a2) {
        _Poll::Ready(p) => p,
        _Poll::Pending => panic!("2nd on capacity-2 token must be Ready"),
    };
    assert!(
        matches!(poll_once(&mut a3), _Poll::Pending),
        "degree 5 above capacity 2 ⇒ capacity binds (min(2,5)=2): the 3rd parks"
    );
}

// spec: design/int/reactor.md §2.13 part 2 / spec/10-io.md §10.12.4.2 item 3 — the
// global admission budget bounds total in-flight detached strands to the global
// degree D: D global acquires succeed, the (D+1)th PARKS until one frees
// (saturate-not-oversaturate). Emits the `GlobalBudget*` events (not `Token*`).
// design: design/int/reactor.md §2.13
#[test]
fn global_budget_bounds_inflight_to_degree_nplus1_parks() {
    start_strand_recording();
    let pool = TokenPool::with_degree(2); // global degree D = 2

    let mut g1 = pool.acquire_global(StrandId(1));
    let mut g2 = pool.acquire_global(StrandId(2));
    let mut g3 = pool.acquire_global(StrandId(3));
    let p1 = match poll_once(&mut g1) {
        _Poll::Ready(p) => p,
        _Poll::Pending => panic!("1st global acquire under degree 2 must be Ready"),
    };
    let _p2 = match poll_once(&mut g2) {
        _Poll::Ready(p) => p,
        _Poll::Pending => panic!("2nd global acquire under degree 2 must be Ready"),
    };
    assert!(
        matches!(poll_once(&mut g3), _Poll::Pending),
        "the (D+1)th detached strand parks on the full global budget (saturate-not-oversaturate)"
    );

    // Release one → the parked (D+1)th launch proceeds.
    drop(p1);
    assert!(
        matches!(poll_once(&mut g3), _Poll::Ready(_)),
        "a completing strand frees a global slot ⇒ the parked launch proceeds"
    );

    // The global gate emits the distinct GlobalBudget* events (not Token*).
    let events = drain_strand_events();
    assert!(
        events.contains(&StrandEvent::GlobalBudgetParked { strand: StrandId(3) }),
        "the over-budget launch records GlobalBudgetParked: {events:?}"
    );
    assert!(
        events.contains(&StrandEvent::GlobalBudgetAcquired { strand: StrandId(3) }),
        "the resumed launch records GlobalBudgetAcquired: {events:?}"
    );
    assert!(
        events.contains(&StrandEvent::GlobalBudgetReleased { strand: StrandId(1) }),
        "the releaser records GlobalBudgetReleased: {events:?}"
    );
    // Negative: the global gate must NOT masquerade as a resource-token event.
    assert!(
        !events
            .iter()
            .any(|e| matches!(e, StrandEvent::TokenParked { .. } | StrandEvent::TokenAcquired { .. })),
        "the global budget must emit GlobalBudget* events, NOT Token*: {events:?}"
    );
}

// spec: design/int/reactor.md §2.14 (the A→C volume consumer) — a supervised
// strand OWNS its global-budget `Permit`; dropping the strand (completion /
// shutdown) drops the `Permit`, freeing a global slot so a parked launch proceeds.
// This is the global half of the A→C contract (the per-token half is covered by
// the §2.9 EffectPoll-drop tests above). RAII, no leak.
// design: design/int/reactor.md §2.14
#[test]
fn dropping_global_permit_frees_budget_parked_launch_proceeds() {
    let pool = TokenPool::with_degree(1); // global budget = 1
    let g1 = match poll_once(&mut pool.acquire_global(StrandId(1))) {
        _Poll::Ready(p) => p,
        _Poll::Pending => panic!("the only global permit must be acquirable"),
    };
    let mut g2 = pool.acquire_global(StrandId(2));
    assert!(matches!(poll_once(&mut g2), _Poll::Pending), "the 2nd launch parks behind the held global permit");
    // Drop the permit as a completing/dropped supervised strand would (RAII).
    drop(g1);
    assert!(
        matches!(poll_once(&mut g2), _Poll::Ready(_)),
        "dropping the strand's global permit frees the budget ⇒ the parked launch proceeds (no leak)"
    );
}

// ===========================================================================
// S96 Chunk C C2 — the A3-review cancellation foundations.
//   finding #4 (§2.17): `Drop for AcquirePermit` — stale-waker removal.
//   finding #3 (§2.16): `ReactorInterest` — active fd/timer deregistration.
//   `sleep` (§2.18): the tokenless timer leaf.
// design: design/int/reactor.md §2.16 / §2.17 / §2.18
// ===========================================================================

use std::sync::atomic::{AtomicBool, Ordering as _Ordering};

/// A `Wake` impl that flips a flag — lets a test observe WHICH parked waiter the
/// releaser woke (the finding-#4 lost-wakeup witness).
struct FlagWaker(std::sync::Arc<AtomicBool>);
impl std::task::Wake for FlagWaker {
    fn wake(self: std::sync::Arc<Self>) {
        self.0.store(true, _Ordering::SeqCst);
    }
    fn wake_by_ref(self: &std::sync::Arc<Self>) {
        self.0.store(true, _Ordering::SeqCst);
    }
}

/// Poll an `Unpin` future once with a specific waker (so the parked entry carries
/// THAT waker), returning the outcome.
fn poll_with<F: _Future + Unpin>(f: &mut F, w: &std::task::Waker) -> _Poll<F::Output> {
    let mut cx = _Context::from_waker(w);
    _Pin::new(f).poll(&mut cx)
}

// spec: design/int/reactor.md §2.17 — finding #4: an `AcquirePermit` dropped WHILE
// PARKED removes its OWN stale waker from the slot's FIFO, so a later `Drop for
// Permit`'s front-`pop` wakes the next LIVE waiter — not the stranded one. Without
// `Drop for AcquirePermit` the release pops+wakes the dead waker (a no-op) while the
// live waiter behind it is NEVER woken and the freed permit goes unclaimed
// (lost-wakeup / a free permit nobody can take). We observe the wake directly via
// flag wakers: the LIVE waiter's flag must fire, the stale one's must not.
// design: design/int/reactor.md §2.17
#[test]
fn dropping_parked_acquire_removes_stale_waker_next_live_waiter_woken() {
    let pool = TokenPool::new();

    // Capacity-1 token 7: a1 takes the only permit.
    let p1 = acquire_now(&pool, 7, 1, StrandId(1));

    // The STALE waiter parks FRONT (it will be cancelled); the LIVE waiter parks
    // behind it. Each carries a distinct flag waker.
    let stale_flag = std::sync::Arc::new(AtomicBool::new(false));
    let live_flag = std::sync::Arc::new(AtomicBool::new(false));
    let stale_waker: std::task::Waker = std::sync::Arc::new(FlagWaker(stale_flag.clone())).into();
    let live_waker: std::task::Waker = std::sync::Arc::new(FlagWaker(live_flag.clone())).into();

    let mut stale = pool.acquire(7, 1, StrandId(2));
    let mut live = pool.acquire(7, 1, StrandId(3));
    assert!(matches!(poll_with(&mut stale, &stale_waker), _Poll::Pending), "stale parks front");
    assert!(matches!(poll_with(&mut live, &live_waker), _Poll::Pending), "live parks behind");

    // Cancel the FRONT waiter while parked (drop it). Finding #4: its Drop
    // `retain`-removes its own entry, so the FIFO front becomes the live waiter.
    drop(stale);

    // Release the permit ⇒ the releaser pops+wakes the FRONT. With finding #4 that
    // is the LIVE waiter; without it, the stranded stale waker.
    drop(p1);

    assert!(
        live_flag.load(_Ordering::SeqCst),
        "finding #4: the release must wake the next LIVE waiter (its waker did NOT fire ⇒ lost wakeup)"
    );
    assert!(
        !stale_flag.load(_Ordering::SeqCst),
        "the cancelled waiter's stale waker must NOT be the one woken"
    );
    // And the live waiter actually acquires on re-poll (the permit is claimable).
    assert!(
        matches!(poll_with(&mut live, &live_waker), _Poll::Ready(_)),
        "the woken live waiter acquires the freed permit"
    );
}

// spec: design/int/reactor.md §2.17 — finding #4 on the GLOBAL-budget acquire (the
// shutdown-cancelled accept-loop launch the A3 review asked to co-cover): a parked
// `acquire_global` cancelled while queued behind a full budget removes its own stale
// waker, so the release wakes the next live launch — same machinery, global token.
// design: design/int/reactor.md §2.17
#[test]
fn dropping_parked_global_acquire_removes_stale_waker_co_covers_shutdown() {
    let pool = TokenPool::with_degree(1); // global budget = 1
    let p1 = match poll_once(&mut pool.acquire_global(StrandId(1))) {
        _Poll::Ready(p) => p,
        _Poll::Pending => panic!("the only global permit must be acquirable"),
    };

    let stale_flag = std::sync::Arc::new(AtomicBool::new(false));
    let live_flag = std::sync::Arc::new(AtomicBool::new(false));
    let stale_waker: std::task::Waker = std::sync::Arc::new(FlagWaker(stale_flag.clone())).into();
    let live_waker: std::task::Waker = std::sync::Arc::new(FlagWaker(live_flag.clone())).into();

    let mut stale = pool.acquire_global(StrandId(2));
    let mut live = pool.acquire_global(StrandId(3));
    assert!(matches!(poll_with(&mut stale, &stale_waker), _Poll::Pending), "stale launch parks front");
    assert!(matches!(poll_with(&mut live, &live_waker), _Poll::Pending), "live launch parks behind");

    drop(stale); // shutdown cancels the front parked launch
    drop(p1); // an in-flight strand completes, freeing the global slot

    assert!(
        live_flag.load(_Ordering::SeqCst),
        "the freed global slot must wake the next LIVE launch (no lost wakeup on the global token)"
    );
    assert!(!stale_flag.load(_Ordering::SeqCst), "the cancelled launch's stale waker must not be woken");
}

// spec: design/int/reactor.md §2.16 — finding #3: an in-flight `EffectPoll` that
// armed reactor interest (an fd/timer waiter) and is DROPPED mid-flight (cancelled
// before `Ready`) ACTIVELY deregisters that interest via its `ReactorInterest` field
// drop. Without it the `fd_waiters`/`timer_waiters` entry + mio registration leak
// until the fd next readies (unbounded growth under volume cancellation). We drive a
// REAL reactor (so the interest is live), arm a far-future timer leaf, drop it, and
// assert the reactor's waiter count returns to 0.
// design: design/int/reactor.md §2.16
#[test]
fn dropping_inflight_poll_deregisters_reactor_interest() {
    let strand = next_strand();
    block_on_reactor(async |env| {
        // Raw read handle on the reactor (B1 provenance — read-only here, between
        // operations, no concurrent turn).
        let reactor = env.host.host as *const Reactor;
        let before = unsafe { (*reactor).waiter_count() };

        // A `sleep` leaf with a far-future deadline: first poll arms a timer and
        // parks (never readies during this test).
        let mut st = SleepState {
            result: 0,
            duration_nanos: 60 * 1_000_000_000, // 60s — never fires here
            deadline_nanos: 0,
        };
        {
            let mut leaf = unsafe {
                EffectPoll::new(
                    &mut st as *mut _ as *mut c_void,
                    sleep_pollfn,
                    env.host,
                    strand,
                )
            };
            assert!(matches!(poll_once(&mut leaf), _Poll::Pending), "sleep leaf arms a timer and parks");
            let armed = unsafe { (*reactor).waiter_count() };
            assert_eq!(armed, before + 1, "the parked leaf armed exactly one reactor (timer) interest");
            // Drop the in-flight leaf (cancellation) → ReactorInterest::drop runs.
        }
        let after = unsafe { (*reactor).waiter_count() };
        assert_eq!(
            after, before,
            "finding #3: dropping the in-flight EffectPoll deregistered its reactor interest \
             (waiter map back to {before}; a leak would leave it at {})",
            before + 1
        );
        0
    })
    .expect("reactor");
}

// spec: design/int/reactor.md §2.18 — the `sleep` tokenless timer leaf: arms the
// reactor timer on first poll (Pending → parks), resumes to `Unit` (0) when the
// timer fires. Proves it genuinely PARKS for ≈the duration (not a busy spin) and
// emits the Dispatched→Suspended→Resumed strand trace, reusing the whole EffectPoll
// / timer-turn machinery. This is the leaf `timeout = race io (sleep d)` builds on.
// design: design/int/reactor.md §2.18
#[test]
fn sleep_leaf_parks_for_duration_then_resumes_unit() {
    start_strand_recording();
    let strand = next_strand();
    let delay_ms = 40u64;

    let start = Instant::now();
    let result = block_on_reactor(async |env| {
        let mut st = SleepState {
            result: 0,
            duration_nanos: (delay_ms * 1_000_000) as i64,
            deadline_nanos: 0,
        };
        let leaf = unsafe {
            EffectPoll::new(&mut st as *mut _ as *mut c_void, sleep_pollfn, env.host, strand)
        };
        leaf.await
    })
    .expect("reactor");
    let elapsed = start.elapsed();

    assert_eq!(result, 0, "sleep resolves to Unit (0)");
    assert!(
        elapsed.as_millis() as u64 >= delay_ms - 10,
        "sleep must genuinely PARK until ≈the deadline (no busy spin), got {elapsed:?}"
    );
    let events = drain_strand_events();
    assert_eq!(
        events,
        vec![
            StrandEvent::EffectDispatched { strand },
            StrandEvent::EffectSuspended { strand },
            StrandEvent::EffectResumed { strand },
        ],
        "the sleep leaf suspends on the reactor timer and resumes"
    );
}
