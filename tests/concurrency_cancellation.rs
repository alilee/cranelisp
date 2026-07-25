//! Sprint 96 — effect-concurrency Chunk C: cancellation + combinator layer
//! (`race` / `select` / `timeout` + structured cancellation) — the QA-first
//! (Phase-5 Chunk-C Stage-1, Wave-C1) **synthetic** e2e acceptance rows.
//!
//! Plan: `tests/plan/sprint-96.md` (CHUNK C) §C1 / §C2 / §C3 / §C4 / §C5a.
//! Contract of record: `design/arch/effect-concurrency.md` §9 (the control half —
//! the combinators are ordinary typed functions constructing trampoline-interpreted
//! IO-ADT nodes; `cancel` is the *consequence* of losing a race = drop the future)
//! / §11 (the cancellation observability event). `design/int/reactor.md` (the
//! Chunk-C cancellation interior — finding #3 active fd-interest deregistration +
//! finding #4 `Drop for AcquirePermit` / pop-until-live). Spec of record (landed
//! this Phase by `/spec`):
//!   - `spec/10-io.md`     §10.12.8  (Structured Control Combinators — race/select/timeout)
//!   - `spec/10-io.md`     §10.12.9  (Structured Cancellation)
//!   - `spec/10-io.md`     §10.12.10 (Reference Control Patterns — graceful shutdown)
//!   - `spec/10-io.md`     §10.12.4.1 (Resource Capacity — Token Pools; permit release)
//!   - `spec/12-runtime.md` §12.4.4  (Structured Control Combinators and Cancellation)
//!
//! ## Lane (post-cutover)
//!
//! The single-ABI / single-trampoline cutover (S96) RETIRED the `concurrency` /
//! `concurrency-runtime` features: the host reactor is UNCONDITIONAL (lazy-init).
//! So there is ONE collapsed test lane — `cargo nextest run` — and this file is
//! **un-gated**; it runs in the default lane (the Chunk-B precedent).
//!
//! ## Posture (Wave-C1 = QA-first, the synthetic RED-first acceptance rows)
//!
//! These are **failing-not-ignored** acceptance guards
//! (`memory/feedback_failing_not_ignored`). Per the Chunk-A/B precedent, Wave-C1
//! authors ONLY the black-box e2e rows that compile as Rust and run RED today —
//! the combinator surface (`race` / `select`) and the structured-cancellation
//! semantics are **absent on HEAD**, so each program errors at RUNTIME ("undefined:
//! race" / the loser is not cancelled / the cancelled effect leaks its permit),
//! NOT at compile time (e2e shell out to the `cranelisp` binary). The workspace
//! BUILDS green while these run RED. They flip GREEN as the Chunk-C /dev waves land:
//!   - C2 (reactor cancellation foundations): finding #3 — an `EffectPoll`-owned
//!     reactor-registration handle whose `Drop` deregisters `fd_waiters` /
//!     `timer_waiters` + mio; finding #4 — `Drop for AcquirePermit` /
//!     pop-until-live release (no lost-wakeup when a parked-awaiting-permit future
//!     is cancelled); the new `poll-block` never-readying-fd cancellable leaf
//!     (Gap G10) added to `tests/scripts/build-link-prereqs.sh`.
//!   - C3 (combinator node + runtime): `race` / `select` new in-process IO node
//!     tags + intrinsics (first-`Poll::Ready` ⇒ drop the loser future(s) ⇒ their
//!     RAII `Permit`s + reactor-interest handles release). `timeout` is derived
//!     `.cl` stdlib (`race io (sleep d)`); tests MUST NOT depend on `stdlib/`
//!     (root `CLAUDE.md` §"Stdlib separation"), so the §C3 rows express `timeout`
//!     **inline** as `(race io (poll-read deadline-tok cap d))` — the existing
//!     `poll-pool` `poll-read` IS an armed-timer "sleep that returns its `ms`", so
//!     the derived form is constructible from the combinator surface + the existing
//!     leaf with ZERO stdlib dependency. If `/spec`/`/stdlib` land a first-class
//!     `timeout` returning `(Option a)`, `/qa` re-points the §C3 rows.
//!
//! ## The A→C RAII-Permit-release-on-drop contract (gate (a))
//!
//! Chunk A BUILT the future-drop RAII permit-release path (the intrinsics-unit
//! predecessor `dropping_inflight_poll_releases_permit_next_waiter_proceeds`,
//! `tests/plan/sprint-96.md` §2B); Chunk C EXERCISES it at the source level here:
//! §C1c (`race_loser_releases_resource_permit`) and §C4a
//! (`cancelled_inflight_poll_releases_permit_next_waiter_proceeds_e2e`) are its
//! named e2e exercises. Co-review with the Chunk-A drop-release machinery.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{CrOutput, Cranelisp};

// =============================================================================
// Tuning. Matches the poll-carrier calibration in `concurrency_poll_capacity.rs`
// / `concurrency_fanout.rs` (D=150 absorbs the poll carrier's ~30 ms fixed reactor
// overhead). FAST ≪ SLOW separates winner from loser; the windows are two-sided
// (timing-flakiness is a banned disposition).
// =============================================================================

/// The "winner" / short delay (ms) — a race winner / a timeout deadline that fires.
const FAST: u64 = 50;
/// The "loser" / long delay (ms) — a race loser / an effect that exceeds a deadline.
/// Large enough that "ran the loser to completion" is unambiguously distinguishable
/// from "cancelled the loser" by wall-clock.
const SLOW: u64 = 400;
/// A trailing same-token effect's delay (ms) — used to witness that a cancelled
/// effect FREED its permit (the trailing effect proceeds promptly).
const D_MS: u64 = 150;

/// Best-of-N minimum for a wall-clock witness — contention can only make a
/// measurement SLOWER, never faster, so the minimum filters scheduler noise.
const BEST_OF_N: usize = 3;

// === Volume tuning (the finding-#3 / finding-#4 at-volume proxies) ============

/// Cancel ≥ 200 in-flight effects in a long loop (the A3-review finding-#3/#4
/// volume threshold — well above any observed corruption/leak threshold).
const VOLUME_N: u64 = 200;
/// A small per-iteration deadline so the volume loop completes in bounded time.
const VOL_SHORT: u64 = 3;
/// Generous wall-clock ceiling (ms) for the volume loops: a leak (finding #3 —
/// unbounded `fd_waiters` growth) or a lost-wakeup (finding #4 — a stranded
/// waiter) shows as super-linear slowdown / a hang (the 30 s harness cap), both
/// caught by this ceiling. A healthy loop is ~linear and finishes well under it.
const VOL_CEILING_MS: u128 = 15_000;

// === The `poll-pool` fixture leaves ==========================================

const POLL_PLATFORM: &str = "poll-pool";
const POLL_READ: &str = "poll-read"; // EXISTS (Chunk A) — armed-timer poll leaf.
const POLL_LOG: &str = "poll-log"; // EXISTS (Chunk A) — armed-timer leaf that prints `tag`.
/// `poll-block` — the Gap-G10 never-readying-fd cancellable leaf (Chunk-C C2 /dev +
/// /platform deliverable): arms interest on an fd that NEVER readies (e.g. the read
/// end of an unwritten pipe) and is cancellable by drop. Unlike the armed-timer
/// `poll-read` (whose entry self-clears at its deadline), `poll-block`'s entry
/// persists until actively deregistered — so it is the leaf that exhibits finding
/// #3's unbounded `fd_waiters` leak if cancellation does not deregister. Absent on
/// HEAD ⇒ clean runtime-RED. Intended shape: `(poll-block token capacity) -> IO Int`.
const POLL_BLOCK: &str = "poll-block";

// === Helpers =================================================================

/// `--run` the program with the workspace platforms on the search path.
fn run_prog(prog: &str) -> CrOutput {
    Cranelisp::new()
        .use_workspace_platforms()
        .run("user.cl")
        .user(prog)
        .output()
}

/// Best-of-`BEST_OF_N` minimum wall-clock (ms) over repeated `--run`s.
fn best_elapsed_ms(prog: &str) -> u128 {
    (0..BEST_OF_N)
        .map(|_| run_prog(prog).elapsed.as_millis())
        .min()
        .expect("BEST_OF_N >= 1")
}

// =============================================================================
// §C1 — `race` (first-to-complete wins; the loser is CANCELLED).
// `race : IO a -> IO a -> IO a` — the first to complete wins and its value is
// returned; the loser is cancelled (= drop the loser's future), which releases its
// permit, deregisters its reactor interest, and means the loser's completion
// side-effect NEVER occurs. A race that ran both to completion would be a `Par`.
// =============================================================================

// spec: spec/10-io.md §10.12.8 — `race` of a FAST and a SLOW poll-read returns the
// FAST branch's value (poll-read returns its `ms`), and completes in ≈ FAST wall-
// clock (the SLOW branch did not gate completion). Item 1 — exactly one branch's
// value (the winner's) is returned.
#[test]
fn race_returns_first_completed_value() {
    // FAST on token 1, SLOW on token 2 (distinct tokens, both run). main IS the
    // race (IO Int); the returned Int is the exit code ⇒ exit FAST.
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read}]])\n\
         (import [primitives [race]])\n\
         (defn main [] (race ({read} 1 1 {fast}) ({read} 2 1 {slow})))\n",
        plat = POLL_PLATFORM,
        read = POLL_READ,
        fast = FAST,
        slow = SLOW,
    );
    run_prog(&prog).assert_exit(FAST as i32);

    let ms = best_elapsed_ms(&prog);
    assert!(
        ms < SLOW as u128,
        "race must complete with the FAST winner (≈{FAST}ms, < the SLOW loser's \
         {SLOW}ms); measured {ms}ms — looks like it waited out the loser (not a race)",
    );
}

// spec: spec/10-io.md §10.12.9 — the LOSER of a race is CANCELLED before its
// completion side-effect: `(race (poll-log … "win") (poll-log … "lose"))` prints
// ONLY "win"; "lose" MUST NOT appear (item 2 — no completion side-effect for a
// cancelled effect). The load-bearing `_neg`: a race that ran both to completion
// (a `Par`) would print BOTH tags.
#[test]
fn race_loser_completion_side_effect_absent_neg() {
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{log}]])\n\
         (import [primitives [race]])\n\
         (defn main [] (race ({log} 1 1 {fast} \"win\") ({log} 2 1 {slow} \"lose\")))\n",
        plat = POLL_PLATFORM,
        log = POLL_LOG,
        fast = FAST,
        slow = SLOW,
    );
    let out = run_prog(&prog);
    let stdout = out.stdout.clone();
    // Positive: the winner ran (its tag printed). RED on HEAD (race undefined ⇒
    // neither tag prints).
    assert!(
        stdout.contains("win"),
        "race winner's side-effect (\"win\") must occur; got stdout={stdout:?}",
    );
    // Negative (load-bearing): the loser was CANCELLED before its print phase.
    assert!(
        !stdout.contains("lose"),
        "race LOSER must be cancelled before its completion side-effect — \"lose\" \
         MUST NOT appear (spec/10-io.md §10.12.9 item 2); got stdout={stdout:?} \
         (both tags ⇒ both branches ran to completion = a Par, not a race)",
    );
}

// spec: spec/10-io.md §10.12.9 — the A→C RAII-Permit-release-on-drop contract,
// e2e. On a SHARED capacity-1 token, the cancelled race loser MUST release its
// permit (item 1 — a permit freed by a cancelled effect becomes available to an
// effect parked on that token). `(bind (race FAST SLOW) (fn [_] trailing))` on one
// capacity-1 token: FAST wins, SLOW is cancelled (parked awaiting the single
// permit), the trailing same-token read then proceeds promptly. A leaked loser
// permit would leave capacity-1 exhausted ⇒ the trailing read waits out SLOW (or
// hangs forever).
#[test]
fn race_loser_releases_resource_permit() {
    // token 7, capacity 1, shared by both race branches AND the trailing read.
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read}]])\n\
         (import [primitives [race bind]])\n\
         (defn main []\n\
           (bind (race ({read} 7 1 {fast}) ({read} 7 1 {slow})) (fn [_]\n\
             ({read} 7 1 {d}))))\n",
        plat = POLL_PLATFORM,
        read = POLL_READ,
        fast = FAST,
        slow = SLOW,
        d = D_MS,
    );
    run_prog(&prog).assert_exit(D_MS as i32);

    let ms = best_elapsed_ms(&prog);
    // < FAST + SLOW: the loser was CANCELLED (its permit freed) and the trailing
    // read proceeded immediately ≈ FAST + D, NOT FAST + SLOW + D. (A leaked permit
    // would park the trailing read until the 30 s cap — also caught here.)
    assert!(
        ms < (FAST + SLOW) as u128,
        "the cancelled race loser must RELEASE its capacity-1 permit so the trailing \
         same-token read proceeds (≈{}ms = FAST+D, < FAST+SLOW = {}ms); measured \
         {ms}ms — looks like the permit leaked (trailing parked) or the loser ran to \
         completion",
        FAST + D_MS,
        FAST + SLOW,
    );
}

// =============================================================================
// §C2 — `select` (n-ary generalisation of `race` over a homogeneous list).
//
// NOTE — re-pointed to the AS-LANDED spec (Gap G8 resolved). The plan drafted §C2
// against a provisional "select reports the winner INDEX" shape; the spec that
// LANDED (§10.12.8 item 3) says `select`/`race` return ONLY the winner's VALUE,
// NOT its index — `select` is the n-ary generalisation of `race` over a List, and
// `select [a b]` is observationally equivalent to `race a b`. A program that must
// distinguish the winner encodes the discriminant in each branch's RESULT VALUE.
// So §C2's rows assert (a) the first-to-complete VALUE is returned and (b) the
// losers' completion side-effects are absent — NOT an index report.
// =============================================================================

// spec: spec/10-io.md §10.12.8 — `select` over a List of poll-reads returns the
// first-to-complete VALUE (the n-ary generalisation of `race`, item 1): the FAST
// branch (index 1, between two SLOW branches) wins and its value is returned;
// wall-clock ≈ FAST.
#[test]
fn select_returns_first_completed_value() {
    // distinct tokens 1/2/3; index 1 (FAST) wins ⇒ exit FAST.
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read}]])\n\
         (import [primitives [select]])\n\
         (defn main []\n\
           (select [({read} 1 1 {slow}) ({read} 2 1 {fast}) ({read} 3 1 {slow})]))\n",
        plat = POLL_PLATFORM,
        read = POLL_READ,
        fast = FAST,
        slow = SLOW,
    );
    run_prog(&prog).assert_exit(FAST as i32);

    let ms = best_elapsed_ms(&prog);
    assert!(
        ms < SLOW as u128,
        "select must complete with the first-to-complete branch (≈{FAST}ms, < the \
         SLOW branches' {SLOW}ms); measured {ms}ms — looks like it waited out a loser",
    );
}

// spec: spec/10-io.md §10.12.9 — `select`'s LOSERS are cancelled, not merely
// ignored (§10.12.8 item 4 + §10.12.9 item 2): over `[(poll-log "a") (poll-log
// "b") (poll-log "c")]` with only "b" fast, ONLY "b" prints — "a" and "c" MUST NOT
// appear (their completion side-effects do not occur). The negative face — a select
// that ran all branches to completion (an n-ary `Par`) would print all three tags.
#[test]
fn select_only_winner_value_returned_losers_side_effects_absent_neg() {
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{log}]])\n\
         (import [primitives [select]])\n\
         (defn main []\n\
           (select [({log} 1 1 {slow} \"a\") ({log} 2 1 {fast} \"b\") ({log} 3 1 {slow} \"c\")]))\n",
        plat = POLL_PLATFORM,
        log = POLL_LOG,
        fast = FAST,
        slow = SLOW,
    );
    let out = run_prog(&prog);
    let stdout = out.stdout.clone();
    assert!(
        stdout.contains('b'),
        "select winner's side-effect (\"b\") must occur; got stdout={stdout:?}",
    );
    assert!(
        !stdout.contains('a') && !stdout.contains('c'),
        "select LOSERS must be cancelled before their completion side-effects — \
         \"a\"/\"c\" MUST NOT appear (spec/10-io.md §10.12.9 item 2); got \
         stdout={stdout:?} (all three ⇒ all ran = an n-ary Par, not a select)",
    );
}

// =============================================================================
// §C3 — `timeout` (`timeout d io`: completes-in-time → result; exceeds → fires +
// io CANCELLED). DERIVED: `timeout d io ≡ race io (sleep d)`. Expressed INLINE as
// `(race io (poll-read deadline-tok cap d))` (the free-standing-test rule — no
// stdlib `timeout`); the deadline `poll-read` IS the `(sleep d)` timer.
// =============================================================================

// spec: spec/10-io.md §10.12.8 — `timeout` where the io COMPLETES before the
// deadline returns the io's result (item 5 — `(Some v)` for a first-class timeout;
// the io's value via the inline `race` form): io FAST vs deadline LONG ⇒ the io
// wins, wall-clock ≈ FAST (< the deadline). The deadline did not fire.
#[test]
fn timeout_io_completes_before_deadline_returns_result() {
    // io = poll-read FAST on token 1; deadline = poll-read SLOW (long) on token 99.
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read}]])\n\
         (import [primitives [race]])\n\
         (defn main [] (race ({read} 1 1 {fast}) ({read} 99 1 {slow})))\n",
        plat = POLL_PLATFORM,
        read = POLL_READ,
        fast = FAST,
        slow = SLOW,
    );
    run_prog(&prog).assert_exit(FAST as i32);

    let ms = best_elapsed_ms(&prog);
    assert!(
        ms < SLOW as u128,
        "timeout where the io completes in time must return the io's result \
         (≈{FAST}ms, < the deadline {SLOW}ms); measured {ms}ms — the deadline fired \
         or the io waited out the deadline",
    );
}

// spec: spec/10-io.md §10.12.9 — `timeout` where the io EXCEEDS the deadline: the
// deadline fires (the inline `race` deadline branch wins, value = the deadline's
// `ms`), wall-clock ≈ SHORT (< the io's LONG — did NOT wait out the io), AND the io
// is CANCELLED — its "io" Ready-phase tag MUST NOT appear (§10.12.9 item 2). The
// load-bearing `_neg`: a timeout that let the io run to completion would print "io"
// and take ≈ the io's LONG delay.
#[test]
fn timeout_io_exceeds_deadline_fires_and_cancels_io_neg() {
    // io = poll-log LONG (SLOW) printing "io" on token 1; deadline = poll-read
    // SHORT (FAST) on token 99 ⇒ the deadline fires ⇒ exit FAST.
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read} {log}]])\n\
         (import [primitives [race]])\n\
         (defn main [] (race ({log} 1 1 {slow} \"io\") ({read} 99 1 {fast})))\n",
        plat = POLL_PLATFORM,
        read = POLL_READ,
        log = POLL_LOG,
        fast = FAST,
        slow = SLOW,
    );
    let out = run_prog(&prog);
    let stdout = out.stdout.clone();
    out.assert_exit(FAST as i32);
    assert!(
        !stdout.contains("io"),
        "timeout exceeded must CANCEL the io before its completion side-effect — \
         \"io\" MUST NOT appear (spec/10-io.md §10.12.9 item 2); got stdout={stdout:?}",
    );

    let ms = best_elapsed_ms(&prog);
    assert!(
        ms < SLOW as u128,
        "timeout exceeded must FIRE at the deadline (≈{FAST}ms, < the io's {SLOW}ms); \
         measured {ms}ms — looks like it waited out the io (the deadline did not fire)",
    );
}

// =============================================================================
// §C4 — Structured cancellation at volume (the load-bearing findings #3 / #4 rows
// the chunk is gated on; the A3-review prerequisites). They prove cancellation at
// volume in a long-running reactor neither LEAKS (finding #3: a cancelled poll
// deregisters its fd interest) nor LOST-WAKES (finding #4: a future cancelled while
// parked awaiting a permit does not strand the next live waiter / the freed permit).
// =============================================================================

// spec: spec/10-io.md §10.12.9 — the A→C contract, standalone. A `timeout`-cancelled
// in-flight poll-read on a SHARED capacity-1 token releases its permit, and the next
// waiter on that SAME token proceeds (item 1). Distinct from §C1c (through `race`'s
// loser): here the cancelled effect is the SLOW one and a trailing same-token read
// is the "next waiter". A leaked permit would park the trailing read forever (the
// 30 s harness cap = a loud RED).
#[test]
fn cancelled_inflight_poll_releases_permit_next_waiter_proceeds_e2e() {
    // SLOW poll-read holds token 7's (capacity 1) permit; the FAST deadline (token
    // 99) wins the race and cancels SLOW ⇒ token 7's permit frees ⇒ the trailing
    // (next-waiter) read on token 7 proceeds ⇒ exit D.
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read}]])\n\
         (import [primitives [race bind]])\n\
         (defn main []\n\
           (bind (race ({read} 7 1 {slow}) ({read} 99 1 {fast})) (fn [_]\n\
             ({read} 7 1 {d}))))\n",
        plat = POLL_PLATFORM,
        read = POLL_READ,
        fast = FAST,
        slow = SLOW,
        d = D_MS,
    );
    run_prog(&prog).assert_exit(D_MS as i32);

    let ms = best_elapsed_ms(&prog);
    assert!(
        ms < SLOW as u128,
        "a cancelled in-flight poll must RELEASE its capacity-1 permit so the next \
         waiter on that token proceeds (≈{}ms, < SLOW {SLOW}ms); measured {ms}ms — \
         the permit leaked (next waiter parked) or the cancelled poll ran to completion",
        FAST + D_MS,
    );
}

// spec: spec/10-io.md §10.12.9 — finding #3 at volume: a long loop that
// `timeout`/race-cancels MANY (>= 200) in-flight polls each arming REAL fd interest
// (the `poll-block` never-readying-fd leaf) over a long-running reactor completes in
// BOUNDED wall-clock and EXITS 0 — the "cancel many ⇒ no unbounded waiter growth"
// observable (item 1 + item 4 — cancellation must not leak the reactor interest).
// On HEAD (no active deregistration, finding #3) the `fd_waiters` map + mio
// registrations grow without bound ⇒ super-linear slowdown / OOM ⇒ the ceiling fails.
// (The direct `fd_waiters`-count assertion is the co-landing intrinsics UNIT row.)
#[test]
fn volume_cancellation_does_not_leak_fd_waiters_bounded() {
    // A tail-recursive loop: each iteration races a never-readying `poll-block`
    // (token n, capacity 1) against a SHORT deadline `poll-read` (token 9999 —
    // OUTSIDE the 1..=VOLUME_N range so it never collides with the loop's
    // `poll-block` token `n`; a deadline token inside the range deadlocks at the
    // iteration where n == that token, FIXME 0473) — the
    // deadline always wins ⇒ the `poll-block` is cancelled (its fd interest must be
    // deregistered on drop). Result discarded; recurse VOLUME_N times ⇒ (Pure 0).
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read} {block}]])\n\
         (import [primitives [race bind Pure sub-i64 eq-i64]])\n\
         (defn cancel-loop [n]\n\
           (if (eq-i64 n 0)\n\
               (Pure 0)\n\
               (bind (race ({block} n 1) ({read} 9999 1 {short})) (fn [_]\n\
                 (cancel-loop (sub-i64 n 1))))))\n\
         (defn main [] (cancel-loop {vol}))\n",
        plat = POLL_PLATFORM,
        read = POLL_READ,
        block = POLL_BLOCK,
        short = VOL_SHORT,
        vol = VOLUME_N,
    );
    run_prog(&prog).assert_exit(0);

    let ms = best_elapsed_ms(&prog);
    assert!(
        ms < VOL_CEILING_MS,
        "cancelling {VOLUME_N} in-flight fd-arming polls must NOT leak reactor \
         interest — the loop must complete in bounded wall-clock (< {VOL_CEILING_MS}ms); \
         measured {ms}ms — looks like unbounded `fd_waiters` growth (finding #3: no \
         active deregistration on `EffectPoll` drop)",
    );
}

// spec: spec/10-io.md §10.12.9 — finding #4 at volume: over a capacity-bounded
// token where effects park awaiting a permit, repeatedly race-cancel a
// parked-awaiting-permit future at volume (>= 200) — every cancellation is followed
// by the next live waiter proceeding, the loop completes + EXITS 0, no deadlock, no
// unclaimable permit (item 1). On HEAD (no `Drop for AcquirePermit` cancel-safety,
// finding #4) a cancelled parked waiter strands its successor + the freed permit ⇒
// the loop hangs (the 30 s harness cap = a loud RED, also caught by the ceiling).
// (The direct FIFO lost-wakeup assertion is the co-landing intrinsics UNIT row.)
#[test]
fn volume_cancel_while_awaiting_permit_next_live_waiter_proceeds() {
    // A tail-recursive loop over a SHARED capacity-1 token 7: each iteration races a
    // SLOW poll-read on token 7 (which contends for the single permit — at volume,
    // successive iterations' reads park awaiting it) against a SHORT deadline on
    // token 99 (which wins and cancels the token-7 read, whether it held or was
    // PARKED-AWAITING the permit). Result discarded; recurse VOLUME_N times. If a
    // cancelled parked waiter lost-wakes its successor, the loop stalls.
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read}]])\n\
         (import [primitives [race bind Pure sub-i64 eq-i64]])\n\
         (defn await-cancel-loop [n]\n\
           (if (eq-i64 n 0)\n\
               (Pure 0)\n\
               (bind (race ({read} 7 1 {slow}) ({read} 99 1 {short})) (fn [_]\n\
                 (await-cancel-loop (sub-i64 n 1))))))\n\
         (defn main [] (await-cancel-loop {vol}))\n",
        plat = POLL_PLATFORM,
        read = POLL_READ,
        slow = SLOW,
        short = VOL_SHORT,
        vol = VOLUME_N,
    );
    run_prog(&prog).assert_exit(0);

    let ms = best_elapsed_ms(&prog);
    assert!(
        ms < VOL_CEILING_MS,
        "cancelling {VOLUME_N} parked-awaiting-permit futures must NOT lost-wake the \
         next live waiter — the loop must complete (< {VOL_CEILING_MS}ms), not deadlock; \
         measured {ms}ms — looks like a stranded waiter / unclaimable permit (finding \
         #4: no `Drop for AcquirePermit` cancel-safety)",
    );
}

// =============================================================================
// §C5a — synthetic graceful-shutdown core (no fan-out; the deferrable-independent
// acceptance). A shutdown trigger (modelled as a `race` of an in-flight effect
// against a short-deadline "shutdown signal") CANCELS the outstanding in-flight
// effect: its completion side-effect does NOT occur AND its resource releases (a
// trailing same-token effect proceeds — permit freed). The synthetic core of
// "shutdown cancels an outstanding strand" — no web/HTTP, no fan-out.
// =============================================================================

// spec: spec/10-io.md §10.12.10 — the graceful-shutdown reference pattern via the
// combinator surface: a long-running effect (poll-log LONG "io" on capacity-1 token
// 7) raced against a SHORT "shutdown signal" (poll-read on token 88) is CANCELLED
// when the signal fires — "io" MUST NOT appear (§10.12.9 item 2) AND token 7's
// permit frees so a trailing same-token read proceeds (item 1). Two-sided wall-clock.
#[test]
fn shutdown_cancels_outstanding_inflight_effect_releasing_resources() {
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read} {log}]])\n\
         (import [primitives [race bind]])\n\
         (defn main []\n\
           (bind (race ({log} 7 1 {slow} \"io\") ({read} 88 1 {fast})) (fn [_]\n\
             ({read} 7 1 {d}))))\n",
        plat = POLL_PLATFORM,
        read = POLL_READ,
        log = POLL_LOG,
        fast = FAST,
        slow = SLOW,
        d = D_MS,
    );
    let out = run_prog(&prog);
    let stdout = out.stdout.clone();
    out.assert_exit(D_MS as i32);
    assert!(
        !stdout.contains("io"),
        "graceful shutdown must CANCEL the outstanding effect before its completion \
         side-effect — \"io\" MUST NOT appear (spec/10-io.md §10.12.10 / §10.12.9 \
         item 2); got stdout={stdout:?}",
    );

    let ms = best_elapsed_ms(&prog);
    assert!(
        ms < SLOW as u128,
        "shutdown must cancel + free the outstanding effect's permit so the trailing \
         same-token effect proceeds (≈{}ms, < SLOW {SLOW}ms); measured {ms}ms — the \
         effect ran to completion or its permit leaked",
        FAST + D_MS,
    );
}
