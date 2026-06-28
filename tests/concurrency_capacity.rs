//! Sprint 95 — effect-concurrency Slice 3 (token-capacity `Semaphore` pool) +
//! Slice 6 (two-pool routing): the QA-first (Phase-5 Wave-1) e2e acceptance rows.
//!
//! Plan: `tests/plan/sprint-95.md` §1B / §1C / §1D / §1F / §2B. Contract of
//! record: `design/arch/effect-concurrency.md` §8.1 (the `(token, capacity)`
//! dynamic-on-the-node carrier) / §8.2 (within-token source ordering) / §7
//! (two-pool model). Spec of record: `spec/10-io.md` §10.12.4.1 (Resource
//! Cardinality — Token Pools; items 1–5).
//!
//! ## Lane
//!
//! The whole file is gated `#![cfg(feature = "concurrency-runtime")]` — it runs
//! ONLY in the `nt-reactor-e2e` lane (`cargo nextest run -p cranelisp --features
//! concurrency-runtime`), where the reactor runtime + the host-owned
//! `HashMap<token, Semaphore(capacity)>` pool + the two-pool router are compiled
//! in. In the default `nt` lane the file compiles to nothing (no collateral RED,
//! no warnings).
//!
//! ## Posture (Phase-5 Wave-1 = RED-first)
//!
//! These are **failing-not-ignored** acceptance guards (`memory/feedback_failing_not_ignored`):
//! the capacity carrier + pool do not exist on HEAD. They fail at RUNTIME (the
//! `pool-demo` blocking platform is absent, or — for §2B — the blocking branch
//! still serializes through the single reactor thread until two-pool routing
//! lands), NOT at compile time (e2e shell out to the `cranelisp` binary), so the
//! workspace BUILDS green while these run RED. They flip GREEN as the /dev waves
//! land:
//!   - §1C/§1D/§1F — Wave 2 (`/platform` `pool-demo` blocking leaf declaring
//!     `(token, capacity)` via `effect_on_resource_with_capacity`) + Wave 4
//!     (intrinsics `HashMap<token, Semaphore>` acquire/park around blocking dispatch).
//!   - §2B — Wave 4 (two-pool routing: blocking branches → rayon, poll → reactor).
//!   - §1B — the unchanged slice-2 poll-overlap mechanism (may already be GREEN
//!     against the existing S94 `async-demo` leaf; a verify-on-HEAD witness, not
//!     part of the intended-RED set).
//!
//! ## The intended `pool-demo` blocking capacity leaf (Wave-2 deliverable, Gap G1)
//!
//! `tests/plan/sprint-95.md` §5 G1: the blocking capacity test-leaf is a
//! `/platform` + `/dev` Wave-2 deliverable. It does NOT exist yet, so this file
//! references the INTENDED surface via the consts below; reconcile the leaf
//! name(s) + the per-row token/capacity knob when the fixture lands (mirrors the
//! S94 `ASYNC_LEAF_PLATFORM`/`ASYNC_LEAF_EFFECT` pattern in
//! `concurrency_reactor.rs`). The leaf is a **platform effect** (not stdlib), so
//! the free-standing-test rule holds. Intended `pool-demo` effects, each declaring
//! its `(token, capacity)` at the effect site and routing to the blocking pool:
//!   - `pool-read  : (Int token, Int capacity, Int ms) -> IO Int` — sleep `ms` on
//!     the token's capacity pool, return `ms`.
//!   - `pool-write : (Int token, Int capacity, Int ms) -> IO Int` — a DISTINCT
//!     effect kind on the same token (the §1F sharing case), sleep `ms`, return `ms`.
//!   - `pool-log   : (Int token, Int capacity, Int ms, String tag) -> IO Int` —
//!     sleep `ms`, print `tag` to real stdout (the §1D source-order witness),
//!     return `ms`.
//!
//! NOTE — do NOT add a `platforms/pool-demo` crate here: an absent platform is a
//! clean runtime-RED; a non-compiling fixture crate would break the workspace
//! build. The fixture lands in Wave 2.

#![cfg(feature = "concurrency-runtime")]

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, CrOutput};

// =============================================================================
// Tuning. D is the per-effect delay; small enough to keep each timed run well
// under budget, large enough to swamp OS jitter and separate the regimes.
// =============================================================================

/// Per-effect delay (ms). With N=2 and 3 effects: unbounded ≈ 1·D, capacity-2
/// ≈ 2·D, serial ≈ 3·D — three regimes separable at a generous margin.
const D_MS: u64 = 60;

/// Best-of-N minimum for a wall-clock witness. CPU/scheduler contention can only
/// make a measurement SLOWER than the true wall-clock, never faster, so the
/// minimum over N filters contention noise and reflects the genuine
/// overlap/parking behaviour. (Same rationale as `spec_10_io::best_of_n_ms`.)
const BEST_OF_N: usize = 3;

// === The intended `pool-demo` blocking capacity leaf (Wave-2 deliverable) ====

const POOL_PLATFORM: &str = "pool-demo";
const POOL_READ: &str = "pool-read";
const POOL_WRITE: &str = "pool-write";
const POOL_LOG: &str = "pool-log";

// === Helpers =================================================================

/// `--run` the program (with the workspace platforms on the search path) and
/// return the captured output.
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
// §1B — distinct-token (independent) POLL effects overlap on the reactor.
// The unchanged slice-2 mechanism (independent poll leaves overlap via the
// reactor `join_all`); NO capacity acquire on the poll path this sprint (poll
// capacity-N is S96 — the node only reserves the slots at the sentinel). Drives
// the existing S94 `async-demo` poll leaf, so it is runnable now (verify-on-HEAD;
// likely GREEN — it extends the S94 two-leaf overlap to three).
// =============================================================================

// spec: spec/10-io.md §10.12.4.1 — three data-independent poll-shape async leaves
// (token 0 / unrestricted — §10.12.4.1 item 5) overlap on ONE reactor thread:
// wall-clock ≈ max(D), not 3·D. The poll-side distinct-token-overlap proof; no
// capacity pool is exercised here (slice-2 mechanism, unchanged).
#[test]
fn n_distinct_token_poll_leaves_overlap_max_not_sum() {
    // Three independent `async-read 60`; `a`/`b`/`c` are pairwise free so the
    // independence analysis Par-groups all three. Summed result = 180 (exit byte)
    // proves all ran; the wall-clock proves overlap.
    let prog = format!(
        "(platform async-demo)\n\
         (import [platform.async-demo [async-read]])\n\
         (import [primitives [bind Pure add-i64]])\n\
         (defn main []\n\
           (bind (async-read {d}) (fn [a]\n\
             (bind (async-read {d}) (fn [b]\n\
               (bind (async-read {d}) (fn [c]\n\
                 (Pure (add-i64 a (add-i64 b c)))))))))) \n",
        d = D_MS,
    );
    run_prog(&prog).assert_exit(180);

    let ms = best_elapsed_ms(&prog);
    assert!(
        ms < (D_MS as u128 * 3) / 2,
        "three independent poll leaves must OVERLAP on one reactor thread \
         (≈max {D_MS}ms, not sum {}ms); measured {ms}ms >= {}ms midpoint",
        D_MS * 3,
        (D_MS * 3) / 2,
    );
}

// =============================================================================
// §1C — same-token capacity-N (BLOCKING carrier): N concurrent, the (N+1)th parks.
// Spec §10.12.4.1 item 2. RED-first: needs the `pool-demo` blocking capacity leaf
// (Wave 2) + the `HashMap<token, Semaphore>` pool (Wave 4).
// =============================================================================

// spec: spec/10-io.md §10.12.4.1 — (N+1) blocking effects on ONE token of
// capacity N: the first N overlap on the blocking pool, the (N+1)th PARKS on the
// token's Semaphore until a permit frees (item 2 — the (N+1)th MUST NOT begin
// until a permit frees). N=2, 3 effects, each D ms ⇒ wall-clock ≈ 2·D, between
// unbounded (~1·D) and serial (~3·D).
#[test]
fn same_token_capacity_n_blocking_admits_n_concurrent_nplus1_parks() {
    // token 7, capacity 2, three independent D-ms blocking reads. Sum = 180 (exit).
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read}]])\n\
         (import [primitives [bind Pure add-i64]])\n\
         (defn main []\n\
           (bind ({read} 7 2 {d}) (fn [a]\n\
             (bind ({read} 7 2 {d}) (fn [b]\n\
               (bind ({read} 7 2 {d}) (fn [c]\n\
                 (Pure (add-i64 a (add-i64 b c)))))))))) \n",
        plat = POOL_PLATFORM,
        read = POOL_READ,
        d = D_MS,
    );
    run_prog(&prog).assert_exit(180);

    let ms = best_elapsed_ms(&prog);
    // Two-sided window: > 1.5·D proves the 3rd PARKED (did not overlap freely);
    // < 2.5·D proves the first two DID overlap (not fully serial). Wide on both
    // edges — timing-flakiness is a banned disposition.
    assert!(
        ms > (D_MS as u128 * 3) / 2,
        "capacity-2 pool: the 3rd same-token effect must PARK (wall-clock \
         > {}ms ≈ 1.5·D); measured {ms}ms — looks like it overlapped freely \
         (capacity not enforced)",
        (D_MS * 3) / 2,
    );
    assert!(
        ms < (D_MS as u128 * 5) / 2,
        "capacity-2 pool: the first two effects must OVERLAP (wall-clock \
         < {}ms ≈ 2.5·D); measured {ms}ms — looks fully serial (≈3·D)",
        (D_MS * 5) / 2,
    );
}

// =============================================================================
// §1D — same-token capacity-1 (BLOCKING carrier): serial AND source-ordered.
// Spec §10.12.4.1 item 3 (capacity 1 == ResourceSerial: exclusion AND order).
// RED-first: needs `pool-demo` (Wave 2) + the pool (Wave 4).
// =============================================================================

// spec: spec/10-io.md §10.12.4.1 — three blocking effects on ONE token of
// capacity 1 serialise (wall-clock ≈ 3·D, not overlapped) AND complete in SOURCE
// ORDER (item 3 — exclusion and order). The ordering is the negative face: a bare
// Semaphore(1) gives exclusion but not order (§8.2). Order is observed via the
// effect's stdout tags ("a","b","c"); the wall-clock witnesses serialisation.
#[test]
fn same_token_capacity_1_blocking_serial_and_source_ordered() {
    // token 9, capacity 1, tags a/b/c in source order, each sleeping D ms.
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{log}]])\n\
         (import [primitives [bind Pure add-i64]])\n\
         (defn main []\n\
           (bind ({log} 9 1 {d} \"a\") (fn [a]\n\
             (bind ({log} 9 1 {d} \"b\") (fn [b]\n\
               (bind ({log} 9 1 {d} \"c\") (fn [c]\n\
                 (Pure (add-i64 a (add-i64 b c)))))))))) \n",
        plat = POOL_PLATFORM,
        log = POOL_LOG,
        d = D_MS,
    );
    let out = run_prog(&prog);
    let stdout = out.stdout.clone();
    out.assert_exit(180);

    // Source order: "a" before "b" before "c" in the captured stdout.
    let ia = stdout.find('a');
    let ib = stdout.find('b');
    let ic = stdout.find('c');
    assert!(
        matches!((ia, ib, ic), (Some(a), Some(b), Some(c)) if a < b && b < c),
        "capacity-1 token must complete in SOURCE ORDER (a<b<c); \
         got stdout={stdout:?}",
    );

    // Serialisation: ≈ 3·D (> 2.5·D), not overlapped.
    let ms = best_elapsed_ms(&prog);
    assert!(
        ms > (D_MS as u128 * 5) / 2,
        "capacity-1 token must SERIALISE (wall-clock > {}ms ≈ 2.5·D, ~3·D); \
         measured {ms}ms — looks like it overlapped (capacity-1 not enforced)",
        (D_MS * 5) / 2,
    );
}

// =============================================================================
// §1F — capacity-on-token sharing (BLOCKING carrier): TWO DISTINCT effects share
// ONE token's pool (the DB-pool case the retired per-effect model couldn't
// express). RED-first: needs `pool-demo` (Wave 2) + the pool (Wave 4).
// =============================================================================

// spec: spec/10-io.md §10.12.4.1 — TWO distinct blocking effect kinds (pool-read
// + pool-write) declaring the SAME token of capacity N draw from ONE shared
// Semaphore(N): total sum-in-flight ≤ N across BOTH kinds; the (N+1)th (of either
// kind) parks. N=2, three mixed effects (read,write,read) ⇒ wall-clock ≈ 2·D. A
// per-effect pool would let each kind run N concurrently (no cross-kind bound)
// and measure ≈1·D, failing the lower bound.
#[test]
fn distinct_blocking_effects_sharing_one_token_share_one_pool_nplus1_parks() {
    // token 5, capacity 2, three mixed-kind effects on the SAME token.
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read} {write}]])\n\
         (import [primitives [bind Pure add-i64]])\n\
         (defn main []\n\
           (bind ({read} 5 2 {d}) (fn [a]\n\
             (bind ({write} 5 2 {d}) (fn [b]\n\
               (bind ({read} 5 2 {d}) (fn [c]\n\
                 (Pure (add-i64 a (add-i64 b c)))))))))) \n",
        plat = POOL_PLATFORM,
        read = POOL_READ,
        write = POOL_WRITE,
        d = D_MS,
    );
    run_prog(&prog).assert_exit(180);

    let ms = best_elapsed_ms(&prog);
    // Shared pool capacity 2: the 3rd effect (of either kind) PARKS ⇒ > 1.5·D;
    // the first two (a read + a write) OVERLAP ⇒ < 2.5·D.
    assert!(
        ms > (D_MS as u128 * 3) / 2,
        "two distinct effects sharing one token of capacity 2: the 3rd must \
         PARK on the SHARED pool (wall-clock > {}ms ≈ 1.5·D); measured {ms}ms — \
         looks like read/write got SEPARATE pools (capacity not shared by token)",
        (D_MS * 3) / 2,
    );
    assert!(
        ms < (D_MS as u128 * 5) / 2,
        "shared capacity-2 pool: the first two effects must OVERLAP (wall-clock \
         < {}ms ≈ 2.5·D); measured {ms}ms — looks fully serial",
        (D_MS * 5) / 2,
    );
}

// =============================================================================
// §2B — Slice 6: mixed blocking + poll-shape `Par` overlaps on BOTH pools.
// One blocking branch (test-capture sleep → rayon) + one poll-shape branch
// (async-demo → reactor) drive both pools concurrently and join. Uses EXISTING
// platforms, so it fails by BEHAVIOUR (not platform-absent): feature-on today the
// blocking branch routes through the single reactor thread and BLOCKS it, so the
// poll branch cannot progress and the two serialise (≈2·D) — RED. Flips GREEN
// when Wave 4's two-pool routing sends the blocking branch to rayon.
// =============================================================================

// spec: spec/10-io.md §10.12.4.1 — a Par with one blocking effect
// (commutative-sleep-ms → rayon/blocking pool) and one poll-shape effect
// (async-read → reactor), each D ms, overlaps concurrently on the two pools:
// wall-clock ≈ max(D) not sum; the summed exit proves both ran. The wakeable
// rayon→reactor bridge is what lets the blocking branch not starve the reactor.
#[test]
fn mixed_blocking_and_poll_par_overlaps_on_both_pools() {
    // Data-independent: `a` (blocking) and `b` (poll) are pairwise free, so the
    // independence analysis Par-groups them. Sum = 120 (exit byte).
    let prog = format!(
        "(platform test-capture)\n\
         (platform async-demo)\n\
         (import [platform.test-capture [commutative-sleep-ms]])\n\
         (import [platform.async-demo [async-read]])\n\
         (import [primitives [bind Pure add-i64]])\n\
         (defn main []\n\
           (bind (commutative-sleep-ms {d}) (fn [a]\n\
             (bind (async-read {d}) (fn [b]\n\
               (Pure (add-i64 a b)))))))\n",
        d = D_MS,
    );
    run_prog(&prog).assert_exit(120);

    let ms = best_elapsed_ms(&prog);
    assert!(
        ms < (D_MS as u128 * 3) / 2,
        "a mixed blocking+poll Par must OVERLAP on BOTH pools (≈max {D_MS}ms, \
         not sum {}ms); measured {ms}ms >= {}ms midpoint — the blocking branch \
         is starving the reactor (two-pool routing not wired)",
        D_MS * 2,
        (D_MS * 3) / 2,
    );
}
