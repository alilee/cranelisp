//! Sprint 96 — effect-concurrency Chunk A: poll-shape live capacity — the
//! QA-first (Phase-5 Wave-A1) e2e acceptance rows.
//!
//! Plan: `tests/plan/sprint-96.md` §1B / §1C / §1D. Contract of record:
//! `design/arch/effect-concurrency.md` §8.1 (the `(token, capacity)`
//! dynamic-on-the-node carrier — now lit up on the POLL carrier) / §8.2
//! (within-token source ordering) / §7 (two-pool model). `design/int/reactor.md`
//! §2.8 (the token-capacity `Semaphore` pool, carrier-agnostic) / §2.9 / §5 (the
//! acquire-around-poll lifecycle — the permit wraps the whole `EffectPoll`
//! establish→ready arc). `design/backend/io-trampoline.md` §14 (the poll-node
//! live `(token, capacity)` bake). Spec of record: `spec/10-io.md` §10.12.4.1
//! (Resource Capacity — Token Pools; items 1–5, REUSED — the poll carrier is
//! mechanism-neutral to the spec).
//!
//! ## Lane
//!
//! The whole file is gated `#![cfg(feature = "concurrency-runtime")]` — it runs
//! ONLY in the `nt-reactor-e2e` lane (`cargo nextest run -p cranelisp --features
//! concurrency-runtime`), where the reactor runtime + the host-owned
//! `HashMap<token, Semaphore(capacity)>` pool + the live poll-node `(token,
//! capacity)` read + the acquire-around-poll lifecycle are compiled in. In the
//! default `nt` lane the file compiles to nothing (no collateral RED, no
//! warnings).
//!
//! ## Posture (Phase-5 Wave-A1 = RED-first)
//!
//! These are **failing-not-ignored** acceptance guards
//! (`memory/feedback_failing_not_ignored`): on HEAD the poll path runs at the
//! S95-reserved SENTINEL capacity 1 with NO acquire-around-poll (the poll node
//! reserves the `(token, capacity)` slots but the trampoline does not read them
//! live yet, and `cranelisp-intrinsics` does not acquire a permit on the poll
//! arc). They fail at RUNTIME (the `poll-pool` poll-shape capacity leaf is
//! absent — Gap G1 — so `(platform poll-pool)` fails to resolve), NOT at compile
//! time (e2e shell out to the `cranelisp` binary), so the workspace BUILDS green
//! while these run RED. They flip GREEN as the Chunk-A /dev waves land:
//!   - A2 (backend bake): the poll node stores live `arg_vals[0]`/`arg_vals[1]`
//!     (token @ field_offset(1)=abs 32, capacity @ field_offset(2)=abs 40)
//!     replacing the S95 `iconst` sentinels.
//!   - A3 (intrinsics acquire-around-poll): `permit: Option<Permit>` on
//!     `EffectPoll`; the single admission gate at establish wrapping the whole
//!     establish→ready arc; eager release on `Poll::Ready` + auto drop-glue
//!     release on future-drop (the A→C RAII contract).
//!   - A4 (platform): the `poll-pool` poll-shape capacity test leaf (Gap G1) —
//!     authored WITH this wave (it consumes the live poll-node carrier), added
//!     to `tests/scripts/build-link-prereqs.sh` so the e2e resolves it.
//!
//! ## The intended `poll-pool` poll-shape capacity leaf (Wave-A4 deliverable, Gap G1)
//!
//! `tests/plan/sprint-96.md` §7 G1: the S95 capacity leaf (`pool-demo`) was
//! BLOCKING; Chunk A needs the **poll-shape analogue** — a `poll-pool` platform
//! whose effects declare `(token, capacity)` at the effect site and route to the
//! **reactor** (not rayon), suspending/resuming on an armed timer. It does NOT
//! exist yet, so this file references the INTENDED surface via the consts below;
//! reconcile the leaf name(s) + the per-row token/capacity knob when the fixture
//! lands (mirrors the S95 `POOL_*` pattern in `concurrency_capacity.rs`). The
//! leaf is a **platform effect** (not stdlib), so the free-standing-test rule
//! holds. Intended `poll-pool` effects, each declaring its `(token, capacity)` at
//! the effect site and routing to the reactor/poll carrier:
//!   - `poll-read  : (Int token, Int capacity, Int ms) -> IO Int` — poll-shape
//!     armed-timer leaf, suspend/resume on the reactor, capacity-pooled; return `ms`.
//!   - `poll-write : (Int token, Int capacity, Int ms) -> IO Int` — a DISTINCT
//!     poll effect kind on the same token (the §1D sharing case), return `ms`.
//!   - `poll-log   : (Int token, Int capacity, Int ms, String tag) -> IO Int` —
//!     poll-shape, print `tag` to real stdout (the §1C source-order witness),
//!     return `ms`.
//!
//! NOTE — do NOT add a `platforms/poll-pool` crate here: an absent platform is a
//! clean runtime-RED; a non-compiling fixture crate would break the workspace
//! build. The fixture lands in Wave A4 (per `tests/plan/sprint-96.md` §7 G1 and
//! the SPRINT.md A4 wave).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{CrOutput, Cranelisp};

// =============================================================================
// Tuning. D is the per-effect delay; small enough to keep each timed run well
// under budget, large enough to swamp OS jitter and separate the regimes.
//
// S96 A4 calibration (poll carrier): D is **larger** than the S95 blocking
// carrier's D=60. The poll carrier carries a fixed ~30 ms per-process overhead the
// blocking carrier does not (mio reactor construction + epoll registration + timer
// wheel + C-ABI waker plumbing + the acquire-around-poll permit hand-off on
// release). At D=60 that fixed cost is ~50% of one D, so the best-of-3 minimum of
// the correctly-overlapping capacity-2 run (≈ 2·D + overhead ≈ 150 ms) sits right
// ON the 2.5·D = 150 ms ceiling and flakes RED even though the overlap/park
// behaviour is correct. Raising D to 150 makes the three regimes 180 / 330 / 480 ms
// — 150 ms apart — so the ~30 ms fixed overhead is comfortably inside every window
// (overlap 330 < 375 ceiling; distinct 180 < 225 ceiling) while the relative
// `1.5·D` / `2.5·D` windows below still discriminate overlap from serial. (The
// blocking-carrier `concurrency_capacity.rs` keeps D=60 — it has no reactor
// overhead.)
// =============================================================================

// qa-ratified S96 B1: the A4d recalibration (D_MS 60→150, exit 180→194) preserves
// each assertion's discriminating intent. At D=150 the three regimes are 180 /
// 330 / 480 ms and the windows are 1.5·D=225 / 2.5·D=375:
//   - §1B capacity-2 overlap: ~330 ∈ (225, 375) — distinct from unbounded (180<225)
//     and serial (480>375). Discriminates.
//   - §1C capacity-1 serial: ~480 > 375. Discriminates.
//   - §1D distinct overlap: ~180 < 225. Discriminates.
//   - §1D shared-token: ~330 ∈ (225, 375). Discriminates.
// The ~30 ms fixed poll-carrier overhead sits comfortably inside every window
// (was ~50% of one D at the old D=60, flaking the §1B ceiling). exit 194 follows
// arithmetically from D=150 (sum 3·150=450, 450 & 0xFF = 194; was 3·60=180 & 0xFF
// = 180). Verdict: RATIFIED — regimes stay distinct, no window collapse.
/// Per-effect delay (ms). With N=2 and 3 effects: unbounded ≈ 1·D, capacity-2
/// ≈ 2·D, serial ≈ 3·D — three regimes separable at a generous margin (the poll
/// carrier's ~30 ms fixed reactor overhead fits inside each window at this D).
const D_MS: u64 = 150;

/// Best-of-N minimum for a wall-clock witness. CPU/scheduler contention can only
/// make a measurement SLOWER than the true wall-clock, never faster, so the
/// minimum over N filters contention noise and reflects the genuine
/// overlap/parking behaviour. (Same rationale as `concurrency_capacity.rs`.)
const BEST_OF_N: usize = 3;

// === The intended `poll-pool` poll-shape capacity leaf (Wave-A4 deliverable) ==

const POLL_PLATFORM: &str = "poll-pool";
const POLL_READ: &str = "poll-read";
const POLL_WRITE: &str = "poll-write";
const POLL_LOG: &str = "poll-log";

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
// §1B — same-token capacity-N POLL: N concurrent, the (N+1)th parks.
// The poll analogue of `concurrency_capacity.rs` §1C (blocking). spec/10-io.md
// §10.12.4.1 item 2 — the (N+1)th MUST NOT begin until a permit frees — now on
// the reactor/poll carrier (the permit wraps the establish→ready arc, so the
// (N+1)th poll does not even register interest until a permit frees).
// =============================================================================

// spec: spec/10-io.md §10.12.4.1 — (N+1) POLL-shape effects on ONE token of
// capacity N: the first N suspend/overlap on the reactor, the (N+1)th PARKS on
// the token's Semaphore until a permit frees (item 2). N=2, 3 effects, each D ms
// ⇒ wall-clock ≈ 2·D, between unbounded (~1·D) and serial (~3·D). The
// (N+1)th-parks-on-the-poll-arc is the load-bearing assertion.
#[test]
fn same_token_capacity_n_poll_admits_n_concurrent_nplus1_parks() {
    // token 7, capacity 2, three independent D-ms poll reads. Sum = 450, OS-truncated to exit 194 (450 & 0xFF).
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read}]])\n\
         (import [primitives [bind Pure add-i64]])\n\
         (defn main []\n\
           (bind ({read} 7 2 {d}) (fn [a]\n\
             (bind ({read} 7 2 {d}) (fn [b]\n\
               (bind ({read} 7 2 {d}) (fn [c]\n\
                 (Pure (add-i64 a (add-i64 b c)))))))))) \n",
        plat = POLL_PLATFORM,
        read = POLL_READ,
        d = D_MS,
    );
    run_prog(&prog).assert_exit(194);

    let ms = best_elapsed_ms(&prog);
    // Two-sided window: > 1.5·D proves the 3rd PARKED (did not overlap freely);
    // < 2.5·D proves the first two DID overlap. Wide on both edges —
    // timing-flakiness is a banned disposition.
    assert!(
        ms > (D_MS as u128 * 3) / 2,
        "capacity-2 poll pool: the 3rd same-token poll effect must PARK \
         (wall-clock > {}ms ≈ 1.5·D); measured {ms}ms — looks like it overlapped \
         freely (poll-carrier capacity not enforced / no acquire-around-poll)",
        (D_MS * 3) / 2,
    );
    assert!(
        ms < (D_MS as u128 * 5) / 2,
        "capacity-2 poll pool: the first two poll effects must OVERLAP on the \
         reactor (wall-clock < {}ms ≈ 2.5·D); measured {ms}ms — looks fully serial",
        (D_MS * 5) / 2,
    );
}

// =============================================================================
// §1C — same-token capacity-1 POLL: serial AND source-ordered.
// The poll analogue of `concurrency_capacity.rs` §1D. §10.12.4.1 item 3 / §8.2 —
// capacity 1 on the poll carrier is exclusion AND source order. The ordering is
// the negative face: a bare Semaphore(1) gives exclusion but not order; the poll
// join_all first-poll-in-source-order + acquire-as-first-action carries order.
// =============================================================================

// spec: spec/10-io.md §10.12.4.1 — three POLL-shape effects on ONE token of
// capacity 1 serialise (wall-clock ≈ 3·D, not overlapped) AND complete in SOURCE
// ORDER (item 3 — exclusion and order). Order observed via the leaf's stdout tags
// ("a","b","c"); the wall-clock witnesses serialisation on the poll arc.
//
// WATCH(/qa S97 §8.2 — same-token ordering home moves to the inference): under the
// v9 ctx-vtable model the trampoline no longer sees tokens, so the v8 SerialGroup
// order-restoring safety net DISSOLVES (`effect-concurrency.md §8.2`). Within-token
// SOURCE ORDER is now carried by the inference's E2 value-locality — but ONLY when
// the effects share the SAME EXPLICIT HANDLE (a shared free var). This test threads
// the token as a literal arg (`9`) across three DATA-INDEPENDENT `log` calls, so
// post-cutover the inference may parallelise them (exclusion via the permit, but NOT
// order) and the a<b<c assertion could break. Phase-5/dev-OWED reshape: thread the
// same explicit handle so E2 serialises them (or split exclusion vs order). Recorded
// in `tests/plan/sprint-97.md` §"§8.2 same-handle ordering watch-item".
#[test]
fn same_token_capacity_1_poll_serial_and_source_ordered() {
    // token 9, capacity 1, tags a/b/c in source order, each suspending D ms.
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{log}]])\n\
         (import [primitives [bind Pure add-i64]])\n\
         (defn main []\n\
           (bind ({log} 9 1 {d} \"a\") (fn [a]\n\
             (bind ({log} 9 1 {d} \"b\") (fn [b]\n\
               (bind ({log} 9 1 {d} \"c\") (fn [c]\n\
                 (Pure (add-i64 a (add-i64 b c)))))))))) \n",
        plat = POLL_PLATFORM,
        log = POLL_LOG,
        d = D_MS,
    );
    let out = run_prog(&prog);
    let stdout = out.stdout.clone();
    out.assert_exit(194);

    // Source order: "a" before "b" before "c" in the captured stdout.
    let ia = stdout.find('a');
    let ib = stdout.find('b');
    let ic = stdout.find('c');
    assert!(
        matches!((ia, ib, ic), (Some(a), Some(b), Some(c)) if a < b && b < c),
        "capacity-1 poll token must complete in SOURCE ORDER (a<b<c); \
         got stdout={stdout:?}",
    );

    // Serialisation: ≈ 3·D (> 2.5·D), not overlapped.
    let ms = best_elapsed_ms(&prog);
    assert!(
        ms > (D_MS as u128 * 5) / 2,
        "capacity-1 poll token must SERIALISE (wall-clock > {}ms ≈ 2.5·D, ~3·D); \
         measured {ms}ms — looks like it overlapped (capacity-1 not enforced on \
         the poll carrier)",
        (D_MS * 5) / 2,
    );
}

// =============================================================================
// §1D — distinct-token POLL independent (overlap) vs shared-token POLL shares
// the pool (the 3rd parks). Two rows: the independence floor and the sharing
// ceiling, both on the capacity-carrying poll leaf.
// =============================================================================

// spec: spec/10-io.md §10.12.4.1 — N (=3) DISTINCT-token poll leaves (each
// capacity >=1, different tokens) overlap on ONE reactor thread: wall-clock ≈
// max(D) not 3·D; no cross-token permit dependency (the independence floor —
// distinct tokens never share a pool). The slice-2 overlap mechanism re-asserted
// on the capacity-carrying poll leaf. (Disambiguated from the S95 bare-async-demo
// `n_distinct_token_poll_leaves_overlap_max_not_sum` in `concurrency_capacity.rs`,
// which is GREEN; this is the capacity-leaf re-assertion — RED until the poll-pool
// leaf + the live poll-node read land.)
#[test]
fn n_distinct_token_poll_capacity_leaves_overlap_max_not_sum() {
    // Three poll reads on DISTINCT tokens 1/2/3, each capacity 1, all D ms.
    // Pairwise data-independent ⇒ Par-grouped; summed result = 450 → exit 194 (450 & 0xFF) proves
    // all ran; the wall-clock proves overlap (no cross-token pool dependency).
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read}]])\n\
         (import [primitives [bind Pure add-i64]])\n\
         (defn main []\n\
           (bind ({read} 1 1 {d}) (fn [a]\n\
             (bind ({read} 2 1 {d}) (fn [b]\n\
               (bind ({read} 3 1 {d}) (fn [c]\n\
                 (Pure (add-i64 a (add-i64 b c)))))))))) \n",
        plat = POLL_PLATFORM,
        read = POLL_READ,
        d = D_MS,
    );
    run_prog(&prog).assert_exit(194);

    let ms = best_elapsed_ms(&prog);
    assert!(
        ms < (D_MS as u128 * 3) / 2,
        "three DISTINCT-token poll capacity leaves must OVERLAP on one reactor \
         thread (≈max {D_MS}ms, not sum {}ms); measured {ms}ms >= {}ms midpoint — \
         looks like distinct tokens shared a pool (cross-token permit dependency)",
        D_MS * 3,
        (D_MS * 3) / 2,
    );
}

// spec: spec/10-io.md §10.12.4.1 — TWO distinct POLL-shape effect kinds
// (poll-read + poll-write) declaring the SAME token of capacity N draw from ONE
// shared Semaphore(N): with N=2, 3 mixed-kind polls, at most 2 overlap and the
// 3rd PARKS regardless of kind (sum-in-flight <= N across both kinds). The
// shared-pool bound is load-bearing — a per-effect-kind pool would let each kind
// run N concurrently (≈1·D) and fail the lower bound.
#[test]
fn distinct_poll_effects_sharing_one_token_share_one_pool_nplus1_parks() {
    // token 5, capacity 2, three mixed-kind effects (read,write,read) on the SAME
    // token. Sum = 450, OS-truncated to exit 194 (450 & 0xFF).
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read} {write}]])\n\
         (import [primitives [bind Pure add-i64]])\n\
         (defn main []\n\
           (bind ({read} 5 2 {d}) (fn [a]\n\
             (bind ({write} 5 2 {d}) (fn [b]\n\
               (bind ({read} 5 2 {d}) (fn [c]\n\
                 (Pure (add-i64 a (add-i64 b c)))))))))) \n",
        plat = POLL_PLATFORM,
        read = POLL_READ,
        write = POLL_WRITE,
        d = D_MS,
    );
    run_prog(&prog).assert_exit(194);

    let ms = best_elapsed_ms(&prog);
    // Shared pool capacity 2: the 3rd effect (of either kind) PARKS ⇒ > 1.5·D;
    // the first two (a read + a write) OVERLAP ⇒ < 2.5·D.
    assert!(
        ms > (D_MS as u128 * 3) / 2,
        "two distinct poll effects sharing one token of capacity 2: the 3rd must \
         PARK on the SHARED pool (wall-clock > {}ms ≈ 1.5·D); measured {ms}ms — \
         looks like read/write got SEPARATE pools (capacity not shared by token)",
        (D_MS * 3) / 2,
    );
    assert!(
        ms < (D_MS as u128 * 5) / 2,
        "shared capacity-2 poll pool: the first two poll effects must OVERLAP \
         (wall-clock < {}ms ≈ 2.5·D); measured {ms}ms — looks fully serial",
        (D_MS * 5) / 2,
    );
}
