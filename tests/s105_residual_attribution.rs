//! S105 Phase-5 — residual-attribution perf-lane BEHAVIOURAL guards.
//!
//! Companion to the graded perf-lane instrument `tests/perf/s105_attribution.py`
//! + fixtures `tests/fixtures/s99/{f7_alloc,f8_stack_witness}.cl`. Per the plan
//! (`tests/plan/s105-residual-attribution.md` §0.5 / §9.1), the graded walls and
//! attribution vectors are perf-lane (NOT nextest guards); what lands in the
//! `cargo nextest` suite is (a) the fixtures' parallel≡serial exit-match
//! CORRECTNESS record (GREEN) and (b) the two failing-not-ignored BEHAVIOURAL
//! guards that flip green when the selected build lever lands.
//!
//! Polarity (probed against HEAD 2026-07-07, release binary) — ALL GREEN:
//!   Correctness record (durable, independent of the perf verdict):
//!     f7_alloc_parallel_serial_exit_match
//!     f8_stack_witness_parallel_serial_exit_match
//!     f8_serial_arm_stack_allocates            (positive control: stack-alloc CAN fire)
//!   Current-behaviour characterizations (the two attribution records, §9.1):
//!     f8_gate5_parallel_arm_correctly_declines_stack_alloc  (§9.1.1 — the 0525
//!         gate-5 behaviour: the stack lever fires only on the non-recursive
//!         in-frame arm, and CORRECTLY declines on the recursive/sparked
//!         parallel-search arm. This is the current, correct behaviour under
//!         the accept-done verdict — the stack lever is NOT selected. FRONTIER:
//!         multi-field SROA would extend stack-alloc onto the parallel shape.)
//!     f3_shared_read_currently_uses_atomic_rc  (§9.1.2 — the F3 dominant term:
//!         a shared-read parallel reduce CURRENTLY emits conservatively-atomic
//!         RC (the sound confinement default). FRONTIER: a confinement-precision
//!         lever (0526/0528) would prove the shared reads Confined and move them
//!         to the non-atomic arm.)
//!
//! S105 CLOSE RECLASSIFICATION (Phase-7 action 1, user-approved): these two were
//! authored Wave-1 as failing-not-ignored REDs asserting an unbuilt feature. Under
//! the accept-done verdict (`tests/plan/s105-attribution-results.md`: the F4-hard
//! residual is unavailable-parallelism → accept-done → `--release`; NO memory or
//! stack lever built this sprint) those assertions would stay RED forever — a
//! misuse of failing-not-ignored, which is reserved for defects with intent-to-fix.
//! They are correct current behaviour we CHOSE not to change. Reclassified to GREEN
//! assertions of the current behaviour, each carrying a `// FRONTIER:` note of the
//! future increment that would flip the expectation. They remain live regression
//! guards of the current behaviour (they catch an accidental change), not perpetual
//! REDs. The frontier work (multi-field SROA; 0526/0528 confinement precision) is
//! handed forward, not owed.
//!
//! Free-standing: every fixture is `(import [primitives [*]])` + inline helpers;
//! zero stdlib dependency (root CLAUDE.md §Stdlib separation). Sources are small
//! inline scale-downs of the committed F7/F8 fixtures (nextest speed; the graded
//! full-scale runs live in the perf harness).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

// ── helpers ──────────────────────────────────────────────────────────────────

fn run_serial(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new().run("user.cl").user(src).env("CRANELISP_NO_LENIENT", "1").output()
}

fn run_parallel(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new().run("user.cl").user(src).env_remove("CRANELISP_NO_LENIENT").output()
}

/// Run with `CRANELISP_RC_STATS=1` at a chosen lenient polarity; return capture.
fn run_rc_stats(src: &str, serial: bool) -> helpers::e2e::CrOutput {
    let c = Cranelisp::new().run("user.cl").user(src).env("CRANELISP_RC_STATS", "1");
    let c = if serial { c.env("CRANELISP_NO_LENIENT", "1") } else { c.env_remove("CRANELISP_NO_LENIENT") };
    c.output()
}

/// Extract an integer field from the single `[RC_STATS]` line (post-S105 grammar,
/// `crates/cranelisp-intrinsics/src/rc.rs::rc_stats_line`, incl. `stack_slot=`,
/// `rc_atomic=`, `rc_nonatomic=`, `alloc_bytes=`).
fn rc_field(stderr: &str, k: &str) -> i64 {
    let line = stderr
        .lines()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("no [RC_STATS] line on stderr:\n{stderr}"));
    line.split_whitespace()
        .find_map(|tok| tok.strip_prefix(&format!("{k}=")))
        .and_then(|v| v.parse().ok())
        .unwrap_or_else(|| panic!("no {k}= field in RC_STATS line: {line}"))
}

// F7 miniature — the (a)-isolating shape: shallow coarse D&C, leaf builds fresh
// unshared Int vecs (heap, RC-light). Scaled DOWN (copies=32) for nextest speed.
const F7_MINI: &str = "(import [primitives [*]])\n\
  (defn rmod [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))\n\
  (defn mid-of [lo hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))\n\
  (defn build-vec [v i n] (if (eq-i64 i n) v (build-vec (vec-push v (add-i64 i 1)) (add-i64 i 1) n)))\n\
  (defn sum-vec [v i n acc] (if (eq-i64 i n) acc (sum-vec v (add-i64 i 1) n (add-i64 acc (vec-get v i)))))\n\
  (defn one [n] (sum-vec (build-vec [] 0 8) 0 8 0))\n\
  (defn leaf-work [lo k acc] (if (le-i64 k 0) acc (leaf-work lo (sub-i64 k 1) (add-i64 acc (one (add-i64 lo k))))))\n\
  (defn reduce-tree [lo hi] (if (le-i64 (sub-i64 hi lo) 1) (leaf-work lo 32 0)\n\
    (add-i64 (reduce-tree lo (mid-of lo hi)) (reduce-tree (mid-of lo hi) hi))))\n\
  (defn main [] (Pure (rmod (reduce-tree 0 16) 251)))\n";

// F8 SERIAL arm — non-recursive phi-P construction (gate 3 & 5 clear ⇒ stack-allocs).
const F8_SERIAL: &str = "(import [primitives [*]])\n\
  (defn rmod [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))\n\
  (deftype P (A [:Int x :Int y]) (B [:Int bx :Int by]))\n\
  (defn one [n] (let [p (if (eq-i64 (rmod n 2) 0) (A n (add-i64 n 1)) (B (add-i64 n 2) n))]\n\
    (match p [(A x y) (add-i64 x y)  (B x y) (sub-i64 x y)])))\n\
  (defn drive [k acc] (if (le-i64 k 0) acc (drive (sub-i64 k 1) (add-i64 acc (one k)))))\n\
  (defn main [] (Pure (rmod (drive 256 0) 1000)))\n";

// F8 PARALLEL arm — the SAME phi-P construction lexically inside a self-recursive
// D&C's spark-bearing apply-args (gate 3 self-recursion + gate 5 spark relocation).
const F8_PARALLEL: &str = "(import [primitives [*]])\n\
  (defn rmod [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))\n\
  (defn mid-of [lo hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))\n\
  (deftype P (A [:Int x :Int y]) (B [:Int bx :Int by]))\n\
  (defn drive [lo hi] (if (le-i64 (sub-i64 hi lo) 1) lo\n\
    (add-i64\n\
      (let [r (drive lo (mid-of lo hi))\n\
            p (if (eq-i64 (rmod r 2) 0) (A r (add-i64 r 1)) (B (add-i64 r 2) r))]\n\
        (match p [(A x y) (add-i64 x y)  (B x y) (sub-i64 x y)]))\n\
      (let [r (drive (mid-of lo hi) hi)\n\
            q (if (eq-i64 (rmod r 2) 0) (A r (add-i64 r 1)) (B (add-i64 r 2) r))]\n\
        (match q [(A x y) (add-i64 x y)  (B x y) (sub-i64 x y)])))))\n\
  (defn main [] (Pure (rmod (drive 0 256) 1000)))\n";

// A minimal shared-grid parallel reduce (F3/F2 miniature): cells read across
// strands. The conservative analysis marks the shared cells Crossing ⇒ atomic RC.
const F3_SHARED_READ: &str = "(import [primitives [*]])\n\
  (deftype Cell (Given [:Int given-value]) (Solved [:Int solved-value]))\n\
  (defn cell-value [c] (match c [(Given v) v  (Solved v) v]))\n\
  (defn rmod [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))\n\
  (defn mid-of [lo hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))\n\
  (defn build-grid [v i n] (if (eq-i64 i n) v (build-grid (vec-push v (Given (add-i64 (rmod i 9) 1))) (add-i64 i 1) n)))\n\
  (defn leaf [g lo] (cell-value (vec-get g (rmod lo (vec-len g)))))\n\
  (defn reduce-tree [g lo hi] (if (le-i64 (sub-i64 hi lo) 1) (leaf g lo)\n\
    (add-i64 (reduce-tree g lo (mid-of lo hi)) (reduce-tree g (mid-of lo hi) hi))))\n\
  (defn main [] (let [g (build-grid [] 0 27)] (Pure (rmod (reduce-tree g 0 64) 251))))\n";

// =============================================================================
// Correctness record (GREEN) — parallel ≡ serial exit-match (§9.1 last para).
// The fixtures' durable cargo-nextest correctness record, independent of perf.
// =============================================================================

// spec: tests/plan/s105-residual-attribution.md §"the (a)-isolating fixture"
#[test]
fn f7_alloc_parallel_serial_exit_match() {
    let s = run_serial(F7_MINI).status.code();
    let p = run_parallel(F7_MINI).status.code();
    assert_eq!(s, p, "F7 parallel must equal serial (lenient eval is transparent)");
    assert!(s.is_some(), "F7 must exit cleanly");
}

// spec: tests/plan/s105-residual-attribution.md §"the parallel stack-allocation witness"
#[test]
fn f8_stack_witness_parallel_serial_exit_match() {
    for src in [F8_SERIAL, F8_PARALLEL] {
        let s = run_serial(src).status.code();
        let p = run_parallel(src).status.code();
        assert_eq!(s, p, "F8 arm parallel must equal serial");
        assert!(s.is_some(), "F8 arm must exit cleanly");
    }
}

// spec: tests/plan/s105-residual-attribution.md §"the parallel stack-allocation witness"
// — positive control: stack allocation CAN fire on the non-recursive in-frame phi-ADT.
#[test]
fn f8_serial_arm_stack_allocates() {
    let out = run_rc_stats(F8_SERIAL, /*serial=*/ true);
    let hits = rc_field(&out.stderr, "stack_slot");
    assert!(
        hits > 0,
        "F8 serial arm (non-recursive phi-ADT) MUST stack-allocate — the escape∧\
         uniqueness stack path is live for the in-frame class; stack_slot={hits}\n{}",
        out.stderr
    );
}

// =============================================================================
// Current-behaviour attribution characterizations (GREEN) — §9.1.
// Reclassified from failing-not-ignored REDs at S105 close (accept-done verdict):
// each asserts the CURRENT, correct behaviour and carries a `// FRONTIER:` note of
// the future increment that would flip it. Live regression guards, not perpetual
// REDs. See the module doc comment for the reclassification rationale.
// =============================================================================

// spec: tests/plan/s105-residual-attribution.md §"Behavioural guards" (guard 1 / §4.1) — the 0525
// gate-5 parallel-residual behaviour. GREEN characterization: the stack lever fires
// only on the non-recursive in-frame arm (f8_serial_arm_stack_allocates, GREEN) and
// CORRECTLY declines on the recursive/sparked parallel-search arm — gate 3 (self-
// recursion) declines the recursive bearer AND gate 5 declines any lenient spark
// relocation, so the SAME construction that stack-allocates in-frame stays heap on
// the parallel path. This is the current, correct behaviour under the S105 accept-
// done verdict: the stack lever is NOT selected, and it must NOT silently start
// firing on the sparked path (which would relocate a possibly-escaping alloc into a
// spark frame). This guard pins that decline.
//
// FRONTIER: multi-field SROA (scalar-replacement of the phi-ADT's fields across the
// spark boundary) is the future increment that would legitimately extend stack-
// allocation onto the parallel shape; when that lands, this expectation flips to
// stack_slot>0 and the test is re-polarised. Handed forward, not owed.
#[test]
fn f8_gate5_parallel_arm_correctly_declines_stack_alloc() {
    let out = run_rc_stats(F8_PARALLEL, /*serial=*/ false);
    let hits = rc_field(&out.stderr, "stack_slot");
    assert_eq!(
        hits, 0,
        "PARALLEL-ARM GATE-5 DECLINE (0525, current correct behaviour): the \
         recursive/sparked parallel-search arm's phi-ADT construction must NOT \
         stack-allocate — gate 3 (self-recursion) + gate 5 (spark relocation) \
         correctly decline it, so the escape∧uniqueness stack lever stays on the \
         in-frame arm only (f8_serial_arm_stack_allocates is the positive control). \
         Observed stack_slot={hits} (expected 0). A non-zero here means stack-alloc \
         has started firing on the sparked path — either the FRONTIER multi-field \
         SROA lever landed (re-polarise this test to stack_slot>0) or an unsound \
         relocation regressed in (investigate before flipping).\n{}",
        out.stderr
    );
}

// spec: tests/plan/s105-residual-attribution.md §"Behavioural guards" (guard 2 / §6) — the F3
// dominant term. GREEN characterization: a shared-read parallel reduce CURRENTLY
// emits conservatively-atomic RC ops (rc_atomic>0). This is the current, correct
// behaviour — atomic RC is the SOUND default for reads the analysis marks Crossing
// (a shared cell read across strands). The S105 attribution measured NONATOMIC_RC
// recovering ~76% of F3's parallel wall, so this atomic RC is the F3 residual term;
// but serial already beats parallel 8× and NO lever was funded, so the sound
// conservative behaviour stands. This guard pins that the shared-read shape is
// still routed through the atomic arm.
//
// FRONTIER: confinement precision (0526 confinement-gated projection elision / 0528
// uniqueness-preservation, `design/arch/effect-concurrency.md` §3.1.6) is the future
// increment that would prove these shared reads Confined and move them to the non-
// atomic arm; when it lands, this expectation flips to rc_atomic==0 and the test is
// re-polarised. Handed forward, not owed.
#[test]
fn f3_shared_read_currently_uses_atomic_rc() {
    let out = run_rc_stats(F3_SHARED_READ, /*serial=*/ false);
    let atomic = rc_field(&out.stderr, "rc_atomic");
    assert!(
        atomic > 0,
        "F3 SHARED-READ ATOMIC RC (current sound-default behaviour): the shared-read \
         parallel reduce is expected to emit conservatively-atomic RC ops \
         (rc_atomic>0) — the sound default for cross-strand Crossing reads. Observed \
         rc_atomic={atomic}. A zero here means the shared reads are no longer routed \
         through the atomic arm — either the FRONTIER confinement-precision lever \
         (0526/0528) landed (re-polarise this test to rc_atomic==0) or an unsound \
         non-atomic regression slipped in (investigate before flipping).\n{}",
        out.stderr
    );
}
