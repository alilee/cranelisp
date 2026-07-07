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
//! Draft-time polarity (probed against HEAD 2026-07-07, release binary):
//!   GREEN (correctness — the durable record independent of the perf verdict):
//!     f7_alloc_parallel_serial_exit_match
//!     f8_stack_witness_parallel_serial_exit_match
//!     f8_serial_arm_stack_allocates            (positive control: stack-alloc CAN fire)
//!   RED (failing-not-ignored — the durable attribution records, §9.1):
//!     f8_gate5_parallel_arm_stack_alloc_reachable  (§9.1.1 — the 0525 gate-5
//!         reachability gap: the stack lever fires only on the non-recursive
//!         in-frame arm, NEVER on the recursive/sparked parallel-search arm;
//!         RED until a spark-frame-aware + recursion-aware stack path lands)
//!     f3_shared_read_residual_atomic_rc_confined  (§9.1.2 — the F3 dominant
//!         term: shared-read parallel reduce emits conservatively-atomic RC that
//!         a confinement-precision lever (0526/0528) would move to the non-atomic
//!         arm; RED until that lever lands)
//!
//! Verdict feeding these bars (`tests/plan/s105-attribution-results.md`): the
//! F4-hard residual is **unavailable-parallelism → accept-done**; F3 carries a
//! large residual-atomic-RC term (NONATOMIC_RC recovers ~76%). The stack lever is
//! NOT selected — the gate-5 sub-verdict shows it never reaches the parallel path.
//! These two RED guards are the durable records of the two live findings, kept
//! failing-not-ignored per `memory/feedback_failing_not_ignored.md` +
//! `memory/feedback_no_fixme_with_failing_test.md`.
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
  (deftype P (A [:Int x :Int y]) (B [:Int x :Int y]))\n\
  (defn one [n] (let [p (if (eq-i64 (rmod n 2) 0) (A n (add-i64 n 1)) (B (add-i64 n 2) n))]\n\
    (match p [(A x y) (add-i64 x y)  (B x y) (sub-i64 x y)])))\n\
  (defn drive [k acc] (if (le-i64 k 0) acc (drive (sub-i64 k 1) (add-i64 acc (one k)))))\n\
  (defn main [] (Pure (rmod (drive 256 0) 1000)))\n";

// F8 PARALLEL arm — the SAME phi-P construction lexically inside a self-recursive
// D&C's spark-bearing apply-args (gate 3 self-recursion + gate 5 spark relocation).
const F8_PARALLEL: &str = "(import [primitives [*]])\n\
  (defn rmod [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))\n\
  (defn mid-of [lo hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))\n\
  (deftype P (A [:Int x :Int y]) (B [:Int x :Int y]))\n\
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
  (deftype Cell (Given [:Int value]) (Solved [:Int value]))\n\
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
// FAILING-NOT-IGNORED attribution records (RED) — §9.1.
// =============================================================================

// spec: tests/plan/s105-residual-attribution.md §"Behavioural guards" (guard 1 / §4.1) — the 0525
// gate-5 parallel-residual reachability gap. RED: the stack lever fires only on
// the non-recursive in-frame arm (f8_serial_arm_stack_allocates, GREEN) and NEVER
// on the recursive/sparked parallel-search arm — the shape the F3/F4 residual
// actually lives on. Gate 3 (self-recursion) declines the recursive bearer AND
// gate 5 declines any lenient spark relocation, so the SAME construction that
// stack-allocates in-frame stays heap on the parallel path. This guard flips
// GREEN only when a spark-frame-aware + recursion-aware stack path lands (a scope
// increase beyond increment I). FIXME(/backend): spark-frame-aware stack path
// (`design/backend/ownership-codegen.md` §4.3 gate 5 / gate 3 relaxation).
#[test]
fn f8_gate5_parallel_arm_stack_alloc_reachable() {
    let out = run_rc_stats(F8_PARALLEL, /*serial=*/ false);
    let hits = rc_field(&out.stderr, "stack_slot");
    assert!(
        hits > 0,
        "PARALLEL-RESIDUAL REACHABILITY GAP (0525 gate-5, RED): the recursive/\
         sparked parallel-search arm's phi-ADT construction does NOT stack-\
         allocate (stack_slot={hits}) — gate 3 (self-recursion) + gate 5 (spark \
         relocation) decline it. The escape∧uniqueness stack lever therefore does \
         NOT recover the (a)-allocation on the parallel path; a spark-frame-aware \
         + recursion-aware stack path is a scope increase beyond increment I. \
         This guard is the durable record; it flips GREEN when that path lands.\n{}",
        out.stderr
    );
}

// spec: tests/plan/s105-residual-attribution.md §"Behavioural guards" (guard 2 / §6) — the F3
// dominant term. RED: a shared-read parallel reduce emits conservatively-atomic
// RC ops (rc_atomic>0) that a confinement-precision lever would move to the
// non-atomic arm. The attribution measured NONATOMIC_RC recovering ~76% of F3's
// parallel wall — the residual-atomic-RC term. A SOUND cure (not the unsound
// blanket NONATOMIC_RC) is 0526 confinement-gated projection elision / 0528
// uniqueness-preservation, which would prove more of these ops Confined and emit
// the non-atomic arm. This guard asserts the atomic arm is eliminated for the
// shared-read shape; RED until 0526/0528 lands. FIXME(/typecheck+/backend):
// 0526/0528 confinement precision (`design/arch/effect-concurrency.md` §3.1.6).
#[test]
fn f3_shared_read_residual_atomic_rc_confined() {
    let out = run_rc_stats(F3_SHARED_READ, /*serial=*/ false);
    let atomic = rc_field(&out.stderr, "rc_atomic");
    assert_eq!(
        atomic, 0,
        "RESIDUAL-ATOMIC-RC (F3 dominant term, RED): the shared-read parallel \
         reduce emits {atomic} conservatively-atomic RC ops. The S105 attribution \
         found NONATOMIC_RC recovers ~76% of F3's parallel wall — this atomic RC \
         is the F3 residual. A sound confinement-precision lever (0526/0528) would \
         prove these ops Confined and emit the non-atomic arm (rc_atomic→0). This \
         guard is the durable record; it flips GREEN when that lever lands.\n{}",
        out.stderr
    );
}
