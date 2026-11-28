//! Serial/parallel value equivalence for the S105 allocation fixtures, and
//! the shared-read atomic-RC characterization. Timing lives in `perf/`.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

// ── helpers ──────────────────────────────────────────────────────────────────

fn run_serial(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .run("user.cl")
        .user(src)
        .env("CRANELISP_NO_LENIENT", "1")
        .output()
}

fn run_parallel(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .run("user.cl")
        .user(src)
        .env_remove("CRANELISP_NO_LENIENT")
        .output()
}

/// Run with `CRANELISP_RC_STATS=1` at a chosen lenient polarity; return capture.
fn run_rc_stats(src: &str, serial: bool) -> helpers::e2e::CrOutput {
    let c = Cranelisp::new()
        .run("user.cl")
        .user(src)
        .env("CRANELISP_RC_STATS", "1");
    let c = if serial {
        c.env("CRANELISP_NO_LENIENT", "1")
    } else {
        c.env_remove("CRANELISP_NO_LENIENT")
    };
    c.output()
}

/// Extract an integer field from the single `[RC_STATS]` line (post-S105 grammar,
/// `crates/cranelisp-intrinsics/src/rc.rs::rc_stats_line`, incl. `rc_atomic=`, `rc_nonatomic=`, `alloc_bytes=`).
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
  (defn main [] (primitives/pure (rmod (reduce-tree 0 16) 251)))\n";

// F8 serial arm: non-recursive phi-P construction.
const F8_SERIAL: &str = "(import [primitives [*]])\n\
  (defn rmod [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))\n\
  (deftype P (A [:Int x :Int y]) (B [:Int bx :Int by]))\n\
  (defn one [n] (let [p (if (eq-i64 (rmod n 2) 0) (A n (add-i64 n 1)) (B (add-i64 n 2) n))]\n\
    (match p [(A x y) (add-i64 x y)  (B x y) (sub-i64 x y)])))\n\
  (defn drive [k acc] (if (le-i64 k 0) acc (drive (sub-i64 k 1) (add-i64 acc (one k)))))\n\
  (defn main [] (primitives/pure (rmod (drive 256 0) 1000)))\n";

// F8 parallel arm: phi-P construction inside a recursive divide-and-conquer.
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
  (defn main [] (primitives/pure (rmod (drive 0 256) 1000)))\n";

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
  (defn main [] (let [g (build-grid [] 0 27)] (primitives/pure (rmod (reduce-tree g 0 64) 251))))\n";

// =============================================================================
// Correctness record (GREEN) — parallel ≡ serial exit-match (§9.1 last para).
// The fixtures' durable cargo-nextest correctness record, independent of perf.
// =============================================================================

// spec: spec/12-runtime.md §12.4.3 — lenient evaluation preserves the serial result (F7 allocation-heavy)
#[test]
fn f7_alloc_parallel_serial_exit_match() {
    let s = run_serial(F7_MINI).status.code();
    let p = run_parallel(F7_MINI).status.code();
    assert_eq!(
        s, p,
        "F7 parallel must equal serial (lenient eval is transparent)"
    );
    assert!(s.is_some(), "F7 must exit cleanly");
}

// spec: spec/12-runtime.md §12.4.3 — lenient evaluation preserves the serial result (F8 both arms)
#[test]
fn f8_stack_witness_parallel_serial_exit_match() {
    for src in [F8_SERIAL, F8_PARALLEL] {
        let s = run_serial(src).status.code();
        let p = run_parallel(src).status.code();
        assert_eq!(s, p, "F8 arm parallel must equal serial");
        assert!(s.is_some(), "F8 arm must exit cleanly");
    }
}

// spec: design/backend/ownership-codegen.md §5.1 — shared reads outside one strand stay atomic; the F3
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
