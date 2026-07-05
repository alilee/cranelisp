//! S103 Phase-5 Stage-1 — increment-II (the write path): the reuse-token +
//! R5-flattening QA-first set.
//!
//! Plan: `tests/plan/s103-test-plan.md` §1.1 (F2v witness + L-C3 reuse fence +
//! reuse counter smoke + R5 value-flatten witness + R5 soundness-couple
//! negative fence), §1.5 (the `(map inc (map dec v))` chaining witness). Spine:
//! `design/arch/ownership-inference.md` §6.3/§7 (R5 mechanism), §7 (write path);
//! backend half `design/backend/ownership-codegen.md` §6 (reuse tokens),
//! §6.3 (a reuse fired on a non-unique value is heap corruption), §7.1/§7.2
//! (R5 flattening, one-word bound); typecheck half
//! `design/typecheck/ownership-inference.md` §7 (result_unique chaining,
//! eligibility-vs-permission).
//!
//! **Draft-time polarity** (probed against HEAD 2026-07-05; the write path has
//! not landed):
//!   GREEN (load-bearing when the mechanism lands — a mechanism that corrupts a
//!     shared value, diverges the toggle, or leaks fails these):
//!     l_c3_reuse_on_shared_value_other_ref_unchanged        (leg i)
//!     l_c3_reuse_on_shared_value_sustained                  (leg i sustained)
//!     l_c3_reuse_on_off_differential_identical_values       (leg iii)
//!     l_c3_reuse_heap_balance_iteration_independent          (leg iv)
//!     l_c3_sustained_epoch_allocs_independent_of_mutation_count (leg v)
//!     reuse_counter_family_present_reads_zero_pre_mechanism
//!     r5_soundness_couple_unflattened_two_ctor_not_copy_moded
//!     chaining_map_inc_map_dec_values_correct
//!     single_ctor / vec_set value-use cells (vec_query_value_use.rs L-M1)
//!   RED (flip when the named mechanism lands, per §6 flip protocol):
//!     l_c3_reuse_on_unique_value_reuse_hit_fires             (leg ii)
//!     reuse_hit_nonzero_when_unique_vec_mutated_in_place
//!     r5_value_flatten_rc_inc_collapses_vs_two_ctor
//!     chaining_map_inc_map_dec_two_in_place_passes
//!     chaining_toggle_off_allocates_intermediate (differential twin)
//!   RED (defect DISCOVERED at drafting — the guard is the record, owner
//!     /backend, the ownership use-counting / COW-eligibility seam §6.3):
//!     l_c3_pure_ssa_alias_vec_set_preserves_value_semantics (pure `(let [w v])`
//!       alias not counted as a use ⇒ in-place mutation corrupts the alias;
//!       exit 198 vs correct 109)
//!
//! Ledger: tests/plan/ledger.md §"Sprint 103 Phase-5 Stage-1 increment-II
//! QA-first RED set".
//!
//! Free-standing: every fixture is `(import [primitives [*]])` + inline helpers;
//! zero stdlib dependency (root CLAUDE.md §Stdlib separation).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

// =============================================================================
// Helpers
// =============================================================================

/// Run a free-standing program in `--run` mode; return the capture.
fn run_program(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new().run("user.cl").user(src).output()
}

/// Run with an explicit ownership-toggle polarity (`env_remove` for OFF, since
/// the toggle is presence-gated) so legs hold under the ambient-polarity L-B2(i)
/// suite run.
fn run_with_ownership(src: &str, no_ownership: bool) -> helpers::e2e::CrOutput {
    let c = Cranelisp::new().run("user.cl").user(src);
    let c = if no_ownership {
        c.env("CRANELISP_NO_OWNERSHIP", "1")
    } else {
        c.env_remove("CRANELISP_NO_OWNERSHIP")
    };
    c.output()
}

/// Run with `CRANELISP_RC_STATS=1`; return the capture.
fn run_with_rc_stats(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .run("user.cl")
        .user(src)
        .env("CRANELISP_RC_STATS", "1")
        .output()
}

/// Extract an integer field `k` from the single `[RC_STATS]` line. The landed
/// S102 H2 grammar (`crates/cranelisp-intrinsics/src/rc.rs::rc_stats_line`):
/// `[RC_STATS] rc_inc=N rc_dec=N allocs=N deallocs=N stack_slot=N reuse_hit=N
/// reuse_miss=N rc_nonatomic=N rc_atomic=N`.
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

/// Assert exit code equals `value % 256` (batch `main` returns `Pure Int`).
fn assert_exit_value(out: helpers::e2e::CrOutput, value: i64) -> helpers::e2e::CrOutput {
    let expected = (value % 256) as i32;
    match out.status.code() {
        Some(c) if c == expected => out,
        other => panic!(
            "expected exit {expected} (= {value} mod 256), got {other:?}\nstdout:\n{}\nstderr:\n{}",
            out.stdout, out.stderr
        ),
    }
}

/// The balance leg: run `template` (contains `{N}`) at N=50 and N=1000 with
/// RC_STATS and assert the alloc/dealloc imbalance is ITERATION-INDEPENDENT — a
/// per-iteration leak scales with N (delta ≥ 950 at this spread); a fixed
/// baseline does not. Bar |delta| ≤ 2, mirroring
/// `ownership_fences.rs::assert_iteration_independent_imbalance` (the at-exit
/// stats-print race is N-independent and bounded ±1; a real leak fails every
/// pair). Best-of-3, re-measuring only the ambiguous case.
fn assert_iteration_independent_imbalance(template: &str, context: &str) {
    let measure = || {
        let small = {
            let o = run_with_rc_stats(&template.replace("{N}", "50"));
            rc_field(&o.stderr, "allocs") - rc_field(&o.stderr, "deallocs")
        };
        let large = {
            let o = run_with_rc_stats(&template.replace("{N}", "1000"));
            rc_field(&o.stderr, "allocs") - rc_field(&o.stderr, "deallocs")
        };
        (small, large, (large - small).abs())
    };
    let mut best = measure();
    for _ in 0..2 {
        if best.2 <= 2 {
            break;
        }
        let next = measure();
        if next.2 < best.2 {
            best = next;
        }
    }
    let (small, large, delta) = best;
    assert!(
        delta <= 2,
        "[{context}] alloc/dealloc imbalance scales with iteration count \
         (N=50 → {small}, N=1000 → {large}, best-of-3 delta {delta}) — a \
         per-iteration leak (reuse-fence balance leg, s103 plan §1.1 leg iv)"
    );
}

// =============================================================================
// L-C3 — the reuse-corruption fence (qa plan §1.1; backend §6.3). A reuse token
// fired on a NON-UNIQUE value is heap corruption; the fence guards that the
// reuse mechanism can only fire when it is sound. Five legs.
// =============================================================================

// spec: design/backend/ownership-codegen.md §6.3 — L-C3 leg (i): a `vec-set` on
// a SHARED value (rc>1) MUST copy-on-write, leaving the OTHER reference
// unchanged. If a reuse token wrongly fires on the shared buffer, the aliased
// reference observes the mutation (corruption). The second reference is minted
// through `(id v)` so it is a genuine retained owning reference (rc>1) — a pure
// SSA alias `(let [w v] ...)` is mis-analysed today (see the discovered-defect
// guard below). GREEN at draft (conservative COW copies the shared source);
// LOAD-BEARING when reuse tokens land — the primary correctness precondition for
// II-G2/G3/G4.
#[test]
fn l_c3_reuse_on_shared_value_other_ref_unchanged() {
    // `w` retains `v` (rc>1); the vec-set of `v` must NOT reuse the shared
    // buffer. w[0] stays 10; v2[0] is 99 ⇒ 109. A wrong reuse gives 198.
    let out = run_program(
        "(import [primitives [*]])\n\
         (defn id [x] x)\n\
         (defn probe []\n\
         \x20 (let [v [10 20 30]\n\
         \x20       w (id v)\n\
         \x20       v2 (vec-set v 0 99)]\n\
         \x20   (add-i64 (vec-get w 0) (vec-get v2 0))))\n\
         (defn main [] (Pure (probe)))\n",
    );
    assert_exit_value(out, 10 + 99);
}

// spec: design/backend/ownership-codegen.md §6.3 — L-C3 leg (i) sustained: the
// shared-source COW invariant under 1000 crossings (a threshold-delayed
// corruption would surface here). Each iteration re-retains and re-mutates; the
// retained read must stay the original value every time. GREEN at draft.
#[test]
fn l_c3_reuse_on_shared_value_sustained() {
    let out = run_program(
        "(import [primitives [*]])\n\
         (defn id [x] x)\n\
         (defn spin [:Int n :Int acc]\n\
         \x20 (if (eq-i64 n 0) acc\n\
         \x20   (let [v [10 20 30]\n\
         \x20         w (id v)\n\
         \x20         v2 (vec-set v 0 99)]\n\
         \x20     (spin (sub-i64 n 1) (add-i64 acc (sub-i64 (vec-get v2 0) (vec-get w 0)))))))\n\
         (defn main [] (Pure (spin 1000 0)))\n",
    );
    // Each iteration contributes 99 - 10 = 89; 1000 * 89 = 89000; mod 256 = 168.
    assert_exit_value(out, 1000 * 89);
}

// spec: spec/12-runtime.md §12.2 — vec VALUE SEMANTICS: `vec-set` returns a NEW
// vec; a distinct binding aliasing the source MUST observe the source's ORIGINAL
// element after the set. DEFECT DISCOVERED AT S103 DRAFTING (failing-not-ignored;
// this guard is the record — no FIXME per
// memory/feedback_no_fixme_with_failing_test.md): a PURE SSA alias
// `(let [w v] ...)` is NOT counted as a second use of `v`, so `(vec-set v 0 99)`
// mutates in place and the aliased `w` reads the corrupted 99 — exit 198 instead
// of the correct 109. The retained-alias shape `(let [w (id v)] ...)` (leg i
// above) and a second direct use of `v` both COW correctly (109); ONLY the pure
// SSA alias mis-analyses (probed 2026-07-05). This is exactly the L-C3
// heap-corruption class — a mutation on a value that is in fact shared. Owner
// /backend (the ownership use-counting / COW-eligibility seam, backend §6.3).
#[test]
fn l_c3_pure_ssa_alias_vec_set_preserves_value_semantics() {
    let out = run_program(
        "(import [primitives [*]])\n\
         (defn probe []\n\
         \x20 (let [v [10 20 30]\n\
         \x20       w v\n\
         \x20       v2 (vec-set v 0 99)]\n\
         \x20   (add-i64 (vec-get w 0) (vec-get v2 0))))\n\
         (defn main [] (Pure (probe)))\n",
    );
    // Value semantics: w[0] MUST stay 10 (109). Today: 198 (in-place corruption).
    assert_exit_value(out, 10 + 99);
}

// spec: design/backend/ownership-codegen.md §6.1 — L-C3 leg (ii): on a UNIQUE
// value (rc==1) the reuse token is permitted to fire (mutate in place) and the
// dropped token feeds the next alloc. RED at draft: `reuse_hit` is a hardcoded
// `0` placeholder (rc.rs §H2 note "gain a writer when reuse lands") — no reuse
// path exists yet. Flips GREEN when reuse tokens land: a fresh unique vec
// mutated in a tight loop registers reuse hits. The VALUE leg is green today
// (correctness); the counter leg is the discriminator.
#[test]
fn l_c3_reuse_on_unique_value_reuse_hit_fires() {
    let out = run_with_rc_stats(
        "(import [primitives [*]])\n\
         (defn build [v i n]\n\
         \x20 (if (eq-i64 i n) v (build (vec-push v i) (add-i64 i 1) n)))\n\
         (defn churn [v i n]\n\
         \x20 (if (eq-i64 i n) v (churn (vec-set v i (add-i64 (vec-get v i) 1)) (add-i64 i 1) n)))\n\
         (defn main []\n\
         \x20 (let [v (build [] 0 64)\n\
         \x20       w (churn v 0 64)]\n\
         \x20   (Pure (vec-get w 0))))\n",
    );
    // Value leg (green today): w[0] = 0 + 1 = 1.
    let out = assert_exit_value(out, 1);
    // Counter leg (RED until reuse lands): a unique-vec in-place churn must
    // register reuse hits once the mechanism fires.
    let hits = rc_field(&out.stderr, "reuse_hit");
    assert!(
        hits > 0,
        "reuse tokens (backend §6) are owed at increment II (/backend, B3): an \
         in-place churn of a unique vec must register reuse_hit>0; got \
         reuse_hit={hits} (placeholder `0`, rc.rs §H2). stderr:\n{}",
        out.stderr
    );
}

// spec: tests/plan/s100-ownership-verification.md §3.1 — L-C3 leg (iii): the
// on/off differential — the reuse mechanism (part of the ownership analysis
// gated by CRANELISP_NO_OWNERSHIP) must produce IDENTICAL observable values
// whether on (default) or off. A reuse that corrupts would diverge the two.
// GREEN at draft; load-bearing when reuse fires.
#[test]
fn l_c3_reuse_on_off_differential_identical_values() {
    let src = "(import [primitives [*]])\n\
        (defn build [v i n]\n\
        \x20 (if (eq-i64 i n) v (build (vec-push v (mul-i64 i 3)) (add-i64 i 1) n)))\n\
        (defn churn [v i n]\n\
        \x20 (if (eq-i64 i n) v (churn (vec-set v i (add-i64 (vec-get v i) 7)) (add-i64 i 1) n)))\n\
        (defn main []\n\
        \x20 (let [v (build [] 0 32) w (churn v 0 32)]\n\
        \x20   (Pure (add-i64 (vec-get w 5) (vec-get w 31)))))\n";
    let on = run_with_ownership(src, false);
    let off = run_with_ownership(src, true);
    assert_eq!(
        on.status.code(),
        off.status.code(),
        "reuse on/off differential: ownership-toggle changed the value \
         (on {:?} != off {:?}); reuse tokens must be observationally invisible \
         (off-ABI, function-local — spine §3.5). on-stderr:\n{}\noff-stderr:\n{}",
        on.status.code(),
        off.status.code(),
        on.stderr,
        off.stderr
    );
    // Concrete value: w[5] = 15+7 = 22; w[31] = 93+7 = 100 ⇒ 122.
    assert_exit_value(on, 122);
}

// spec: tests/plan/s100-ownership-verification.md §3.2 — L-C3 leg (iv): the
// heap-balance leg — an in-place mutation of a uniquely-threaded vec must not
// leak (the mutate branch — v is the sole owner at each `vec-set`, written with
// a fresh value, no live read-borrow of the same slot). Imbalance
// iteration-independent. GREEN at draft (probed 2026-07-05: allocs==deallocs).
// LOAD-BEARING when reuse tokens land — a token that fails to release the
// displaced buffer fails here. (The COW *copy* branch's 0474 leak — source live
// after the set — has its own dedicated guards in
// tests/vec_cow_value_use_leak.rs; this fence guards the mutate/unique path the
// reuse tokens optimize.) ASan leg: tests/scripts/asan/, at B3 wave gates.
#[test]
fn l_c3_reuse_heap_balance_iteration_independent() {
    let template = "(import [primitives [*]])\n\
        (defn build [v i n]\n\
        \x20 (if (eq-i64 i n) v (build (vec-push v i) (add-i64 i 1) n)))\n\
        (defn churn [v i n]\n\
        \x20 (if (eq-i64 i n) v (churn (vec-set v i 0) (add-i64 i 1) n)))\n\
        (defn spin [:Int k :Int acc]\n\
        \x20 (if (eq-i64 k 0) acc\n\
        \x20   (let [w (churn (build [] 0 16) 0 16)]\n\
        \x20     (spin (sub-i64 k 1) (add-i64 acc (vec-get w 0))))))\n\
        (defn main [] (Pure (spin {N} 0)))\n";
    assert_iteration_independent_imbalance(template, "L-C3 reuse");
}

// spec: design/backend/ownership-codegen.md §6.1 — L-C3 leg (v): the sustained
// epoch — a uniquely-threaded vec mutated K times in place performs at most ONE
// allocation (the initial build; each in-place `vec-set` reuses the owned
// buffer), so allocs do NOT scale with the per-epoch mutation count. GREEN at
// draft (probed 2026-07-05: the unique mutate branch is already in-place).
// LOAD-BEARING when reuse tokens land — they must PRESERVE this in-place
// property (a reuse regression that re-copies each mutation makes allocs scale
// with K and fails here).
#[test]
fn l_c3_sustained_epoch_allocs_independent_of_mutation_count() {
    // One epoch, K in-place mutations of a freshly-built unique 8-elem vec.
    // `{K}` is the mutation count; the alloc delta between K=4 and K=64 must be
    // BOUNDED (in-place ⇒ constant) rather than scaling with K.
    let template = "(import [primitives [*]])\n\
        (defn build [v i n]\n\
        \x20 (if (eq-i64 i n) v (build (vec-push v 0) (add-i64 i 1) n)))\n\
        (defn churn [v i n]\n\
        \x20 (if (eq-i64 i n) v (churn (vec-set v 0 i) (add-i64 i 1) n)))\n\
        (defn main []\n\
        \x20 (let [w (churn (build [] 0 8) 0 {K})]\n\
        \x20   (Pure (vec-get w 0))))\n";
    let allocs = |k: &str| -> i64 {
        let o = run_with_rc_stats(&template.replace("{K}", k));
        rc_field(&o.stderr, "allocs")
    };
    let a_small = allocs("4");
    let a_large = allocs("64");
    let delta = a_large - a_small;
    assert!(
        delta <= 4,
        "an in-place churn of a uniquely-threaded vec must not scale allocs with \
         the mutation count: allocs at K=4 → {a_small}, K=64 → {a_large}, delta \
         {delta}. Reuse tokens must preserve this in-place property (backend §6)."
    );
}

// =============================================================================
// Reuse hit/miss counter smoke (qa plan §1.1 — against the LANDED S102 H2
// RC_STATS grammar; the counters exist and read 0 pre-mechanism).
// =============================================================================

// spec: design/backend/ownership-codegen.md §13.2 — the H2 grammar's reuse
// counter FAMILY is present and reads 0 before the mechanism fires (the
// placeholder honesty rc.rs §H2 pins). GREEN at draft.
#[test]
fn reuse_counter_family_present_reads_zero_pre_mechanism() {
    let out = run_with_rc_stats(
        "(import [primitives [*]])\n\
         (defn main [] (Pure (vec-get [1 2 3] 0)))\n",
    );
    let line = out
        .stderr
        .lines()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or("")
        .to_string();
    assert!(
        line.contains("reuse_hit=") && line.contains("reuse_miss="),
        "the landed H2 RC_STATS grammar carries the reuse_hit/reuse_miss counter \
         family; line: {line}"
    );
    assert_eq!(
        rc_field(&out.stderr, "reuse_hit"),
        0,
        "reuse_hit must read 0 before the reuse mechanism lands (placeholder honesty)"
    );
    assert_eq!(rc_field(&out.stderr, "reuse_miss"), 0);
}

// spec: design/backend/ownership-codegen.md §6.5 — the reuse counter moves once
// the mechanism fires: an in-place unique-vec mutation registers a non-zero
// reuse_hit. RED at draft (hardcoded 0). Companion to
// `l_c3_reuse_on_unique_value_reuse_hit_fires` (that one also pins the value);
// this one is the minimal counter-movement smoke.
#[test]
fn reuse_hit_nonzero_when_unique_vec_mutated_in_place() {
    let out = run_with_rc_stats(
        "(import [primitives [*]])\n\
         (defn build [v i n]\n\
         \x20 (if (eq-i64 i n) v (build (vec-push v i) (add-i64 i 1) n)))\n\
         (defn churn [v i n]\n\
         \x20 (if (eq-i64 i n) v (churn (vec-set v i 0) (add-i64 i 1) n)))\n\
         (defn main [] (Pure (vec-len (churn (build [] 0 128) 0 128))))\n",
    );
    let hits = rc_field(&out.stderr, "reuse_hit");
    assert!(
        hits > 0,
        "an in-place churn of a unique vec must register reuse_hit>0 once the \
         reuse mechanism lands (/backend, B3); got {hits}. stderr:\n{}",
        out.stderr
    );
}

// =============================================================================
// R5 value-flatten witness (qa plan §1.1, gate II-G1 attribution). The rc_inc
// collapse: F2v (one-word single-ctor `Cell`) flattens under R5, so its
// per-copy per-cell `rc_inc` volume collapses vs F2 (two-ctor `Cell`, NOT
// R5-first-landing-covered per §5 limit 1). The two fixtures are structurally
// identical apart from the payload constructor count, so pre-R5 their rc_inc
// counts are ~equal; post-R5 F2v's collapses. RED until R5 lands.
// =============================================================================

// spec: design/backend/ownership-codegen.md §7.1 — R5 value-flatten witness:
// F2v's rc_inc collapses materially below F2's once the one-word single-ctor
// payload is stored by value (null elem clone/drop fns, memcpy copies). RED at
// draft (F2v ≈ F2, both inc per retained cell on every shared-grid copy). The
// perf/gate-graded II-G1 "< 1% of B2" bar is `ig_gates.py`; this in-suite
// witness is the coarser RED-until-mechanism signal (a strict, margin-bearing
// drop, scheduling-independent because rc_inc is deterministic).
#[test]
fn r5_value_flatten_rc_inc_collapses_vs_two_ctor() {
    let f2v = run_with_rc_stats(include_str!("fixtures/s99/f2v_single_ctor.cl"));
    let f2 = run_with_rc_stats(include_str!("fixtures/s99/f2_contention.cl"));
    let f2v_inc = rc_field(&f2v.stderr, "rc_inc");
    let f2_inc = rc_field(&f2.stderr, "rc_inc");
    assert!(
        f2v_inc * 2 < f2_inc,
        "R5 must flatten F2v's one-word single-ctor `Cell` payload (by-value \
         copies, null elem fns) so its rc_inc collapses vs the structurally \
         identical two-ctor F2: expected f2v_inc*2 < f2_inc, got f2v_inc={f2v_inc} \
         f2_inc={f2_inc}. RED until R5 lands (backend §7.1); pre-R5 the two are \
         ~equal (both inc every retained cell per shared-grid copy)."
    );
}

// spec: design/arch/ownership-inference.md §6.3 — R5 soundness-couple NEGATIVE
// fence: a shape that LOOKS Copy-eligible but is NOT flattened (two-ctor per
// §7.1 — F2's `Cell`) must NOT be moded/treated `Copy`. If a Copy-moded-but-
// unflattened param slips through, its incs are wrongly skipped → missing-inc
// UAF. Sustained-use + heap-balance guards that: values stay correct across
// 1000 crossings AND the imbalance is iteration-independent. GREEN at draft
// (nothing flattens); LOAD-BEARING when R5 lands — the guard the
// `value_layout` single-source predicate cannot be by-passed.
#[test]
fn r5_soundness_couple_unflattened_two_ctor_not_copy_moded() {
    // Two-ctor Cell in a vec, projected + re-read after the root is copied —
    // the missing-inc UAF would surface as a wrong cell value or a crash.
    let template = "(import [primitives [*]])\n\
        (deftype Cell (Given [:Int value]) (Solved [:Int value]))\n\
        (defn cval [c] (match c [(Given v) v  (Solved v) v]))\n\
        (defn spin [:Int n :Int acc v]\n\
        \x20 (if (eq-i64 n 0) acc\n\
        \x20   (let [w (vec-set v 0 (Solved 7))]\n\
        \x20     (spin (sub-i64 n 1)\n\
        \x20       (add-i64 acc (add-i64 (cval (vec-get w 0)) (cval (vec-get v 1)))) v))))\n\
        (defn main [] (Pure (spin {N} 0 [(Given 3) (Given 4)])))\n";
    let out = run_program(&template.replace("{N}", "1000"));
    // w[0] = Solved 7 (7); v[1] stays Given 4 (4) — the aliased original is
    // never mutated. 1000 * (7 + 4) = 11000; mod 256 = 248.
    assert_exit_value(out, 1000 * (7 + 4));
    assert_iteration_independent_imbalance(template, "R5 negative fence (two-ctor)");
}

// =============================================================================
// The chaining witness (qa plan §1.5, II-G2 companion): the fused
// `(map inc (map dec v))` pipeline as TWO IN-PLACE PASSES, ZERO INTERMEDIATE
// ALLOCATION (typecheck §7.2 success metric = proof chaining). `map`/`inc`/`dec`
// are defined inline (free-standing); `map` maps by in-place-eligible `vec-set`.
// =============================================================================

/// The chaining fixture: `mapf` maps a fn over a vec by `vec-set` in place (so a
/// UNIQUE input can be mutated without reallocating); `(mapf inc (mapf dec v))`
/// is the fused pipeline whose inner result is a fresh unique vec the outer pass
/// can reuse. `{N}` sizes the vec.
const CHAIN_SRC: &str = "(import [primitives [*]])\n\
    (defn inc [x] (add-i64 x 1))\n\
    (defn dec [x] (sub-i64 x 1))\n\
    (defn map-go [f v i n]\n\
    \x20 (if (eq-i64 i n) v (map-go f (vec-set v i (f (vec-get v i))) (add-i64 i 1) n)))\n\
    (defn mapf [f v] (map-go f v 0 (vec-len v)))\n\
    (defn build [v i n]\n\
    \x20 (if (eq-i64 i n) v (build (vec-push v i) (add-i64 i 1) n)))\n\
    (defn main []\n\
    \x20 (let [v (build [] 0 {N})]\n\
    \x20   (Pure (vec-get (mapf inc (mapf dec v)) 3))))\n";

// spec: design/typecheck/ownership-inference.md §7.2 — the chaining pipeline's
// VALUE correctness (GREEN at draft): `(mapf inc (mapf dec v))` leaves each
// element unchanged (+1 then −1), so element 3 reads 3. Guards that the fused
// pipeline is semantically transparent regardless of the reuse decision.
#[test]
fn chaining_map_inc_map_dec_values_correct() {
    let out = run_program(&CHAIN_SRC.replace("{N}", "64"));
    assert_exit_value(out, 3);
}

// spec: design/typecheck/ownership-inference.md §7.2 — the II-G2 chaining
// witness: the fused pipeline runs as TWO IN-PLACE PASSES with ZERO
// intermediate allocation — the inner `mapf`'s unique result is REUSED by the
// outer pass (reuse_hit fires; no fresh vec is minted for the composition). RED
// at draft (reuse_hit hardcoded 0). Flips when `result_unique` chaining +
// reuse tokens land.
#[test]
fn chaining_map_inc_map_dec_two_in_place_passes() {
    let out = run_with_rc_stats(&CHAIN_SRC.replace("{N}", "64"));
    let hits = rc_field(&out.stderr, "reuse_hit");
    assert!(
        hits > 0,
        "the fused `(mapf inc (mapf dec v))` pipeline must run as two in-place \
         passes (the inner unique result reused by the outer pass — reuse_hit>0) \
         once result_unique chaining + reuse tokens land (typecheck §7.2, \
         /backend + /typecheck B1/B2); got reuse_hit={hits}. stderr:\n{}",
        out.stderr
    );
}

// spec: design/typecheck/ownership-inference.md §7.2 — the differential twin:
// with the ownership analysis OFF (CRANELISP_NO_OWNERSHIP), the pipeline cannot
// prove uniqueness, so each `vec-set` on the shared vec COW-copies — the
// composition allocates strictly MORE than the reuse-enabled run. RED at draft:
// on and off allocate the same (no reuse path exists to differentiate them).
// Flips when reuse tokens make the ON run allocate fewer.
#[test]
fn chaining_toggle_off_allocates_intermediate() {
    let src = CHAIN_SRC.replace("{N}", "64");
    let on = {
        let o = Cranelisp::new()
            .run("user.cl")
            .user(&src)
            .env("CRANELISP_RC_STATS", "1")
            .env_remove("CRANELISP_NO_OWNERSHIP")
            .output();
        rc_field(&o.stderr, "allocs")
    };
    let off = {
        let o = Cranelisp::new()
            .run("user.cl")
            .user(&src)
            .env("CRANELISP_RC_STATS", "1")
            .env("CRANELISP_NO_OWNERSHIP", "1")
            .output();
        rc_field(&o.stderr, "allocs")
    };
    assert!(
        on < off,
        "reuse tokens must make the ownership-ON run allocate strictly fewer \
         than the analysis-OFF run for the fused chaining pipeline (the toggle-off \
         conservative path COW-copies each pass): on allocs={on}, off allocs={off}. \
         RED until reuse tokens land (differential twin, qa plan §1.5)."
    );
}
