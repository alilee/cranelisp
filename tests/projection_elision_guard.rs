//! S102 Wave 14 — §3.3 consumer-driven vec-get projection-elision GUARD SET
//! (the adversarial `/review` item D: the "we only admit the safe shape"
//! safety argument had no committed proof that the UNSAFE shapes are declined,
//! no regression for the escaping-projection false-green class, and no
//! behavioral test of the 0522 fn-as-value wrapper path).
//!
//! Landed mechanism (commits e51629f / fb6a828): a DIRECT `(vec-get g i)`
//! projection — `g` a named binding, heap-typed element — passed DIRECTLY into
//! a callee parameter classified `Borrowed` collapses its element inc + post-
//! call dec pair (`compile_consuming_arg_list_moded` →
//! `FnCompiler::elide_vecget_span`; `emit_vec_get_core` skips the inc). It
//! DECLINES for every other shape: a `Fresh`-rooted vec-get, an `Owned`-param
//! position, a control-flow / let wrapped arg, a `NeverHeap` (unboxed) element.
//!
//! **These land GREEN — regression guards that PIN the now-sound behaviour.**
//! They are NOT defect repros. Any RED here means the review missed a real
//! defect (escalate to /dev backend); do NOT force it green.
//!
//! Design: `design/backend/ownership-codegen.md` §3.3 (the elision + its
//! decline boundary), §3.4/§3.5 (the D24 adaptation algebra / R2 value
//! wrapper — item 3). The escaping-projection soundness lesson (Sprint-61
//! read-proj → COW-release-root → use, which false-greened the release binary)
//! is `memory/feedback_verify_fix_not_symptom_absence.md`.
//!
//! Two assertion vocabularies, mirroring `tests/ownership_fences.rs`:
//!   (i)  OUTPUT-ORACLE — the observable result under the elision (analysis ON)
//!        is byte-identical to analysis OFF (`CRANELISP_NO_OWNERSHIP=1`). If the
//!        elision ever changed a value, ON≠OFF fails loudly. This is the
//!        soundness invariant for the decline gates and the headline alike.
//!   (ii) BALANCE — `CRANELISP_RC_STATS` alloc/dealloc imbalance is
//!        ITERATION-INDEPENDENT (N=50 vs N=1000): a per-crossing leak or a
//!        double-free (negative-scaling) scales with N, a fixed baseline does
//!        not. The escaping projections must materialize and release EXACTLY
//!        once; the elided borrow must not leak or over-free.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

/// Run a free-standing program in `--run` mode (the program self-imports; no
/// prelude file). `CRANELISP_NO_OWNERSHIP` is explicitly removed so an ambient
/// analysis-off env can never mask an ON-path defect.
fn run_program(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .run("user.cl")
        .user(src)
        .env_remove("CRANELISP_NO_OWNERSHIP")
        .output()
}

/// Run the same program with the analysis-off oracle switch set.
fn run_program_ownership_off(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .run("user.cl")
        .user(src)
        .env("CRANELISP_NO_OWNERSHIP", "1")
        .output()
}

/// OUTPUT-ORACLE: the program's observable behaviour (stdout + exit code) with
/// the projection-elision live MUST equal its behaviour with ownership analysis
/// off. The elision is an RC-traffic optimisation; it must never move a value.
fn assert_output_matches_ownership_off(src: &str, context: &str) -> helpers::e2e::CrOutput {
    let on = run_program(src);
    let off = run_program_ownership_off(src);
    assert_eq!(
        on.status.code(),
        off.status.code(),
        "[{context}] exit code diverged ON vs analysis-OFF \
         (elision changed observable behaviour — §3.3 soundness)\n\
         ON stdout:\n{}\nON stderr:\n{}\nOFF stdout:\n{}\nOFF stderr:\n{}",
        on.stdout,
        on.stderr,
        off.stdout,
        off.stderr
    );
    assert_eq!(
        on.stdout, off.stdout,
        "[{context}] stdout diverged ON vs analysis-OFF (elision changed \
         observable output — §3.3 soundness)"
    );
    on
}

/// Assert exit code equals `value % 256` (batch `main` returns `Pure Int`; the
/// process exit carries it, mod 256).
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

/// Parse the `allocs − deallocs` imbalance from the at-exit `[RC_STATS]` line.
fn rc_imbalance(stderr: &str) -> i64 {
    let line = stderr
        .lines()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("no [RC_STATS] line on stderr: {stderr}"));
    let field = |k: &str| -> i64 {
        line.split_whitespace()
            .find_map(|tok| tok.strip_prefix(&format!("{k}=")))
            .and_then(|v| v.parse().ok())
            .unwrap_or_else(|| panic!("no {k}= field in RC_STATS line: {line}"))
    };
    field("allocs") - field("deallocs")
}

/// BALANCE leg: run `template` (must contain `{N}`) at N=50 and N=1000 with
/// `CRANELISP_RC_STATS=1` and assert the imbalance is ITERATION-INDEPENDENT.
/// A per-crossing leak (materialize-but-never-release) or a per-crossing
/// double-free scales with N; a fixed module baseline does not. Tolerance
/// |delta| ≤ 2 matches `tests/ownership_fences.rs` (±1 at-exit stats jitter
/// under parallel suite load, N-independent).
fn assert_iteration_independent_imbalance(template: &str, context: &str) {
    let small = rc_imbalance(
        &Cranelisp::new()
            .run("user.cl")
            .user(&template.replace("{N}", "50"))
            .env("CRANELISP_RC_STATS", "1")
            .env_remove("CRANELISP_NO_OWNERSHIP")
            .output()
            .stderr,
    );
    let large = rc_imbalance(
        &Cranelisp::new()
            .run("user.cl")
            .user(&template.replace("{N}", "1000"))
            .env("CRANELISP_RC_STATS", "1")
            .env_remove("CRANELISP_NO_OWNERSHIP")
            .output()
            .stderr,
    );
    let delta = (large - small).abs();
    assert!(
        delta <= 2,
        "[{context}] alloc/dealloc imbalance scales with iteration count \
         (N=50 → {small}, N=1000 → {large}) — a per-crossing leak or \
         double-free at the projection seam (§3.3 balance leg)"
    );
}

// =============================================================================
// HEADLINE (positive) — the ONE shape the elision fires on. The F1
// machinery-tax class `(reader (vec-get g i))`: a direct vec-get of a named
// binding, heap-typed element, passed DIRECTLY into a Borrowed param. The
// inc+dec pair collapses; the observable result is unchanged (oracle) and the
// balance is iteration-independent (no leak from the skipped inc; no over-free).
// =============================================================================

const ELIDE_TEMPLATE: &str = "(import [primitives [*]])\n\
    (defn read-str [:String s] (str-len s))\n\
    (defn probe [v] (read-str (vec-get v 0)))\n\
    (defn spin [:Int n :Int acc v]\n\
    \x20 (if (eq-i64 n 0) acc\n\
    \x20   (spin (sub-i64 n 1) (add-i64 acc (probe v)) v)))\n\
    (defn main [] (Pure (spin {N} 0 [\"hello\" \"bb\"])))\n";

// spec: design/backend/ownership-codegen.md §3.3 — headline elision: a direct
// vec-get of a named binding into a Borrowed param. Output correct AND
// identical to analysis-off (the collapse is invisible to the result).
#[test]
fn elide_direct_vecget_into_borrowed_param_headline() {
    let src = ELIDE_TEMPLATE.replace("{N}", "1000");
    let out = assert_output_matches_ownership_off(&src, "headline elide");
    assert_exit_value(out, 1000 * 5);
}

// spec: design/backend/ownership-codegen.md §3.3 — headline balance leg: the
// collapsed inc must not leak and the retained root's single release must not
// double-free (imbalance iteration-independent).
#[test]
fn elide_headline_balance_iteration_independent() {
    assert_iteration_independent_imbalance(ELIDE_TEMPLATE, "headline elide");
}

// =============================================================================
// GATE-DECLINE (negative) — each gate of the predicate independently declines.
// The elision must NOT fire, and the observable result stays correct + oracle-
// identical. If a future edit widened any gate to admit these, the value would
// be unchanged (still a valid output) but the balance / perturbation guards
// below would catch the resulting UAF. The oracle here pins that the DECLINE
// path is behaviourally the conservative one.
// =============================================================================

// spec: design/backend/ownership-codegen.md §3.3 — DECLINE: an `Owned`-param
// position (the callee RETURNS its argument → escapes). The projection is an
// ordinary owned temporary here; eliding it would leave the escaped element
// unreferenced. Correct output, oracle-identical.
#[test]
fn decline_owned_position_callee_returns_arg() {
    let src = "(import [primitives [*]])\n\
        (defn keep [x] x)\n\
        (defn main [] (Pure (str-len (keep (vec-get [\"hello\" \"bb\"] 0)))))\n";
    let out = assert_output_matches_ownership_off(src, "decline owned-position");
    assert_exit_value(out, 5);
}

// spec: design/backend/ownership-codegen.md §3.3 — DECLINE: a `NeverHeap`
// (unboxed Int) element. RC never touches a scalar; the heap-typed-element
// gate declines. Correct output, oracle-identical.
#[test]
fn decline_neverheap_int_element() {
    let src = "(import [primitives [*]])\n\
        (defn add1 [:Int x] (add-i64 x 1))\n\
        (defn probe [v] (add1 (vec-get v 0)))\n\
        (defn main [] (Pure (probe [10 20 30])))\n";
    let out = assert_output_matches_ownership_off(src, "decline NeverHeap");
    assert_exit_value(out, 11);
}

// spec: design/backend/ownership-codegen.md §3.3 — DECLINE: a `Fresh`-rooted
// vec-get. The root is an inline vec literal (no named binding / no provenance
// site fact), so the projection has no root to retain across the call — the
// named-root gate declines. Correct output, oracle-identical.
#[test]
fn decline_fresh_rooted_vecget() {
    let src = "(import [primitives [*]])\n\
        (defn read-str [:String s] (str-len s))\n\
        (defn main [] (Pure (read-str (vec-get [\"hello\" \"bb\"] 0))))\n";
    let out = assert_output_matches_ownership_off(src, "decline Fresh-rooted");
    assert_exit_value(out, 5);
}

// spec: design/backend/ownership-codegen.md §3.3 — DECLINE: a control-flow-
// wrapped arg. `(if flag (vec-get v 0) other)` is not a DIRECT vec-get Apply in
// argument position, so the direct-projection gate declines. Correct output,
// oracle-identical.
#[test]
fn decline_control_flow_wrapped_arg() {
    let src = "(import [primitives [*]])\n\
        (defn read-str [:String s] (str-len s))\n\
        (defn probe [v flag] (read-str (if flag (vec-get v 0) \"zzz\")))\n\
        (defn main [] (Pure (probe [\"hello\" \"bb\"] true)))\n";
    let out = assert_output_matches_ownership_off(src, "decline if-wrapped");
    assert_exit_value(out, 5);
}

// spec: design/backend/ownership-codegen.md §3.3 — DECLINE: a let-bound
// projection. The arg is a bare `Var`, not a direct vec-get Apply — the gate
// declines. Correct output, oracle-identical.
#[test]
fn decline_let_bound_projection() {
    let src = "(import [primitives [*]])\n\
        (defn read-str [:String s] (str-len s))\n\
        (defn probe [v] (let [x (vec-get v 0)] (read-str x)))\n\
        (defn main [] (Pure (probe [\"hello\" \"bb\"])))\n";
    let out = assert_output_matches_ownership_off(src, "decline let-bound");
    assert_exit_value(out, 5);
}

// =============================================================================
// ESCAPING-PROJECTION NEGATIVES — the false-green class. A borrowed view that
// escapes the producing function (returned, stored) has no protective
// reference; the mechanism MUST decline the elision and materialize instead, so
// the escaped element is retained and released exactly once. Sustained +
// balance-checked; the perturbation guard below is the exact false-green
// witness.
// =============================================================================

const ESCAPE_RETURN_TEMPLATE: &str = "(import [primitives [*]])\n\
    (defn get0 [v] (vec-get v 0))\n\
    (defn spin [:Int n :Int acc v]\n\
    \x20 (if (eq-i64 n 0) acc\n\
    \x20   (spin (sub-i64 n 1) (add-i64 acc (str-len (get0 v))) v)))\n\
    (defn main [] (Pure (spin {N} 0 [\"hello\" \"bb\"])))\n";

// spec: design/backend/ownership-codegen.md §3.3 — a projection RETURNED out of
// the projecting fn escapes; the elision declines (return_is_fresh_by_summary
// stays Fresh-only, a ProjectionOf result keeps its materialization). The
// returned element reads correctly across 1000 crossings (UAF side) and the
// root stays intact. Oracle-identical.
#[test]
fn escaping_projection_returned_survives_sustained() {
    let src = ESCAPE_RETURN_TEMPLATE.replace("{N}", "1000");
    let out = assert_output_matches_ownership_off(&src, "escape-return");
    assert_exit_value(out, 1000 * 5);
}

// spec: design/backend/ownership-codegen.md §3.3 — double-free / leak twin: the
// escaping projection is materialized and released EXACTLY once (imbalance
// iteration-independent). A skipped materialization would double-free
// (negative-scaling); a leaked one scales positively.
#[test]
fn escaping_projection_returned_balance_iteration_independent() {
    assert_iteration_independent_imbalance(ESCAPE_RETURN_TEMPLATE, "escape-return");
}

const ESCAPE_STORE_TEMPLATE: &str = "(import [primitives [*]])\n\
    (defn spin [:Int n :Int acc v]\n\
    \x20 (if (eq-i64 n 0) acc\n\
    \x20   (spin (sub-i64 n 1)\n\
    \x20     (add-i64 acc (str-len (vec-get (vec-push [] (vec-get v 0)) 0))) v)))\n\
    (defn main [] (Pure (spin {N} 0 [\"hello\" \"bb\"])))\n";

// spec: design/backend/ownership-codegen.md §3.3 — a projection STORED into a
// fresh escaping Vec (`vec-push [] (vec-get v 0)`) escapes into the container;
// the store materializes (values read back correctly), root intact, balance
// iteration-independent. Oracle-identical.
#[test]
fn escaping_projection_stored_into_vec_survives_sustained() {
    let src = ESCAPE_STORE_TEMPLATE.replace("{N}", "500");
    let out = assert_output_matches_ownership_off(&src, "escape-store");
    assert_exit_value(out, 500 * 5);
    assert_iteration_independent_imbalance(ESCAPE_STORE_TEMPLATE, "escape-store");
}

// =============================================================================
// THE SPRINT-61 FALSE-GREEN CLASS — read a projection, COW-release/mutate the
// root, then use the projection. This is the exact shape that false-greened the
// release binary (producer-side elision propagated a borrowed view past the
// root's COW; under lenient eval a sibling's free raced the un-referenced read).
// The landed consumer-driven mechanism declines it; the projection must read
// its OLD value after the root's COW write.
// =============================================================================

const SPRINT61_SRC: &str = "(import [primitives [*]])\n\
    (defn probe []\n\
    \x20 (let [v [\"aa\" \"bbb\"]\n\
    \x20       e (vec-get v 0)\n\
    \x20       w (vec-set v 0 \"cccc\")]\n\
    \x20   (add-i64 (str-len e) (str-len (vec-get w 0)))))\n\
    (defn main [] (Pure (probe)))\n";

// spec: spec/12-runtime.md §12.3.1 — heap values MUST stay live while
// reachable: the projected element `e` (read BEFORE the COW write) must still
// read its old value "aa" (2) after `(vec-set v 0 "cccc")` copies-on-write the
// root; `w[0]` reads the new "cccc" (4). Small + CLIF-inspectable. Oracle-
// identical.
#[test]
fn sprint61_read_projection_cow_release_root_then_use() {
    let out = assert_output_matches_ownership_off(SPRINT61_SRC, "sprint61 cow-release");
    // e = "aa" (2) survives the COW; w[0] = "cccc" (4).
    assert_exit_value(out, 2 + 4);
}

// spec: spec/12-runtime.md §12.3.1 — the perturbation witness for the exact
// false-green class (`memory/feedback_verify_fix_not_symptom_absence.md`):
// `MALLOC_PERTURB_` fills freed chunks with a byte pattern, so if the mechanism
// wrongly elided/released the projection `e` before its post-COW use, `str-len
// e` would read poisoned bytes (garbage length) instead of 2. A stable exit 6
// under perturbation is behavioural evidence the projection stayed live — not a
// balance-passing false-green. Committed as a self-contained guard (the
// env-var is set on the spawned child); the full same-seed f4_sudoku
// perturbation sweep is the manual witness recorded in commit e51629f.
#[test]
fn sprint61_read_projection_cow_release_under_malloc_perturb() {
    Cranelisp::new()
        .run("user.cl")
        .user(SPRINT61_SRC)
        .env("MALLOC_PERTURB_", "165")
        .env_remove("CRANELISP_NO_OWNERSHIP")
        .output()
        .assert_exit(2 + 4);
}

// =============================================================================
// 0522 fn-as-value WRAPPER — a moded callee whose result is `ProjectionOf`
// (`get0 [v] (vec-get v 0)`, result ProjectionOf(0)) used as a FIRST-CLASS
// closure value through a HOF. The value-use synthesizes the D24 wrapper
// (`emit_d24_adaptation`, §3.4/§3.5); the FIXME-0522 reconcile made the wrapper
// DROP its ProjectionOf-result inc (the moded body already returns an owned
// reference, so wrapper+callee can never both inc). The returned element must
// retain exactly one owned reference — no leak, no premature free. Previously
// ZERO behavioural coverage.
// =============================================================================

const FN_AS_VALUE_TEMPLATE: &str = "(import [primitives [*]])\n\
    (defn get0 [v] (vec-get v 0))\n\
    (defn apply-it [f v] (f v))\n\
    (defn spin [:Int n :Int acc v]\n\
    \x20 (if (eq-i64 n 0) acc\n\
    \x20   (spin (sub-i64 n 1) (add-i64 acc (str-len (apply-it get0 v))) v)))\n\
    (defn main [] (Pure (spin {N} 0 [\"hello\" \"bb\"])))\n";

// spec: design/backend/ownership-codegen.md §3.5 — the R2 value wrapper for a
// `ProjectionOf`-result callee used as a closure value: the element returned
// through the wrapper reads correctly and survives. Oracle-identical.
#[test]
fn fn_as_value_projectionof_wrapper_returns_element() {
    let src = FN_AS_VALUE_TEMPLATE.replace("{N}", "1000");
    let out = assert_output_matches_ownership_off(&src, "fn-as-value ProjectionOf wrapper");
    assert_exit_value(out, 1000 * 5);
}

// spec: design/backend/ownership-codegen.md §3.4 — the adaptation algebra must
// net exactly one owned reference at the wrapper edge: the FIXME-0522 reconcile
// dropped the wrapper's ProjectionOf inc so callee-materialization and wrapper-
// adaptation cannot BOTH inc (double-count → leak) nor both omit (→ premature
// free). Balance iteration-independent proves neither over- nor under-counts.
#[test]
fn fn_as_value_projectionof_wrapper_balance_iteration_independent() {
    assert_iteration_independent_imbalance(
        FN_AS_VALUE_TEMPLATE,
        "fn-as-value ProjectionOf wrapper",
    );
}
