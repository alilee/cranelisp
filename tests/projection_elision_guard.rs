//! Projection lifetime and counting guards under uniform reference counting.
//!
//! Fixtures cover direct, wrapped, returned and stored Vec projections, a
//! projection retained across COW, and a function used through a closure value.
//! Output is compared with moves off (`CRANELISP_NO_OWNERSHIP=1`); repeated
//! crossings must have iteration-independent allocation imbalance. The COW
//! witness also runs with freed-memory perturbation to expose a premature free.
//! These assertions observe values and lifetime, not a particular elision.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

fn run_program(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .run("user.cl")
        .user(src)
        .env_remove("CRANELISP_NO_OWNERSHIP")
        .output()
}

fn run_program_ownership_off(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .run("user.cl")
        .user(src)
        .env("CRANELISP_NO_OWNERSHIP", "1")
        .output()
}

fn assert_output_matches_ownership_off(src: &str, context: &str) -> helpers::e2e::CrOutput {
    let on = run_program(src);
    let off = run_program_ownership_off(src);
    assert_eq!(
        on.status.code(),
        off.status.code(),
        "[{context}] exit code diverged ON vs analysis-OFF \
         (moves changed observable behaviour — uniform counting §2.1)\n\
         ON stdout:\n{}\nON stderr:\n{}\nOFF stdout:\n{}\nOFF stderr:\n{}",
        on.stdout,
        on.stderr,
        off.stdout,
        off.stderr
    );
    assert_eq!(
        on.stdout, off.stdout,
        "[{context}] stdout diverged ON vs analysis-OFF (moves changed \
         observable output — uniform counting §2.1)"
    );
    on
}

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
         double-free at projection consumption (uniform counting §1)"
    );
}

const ELIDE_TEMPLATE: &str = "(import [primitives [*]])\n\
    (defn read-str [:String s] (str-len s))\n\
    (defn probe [v] (read-str (vec-get v 0)))\n\
    (defn spin [:Int n :Int acc v]\n\
    \x20 (if (eq-i64 n 0) acc\n\
    \x20   (spin (sub-i64 n 1) (add-i64 acc (probe v)) v)))\n\
    (defn main [] (Pure (spin {N} 0 [\"hello\" \"bb\"])))\n";

// spec: design/backend/uniform-counting.md §2.1 — Direct projection into a read-only callee agrees with moves off.
#[test]
fn elide_direct_vecget_into_borrowed_param_headline() {
    let src = ELIDE_TEMPLATE.replace("{N}", "1000");
    let out = assert_output_matches_ownership_off(&src, "headline elide");
    assert_exit_value(out, 1000 * 5);
}

// spec: design/backend/uniform-counting.md §1 — Repeated projection consumption has no per-crossing imbalance.
#[test]
fn elide_headline_balance_iteration_independent() {
    assert_iteration_independent_imbalance(ELIDE_TEMPLATE, "headline elide");
}

// spec: design/backend/uniform-counting.md §1 — A returned projection retains its owned reference through the caller.
#[test]
fn decline_owned_position_callee_returns_arg() {
    let src = "(import [primitives [*]])\n\
        (defn keep [x] x)\n\
        (defn main [] (Pure (str-len (keep (vec-get [\"hello\" \"bb\"] 0)))))\n";
    let out = assert_output_matches_ownership_off(src, "decline owned-position");
    assert_exit_value(out, 5);
}

// spec: design/backend/uniform-counting.md §2.1 — Scalar projection output agrees with moves off.
#[test]
fn decline_neverheap_int_element() {
    let src = "(import [primitives [*]])\n\
        (defn add1 [:Int x] (add-i64 x 1))\n\
        (defn probe [v] (add1 (vec-get v 0)))\n\
        (defn main [] (Pure (probe [10 20 30])))\n";
    let out = assert_output_matches_ownership_off(src, "decline NeverHeap");
    assert_exit_value(out, 11);
}

// spec: design/backend/uniform-counting.md §1 — A projected element survives consumption of its temporary Vec root.
#[test]
fn decline_fresh_rooted_vecget() {
    let src = "(import [primitives [*]])\n\
        (defn read-str [:String s] (str-len s))\n\
        (defn main [] (Pure (read-str (vec-get [\"hello\" \"bb\"] 0))))\n";
    let out = assert_output_matches_ownership_off(src, "decline Fresh-rooted");
    assert_exit_value(out, 5);
}

// spec: design/backend/uniform-counting.md §2.1 — A branch-selected projection agrees with moves off.
#[test]
fn decline_control_flow_wrapped_arg() {
    let src = "(import [primitives [*]])\n\
        (defn read-str [:String s] (str-len s))\n\
        (defn probe [v flag] (read-str (if flag (vec-get v 0) \"zzz\")))\n\
        (defn main [] (Pure (probe [\"hello\" \"bb\"] true)))\n";
    let out = assert_output_matches_ownership_off(src, "decline if-wrapped");
    assert_exit_value(out, 5);
}

// spec: design/backend/uniform-counting.md §1 — A let-bound projection owns its reference until consumed.
#[test]
fn decline_let_bound_projection() {
    let src = "(import [primitives [*]])\n\
        (defn read-str [:String s] (str-len s))\n\
        (defn probe [v] (let [x (vec-get v 0)] (read-str x)))\n\
        (defn main [] (Pure (probe [\"hello\" \"bb\"])))\n";
    let out = assert_output_matches_ownership_off(src, "decline let-bound");
    assert_exit_value(out, 5);
}

const ESCAPE_RETURN_TEMPLATE: &str = "(import [primitives [*]])\n\
    (defn get0 [v] (vec-get v 0))\n\
    (defn spin [:Int n :Int acc v]\n\
    \x20 (if (eq-i64 n 0) acc\n\
    \x20   (spin (sub-i64 n 1) (add-i64 acc (str-len (get0 v))) v)))\n\
    (defn main [] (Pure (spin {N} 0 [\"hello\" \"bb\"])))\n";

// spec: design/backend/uniform-counting.md §1 — Returned elements survive repeated function crossings.
#[test]
fn escaping_projection_returned_survives_sustained() {
    let src = ESCAPE_RETURN_TEMPLATE.replace("{N}", "1000");
    let out = assert_output_matches_ownership_off(&src, "escape-return");
    assert_exit_value(out, 1000 * 5);
}

// spec: design/backend/uniform-counting.md §1 — Returned elements are consumed exactly once at each crossing.
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

// spec: design/backend/uniform-counting.md §1 — Stored elements stay live and balance independently of iteration count.
#[test]
fn escaping_projection_stored_into_vec_survives_sustained() {
    let src = ESCAPE_STORE_TEMPLATE.replace("{N}", "500");
    let out = assert_output_matches_ownership_off(&src, "escape-store");
    assert_exit_value(out, 500 * 5);
    assert_iteration_independent_imbalance(ESCAPE_STORE_TEMPLATE, "escape-store");
}

const SPRINT61_SRC: &str = "(import [primitives [*]])\n\
    (defn probe []\n\
    \x20 (let [v [\"aa\" \"bbb\"]\n\
    \x20       e (vec-get v 0)\n\
    \x20       w (vec-set v 0 \"cccc\")]\n\
    \x20   (add-i64 (str-len e) (str-len (vec-get w 0)))))\n\
    (defn main [] (Pure (probe)))\n";

// spec: spec/12-runtime.md §12.3.1 — An independently owned projection keeps its old value across root COW.
#[test]
fn sprint61_read_projection_cow_release_root_then_use() {
    let out = assert_output_matches_ownership_off(SPRINT61_SRC, "sprint61 cow-release");
    assert_exit_value(out, 2 + 4);
}

// spec: spec/12-runtime.md §12.3.1 — The pre-COW element survives even when freed memory is poisoned.
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

const FN_AS_VALUE_TEMPLATE: &str = "(import [primitives [*]])\n\
    (defn get0 [v] (vec-get v 0))\n\
    (defn apply-it [f v] (f v))\n\
    (defn spin [:Int n :Int acc v]\n\
    \x20 (if (eq-i64 n 0) acc\n\
    \x20   (spin (sub-i64 n 1) (add-i64 acc (str-len (apply-it get0 v))) v)))\n\
    (defn main [] (Pure (spin {N} 0 [\"hello\" \"bb\"])))\n";

// spec: design/backend/uniform-counting.md §3.3 — A function-value wrapper forwards owned arguments and returns a live element.
#[test]
fn fn_as_value_projectionof_wrapper_returns_element() {
    let src = FN_AS_VALUE_TEMPLATE.replace("{N}", "1000");
    let out = assert_output_matches_ownership_off(&src, "fn-as-value ProjectionOf wrapper");
    assert_exit_value(out, 1000 * 5);
}

// spec: design/backend/uniform-counting.md §3.3 — The function-value wrapper does not add per-crossing imbalance.
#[test]
fn fn_as_value_projectionof_wrapper_balance_iteration_independent() {
    assert_iteration_independent_imbalance(
        FN_AS_VALUE_TEMPLATE,
        "fn-as-value ProjectionOf wrapper",
    );
}
