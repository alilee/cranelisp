// rc_escape_release_0763.rs — S115 W3c, FIXME 0763 pin batch (all GREEN).
//
// The W3/W3b backend RC-release batch fixed five distinct heap-value leaks whose
// common mechanism was `is_fresh_construction` not covering the box-minting node
// kinds: a freshly-minted heap value that ESCAPES its defining frame (returned
// through a let, out of a curried application, or captured into another closure)
// was never released, leaking one or two objects per call. The unit tier pins the
// classifier at its seam; these are the second tier — the faces that are only
// observable end-to-end, as a per-iteration alloc/dealloc imbalance under
// `CRANELISP_RC_STATS=1`.
//
// Provenance: FIXME 0763 (`/dev`(cranelisp-backend), S115 W3b) records the shapes
// and the exact pre-/post-fix numbers, all reproduced verbatim here at W3b HEAD:
//
//   A  applied immediately                    201/201
//   B  curried value let-bound, same frame     201/201
//   C  curried value RETURNED from its frame   201/201   (was 201/1)
//   C2 as C, target closure captures a String  301/301   (was 301/1)
//   D  plain lambda returned through TWO lets  301/301   (was 301/101)
//   E  VecLit returned through one let         201/201   (was 201/101)
//   F  lambda capturing another closure        301/301   (was 301/1)
//   G  (Pure (peek (Gr [5 5]))) — 0753          3/3      (was ON 3/2, OFF 3/3)
//   G2 the String-field twin of G               3/3
//
// These are REGRESSION GUARDS on freshly-fixed behaviour, not defect repros: the
// assertion is EXACT balance (`allocs == deallocs`), which is what
// spec/12-runtime.md §12.3.1 requires and what a leak — or an over-correction
// into a premature free, the opposite polarity — breaks.
//
// Both toggle states are pinned on every shape (`CRANELISP_NO_OWNERSHIP` set and
// unset): the 0753 signature was a toggle ASYMMETRY (ON 3/2, OFF 3/3), so a pin
// on one toggle alone would have missed it. The A-group (0749, the curry/escape
// axis) additionally runs through `--link` as well as `--run` — a
// REPL/`--run`/`--link` divergence is always a defect and the escape axis is
// exactly where a mode-specific release would hide.
//
// Serial (`CRANELISP_NO_LENIENT=1` — no sparks, per the RC-tests-run-serially
// convention). PrimitivesOnly, free-standing (no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

/// The 100-iteration driver: calls `one` in a tail loop and accumulates, so a
/// per-call leak shows as ~N missing deallocs rather than an O(1) residue.
const DRIVER: &str = "(defn go [n acc] (if (eq-i64 n 0) acc \
     (go (sub-i64 n 1) (add-i64 acc (one)))))\n\
     (defn main [] (Pure (go 100 0)))\n";

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Mode {
    Run,
    LinkThenRun,
}

/// One measurement: compile+run `src` and return `(allocs, deallocs, exit_code)`.
///
/// The LAST `[RC_STATS]` line is the program's — under `--link` the compiler
/// process emits its own (0/0) line first, and taking the first would silently
/// measure the linker instead of the linked program.
fn rc_balance(src: &str, mode: Mode, ownership_off: bool) -> (i64, i64, Option<i32>) {
    let mut b = Cranelisp::new().with_prelude(PreludeVariant::PrimitivesOnly);
    b = match mode {
        Mode::Run => b.run("user.cl"),
        Mode::LinkThenRun => b.link_then_run("user.cl"),
    };
    b = b
        .user(src)
        .env("CRANELISP_RC_STATS", "1")
        .env("CRANELISP_NO_LENIENT", "1");
    if ownership_off {
        b = b.env("CRANELISP_NO_OWNERSHIP", "1");
    }
    let out = b.output();
    let line = out
        .stderr
        .lines()
        .rev()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("no [RC_STATS] line ({mode:?}):\n{}", out.stderr))
        .to_string();
    let field = |k: &str| -> i64 {
        line.split_whitespace()
            .find_map(|t| t.strip_prefix(k).and_then(|v| v.parse().ok()))
            .unwrap_or_else(|| panic!("no {k} in: {line}"))
    };
    (field("allocs="), field("deallocs="), out.status.code())
}

/// Assert EXACT balance for `src` across both ownership-toggle states in every
/// requested mode, and that the program produced `expect_exit` (so a shape that
/// silently stopped running cannot pass by allocating nothing).
fn assert_balanced(shape: &str, src: &str, expect_exit: i32, modes: &[Mode]) {
    for &mode in modes {
        for ownership_off in [false, true] {
            let (allocs, deallocs, code) = rc_balance(src, mode, ownership_off);
            let toggle = if ownership_off {
                "CRANELISP_NO_OWNERSHIP=1"
            } else {
                "ownership analysis ON"
            };
            assert_eq!(
                allocs, deallocs,
                "{shape} ({mode:?}, {toggle}) MUST balance exactly: allocs={allocs} \
                 deallocs={deallocs} (residue {}). A freshly-minted heap value that \
                 escapes its defining frame must still be released.",
                allocs - deallocs
            );
            assert_eq!(
                code,
                Some(expect_exit),
                "{shape} ({mode:?}, {toggle}) must still compute its value"
            );
            // Non-vacuity: a measurement of 0/0 balances trivially. Every shape
            // here allocates, so a zero count means the stats line measured the
            // wrong process (the `--link` compiler emits its own 0/0 line).
            assert!(
                allocs > 0,
                "{shape} ({mode:?}, {toggle}) measured 0 allocs — the balance \
                 assertion would be vacuous"
            );
        }
    }
}

const BOTH_MODES: &[Mode] = &[Mode::Run, Mode::LinkThenRun];
const RUN_ONLY: &[Mode] = &[Mode::Run];

// =============================================================================
// A group — FIXME 0749, the curry-the-local-closure arm across the escape axis
// =============================================================================

// A — the curried value is applied in the SAME expression. This arm was the only
// one verified by the W3 change-set; it was already balanced and is the control
// that proves the fix did not over-correct the non-escaping face into an
// under-count.
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
#[test]
fn curried_local_closure_applied_immediately_balances() {
    let src = format!(
        "(defn one [] (let [g (fn [a b] (add-i64 a b))] ((g 1) 2)))\n{DRIVER}"
    );
    assert_balanced("A (curry applied immediately)", &src, 44, BOTH_MODES);
}

// B — the curried value is let-bound and applied in the same frame (it never
// escapes). Balanced before and after; the second control on the escape axis.
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
#[test]
fn curried_local_closure_let_bound_in_same_frame_balances() {
    let src = format!(
        "(defn one [] (let [g (fn [a b] (add-i64 a b))] (let [h (g 1)] (h 2))))\n{DRIVER}"
    );
    assert_balanced("B (curry let-bound in frame)", &src, 44, BOTH_MODES);
}

// C — the curried value is RETURNED from its defining frame. This is the arm that
// leaked: 201 allocs / 1 dealloc before the W3b fix — every escaping partial
// application leaked, unboundedly with the loop count.
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-backend rc_emission.rs::is_fresh_construction (escaping curried partial application never released) found=S115 owner=/dev
#[test]
fn curried_local_closure_escaping_its_frame_balances() {
    let src = format!(
        "(defn mk [] (let [g (fn [a b] (add-i64 a b))] (g 1)))\n\
         (defn one [] ((mk) 2))\n{DRIVER}"
    );
    assert_balanced("C (curried value escapes)", &src, 44, BOTH_MODES);
}

// C2 — as C, but the target closure captures a String, so the escaping value owns
// a nested heap object too: 301 allocs / 1 dealloc before the fix. Guards that the
// release reaches the capture payload, not just the closure box.
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-backend rc_emission.rs::is_fresh_construction (escaping curried partial application with a String capture) found=S115 owner=/dev
#[test]
fn curried_escaping_closure_with_string_capture_balances() {
    let src = format!(
        "(defn mk [] (let [s \"hello\"] \
           (let [g (fn [a b] (add-i64 (add-i64 a b) (str-len s)))] (g 1))))\n\
         (defn one [] ((mk) 2))\n{DRIVER}"
    );
    assert_balanced("C2 (escaping curry, String capture)", &src, 32, BOTH_MODES);
}

// =============================================================================
// B group — the same defect with NO curry involved. `is_fresh_construction` did
// not cover the box-minting node kinds, so each of these is an independent face
// of ONE fix and guards a different arm of it.
// =============================================================================

// D — a plain lambda returned through TWO lets: 301/101 before the fix (the
// captured String and the closure box leaked per call; the outer `t` binding was
// released). No curry, no partial application.
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-backend rc_emission.rs::is_fresh_construction (Lambda returned through nested lets) found=S115 owner=/dev
#[test]
fn lambda_returned_through_nested_lets_balances() {
    let src = format!(
        "(defn mk [] (let [s \"hello\"] (let [t \"world\"] \
           (fn [b] (add-i64 b (str-len s))))))\n\
         (defn one [] ((mk) 2))\n{DRIVER}"
    );
    assert_balanced("D (lambda through two lets)", &src, 188, RUN_ONLY);
}

// E — a VecLit returned through one let: 201/101 before the fix. The returned
// value is a vec, not a closure — the leaking node kind is the literal
// construction itself, which is why a closure-shaped fix would have missed it.
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-backend rc_emission.rs::is_fresh_construction (VecLit returned through a let) found=S115 owner=/dev
#[test]
fn vec_literal_returned_through_let_balances() {
    let src = format!(
        "(defn mk [] (let [s \"hello\"] [1 2 (str-len s)]))\n\
         (defn one [] (vec-len (mk)))\n{DRIVER}"
    );
    assert_balanced("E (VecLit through a let)", &src, 44, RUN_ONLY);
}

// F — a lambda capturing ANOTHER closure, both escaping: 301/1 before the fix.
// The escaping value's capture is itself heap and itself fresh, so this arm pins
// that the release recurses through a closure-valued capture.
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-backend rc_emission.rs::is_fresh_construction (lambda capturing a closure, both escaping) found=S115 owner=/dev
#[test]
fn lambda_capturing_a_closure_balances() {
    let src = format!(
        "(defn mk [] (let [s \"hello\"] \
           (let [g (fn [b] (add-i64 b (str-len s)))] (fn [c] (g c)))))\n\
         (defn one [] ((mk) 2))\n{DRIVER}"
    );
    assert_balanced("F (lambda capturing a closure)", &src, 188, RUN_ONLY);
}

// =============================================================================
// C group — FIXME 0753, the toggle-ON constant residual
// =============================================================================

// G — the 0753 reduced shape. No loop, no TCO, no `vec-set`: constructing an ADT
// that wraps a vec literal and passing it to a function that ignores it left ONE
// object unfreed with ownership analysis ON (3 allocs / 2 deallocs) while the
// toggle-OFF path balanced. The toggle ASYMMETRY was the signature, so both
// states are asserted here and both must be exact.
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
// defect: class=rc-miscount locus=crates/cranelisp-backend type-directed rc-dec emission (ADT-wrapped vec argument, ownership-ON residual) found=S115 owner=/dev
#[test]
fn adt_wrapped_vec_argument_balances_both_toggles() {
    let src = "(deftype G2 (Gr [cells]))\n\
               (defn peek [g] 7)\n\
               (defn main [] (Pure (peek (Gr [5 5]))))\n";
    assert_balanced("G (0753 reduced shape)", src, 7, RUN_ONLY);
}

// G2 — the String-field twin of G: the ADT wraps a String instead of a vec and the
// callee actually matches on it. Balanced in both toggles; the twin fixture that
// would diverge if the release became keyed on the vec shape rather than on the
// owning type.
// spec: spec/12-runtime.md §12.3.1 — heap values are freed when no longer reachable.
#[test]
fn adt_wrapped_string_argument_balances_both_toggles() {
    let src = "(deftype G2 (Gr [s]))\n\
               (defn peek [g] (match g [(Gr s) (str-len s)]))\n\
               (defn main [] (Pure (peek (Gr \"hi\"))))\n";
    assert_balanced("G2 (0753 String-field twin)", src, 2, RUN_ONLY);
}
