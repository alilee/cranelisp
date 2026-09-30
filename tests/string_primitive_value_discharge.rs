//! String extern primitives called through each backend path (ACT-0974;
//! S122 K2).
//!
//! The only-read primitives' declarations borrow their arguments, while the
//! extern shims consume them. A call through a function value goes through
//! the GOT wrapper, so a doubled or missing discharge there would show against
//! a direct call. The pair differs only in whether each of the six primitives
//! is called directly or through `call1`/`call2`. Both strings stay live after
//! every call, so an early release meets a freed block under the armed
//! `CRANELISP_RC_DEC_CHECK` before the program's own final release.
//!
//! The SI cells extend the same question to `string-identity` and to the
//! other paths that choose an extern's argument convention: a temporary
//! argument, a returned result, `Display.show` dispatch, an `Owned` extern as a
//! value, and auto-curry (`tests/plan/s122-evidence-delta.md`, ACT-0974
//! prepared delta). Each is a marginal pair whose halves differ in one respect.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;
use helpers::marginal::{Child, Marginal, MarginalPair};

/// Run `n`'s definition with `s` live after it and the seam checks armed:
/// exit 8 (`str-len` of "abcd", twice) and no seam violation on stderr.
fn str_len_releases_once(label: &str, n: &str) {
    let out = Cranelisp::new()
        .file(
            "user.cl",
            &format!(
                "(import [primitives [Pure add-i64 str-concat str-len]])\n\
                 (defn call1 [f s] (f s))\n\
                 (defn user-len [s] (str-len s))\n\
                 (defn main []\n\
                   (let [s (str-concat \"ab\" \"cd\")\n\
                         n {n}]\n\
                     (Pure (add-i64 n (str-len s)))))\n"
            ),
        )
        .run("user.cl")
        .env("CRANELISP_RC_DEC_CHECK", "1")
        .output();
    assert!(
        out.status.code() == Some(8) && !out.stderr.contains("SEAM VIOLATION"),
        "{label}: the String argument must be released once, after its last \
         read (exit 8, no seam violation)\n--- exit {:?}\n--- stdout:\n{}\n\
         --- stderr:\n{}",
        out.status.code(),
        out.stdout,
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.3.1 — `str-len` (spec/appendix-a-builtins.md
// §A.3) called as a function value releases its argument exactly once.
//
// On 2026-09-30 (source `f0d1006f…`) the subject stopped at
// `consume_shallow: PRECHECK … the target was already released`. The two
// controls below pass the same predicate. Attribution is QA's (ACT-0974); the
// filed source-read candidate is the GOT wrapper's `Mode::Borrowed` discharge
// beside the consuming extern shim.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/fn_as_value.rs::emit_d24_adaptation found=S122 owner=/dev
#[test]
fn str_len_as_function_value_releases_its_argument_once() {
    str_len_releases_once("(call1 str-len s)", "(call1 str-len s)");
}

// spec: spec/appendix-a-builtins.md §A.3 Primitive Functions (Host-Implemented)
// — the direct-call control for the `str-len` function-value cell.
#[test]
fn str_len_direct_call_releases_its_argument_once() {
    str_len_releases_once("(str-len s)", "(str-len s)");
}

// spec: spec/12-runtime.md §12.3.1 — the same `call1` path over a user-defined
// borrowing function releases its argument once; the control that separates a
// primitive value from function-value calls in general.
#[test]
fn user_function_value_releases_its_argument_once() {
    str_len_releases_once("(call1 user-len s)", "(call1 user-len s)");
}

fn program(calls: [&str; 6]) -> Child {
    let [len, eq, neq, starts, ends, contains] = calls;
    Child::new(&format!(
        "(import [primitives [Pure add-i64 str-concat str-len str-eq neq-string\n\
                              starts-with? ends-with? contains?]])\n\
         (defn call1 [f s] (f s))\n\
         (defn call2 [f a b] (f a b))\n\
         (defn b2i [b] (if b 1 0))\n\
         (defn main []\n\
           (let [s (str-concat \"ab\" \"cd\")\n\
                 t (str-concat \"ab\" \"\")\n\
                 n (add-i64 {len}\n\
                   (add-i64 (b2i {eq})\n\
                   (add-i64 (b2i {neq})\n\
                   (add-i64 (b2i {starts})\n\
                   (add-i64 (b2i {ends}) (b2i {contains}))))))]\n\
             (Pure (add-i64 n (add-i64 (str-len s) (str-len t))))))\n"
    ))
    .env("CRANELISP_RC_DEC_CHECK", "1")
}

// spec: spec/12-runtime.md §12.3.1 — `str-len`, `str-eq`, `neq-string`,
// `starts-with?`, `ends-with?` and `contains?` (spec/appendix-a-builtins.md
// §A.3) called as function values compute what the direct calls compute and
// release their arguments exactly as often.
//
// s = "abcd", t = "ab": 4 + 0 + 1 + 1 + 0 + 1, then 4 + 2 from the live reads,
// so exit 13; a lost or freed argument changes the value.
#[test]
fn string_primitives_as_function_values_balance_against_direct_calls() {
    let pair = MarginalPair::new(
        "six String primitives called through function values",
        program([
            "(str-len s)",
            "(str-eq s t)",
            "(neq-string s t)",
            "(starts-with? s t)",
            "(ends-with? s t)",
            "(contains? s t)",
        ]),
        program([
            "(call1 str-len s)",
            "(call2 str-eq s t)",
            "(call2 neq-string s t)",
            "(call2 starts-with? s t)",
            "(call2 ends-with? s t)",
            "(call2 contains? s t)",
        ]),
    )
    .measure();
    assert_eq!(pair.control().exit_code(), Some(13), "{}", pair.report());
    assert_eq!(pair.subject().exit_code(), Some(13), "{}", pair.report());
    pair.assert_balanced("String primitives called through function values");
}

const IMPORTS: &str = "(import [primitives [Pure String add-i64 str-concat str-len str-eq \
                                          string-identity]])\n\
                       (defn call1 [f s] (f s))\n\
                       (defn call2 [f a b] (f a b))\n\
                       (defn b2i [b] (if b 1 0))\n";

/// A `--run` child with the seam checks armed: `IMPORTS`, then `defs`, then
/// `(defn main [] body)`.
fn child(defs: &str, body: &str) -> Child {
    Child::new(&format!("{IMPORTS}{defs}\n(defn main [] {body})\n"))
        .env("CRANELISP_RC_DEC_CHECK", "1")
}

/// Measure the pair; both halves must compute `exit`, so a lost or freed
/// argument cannot hide behind a balanced count.
fn measure(label: &str, exit: i32, control: Child, subject: Child) -> Marginal {
    let pair = MarginalPair::new(label, control, subject).measure();
    assert!(
        pair.control().exit_code() == Some(exit) && pair.subject().exit_code() == Some(exit),
        "both halves must exit {exit}\n{}\n--- control stderr ---\n{}\n--- subject stderr ---\n{}",
        pair.report(),
        pair.control().stderr,
        pair.subject().stderr
    );
    pair
}

/// `s` = "abcd" is bound, `u` is computed from it, and both are read at the
/// end: exit 8.
fn both_live(u: &str) -> String {
    format!(
        "(let [s (str-concat \"ab\" \"cd\")\n\
               u {u}]\n\
           (Pure (add-i64 (str-len u) (str-len s))))"
    )
}

// spec: spec/12-runtime.md §12.3.1 — `string-identity` (spec/appendix-a-builtins.md
// §A.3) called as a function value releases each reference exactly once; its
// argument stays live afterwards.
//
// SI-1 (F2b). The control is the direct call.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/fn_as_value.rs::emit_d24_adaptation found=S122 owner=/dev
#[test]
fn string_identity_as_function_value_balances_against_its_direct_call() {
    measure(
        "string-identity called through call1",
        8,
        child("", &both_live("(string-identity s)")),
        child("", &both_live("(call1 string-identity s)")),
    )
    .assert_balanced("string-identity through a function value");
}

// spec: spec/12-runtime.md §12.3.1 — a temporary passed to `string-identity`
// is released exactly once.
//
// SI-2 (F2a). The control passes the same string let-bound.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_extern_primitive_call found=S122 owner=/dev
#[test]
fn string_identity_over_a_temporary_balances_against_a_bound_argument() {
    measure(
        "string-identity over a temporary argument",
        4,
        child(
            "",
            "(let [s (str-concat \"ab\" \"cd\") u (string-identity s)] (Pure (str-len u)))",
        ),
        child(
            "",
            "(let [u (string-identity (str-concat \"ab\" \"cd\"))] (Pure (str-len u)))",
        ),
    )
    .assert_balanced("string-identity over a temporary");
}

// spec: spec/12-runtime.md §12.3.1 — a user function returning
// `(string-identity s)` releases each reference exactly once when called
// directly with `s` live afterwards.
//
// SI-3 (F3). The control body returns `s` itself.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::call_returns_owned_reference found=S122 owner=/dev
#[test]
fn body_returning_string_identity_balances_against_returning_its_argument() {
    let call = both_live("(user-id s)");
    measure(
        "a body returning string-identity's result",
        8,
        child("(defn user-id [s] s)", &call),
        child("(defn user-id [s] (string-identity s))", &call),
    )
    .assert_balanced("a returned string-identity result");
}

/// A test-local `Display` whose `String` impl typecheck's builtin dispatch
/// maps to `string-identity`. The mapping is keyed by bare trait, method and
/// type names, so the stdlib trait is not needed.
const DISPLAY: &str = "(deftrait Display (show [self] String))\n\
                       (impl Display String (defn show [x] x))\n";

// spec: spec/12-runtime.md §12.3.1 — `show` on a String through a `Display`
// trait (spec/07-traits.md) releases each reference exactly once.
//
// SI-4. The control is the same program with `render` returning `s` without
// `show`. The subject's residual observed before the correction is the
// evidence that this dispatch reaches the shim.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::call_returns_owned_reference found=S122 owner=/dev
#[test]
fn display_show_on_a_string_balances_against_the_program_without_show() {
    let call = both_live("(render s)");
    measure(
        "Display.show on a String",
        8,
        child(&format!("{DISPLAY}(defn render [s] s)"), &call),
        child(&format!("{DISPLAY}(defn render [s] (show s))"), &call),
    )
    .assert_balanced("Display.show on a String");
}

// spec: spec/12-runtime.md §12.3.1 — `str-concat`, an `Owned`-declared
// consuming extern, called as a function value balances against its direct
// call. SI-5, a twin whose convention the ACT-0974 correction must not change.
//
// s = "abcd", t = "x": 5 + 4 + 1, so exit 10.
#[test]
fn owned_extern_as_function_value_balances_against_its_direct_call() {
    let program = |u: &str| {
        format!(
            "(let [s (str-concat \"ab\" \"cd\")\n\
                   t (str-concat \"x\" \"\")\n\
                   u {u}]\n\
               (Pure (add-i64 (str-len u) (add-i64 (str-len s) (str-len t)))))"
        )
    };
    measure(
        "str-concat called through call2",
        10,
        child("", &program("(str-concat s t)")),
        child("", &program("(call2 str-concat s t)")),
    )
    .assert_balanced("str-concat through a function value");
}

// spec: spec/12-runtime.md §12.3.1 — a partially applied only-read extern,
// `(str-eq s)`, called through a function value balances against the direct
// call. SI-6, a twin for the auto-curry target call.
//
// s = t = "abcd": 1 + 4 + 4, so exit 9.
#[test]
fn curried_only_read_extern_balances_against_its_direct_call() {
    let program = |b: &str| {
        format!(
            "(let [s (str-concat \"ab\" \"cd\")\n\
                   t (str-concat \"ab\" \"cd\")\n\
                   n (b2i {b})]\n\
               (Pure (add-i64 n (add-i64 (str-len s) (str-len t)))))"
        )
    };
    measure(
        "str-eq curried then called through call1",
        9,
        child("", &program("(str-eq s t)")),
        child("", &program("(call1 (str-eq s) t)")),
    )
    .assert_balanced("a curried str-eq through a function value");
}
