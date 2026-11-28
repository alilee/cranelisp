//! FIXME 0916 formerly treated a generic trait-method instance's scalar payload
//! as a heap pointer. At S118 the residual-`Var` payload acquired a guarded RC
//! increment; values at or above 1024 caused a wild atomic write at payload+8.
//! The initial TCO-loss hypothesis was falsified: both variants used a loop jump.
//!
//! S121's concrete monomorphisation (992cb595) removed that exposure from this
//! program. The trait call now has a concrete Int payload. These guards retain
//! the 1023/1024 boundary and the plain-defn control at 400,000 iterations; they
//! do not witness the remaining residual-Var family in FIXME 0903.
//!
//! Historical S118 observations, --run --no-cache:
//! trait fmap returned 7 at n=1023 and SIGSEGV at n=1024 and n=2000;
//! plain fmapo returned 7 through n=400000.

#[path = "helpers/mod.rs"]
mod helpers;

use std::os::unix::process::ExitStatusExt;

use helpers::e2e::{CrOutput, Cranelisp, PreludeVariant};

/// The nine-liner, parameterised on the two axes that discriminate: which
/// callee sits in the `match` scrutinee (the generic trait method vs the
/// byte-identical plain `defn`) and the starting `n` (which IS the `Some`
/// payload's value on the first iteration).
fn program(scrutinee_callee: &str, n: u32) -> String {
    format!(
        "(import [primitives [IO pure sub-i64 eq-i64]])\n\
         (deftype (Option a) None (Some [:a val]))\n\
         (deftrait (Functor f)\n\
           (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (impl (Functor f) (Functor Option)\n\
           (defn fmap [g o] (match o [None None (Some x) (Some (g x))])))\n\
         (defn fmapo [g o] (match o [None None (Some x) (Some (g x))]))\n\
         (defn go [n acc]\n\
           (if (eq-i64 n 0)\n\
             (primitives/pure acc)\n\
             (match ({scrutinee_callee} (fn [z] z) (Some n))\n\
               [(Some v) (go (sub-i64 n 1) acc)\n\
                None     (primitives/pure 0)])))\n\
         (defn main [] (go {n} 7))\n"
    )
}

fn run(scrutinee_callee: &str, n: u32) -> CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .file("m.cl", &program(scrutinee_callee, n))
        .run("m.cl")
        .cli_flag("--no-cache")
        .output()
}

/// Assert the child completed under its own control — no signal — and returned
/// the program's accumulator. Exit STATUS, not stdout: a SIGSEGV produces no
/// diagnostic at all, so status is the only channel that carries the failure.
fn assert_exited_cleanly(out: CrOutput, what: &str) {
    match (out.status.code(), out.status.signal()) {
        (Some(7), _) => {}
        (code, signal) => panic!(
            "{what}\nexpected a clean exit with the accumulator (7); got code={code:?} \
             signal={signal:?} (signal 11 = SIGSEGV — a wild atomic write at \
             payload+8, FIXME 0916)\nstdout:\n{}\nstderr:\n{}",
            out.stdout, out.stderr
        ),
    }
}

// The SUBJECT. A `Some` payload whose Int VALUE is at or above
// `NULLARY_TAG_THRESHOLD` (1024) must not be RC-manipulated as a pointer. Both
// probed values are asserted: 1024 is the exact boundary (the mechanism), 2000
// is the filing's original observation (the symptom).
// spec: spec/12-runtime.md §12.3.1 — the runtime manages heap values; a scalar
// is not one, and nothing may dereference or RC it as if it were.
// defect: class=scalar-as-pointer locus=crates/cranelisp-backend generic trait-method instance, residual-var slot RC guard found=S118 owner=/dev fixed=S121/992cb595
#[test]
fn trait_method_instance_does_not_rc_a_scalar_payload_as_a_pointer() {
    for n in [1024, 2000] {
        assert_exited_cleanly(
            run("fmap", n),
            &format!(
                "trait-dispatched scrutinee at n={n}: the generic instance \
                 `Functor.fmap$user/Option` must not RC its residual-`Var` payload \
                 slot — the payload here is a raw Int (FIXME 0916)"
            ),
        );
    }
}

// The BOUNDARY control — one below the threshold, same subject program in every
// other respect. It passed at S118 while the subject failed, distinguishing
// the payload-value threshold from recursion depth.
// spec: spec/12-runtime.md §12.3.1 — the runtime manages heap values; a scalar
// is not one, and nothing may dereference or RC it as if it were.
// defect: class=scalar-as-pointer locus=crates/cranelisp-backend generic trait-method instance, residual-var slot RC guard found=S118 owner=/dev fixed=S121/992cb595
#[test]
fn trait_method_instance_is_clean_just_below_the_nullary_tag_threshold() {
    assert_exited_cleanly(
        run("fmap", 1023),
        "trait-dispatched scrutinee at n=1023 (one below NULLARY_TAG_THRESHOLD) \
         completes cleanly — the discriminator is the payload VALUE, not the \
         recursion depth (FIXME 0916)",
    );
}

// The MONOMORPHISED control — the same body as a plain `defn`, 400,000
// iterations, 400x past the depth the filing read as a stack threshold. It
// passed at S118: it emitted no payload RC, and both self calls were jumps.
// spec: spec/12-runtime.md §12.5 — self-recursive tail calls run in constant
// stack space and MUST NOT stack-overflow.
// defect: class=scalar-as-pointer locus=crates/cranelisp-backend generic trait-method instance, residual-var slot RC guard found=S118 owner=/dev fixed=S121/992cb595
#[test]
fn plain_defn_scrutinee_is_clean_at_400k_iterations() {
    assert_exited_cleanly(
        run("fmapo", 400_000),
        "the byte-identical plain-`defn` scrutinee survives 400,000 iterations: \
         the subject's SIGSEGV is not deep recursion and not lost TCO (FIXME \
         0916, mechanism falsified in tests/plan/s118-test-plan.md §11.8.5)",
    );
}
