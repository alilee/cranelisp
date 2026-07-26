//! FIXME 0916 — a generic trait-method instance RC-manipulates a SCALAR
//! payload as if it were a heap pointer, and wild-writes when the scalar's
//! value crosses `NULLARY_TAG_THRESHOLD`.
//!
//! The filing's title ("a self tail call in a `match` arm SIGSEGVs at ~1,000
//! depth when the scrutinee is a trait-method call") named a mechanism that
//! `/qa`'s CLIF probe FALSIFIED (`tests/plan/s118-test-plan.md` §11.8.5): TCO
//! is intact — `go`'s self call compiles to `jump block1(…)` in BOTH variants,
//! no frame growth, no lost tail call. The ~1,000 "depth threshold" was the
//! payload VALUE crossing 1024, because `n` counts DOWN from the start value.
//!
//! What actually happens: the generic instance `Functor.fmap$user/Option` is
//! compiled once per type constructor with the `Some` payload typed as a
//! residual `Var`, and emits a threshold-guarded RC inc on that payload
//! (`icmp ult v15, 1024; … atomic_rmw.i64 add v15+8`). The payload is a raw
//! `Int`. When its value is ≥ 1024 the guard reads it as a heap pointer and
//! performs a wild atomic write at address `payload+8` → SIGSEGV. The
//! monomorphised control emits zero RC ops on the same payload. The nullary-tag
//! guard discriminates TAGS from POINTERS; it is categorically unable to
//! discriminate SCALARS from pointers, so it cannot license RC ops on a slot
//! whose category is unknown at emission. Attributed to `cranelisp-backend`,
//! FIXME 0903 family 2, whose consequence is upgraded by this cell from "silent
//! leak" to memory-unsafe wild write.
//!
//! Measured at S118 HEAD, `--run --no-cache`, exit STATUS (the failure mode is
//! a signal, so a value assertion would never see it):
//!
//! | scrutinee                | n=1023 | n=1024 | n=2000 | n=400000 |
//! |--------------------------|--------|--------|--------|----------|
//! | trait method `fmap`      | exit 7 | SIGSEGV| SIGSEGV| —        |
//! | plain `defn fmapo`       | exit 7 | exit 7 | exit 7 | exit 7   |
//!
//! The three cells below are that table's discriminating corners. The pair is
//! what makes the finding legible: a lone deep-recursion RED reads as "deep
//! recursion overflows the stack", which is precisely what this is NOT — the
//! plain-`defn` control survives 400,000 iterations of the same shape, and the
//! subject dies on its FIRST iteration at n=1024 while surviving n=1023.
//!
//! Free-standing per root `CLAUDE.md` §"Stdlib separation": every name is
//! either imported from `primitives` or defined in the fixture.

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
        "(import [primitives [IO Pure sub-i64 eq-i64]])\n\
         (deftype (Option a) None (Some [:a val]))\n\
         (deftrait (Functor f)\n\
           (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (impl (Functor f) (Functor Option)\n\
           (defn fmap [g o] (match o [None None (Some x) (Some (g x))])))\n\
         (defn fmapo [g o] (match o [None None (Some x) (Some (g x))]))\n\
         (defn go [n acc]\n\
           (if (eq-i64 n 0)\n\
             (Pure acc)\n\
             (match ({scrutinee_callee} (fn [z] z) (Some n))\n\
               [(Some v) (go (sub-i64 n 1) acc)\n\
                None     (Pure 0)])))\n\
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
// defect: class=scalar-as-pointer locus=crates/cranelisp-backend generic trait-method instance, residual-var slot RC guard found=S118 owner=/dev
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
// other respect. GREEN at HEAD, and that is what makes the cell above a
// value-threshold finding rather than a depth finding: 1023 iterations of the
// identical shape complete cleanly.
// spec: spec/12-runtime.md §12.3.1 — the runtime manages heap values; a scalar
// is not one, and nothing may dereference or RC it as if it were.
// defect: class=scalar-as-pointer locus=crates/cranelisp-backend generic trait-method instance, residual-var slot RC guard found=S118 owner=/dev
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
// iterations, 400x past the depth the filing read as a stack threshold. GREEN
// at HEAD: it emits zero RC ops on the payload, and the self tail call is a
// jump in both variants, so this is also a standing §12.5 exercise.
// spec: spec/12-runtime.md §12.5 — self-recursive tail calls run in constant
// stack space and MUST NOT stack-overflow.
// defect: class=scalar-as-pointer locus=crates/cranelisp-backend generic trait-method instance, residual-var slot RC guard found=S118 owner=/dev
#[test]
fn plain_defn_scrutinee_is_clean_at_400k_iterations() {
    assert_exited_cleanly(
        run("fmapo", 400_000),
        "the byte-identical plain-`defn` scrutinee survives 400,000 iterations: \
         the subject's SIGSEGV is not deep recursion and not lost TCO (FIXME \
         0916, mechanism falsified in tests/plan/s118-test-plan.md §11.8.5)",
    );
}
