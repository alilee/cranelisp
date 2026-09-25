//! Regression guards for FIXME 0917, fixed in S120 (`cbb3be9e`): a `match`
//! arm returning a NULLARY constructor beside a boxed arm stranded the whole
//! loop.
//!
//! The subject and the control below are byte-identical apart from `step`'s
//! arms: the subject returns `None` from arms the loop never takes, the control
//! returns `(Some …)` from all of them. Nothing else differs — same `deftype`s,
//! same accessor, same COW `vec-set`, same driving loop, same iteration count.
//!
//! Pre-fix measurement at S118 (`--run --no-cache`, and again through `--link`):
//!
//! | loop    |    N | allocs | deallocs | residue |
//! |---------|-----:|-------:|---------:|--------:|
//! | subject |  100 |    406 |      **4** |     402 |
//! | subject | 1100 |   4406 |      **4** |    4402 |
//! | control |  100 |    406 |      406 |   **0** |
//! | control | 1100 |   4406 |     4406 |   **0** |
//!
//! The subject's `step` ended with a `NULLARY_TAG_THRESHOLD`-guarded protect inc
//! on the match result that nothing balanced, so each returned `(Some …)` tree
//! stranded at rc=1: a nullary `ConstrADT` arm classified non-Fresh in the
//! result-provenance join. The fix gave `ValueProvenance` a `NoReference` bottom
//! below `Fresh`; the ruling is `design/backend/non-concrete-release-contract.md`
//! §6. The exemplar's `eliminate` has this shape — the application-scale guard
//! is `tests/exemplar_ownership_residue_s116.rs`.
//!
//! Free-standing per root `CLAUDE.md` §"Stdlib separation": no prelude file and
//! no `CRANELISP_LIB`, with `(import [primitives [*]])` supplying the same bare
//! primitive surface `PreludeVariant::PrimitivesOnly` gives a builder-driven
//! cell.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::marginal::{Child, Instrument, MarginalPair};

/// The two programs differ ONLY in `step`'s returned constructors — the string
/// below is the whole subject/control axis, substituted into one template.
fn program(step_arms: &str) -> String {
    format!(
        "(platform stdio)\n\
         (import [primitives [*]])\n\
         \n\
         (deftype Item (A [:Int a]) (B [:Int b]))\n\
         (deftype Box [:(Vec Item) items])\n\
         \n\
         (defn item-at [bx i] (match bx [(Box items) (vec-get items i)]))\n\
         (defn set-item [bx i it] (match bx [(Box items) (Box (vec-set items i it))]))\n\
         \n\
         (defn step [bx i d]\n\
           (let [it (item-at bx i)]\n\
             (match it\n\
               [{step_arms}])))\n\
         \n\
         (defn subject-loop [bx n acc]\n\
           (if (eq-i64 n 0) acc\n\
             (match (step bx 0 5)\n\
               [(Some b2) (subject-loop bx (sub-i64 n 1) (add-i64 acc 1)) None acc])))\n\
         \n\
         (defn main [] (Pure (subject-loop (Box [(A 1) (A 2) (A 3)]) 1100 0)))\n"
    )
}

/// One arm returns the NULLARY `None`, the other a boxed `(Some …)`. Neither
/// `None` arm is ever taken at runtime — its mere presence triggered 0917.
fn subject() -> String {
    program(
        "(A x) (if (eq-i64 x d) None (Some (set-item bx i (A d))))\n\
                (B x) None",
    )
}

/// Identical except that no arm returns a nullary constructor.
fn control() -> String {
    program(
        "(A x) (if (eq-i64 x d) (Some bx) (Some (set-item bx i (A d))))\n\
                (B x) (Some bx)",
    )
}

const CONTRACT: &str = "a match whose arms mix a nullary constructor with a \
    boxed one MUST free its loop's garbage exactly as the all-boxed control \
    does — the nullary arm is not even taken (FIXME 0917)";

// spec: spec/12-runtime.md §12.3.1 — unreachable heap ownership is released.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/rc_emission.rs::protect_return_value found=S118 owner=/dev fixed=S120/cbb3be9e
//   — the filing cited `fn_compiler.rs`, where this method was never defined;
//   the token corrects that citation and does not move the seam.
#[test]
fn nullary_arm_beside_boxed_arm_frees_its_loop_under_run() {
    MarginalPair::new(
        "nullary-arm vs all-boxed-arm match result, 1100-iteration loop, --run",
        Child::new(&control()),
        Child::new(&subject()),
    )
    .instrument(Instrument::RcStats)
    .measure()
    .assert_balanced(CONTRACT);
}

// The `--link` face of the same pair: the produced executable is measured, not
// the linking child. The pre-fix numbers were identical in both modes, so a
// divergence here is a new mode-divergence finding, not a return of 0917.
// spec: spec/12-runtime.md §12.3.1 — unreachable heap ownership is released.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/rc_emission.rs::protect_return_value found=S118 owner=/dev fixed=S120/cbb3be9e
//   — the filing cited `fn_compiler.rs`, where this method was never defined;
//   the token corrects that citation and does not move the seam.
#[test]
fn nullary_arm_beside_boxed_arm_frees_its_loop_under_link() {
    MarginalPair::new(
        "nullary-arm vs all-boxed-arm match result, 1100-iteration loop, --link",
        Child::new(&control()).link_then_run(),
        Child::new(&subject()).link_then_run(),
    )
    .instrument(Instrument::RcStats)
    .measure()
    .assert_balanced(CONTRACT);
}

// spec: spec/12-runtime.md §12.3.1 — forwarding an owned result must not retain
// unreachable heap ownership after the caller releases it.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/rc_emission.rs::protect_return_value found=S121 owner=/dev fixed=S121/992cb595
#[test]
fn forwarding_fresh_option_releases_its_payload() {
    let program = |callee: &str, count: i64| {
        format!(
            "(import [primitives [*]])\n\
             (deftype Payload [:(Vec Int) values])\n\
             (defn make-option [p n] (if (eq-i64 n 0) None (Some p)))\n\
             (defn forward [p n] (make-option p n))\n\
             (defn run-loop [n]\n\
               (if (eq-i64 n 0) 0\n\
                 (match ({callee} (Payload [1]) n)\n\
                   [None 100\n\
                    (Some p) (match p [(Payload xs)\n\
                      (add-i64 (vec-get xs 0) (run-loop (sub-i64 n 1)))])])))\n\
             (defn main [] (Pure (run-loop {count})))\n"
        )
    };
    let measurements = [8, 32].map(|count| {
        let m = MarginalPair::new(
            &format!("forwarded versus direct fresh Option, {count} iterations"),
            Child::new(&program("make-option", count)),
            Child::new(&program("forward", count)),
        )
        .instrument(Instrument::RcStats)
        .measure();
        assert_eq!(
            m.control().exit_code(),
            Some(count as i32),
            "{}",
            m.control().stderr
        );
        assert_eq!(
            m.subject().exit_code(),
            Some(count as i32),
            "{}",
            m.subject().stderr
        );
        m
    });
    let [small, large] = measurements;
    let report = format!("{}\n{}", small.report(), large.report());
    assert_eq!(
        large.control().residual() - small.control().residual(),
        0,
        "the direct helper control must not retain unreachable owners as its loop grows\n{report}"
    );
    assert_eq!(
        large.residual() - small.residual(),
        0,
        "forwarding an owned Option must not add unreachable retention as its loop grows\n{report}"
    );
}
