//! FIXME 0917 — a `match` arm returning a NULLARY constructor beside a boxed
//! arm strands the whole loop.
//!
//! The subject and the control below are byte-identical apart from `step`'s
//! arms: the subject returns `None` from arms the loop never takes, the control
//! returns `(Some …)` from all of them. Nothing else differs — same `deftype`s,
//! same accessor, same COW `vec-set`, same driving loop, same iteration count.
//!
//! Measured at S118 HEAD (`--run --no-cache`, and again through `--link`):
//!
//! | loop    |    N | allocs | deallocs | residue |
//! |---------|-----:|-------:|---------:|--------:|
//! | subject |  100 |    406 |      **4** |     402 |
//! | subject | 1100 |   4406 |      **4** |    4402 |
//! | control |  100 |    406 |      406 |   **0** |
//! | control | 1100 |   4406 |     4406 |   **0** |
//!
//! Slope exactly 4 objects/iteration and deallocs CONSTANT: after the first
//! four the loop performs no deallocation whatsoever. `/qa`'s CLIF probe
//! (`tests/plan/s118-test-plan.md` §11.8.1) localises it to one instruction —
//! the subject's `step` ends with a `NULLARY_TAG_THRESHOLD`-guarded protect inc
//! on the match result (`icmp ult v10, 1024; brif …; atomic_rmw add v10+8`)
//! that nothing balances, so the returned `(Some …)` tree leaves the frame at
//! rc=2 and strands at rc=1 once the caller releases its one count. The
//! control's `step` emits no protect inc at that seam. Both callers are correct
//! for their callee's truthful summary, so typecheck is exonerated: the defect
//! is that a nullary `ConstrADT` arm classifies non-Fresh in the
//! `value_provenance`/`is_fresh_construction` join, licensing a protect that
//! only a genuinely aliasing result could ever balance.
//!
//! This is the real owner of cell #21
//! (`tests/exemplar_ownership_residue_s116.rs`) — the exemplar's `eliminate` is
//! this shape, and the reduction accounts for 100% of its 12,431 warm retained
//! objects. It is NOT a FIXME 0903 family: every type here is concrete and no
//! residual signature var is involved.
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
/// `None` arm is ever taken at runtime — its mere presence is the defect.
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
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/rc_emission.rs::protect_return_value found=S118 owner=/dev
//   — the locus token cited `fn_compiler.rs` at filing; the method was never
//   defined there (FIXME 0917's header carries the `git log -S` proof), so this
//   is a factual correction of the citation, not a move of the seam.
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
// the linking child. /port verified the numbers are identical through both
// toggles, so a divergence here would be a NEW finding (mode divergence) on top
// of 0917, not a duplicate of the cell above.
// spec: spec/12-runtime.md §12.3.1 — unreachable heap ownership is released.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/rc_emission.rs::protect_return_value found=S118 owner=/dev
//   — the locus token cited `fn_compiler.rs` at filing; the method was never
//   defined there (FIXME 0917's header carries the `git log -S` proof), so this
//   is a factual correction of the citation, not a move of the seam.
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
