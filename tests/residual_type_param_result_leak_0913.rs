//! Regression guard for FIXME 0913 (retired S122): a REPL result whose
//! displayed type kept a RESIDUAL TYPE PARAMETER was never released.
//!
//! The pair isolates one variable: the same expression and value, differing
//! only in whether an annotation pins the residual parameter.
//!
//! ```text
//! subject : (Err "boom")                        :(primitives/Result a primitives/String)
//! control : :(Result String String) (Err "boom") :(primitives/Result primitives/String primitives/String)
//! ```
//!
//! Measured at S118 HEAD over 20 identical turns, child exit counters:
//! control `ALLOC_COUNT=40 DEALLOC_COUNT=40` (exactly balanced), subject
//! `ALLOC_COUNT=40 DEALLOC_COUNT=0` — two allocations per turn and no
//! deallocations, growing linearly in session length.
//!
//! The axis was the presence of a residual parameter, not which parameter, not
//! whether the payload is heap or scalar, and not `Vec`: `(Ok 1)` leaked its
//! `Result` box with an `Int` payload, and `(vec)` leaked too. `None` cannot
//! leak — it is a nullary tag with no allocation.
//!
//! The defect lived at the LENIENT VIEW, `MonoExpr::lenient_from_expr` in
//! typecheck (`design/int/result-owner.md` §1.1.1; `/qa`'s S118 P6 triage,
//! `tests/plan/s118-test-plan.md` §11.8.3): backend keyed the result root
//! through that view's `ConcreteType::Int` placeholder and emitted no glue, so
//! the result owner could not release what was never emitted.
//!
//! **The control's annotation is not the fix.** The residual-parameter
//! displays are spec-required (`repl/spec.md` §1.5/§4.1); the release behind
//! them must match the pinned twin without the user annotating.
//!
//! Instrument: the child's EXIT allocator counters
//! (`CRANELISP_ALLOC_PARITY_DUMP`), which observe the whole session. The cell
//! predates the `/mem <expr>` window correction (FIXME 0914, retired S122;
//! `tests/plan/s122-evidence-delta.md` §"Retained records of the deleted
//! filings").

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::marginal::{Child, Instrument, MarginalPair};

/// Turns per child. Small enough to stay fast, large enough that the slope
/// (2 allocations/turn) dwarfs any one-off; the assertion is exact regardless.
const TURNS: usize = 20;

/// Both children open with the SAME import so `Result`/`Err` resolve without a
/// prelude file (root `CLAUDE.md` §"Stdlib separation"), then repeat one turn.
/// Everything but the annotation is common and cancels in the marginal.
fn session(turn: &str) -> String {
    let mut s = String::from("(import [primitives [*]])\n");
    for _ in 0..TURNS {
        s.push_str(turn);
        s.push('\n');
    }
    s
}

// spec: spec/12-runtime.md §12.3.1 — unreachable heap ownership is released.
// The result of a REPL turn becomes unreachable when the turn ends, whatever
// its displayed type; design/int/result-owner.md §1.1.1 names the seam.
// defect: class=rc-miscount locus=cranelisp-typecheck::MonoExpr::lenient_from_expr found=S118 owner=/dev
#[test]
fn unannotated_result_turn_releases_like_its_annotated_twin() {
    MarginalPair::new(
        "20 `(Err \"boom\")` REPL turns, annotation-pinned control",
        Child::repl(&session(r#":(Result String String) (Err "boom")"#)),
        Child::repl(&session(r#"(Err "boom")"#)),
    )
    .instrument(Instrument::AllocParity)
    .measure()
    .assert_balanced(
        "a turn whose result type keeps a residual parameter MUST release its \
         result tree exactly as the annotation-pinned twin does — the displays \
         differ, the ownership must not (FIXME 0913)",
    );
}
