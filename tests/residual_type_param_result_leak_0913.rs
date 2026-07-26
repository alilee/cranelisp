//! FIXME 0913 — a REPL result whose displayed type keeps a RESIDUAL TYPE
//! PARAMETER is never released.
//!
//! The pair below is the whole finding, reduced to one variable: the same
//! expression, the same value, differing only in whether an annotation pins the
//! residual parameter.
//!
//! ```text
//! subject : (Err "boom")                        :(primitives/Result a primitives/String)
//! control : :(Result String String) (Err "boom") :(primitives/Result primitives/String primitives/String)
//! ```
//!
//! Measured at S118 HEAD over 20 identical turns, child exit counters:
//! control `ALLOC_COUNT=40 DEALLOC_COUNT=40` (exactly balanced), subject
//! `ALLOC_COUNT=40 DEALLOC_COUNT=0` — two allocations per turn, ZERO
//! deallocations, growing linearly in session length.
//!
//! The axis is the presence of a residual parameter, not which parameter, not
//! whether the payload is heap or scalar, and not `Vec`: `(Ok 1)` leaks its
//! `Result` box with an `Int` payload, and `(vec)` leaks too. `None` cannot
//! leak — it is a nullary tag with no allocation, and the design record's
//! citation of it as a leaking case is the reason the recorded scope
//! (`[]`/`None`, an exotic corner) read narrower than the truth: this covers
//! `(Ok x)`/`(Err x)`, the most common result shape in the language, on the
//! first unannotated try.
//!
//! Owner, per `design/int/result-owner.md` §1.1.1 and `/qa`'s S118 P6 triage
//! (`tests/plan/s118-test-plan.md` §11.8.3): the LENIENT VIEW,
//! `MonoExpr::lenient_from_expr` in typecheck — backend keyed the result root
//! through that view's `ConcreteType::Int` placeholder and emitted no glue, so
//! the result owner cannot release what was never emitted. Not re-opened here.
//!
//! **Do not close this by annotating.** "Annotate your `Result` and it stops
//! leaking" is not a user-facing contract, and the residual-parameter displays
//! themselves are spec-required (`repl/spec.md` §1.5/§4.1) and correct — the
//! release behind them is not.
//!
//! Instrument: the child's EXIT allocator counters
//! (`CRANELISP_ALLOC_PARITY_DUMP`), never `/mem` deltas. `/mem`'s window closes
//! before the result release and is itself the subject of FIXME 0914, so a
//! `/mem`-based cell here would be measuring the other defect.

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
