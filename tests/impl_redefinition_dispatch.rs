// impl_redefinition_dispatch.rs — S114 Phase-6b, NEW finding (/repl Phase-6b probe).
//
// Re-`impl`ing a trait for the same type in one session is SILENTLY IGNORED: the
// second `(impl Sizeable Box …)` prints the SAME plain confirmation as the first
// (`impl user/Sizeable for user/Box`, implying success), yet dispatch still runs
// the FIRST impl's body (12, not 7). Verified at HEAD: the transcript below emits
// `:primitives/Int 12` both before AND after the redefinition — the new body never
// takes, and nothing tells the user it was rejected.
//
// The intended semantics are an OPEN USER QUESTION (Phase 7): hot-reload (like
// `defn` redefinition — the new impl dispatches) vs immutable-per-session (the
// redefinition is rejected/warned, not silently confirmed). Under EITHER ruling
// today's behaviour is wrong. This pin is POLARITY-SAFE: it fails RED under both
// rulings and goes green under whichever the user chooses — after a re-impl, the
// session MUST either dispatch the NEW impl (7) OR emit an explicit not-replaced
// notice/error. Currently NEITHER holds.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// The verbatim /repl probe: declare a trait + type, impl → 12, dispatch, re-impl →
// 7, dispatch again.
const REIMPL_TRANSCRIPT: &str = "(deftype Box (Bx [:Int v]))\n\
     (deftrait Sizeable (size [x] Int))\n\
     (impl Sizeable Box (defn size [x] 12))\n\
     (size (Bx 0))\n\
     (impl Sizeable Box (defn size [x] 7))\n\
     (size (Bx 0))\n";

// Polarity-safe pin — after re-impl, EITHER the new impl dispatches (7) OR an
// explicit not-replaced notice/error appears. Today the second `(size (Bx 0))` is
// `:primitives/Int 12` and the re-impl confirmation is indistinguishable from the
// first — NEITHER branch holds. Goes green under hot-reload (7 appears) OR under
// immutable-per-session (a not-replaced notice appears).
// spec: spec/05-definitions.md §5.4 — `impl` registration/dispatch; the
// redefinition semantics (hot-reload vs immutable) are an OPEN USER QUESTION, but
// silently confirming a redefinition that does not take is wrong under either.
// defect: class=silent-accept locus=src (impl registration/dispatch seam) found=S114 owner=user-ruling-then-dev
#[test]
fn reimpl_either_dispatches_new_or_notices_not_replaced() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(REIMPL_TRANSCRIPT)
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);

    // Branch A — hot-reload ruling: the redefined impl dispatches → 7.
    let new_impl_dispatched = combined.contains(":primitives/Int 7");

    // Branch B — immutable ruling: an explicit notice that the redefinition was
    // NOT applied (any of these "not-replaced" signal words). Today's output —
    // `impl user/Sizeable for user/Box` + `:primitives/Int 12` — contains none.
    let not_replaced_notice = [
        "already",
        "not replaced",
        "cannot redefine",
        "duplicate impl",
        "existing impl",
        "already implemented",
        "ignored",
        "exists",
    ]
    .iter()
    .any(|w| combined.contains(w));

    assert!(
        new_impl_dispatched || not_replaced_notice,
        "after a re-impl of Sizeable for Box, the session MUST either dispatch the \
         NEW impl (`:primitives/Int 7`) OR emit an explicit not-replaced \
         notice/error — today it silently prints a success-looking confirmation \
         and still dispatches the FIRST impl (12). Got:\n{combined}"
    );
}
