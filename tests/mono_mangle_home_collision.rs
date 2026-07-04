//! FIXME 0508 (S102, /qa-repro half) — the mono-mangler HOME-axis silent
//! miscompile. `build_mangled_name` (`monomorphise.rs:1034`) mints
//! `"{bare_fn_name}${types}"` — **home-independent**. Two DISTINCT modules
//! each exporting a public generic of the SAME bare name, both FQ-referenced
//! in ONE consumer form at the SAME concrete arg types, both mint the SAME key
//! (`twist$Int+Int`) in the consumer's batch. The `seen`/dedup short-circuit
//! binds the second call to the FIRST module's already-minted body/GOT-slot
//! (`register_mono_entry`'s `existing_got_slot` reuse) → SILENT wrong-dispatch,
//! no diagnostic. This is the worst defect class: a miscompile that succeeds.
//!
//! This is the HOME axis. Sibling axes of the same lossy mangler:
//!   - ADT-arg axis (0483) — guarded by `tests/vec_query_value_use.rs`;
//!   - latent Fn-param-drop axis (see FIXME 0519).
//! All three are cured by the ONE unified lossless mangler, FIXME 0519
//! ({home}/{bare}${recursive-concrete-sig}). Home-qualifying the key mints
//! `a/twist$Int+Int` ≠ `b/twist$Int+Int` → two distinct bodies → correct
//! dispatch. This guard is the durable record + trigger for the HOME axis.
//!
//! FIXME(/dev typecheck): resolved by 0519 (unified lossless mono-mangler,
//! `cranelisp-typecheck`).
//!
//! Reduction notes:
//!   - The two calls MUST share ONE consumer form so they land in ONE mono
//!     batch (one `seen` map). Separate REPL turns instead surface a distinct
//!     module-load collision ("undefined variable: add-i64" as the SECOND
//!     same-named module recompiles) — a related but different symptom; this
//!     guard pins the clean 0508 mono-`seen`-collision.
//!   - `twist` needs a PHANTOM generic param (`g:a`) so it monomorphises,
//!     while its `x:Int → Int` body gives an observable, body-distinct result
//!     (a/`+100` vs b/`+200`). A purely-generic `(Fn [a] a)` has no
//!     Int-observable body; arithmetic on the observed value would force the
//!     param concrete and defeat monomorphisation. Confirmed generic on HEAD:
//!     `a/twist : (Fn [a primitives/Int] primitives/Int)`.
//!   - Observed on HEAD (RED): `(add-i64 (a/twist 0 5) (b/twist 0 5))` →
//!     `:primitives/Int 210` (105 + 105 — BOTH dispatch a's `+100` body).
//!     Correct is 310 (105 + 205). Order-confirmed: reversing the two calls
//!     yields 410 (both dispatch b's `+200` body) — the FIRST-referenced
//!     module's minted body wins, the second collides onto its slot.
//!
//! Failing-not-ignored per `memory/feedback_failing_not_ignored.md`; ledger:
//! `tests/plan/ledger.md` §"Sprint 102 — 0508 HOME-axis mono-mangle guard".

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// Module `a`: public generic `twist` whose Int body adds 100.
// `g` is a phantom generic param (unused → generalized to `a`), forcing the
// fn through monomorphisation; `x:Int` anchors an observable Int result.
const A_MODULE: &str = "(import [primitives [*]])\n\
                        (defn twist [g x] (add-i64 x 100))\n";

// Module `b`: a DISTINCT module, same bare generic name `twist`, body adds 200.
const B_MODULE: &str = "(import [primitives [*]])\n\
                        (defn twist [g x] (add-i64 x 200))\n";

// spec: spec/08-modules.md §8.5 — a fully-qualified `module/name` reference
// resolves through the module system to that module's definition; two distinct
// modules' same-named generics are distinct functions and MUST monomorphise +
// dispatch to their OWN bodies. RED on HEAD (FIXME 0508, HOME-axis mono-mangle
// collision): both `a/twist` and `b/twist` at `Int` mint the home-blind key
// `twist$Int+Int`; the second call silently reuses the first's minted body, so
// `(add-i64 (a/twist 0 5) (b/twist 0 5))` returns 210 (105+105) not 310
// (105+205). Flips green when FIXME 0519's home-qualified mangler mints two
// distinct instances.
#[test]
fn two_same_named_imported_generics_dispatch_to_own_bodies() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("a.cl", A_MODULE)
        .file("b.cl", B_MODULE)
        .stdin(
            "(import [primitives [*]])\n\
             (add-i64 (a/twist 0 5) (b/twist 0 5))\n",
        )
        .output()
        // Succeeds (no crash) — the RED signal is the WRONG VALUE, the hallmark
        // of a silent miscompile.
        .assert_ok()
        // a/twist 5 → 105, b/twist 5 → 205, sum → 310 (the correct dispatch).
        .assert_stdout_contains(":primitives/Int 310")
        // The specific wrong-dispatch value: both calls binding a's body.
        .assert_stdout_does_not_contain(":primitives/Int 210");
}
