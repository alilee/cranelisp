// match_scrutinee_yielded_borrow_0781.rs — the e2e tier for FIXME 0781's
// syntactic-temporary class in the match/vec release seams (S115 W4c, `/dev`
// backend; e2e requested IN-WAVE per METHOD §2.2 rather than deferred).
//
// THE DEFECT (fixed; these are the durable regression guards). Two RC-emission
// gates decided "is this container THIS frame's owned temporary?" by asking the
// container EXPRESSION's node kind — `matches!(expr, MonoExpr::Var { .. })` —
// instead of asking the container VALUE's provenance:
//
//   - `compiler/match_codegen.rs`  — `compile_var_pattern_arm`'s `is_alias` and
//     `dec_temporary_scrutinee`'s `is_temp` (the same question, opposite
//     polarity);
//   - `compiler/vec_codegen.rs`    — `emit_vec_drop_if_temporary`.
//
// An `If`, `Match` or `Let` node that merely YIELDS a borrowed param is not a
// `Var`, so it took the release path: the enclosing frame's box was freed while
// the caller still owned it, and the caller's own dec then hit freed memory.
// `--run` often survives it; the LINKED binary aborts deterministically, which
// is why every cell below drives the `--link` face.
//
// MEASURED (`PrimitivesOnly`, `--link`): every program here exited **134**
// (`corrupted double-linked list` / `free(): chunks in smallbin corrupted`)
// before the W4c change-set and exits **9** after it.
//
// THE FIX (what a re-break would undo): all five gates in the two seams now read
// ONE derived answer, `fn_compiler::value_provenance` (lattice
// `Fresh ⊑ OwnedTemporary ⊑ NotOwnedHere`), at two thresholds —
// `is_fresh_construction` = `== Fresh`, `yields_owned_temporary` =
// `!= NotOwnedHere`. See `crates/cranelisp-backend/CLAUDE.md` §"RC-emission
// gates that are ONE predicate, not per-site syntax".
//
// INSTRUMENT. Each cell runs the MS-P1 safety matrix (`SafetyMatrix`): modes ×
// ownership toggle {ON, OFF = `CRANELISP_NO_OWNERSHIP=1`, the conservative
// all-Owned reference semantics} × {differential equivalence, `--link` face,
// RC-balance differential, `RC_DEC_CHECK` zero}. The toggle-OFF leg matters
// here: a release keyed on syntax is emitted regardless of the ownership
// analysis, so the conservative lowering is NOT a safe harbour for this class,
// and pinning both toggles is what stops a future "fix" that merely suppresses
// the analysis.
//
// Companion tiers: the in-crate unit pins live at
// `crates/cranelisp-backend/src/compiler/match_codegen/scrutinee_ownership_tests.rs`
// (they count `atomic_rmw` decs in CLIF and carry the detection proof); these
// cells pin the observable end-to-end consequence the counts stand for.
//
// NOT COVERED HERE — FIXME 0782 (`(match [7 8 9] [xs (vec-get xs 1)])`, a
// var-pattern arm double-releasing a genuinely-OWNED temporary scrutinee) is a
// DIFFERENT, still-open defect in the same seam, filed with its own repro plan
// and owned by `/dev` next sprint. Every scrutinee below is a BORROWED param
// reaching the match through a yielding node — the complementary case.
//
// Stdlib-free: `primitives` only (root CLAUDE.md §Design Principles).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{PreludeVariant, SafetyMatrix};

fn matrix(program: &str) -> SafetyMatrix {
    SafetyMatrix::new(program)
        .prelude(PreludeVariant::PrimitivesOnly)
        .expect_exit(9)
}

// ---- face 1: `If`-yielded borrowed param as a match scrutinee ---------------

// spec: spec/12-runtime.md §12.1 — a match scrutinee that merely YIELDS a
// borrowed param is not this frame's to release. `(if b v v)` (both arms the
// same borrowed param, so no aliasing subtlety at all) reaching a var-pattern
// arm that READS it must not free the caller's box.
// MEASURED: `--link` exit 134 before W4c, exit 9 after.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/match_codegen.rs::compile_var_pattern_arm found=S115 owner=/dev
#[test]
fn if_yielded_borrowed_param_match_scrutinee_not_double_released() {
    matrix(
        "(defn f [v b] (match (if b v v) [xs (vec-get xs 0)]))\n\
         (defn main [] (Pure (f [9 9 9] false)))\n",
    )
    .assert();
}

// ---- face 2: `Let`-yielded binding as a match scrutinee ---------------------

// spec: spec/12-runtime.md §12.1 — the `let`-yielding twin of face 1. A `Let`
// whose body is the bound name is just as much "not a `Var` node" as an `If`,
// and took the same release path. No control flow is involved, which isolates
// the node-kind test as the whole mechanism.
// MEASURED: `--link` exit 134 before W4c, exit 9 after.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/match_codegen.rs::compile_var_pattern_arm found=S115 owner=/dev
#[test]
fn let_yielded_binding_match_scrutinee_not_double_released() {
    matrix(
        "(defn f [v] (match (let [w v] w) [xs (vec-get xs 0)]))\n\
         (defn main [] (Pure (f [9 9 9])))\n",
    )
    .assert();
}

// ---- face 3: ADT constructor pattern over a yielded borrowed scrutinee ------

// spec: spec/12-runtime.md §12.1 — the ADT-pattern twin: the arm destructures
// with a CONSTRUCTOR pattern rather than a var pattern, so the release runs
// through `dec_temporary_scrutinee`'s `is_temp` leg instead of the
// `compile_var_pattern_arm` `is_alias` leg. Both legs asked the same
// syntactic question, so both faces aborted — and one fix had to close both.
// MEASURED: `--link` exit 134 before W4c, exit 9 after.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/match_codegen.rs::dec_temporary_scrutinee found=S115 owner=/dev
#[test]
fn if_yielded_borrowed_adt_scrutinee_constructor_pattern_not_double_released() {
    matrix(
        "(deftype Wrap (MkWrap [:(Vec Int) items]))\n\
         (defn f [t b] (match (if b t t) [(MkWrap xs) (vec-get xs 0)]))\n\
         (defn main [] (Pure (f (MkWrap [9 9 9]) false)))\n",
    )
    .assert();
}

// ---- face 4: `Let`-yielded binding as a `vec-get` container ----------------

// spec: spec/12-runtime.md §12.1 — the sibling seam. `emit_vec_drop_if_temporary`
// carried the identical `MonoExpr::Var` test, so a `Let`-yielded borrowed param
// in CONTAINER position (no match anywhere) aborted the same way. Pinning it
// alongside the match faces is what makes the class — rather than one seam —
// the thing under guard.
// MEASURED: `--link` exit 134 before W4c, exit 9 after.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::emit_vec_drop_if_temporary found=S115 owner=/dev
#[test]
fn let_yielded_binding_vec_get_container_not_released() {
    matrix(
        "(defn f [v] (vec-get (let [w v] w) 0))\n\
         (defn main [] (Pure (f [9 9 9])))\n",
    )
    .assert();
}

// spec: spec/12-runtime.md §12.1 — the fourth cell of the {match seam,
// vec_codegen seam} × {`If`-yield, `Let`-yield} matrix, and FIXME 0781's own
// minimal reduction ("Q3 is the whole defect in one line: no `let`, no COW, no
// may-alias, both `If` arms identical"). Faces 1–4 without it leave exactly one
// combination unexercised, which is where a partial re-break would hide.
// MEASURED: `--link` exit 134 ("corrupted double-linked list") before W4c,
// exit 9 after.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::emit_vec_drop_if_temporary found=S115 owner=/dev
#[test]
fn if_yielded_borrowed_param_vec_get_container_not_released() {
    matrix(
        "(defn f [v b] (vec-get (if b v v) 0))\n\
         (defn main [] (Pure (f [9 9 9] false)))\n",
    )
    .assert();
}

// ---- discriminating controls (METHOD §2.2) ---------------------------------

// spec: spec/12-runtime.md §12.1 — CONTROL for faces 1/2: the SAME read with
// the scrutinee spelled as a bare `Var`. The old syntactic test and the new
// provenance answer agree on every `Var`, so this cell was clean before AND
// after — it is the fence proving the four cells above pin a NARROWING of the
// release, not its deletion.
#[test]
fn bare_var_match_scrutinee_control_stays_clean() {
    matrix(
        "(defn f [v] (match v [xs (vec-get xs 0)]))\n\
         (defn main [] (Pure (f [9 9 9])))\n",
    )
    .assert();
}

// spec: spec/12-runtime.md §12.1 — CONTROL for face 4: the bare-`Var` container
// twin. Same role as the cell above, on the `vec_codegen` seam.
#[test]
fn bare_var_vec_get_container_control_stays_clean() {
    matrix(
        "(defn f [v] (vec-get v 0))\n\
         (defn main [] (Pure (f [9 9 9])))\n",
    )
    .assert();
}
