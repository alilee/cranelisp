// bd_a_annotation_ascription.rs — BD-A1/A2 (S113 W5b, plan §4.1).
//
// spec §2.3.8 MUST: "an annotation MAY appear in EVERY expression position." The
// same family, one cure shape: route every operand position through the ONE
// annotation-aware seam (`build_one_expr_at`) + mirror `parse_defn`'s trailing
// rejection at the sibling sites; each parser having grown its own subset is the
// S108 codepath-duplication mechanism verbatim (P7).
//
// BD-A1: `:Type`-ascription WRONG-REJECTED in four positions (`class=wrong-reject`)
//   — each with its bare-body GREEN twin.
// BD-A2: trailing-form SILENT-DROP in two sibling positions (`class=silent-accept`)
//   — the family's existing RED is `deftype_ctor_trailing_form…` (cited).
//
// Free-standing (no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn run_prims(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(src)
        .output()
}

// ---- BD-A1: :Type-ascription wrong-rejects ×4 (RED) + bare twins (GREEN) -------

// LET BODY position. `(let [x 41] :Int x)` ascribes the let body — valid per
// §2.3.8 — but is WRONGLY REJECTED with a parse error. Should return 41.
// spec: spec/03-types.md §2.3.8 — an annotation may appear in every expression position (let body).
// defect: class=wrong-reject locus=crates/cranelisp-frontend/src/ast_builder.rs::build_let (body position not routed through build_one_expr_at) found=S113 owner=/dev
#[test]
fn let_body_ascription_accepted() {
    let out = run_prims("(defn f [] (let [x 41] :Int x))\n(defn main [] (Pure (f)))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("parse error"),
        "an ascribed let body `(let [x 41] :Int x)` MUST be accepted (§2.3.8); \
         wrongly parse-rejected today; got:\n{c}"
    );
    out.assert_exit(41);
}

// spec: spec/03-types.md §2.3.8 — bare let body twin (GREEN).
#[test]
fn let_body_bare_twin() {
    run_prims("(defn f [] (let [x 41] x))\n(defn main [] (Pure (f)))\n").assert_exit(41);
}

// IMPL-METHOD BODY position. `(impl T Int (defn m [x] :Int x))` — the method body
// is ascribed; wrongly parse-rejected. Should dispatch `(m 41)` → 41.
// spec: spec/03-types.md §2.3.8 — annotation in an impl-method body.
// defect: class=wrong-reject locus=crates/cranelisp-frontend/src/ast_builder.rs::build_impl_method (body not routed through build_one_expr_at) found=S113 owner=/dev
#[test]
fn impl_method_body_ascription_accepted() {
    let out = run_prims(
        "(deftrait T (m [self] Int))\n\
         (impl T Int (defn m [x] :Int x))\n\
         (defn main [] (Pure (m 41)))\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("parse error") && !c.to_lowercase().contains("annot"),
        "an ascribed impl-method body `(defn m [x] :Int x)` MUST be accepted \
         (§2.3.8); wrongly rejected today; got:\n{c}"
    );
    out.assert_exit(41);
}

// spec: spec/03-types.md §2.3.8 — bare impl-method body twin (GREEN).
#[test]
fn impl_method_body_bare_twin() {
    run_prims(
        "(deftrait T (m [self] Int))\n\
         (impl T Int (defn m [x] x))\n\
         (defn main [] (Pure (m 41)))\n",
    )
    .assert_exit(41);
}

// TRAIT DEFAULT-METHOD BODY position. `(deftrait T (m [x] :Int :Int x))` — the
// default body `:Int x` is ascribed; wrongly parse-rejected. Should compile.
// spec: spec/03-types.md §2.3.8 — annotation in a trait default-method body.
// defect: class=wrong-reject locus=crates/cranelisp-frontend/src/ast_builder.rs::build_method_sig (default body not routed through build_one_expr_at) found=S113 owner=/dev
#[test]
fn trait_default_method_body_ascription_accepted() {
    let out = run_prims("(deftrait T (m [x] :Int :Int x))\n(defn main [] (Pure 0))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("parse error"),
        "an ascribed trait default-method body `(m [x] :Int :Int x)` MUST be \
         accepted (§2.3.8); wrongly parse-rejected today; got:\n{c}"
    );
    out.assert_exit(0);
}

// spec: spec/03-types.md §2.3.8 — bare trait default-method body twin (GREEN).
#[test]
fn trait_default_method_body_bare_twin() {
    run_prims("(deftrait T (m [x] :Int x))\n(defn main [] (Pure 0))\n").assert_exit(0);
}

// TRACE OPERAND position. `(trace :Int 5)` ascribes the traced operand; wrongly
// parse-rejected. Should compile.
// spec: spec/03-types.md §2.3.8 — annotation in a `trace` operand.
// defect: class=wrong-reject locus=crates/cranelisp-frontend/src/ast_builder.rs::build_trace (operand not routed through build_one_expr_at) found=S113 owner=/dev
#[test]
fn trace_operand_ascription_accepted() {
    let out = run_prims("(defn f [] (trace :Int 5))\n(defn main [] (Pure 0))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("parse error"),
        "an ascribed `trace` operand `(trace :Int 5)` MUST be accepted (§2.3.8); \
         wrongly parse-rejected today; got:\n{c}"
    );
    out.assert_exit(0);
}

// spec: spec/03-types.md §2.3.8 — bare trace operand twin (GREEN).
#[test]
fn trace_operand_bare_twin() {
    run_prims("(defn f [] (trace 5))\n(defn main [] (Pure 0))\n").assert_exit(0);
}

// ---- BD-A2: trailing-form silent-drop siblings ×2 (RED, silent-accept) ---------

// IMPL-METHOD trailing form: `(defn m [x] x 999)` inside an impl silently DROPS
// `999` (contrast `parse_defn` which rejects). Sibling of the pinned
// `deftype_ctor_trailing_form_after_field_bracket_rejected_neg` family.
// spec: spec/05-definitions.md §5.1.1 — a defn body is a single form; a trailing
// form is rejected (must mirror `parse_defn`).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_impl_method (trailing form silently dropped; parse_defn rejects) found=S113 owner=/dev
#[test]
fn impl_method_trailing_form_rejected_neg() {
    let out = run_prims(
        "(deftrait T (m [self] Int))\n\
         (impl T Int (defn m [x] x 999))\n\
         (defn main [] (Pure (m 5)))\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "a trailing form after an impl-method body `(defn m [x] x 999)` MUST be \
         rejected (mirror `parse_defn`); today `999` is silently dropped and the \
         method returns `x`; got exit {:?}:\n{c}",
        out.status.code()
    );
}

// TRAIT-SIG trailing form: `(show [x] Int 999)` — a trailing form after the
// return type (no default body expected here) silently dropped.
// spec: spec/05-definitions.md §5.3 — a required method sig ends at its return type.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_method_sig (trailing form silently dropped) found=S113 owner=/dev
#[test]
fn trait_method_sig_trailing_form_rejected_neg() {
    let out = run_prims("(deftrait T (show [x] Int 999 888))\n(defn main [] (Pure 0))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "a trailing form after a trait method signature `(show [x] Int 999 888)` \
         MUST be rejected (a required sig ends at its return type; a single default \
         body is the only permitted following form); today extra forms are silently \
         dropped; got exit {:?}:\n{c}",
        out.status.code()
    );
}

// =============================================================================
// M1 matrix spot cells (s114-test-plan §5.1; enforcement-matrices.md §1). The nine
// CORRECT operand positions route their body through `build_one_expr_at` today:
// these born-green fences pin the ascribed-ACCEPT and trailing-REJECT columns at
// the spot positions that had no committed pin, so the one-seam fix (`build_body_to_end`)
// keeps them routed. A row that stops accepting `:Type body` or stops rejecting a
// trailing form after the seam adoption is caught here. (The WRONG positions —
// let-body, impl-method, trait-default, trace — are the BD-A1/A2 REDs above.)
// =============================================================================

// M1 ascribed spot-pin — FN BODY. `(fn [n] :Int n)` — the closure body is ascribed
// and MUST be accepted (routed). `(g 7)` = 7.
// spec: spec/03-types.md §2.3.8 — an annotation may appear in an `fn` body.
#[test]
fn m1_fn_body_ascription_accepted_spot() {
    run_prims("(defn f [] (let [g (fn [n] :Int n)] (g 7)))\n(defn main [] (Pure (f)))\n")
        .assert_exit(7);
}

// M1 ascribed spot-pin — IF BRANCHES. `(if c :Int 10 :Int 20)` — both branches
// ascribed, accepted. `(f 0)` = 10.
// spec: spec/03-types.md §2.3.8 — an annotation may appear in an `if` branch.
#[test]
fn m1_if_branch_ascription_accepted_spot() {
    run_prims(
        "(defn f [c] (if (eq-i64 c 0) :Int 10 :Int 20))\n(defn main [] (Pure (f 0)))\n",
    )
    .assert_exit(10);
}

// M1 ascribed spot-pin — MATCH ARM BODY. `(match v [x :Int x])` — the arm body
// ascribed, accepted. `(f 7)` = 7.
// spec: spec/03-types.md §2.3.8 — an annotation may appear in a match arm body.
#[test]
fn m1_match_arm_ascription_accepted_spot() {
    run_prims("(defn f [v] (match v [x :Int x]))\n(defn main [] (Pure (f 7)))\n").assert_exit(7);
}

// M1 ascribed spot-pin — LET VALUE. `(let [x :Int 7] x)` — the binding value
// ascribed, accepted. `(f)` = 7.
// spec: spec/03-types.md §2.3.8 — an annotation may appear in a `let` binding value.
#[test]
fn m1_let_value_ascription_accepted_spot() {
    run_prims("(defn f [] (let [x :Int 7] x))\n(defn main [] (Pure (f)))\n").assert_exit(7);
}

// M1 ascribed spot-pin — APPLY ARG. `(add-i64 :Int 3 4)` — an application argument
// ascribed (multi-operand position, `build_args_with_annotations`), accepted. = 7.
// spec: spec/03-types.md §2.3.8 — an annotation may appear in an application argument.
#[test]
fn m1_apply_arg_ascription_accepted_spot() {
    run_prims("(defn f [] (add-i64 :Int 3 4))\n(defn main [] (Pure (f)))\n").assert_exit(7);
}

// M1 REQUIRED trailing cell — LET BODY. `(let [x 1] x 9)` — a trailing form after
// the let body MUST be rejected (post-fix via `build_body_to_end`; today the
// arity-locked `!= 3` gate rejects it — the seam makes the reject structural, not
// incidental). Born-green fence.
// spec: spec/04-expressions.md §4.3 — a `let` body is a single form; a trailing form
// is rejected.
#[test]
fn m1_let_body_trailing_form_rejected_neg() {
    let out = run_prims("(defn f [] (let [x 1] x 9))\n(defn main [] (Pure (f)))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "a trailing form after a `let` body `(let [x 1] x 9)` MUST be rejected; \
         got exit {:?}:\n{c}",
        out.status.code()
    );
}

// M1 REQUIRED trailing cell — TRACE OPERAND. `(trace 5 9)` — a trailing form after
// the traced operand MUST be rejected (post-fix via the seam; today the arity gate
// rejects it). Born-green fence.
// spec: spec/04-expressions.md §4.12 — a `trace` takes a single operand form; a
// trailing form is rejected.
#[test]
fn m1_trace_trailing_form_rejected_neg() {
    let out = run_prims("(defn f [] (trace 5 9))\n(defn main [] (Pure 0))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "a trailing form after a `trace` operand `(trace 5 9)` MUST be rejected; \
         got exit {:?}:\n{c}",
        out.status.code()
    );
}

// M1 trailing spot cell — FN BODY. `(fn [n] n 9)` — a trailing form after the
// closure body MUST be rejected. Born-green fence.
// spec: spec/04-expressions.md §4.5 — an `fn` body is a single form; a trailing form
// is rejected.
#[test]
fn m1_fn_body_trailing_form_rejected_neg() {
    let out = run_prims("(defn f [] (let [g (fn [n] n 9)] (g 7)))\n(defn main [] (Pure (f)))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "a trailing form after an `fn` body `(fn [n] n 9)` MUST be rejected; got \
         exit {:?}:\n{c}",
        out.status.code()
    );
}
