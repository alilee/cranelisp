// ra_annotation_qualifier_0682.rs — Track D RA cells (s114-test-plan §5.2;
// design/frontend/enforcement-matrices.md §3; user ruling 2026-07-20).
//
// `:` is a `^`-style reader macro — whitespace between `:` and its form ALLOWED
// (`: Int` ≡ `:Int`); the bound form MUST be a type expression; `:foo/` ERRORS;
// bare `foo/` ERRORS anywhere; `/bar` (empty module half) ERRORS; bare `/`
// (division) stands. Spec anchors: §1.4.5, §2.3.8, §2.4, §8.5.1 (all [S114]).
//
// Flip: the RA rows flip with the /dev(frontend) W-D1 change-set (RA reader
// consolidation — ONE `consume_dotted_module_path` + `/bar` `read_operator` guard +
// the `try_consume_annotation` bare-`:` type-form reject). The RA-N4 bare-`/`
// division fence is the acid test the reject does not over-reach (Principle 16).
//
// POLARITY NOTE (/testing, verified 2026-07-20; reported to /qa): at HEAD only
// RA-N1/RA-N2 (`:foo/`, `:a.b/` annotation-position dangling qualifiers) are RED
// (SILENTLY ACCEPTED, degrade to `:foo`/`:a.b`). RA-N3 (`foo/` value+operand)
// ALREADY errors located ("expected local name after '/'") — born-green. RA-P1/P2
// (space tolerance) ALREADY work — born-green. RA-N4 division fence — born-green.
// RA-N5 (`:3`) already errors (incidentally). RA-N6 (`/bar`) errors today but via
// an INCIDENTAL split (`/`+`bar` → extra-forms / undefined-`/`), NOT the located
// empty-module-half reject — so RA-N6 asserts the LOCATED qualifier reject and is
// RED until W-D1's `read_operator` guard lands. Free-standing.

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

fn combined(out: &helpers::e2e::CrOutput) -> String {
    format!("{}{}", out.stdout, out.stderr)
}

// ---- RA-P1 — space tolerance, PARAM position (born-green fence) -----------------

// `(defn f [: Int x] :Int x)` — the spaced `: Int` annotation binds the param `x`
// exactly as `:Int x` does. Both spellings MUST give the same result. `(f 7)` = 7.
// spec: spec/02-grammar.md §2.3.8 — `:` is a `^`-style reader macro; whitespace
// between `:` and its form is permitted (`: Int` ≡ `:Int`).
#[test]
fn space_tolerance_param_position_equiv() {
    run_prims("(defn f [: Int x] :Int x)\n(defn main [] (Pure (f 7)))\n").assert_exit(7);
    run_prims("(defn f [:Int x] :Int x)\n(defn main [] (Pure (f 7)))\n").assert_exit(7);
}

// ---- RA-P2 — space tolerance, EXPRESSION position (born-green fence) ------------

// A spaced annotation in an expression (let-value) position `: Int` ≡ `:Int`, and a
// list-form type `: (Fn [Int] Int)` is accepted. Both `(let [x : Int 7] x)` and the
// no-space spelling give 7; the list-form annotates a closure.
// spec: spec/02-grammar.md §2.3.8 — whitespace tolerance in every expression
// position, including a list-form type `: (Fn [Int] Int)`.
#[test]
fn space_tolerance_expression_position_equiv() {
    run_prims("(defn f [] (let [x : Int 7] x))\n(defn main [] (Pure (f)))\n").assert_exit(7);
    run_prims("(defn f [] (let [x :Int 7] x))\n(defn main [] (Pure (f)))\n").assert_exit(7);
    // list-form spaced annotation on a closure value.
    run_prims(
        "(defn f [] (let [g : (Fn [Int] Int) (fn [n] (add-i64 n 1))] (g 4)))\n\
         (defn main [] (Pure (f)))\n",
    )
    .assert_exit(5);
}

// ---- RA-N1/N2 — dangling qualifier in ANNOTATION position (RED, silent-accept) --

// `:foo/` MUST be a located error; today `read_qualified_tail` silently degrades it
// to `:foo` (a minted type-var annotation), so the program compiles and exits 0.
// spec: spec/01-lexical.md §1.4.5 — a dangling qualifier (`:foo/`) is a located
// error, never a silent degradation to `:foo`.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/reader.rs::read_qualified_tail (`:foo/` degrades to `:foo`; located reject re-lands W-D1) found=S114 owner=/dev
#[test]
fn annotation_dangling_qualifier_empty_local_rejected_neg() {
    let out = run_prims("(defn f [] :foo/ 5)\n(defn main [] (Pure 0))\n");
    let c = combined(&out);
    assert!(
        out.status.code() != Some(0) && c.to_lowercase().contains("error"),
        "`:foo/` (empty local half) MUST be a located error (§1.4.5), NOT silently \
         degrade to `:foo` and compile; got exit {:?}:\n{c}",
        out.status.code()
    );
}

// `:a.b/` — the dotted-module swallow mirror. Same reject.
// spec: spec/01-lexical.md §1.4.5 — `:a.b/` (dotted module, empty local) is a
// located error, not a degradation to `:a.b`.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/reader.rs::read_qualified_tail (dotted `:a.b/` swallow; located reject re-lands W-D1) found=S114 owner=/dev
#[test]
fn annotation_dangling_qualifier_dotted_empty_local_rejected_neg() {
    let out = run_prims("(defn f [] :a.b/ 5)\n(defn main [] (Pure 0))\n");
    let c = combined(&out);
    assert!(
        out.status.code() != Some(0) && c.to_lowercase().contains("error"),
        "`:a.b/` (dotted module, empty local half) MUST be a located error (§1.4.5), \
         NOT silently degrade to `:a.b`; got exit {:?}:\n{c}",
        out.status.code()
    );
}

// ---- RA-N3 — bare `foo/` in value + operand position (born-green fence) ---------

// `foo/` (empty local half) in value position already errors located ("expected
// local name after '/'"). Born-green fence — must stay rejected through W-D1.
// spec: spec/08-modules.md §8.5.1 — a dangling qualifier `foo/` is a located error
// in every position (value).
#[test]
fn bare_dangling_qualifier_value_position_rejected() {
    let out = run_prims("(defn f [] foo/)\n(defn main [] (Pure 0))\n");
    let c = combined(&out);
    assert!(
        out.status.code() != Some(0) && c.to_lowercase().contains("error"),
        "bare `foo/` in value position MUST be a located error (§8.5.1); got exit \
         {:?}:\n{c}",
        out.status.code()
    );
}

// `foo/` in operand position — same reject.
// spec: spec/08-modules.md §8.5.1 — a dangling qualifier is a located error in
// operand position too.
#[test]
fn bare_dangling_qualifier_operand_position_rejected() {
    let out = run_prims("(defn f [] (add-i64 foo/ 1))\n(defn main [] (Pure 0))\n");
    let c = combined(&out);
    assert!(
        out.status.code() != Some(0) && c.to_lowercase().contains("error"),
        "bare `foo/` in operand position MUST be a located error (§8.5.1); got exit \
         {:?}:\n{c}",
        out.status.code()
    );
}

// ---- RA-N4 — bare `/` division GREEN fence (must stay green) --------------------

// `(/ 6 2)` → 3. The lone `/` (both halves empty) is the division operator, NOT a
// dangling qualifier — the acid test that the qualifier reject does not over-reach
// (Principle 16). Uses TestStandard (Num operators). MUST stay GREEN through W-D1.
// spec: spec/08-modules.md §8.5.1 — a lone `/` is the division symbol, not a
// dangling qualifier (the bare-`/` MUST-NOT-over-reach fence).
#[test]
fn bare_slash_division_stays_legal_green() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .run("user.cl")
        .user("(defn main [] (Pure (/ 6 2)))\n")
        .output()
        .assert_exit(3);
}

// ---- RA-N5 — bound form must be a type expression (born-green reject) -----------

// `:3` binds a non-type form (an Int literal) — a compile-time error. Today the
// bare-`:` arm SWALLOWS the `build_type_expr` failure and degrades `:` to a `Var`,
// so `:3` is silently accepted and the only error is the INCIDENTAL "defn has extra
// forms" from the degraded tokens. The fix makes the reject a located "the form
// bound by `:` must be a type expression". This cell asserts ONLY the non-type-form
// reject (the 0589 lowercase-mints-a-var family is separate); RED until W-D1
// (asserting the incidental artifact is ABSENT).
// spec: spec/02-grammar.md §2.3.8 — the form bound by `:` MUST be a type expression;
// a non-type bound form is a compile-time error.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::try_consume_annotation (bare-`:` swallows a non-type bound form → degrades to `Var`; located reject re-lands W-D1) found=S114 owner=/dev
#[test]
fn annotation_non_type_bound_form_rejected_neg() {
    let out = run_prims("(defn f [] :3 5)\n(defn main [] (Pure 0))\n");
    let c = combined(&out).to_lowercase();
    assert!(
        out.status.code() != Some(0) && !c.contains("extra forms"),
        "`:3` binds a non-type form (Int literal) — MUST be a LOCATED compile-time \
         error (§2.3.8: the form bound by `:` must be a type expression), NOT \
         silently accepted with `:` degraded to a `Var` (surfacing only the \
         incidental `defn has extra forms`); got exit {:?}:\n{}",
        out.status.code(),
        combined(&out)
    );
}

// ---- RA-N6 — `/bar` empty-module-half (RED, located reject re-lands W-D1) -------

// `/bar` (empty module half) MUST be a LOCATED dangling-qualifier error (user
// confirmation 2026-07-20; §8.5.1 symmetric reading). Today the reader SPLITS it
// into `/` + `bar` — value position yields an incidental "defn has extra forms",
// operand position yields "undefined variable: /" — NEITHER the located qualifier
// reject. RED until W-D1's `read_operator` `/bar` guard lands (the ONE genuinely-
// new lexical reject). The reject must name the module/qualifier problem, NOT be an
// incidental split artifact.
// spec: spec/08-modules.md §8.5.1 — `/bar` (empty module half) is a located
// compile-time error in every position (value).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/reader.rs::read_operator (`/bar` splits into `/`+`bar`; located empty-module-half reject re-lands W-D1) found=S114 owner=/dev
#[test]
fn slash_bar_empty_module_half_value_position_rejected_neg() {
    let out = run_prims("(defn f [] /bar)\n(defn main [] (Pure 0))\n");
    let c = combined(&out).to_lowercase();
    // RED today: the reject is the INCIDENTAL split artifact "defn has extra forms"
    // (the reader splits `/bar` into `/`+`bar`), NOT a located empty-module-half
    // reject. Asserting the artifact is ABSENT makes this RED now, GREEN when
    // W-D1's `read_operator` guard lands the located reject (which fires at
    // tokenization, before the defn-tail — so "extra forms" cannot appear).
    assert!(
        out.status.code() != Some(0)
            && !c.contains("extra forms")
            && !c.contains("undefined variable"),
        "`/bar` (empty module half) MUST be a LOCATED dangling-qualifier error at \
         the `/` token (§8.5.1) — today the reader splits it into `/`+`bar` and \
         errors only incidentally (`defn has extra forms`); got exit {:?}:\n{}",
        out.status.code(),
        combined(&out)
    );
}

// `/bar` in operand position — same located reject (today: "undefined variable: /").
// spec: spec/08-modules.md §8.5.1 — `/bar` is a located error in operand position.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/reader.rs::read_operator (`/bar` operand-position split; located reject re-lands W-D1) found=S114 owner=/dev
#[test]
fn slash_bar_empty_module_half_operand_position_rejected_neg() {
    let out = run_prims("(defn f [] (add-i64 /bar 1))\n(defn main [] (Pure 0))\n");
    let c = combined(&out).to_lowercase();
    // RED today: the reject is the INCIDENTAL "undefined variable: /" (the reader
    // splits `/bar` into `/`+`bar`), NOT a located empty-module-half reject.
    // GREEN when W-D1's `read_operator` guard lands (rejects at the `/` token).
    assert!(
        out.status.code() != Some(0)
            && !c.contains("extra forms")
            && !c.contains("undefined variable"),
        "`/bar` (empty module half) in operand position MUST be a LOCATED \
         dangling-qualifier error at the `/` token (§8.5.1) — today it errors only \
         as `undefined variable: /`; got exit {:?}:\n{}",
        out.status.code(),
        combined(&out)
    );
}
