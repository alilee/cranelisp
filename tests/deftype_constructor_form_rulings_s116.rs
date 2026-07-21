// deftype_constructor_form_rulings_s116.rs — S115 Phase 7 behaviour pins for two
// settled USER RULINGS on `deftype` constructor form. BOTH are UNIMPLEMENTED at
// HEAD, so the four reject cells are **intended REDs** whose flip trigger is the
// **S116 implementation wave** (S115 scribes the rulings and lands the pins only;
// no S115 fix wave carries them). The `/spec` scribing of the rulings into
// `spec/05-definitions.md` §5.2 lands in this same phase, concurrently.
//
// RULING 1 — parens on a constructor REQUIRE content.
//   `'(' CONSTRUCTOR_NAME ')'` — a parenthesized constructor arm carrying
//   NEITHER a docstring NOR a field list — is a **parse error**. The `deftype`
//   grammar's nullary arms are the bare name (`Red`) and the documented form
//   (`(Red "doc")`); an empty-content paren is not a third spelling of the bare
//   name. Accepted at HEAD.
//
// RULING 2 — a NULLARY constructor may not share its type's name.
//   `(deftype Flag Flag)` is a compile-time error. The type name doubling as a
//   constructor is the §5.2.1 PRODUCT form and is reached through a field list
//   — `(deftype Point [:Int x :Int y])`. The unit type is spelled
//   `(deftype Unit [])`, a product with zero fields, NOT a nullary constructor
//   sharing its type's name. Accepted at HEAD.
//
// The GREEN controls carry equal weight: an over-broad implementation that
// rejects the whole neighbourhood must not be able to pass. Each control is a
// spelling that MUST survive both rulings — the product form sharing its type
// name (§5.2.1), the documented nullary (§5.2.5, which has no other spelling),
// the mixed sum type (§5.2.2), the plain enum (§5.2.3), and the unit type
// itself. `(deftype Flag ())` is the pre-existing anchor the ruling-1 reject
// widens: it ALREADY rejects with `parse error: empty constructor`, and the
// widened rule must reach `(deftype Flag (Flag))` the same way.
//
// Measured at HEAD (fresh cwd, `CRANELISP_LIB` pinned): all four reject cells
// print `:user/… ; deftype`; all six controls behave as pinned.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn repl_prims(lines: &str) -> String {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output();
    format!("{}{}", out.stdout, out.stderr)
}

/// The acceptance marker the REPL prints for an admitted `deftype`.
const ACCEPTED: &str = "; deftype";

fn assert_rejected(c: &str, form: &str, why: &str) {
    assert!(
        !c.contains(ACCEPTED),
        "`{form}` MUST be rejected — {why}. It is ACCEPTED at HEAD (the \
         `{ACCEPTED}` marker is present); flips with the S116 implementation \
         wave. got:\n{c}"
    );
    assert!(
        c.to_lowercase().contains("error"),
        "`{form}` MUST produce a compile-time diagnostic — {why}; got:\n{c}"
    );
}

fn assert_accepted(c: &str, form: &str, why: &str) {
    assert!(
        c.contains(ACCEPTED),
        "`{form}` MUST stay accepted — {why}. A reject here means the S116 \
         implementation of the constructor-form rulings over-reached. got:\n{c}"
    );
    assert!(
        !c.to_lowercase().contains("error"),
        "`{form}` MUST NOT produce any diagnostic — {why}; got:\n{c}"
    );
}

// ---------------------------------------------------------------------------
// RULING 1 — parens on a constructor require content. Three REDs.
// ---------------------------------------------------------------------------

// RED — the minimal face: one content-free parenthesized arm.
// spec: spec/05-definitions.md §5.2.2 — Sum Type (Multiple Constructors)
// [S115 ruling — `'(' CTOR ')'` with neither docstring nor field list is a parse
// error; implementation carries to S116]
// defect: class=silent-accept locus=frontend deftype constructor arm parser — content-free parenthesized ctor admitted as a bare nullary found=S115 owner=/dev
#[test]
fn deftype_content_free_paren_constructor_rejected_neg() {
    let c = repl_prims("(deftype Flag (Flag))\n");
    assert_rejected(
        &c,
        "(deftype Flag (Flag))",
        "a parenthesized constructor arm must carry a docstring or a field list; \
         empty parens are not a third spelling of the bare nullary name",
    );
}

// RED — the content-free paren MIXED with legal bare-nullary siblings, so the
// reject cannot be an artifact of the arm being the only one.
// spec: spec/05-definitions.md §5.2.3 — Enum (All Nullary) [S115 ruling —
// `'(' CTOR ')'` requires content; implementation carries to S116]
// defect: class=silent-accept locus=frontend deftype constructor arm parser — content-free paren alongside bare-nullary siblings found=S115 owner=/dev
#[test]
fn deftype_content_free_paren_among_bare_nullaries_rejected_neg() {
    let c = repl_prims("(deftype Color (Red) Green Blue)\n");
    assert_rejected(
        &c,
        "(deftype Color (Red) Green Blue)",
        "the `(Red)` arm carries neither docstring nor field list; the legal \
         spelling alongside `Green`/`Blue` is the bare name `Red`",
    );
}

// RED — the polymorphic face: content-free paren beside a legal fielded arm in
// a parameterised type head. Pins that neither the type parameter nor the
// well-formed sibling arm rescues the malformed one.
// spec: spec/05-definitions.md §5.2.2 — Sum Type (Multiple Constructors)
// [S115 ruling — `'(' CTOR ')'` requires content; implementation carries to S116]
// defect: class=silent-accept locus=frontend deftype constructor arm parser — content-free paren in a polymorphic sum type found=S115 owner=/dev
#[test]
fn deftype_content_free_paren_in_polymorphic_type_rejected_neg() {
    let c = repl_prims("(deftype (Maybe a) (Nothing) (Just [:a val]))\n");
    assert_rejected(
        &c,
        "(deftype (Maybe a) (Nothing) (Just [:a val]))",
        "`(Nothing)` carries neither docstring nor field list; the legal spelling \
         is the bare `Nothing`",
    );
}

// ---------------------------------------------------------------------------
// RULING 2 — a nullary constructor may not share its type's name. One RED.
// ---------------------------------------------------------------------------

// RED — the bare nullary sharing the type name. The type-name-as-constructor
// relation is the §5.2.1 product form and is reached through a field list; the
// zero-field product `(deftype Unit [])` is the unit type's spelling (control
// below).
// spec: spec/05-definitions.md §5.2.1 — Product Type (Single Constructor)
// [S115 ruling — a nullary constructor may not share its type's name; the unit
// type is `(deftype Unit [])`; implementation carries to S116]
// defect: class=silent-accept locus=frontend deftype constructor-registration seam — bare nullary sharing the type name admitted found=S115 owner=/dev
#[test]
fn deftype_nullary_constructor_sharing_type_name_rejected_neg() {
    let c = repl_prims("(deftype Flag Flag)\n");
    assert_rejected(
        &c,
        "(deftype Flag Flag)",
        "a nullary constructor may not share its type's name; the type name \
         doubles as a constructor only through the §5.2.1 product field-list \
         form, and the unit type is spelled `(deftype Unit [])`",
    );
}

// ---------------------------------------------------------------------------
// BORN-GREEN CONTROLS — the boundary the two rulings MUST NOT cross.
// ---------------------------------------------------------------------------

// GREEN — the unit type. Ruling 2 names this as the sanctioned spelling, so it
// is the single most important control in the file: an implementation that
// rejects `(deftype Flag Flag)` by banning "type name equals constructor name"
// wholesale would break it.
// spec: spec/05-definitions.md §5.2.1 — Product Type (Single Constructor)
// [S115 ruling — the unit type is `(deftype Unit [])`]
#[test]
fn deftype_unit_zero_field_product_control_green() {
    let c = repl_prims("(deftype Unit [])\n");
    assert_accepted(
        &c,
        "(deftype Unit [])",
        "the zero-field product IS the unit type's spelling under ruling 2",
    );
}

// GREEN — the ordinary product constructor sharing its type name. Ruling 2
// bites on NULLARY constructors only; §5.2.1's whole design is the type name
// doubling as the sole constructor over a field list.
// spec: spec/05-definitions.md §5.2.1 — Product Type (Single Constructor)
#[test]
fn deftype_product_constructor_sharing_type_name_control_green() {
    let c = repl_prims("(deftype Point [:primitives/Int x :primitives/Int y])\n");
    assert_accepted(
        &c,
        "(deftype Point [:primitives/Int x :primitives/Int y])",
        "a PRODUCT constructor sharing the type name is the normal §5.2.1 form; \
         ruling 2 restricts NULLARY constructors only",
    );
}

// GREEN — the documented nullary. Ruling 1 bans the CONTENT-FREE paren; a
// docstring IS content, and §5.2.5 gives the documented nullary no other
// spelling (a bare `Raised` has nowhere to hang its docstring).
// spec: spec/05-definitions.md §5.2.5 — Docstrings on Types and Constructors
#[test]
fn deftype_documented_nullary_control_green() {
    let c = repl_prims("(deftype Flag (Raised \"a documented nullary\"))\n");
    assert_accepted(
        &c,
        "(deftype Flag (Raised \"a documented nullary\"))",
        "a docstring is content; §5.2.5's documented nullary has no other spelling",
    );
}

// GREEN — the documented nullary that ALSO shares its type's name. This is the
// cell where rulings 1 and 2 meet: the paren is legal (docstring = content), and
// the constructor is nullary AND named `Flag` like its type. It is GREEN at HEAD
// and pinned green per the Phase-7 dispatch — but the two rulings as stated do
// not settle it between them (ruling 2 says "a nullary constructor may not share
// its type's name" without excepting the documented spelling, which would make
// this a reject and leave a documented nullary with NO legal same-name form).
// FIXME 0846 (`/spec`) carries the question; if the ruling is scribed to reach
// the documented spelling, this cell flips to `assert_rejected` with the other
// ruling-2 RED — it is a pin awaiting a scribe, not settled coverage.
// spec: spec/05-definitions.md §5.2.5 — Docstrings on Types and Constructors
#[test]
fn deftype_documented_nullary_sharing_type_name_control_green() {
    let c = repl_prims("(deftype Flag (Flag \"a documented nullary\"))\n");
    assert_accepted(
        &c,
        "(deftype Flag (Flag \"a documented nullary\"))",
        "the docstring makes the paren legal under ruling 1; ruling 2's reach \
         over this spelling is open (FIXME 0846)",
    );
}

// GREEN — the mixed sum type: a bare nullary arm beside a fielded arm. Both
// spellings are legal under both rulings.
// spec: spec/05-definitions.md §5.2.2 — Sum Type (Multiple Constructors)
#[test]
fn deftype_mixed_bare_nullary_and_fielded_control_green() {
    let c = repl_prims("(deftype Shape Square (Circle [:primitives/Int r]))\n");
    assert_accepted(
        &c,
        "(deftype Shape Square (Circle [:primitives/Int r]))",
        "bare nullary + fielded arms are the ordinary §5.2.2 sum type",
    );
}

// GREEN — the plain enum. Ruling 1's reject is about PARENS, never about bare
// nullary names.
// spec: spec/05-definitions.md §5.2.3 — Enum (All Nullary)
#[test]
fn deftype_plain_enum_control_green() {
    let c = repl_prims("(deftype Color Red Green Blue)\n");
    assert_accepted(
        &c,
        "(deftype Color Red Green Blue)",
        "bare nullary names are the §5.2.3 enum form and carry no parens at all",
    );
}

// GREEN ANCHOR — the pre-existing behaviour ruling 1 widens. `(deftype Flag ())`
// — parens with no name at all — ALREADY rejects with `parse error: empty
// constructor`. Ruling 1 extends that reject from "no name" to "no content";
// this cell pins the anchor so the widening is visibly an extension of one
// diagnostic rather than a second, parallel check.
// spec: spec/05-definitions.md §5.2.2 — Sum Type (Multiple Constructors)
#[test]
fn deftype_empty_parens_constructor_rejected_neg_anchor() {
    let c = repl_prims("(deftype Flag ())\n");
    assert!(
        !c.contains(ACCEPTED),
        "`(deftype Flag ())` already rejects at HEAD and MUST keep rejecting; \
         got:\n{c}"
    );
    assert!(
        c.contains("empty constructor"),
        "the existing anchor diagnostic is `parse error: empty constructor` — \
         ruling 1's widened reject should extend THIS diagnostic, not add a \
         parallel one; got:\n{c}"
    );
}
