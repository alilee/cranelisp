// deftype_constructor_form_rulings_s116.rs — S115 Phase 7 behaviour pins for the
// SETTLED USER RULINGS on `deftype` constructor form and nullary-constructor
// PATTERNS. Every reject cell is UNIMPLEMENTED at HEAD, so each is an **intended
// RED** whose flip trigger is the **S116 implementation wave** (S115 scribes the
// rulings and lands the pins only; no S115 fix wave carries them). The `/spec`
// scribing lands concurrently — the definition rulings in
// `spec/05-definitions.md §5.2`, the pattern ruling in `spec/02-grammar.md §2.5.1`.
//
// RULING 1 — parens on a constructor REQUIRE content.
//   `'(' CONSTRUCTOR_NAME ')'` — a parenthesized arm carrying NEITHER a docstring
//   NOR a field list — is a parse error. Bare `Red` and documented `(Red "doc")`
//   are the nullary spellings; an empty-content paren is not a third. (§5.2.2)
//
// RULING 2 — a NULLARY constructor may not share its type's name — and the
//   docstring is IRRELEVANT to the verdict. `(deftype Flag Flag)`,
//   `(deftype Flag (Flag))`, and the DOCUMENTED `(deftype Flag (Flag "doc"))` are
//   all compile-time errors: each names a nullary constructor `Flag` inside type
//   `Flag`. A documented nullary is legal only when its name DIFFERS from the type
//   (`(deftype Flag (Raised "doc"))`) — the docstring never rescues the shared
//   name. The type-name-as-constructor relation is the §5.2.1 PRODUCT form, reached
//   through a field list; the unit type is `(deftype Unit [])`, a zero-field
//   product, NOT a nullary sharing its type's name. (Settles the FIXME-0846
//   tension: the shared name is the fault, not the parens or the docstring.)
//   (§5.2.1/§5.2.2)
//
// RULING 3 — an EMPTY field list is illegal in a constructor ARM, legal in PRODUCT
//   position. `(deftype Flag (Flag []))` and `(deftype Something (Unit []))` reject:
//   an arm `'(' NAME '[' ']' ')'` is redundant — bare `NAME` already spells the
//   nullary variant. The SAME `[]` at deftype level — `(deftype Unit [])` — is the
//   zero-field product, the ONLY spelling of the unit type, and stays legal. The
//   distinction is position: a product field list at deftype level vs. an arm field
//   list inside the arm parens. (§5.2.1 product vs §5.2.2 arm)
//
// RULING 4 — `(Ctor)` is illegal as a PATTERN. A nullary variant is matched by its
//   BARE name (`Red`); a zero-binding parenthesized pattern `(Red)` is illegal. The
//   rule bites ONLY on the zero-binding paren — a parenthesized pattern that binds a
//   sub-pattern (`(Some x)`, `(Wrap x)`) stays legal. (§2.5.1)
//
// The GREEN controls carry equal weight: an over-broad implementation that rejects
// the whole neighbourhood must not pass. Each control is a spelling that MUST
// survive its ruling — the product form sharing its type name (§5.2.1), the
// documented nullary whose name DIFFERS (§5.2.5, its only spelling), the mixed sum
// type (§5.2.2), the plain enum (§5.2.3), the zero-field unit product, the
// bare-name pattern, and the binding pattern. `(deftype Flag ())` is the
// pre-existing anchor ruling 1 widens: it ALREADY rejects with
// `parse error: empty constructor`.
//
// Measured at HEAD (fresh cwd, `CRANELISP_LIB` pinned via primitives-only prelude):
// every reject cell is ACCEPTED today (the `; deftype` marker is present, or the
// match evaluates with no diagnostic); every control behaves as pinned.

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

/// Pattern-position reject (ruling 4). Unlike a definition reject, the snippet
/// legitimately DEFINES a type first, so the `; deftype` acceptance marker IS
/// present and cannot be the reject signal. The reject signal is a diagnostic on
/// the `match` itself: at HEAD `(Ctor)` parses as a zero-binding constructor
/// pattern and the match evaluates cleanly, so the absence of `error` is the RED.
fn assert_match_rejected(c: &str, form: &str, why: &str) {
    assert!(
        c.to_lowercase().contains("error"),
        "`{form}` MUST produce a compile-time diagnostic — {why}. It is ACCEPTED \
         at HEAD (the match evaluates with no diagnostic); flips with the S116 \
         implementation wave. got:\n{c}"
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
// RULING 3 — an empty field list is illegal in a constructor ARM. Two REDs.
// ---------------------------------------------------------------------------

// RED — the empty field list inside an arm. `(Flag [])` is a zero-field product
// arm; the bare `Flag` already spells the nullary variant, so the arm form is
// redundant and rejects. (It ALSO shares the type name — the isolating sibling
// below removes that confound.)
// spec: spec/05-definitions.md §5.2.2 — Sum Type (Multiple Constructors)
// [S115 ruling — an empty field list is illegal in a constructor ARM (legal only
// as a §5.2.1 zero-field PRODUCT at deftype level); implementation carries to S116]
// defect: class=silent-accept locus=frontend deftype constructor arm parser — empty field list in an arm admitted as a nullary found=S115 owner=/dev
#[test]
fn deftype_empty_field_list_arm_rejected_neg() {
    let c = repl_prims("(deftype Flag (Flag []))\n");
    assert_rejected(
        &c,
        "(deftype Flag (Flag []))",
        "an empty field list is illegal inside a constructor arm — the bare name \
         `Flag` already spells the nullary variant; the empty `[]` is legal only \
         as a zero-field PRODUCT at deftype level (`(deftype Unit [])`)",
    );
}

// RED — the empty-field-list arm with a name that DIFFERS from the type, so the
// reject can ONLY be the ruling-3 empty-field-list fault, never the ruling-2
// shared-name fault. This is the clean isolation of ruling 3.
// spec: spec/05-definitions.md §5.2.2 — Sum Type (Multiple Constructors)
// [S115 ruling — an empty field list is illegal in a constructor ARM regardless of
// the arm's name; implementation carries to S116]
// defect: class=silent-accept locus=frontend deftype constructor arm parser — empty field list in a differently-named arm admitted as a nullary found=S115 owner=/dev
#[test]
fn deftype_empty_field_list_arm_name_differs_rejected_neg() {
    let c = repl_prims("(deftype Something (Unit []))\n");
    assert_rejected(
        &c,
        "(deftype Something (Unit []))",
        "an empty field list is illegal inside a constructor arm even when the \
         arm's name differs from the type — the fault is the redundant empty `[]` \
         in arm position, not any name-sharing",
    );
}

// ---------------------------------------------------------------------------
// BORN-GREEN CONTROLS — the boundary the rulings MUST NOT cross.
// ---------------------------------------------------------------------------

// GREEN — the unit type. The single most important control in the file: it is
// the sanctioned spelling under BOTH ruling 2 and ruling 3, so two over-broad
// implementations would break it. Ruling 2: an implementation that rejects
// `(deftype Flag Flag)` by banning "type name equals constructor name" wholesale
// breaks it. Ruling 3: an implementation that rejects the empty field list `[]`
// WHOLESALE — instead of only in arm position — breaks it. The `[]` here is a
// product field list at DEFTYPE level (the zero-field product, the only spelling
// of the unit type); the ruling-3 reject bites the SAME `[]` only when it sits
// inside an arm's parens.
// spec: spec/05-definitions.md §5.2.1 — Product Type (Single Constructor)
// [S115 ruling — the unit type is `(deftype Unit [])`; the empty `[]` is legal
// as a zero-field product, illegal only inside a constructor arm]
#[test]
fn deftype_unit_zero_field_product_control_green() {
    let c = repl_prims("(deftype Unit [])\n");
    assert_accepted(
        &c,
        "(deftype Unit [])",
        "the zero-field product IS the unit type's spelling (ruling 2); the empty \
         `[]` at deftype level is a legal PRODUCT field list, and ruling 3 rejects \
         `[]` only inside an arm's parens",
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

// RED — the documented nullary that ALSO shares its type's name. This is where
// rulings 1 and 2 meet, and the user has SETTLED it (2026-07-21): `(Flag "doc")`
// is a nullary constructor named `Flag` inside type `Flag`, and a nullary variant
// may not share its type's name. The docstring is IRRELEVANT to the verdict — it
// makes the paren legal under ruling 1, but ruling 2 rejects on the shared NAME,
// not the parens. The isolation control below (name differs) proves this is not a
// ban on docstrings. Settles the FIXME-0846 tension. Accepted at HEAD.
// spec: spec/05-definitions.md §5.2.2 — Sum Type (Multiple Constructors)
// [S115 ruling — a nullary constructor may not share its type's name; the
// docstring does not rescue the shared name; implementation carries to S116]
// defect: class=silent-accept locus=frontend deftype constructor-registration seam — documented nullary sharing the type name admitted found=S115 owner=/dev
#[test]
fn deftype_documented_nullary_sharing_type_name_rejected_neg() {
    let c = repl_prims("(deftype Flag (Flag \"a documented nullary\"))\n");
    assert_rejected(
        &c,
        "(deftype Flag (Flag \"a documented nullary\"))",
        "a nullary constructor may not share its type's name; the docstring makes \
         the paren legal but does NOT rescue the shared name — the fault is the \
         name, not the parens or the docstring",
    );
}

// GREEN — the isolation control for the reject above: a DOCUMENTED nullary whose
// name DIFFERS from the type, in a polymorphic sum type. This proves the ruling-2
// reject bites on the shared NAME, never on the docstring — a documented nullary
// is perfectly legal when it does not repeat the type's name. If this went RED
// alongside the reject above, the S116 implementation banned docstrings on nullary
// constructors, which is NOT the ruling.
// spec: spec/05-definitions.md §5.2.5 — Docstrings on Types and Constructors
#[test]
fn deftype_documented_nullary_name_differs_polymorphic_control_green() {
    let c = repl_prims("(deftype (Opt a) (None \"a documented nullary\") (Some [:a v]))\n");
    assert_accepted(
        &c,
        "(deftype (Opt a) (None \"a documented nullary\") (Some [:a v]))",
        "a documented nullary whose name DIFFERS from the type is legal; ruling 2 \
         rejects the shared NAME, not the docstring",
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

// ---------------------------------------------------------------------------
// RULING 4 — `(Ctor)` is illegal as a PATTERN. One RED + two GREEN controls.
// A nullary variant is matched by its bare name; a zero-binding parenthesized
// pattern is illegal. The reject snippet legitimately defines a type first (so
// the `; deftype` marker is present) — the reject signal is a diagnostic on the
// `match`, checked by `assert_match_rejected`, not the marker's absence.
// ---------------------------------------------------------------------------

// RED — the zero-binding parenthesized pattern `(Red)`. A nullary variant `Red`
// is matched by its BARE name; the empty-parens pattern carries no bindings and
// is illegal. At HEAD `(Red)` parses as a constructor pattern with zero bindings
// and the match evaluates to 1 with no diagnostic; it must reject at S116.
// spec: spec/02-grammar.md §2.5.1 — Constructor Pattern
// [S115 ruling — `(Ctor)` with zero bindings is illegal in pattern position; a
// nullary variant is matched by its bare name; implementation carries to S116]
// defect: class=silent-accept locus=frontend match pattern parser — zero-binding parenthesized constructor pattern admitted found=S115 owner=/dev
#[test]
fn match_nullary_constructor_empty_parens_pattern_rejected_neg() {
    let c = repl_prims(
        "(deftype Color Red Green Blue)\n\
         (defn f [:Color c] (match c [(Red) 1 Green 2 Blue 3]))\n\
         (f Red)\n",
    );
    assert_match_rejected(
        &c,
        "(match c [(Red) 1 Green 2 Blue 3])",
        "a nullary variant is matched by its BARE name `Red`; the zero-binding \
         parenthesized pattern `(Red)` carries no bindings and is illegal",
    );
}

// GREEN — the bare-name pattern control. `Red` bare is the sanctioned spelling
// for matching a nullary variant; ruling 4's reject is about the zero-binding
// PARENS, never about bare nullary names. If this went RED the S116 pattern
// implementation over-reached onto the legal bare form.
// spec: spec/02-grammar.md §2.5.1 — Constructor Pattern
#[test]
fn match_nullary_constructor_bare_name_pattern_control_green() {
    let c = repl_prims(
        "(deftype Color Red Green Blue)\n\
         (defn f [:Color c] (match c [Red 1 Green 2 Blue 3]))\n\
         (f Red)\n",
    );
    assert_accepted(
        &c,
        "(match c [Red 1 Green 2 Blue 3])",
        "the bare name `Red` is the §2.5.1 nullary-pattern spelling; ruling 4 bites \
         only on the zero-binding parenthesized form",
    );
}

// GREEN — the binding-pattern control. A parenthesized pattern that DOES bind a
// sub-pattern (`(Wrap x)`) is legal and untouched — ruling 4 bites ONLY on the
// zero-binding paren. A unique constructor name (`Wrap`, not `Some`) avoids the
// bare-`Some` ambiguity against any ambient primitives-level `Some`.
// spec: spec/02-grammar.md §2.5.1 — Constructor Pattern
#[test]
fn match_constructor_pattern_binding_subpattern_control_green() {
    let c = repl_prims(
        "(deftype (Box a) (Wrap [:a v]))\n\
         (match (Wrap 5) [(Wrap x) x])\n",
    );
    assert_accepted(
        &c,
        "(match (Wrap 5) [(Wrap x) x])",
        "a parenthesized pattern that binds a sub-pattern is legal; ruling 4 rejects \
         only the ZERO-binding parenthesized pattern",
    );
}
