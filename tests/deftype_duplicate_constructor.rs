// deftype_duplicate_constructor.rs — S115 Phase 7, live defect pin.
//
// A `deftype` that declares the SAME constructor name twice is accepted
// silently at HEAD — no error, no warning, no ambiguity diagnostic:
//
//     (deftype Flag (Flag) (Flag))    ->  :user/Flag ; deftype
//                                          ; match:
//                                          ;  Flag Flag
//
// The consequence is not cosmetic. Each `deftype` arm mints a distinct variant
// (§5.2.2) and a module-level callable keyed on the constructor name, so the
// two arms contend for ONE key: the later arm wins and the earlier variant
// becomes **unconstructible and unmatchable** while still occupying a tag.
// Measured at HEAD in a fresh cwd (`CRANELISP_LIB` pinned, no `user.cl`):
//
//     (deftype T (P [:Int a]) (P [:String b]))   ; accepted, ; match: P P
//     (P 1)  ->  type error: expected primitives/String, got primitives/Int
//
// — the `:Int` variant declared FIRST cannot be built at all, and nothing said
// so. Same for the enum spelling: `(deftype C Red Red Green)` is accepted and
// `(match c [Red 1 Red 2 Green 3])` returns 1 with no unreachable-arm error.
//
// SPEC BASIS — the rule is NOT stated, the invariant it breaks IS.
// `spec/05-definitions.md` §5.2 never says constructor names within one
// `deftype` must be distinct. What the spec DOES state normatively:
//
//   - §5.2.2 — "each introduces a **distinct** variant"; a constructor name is
//     a **binder** minting a module-level callable;
//   - `spec/08-modules.md` §8.5.2 — `Type.Ctor` is the CANONICAL constructor
//     name, and "`Type.member` always denotes exactly one thing … leaving the
//     canonical `Type.member` a unique referent in **every case**". §8.5.2
//     reaches that conclusion by enumerating the possible collisions as
//     accessor-vs-method only — it never considered ctor-vs-ctor WITHIN one
//     type, which is exactly what these cells produce (`T.P` denoting two
//     distinct variants).
//   - §8.6.5's duplicate-constructor ruling covers the CROSS-type case and is
//     explicitly reasoned as permitted because "each is a derived member of a
//     **distinct** in-scope type" — that reasoning does not extend here, and
//     the alias-poison remedy is unavailable: there is no second canonical form
//     to disambiguate to.
//
// So the disposition is spec-DERIVED (rejection is the only outcome consistent
// with §8.5.2's uniqueness invariant) but not spec-STATED. FIXME 0845 (`/spec`)
// asks for the rule to be scribed, with the diagnostic wording and the sibling
// duplicate-FIELD-name case (`(deftype T [:Int a :Int a])`, also silently
// accepted at HEAD, same §8.5.2 invariant via §5.2.6 accessors).
//
// Prior art for the shape of the reject: `spec/05-definitions.md` §5.1 already
// requires parameter names to be unique within a parameter list, and HEAD
// enforces it — `(defn f [x x] x)` => `parse error: duplicate parameter name
// 'x'`. The constructor column has no such check.
//
// The three REDs below use spellings that the two S115 constructor-form rulings
// (parens-require-content; nullary-may-not-share-the-type-name — see
// `deftype_constructor_form_rulings_s116.rs`) leave LEGAL, so each cell pins
// duplication ALONE and cannot be flipped green by a sibling ruling landing.
//
// FAILING-NOT-IGNORED. Owner `/dev`; the record and trigger is this file.

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

/// The acceptance marker the REPL prints for an admitted `deftype`. Its ABSENCE
/// is the load-bearing assertion: a rejected `deftype` never reaches display.
const ACCEPTED: &str = "; deftype";

fn assert_rejected(c: &str, form: &str, ctor: &str) {
    assert!(
        !c.contains(ACCEPTED),
        "`{form}` declares the constructor `{ctor}` TWICE — the two arms contend \
         for one module-level binder and one canonical `Type.{ctor}` name, which \
         §8.5.2 requires to denote exactly one thing. It MUST be rejected, not \
         admitted (the `{ACCEPTED}` acceptance marker is present). got:\n{c}"
    );
    assert!(
        c.to_lowercase().contains("error"),
        "`{form}` MUST produce a compile-time diagnostic naming the duplicate \
         constructor `{ctor}`; today it is accepted in silence. got:\n{c}"
    );
}

// RED — duplicate NULLARY arms, in the docstring-nullary spelling (legal under
// both S115 constructor-form rulings: parens carry content, and neither ctor
// shares the type name). Both arms mint the binder `Raised`.
// spec: spec/05-definitions.md §5.2.2 — Sum Type (Multiple Constructors) — "each
// introduces a distinct variant" × spec/08-modules.md §8.5.2 — Dotted Names
// ("`Type.member` always denotes exactly one thing")
// defect: class=silent-accept locus=frontend deftype constructor-registration seam — no duplicate-name check across constructor arms (FIXME 0845 scribes the rule) found=S115 owner=/dev
#[test]
fn deftype_duplicate_nullary_constructor_rejected_neg() {
    let c = repl_prims("(deftype Flag (Raised \"up\") (Raised \"still up\"))\n");
    assert_rejected(&c, "(deftype Flag (Raised \"up\") (Raised \"still up\"))", "Raised");
}

// RED — duplicate arms in the ENUM spelling (§5.2.3, all-nullary bare names).
// Accepted at HEAD; the second `Red` becomes a dead match arm that produces no
// unreachable-arm error and a variant that cannot be constructed.
// spec: spec/05-definitions.md §5.2.3 — Enum (All Nullary) × §5.2.2 "each
// introduces a distinct variant"
// defect: class=silent-accept locus=frontend deftype constructor-registration seam — enum arm spelling, no duplicate-name check (FIXME 0845) found=S115 owner=/dev
#[test]
fn deftype_duplicate_enum_constructor_rejected_neg() {
    let c = repl_prims("(deftype Color Red Red Green)\n");
    assert_rejected(&c, "(deftype Color Red Red Green)", "Red");
}

// RED — duplicate FIELDED arms. The sharpest face: the two arms declare
// DIFFERENT field types, the later arm silently wins the binder, and the
// earlier variant is unconstructible — `(P 1)` reports a String/Int mismatch
// against a variant the program never named.
// spec: spec/05-definitions.md §5.2.2 — Sum Type (Multiple Constructors);
// data constructors are functions, one per distinct variant
// defect: class=silent-accept locus=frontend deftype constructor-registration seam — fielded arm spelling; later arm shadows the earlier variant's callable (FIXME 0845) found=S115 owner=/dev
#[test]
fn deftype_duplicate_fielded_constructor_rejected_neg() {
    let c = repl_prims("(deftype T (P [:primitives/Int a]) (P [:primitives/String b]))\n");
    assert_rejected(
        &c,
        "(deftype T (P [:primitives/Int a]) (P [:primitives/String b]))",
        "P",
    );
}

// GREEN control TWIN — the same two-arm shape with DISTINCT constructor names
// is the ordinary §5.2.2 sum type and MUST stay accepted. Fences the REDs
// above: what is rejected is the duplication, not the multi-arm form.
// spec: spec/05-definitions.md §5.2.2 — Sum Type (Multiple Constructors)
#[test]
fn deftype_distinct_fielded_constructors_control_green() {
    let c = repl_prims("(deftype T (P [:primitives/Int a]) (Q [:primitives/String b]))\n");
    assert!(
        c.contains(ACCEPTED),
        "distinct constructor names in one `deftype` are the ordinary §5.2.2 sum \
         type and MUST be accepted; got:\n{c}"
    );
    assert!(
        !c.to_lowercase().contains("error"),
        "distinct constructor names MUST NOT produce any diagnostic; got:\n{c}"
    );
}
