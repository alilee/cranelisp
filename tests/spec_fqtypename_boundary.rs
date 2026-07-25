// spec_fqtypename_boundary.rs — FQTypeName cross-module boundary CEMENT tests.
//
// EXPECTED GREEN. These are NOT defect repros — they confirm EXISTING
// compliance. Per the /arch FQTypeName audit, the source is already correct
// (the (D)-difference count is 0): `Type::ADT` carries a fully-qualified
// `FQTypeName`, so two modules that define a `deftype` with the SAME short name
// resolve distinctly, and the self-documenting REPL displays the fully-qualified
// type in type position. These tests are the durable regression guard that
// would go RED if `Type::ADT` ever lost its `FQTypeName` and collapsed to a bare
// short `TypeName` (a real, dangerous collapse — it would alias two distinct
// types).
//
// If reasoning suggests one of these would FAIL on the current binary, that is
// an unexpected leak — flag it (do not silently relax the assertion).
//
// spec: spec/08-modules.md §8.5 — Qualified Names (a name resolves to exactly
// one definition, identified by `module_path '/' local_name`; two modules with
// the same short name are distinct).
// design basis: Decision 0047 — FQTypeName is binding as the cross-crate
// boundary type for resolved-stage type identifiers
// (design/arch/decisions/0047-fqtypename-binding-at-resolved-stage-boundaries.md).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// =============================================================================
// Cross-module same-short-name — distinct resolution (the FQTypeName guard)
// =============================================================================

// spec: spec/08-modules.md §8.5 — Qualified Names
// EXPECTED GREEN. Two modules `a` and `b` each define a type whose SHORT name is
// `Box` but with DIFFERENT field shapes (`a/Box` = one Int; `b/Box` = two Ints).
// A program imports both, constructs each, and pattern-matches each to read its
// fields. Both MUST resolve distinctly — `(ABox 7)` reads back 7, `(BBox 3 4)`
// reads back 3+4=7 — and the program exits with their combined witness (14).
// If `Type::ADT` collapsed to a bare short `TypeName`, `a/Box` and `b/Box` would
// alias and the two-field match against the one-field type (or vice-versa) would
// mis-resolve or crash.
#[test]
fn fqtypename_cross_module_same_short_name_resolve_distinctly() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        // Module a: `Box` with a single Int field, constructor `ABox`.
        .file(
            "a.cl",
            "(deftype Box (ABox [:primitives/Int n]))\n\
             (defn a-val [b] (match b [(ABox n) n]))\n",
        )
        // Module b: `Box` with TWO Int fields, constructor `BBox`. Same short
        // type name `Box`, different field shape.
        .file(
            "b.cl",
            "(import [primitives [add-i64]])\n\
             (deftype Box (BBox [:primitives/Int x :primitives/Int y]))\n\
             (defn b-val [b] (match b [(BBox x y) (add-i64 x y)]))\n",
        )
        // Entry: import both `Box` types + their constructors + accessors, FQ
        // where the short name would collide. Construct each, sum the witnesses.
        .file(
            "main.cl",
            "(import [primitives [add-i64 Pure]])\n\
             (import [a [Box ABox a-val]])\n\
             (import [b [BBox b-val]])\n\
             (defn main [] (Pure (add-i64 (a-val (ABox 7)) (b-val (BBox 3 4)))))\n",
        )
        .run("main.cl")
        .output();

    let combined = format!("{}\n{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("undefined")
            && !combined.contains("type error")
            && !combined.contains("collision"),
        "two modules defining a same-short-name type (`a/Box`, `b/Box`) MUST \
         resolve distinctly via FQTypeName (spec §8.5; Decision 0047); got:\n{combined}"
    );
    // 7 (from a/Box) + (3+4) (from b/Box) = 14.
    out.assert_exit(14);
}

// spec: spec/08-modules.md §8.5 — Qualified Names
// EXPECTED GREEN (negative companion). The same two same-short-name types, but
// the entry references `b`'s two-field constructor `BBox` while matching with a
// pattern shaped for `a`'s one-field `ABox`. Because the types are DISTINCT
// (FQTypeName), the compiler MUST reject the cross-type mismatch rather than
// silently aliasing `a/Box` and `b/Box` (which a bare-`TypeName` collapse would
// permit). The program MUST NOT compile-and-run to a clean Int.
#[test]
fn fqtypename_cross_module_same_short_name_neg_no_alias_collapse() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .file("a.cl", "(deftype Box (ABox [:primitives/Int n]))\n")
        .file(
            "b.cl",
            "(deftype Box (BBox [:primitives/Int x :primitives/Int y]))\n",
        )
        // Entry matches a `BBox` (b/Box, two fields) value against an `ABox`
        // (a/Box, one field) pattern. If `a/Box`/`b/Box` aliased, the typechecker
        // would wrongly accept this. With distinct FQTypeNames it MUST be rejected.
        .file(
            "main.cl",
            "(import [a [ABox]])\n\
             (import [b [BBox]])\n\
             (defn main [] (match (BBox 3 4) [(ABox n) n]))\n",
        )
        .run("main.cl")
        .output();

    assert!(
        !out.status.success(),
        "matching a `b/Box` value against an `a/Box` pattern MUST be rejected — \
         the two same-short-name types are distinct (FQTypeName; spec §8.5; \
         Decision 0047). A clean exit here would mean the types aliased.\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

// =============================================================================
// REPL introspection — fully-qualified type display (the FQ-display principle)
// =============================================================================

// spec: spec/08-modules.md §8.5 — Qualified Names
// EXPECTED GREEN. The self-documenting REPL displays an ADT's type in
// FULLY-QUALIFIED form. A `deftype Box` defined in the REPL's entry module (the
// default `user` module) introspects/value-displays as `:user/Box …`, not the
// bare short `Box` in type position. (Per the self-documenting-REPL FQ-display
// principle in root CLAUDE.md, Design Principles section.)
#[test]
fn fqtypename_repl_introspection_displays_fully_qualified() {
    // Define the type, then introspect it. The deftype echo itself tags the type
    // as `:user/Box ; deftype` (the universal `:Type name ; classification`
    // format), which is the fully-qualified type in type position.
    let out = Cranelisp::repl_capture(
        "(deftype Box (Boxed [:primitives/Int n]))\n\
         /info Box\n",
    );
    assert!(
        out.stdout.contains(":user/Box"),
        "REPL MUST display the ADT type fully-qualified as `:user/Box`; got stdout:\n{}",
        out.stdout
    );
}

// spec: spec/08-modules.md §8.5 — Qualified Names
// EXPECTED GREEN (negative). The FQ-display requirement implies the REPL MUST
// NOT show the BARE short name `:Box` in type position (the colon-prefixed type
// tag). A leak here would mean type display dropped the module qualifier — the
// observable face of an FQTypeName collapse.
#[test]
fn fqtypename_repl_introspection_neg_no_bare_short_name_in_type_position() {
    let out = Cranelisp::repl_capture(
        "(deftype Box (Boxed [:primitives/Int n]))\n\
         /info Box\n",
    );
    // The colon-prefixed type tag `:Box` (bare, no module) MUST NOT appear.
    // We scan for the literal `:Box` token NOT preceded by a module segment.
    // `:user/Box` is correct and contains `Box` but not the bare `:Box` tag.
    let leaks_bare = out
        .stdout
        .lines()
        .any(|l| l.contains(":Box") && !l.contains("/Box"));
    assert!(
        !leaks_bare,
        "REPL type display MUST NOT show the bare short name `:Box` in type \
         position (FQ-display principle; spec §8.5); got stdout:\n{}",
        out.stdout
    );
}
