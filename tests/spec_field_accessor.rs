// spec_field_accessor.rs — INVERTED-MODEL field-accessor guards (Sprint 91,
// FIXME 0365).
//
// The 0365 field-accessor model was INVERTED this wave (user-ruled; design of
// record: `design/typecheck/fixme-0365-field-accessor-dotted.md §1.6`):
//
//   - `Type.field` (e.g. `Box.v`) is the CANONICAL, uniformly-Public accessor —
//     the one compiled function per (type, field).
//   - bare `field` (e.g. `v`) is a CONVENIENCE ALIAS (a `ModuleEntry::Import`
//     edge to the canonical key) — no second compiled function.
//   - AMBIGUITY lives in the bare alias: when two same-module types share a field
//     name, the bare key becomes `Ambiguous`; the canonical `Box.v`/`Cup.v` stay
//     valid (§1.6.2).
//
// The load-bearing payoff (§1.6.3 / §1.6.6) is CROSS-MODULE NO-CLIFF: because the
// canonical `Type.field` `Def` is unconditionally Public, `m/Box.v` resolves
// cross-module in EVERY case — INCLUDING a contested field — which would have
// FAILED under the retired design (where a contested field's accessor went
// non-Public). These guards pin the inverted behaviour; the `/dev` impl landed
// green this wave, so they are GREEN guards (regression floors), not RED-first.
//
// Free-standing: PrimitivesOnly prelude; lib-dir module trees built inline.
// Spec: spec/05-definitions.md §5.2.6 (Generated Accessors, reframed),
// spec/08-modules.md §8.5.2 (Dotted Names, reframed), §8.6.5 (bare-name
// ambiguity / poisoning).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output()
}

// ===========================================================================
// §1.6.6 — cross-module reachability: the no-cliff regression guard
// ===========================================================================

// spec: spec/08-modules.md §8.5.2 — cross-module canonical accessor: a module `m`
// (`shapes`) defining `(deftype Box [:Int v])` is imported by `main`; the
// qualified canonical accessor `shapes/Box.v` resolves AND types cross-module
// (the canonical `Def` is uniformly Public per the inverted model). `(shapes/Box.v
// (Box 7))` = 7.
#[test]
fn cross_module_canonical_accessor_resolves() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("lib/shapes.cl", "(deftype Box [:primitives/Int v])\n")
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [shapes [Box]])\n\
             (defn main [] (Pure (shapes/Box.v (Box 7))))",
        )
        .lib_dir("lib")
        .run("main")
        .output()
        .assert_exit(7);
}

// spec: spec/08-modules.md §8.5.2 — THE CONTESTED NO-CLIFF GUARD (the inversion's
// payoff, §1.6.6 load-bearing). A module `m` (`shapes`) defines BOTH `Box` and
// `Cup` with a field `v` (so bare `v` is contested in `m`). `m/Box.v` AND `m/Cup.v`
// STILL resolve cross-module — `(add-i64 (shapes/Box.v (Box 5)) (shapes/Cup.v (Cup
// 9)))` = 14. Under the RETIRED design a contested field's accessor went
// non-Public and this would have FAILED cross-module; the canonical-always-Public
// inversion removes the cliff. This is the regression guard that proves the
// inversion.
#[test]
fn cross_module_contested_canonical_accessors_no_cliff() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "lib/shapes.cl",
            "(deftype Box [:primitives/Int v])\n\
             (deftype Cup [:primitives/Int v])\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure add-i64]])\n\
             (import [shapes [Box Cup]])\n\
             (defn main [] (Pure (add-i64 (shapes/Box.v (Box 5)) \
                                          (shapes/Cup.v (Cup 9)))))",
        )
        .lib_dir("lib")
        .run("main")
        .output()
        // No cliff: BOTH contested canonical accessors resolve cross-module → 14.
        .assert_exit(14);
}

// spec: spec/08-modules.md §8.6.5 — NEG (cross-module, contested): the BARE
// cross-module name `m/v` MUST NOT silently dispatch in the contested case — it is
// rejected (the bare alias is `Ambiguous` in `m`), while the canonical
// `m/Box.v`/`m/Cup.v` always work (asserted above). The behavioural contrast: the
// contested bare `shapes/v` program does NOT successfully compute the field value
// (it errors / does not exit cleanly with the accessor's result).
//
// NOTE: the diagnostic wording on the contested bare cross-module path is
// currently the module-resolution error rather than a clean "ambiguous bare name"
// message (a diagnostic-quality gap on the qualified-bare-name path, distinct from
// the accessor inversion); this guard pins the BEHAVIOURAL outcome (rejected, not
// silently dispatched), not the exact message.
#[test]
fn cross_module_contested_bare_accessor_rejected_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file(
            "lib/shapes.cl",
            "(deftype Box [:primitives/Int v])\n\
             (deftype Cup [:primitives/Int v])\n",
        )
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [shapes [Box Cup]])\n\
             (defn main [] (Pure (shapes/v (Box 5))))",
        )
        .lib_dir("lib")
        .run("main")
        .output();
    // The contested bare cross-module accessor MUST NOT succeed as the field
    // accessor — it must NOT exit 5 (the value `Box.v` would yield). It is
    // rejected (the bare alias is ambiguous in `m`).
    assert_ne!(
        out.status.code(),
        Some(5),
        "a contested bare cross-module accessor `shapes/v` MUST NOT silently \
         dispatch to a field accessor (it is ambiguous in the source module, \
         §8.6.5); the canonical `shapes/Box.v` is the unambiguous form. \
         stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// ===========================================================================
// §1.6.2 — bare alias behaviour (resolves when unique; ambiguous when contested)
// ===========================================================================

// spec: spec/05-definitions.md §5.2.6 — bare alias resolves when EXACTLY ONE type
// owns the field. With a single `(deftype Box [:Int v])`, the bare `v` alias
// resolves to the canonical accessor and types `(Fn [Box] Int)`; `(v (Box 5))` =
// 5. (Same-module; the alias edge follows to the canonical `Box.v` Def.)
#[test]
fn bare_alias_resolves_when_field_unique() {
    repl_prims(
        "(deftype Box [:primitives/Int v])\n\
         (v (Box 5))\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/08-modules.md §8.6.5 — bare alias is AMBIGUOUS when two same-module
// types share the field, BUT the canonical `Box.v`/`Cup.v` both still work. The
// ambiguity lives in the bare alias (§1.6.2), not in the canonical accessors.
#[test]
fn bare_alias_ambiguous_canonical_both_work() {
    let out = repl_prims(
        "(deftype Box [:primitives/Int v])\n\
         (deftype Cup [:primitives/Int v])\n\
         (Box.v (Box 5))\n\
         (Cup.v (Cup 9))\n\
         (v (Box 5))\n",
    );
    // The canonical accessors both resolve cleanly (the inversion keeps them valid).
    out.assert_stdout_contains_all(&[":primitives/Int 5", ":primitives/Int 9"]);
    // The bare alias `v` is ambiguous — a diagnostic naming the canonical
    // alternatives. (Re-fetch via a second session for the negative arm so the
    // consuming assertion above does not move `out`.)
    let amb = repl_prims(
        "(deftype Box [:primitives/Int v])\n\
         (deftype Cup [:primitives/Int v])\n\
         (v (Box 5))\n",
    );
    let lc = format!("{}{}", amb.stdout, amb.stderr).to_lowercase();
    assert!(
        lc.contains("ambiguous") || (lc.contains("error") && lc.contains("box.v")),
        "a contested bare alias `v` MUST be an ambiguity error naming the canonical \
         alternatives `Box.v`/`Cup.v` (§8.6.5 / §1.6.2); stdout={} stderr={}",
        amb.stdout,
        amb.stderr
    );
}

// ===========================================================================
// §5.2.6 — THE CONSTRUCTOR-ARM AXIS (FIXME 0867, S118 W1 repro)
//
// FIXME 0867 (`/repl`, S117 Phase 6b) found that
// `(deftype (Pair a b) (MkPair [:a fst :b snd]))` mints NEITHER the canonical
// `Pair.fst` nor the unique bare `fst`, and attributed the gap to the
// TYPE-PARAMETER axis: "a concrete product mints both, a polymorphic product
// mints neither".
//
// REDUCED AT HEAD `e15ff20f` (`/testing`, S118 W1). The type parameter is NOT
// causal. The axis is WHERE THE FIELD LIST LIVES:
//
//   deftype form                                        `T.f`   bare `f`
//   (deftype Box [:Int v])                     product    yes      yes
//   (deftype (Bx a) [:a val])            poly product     yes      yes   ← poly, GREEN
//   (deftype Bz (Bz [:Int v]))          same-name arm     yes      yes
//   (deftype (Pz a) (Pz [:a v]))   poly same-name arm     yes      yes   ← poly, GREEN
//   (deftype Bxx (MkBxx [:Int v]))     distinct-name arm   NO       NO   ← concrete, RED
//   (deftype (Duo a b) (MkDuo [:a fst :b snd]))          NO       NO   ← 0867's case
//   (deftype Sh Circ (Sq [:Int side]))         sum         NO       NO
//   (deftype (Opt a) Nul (Jus [:a unwrap]))  poly sum      NO       NO
//
// Two polymorphic forms mint BOTH accessors, and a CONCRETE distinct-name
// constructor arm mints NEITHER. So the defect is: **field accessors are
// synthesised only from the deftype-LEVEL field list (and the same-name
// single-constructor spelling that reduces to it); a field list living in a
// named constructor arm whose name differs from the type's contributes no
// accessor at all.** That is every sum type and every product spelled with a
// distinct constructor — far wider than 0867's polymorphic-product framing, and
// it makes spec §5.2.6's OWN sum-type example (`Option.unwrap` /
// bare `unwrap` over `(deftype (Option a) None (Some [:a unwrap]))`)
// non-conforming.
//
// WHY THE WHOLE AXIS WAS INVISIBLE (tests/CLAUDE.md §"Coverage by definition
// variants"): every pre-existing accessor guard — the four cells below, plus
// `spec_05_definitions::{generated_field_accessor_resolves_as_free_callable,
// accessor_is_first_class_value_passable, accessor_cross_type_duplicate_field_name}`
// — spells its type `(deftype Box [:primitives/Int v])`. One variant of the
// definition form was exercised; the missing cell is exactly where the sibling
// variant diverged. The matrix below is the variant × polarity grid that lens
// asks for, with the GREEN rows kept so the divergence NAMES its site instead of
// just failing.
//
// The duplicate-field ambiguity family above is retained unchanged as the
// negative boundary: a fix must mint the bare alias for these forms WITHOUT
// weakening the contested-name rejection (§8.6.5).
//
// `/qa` finalizes the narrow `/dev` attribution from these REDs (FIXME 0867
// §"Proposed resolution"); the `class=` below is `/testing`'s reading of the
// controlled vocabulary and is `/qa`'s to re-label.
// ===========================================================================

// 0867's own case, verbatim modulo the type name (`Pair` is a primitives-seeded
// name, so a `deftype Pair` under any prelude that provides it is a §8.6.4
// definition-over-import conflict, not an accessor question — the rename keeps
// the cell about accessors).
// spec: spec/05-definitions.md §5.2.6 — Generated Accessors: "For each named
// field in a type definition, an accessor function is automatically generated",
// canonical `Type.field` plus the unique bare alias. Nothing in §5.2.6 excludes
// a type parameter or a named constructor arm.
// defect: class=enumeration-miss locus=field-accessor synthesis walks the deftype-LEVEL field list only and omits named-constructor-arm field lists — no canonical `Type.field` Def and no bare-alias Import edge minted found=S117 owner=/dev
#[test]
fn polymorphic_product_mints_canonical_and_unique_bare_accessors() {
    let out = repl_prims(
        "(deftype (Duo a b) (MkDuo [:a fst :b snd]))\n\
         (Duo.fst (MkDuo 42 false))\n\
         (fst (MkDuo 42 false))\n",
    );
    let both = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !both.contains("undefined variable: Duo.fst"),
        "the CANONICAL accessor `Duo.fst` MUST be minted for a field declared in \
         a named constructor arm (§5.2.6); it is undefined. stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    assert!(
        !both.contains("undefined variable: fst"),
        "the unique bare alias `fst` MUST resolve — no second `fst` field exists, \
         so this is not the §8.6.5 ambiguity case (§5.2.6); it is undefined. \
         stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    out.assert_stdout_contains_all(&[":primitives/Int 42"]);
}

// THE DISCRIMINATING RED — the same shape with NO type parameter. This is the
// cell that removes polymorphism from the causal chain: `Bxx` is concrete, a
// single-constructor product, one field, no contest — and it mints neither
// accessor. Pair it with `control_polymorphic_deftype_level_product_*` below
// (polymorphic, GREEN) and the axis is pinned to the constructor arm.
// spec: spec/05-definitions.md §5.2.6 — Generated Accessors; a product's
// accessors are total and are generated for each named field.
// defect: class=enumeration-miss locus=field-accessor synthesis walks the deftype-LEVEL field list only and omits named-constructor-arm field lists — concrete face, no type parameter involved found=S117 owner=/dev
#[test]
fn concrete_constructor_arm_product_mints_canonical_and_unique_bare_accessors() {
    let out = repl_prims(
        "(deftype Bxx (MkBxx [:primitives/Int v]))\n\
         (Bxx.v (MkBxx 5))\n\
         (v (MkBxx 5))\n",
    );
    let both = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !both.contains("undefined variable: Bxx.v") && !both.contains("undefined variable: v"),
        "a CONCRETE single-constructor product whose constructor name differs \
         from its type name MUST still mint `Bxx.v` and the unique bare `v` \
         (§5.2.6) — the type parameter is not the variable. stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    out.assert_stdout_contains(":primitives/Int 5");
}

// THE SPEC'S OWN EXAMPLE — §5.2.6 "Sum type accessors are partial" shows
// `(deftype (Option a) None (Some [:a unwrap]))` with `(Option.unwrap (Some 42))`
// and `(unwrap (Some 42))` both yielding 42. Renamed to `Opt`/`Jus` only because
// `Option`/`Some` are primitives-seeded (§8.6.4). Neither accessor exists.
//
// This is the widest statement of the defect and the reason it outranks 0867's
// framing: the partial sum-type accessor is a documented, exampled §5.2.6
// feature with no implementation for any type, of any arity, at any polymorphism.
// spec: spec/05-definitions.md §5.2.6 — Generated Accessors: "Sum type
// accessors are partial — they succeed on the matching variant and panic on
// mismatched variants", with `Option.unwrap` / bare `unwrap` as the example.
// defect: class=enumeration-miss locus=field-accessor synthesis walks the deftype-LEVEL field list only and omits named-constructor-arm field lists — sum-type face, the spec's own §5.2.6 example found=S117 owner=/dev
#[test]
fn sum_type_variant_field_mints_canonical_and_unique_bare_accessors() {
    let out = repl_prims(
        "(deftype (Opt a) Nul (Jus [:a unwrap]))\n\
         (Opt.unwrap (Jus 42))\n\
         (unwrap (Jus 42))\n",
    );
    let both = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !both.contains("undefined variable: Opt.unwrap")
            && !both.contains("undefined variable: unwrap"),
        "§5.2.6's own sum-type example MUST work: `Opt.unwrap` and the unique \
         bare `unwrap` over `(deftype (Opt a) Nul (Jus [:a unwrap]))`. Both are \
         undefined. stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    out.assert_stdout_contains(":primitives/Int 42");
}

// CONTROL (GREEN) — a POLYMORPHIC product spelled with the deftype-LEVEL field
// list mints BOTH accessors. This is the cell that falsifies 0867's stated
// attribution: the type parameter is present and everything works. Read against
// `polymorphic_product_mints_canonical_and_unique_bare_accessors` above, the
// only difference is where the field list is written.
// spec: spec/05-definitions.md §5.2.6 — Generated Accessors; a type parameter
// does not change accessor generation.
#[test]
fn control_polymorphic_deftype_level_product_mints_both_accessors_green() {
    repl_prims(
        "(deftype (Bx a) [:a val])\n\
         (Bx.val (Bx 7))\n\
         (val (Bx 7))\n",
    )
    .assert_stdout_contains(":primitives/Int 7");
}

// CONTROL (GREEN) — a constructor arm whose name EQUALS the type name mints both
// accessors, concrete and polymorphic alike. `(deftype Bz (Bz [:Int v]))` is
// §5.2.1's "product constructor sharing the type name is the normal case", and
// it reduces to the deftype-level form. Its GREEN is what narrows the defect
// from "constructor arms" to "constructor arms whose name differs from the
// type's" — the sharpest available statement of the surviving synthesis path.
// spec: spec/05-definitions.md §5.2.6 — Generated Accessors; §5.2.7, a product
// constructor sharing the type name is the normal case.
#[test]
fn control_same_name_constructor_arm_mints_both_accessors_green() {
    repl_prims(
        "(deftype Bz (Bz [:primitives/Int v]))\n\
         (Bz.v (Bz 5))\n\
         (v (Bz 5))\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
    repl_prims(
        "(deftype (Pz a) (Pz [:a v]))\n\
         (Pz.v (Pz 6))\n\
         (v (Pz 6))\n",
    )
    .assert_stdout_contains(":primitives/Int 6");
}

// ===========================================================================
// §1.6.5 — `/list` shows the canonical qualified accessor
// ===========================================================================

// spec: spec/08-modules.md §8.5.2 — `/list` shows the CANONICAL qualified
// accessor `Box.v` for a product type's field (qualified-display convention,
// §1.6.5). Every field of every type lists as `Type.field`.
#[test]
fn list_shows_canonical_qualified_accessor() {
    let out = repl_prims("(deftype Box [:primitives/Int v])\n/list\n");
    out.assert_stdout_contains("Box.v");

    // FIXME(0438): whether the BARE `v` alias ALSO appears in `/list` (option A
    // "show canonical only" vs option B "annotate alias") is an open `/repl` call
    // (design §1.6.5 recommends A but defers the surface wording to /repl via
    // FIXME 0438). DO NOT assert bare `v` is present/absent here until 0438 is
    // resolved — the assertion line goes here once /repl rules:
    //   out.assert_stdout_does_not_contain(<bare-v-as-separate-symbol>);  // option A
    // or the option-B annotation form.
}

// ===========================================================================
// §1.6.6 — one compiled function per (type, field): behaviour-equivalent dispatch
// ===========================================================================

// spec: spec/05-definitions.md §5.2.6 — the bare alias adds NO second compiled
// function: bare `v` and canonical `Box.v` dispatch to the SAME accessor (the
// alias is an `Import` edge to the canonical `Def`). Behaviour-equivalence floor
// at the e2e level — both forms yield the identical value for the same input
// (the /dev unit-tier owns the no-duplicate-GOT-slot assertion; this is the
// observable consequence).
#[test]
fn bare_alias_and_canonical_dispatch_equivalently() {
    repl_prims(
        "(deftype Box [:primitives/Int v])\n\
         (v (Box 42))\n\
         (Box.v (Box 42))\n",
    )
    // Both the bare alias and the canonical accessor produce 42 — same function,
    // one compiled per (type, field).
    .assert_stdout_contains(":primitives/Int 42");
}
