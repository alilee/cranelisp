// spec_field_accessor.rs — INVERTED-MODEL field-accessor guards (Sprint 91,
// FIXME 0365).
//
// The 0365 field-accessor model was INVERTED this wave (user-ruled; design of
// record: `design/typecheck/fixme-0365-field-accessor-dotted.md §1.6`):
//
//   - `Type.field` (e.g. `Box.v`) is the CANONICAL, uniformly-Public accessor —
//     the one compiled function per (type, field).
//   - bare `field` (e.g. `v`) is a convenience exposure of that canonical
//     declaration — no second compiled function.
//   - when types share a field name, every canonical accessor remains a
//     candidate. Ordinary use-site constraints select one; only a fixed-point
//     survivor set larger than one is ambiguous. `Box.v`/`Cup.v` stay valid.
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
// candidate selection / ambiguity).

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

// spec: spec/08-modules.md §8.6.5 — a contested module-qualified convenience spelling
// remains a candidate set. The argument type selects `Box.v` and `Cup.v`
// independently; an `Int` argument matches neither and reports no matching
// declaration rather than silently choosing, reporting ambiguity, or claiming
// the spelling is undefined.
#[test]
fn cross_module_contested_bare_accessor_selects_by_type_and_no_match_neg() {
    fn run_main(expr: &str) -> helpers::e2e::CrOutput {
        Cranelisp::new()
            .with_prelude(PreludeVariant::PrimitivesOnly)
            .file(
                "lib/shapes.cl",
                "(deftype Box [:primitives/Int v])\n\
                 (deftype Cup [:primitives/Int v])\n",
            )
            .file(
                "main.cl",
                &format!(
                    "(import [primitives [Pure]])\n\
                     (import [shapes [Box Cup]])\n\
                     (defn main [] (Pure {expr}))"
                ),
            )
            .lib_dir("lib")
            .run("main")
            .output()
    }

    for (expr, expected) in [("(shapes/v (Box 5))", 5), ("(shapes/v (Cup 9))", 9)] {
        let out = run_main(expr);
        let diagnostic = format!("{}{}", out.stdout, out.stderr).to_lowercase();
        assert!(
            !diagnostic.contains("ambiguous") && !diagnostic.contains("no matching"),
            "argument-directed selection of `{expr}` MUST succeed without a candidate \
             diagnostic; stdout={} stderr={}",
            out.stdout,
            out.stderr
        );
        out.assert_exit(expected);
    }

    let no_match = run_main("(shapes/v 5)");
    let diagnostic = format!("{}{}", no_match.stdout, no_match.stderr).to_lowercase();
    assert!(
        !no_match.status.success(),
        "an `Int` argument matches neither contested accessor and MUST be rejected; \
         stdout={} stderr={}",
        no_match.stdout,
        no_match.stderr
    );
    assert!(
        diagnostic.contains("no matching")
            && !diagnostic.contains("ambiguous")
            && !diagnostic.contains("undefined variable"),
        "zero compatible `shapes/v` candidates MUST be a no-matching-declaration \
         error distinct from ambiguity and unknown spelling; stdout={} stderr={}",
        no_match.stdout,
        no_match.stderr
    );
}

// ===========================================================================
// §1.6.2 — bare exposure behaviour (type-selected or fixed-point ambiguous)
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

// spec: spec/03-types.md §3.5.3 and spec/08-modules.md §8.6.5 — ordinary
// argument constraints select a contested bare accessor independently at each
// use. An unconstrained first-class use remains ambiguous and lists the complete
// deduplicated canonical survivor set; dotted canonical uses always work.
#[test]
fn bare_alias_ambiguous_canonical_both_work() {
    let canonical = repl_prims(
        "(deftype Box [:primitives/Int v])\n\
         (deftype Cup [:primitives/Int v])\n\
         (Box.v (Box 5))\n\
         (Cup.v (Cup 9))\n",
    );
    canonical.assert_stdout_contains_all(&[":primitives/Int 5", ":primitives/Int 9"]);

    let box_call = repl_prims(
        "(deftype Box [:primitives/Int v])\n\
         (deftype Cup [:primitives/Int v])\n\
         (v (Box 5))\n",
    );
    let box_diagnostic = format!("{}{}", box_call.stdout, box_call.stderr).to_lowercase();
    assert!(
        !box_diagnostic.contains("ambiguous") && !box_diagnostic.contains("error"),
        "the `Box` argument MUST uniquely select `user/Box.v`; stdout={} stderr={}",
        box_call.stdout,
        box_call.stderr
    );
    box_call.assert_stdout_contains(":primitives/Int 5");

    let cup_call = repl_prims(
        "(deftype Box [:primitives/Int v])\n\
         (deftype Cup [:primitives/Int v])\n\
         (v (Cup 9))\n",
    );
    let cup_diagnostic = format!("{}{}", cup_call.stdout, cup_call.stderr).to_lowercase();
    assert!(
        !cup_diagnostic.contains("ambiguous") && !cup_diagnostic.contains("error"),
        "the `Cup` argument MUST uniquely select `user/Cup.v`; stdout={} stderr={}",
        cup_call.stdout,
        cup_call.stderr
    );
    cup_call.assert_stdout_contains(":primitives/Int 9");

    let amb = repl_prims(
        "(deftype Box [:primitives/Int v])\n\
         (deftype Cup [:primitives/Int v])\n\
         (defn discard [f] 0)\n\
         (discard v)\n",
    );
    let diagnostic = format!("{}{}", amb.stdout, amb.stderr);
    let lc = diagnostic.to_lowercase();
    assert!(
        lc.contains("ambiguous")
            && diagnostic.contains("user/Box.v")
            && diagnostic.contains("user/Cup.v")
            && !lc.contains("undefined variable")
            && !lc.contains("no matching"),
        "an unconstrained first-class `v` MUST be ambiguous and list both canonical \
         survivors exactly as candidates, not report unknown/no-match; stdout={} stderr={}",
        amb.stdout,
        amb.stderr
    );
    assert_eq!(
        diagnostic.matches("user/Box.v").count(),
        1,
        "the ambiguity diagnostic MUST deduplicate `user/Box.v`; {diagnostic}"
    );
    assert_eq!(
        diagnostic.matches("user/Cup.v").count(),
        1,
        "the ambiguity diagnostic MUST deduplicate `user/Cup.v`; {diagnostic}"
    );
}

// ===========================================================================
// §5.2.6 — product accessors versus sum payload labels (S121 ruling)
//
// A product has one same-name constructor, so each product field denotes a
// total projection and mints `Type.field` plus its bare convenience candidate.
// A differently named constructor arm is a sum variant even when it is the
// type's only arm. Its labels document positional payloads; they mint no names.
// Extraction from a sum is therefore exhaustive `match`, never a partial
// accessor with a runtime variant check.
// ===========================================================================

fn assert_undefined_accessor(form: &str, use_site: &str, name: &str) {
    let out = repl_prims(&format!("{form}\n{use_site}\n"));
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("undefined variable") && combined.contains(name),
        "sum payload label `{name}` MUST NOT mint an accessor; got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/05-definitions.md §5.2.2 and §5.2.6 — a differently named
// constructor is a sum variant; its payload labels mint no accessors.
#[test]
fn polymorphic_single_sum_arm_payload_labels_do_not_mint_accessors_neg() {
    let form = "(deftype (Duo a b) (MkDuo [:a fst :b snd]))";
    assert_undefined_accessor(form, "(Duo.fst (MkDuo 42 false))", "Duo.fst");
    assert_undefined_accessor(form, "(fst (MkDuo 42 false))", "fst");

    repl_prims(
        "(deftype (Duo a b) (MkDuo [:a fst :b snd]))\n\
         (match (MkDuo 42 false) [(MkDuo x _) x])\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/05-definitions.md §5.2.2 and §5.2.6 — the rule is determined
// by the product/sum shape, not by whether the type is polymorphic.
#[test]
fn monomorphic_single_sum_arm_payload_label_does_not_mint_accessor_neg() {
    let form = "(deftype Bxx (MkBxx [:primitives/Int v]))";
    assert_undefined_accessor(form, "(Bxx.v (MkBxx 5))", "Bxx.v");
    assert_undefined_accessor(form, "(v (MkBxx 5))", "v");

    repl_prims(
        "(deftype Bxx (MkBxx [:primitives/Int v]))\n\
         (match (MkBxx 5) [(MkBxx x) x])\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/05-definitions.md §5.2.2 and §5.2.6 — sum payload extraction
// is positional matching. `unwrap` is metadata, not a callable language name.
#[test]
fn sum_payload_label_extracts_by_match_and_mints_no_accessor_neg() {
    let form = "(deftype (Opt a) Nul (Jus [:a unwrap]))";
    assert_undefined_accessor(form, "(Opt.unwrap (Jus 42))", "Opt.unwrap");
    assert_undefined_accessor(form, "(unwrap (Jus 42))", "unwrap");

    repl_prims(
        "(deftype (Opt a) Nul (Jus [:a unwrap]))\n\
         (match (Jus 42) [(Jus x) x Nul 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// CONTROL (GREEN) — a POLYMORPHIC product spelled with the deftype-LEVEL field
// list mints BOTH accessors. This is the positive side of the product/sum
// boundary and proves that polymorphism does not suppress total projections.
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

// CONTROL (GREEN) — a constructor arm whose name EQUALS the type name is the
// product spelling and mints both accessors, concrete and polymorphic alike.
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
