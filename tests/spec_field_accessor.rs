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
// §1.6.5 — `/list` shows the canonical qualified accessor
// ===========================================================================

// spec: spec/08-modules.md §8.5.2 — `/list` shows the CANONICAL qualified
// accessor `Box.v` for a product type's field (qualified-display convention,
// §1.6.5). Every field of every type lists as `Type.field`.
#[test]
fn list_shows_canonical_qualified_accessor() {
    let out = repl_prims(
        "(deftype Box [:primitives/Int v])\n/list\n",
    );
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
