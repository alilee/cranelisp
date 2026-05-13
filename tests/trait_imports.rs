// trait_imports.rs — Trait-method import / short-name resolution under
// Principle 17 (per-method `ModuleEntry::Import` injection).
//
// This file is the **stdlib-independent** regression guard for trait-method
// short-name resolution. Four shapes in `tests/stdlib_trait_impls.rs` fail
// today because trait-method short-name resolution is incomplete:
//
//   - `(show 42)` / `(show 3.14)`     — Display call-site, short name
//   - `(let [f =] (f a b))`           — Eq operator as a first-class value
//   - `(let [f not] (f true))`        — Primitive operator as a value
//
// `tests/stdlib_trait_impls.rs` couples these regressions to stdlib
// evolution. Per `CLAUDE.md` §"Design Principles" — Stdlib separation,
// trait-import discipline is a **language-level** concern that must be
// validated independently of `stdlib/`. This file uses
// `PreludeVariant::TestStandard` (the QA-owned fixture at
// `tests/fixtures/preludes/test-standard.cl`), which provides `Display` +
// `show` impls directly so the language behaviour can be exercised
// without dragging stdlib in.
//
// Failing-not-ignored per `memory/feedback_failing_not_ignored.md`. The
// failure shape exposes the per-method `ModuleEntry::Import` gap that
// Sprint 66 Wave 3a is in design to close. Once that work lands, these
// tests pass.
//
// Spec anchors:
//   §7.4 — Method Resolution (Static Dispatch) — bare `show` must
//          resolve to `Display.show$Int` at the call site.
//   §7.6 — Operators as First-Class Values — `(let [f =] (f a b))` and
//          analogous shapes for any trait method (or primitive).
//   §8.8.1 — Implicit Import (prelude glob) — the bridge that makes
//          trait method short names visible in user code.
//
// FQSymbol-shape agnosticism: every assertion below checks observable
// REPL output only (`:primitives/Int N`, `:primitives/Bool true`,
// `:primitives/String "..."`, or the literal `42` / `3.14`). No
// assertion encodes which of Option A/B/C `/arch` selects for the
// FQSymbol representation in the upcoming Wave 3a-α refactor.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// =============================================================================
// Helpers
// =============================================================================

fn repl_std(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin(lines)
        .output()
}

fn repl_no_prelude(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::None)
        .stdin(lines)
        .output()
}

// =============================================================================
// Display — call-site short-name resolution (§7.4 + §7.6)
// =============================================================================

// spec: spec/07-traits.md §7.4 — bare `show` MUST resolve to `Display.show$Int`
// at the call site when `Display` is in the implicit prelude scope (§8.8.1).
// Today fails: `undefined variable: show`.
#[test]
fn trait_method_short_name_resolves_via_prelude_import_for_call_site_int() {
    let out = repl_std("(show 42)\n");
    assert!(
        out.stdout.contains("\"42\"") || out.stdout.contains("42"),
        "(show 42) MUST resolve `show` to Display.show$Int via prelude import \
         and produce `\"42\"`; got stdout:\n{}",
        out.stdout
    );
}

// spec: spec/07-traits.md §7.4 — Display.show$Float dispatch shape.
// Today fails: `undefined variable: show`.
#[test]
fn trait_method_short_name_resolves_via_prelude_import_for_call_site_float() {
    let out = repl_std("(show 3.14)\n");
    assert!(
        out.stdout.contains("3.14"),
        "(show 3.14) MUST resolve `show` to Display.show$Float via prelude \
         import; got stdout:\n{}",
        out.stdout
    );
}

// spec: spec/07-traits.md §7.4 — Display.show$Bool dispatch shape; verifies
// short-name resolution works across the full impl set, not just numeric.
#[test]
fn trait_method_short_name_resolves_via_prelude_import_for_call_site_bool() {
    let out = repl_std("(show true)\n");
    assert!(
        out.stdout.contains("true"),
        "(show true) MUST resolve `show` to Display.show$Bool and produce \
         \"true\"; got stdout:\n{}",
        out.stdout
    );
}

// =============================================================================
// Eq / Display — operator-as-value (mappable-path) (§7.6)
// =============================================================================

// spec: spec/07-traits.md §7.6 — when bound to a variable, a trait method
// is wrapped in a closure that dispatches per the value's type at call
// time. Today fails: `undefined variable: =`.
#[test]
fn trait_method_short_name_resolves_as_value_for_eq_string() {
    let out = repl_std("(let [f =] (f \"hi\" \"hi\"))\n");
    assert!(
        out.stdout.contains(":primitives/Bool true"),
        "(let [f =] (f \"hi\" \"hi\")) MUST resolve `=` as a first-class \
         value of Eq.=$String per §7.6; got stdout:\n{}",
        out.stdout
    );
}

// spec: spec/07-traits.md §7.6 — same shape, Int impl. Adds coverage that
// per-method Import injection isn't restricted to one impl row.
#[test]
fn trait_method_short_name_resolves_as_value_for_eq_int() {
    let out = repl_std("(let [f =] (f 1 1))\n");
    assert!(
        out.stdout.contains(":primitives/Bool true"),
        "(let [f =] (f 1 1)) MUST resolve `=` as a first-class value of \
         Eq.=$Int per §7.6; got stdout:\n{}",
        out.stdout
    );
}

// spec: spec/07-traits.md §7.6 — Display.show as a first-class value.
// Same discipline as the Eq cases: bare `show` must resolve when stored
// in a local binding, not only at the direct call site.
#[test]
fn trait_method_short_name_resolves_as_value_for_display_show_int() {
    let out = repl_std("(let [f show] (f 42))\n");
    assert!(
        out.stdout.contains("\"42\"") || out.stdout.contains("42"),
        "(let [f show] (f 42)) MUST resolve `show` as a first-class value \
         of Display.show$Int per §7.6; got stdout:\n{}",
        out.stdout
    );
}

// =============================================================================
// Primitive `not` — mappable-path (§7.6 analogue / primitive-as-value)
// =============================================================================
//
// `not` is a primitive (per `spec/appendix-a-builtins.md` §"Boolean"), not
// a trait method. The standard resolution path treats it as a regular
// function. The mappable-path discipline (§7.6 generalised to ordinary
// function values) requires it to be usable as a first-class value once
// brought into scope by the prelude's `(import [primitives [*]])`.
//
// Today fails: `undefined variable: not`. The fix is **upstream** — seed
// `not` with a symbol-table entry / GOT slot like any other primitive,
// not via a backend special-case. The test exercises the standard
// resolution path; the test fixture must NOT replicate the backend's
// inline-special-casing of `not`.

// spec: spec/appendix-a-builtins.md §A.3
// spec: spec/07-traits.md §7.6 — primitive function (`not`, listed under
// "Boolean" in §A.3 Inline Primitives) MUST be available as a
// first-class value when brought into scope via the prelude's
// `(import [primitives [*]])`.
#[test]
fn primitive_not_resolves_as_value_via_prelude_import() {
    let out = repl_std("(let [f not] (f true))\n");
    assert!(
        out.stdout.contains(":primitives/Bool false"),
        "(let [f not] (f true)) MUST resolve `not` as a first-class value \
         (no backend special-case); got stdout:\n{}",
        out.stdout
    );
}

// spec: spec/appendix-a-builtins.md §A.3 — sister positive: inline
// path. Sanity check that the prelude-import side is intact even when the
// mappable path is broken (isolates the failure shape).
#[test]
fn primitive_not_resolves_at_call_site_via_prelude_import() {
    let out = repl_std("(not true)\n");
    assert!(
        out.stdout.contains(":primitives/Bool false"),
        "(not true) MUST resolve `not` at the call site via prelude import; \
         got stdout:\n{}",
        out.stdout
    );
}

// =============================================================================
// Negative: trait-method short names MUST NOT resolve without a prelude
// =============================================================================
//
// Sanity-check the discipline: when no prelude is loaded
// (`PreludeVariant::None`), `show` / `=` / `not` are NOT in scope and
// must surface a resolution error. If these accidentally pass green
// without a prelude, the import discipline is leaking.

// spec: spec/08-modules.md §8.8.1 — with no prelude in scope, bare trait
// method names MUST NOT resolve. (Negative complement of the positive
// `trait_method_short_name_resolves_via_prelude_import_for_call_site_*`.)
#[test]
fn trait_method_short_name_not_resolved_without_prelude_neg() {
    let out = repl_no_prelude("(show 42)\n");
    let combined = format!("{}\n{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        combined.contains("undefined")
            || combined.contains("unresolved")
            || combined.contains("error"),
        "without a prelude, bare `show` MUST surface a resolution error \
         (no implicit Display import); got stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    // Negative shape: must NOT successfully print "42" / "\"42\"" as if
    // it had resolved. (Leakage check.)
    assert!(
        !out.stdout.contains(":primitives/String"),
        "without a prelude, `(show 42)` MUST NOT succeed and produce a \
         String value; got stdout:\n{}",
        out.stdout
    );
}

// spec: spec/08-modules.md §8.8.1 — same discipline for `=`. Today this
// already fails without a prelude (the existing implementation does not
// silently seed Eq.= short-name), but the assertion is the durable guard
// against a future regression where per-method imports go too far and
// leak into the no-prelude case.
#[test]
fn eq_operator_short_name_not_resolved_without_prelude_neg() {
    let out = repl_no_prelude("(let [f =] (f 1 1))\n");
    let combined = format!("{}\n{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        combined.contains("undefined")
            || combined.contains("unresolved")
            || combined.contains("error"),
        "without a prelude, bare `=` MUST surface a resolution error; \
         got stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    assert!(
        !out.stdout.contains(":primitives/Bool true"),
        "without a prelude, `(let [f =] (f 1 1))` MUST NOT silently \
         succeed; got stdout:\n{}",
        out.stdout
    );
}
