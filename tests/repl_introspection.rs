// repl_introspection.rs — REPL slash-command + introspection surface (Sprint 64 Wave 3 Batch 7 sub-batch 1).
//
// Carries forward the slash-command + introspection assertions from the
// integration-tier `repl_experience.rs`, `repl_negative.rs`, `ring3_repl.rs`,
// `v4_repl_eval.rs`. Per `tests/plan/PLAN.md §"Mode canonicalisation"`,
// canonical mode is REPL (this file IS the REPL surface — slash commands).
//
// What this file covers (per `repl/spec.md §3` introspection + §4 universal
// display + §11 macro introspection):
//   - Universal `:Type value ; classification` display format for defn /
//     deftype / deftrait / defmacro
//   - /list — categorisation by source (special forms, macros, types, fns)
//   - /imports — special forms always present; user-imports listed
//   - /info, /sig, /doc, /type — symbol introspection
//   - /help — command catalogue
//   - /expand — macro expansion at the REPL
//   - Bare-name lookup — symbols resolve to their defining special form's display
//
// Coverage discipline: each test pipes one or two REPL forms followed by the
// slash command and asserts the substring(s) in stdout. Tests use bare
// `Cranelisp::new().repl()` (no prelude) when only primitives are needed;
// `with_prelude(PreludeVariant::PrimitivesOnly)` when bare-name primitives
// (`add-i64`, etc.) are wanted from the auto-prelude rather than an explicit
// `(import [primitives [*]])` form.
//
// Many integration-tier tests in the legacy sources tested the same
// assertion through the Rust API (e.g., `format_result(3, &Type::Int)`
// directly). Those internal-format tests are quarantined; the e2e form here
// asserts the same shape via stdout substring against the running binary.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// Test-authoring shortcuts: `Cranelisp::repl_capture(lines)` for bare REPL,
// `Cranelisp::repl_prims_capture(lines)` for REPL with PrimitivesOnly prelude.
// Both collapse `Cranelisp::new().repl()[.with_prelude(...)].stdin(lines).output()`
// into one call. The local one-liners below keep call-sites short.
fn repl(lines: &str) -> helpers::e2e::CrOutput { Cranelisp::repl_capture(lines) }
fn repl_prims(lines: &str) -> helpers::e2e::CrOutput { Cranelisp::repl_prims_capture(lines) }

// =============================================================================
// Universal display format — repl/spec.md §1.2 / §4.1
// =============================================================================

// spec: repl/spec.md §1.2 — Int display format `:primitives/Int N`
#[test]
fn display_int_result() {
    repl_prims("(add-i64 1 2)\n").assert_stdout_contains(":primitives/Int 3");
}

// spec: repl/spec.md §1.2 — Bool true display format
#[test]
fn display_bool_true() {
    repl_prims("(eq-i64 1 1)\n").assert_stdout_contains(":primitives/Bool true");
}

// spec: repl/spec.md §1.2 — Bool false display format
#[test]
fn display_bool_false() {
    repl_prims("(eq-i64 1 2)\n").assert_stdout_contains(":primitives/Bool false");
}

// spec: repl/spec.md §1.2 — Float display format
#[test]
fn display_float_result() {
    repl_prims("(add-f64 1.0 2.14)\n").assert_stdout_contains(":primitives/Float 3.14");
}

// spec: repl/spec.md §1.2 — negative Int displays
#[test]
fn display_negative_int() {
    repl_prims("(sub-i64 0 5)\n").assert_stdout_contains(":primitives/Int -5");
}

// spec: repl/spec.md §1.2 — zero Int displays
#[test]
fn display_zero_int() {
    repl_prims("(sub-i64 1 1)\n").assert_stdout_contains(":primitives/Int 0");
}

// spec: repl/spec.md §1.2 — large Int displays without overflow truncation
#[test]
fn display_large_int() {
    repl_prims("(mul-i64 1000000 1000000)\n")
        .assert_stdout_contains(":primitives/Int 1000000000000");
}

// spec: repl/spec.md §1.2 — colon prefix is mandatory in the display format
#[test]
fn display_format_has_colon_prefix() {
    let out = repl_prims("(add-i64 1 2)\n");
    assert!(
        out.stdout.contains(":primitives/Int"),
        "display must use ':Type' colon-prefix form; got stdout:\n{}",
        out.stdout
    );
}

// =============================================================================
// String literal display — repl/spec.md §1.2
// =============================================================================

// spec: repl/spec.md §1.2 — String literal display
#[test]
fn display_string_literal() {
    repl(r#""hello"
"#)
    .assert_stdout_contains(":primitives/String");
    // The quotes around the value are tolerated; we only require the type tag.
}

// =============================================================================
// defn display — repl/spec.md §1.3 / §4.1
// =============================================================================

// spec: repl/spec.md §1.3 — defn produces `:(Fn [...] Ret) module/name ; defn`
#[test]
fn defn_display_zero_arg_thunk() {
    repl_prims("(defn answer [] 42)\n")
        .assert_stdout_contains(":(Fn [] primitives/Int) user/answer ; defn");
}

// spec: repl/spec.md §1.3 — defn with one Int param
#[test]
fn defn_display_one_param() {
    repl_prims("(defn inc [x] (add-i64 x 1))\n")
        .assert_stdout_contains(":(Fn [primitives/Int] primitives/Int) user/inc ; defn");
}

// spec: repl/spec.md §1.3 — polymorphic defn shows type variables
#[test]
fn defn_display_polymorphic_id() {
    // The type-var rendering is `(Fn [a] a)` — exact name not load-bearing,
    // but it MUST NOT contain `t0`/`t1`/internal vars.
    repl("(defn id [x] x)\n")
        .assert_stdout_contains("user/id ; defn")
        .assert_stdout_does_not_contain("t0")
        .assert_stdout_does_not_contain("t1");
}

// spec: repl/spec.md §1.1 — a host-promised extern builtin (`DefKind::PrimitiveExtern`)
// in the `primitives` module classifies as `; primitive`, NOT `; defn`. The S96
// concurrency builtins `race`/`select`/`sleep` are `PrimitiveExtern`s; before the
// FIXME-0481 fix the classifier matched only `DefKind::Primitive`, so they (and
// `bind`) mis-rendered as `; defn`. A got-slotted `Primitive` (`add-i64`) was
// always correct; this pins the extern arm.
#[test]
fn extern_primitive_classifies_as_primitive_not_defn() {
    let out = repl_prims("(import [primitives [race]])\nrace\n");
    out.assert_stdout_contains("primitives/race ; primitive")
        .assert_stdout_does_not_contain("primitives/race ; defn");
}

// spec: repl/spec.md §1.3 — defn classification is `; defn`, not `closure`
#[test]
fn defn_display_neg_not_closure() {
    let out = repl_prims("(defn foo [] 42)\n");
    assert!(
        !out.stdout.contains("closure"),
        "top-level defn must NOT display as closure; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// deftype display — repl/spec.md §1.3 / §4.1
// =============================================================================

// spec: repl/spec.md §1.3 — deftype enum produces `:user/Name ; deftype`
#[test]
fn deftype_display_enum() {
    repl("(deftype Color Red Green Blue)\n")
        .assert_stdout_contains(":user/Color ; deftype");
}

// spec: repl/spec.md §1.3 — deftype enum lists constructors in match line
#[test]
fn deftype_display_lists_constructors() {
    repl("(deftype Color Red Green Blue)\n")
        .assert_stdout_contains_all(&["Red", "Green", "Blue"]);
}

// spec: repl/spec.md §1.3 — constructor display tags type and name
#[test]
fn constructor_display() {
    repl("(deftype Color Red Green Blue)
Red
")
    .assert_stdout_contains(":user/Color");
}

// =============================================================================
// /list — repl/spec.md §3.3
// =============================================================================

// spec: repl/spec.md §3.3 — empty session has no user definitions
#[test]
fn list_empty_session() {
    repl("/list\n").assert_stdout_contains("(no definitions)");
}

// spec: repl/spec.md §3.3 — defn appears under Fns category
#[test]
fn list_shows_fn_after_defn() {
    repl_prims("(defn foo [] 42)
/list
")
    .assert_stdout_contains_all(&["Fns:", "foo"]);
}

// spec: repl/spec.md §3.3 (negative) — /list does NOT show primitives in user module
#[test]
fn list_neg_no_primitives_in_user() {
    let out = repl_prims("/list\n");
    // Empty user module — no primitives should appear.
    assert!(
        !out.stdout.contains("add-i64"),
        "/list MUST NOT show primitives like add-i64 in user module; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.3 — /list groups types under Types category
#[test]
fn list_shows_types_category() {
    let out = repl("(deftype Color Red Green Blue)
/list
");
    assert!(
        out.stdout.contains("Color"),
        "/list must include the user-defined type 'Color'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.3 (negative) — /list omits empty categories
// Only the populated category appears; absent ones don't render headers.
// (carry: legacy/e2e.rs::e2e_s3_3_list_neg_empty_categories_omitted)
#[test]
fn list_neg_empty_categories_omitted() {
    let out = repl("(defn foo [x] x)\n/list\n");
    assert!(
        !out.stdout.contains("Types:"),
        "/list MUST NOT render 'Types:' header when no types defined; got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("Traits:"),
        "/list MUST NOT render 'Traits:' header when no traits defined; got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("Macros:"),
        "/list MUST NOT render 'Macros:' header when no macros defined; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.3 (negative) — /list MUST NOT show the synthetic
// `__expr` top-level-expression wrapper (S91 Phase 6, defect surfaced by /repl).
// FAILING-NOT-IGNORED defect repro — routes to /int to filter `__expr`.
//
// §3.3 says `/list` shows USER definitions. A bare top-level expression eval
// (e.g. `3`, `(foo)`) creates a synthetic `__expr` binding internally; that
// internal wrapper then leaks into the `/list` "Fns:" category. After evaluating
// a single bare expression and nothing else, `/list` MUST report `(no
// definitions)` — there are none. Today it instead renders `Fns:\n  __expr`,
// exposing an internal name the user never wrote. The fix (in /int) filters
// `__expr` from the listing exactly as `$`-mangled internal names are filtered.
// RED today: `/list` contains `__expr`; flips green when the wrapper is filtered.
#[test]
fn list_neg_no_synthetic_expr_wrapper() {
    let out = repl("3\n/list\n");
    assert!(
        !out.stdout.contains("__expr"),
        "/list MUST NOT show the internal `__expr` top-level-expression wrapper \
         per §3.3 (it is not a user definition); got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.3 (negative) — /list does NOT show special forms
// Special forms belong to /imports, not /list.
// (carry: legacy/e2e.rs::e2e_s3_3_list_neg_no_special_forms)
#[test]
fn list_neg_no_special_forms_category() {
    let out = repl("/list\n");
    assert!(
        !out.stdout.contains("Special forms"),
        "/list MUST NOT include 'Special forms' (that's /imports' category); got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.3 (negative) — /list shows '(no definitions)' when
// only imports were made — imports do not constitute user definitions.
// (carry: legacy/e2e.rs::e2e_s3_3_list_neg_no_imports)
#[test]
fn list_neg_only_imports_shows_no_definitions() {
    let out = repl("(import [primitives [add-i64]])\n/list\n");
    assert!(
        out.stdout.contains("(no definitions)"),
        "/list MUST report '(no definitions)' when only imports exist; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// /imports — repl/spec.md §3.4
// =============================================================================

// spec: repl/spec.md §3.4 — /imports shows special forms always present
#[test]
fn imports_lists_special_forms() {
    let out = repl("/imports\n");
    // Special forms are always present per the spec.
    assert!(
        out.stdout.contains("defn") || out.stdout.contains("Special"),
        "/imports must mention special forms; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.4 — /imports shows imported symbols after import
#[test]
fn imports_shows_imported_primitive() {
    let out = repl("(import [primitives [add-i64]])
/imports
");
    assert!(
        out.stdout.contains("add-i64"),
        "/imports must show imported primitive 'add-i64'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.4 (negative) — /imports on a fresh no-prelude session
// MUST NOT show primitives. Primitives reach user code via module-resolution
// fallback, not via import. The Slice 1 bare-primitive fix expanded resolver
// reach but MUST NOT promote primitives into the import-visible surface.
// (carry: legacy/e2e.rs::e2e_s3_4_imports_empty_neg_no_primitives_leak)
#[test]
fn imports_neg_no_primitives_leak_on_fresh_session() {
    let out = repl("/imports\n");
    for leaked in ["add-i64", "eq-i64", "sub-i64", "mul-i64", "primitives/"] {
        assert!(
            !out.stdout.contains(leaked),
            "/imports on fresh no-prelude session MUST NOT show `{leaked}` — \
             primitives reach user code via fallback, not via import; got:\n{}",
            out.stdout
        );
    }
    // No category headers for empty domains.
    for cat in ["Fns:", "Types:", "Traits:", "Macros:"] {
        assert!(
            !out.stdout.contains(cat),
            "/imports on fresh no-prelude session MUST NOT render '{cat}' \
             category — only Special forms applies; got:\n{}",
            out.stdout
        );
    }
}

// =============================================================================
// /imports — Prelude-as-outer-scope presentation (S78 Wave 4 §2.6)
//
// Under the SETTLED prelude-as-outer-scope model
// (`design/int/s78-entry-module.md §2.6`), `/imports` lists prelude-provided
// names under a DISTINCT "Prelude (implicit)" group — present only when the
// per-module prelude fallback is ON. The explicit-import categories
// (Fns/Types/Traits/Macros) narrow to what the module actually imported.
//
// CLASSIFICATION: RED-by-design (the §2.6 tripwire). Under the CURRENT
// flattened model, prelude names are materialised into the module table as
// indistinguishable `Import` entries and render FLAT under Fns/Types — there
// is no "Prelude (implicit)" group, and a refusing module still shows the
// (already-flattened) prelude names. These tests stay failing-not-ignored
// until /dev lands the §2.6 `/imports` group + the per-module fallback bit.
//
// These tests construct the builder directly with a custom `prelude.cl`
// (re-exporting primitives + defining sentinel `gulp`) so the provided
// names are known. cwd is the per-test tmpdir, so the project-root prelude
// shadows stdlib (§8.8.2) and the REPL picks it up.
// =============================================================================

/// Pipe `lines` to a REPL whose project-root `prelude.cl` re-exports
/// primitives and defines sentinel `gulp`.
fn repl_with_gulp_prelude(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .prelude("(export [primitives [*]])\n(defn gulp [x] (add-i64 x 1))\n")
        .repl()
        .stdin(lines)
        .output()
}

// spec: design/int/s78-entry-module.md §2.6 — when the prelude fallback is ON,
//   `/imports` renders prelude-provided names under a distinct
//   "Prelude (implicit)" group (a header containing "Prelude" and "implicit").
//
// CLASSIFICATION: RED-by-design. Current output lists `gulp`/`add-i64` flat
// under `Fns:` with no "Prelude (implicit)" header.
#[test]
fn imports_shows_prelude_implicit_group() {
    let out = repl_with_gulp_prelude("/imports\n");
    let lower = out.stdout.to_lowercase();
    assert!(
        lower.contains("prelude") && lower.contains("implicit"),
        "/imports MUST render a 'Prelude (implicit)' group for prelude-provided \
         names when the fallback is ON; got:\n{}",
        out.stdout
    );
    // The prelude-provided names themselves remain visible (discoverability).
    assert!(
        out.stdout.contains("gulp"),
        "/imports MUST still surface the prelude-provided 'gulp'; got:\n{}",
        out.stdout
    );
}

// spec: design/int/s78-entry-module.md §2.6 — the prelude-provided names MUST
//   NOT be mixed into the explicit-import categories; they belong to the
//   distinct "Prelude (implicit)" group. Here, with NO explicit imports, the
//   explicit `Fns:` category MUST NOT list the prelude-provided `gulp`.
//
// CLASSIFICATION: RED-by-design (negative companion). Current output lists
// `gulp` under a flat `Fns:` category — exactly what the model forbids.
#[test]
fn imports_neg_prelude_names_not_in_explicit_categories() {
    let out = repl_with_gulp_prelude("/imports\n");
    // No explicit imports were made, so the explicit `Fns:` category must be
    // absent (prelude names live in the Prelude group, not here).
    let in_flat_fns = out
        .stdout
        .lines()
        .skip_while(|l| !l.trim_start().starts_with("Fns:"))
        .skip(1)
        .take_while(|l| l.starts_with("  ") || l.trim().is_empty())
        .any(|l| l.trim() == "gulp" || l.trim() == "add-i64");
    assert!(
        !in_flat_fns,
        "/imports MUST NOT list prelude-provided names under a flat explicit \
         'Fns:' category — they belong to the 'Prelude (implicit)' group; \
         got:\n{}",
        out.stdout
    );
}

// spec: design/int/s78-entry-module.md §2.6 — when a module REFUSES the prelude
//   (`(import [prelude []])`), the fallback bit is OFF and the
//   "Prelude (implicit)" group is ABSENT (no implicit fallback is active).
//
// CLASSIFICATION: RED-by-design. Current REPL flattens the prelude before the
// refusal line, so prelude names still appear; and there is no group concept
// to suppress. This pins the model's "group absent when refused".
#[test]
fn imports_neg_no_prelude_group_when_refused() {
    let out = repl_with_gulp_prelude("(import [prelude []])\n/imports\n");
    let lower = out.stdout.to_lowercase();
    assert!(
        !(lower.contains("prelude") && lower.contains("implicit")),
        "/imports MUST NOT render a 'Prelude (implicit)' group when the module \
         refuses the prelude; got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("gulp"),
        "after refusing the prelude, the prelude-provided 'gulp' MUST NOT appear \
         in /imports (no implicit fallback is active); got:\n{}",
        out.stdout
    );
}

// =============================================================================
// /sig, /doc, /info, /type — repl/spec.md §3.1, §3.2
// =============================================================================

// spec: repl/spec.md §3.1 — /sig shows the type signature
#[test]
fn sig_shows_type_signature() {
    let out = repl_prims("(defn inc [x] (add-i64 x 1))
/sig inc
");
    assert!(
        out.stdout.contains("Fn"),
        "/sig must show a function type; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.1 — /doc on un-documented fn says no docstring
#[test]
fn doc_no_docstring() {
    let out = repl_prims("(defn foo [] 42)
/doc foo
");
    assert!(
        out.stdout.contains("no docstring"),
        "/doc must report 'no docstring' for un-documented fn; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.1 — /doc shows the docstring when present
#[test]
fn doc_shows_docstring() {
    let out = repl_prims(r#"(defn foo "increments by zero" [] 42)
/doc foo
"#);
    // The docstring text should appear in /doc output.
    assert!(
        out.stdout.contains("increments by zero"),
        "/doc must surface the docstring text; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.1 — /type shows the type without evaluating (per Command Inventory)
#[test]
fn type_shows_int_for_arithmetic() {
    let out = repl_prims("/type (add-i64 1 2)\n");
    assert!(
        out.stdout.contains("Int"),
        "/type must report Int for arithmetic; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// /help — repl/spec.md §3
// =============================================================================

// spec: repl/spec.md §3.2 — /help lists the command catalogue
#[test]
fn help_lists_commands() {
    repl("/help\n")
        .assert_stdout_contains_all(&["/help", "/list", "/sig"]);
}

// =============================================================================
// /expand — repl/spec.md §11.1
// =============================================================================

// spec: repl/spec.md §11.1 — /expand shows the macro expansion
#[test]
fn expand_user_defmacro() {
    let out = repl_prims("(defmacro double [x] `(add-i64 ~x ~x))
/expand (double 5)
");
    // The expansion should reveal `add-i64` (the macro template).
    assert!(
        out.stdout.contains("add-i64"),
        "/expand must reveal the expansion's body; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §11.1 — /expand on a non-macro form returns it unchanged
#[test]
fn expand_neg_non_macro_unchanged() {
    let out = repl_prims("/expand (add-i64 1 2)\n");
    // Non-macro form should not error.
    assert!(
        !out.stdout.contains("Error"),
        "/expand on non-macro must not error; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// defmacro display — repl/spec.md §4.1.6 / §11.3
// =============================================================================

// spec: repl/spec.md §4.1.6 — single-clause defmacro classified as `; defmacro`
#[test]
fn defmacro_display_single_clause() {
    repl("(defmacro double [x] `(add-i64 ~x ~x))
")
    .assert_stdout_contains(":user/double ; defmacro");
}

// spec: repl/spec.md §4.1.6 — multi-clause defmacro
#[test]
fn defmacro_display_multi_clause() {
    let out = repl("(defmacro pick ([x] x) ([x y] x))
");
    assert!(
        out.stdout.contains(":user/pick ; defmacro"),
        "multi-clause defmacro must display ':user/pick ; defmacro'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §11.4 — bare macro lookup shows it's a macro
#[test]
fn bare_macro_lookup() {
    let out = repl("(defmacro double [x] `(add-i64 ~x ~x))
double
");
    assert!(
        out.stdout.contains("defmacro") || out.stdout.contains("macro"),
        "bare macro lookup must surface its 'macro' classification; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// /list with macros — repl/spec.md §11.2
// =============================================================================

// spec: repl/spec.md §11.2.1 — defmacro appears in /list under Macros
#[test]
fn list_shows_macros_after_defmacro() {
    let out = repl("(defmacro double [x] `(add-i64 ~x ~x))
/list
");
    assert!(
        out.stdout.contains("double"),
        "/list must include defmacro 'double'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §11.2.1 (negative) — defmacro NOT under Fns category
#[test]
fn list_neg_macros_not_in_functions() {
    let out = repl_prims("(defn inc [x] (add-i64 x 1))
(defmacro double [x] `(add-i64 ~x ~x))
/list
");
    // Both 'inc' and 'double' should appear, but 'double' should be in Macros,
    // not Fns. Check for Macros section header presence.
    assert!(
        out.stdout.contains("Macros:") || out.stdout.contains("Macro"),
        "/list must include a Macros category for defmacros; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Symbol-layout (line-breaking) algorithm — repl/spec.md §3.3 rules L0–L4
// (FIXME 0415; /repl promoted the layout to a normative MUST in S87)
//
// STATUS: FAILING-NOT-IGNORED. The live formatter (`src/repl.rs::handle_list`
// + `append_name_category`) does NOT implement the L0–L4 layout at all — it
// renders one name per line and (for Fns) appends `: <type>`. Every rule
// below diverges; the single resolver is /int in `src/repl.rs` (the
// symbol-list formatter). See `tests/plan/ledger.md` S87 RED entry.
// =============================================================================

/// Extract the body lines of a `/list`/`/imports`/`/exports` category — the
/// run of lines beginning with two spaces immediately following the `Label:`
/// header line. REPL stdout prefixes the HEADER line with the timing+prompt
/// banner (`0+0ms; user> Fns:`) but body lines carry no prefix, so we match
/// the header by suffix and collect the indented run that follows.
///
/// Returns the body lines with their leading two spaces stripped, in order.
fn category_body_lines(stdout: &str, label: &str) -> Vec<String> {
    let header = format!("{label}:");
    let mut lines = stdout.lines();
    // Find the header line (it ends with `<label>:` after the prompt banner).
    while let Some(line) = lines.next() {
        if line.trim_end().ends_with(&header) {
            // Collect the indented run.
            let mut body = Vec::new();
            for next in lines.by_ref() {
                if let Some(rest) = next.strip_prefix("  ") {
                    body.push(rest.to_string());
                } else {
                    break;
                }
            }
            return body;
        }
    }
    Vec::new()
}

// spec: repl/spec.md §3.3 — L0: a category with FEWER THAN 7 names renders on a
// SINGLE line after the label, space-separated, with NO line-breaking applied.
#[test]
fn list_layout_l0_under_seven_single_line() {
    // Six Fns (< 7) → one space-separated line: "alpha beta delta eps gamma zeta".
    let out = repl(
        "(defn alpha [] 1)
(defn beta [] 1)
(defn delta [] 1)
(defn eps [] 1)
(defn gamma [] 1)
(defn zeta [] 1)
/list
",
    );
    let body = category_body_lines(&out.stdout, "Fns");
    assert_eq!(
        body,
        vec!["alpha beta delta eps gamma zeta".to_string()],
        "L0: <7 names MUST render on a single space-separated line, names only; got body:\n{:?}\nfull stdout:\n{}",
        body,
        out.stdout
    );
}

// spec: repl/spec.md §3.3 — L0 negative (boundary): EXACTLY 6 names stay
// single-line. The threshold is 7, not 6 — six MUST NOT trigger breaking.
#[test]
fn list_layout_l0_neg_exactly_six_not_broken() {
    let out = repl(
        "(defn alpha [] 1)
(defn beta [] 1)
(defn delta [] 1)
(defn eps [] 1)
(defn gamma [] 1)
(defn zeta [] 1)
/list
",
    );
    let body = category_body_lines(&out.stdout, "Fns");
    assert_eq!(
        body.len(),
        1,
        "L0 boundary: exactly 6 names MUST stay on ONE line (threshold is 7); got {} body lines:\n{:?}\nfull stdout:\n{}",
        body.len(),
        body,
        out.stdout
    );
}

// spec: repl/spec.md §3.3 — L1 boundary: EXACTLY 7 names trigger the breaking
// layout. Where 6 stayed on one line, 7 MUST break into multiple lines.
#[test]
fn list_layout_l1_seven_triggers_break() {
    // Seven Fns across letter groups a,b,c,d,e → operators absent, so L3 packs
    // groups onto rows. With one name per letter (a..g) all 7 names exceed the
    // 6-per-row cap, so the layout MUST produce more than one body line.
    let out = repl(
        "(defn aa [] 1)
(defn bb [] 1)
(defn cc [] 1)
(defn dd [] 1)
(defn ee [] 1)
(defn ff [] 1)
(defn gg [] 1)
/list
",
    );
    let body = category_body_lines(&out.stdout, "Fns");
    assert!(
        body.len() >= 2,
        "L1: 7 names MUST trigger the breaking layout (>1 body line); got {} line(s):\n{:?}\nfull stdout:\n{}",
        body.len(),
        body,
        out.stdout
    );
    // Every body line must hold names-only (no `: type` signature).
    for line in &body {
        assert!(
            !line.contains(':'),
            "L1: body lines MUST be names only (no type signatures); got line {line:?}\nfull stdout:\n{}",
            out.stdout
        );
    }
}

// spec: repl/spec.md §3.3 — L2: operators (non-alphabetic symbols) appear FIRST,
// 6 per line; after the last operator a NEW line MUST start (an operator MUST
// NEVER share a line with an alphabetic name).
#[test]
fn list_layout_l2_operators_first_own_line() {
    // 2 operators + 5 alphabetic names = 7 → breaking layout.
    // Expected:
    //   + -
    //   abs add ceil drop echo
    let out = repl(
        "(defn + [a b] a)
(defn - [a b] a)
(defn abs [x] x)
(defn add [x] x)
(defn ceil [x] x)
(defn drop [x] x)
(defn echo [x] x)
/list
",
    );
    let body = category_body_lines(&out.stdout, "Fns");
    assert!(
        body.first().map(|l| l.as_str()) == Some("+ -"),
        "L2: operators MUST appear first on their own line ('+ -'); got body:\n{:?}\nfull stdout:\n{}",
        body,
        out.stdout
    );
}

// spec: repl/spec.md §3.3 (negative) — L2: an operator MUST NEVER share a row
// with an alphabetic name. No body line may contain BOTH an operator token and
// an alphabetic-name token.
#[test]
fn list_layout_l2_neg_operator_never_shares_name_row() {
    let out = repl(
        "(defn + [a b] a)
(defn - [a b] a)
(defn abs [x] x)
(defn add [x] x)
(defn ceil [x] x)
(defn drop [x] x)
(defn echo [x] x)
/list
",
    );
    let body = category_body_lines(&out.stdout, "Fns");
    let is_operator =
        |tok: &str| tok.chars().next().map(|c| !c.is_alphabetic()).unwrap_or(false);
    for line in &body {
        let toks: Vec<&str> = line.split_whitespace().collect();
        let has_op = toks.iter().any(|t| is_operator(t));
        let has_name = toks.iter().any(|t| !is_operator(t));
        assert!(
            !(has_op && has_name),
            "L2 negative: a row MUST NOT mix operators and alphabetic names; got row {line:?}\nfull stdout:\n{}",
            out.stdout
        );
    }
}

// spec: repl/spec.md §3.3 — L3: letter groups break early to stay together. A
// group is flushed to a fresh row when `current_count + group_size > 6`; a group
// MUST therefore appear entirely on one row (unless it alone has 7+ names — L4).
#[test]
fn list_layout_l3_letter_group_early_break() {
    // Group sizes: a=4 (aa,ab,ac,ad), b=4 (ba,bb,bc,bd). Total 8 → breaking.
    // a-group (4) fits on row 1; adding b-group (4) → 4+4=8 > 6, so b flushes
    // to a fresh row. Expected exactly two rows, each holding one whole group:
    //   aa ab ac ad
    //   ba bb bc bd
    let out = repl(
        "(defn aa [] 1)
(defn ab [] 1)
(defn ac [] 1)
(defn ad [] 1)
(defn ba [] 1)
(defn bb [] 1)
(defn bc [] 1)
(defn bd [] 1)
/list
",
    );
    let body = category_body_lines(&out.stdout, "Fns");
    assert_eq!(
        body,
        vec!["aa ab ac ad".to_string(), "ba bb bc bd".to_string()],
        "L3: letter groups MUST early-break to stay whole (a-group then b-group on separate rows); got body:\n{:?}\nfull stdout:\n{}",
        body,
        out.stdout
    );
}

// spec: repl/spec.md §3.3 (negative) — L3: no letter group straddles a row
// boundary. Every body line's names share a common first letter, OR the line is
// a packed run of complete single-letter groups (no group split across rows).
#[test]
fn list_layout_l3_neg_no_group_straddles_row() {
    let out = repl(
        "(defn aa [] 1)
(defn ab [] 1)
(defn ac [] 1)
(defn ad [] 1)
(defn ba [] 1)
(defn bb [] 1)
(defn bc [] 1)
(defn bd [] 1)
/list
",
    );
    let body = category_body_lines(&out.stdout, "Fns");
    // Build per-row sets of first letters; a group straddles iff the same first
    // letter appears on two different rows.
    use std::collections::{HashMap, HashSet};
    let mut letter_rows: HashMap<char, HashSet<usize>> = HashMap::new();
    for (row, line) in body.iter().enumerate() {
        for tok in line.split_whitespace() {
            if let Some(c) = tok.chars().next() {
                if c.is_alphabetic() {
                    letter_rows.entry(c.to_ascii_lowercase()).or_default().insert(row);
                }
            }
        }
    }
    for (letter, rows) in &letter_rows {
        assert!(
            rows.len() <= 1,
            "L3 negative: letter group '{letter}' MUST NOT straddle a row boundary (found on rows {rows:?}); body:\n{:?}\nfull stdout:\n{}",
            body,
            out.stdout
        );
    }
}

// spec: repl/spec.md §3.3 — L4: a single letter group with MORE THAN 6 names
// hard-wraps at 6 names per line within itself.
#[test]
fn list_layout_l4_oversized_group_wraps_at_six() {
    // One letter group 'a' with 7 names → wraps 6 + 1:
    //   aa ab ac ad ae af
    //   ag
    let out = repl(
        "(defn aa [] 1)
(defn ab [] 1)
(defn ac [] 1)
(defn ad [] 1)
(defn ae [] 1)
(defn af [] 1)
(defn ag [] 1)
/list
",
    );
    let body = category_body_lines(&out.stdout, "Fns");
    assert_eq!(
        body,
        vec!["aa ab ac ad ae af".to_string(), "ag".to_string()],
        "L4: an oversized single-letter group MUST hard-wrap at 6/line; got body:\n{:?}\nfull stdout:\n{}",
        body,
        out.stdout
    );
}

// spec: repl/spec.md §3.3, §3.4, §3.5 — cross-command consistency: the SAME name
// set fed to `/list` and `/exports` produces BYTE-FOR-BYTE identical layout (one
// shared formatter, not three divergent ones).
#[test]
fn layout_cross_command_list_exports_byte_identical() {
    // Define 7 Fns in a submodule `m`, then compare `/exports m` against `/list`
    // run while the cursor is in `m`. Same name set ⇒ identical category body.
    let list_out = repl(
        "(defn aa [] 1)
(defn ab [] 1)
(defn ac [] 1)
(defn ad [] 1)
(defn ba [] 1)
(defn bb [] 1)
(defn bc [] 1)
/list
",
    );
    let exports_out = repl(
        "(defn aa [] 1)
(defn ab [] 1)
(defn ac [] 1)
(defn ad [] 1)
(defn ba [] 1)
(defn bb [] 1)
(defn bc [] 1)
/exports user
",
    );
    let list_body = category_body_lines(&list_out.stdout, "Fns");
    let exports_body = category_body_lines(&exports_out.stdout, "Fns");
    assert_eq!(
        list_body, exports_body,
        "/list and /exports MUST produce byte-for-byte identical Fns layout for the same name set;\n/list body:\n{:?}\n/exports body:\n{:?}\n/list stdout:\n{}\n/exports stdout:\n{}",
        list_body, exports_body, list_out.stdout, exports_out.stdout
    );
}

// spec: repl/spec.md §3.3 (negative) — category purity: the Fns layout body
// holds ONLY names defined in the current module — no `: type` signatures leak
// into the name rows, and no primitives (`add-i64`) appear.
#[test]
fn list_layout_neg_names_only_no_type_sigs() {
    let out = repl(
        "(defn aa [] 1)
(defn ab [] 1)
(defn ac [] 1)
(defn ad [] 1)
(defn ba [] 1)
(defn bb [] 1)
(defn bc [] 1)
/list
",
    );
    let body = category_body_lines(&out.stdout, "Fns");
    for line in &body {
        assert!(
            !line.contains(':') && !line.contains("Fn ["),
            "category purity: Fns rows MUST be names only — no type signatures; got row {line:?}\nfull stdout:\n{}",
            out.stdout
        );
        assert!(
            !line.contains("add-i64"),
            "category purity: a user-module /list MUST NOT leak primitives; got row {line:?}\nfull stdout:\n{}",
            out.stdout
        );
    }
}

// =============================================================================
// Multi-eval persistence — repl/spec.md §15.2
// =============================================================================

// spec: repl/spec.md §15.2 — defns persist across REPL eval rounds
#[test]
fn defn_persists_across_evals() {
    repl_prims("(defn double [x] (mul-i64 x 2))
(double 21)
")
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: repl/spec.md §15.2 — multiple defns coexist
#[test]
fn multi_defn_coexist() {
    repl_prims("(defn one [] 1)
(defn two [] 2)
(add-i64 (one) (two))
")
    .assert_stdout_contains(":primitives/Int 3");
}

// =============================================================================
// Empty / whitespace input — repl/spec.md §2.3
// =============================================================================

// spec: repl/spec.md §2.3 — empty input is silent (no error)
#[test]
fn empty_input_silent() {
    let out = repl("\n");
    assert!(
        !out.stdout.to_lowercase().contains("error"),
        "blank input must not error; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §2.3 — comment-only input is silent
#[test]
fn comment_only_silent() {
    let out = repl("; just a comment\n");
    assert!(
        !out.stdout.to_lowercase().contains("error"),
        "comment-only input must not error; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Slash commands tolerate unknown names gracefully — repl/spec.md §5.2
// =============================================================================

// spec: repl/spec.md §5.2 — /sig of unknown name is graceful
#[test]
fn sig_unknown_name_graceful() {
    let out = repl("/sig nonexistent-name\n");
    // Should not crash; should give some message.
    assert!(out.status.success(), "/sig of unknown must not crash REPL");
}

// =============================================================================
// Wave 5.6 file 6 e2e.rs chunk-1 GAP-COVER carry-forwards (per
// tests/plan/wave-5.6-e2e-reaudit.md). Each carries a `(carry: legacy/...)`
// provenance tag. Three prelude-Option tests are REGRESSION-GUARDs against
// historic display BUGs (raw-pointer / definition-vs-value display) that
// the current implementation no longer exhibits — they land green and are
// preserved as durable regression guards per
// memory/feedback_repros_join_suite.md.
// =============================================================================

// spec: repl/spec.md §4.1.2 — a BARE nullary-constructor lookup is a
// Constructor INTROSPECTION display `:{type} {module}/{Type.Ctor} ; deftype`
// (spec example: `Red` -> `:user/Color user/Color.Red ; deftype`). It MUST be
// enveloped identically to an applied/function-typed ctor's bare lookup
// (`Some` -> `:(Fn [a] (…/Option a)) primitives/Option.Some ; deftype`): same
// `; deftype` suffix, same `{module}/` qualifier on the ctor home.
// defect: class=display-envelope-mirror locus=src/eval.rs::check_bare_symbol_introspection found=S108 owner=/dev
//
// Fixed S108 (D2). Before the fix a bare CONCRETE nullary ctor showed
// `:user/Color Color.Red` — dropping BOTH the module qualifier and `; deftype`.
// `check_bare_symbol_introspection` special-cased `field_count == 0` and routed
// nullary ctors to runtime EVALUATION + the value-display envelope (src/display.rs
// `:{type} {ctor}`) instead of the introspection envelope (src/repl.rs
// `format_def_entry` Constructor arm: `:{type} {module}/{ctor} ; deftype`) — two
// code paths formatting one concept, diverged. The fix collapsed the duplication,
// routing only the CONCRETE bare nullary ctor through the same `format_def_entry`
// Constructor arm as applied ctors, discriminated by `Type::is_concrete()`
// (crates/cranelisp-types/src/types.rs). The divergence never extended to the
// seeded `Option`/`None`: bare `None` is result-only-polymorphic and its value
// display WITHOUT `; deftype` (`:(prelude/Option a) Option.None`) is AS-SPECIFIED
// by §1.5.1 (`None` is a value, not an instance of this defect — pinned green by
// prelude_option_none_value_display_neg_definition_metadata); the non-concrete
// case falls to the §1.5.1 value display, and the display.rs value path remains
// for genuine runtime values (§1.5, e.g. `(Some 42)`).
#[test]
fn nullary_constructor_bare_lookup_shows_deftype_and_qualified_home() {
    let out = repl("(deftype Color (Red) (Green))
Red
");
    // Assert the FULL §4.1.2 line as one substring — the `; deftype` and the
    // qualified `user/Color.Red` together. A looser `contains("; deftype")`
    // would false-pass on the `deftype` DEFINITION echo (`:user/Color ; deftype`).
    assert!(
        out.stdout.contains(":user/Color user/Color.Red ; deftype"),
        "bare nullary ctor 'Red' MUST display ':user/Color user/Color.Red ; deftype' \
         per §4.1.2 (qualified ctor home + '; deftype' classification), enveloped \
         identically to an applied ctor; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.5 — applied data constructor displays in
// parenthesised dot-notation `(Type.Ctor args...)` value form.
// (carry: legacy/e2e.rs::e2e_s1_5_data_ctor_dot_notation)
#[test]
fn data_constructor_applied_dot_notation_display() {
    repl("(deftype (Option a) None (Some [:a val]))
(Some 42)
")
    .assert_stdout_contains("(Option.Some 42)");
}

// spec: repl/spec.md §1.5 — prelude-Option `(Some 42)` value displays in
// dot-notation; MUST NOT show a raw heap pointer in the value position.
// REGRESSION-GUARD: the legacy test was marked "BUG"; the current
// implementation displays the value correctly.
// (carry: legacy/e2e.rs::e2e_s1_5_prelude_option_some_display)
#[test]
fn prelude_option_some_display_neg_raw_pointer() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("(Some 42)\n")
        .output();
    assert!(
        out.stdout.contains("(Option.Some 42)"),
        "prelude `(Some 42)` MUST display as `(Option.Some 42)`; got:\n{}",
        out.stdout
    );
    // Negative: must NOT contain a long-digit-string raw heap pointer where
    // the value should appear. Allow the `(Option.Some 42)` token itself.
    let leak = out
        .stdout
        .lines()
        .any(|l| {
            l.contains("Option")
                && l.chars().filter(|c| c.is_ascii_digit()).count() > 5
                && !l.contains("(Option.Some 42)")
        });
    assert!(
        !leak,
        "result must not contain a raw heap pointer; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.5.1 — Bare Polymorphic Values — Type Display via
// Introspection. A bare `None` (type `∀a. (Option a)`) entered at the REPL
// DISPLAYS its polymorphic type/value (`Option.None`); it is a type-display
// disposition (spec §3.11.2), NOT an ambiguity error (§3.11.1 fires only when
// the same value reaches codegen). MUST NOT render the *definition* drawer
// (`; deftype` / `fn.option/` qualified path) when bare `None` is a value.
// SPEC-CORRECT under the §3.11 ruling (FIXME 0378) — MUST stay GREEN; the
// /dev relay keeps it green via introspection after the slot-less reshape.
// (carry: legacy/e2e.rs::e2e_s1_5_prelude_option_none_display)
#[test]
fn prelude_option_none_value_display_neg_definition_metadata() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("None\n")
        .output();
    assert!(
        out.stdout.contains("Option.None"),
        "bare `None` MUST display the value `Option.None`; got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("; deftype"),
        "bare `None` (value) MUST NOT show the deftype-definition drawer; got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("fn.option/"),
        "bare `None` MUST NOT show a module-qualified constructor path; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.5 — prelude-Option `(Some "hello")` displays the
// string contents inside the dot-notation form; MUST NOT render a raw
// heap pointer for the String payload.
// REGRESSION-GUARD: legacy test marked "BUG"; current implementation shows
// the formatted value correctly.
// (carry: legacy/e2e.rs::e2e_s1_5_prelude_option_some_string_display)
#[test]
fn prelude_option_some_string_payload_display() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("(Some \"hello\")\n")
        .output();
    assert!(
        out.stdout.contains("\"hello\""),
        "prelude `(Some \"hello\")` MUST display the string payload; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("Option.Some"),
        "prelude `(Some \"hello\")` MUST use `Option.Some` ctor notation; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.4 — `/info <name>` shows symbol metadata including
// the compiled code size in `bytes`.
// (carry: legacy/e2e.rs::e2e_s3_4_info)
#[test]
fn info_shows_symbol_metadata_with_code_size() {
    let out = repl_prims("(defn double [x] (mul-i64 x 2))
/info double
");
    assert!(
        out.stdout.contains("double"),
        "/info MUST surface the symbol name 'double'; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("bytes"),
        "/info MUST surface the compiled code size as 'bytes'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.6 — `/info <name>` MUST display the definition
// source between the signature line and the code stats (the §3.6 worked
// example's second line). FIXME 0480: this third MUST component was omitted
// for both the healthy and broken arms; the broken-arm guard lives in
// tests/repl_redefinition.rs::redefine_broken_caller_info_and_sig_report_broken_status.
#[test]
fn info_shows_definition_source_line() {
    let out = repl_prims("(defn double [x] (mul-i64 x 2))\n/info double\n");
    assert!(
        out.stdout.contains("(defn double") && out.stdout.contains("(mul-i64 x 2)"),
        "/info MUST display the definition source (repl/spec.md §3.6); got:\n{}",
        out.stdout
    );
    // Order: the source block precedes the code-size stats line.
    let src_pos = out.stdout.find("(defn double").unwrap();
    let bytes_pos = out.stdout.find(" bytes").unwrap_or(usize::MAX);
    assert!(
        src_pos < bytes_pos,
        "definition source must precede the code stats (§3.6 layout); got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.1 — `/time <expr>` displays elapsed evaluation time
// in milliseconds.
// (carry: legacy/e2e.rs::e2e_s3_1_time)
#[test]
fn time_shows_expression_timing_in_ms() {
    let out = repl_prims("/time (add-i64 1 2)\n");
    assert!(
        out.stdout.contains("ms"),
        "/time MUST surface elapsed time in milliseconds; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.1 — bare primitive type-name lookup produces type
// info, not an "undefined" error. The Int instance is canonical here; the
// same display shape applies to Bool/Float/String (see legacy
// `e2e_s1_1_bare_type_{bool,float,string}` — absorbed by this carry per
// the Wave 5.6 audit).
// (carry: legacy/e2e.rs::e2e_s1_1_bare_type_int)
#[test]
fn bare_primitive_type_int_displays_type_info() {
    let out = repl("Int\n").assert_ok();
    assert!(
        !out.stdout.contains("Error:"),
        "bare 'Int' MUST display type info, not an error; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("Int"),
        "bare 'Int' MUST mention the type name in display; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.1 — bare user-defined type-name lookup produces
// type info, distinct from the primitive case (separate resolution path
// through user-defined-type registry vs primitive type registry).
// (carry: legacy/e2e.rs::e2e_s1_1_bare_type_user_defined)
#[test]
fn bare_user_defined_type_lookup_displays_type_info() {
    let out = repl("(deftype Color Red Green Blue)
Color
")
    .assert_ok();
    assert!(
        !out.stdout.contains("Error:"),
        "bare user-defined type 'Color' MUST display type info, not error; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("Color"),
        "bare 'Color' MUST mention the type name in display; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Wave 5.6 file 6 e2e.rs chunk-2 GAP-COVER carry-forwards (per
// tests/plan/wave-5.6-e2e-reaudit.md chunk 2). Each carries a
// `(carry: legacy/...)` provenance tag.
// =============================================================================

// spec: repl/spec.md §4.1.5 — bare `fn` self-documents (no error; signature
// shape `(Fn [params body] function)` and the keyword name in the line).
// (carry: legacy/e2e.rs::e2e_s4_2_special_form_fn)
#[test]
fn special_forms_bare_lookup_fn_self_documenting() {
    let out = repl("fn\n");
    assert!(
        !out.stdout.contains("Error:"),
        "bare 'fn' MUST self-document (not error); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("Fn") && out.stdout.contains("fn"),
        "bare 'fn' MUST surface a signature-shaped line containing 'Fn' and the keyword 'fn'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.5 — bare `defn` self-documents.
// (carry: legacy/e2e.rs::e2e_s4_2_special_form_defn)
#[test]
fn special_forms_bare_lookup_defn_self_documenting() {
    let out = repl("defn\n");
    assert!(
        !out.stdout.contains("Error:"),
        "bare 'defn' MUST self-document (not error); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("Fn") && out.stdout.contains("defn"),
        "bare 'defn' MUST surface a signature-shaped line containing 'Fn' and the keyword 'defn'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.5 — bare `deftype` self-documents.
// (carry: legacy/e2e.rs::e2e_s4_2_special_form_deftype)
#[test]
fn special_forms_bare_lookup_deftype_self_documenting() {
    let out = repl("deftype\n");
    assert!(
        !out.stdout.contains("Error:"),
        "bare 'deftype' MUST self-document (not error); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("Fn") && out.stdout.contains("deftype"),
        "bare 'deftype' MUST surface a signature-shaped line containing 'Fn' and the keyword 'deftype'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.5 — bare `match` self-documents.
// (carry: legacy/e2e.rs::e2e_s4_2_special_form_match)
#[test]
fn special_forms_bare_lookup_match_self_documenting() {
    let out = repl("match\n");
    assert!(
        !out.stdout.contains("Error:"),
        "bare 'match' MUST self-document (not error); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("Fn") && out.stdout.contains("match"),
        "bare 'match' MUST surface a signature-shaped line containing 'Fn' and the keyword 'match'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.5 — bare `defmacro` self-documents (does NOT
// produce an "undefined variable" error). Distinct code path from the
// other special forms (`defmacro` is handled by the macro registry).
// (carry: legacy/e2e.rs::e2e_s4_2_special_form_defmacro)
#[test]
fn special_forms_bare_lookup_defmacro_self_documenting() {
    let out = repl("defmacro\n");
    assert!(
        !out.stdout.contains("undefined variable"),
        "bare 'defmacro' MUST self-document (not 'undefined variable'); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("Fn") && out.stdout.contains("defmacro"),
        "bare 'defmacro' MUST surface a signature-shaped line containing 'Fn' and the keyword 'defmacro'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.8 — bare `+` operator self-documents (Fn type).
// Operator availability requires the trait + impls, supplied by the
// TestStandard prelude (Num/Eq/Ord on Int/Float/Bool/String).
// (carry: legacy/e2e.rs::e2e_s4_3_operator_plus_feedback)
#[test]
fn operator_plus_bare_lookup_displays_signature() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("+\n")
        .output();
    assert!(
        !out.stdout.contains("Error:"),
        "bare '+' MUST display type info (not error); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("Fn") && out.stdout.contains("+"),
        "bare '+' MUST surface 'Fn' + the operator symbol; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.8 — bare `=` operator self-documents (Fn returning Bool).
// (carry: legacy/e2e.rs::e2e_s4_3_operator_eq_feedback)
#[test]
fn operator_eq_bare_lookup_displays_signature() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("=\n")
        .output();
    assert!(
        !out.stdout.contains("Error:"),
        "bare '=' MUST display type info (not error); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("Fn") && out.stdout.contains("Bool"),
        "bare '=' MUST surface 'Fn' + Bool return type; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.8 — bare `<` operator self-documents (Fn returning Bool).
// (carry: legacy/e2e.rs::e2e_s4_3_operator_lt_feedback)
#[test]
fn operator_lt_bare_lookup_displays_signature() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("<\n")
        .output();
    assert!(
        !out.stdout.contains("Error:"),
        "bare '<' MUST display type info (not error); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("Fn") && out.stdout.contains("Bool"),
        "bare '<' MUST surface 'Fn' + Bool return type; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.3 — `/list` shows a Traits category after a
// `deftrait` form. Distinct from `list_shows_types_category` (Types
// category) and `list_shows_macros_after_defmacro` (Macros category).
// (carry: legacy/e2e.rs::e2e_s3_3_list_traits)
#[test]
fn list_shows_traits_after_deftrait() {
    let out = repl_prims("(deftrait Sizeable (size [self] Int))
/list
");
    assert!(
        out.stdout.contains("Traits"),
        "/list MUST surface 'Traits' category after deftrait; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("Sizeable"),
        "/list MUST list the user-defined trait 'Sizeable'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §11.1 — `/expand` recursively expands nested macros to
// fixed point (the expansion result MUST NOT contain a still-expandable
// macro reference). The fixpoint property defends against partial
// expansion that would leave unresolved macro references in the output.
// (carry: legacy/e2e.rs::e2e_s11_1_expand_nested_macros)
#[test]
fn expand_recursively_to_fixpoint() {
    let out = repl_prims("(defmacro inc [x] `(add-i64 ~x 1))
(defmacro double-inc [x] `(inc (inc ~x)))
/expand (double-inc 5)
");
    // The /expand line must contain `add-i64` (fully expanded form).
    let expand_line = out
        .stdout
        .lines()
        .find(|l| l.contains("add-i64"))
        .unwrap_or_else(|| panic!(
            "/expand MUST recursively expand to add-i64; got:\n{}",
            out.stdout
        ));
    // Negative: the expansion MUST NOT contain `inc` — fixpoint reached.
    assert!(
        !expand_line.contains("inc"),
        "/expand MUST reach fixed point (no 'inc' in expansion); got line:\n{}",
        expand_line
    );
}

// spec: repl/spec.md §11.2.4 — `/doc <macro>` on a macro without a
// docstring surfaces the macro name (not an error). Distinct code path
// from /doc on a fn (covered by `doc_no_docstring`).
// (carry: legacy/e2e.rs::e2e_s11_2_4_doc_macro_no_docstring)
#[test]
fn doc_macro_no_docstring() {
    let out = repl("(defmacro my-mac [x] x)
/doc my-mac
");
    assert!(
        out.stdout.contains("my-mac"),
        "/doc on docstringless macro MUST mention the macro name; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §11.2.4 — `/doc <macro>` surfaces the docstring text
// when the macro was defined with one. Distinct code path from /doc on a
// fn (covered by `doc_shows_docstring`).
// (carry: legacy/e2e.rs::e2e_s11_2_4_doc_macro_with_docstring)
#[test]
fn doc_macro_with_docstring() {
    let out = repl_prims("(defmacro my-inc \"Increment by one\" [x] `(add-i64 ~x 1))
/doc my-inc
");
    assert!(
        out.stdout.contains("Increment by one"),
        "/doc on documented macro MUST surface the docstring text; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §11.2.2 — `/info <macro>` on a MULTI-CLAUSE macro MUST
// display the clause COUNT. The §11.2.2 worked example shows `/info cond`
// emitting all clause signatures followed by `  2 clauses`. This test asserts
// the count line is present alongside the clause signatures and docstring.
//
// FAILING-NOT-IGNORED defect guard (resolver: /repl): the current `/info` output
// lists clause signatures + docstring but does NOT emit the `N clauses` count
// line. This is a spec↔impl divergence in REPL introspection formatting (owner
// /repl resolves the spec/format question; /int wires the count into the
// `/info` macro card). Flips GREEN when the count line is emitted. Also covers
// the §11.2.2 table-row gap (no `/info`-multi-clause-macro test).
#[test]
fn info_multi_clause_macro_shows_clause_count() {
    let out = repl_prims(
        "(defmacro cond \"Multi-way conditional\" ([x] x) ([x body & rest] x))\n\
         /info cond\n",
    );
    let display = &out.stdout;
    // Precondition: the clause signatures and classification are present (the
    // parts that already work — keeps the failure attributable to the count).
    assert!(
        display.contains("defmacro") && display.contains("[x] -> Sexp"),
        "/info on a macro MUST show classification + clause signatures; \
         got:\n{display}"
    );
    // The defect: the clause COUNT line MUST appear per §11.2.2.
    assert!(
        display.contains("2 clauses"),
        "/info on a multi-clause macro MUST display the clause count \
         (`2 clauses`) per repl/spec.md §11.2.2; got:\n{display}"
    );
}

// spec: repl/spec.md §3.4 — `/imports <module>` filters listed imports by
// source module. With an explicit primitive import, `/imports primitives`
// MUST show the imported primitive name. Distinct from
// `imports_shows_imported_primitive` which exercises the no-arg form.
// (carry: legacy/e2e.rs::e2e_s3_4_imports_filter_by_module)
#[test]
fn imports_filter_by_source_module() {
    let out = repl("(import [primitives [add-i64]])
/imports primitives
");
    assert!(
        out.stdout.contains("add-i64"),
        "/imports primitives MUST show the imported primitive 'add-i64'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.4 — `/imports <nonexistent>` MUST NOT error. The
// graceful-handling property: a misspelled or nonexistent module produces
// an empty/quiet listing, not a stack trace or error message.
// (carry: legacy/e2e.rs::e2e_s3_4_neg_imports_nonexistent_not_error)
#[test]
fn imports_filter_neg_nonexistent_module_not_error() {
    let out = repl("/imports nonexistent
");
    assert!(
        !out.stdout.contains("Error:"),
        "/imports <nonexistent> MUST NOT error; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.3 — `/list <prefix>` performs a case-insensitive
// prefix match across categories. Three defns (`foo`, `bar`, `fuzz`) +
// `/list f` MUST surface the f-prefixed names. Preserves the legacy
// positive-only assertion shape (presence of `foo` + `fuzz`).
// (carry: legacy/e2e.rs::e2e_s3_3_list_prefix_filter)
#[test]
fn list_prefix_filter_matches_names() {
    let out = repl("(defn foo [x] x)
(defn bar [x] x)
(defn fuzz [x] x)
/list f
");
    assert!(
        out.stdout.contains("foo"),
        "/list f MUST surface 'foo' (prefix match); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("fuzz"),
        "/list f MUST surface 'fuzz' (prefix match); got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Wave 5.6 file 6 e2e.rs chunk-3 GAP-COVER carry-forwards (per
// tests/plan/wave-5.6-e2e-reaudit.md chunk 3). Each carries a
// `(carry: legacy/...)` provenance tag.
// =============================================================================

// spec: repl/spec.md §3.4 — neg: `/imports nonexistent` is silent AND the
// REPL recovers — a subsequent expression evaluates normally. Distinct
// from `imports_filter_neg_nonexistent_module_not_error` (which only
// asserts the no-error angle): this preserves the recovery property
// (session continuity after a slash-command argument-edge case).
// (carry: legacy/e2e.rs::e2e_s3_4_neg_imports_nonexistent_silent)
#[test]
fn imports_filter_neg_nonexistent_silent_recovery() {
    let out = repl("/imports nonexistent
42
")
    .assert_ok();
    assert!(
        !out.stdout.contains("Error:"),
        "/imports nonexistent MUST be silent (no Error); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":primitives/Int 42"),
        "REPL MUST recover and evaluate the next expression; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.5 — `/exports` with no argument MUST emit a usage hint.
// (carry: legacy/e2e.rs::e2e_s3_5_exports_no_arg_usage)
#[test]
fn exports_no_arg_shows_usage() {
    let out = repl("/exports\n");
    let s = &out.stdout;
    assert!(
        s.contains("Usage:") || s.contains("usage:") || s.contains("/exports <module"),
        "/exports with no arg MUST surface a usage hint; got:\n{}",
        s
    );
}

// spec: repl/spec.md §3.5 — `/exports <nonexistent>` MUST NOT crash and
// MUST surface a graceful module-missing message.
// (carry: legacy/e2e.rs::e2e_s3_5_exports_not_found)
#[test]
fn exports_neg_nonexistent_module_not_found() {
    let out = repl("/exports nonexistent\n");
    let s = &out.stdout;
    assert!(
        s.contains("not found") || s.contains("Module"),
        "/exports nonexistent MUST surface a 'not found' / 'Module' diagnostic; got:\n{}",
        s
    );
}

// spec: repl/spec.md §3.5 — `/exports <mod>` lists the module's public
// symbols. Define `bar` in `mymod`, switch back to `user`, then
// `/exports mymod` MUST surface `bar`.
// (carry: legacy/e2e.rs::e2e_s3_5_exports_lists_symbols)
#[test]
fn exports_lists_public_symbols_after_defn() {
    let out = repl("/mod mymod
(defn bar [x] x)
/mod user
/exports mymod
");
    assert!(
        out.stdout.contains("bar"),
        "/exports mymod MUST list the public symbol 'bar'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.3 — deftype display includes a `; match:` section
// header listing constructors. Distinct from
// `deftype_display_lists_constructors` (which asserts the ctors-listed
// angle without enforcing the section-header substring).
// (carry: legacy/e2e.rs::e2e_s1_3_deftype_match_section)
#[test]
fn deftype_display_match_section_header() {
    let out = repl("(deftype Color Red Green Blue)\n");
    assert!(
        out.stdout.contains("; match:"),
        "deftype display MUST include a '; match:' section per §1.3; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("Red") && out.stdout.contains("Green") && out.stdout.contains("Blue"),
        "deftype '; match:' section MUST list constructors; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.3 — deftrait display includes a `; deftrait`
// classification AND a `; defn:` section header listing methods.
// (carry: legacy/e2e.rs::e2e_s1_3_deftrait_defn_section)
#[test]
fn deftrait_display_defn_section_lists_methods() {
    let out = repl("(deftrait (Sizeable a) (size [a] Int))\n");
    assert!(
        out.stdout.contains("; deftrait"),
        "deftrait display MUST include '; deftrait' classification; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("; defn:"),
        "deftrait display MUST include a '; defn:' section per §1.3; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("size"),
        "deftrait '; defn:' section MUST list method 'size'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.1 — bare fn lookup (after defn) shows `; defn`
// classification on the lookup line. Distinct from `defn_display_one_param`
// (which asserts the 1st-result line of the `defn` form): this asserts
// the bare-symbol-lookup re-display path produces the same classification.
// (carry: legacy/e2e.rs::e2e_s4_1_bare_fn_classification)
#[test]
fn bare_fn_lookup_after_defn_shows_defn_classification() {
    let out = repl_prims("(defn inc [n] (add-i64 n 1))
inc
");
    assert!(
        out.stdout.contains("; defn"),
        "bare fn lookup MUST surface '; defn' classification; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.3 — bare type lookup shows `; deftype` AND a
// `; match:` section header. Distinct from `bare_user_defined_type_lookup_displays_type_info`
// (which asserts only no-error + name presence): this enforces the
// classification token + section header per the universal-format spec.
// (carry: legacy/e2e.rs::e2e_s4_1_bare_type_match_section)
#[test]
fn bare_type_lookup_includes_match_section() {
    let out = repl("(deftype Color Red Green Blue)
Color
");
    assert!(
        out.stdout.contains("; deftype"),
        "bare type 'Color' MUST surface '; deftype' classification; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("; match:"),
        "bare type 'Color' MUST surface '; match:' section per §4.1.3; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.3 — a bare type lookup MUST surface the `; match:`
// constructor section for EVERY deftype-classified ADT, including the
// primitives-SEEDED ADTs (Option/Result/IO) reached via the implicit prelude
// glob — not only user-module deftypes. §4.1.3's canonical example IS `Option`
// → `; match:` / `;  None Some`.
// defect: class=wrong-scope-lookup locus=src/repl.rs::format_type_display found=S108 owner=/dev
//
// Fixed S108 (D1). Before the fix `format_type_display` looked up constructors
// via `lookup_type_def_chain` from `current_module_path()` ("user"), NOT the
// type's resolved home (primitives), so for a seeded ADT the chain never
// reached the home and the primary line surfaced without `; match:`. A user
// deftype (Rotation) worked only incidentally because scope == home; Some/None
// resolved individually, so the ctor DATA existed — a reverse-lookup scope bug,
// not missing data. The fix roots the constructor chain-lookup at the resolved
// home `module` the function already holds (at the home the TypeDef is local,
// chain terminates depth 0).
#[test]
fn seeded_option_bare_lookup_includes_match_section() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin("Option\n")
        .output();
    assert!(
        out.stdout.contains(":primitives/Option ; deftype"),
        "bare 'Option' MUST surface ':primitives/Option ; deftype'; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("; match:"),
        "bare seeded ADT 'Option' MUST surface '; match:' section per §4.1.3, \
         same as a user deftype; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("None") && out.stdout.contains("Some"),
        "bare 'Option' '; match:' section MUST list constructors None and Some; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.4 — bare trait lookup shows `; deftrait`
// classification AND a `; defn:` section listing methods.
// (carry: legacy/e2e.rs::e2e_s4_1_bare_trait_defn_section)
#[test]
fn bare_trait_lookup_includes_defn_section() {
    let out = repl("(deftrait (Sizeable a) (size [a] Int))
Sizeable
");
    assert!(
        out.stdout.contains("; deftrait"),
        "bare trait 'Sizeable' MUST surface '; deftrait' classification; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("; defn:"),
        "bare trait 'Sizeable' MUST surface '; defn:' section per §4.1.4; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("size"),
        "bare trait '; defn:' section MUST list method 'size'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.5 — bare special form `if` shows `; special form`
// classification token. Strictly stronger than the bare-`if`/`let` self-doc
// tests (which only assert no-error + Fn/Bool); this enforces the universal-
// format classification token specifically.
// (carry: legacy/e2e.rs::e2e_s4_1_bare_special_form_classification)
#[test]
fn bare_special_form_if_classification_token() {
    let out = repl("if\n");
    assert!(
        out.stdout.contains("; special form"),
        "bare 'if' MUST surface '; special form' classification per §4.1.5; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.6 — bare macro lookup shows `; defmacro`
// classification AND clause signature `; [x] -> Sexp`.
// (carry: legacy/e2e.rs::e2e_s4_1_bare_macro_defmacro)
#[test]
fn bare_macro_lookup_shows_clause_signature() {
    let out = repl_prims("(defmacro inc [x] `(add-i64 ~x 1))
inc
");
    assert!(
        out.stdout.contains("; defmacro"),
        "bare macro 'inc' MUST surface '; defmacro' classification; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("; [x] -> Sexp"),
        "bare macro 'inc' MUST surface clause signature '; [x] -> Sexp' per §4.1.6; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.3 — bare builtin type `Int` shows `; type`
// classification token AND the FQN `primitives/Int`. Distinct from
// `bare_primitive_type_int_displays_type_info` (which only asserts no-error
// + name presence).
// (carry: legacy/e2e.rs::e2e_s4_1_bare_builtin_type)
#[test]
fn bare_builtin_type_int_shows_type_classification() {
    let out = repl("Int\n");
    assert!(
        out.stdout.contains("; type"),
        "bare 'Int' MUST surface '; type' classification per §4.1.3; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("primitives/Int"),
        "bare 'Int' MUST surface FQN 'primitives/Int'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.3 — neg: `/list` MUST NOT show `Fns:` category
// when only deftype is defined. Distinct from
// `list_neg_no_special_forms_category` and `list_neg_only_imports_shows_no_definitions`:
// this is the category-boundary regression-guard that constructors are
// classified as Types (not Fns).
// (carry: legacy/e2e.rs::e2e_s3_3_list_neg_ctors_not_in_fns)
#[test]
fn list_neg_no_fns_category_when_only_types() {
    let out = repl("(deftype Color Red Green Blue)
/list
");
    assert!(
        !out.stdout.contains("Fns:"),
        "/list MUST NOT render 'Fns:' header when only deftype defined; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.1 (and spec/appendix-a-builtins.md §A.5) —
// `/doc <builtin>` on a primitive MUST mention the primitive's name and
// MUST NOT surface "unknown". Distinct from `doc_no_docstring`/
// `doc_shows_docstring` (user-fn paths): builtin lookup is a separate
// resolution path.
// (carry: legacy/e2e.rs::e2e_s3_1_doc_builtin)
#[test]
fn doc_builtin_primitive_shows_name() {
    let out = repl_prims("/doc add-i64\n");
    assert!(
        out.stdout.contains("add-i64"),
        "/doc on builtin MUST mention the primitive name 'add-i64'; got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("unknown"),
        "/doc on builtin MUST NOT surface 'unknown'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.1 — neg: `/doc` with no argument MUST surface a
// usage hint.
// (carry: legacy/e2e.rs::e2e_s3_1_doc_neg_no_arg)
#[test]
fn doc_no_arg_shows_usage() {
    let out = repl("/doc\n");
    let s = &out.stdout;
    assert!(
        s.contains("usage") || s.contains("/doc"),
        "/doc with no arg MUST surface a usage hint; got:\n{}",
        s
    );
}

// spec: repl/spec.md §3.1 — `/source <name>` shows the original source
// text of the named definition.
// (carry: legacy/e2e.rs::e2e_s3_1_source_user_fn)
#[test]
fn source_user_fn_shows_original_text() {
    let out = repl_prims("(defn double [x] (add-i64 x x))
/source double
");
    let s = &out.stdout;
    assert!(
        s.contains("defn double") || s.contains("(defn double"),
        "/source MUST surface original source text containing 'defn double'; got:\n{}",
        s
    );
}

// spec: repl/spec.md §3.1 — `/sexp <name>` shows the parsed S-expression
// (not "unknown command") and references the definition name.
// (carry: legacy/e2e.rs::e2e_s3_1_sexp_user_fn)
#[test]
fn sexp_user_fn_shows_parsed_form() {
    let out = repl_prims("(defn double [x] (add-i64 x x))
/sexp double
");
    let s = &out.stdout;
    assert!(
        !s.contains("unknown command"),
        "/sexp MUST be a recognised command; got:\n{}",
        s
    );
    assert!(
        s.contains("double") || s.contains("defn"),
        "/sexp output MUST reference the definition; got:\n{}",
        s
    );
}

// spec: repl/spec.md §3.1 — `/ast <name>` shows AST structure (not
// "unknown command") and references the definition name.
// (carry: legacy/e2e.rs::e2e_s3_1_ast_user_fn)
#[test]
fn ast_user_fn_shows_ast_structure() {
    let out = repl_prims("(defn double [x] (add-i64 x x))
/ast double
");
    let s = &out.stdout;
    assert!(
        !s.contains("unknown command"),
        "/ast MUST be a recognised command; got:\n{}",
        s
    );
    assert!(
        s.contains("double") || s.contains("Defn") || s.contains("defn"),
        "/ast output MUST reference the AST/definition; got:\n{}",
        s
    );
}

// spec: repl/spec.md §3.1 — `/clif <name>` shows Cranelift IR (not
// "unknown command") and contains IR keywords (block / function / v).
// (carry: legacy/e2e.rs::e2e_s3_1_clif_user_fn)
#[test]
fn clif_user_fn_shows_cranelift_ir() {
    let out = repl_prims("(defn double [x] (add-i64 x x))
/clif double
");
    let s = &out.stdout;
    assert!(
        !s.contains("unknown command"),
        "/clif MUST be a recognised command; got:\n{}",
        s
    );
    assert!(
        s.contains("block") || s.contains("function") || s.contains("v"),
        "/clif output MUST contain Cranelift IR keywords; got:\n{}",
        s
    );
}

// spec: repl/spec.md §3.1 — `/disasm <name>` is a recognised command.
// Weak assertion preserved per chunk-3 audit: disasm output content is
// platform-conditional (varies by arch) so only the recognised-command
// check is portable across e2e environments.
// (carry: legacy/e2e.rs::e2e_s3_1_disasm_user_fn)
#[test]
fn disasm_user_fn_recognized_command() {
    let out = repl_prims("(defn double [x] (add-i64 x x))
/disasm double
");
    assert!(
        !out.stdout.contains("unknown command"),
        "/disasm MUST be a recognised command; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.1 — `/disasm <name>` MUST "Show disassembled native
// code" for a compiled function. This is the stronger sibling to the weak
// recognised-command guard above: it asserts /disasm actually emits the
// disassembly (the `; disasm for <name>` header from
// CompilerSession::handle_disasm + at least one capstone instruction line),
// and NOT the dead-path "no disassembly available" error.
//
// DEFECT (S86): /disasm is DEAD. handle_disasm reads intr.disasm from the
// introspection record, but that field is NEVER populated — native disasm is
// re-derived on demand via cranelisp_backend::produce_disasm, which has ZERO
// call sites in src/. So /disasm <name> returns
// "no disassembly available for '<name>'" for every name, even a freshly
// JIT-compiled fn. (Contrast: /clif works because intr.clif_ir IS captured.)
// resolver: /int. This test is failing-not-ignored per
// memory/feedback_failing_not_ignored.md; it flips green when /int wires
// produce_disasm into the /disasm handler.
#[test]
fn disasm_command_shows_native_code_for_compiled_fn() {
    // `sq` actually JIT-compiles, so native code (hence disassembly) exists.
    let out = repl_prims("(defn sq [x] (mul-i64 x x))
(sq 7)
/disasm sq
");
    let s = &out.stdout;
    assert!(
        !s.contains("no disassembly available"),
        "/disasm MUST NOT hit the dead 'no disassembly available' path for a \
         compiled fn; got:\n{}",
        s
    );
    assert!(
        s.contains("disasm for sq"),
        "/disasm output MUST contain the `; disasm for sq` header; got:\n{}",
        s
    );
    // produce_disasm emits one `0xADDR\tmnemonic\toperands` line per
    // instruction — a hex address prefix is the portable cross-arch marker
    // that real native code was disassembled.
    assert!(
        s.contains("0x"),
        "/disasm output MUST contain at least one disassembled instruction \
         line (hex address prefix); got:\n{}",
        s
    );
}

// spec: repl/spec.md §3.7 — bare `/mem` snapshot emits two lines:
// `; live: <bytes> bytes (<live-allocs> allocations)` and
// `; allocs: <allocs>  deallocs: <deallocs>`. Negative companion: the
// snapshot form MUST NOT emit a `; delta:` line.
// (carry: legacy/e2e.rs::mem_command_snapshot_emits_live_and_allocs)
#[test]
fn mem_snapshot_emits_live_and_allocs_neg_no_delta() {
    let out = repl("/mem\n");
    let has_live = out
        .stdout
        .lines()
        .any(|l| l.contains("; live:") && l.contains("bytes (") && l.contains("allocations)"));
    assert!(
        has_live,
        "/mem MUST emit '; live: N bytes (M allocations)' line per §3.7; got:\n{}",
        out.stdout
    );
    let has_allocs = out
        .stdout
        .lines()
        .any(|l| l.contains("; allocs:") && l.contains("deallocs:"));
    assert!(
        has_allocs,
        "/mem MUST emit '; allocs: N  deallocs: M' line per §3.7; got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("; delta:"),
        "bare /mem (no expr) MUST NOT emit a '; delta:' line; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.7 — `/mem <expr>` evaluates the expression, prints
// the formatted result, then emits one `; delta:` line carrying signed
// `bytes` and `live` deltas plus `allocs` / `deallocs` fields.
// (carry: legacy/e2e.rs::mem_command_delta_runs_expr_and_shows_signed_deltas)
#[test]
fn mem_with_expr_emits_signed_delta_line() {
    let out = repl(
        "(import [primitives [str-concat]])
/mem (str-concat \"hi \" \"world\")
",
    );
    assert!(
        out.stdout.contains(":primitives/String"),
        "/mem <expr> MUST print the formatted result first; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("\"hi world\""),
        "/mem <expr> MUST evaluate the expression; got:\n{}",
        out.stdout
    );
    let delta_line = out
        .stdout
        .lines()
        .find(|l| l.contains("; delta:"))
        .unwrap_or_else(|| {
            panic!(
                "/mem <expr> MUST emit a '; delta:' line per §3.7; got:\n{}",
                out.stdout
            )
        });
    for needle in &["allocs +", "deallocs +", "bytes ", "live "] {
        assert!(
            delta_line.contains(needle),
            "delta line missing '{needle}'; got:\n{delta_line}\nfull stdout:\n{}",
            out.stdout
        );
    }
    assert!(
        delta_line.contains("bytes +") || delta_line.contains("bytes -"),
        "'bytes' delta MUST carry a signed prefix per §3.7; got:\n{delta_line}"
    );
    assert!(
        delta_line.contains("live +")
            || delta_line.contains("live -")
            || delta_line.contains("live 0"),
        "'live' delta MUST be signed per §3.7; got:\n{delta_line}"
    );
}

// spec: repl/spec.md §3.7 — process-start counters are zero. Bare `/mem`
// before any user evaluation reports `; live: 0 bytes (0 allocations)`
// and `; allocs: 0  deallocs: 0`.
// (carry: legacy/e2e.rs::mem_command_baseline_counters_zero_at_start)
#[test]
fn mem_baseline_zero_at_process_start() {
    let out = repl("/mem\n");
    assert!(
        out.stdout.contains("; live: 0 bytes (0 allocations)"),
        "process-start '; live:' MUST be '0 bytes (0 allocations)' per §3.7; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("; allocs: 0  deallocs: 0"),
        "process-start '; allocs: 0  deallocs: 0' MUST hold per §3.7; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.1 + §3.7 — `/m` is the documented short alias
// for `/mem`. Both produce the same snapshot output.
// (carry: legacy/e2e.rs::mem_command_alias_m_works)
#[test]
fn mem_alias_m_equivalent_to_mem() {
    let out = repl("/m\n");
    assert!(
        out.stdout.contains("; live:") && out.stdout.contains("bytes ("),
        "/m alias MUST produce the same snapshot as /mem (live line); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("; allocs:") && out.stdout.contains("deallocs:"),
        "/m alias MUST emit '; allocs:' line; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forwards (chunk 2)
// =============================================================================

// spec: repl/spec.md §1.5 — product ADT value display format. A product
// constructor displays parenthesised, **without dot notation**:
// `:user/Point (Point 3 4)`. Distinct from
// `data_constructor_applied_dot_notation_display` which covers sum
// constructor display `(Option.Some 42)` (dot notation). The
// product-vs-sum display distinction is not isolated elsewhere.
// (carry: legacy/ring1.rs::repl_adt_product)
//
// LAYERED DEFECT (S77 W-Fix triage, /qa): this test failed FIRST on RT1
// (bare `:Int` in the deftype fields — spec/03-types.md §3.1 requires the type
// be imported or fully-qualified). The `(import [primitives [Int]])` fixture fix
// (added below) clears RT1, but the test then STILL FAILS on a genuine
// product-value DISPLAY defect: a single-constructor product whose ctor name
// matches the type name displays as `:user/Point Point` (ctor name only, fields
// dropped) instead of `(Point 3 4)` per repl/spec.md §1.5 line 309. Verified
// first-hand in a fresh tmpdir; the sum-ctor path `(Option.Some 42)` renders
// fields correctly, so the formatter CAN show fields — the single-ctor product
// path drops them. Failing-not-ignored; resolver = FIXME 0302 (/dev int —
// product single-ctor value formatter).
#[test]
fn data_constructor_product_no_dot_notation_display() {
    // spec/03-types.md §3.1: bare `:Int` MUST be imported (RT1 fixture fix).
    let out = repl(
        "(import [primitives [Int]])\n\
         (deftype Point [:Int x :Int y])\n\
         (Point 3 4)\n",
    );
    assert!(
        out.stdout.contains("(Point 3 4)"),
        "product ctor MUST display as `(Point 3 4)` per §1.5; got:\n{}",
        out.stdout
    );
    // Negative: must NOT use dot notation `Point.Point` for the product
    // constructor — that shape is reserved for sum-type constructor
    // display (e.g., `Option.Some`).
    assert!(
        !out.stdout.contains("Point.Point"),
        "product ctor MUST NOT use dot notation; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.2, §1.5 — closure-as-value MUST display with the
// `<closure>` token in the value position (the `<closure>` shape appears in
// both the §1.2 value-line and the §1.5 Closure row). Only the negative companion
// `defn_display_neg_not_closure` exists (asserting top-level defns do
// NOT show "closure"); the positive `<closure>` formatter assertion was
// uncovered. The closure produced by `(make-adder 5)` returns a fn value,
// which is the canonical positive `<closure>` shape.
// (carry: legacy/ring1.rs::repl_closure_display)
#[test]
fn closure_value_display_shows_closure_token() {
    let out = repl_prims(
        "(defn make-adder [n] (fn [x] (add-i64 n x)))\n\
         (make-adder 5)\n",
    );
    assert!(
        out.stdout.contains("<closure>"),
        "closure value MUST display with `<closure>` token per §1.2; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forwards (chunk 4)
// =============================================================================

// spec: repl/spec.md §1.5 — Vec value display MUST render the element
// content (not just the type prefix). `vec_literal_int` asserts only
// the `:primitives/Vec` type prefix; this carry asserts that the actual
// element-content rendering is present in the displayed value, matching
// either a comma-separated `[1, 2, 3]` or a space-separated `[1 2 3]`
// rendering. Distinct from `:primitives/Vec` type prefix coverage.
// (carry: legacy/ring1.rs::repl_vec_display)
#[test]
fn vec_value_display_shows_element_content() {
    let out = repl_prims("[1 2 3]\n");
    assert!(
        out.stdout.contains("[1 2 3]") || out.stdout.contains("[1, 2, 3]"),
        "Vec display MUST render element content per §1.5, got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Wave 5.6 ring2.rs GAP-COVER carry-forwards (chunk 3)
// =============================================================================

// spec: repl/spec.md §1.3 — constrained-fn display MUST use inline
// constraint notation `:(Fn [:Num a] a) user/double` for a 1-param
// constrained polymorphic defn. Distinct from `defn_display_polymorphic_id`
// which exercises the UNCONSTRAINED `(Fn [a] a)` form. The inline
// constraint syntax (`:Num a`) is unique to constrained fns and is not
// exercised by any prior carry-forward.
// Cross-ref: spec/03-types.md §3.4.1 — Constraint Syntax in Display.
// (carry: legacy/ring2.rs::repl_constrained_fn_shows_constraints)
#[test]
fn constrained_fn_display_shows_inline_num_constraint() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("(defn double [x] (+ x x))\n")
        .output();
    assert!(
        out.stdout.contains(":(Fn [:Num a] a) user/double"),
        "constrained fn display MUST use inline constraint notation per §1.3 + §3.4.1; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("; defn"),
        "constrained fn display MUST include '; defn' classification per §1.3; got:\n{}",
        out.stdout
    );
}

// spec: spec/03-types.md §3.4.1 — REGRESSION-GUARD: 2-param constrained-fn
// display MUST repeat the `:Num` prefix on every constrained var
// (`:(Fn [:Num a :Num a] a)`), NOT elided as `[:Num a a]` or `[:Num a :a]`.
// Per spec/03-types.md §3.4.1: "Multiple constraints on the same variable
// are listed consecutively before the variable name." The repeat-vs-elide
// distinction is a Sprint-N display regression risk.
// Cross-ref: repl/spec.md §1.3 — definition results.
// (carry: legacy/ring2.rs::repl_constrained_fn_two_params_shows_subsequent_colon_var)
#[test]
fn constrained_fn_display_repeats_num_on_each_param_neg_no_elision() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("(defn add [x y] (+ x y))\n")
        .output();
    assert!(
        out.stdout.contains(":(Fn [:Num a :Num a] a) user/add"),
        "constrained fn display MUST repeat ':Num' on every constrained \
         param per §3.4.1 (no elision to ':Num a a' or ':Num a :a'); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("; defn"),
        "constrained fn display MUST include '; defn' classification per §1.3; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.3 — impl form's display result MUST be exactly
// `impl user/Sizeable for user/MyType` (full-line equality, no extra
// ornament, no trailing classification, no leading prefix). The existing
// `spec_07_traits.rs::trait_multiple_impls` asserts the substring appears
// among multi-line output; this asserts that the impl form's own display
// result is exactly the canonical line.
// (carry: legacy/ring2.rs::repl_impl_display_shows_trait_for_type)
#[test]
fn impl_form_display_result_is_exactly_impl_trait_for_type() {
    // spec/03-types.md §3.1: bare type refs (`Int`) MUST be imported or
    // fully-qualified — import the `Int` type so the trait return-type and
    // deftype field annotations resolve (RT1 fixture fix, S77 W-Fix).
    let out = repl(
        "(import [primitives [Int]])\n\
         (deftrait (Sizeable a) (size [a] Int))\n\
         (deftype MyType [:Int val])\n\
         (impl Sizeable MyType (defn size [self] 42))\n",
    );
    assert!(
        out.stdout.contains("impl user/Sizeable for user/MyType"),
        "impl form display result MUST be 'impl user/Sizeable for user/MyType' per §1.3; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Sprint 64 Wave 6 batch 5 — bare-primitive value-path Slice 1 carry-forwards
// =============================================================================
//
// Carry-forward from `tests/legacy/sprint61_bare_primitive.rs` per Wave 6
// batch 5 audit. Five tests guard the Sprint 61 Slice 1 fix in
// `src/session_v4.rs::resolve_entry_for_display` +
// `check_bare_symbol_introspection`: the fix aligns the bare-value path
// (typing `add-i64` at the prompt) with the introspection path (`/sig
// add-i64`) and the call path (`(add-i64 2 3)`) so that a re-exported
// primitive resolves through `user → prelude → primitives` to its
// terminal `Def` and produces a spec-conforming introspection card.
//
// Sibling cluster: the existing `bare_primitive_type_int_displays_type_info`
// test above covers bare primitive **type** lookup; these five cover bare
// primitive **fn** lookup (different resolution path through the symbol
// table).
//
// REGRESSION-GUARD: Sprint 61 Slice 1 — bare-primitive value-path fix.
// =============================================================================

// spec: repl/spec.md §1.1 — universal `:Type name ; classification - doc`
//       output format
// (carry: legacy/sprint61_bare_primitive.rs::bare_primitive_add_i64_at_prompt_displays_type_and_fqn)
#[test]
fn bare_primitive_add_i64_at_prompt_displays_type_and_fqn() {
    let out = repl_prims("add-i64\n");
    let display = &out.stdout;
    assert!(
        display.contains("primitives/add-i64"),
        "bare `add-i64` MUST resolve to the primitives-qualified name per \
         spec/08-modules.md §8.9 re-export provenance; got:\n{display}"
    );
    assert!(
        display.contains("(Fn ["),
        "bare `add-i64` MUST display a function type prefix `:(Fn [...] ...)`; \
         got:\n{display}"
    );
    assert!(
        display.contains("; primitive"),
        "classification MUST be `; primitive` per repl/spec.md §1.1 + §4.1.1 \
         for a primitive Def; got:\n{display}"
    );
    assert!(
        display.contains("; primitive - "),
        "output MUST carry `; primitive - <docstring>` per the universal \
         format (repl/spec.md §1.1); got:\n{display}"
    );
}

// spec: repl/spec.md §4.1.7 — negative: a primitive lookup MUST NOT be empty
// and MUST NOT be misclassified. Looking up the primitive `add-i64` must
// produce a populated card — it must NOT surface "undefined", must NOT be a
// blank line, and must NOT classify the builtin as a user `defn` (the
// classification distinguishes builtins from user-defined functions per the
// §4.1.7 "Classification `primitive` (distinguishes builtins from user-defined
// `defn`)" requirement). Negative companion to
// `bare_primitive_add_i64_at_prompt_displays_type_and_fqn`.
#[test]
fn bare_primitive_lookup_not_empty_neg() {
    let out = repl_prims("add-i64\n");
    let display = &out.stdout;
    assert!(
        !display.contains("undefined"),
        "a primitive lookup MUST NOT report `undefined` — the primitive is \
         resolvable per repl/spec.md §4.1.7; got:\n{display}"
    );
    assert!(
        display.contains(":(Fn ["),
        "a primitive lookup MUST NOT be empty — it MUST emit a populated \
         `:Type name` card per repl/spec.md §4.1.7; got:\n{display}"
    );
    assert!(
        !display.contains("primitives/add-i64 ; defn"),
        "a primitive MUST NOT be classified as a user `defn` — classification \
         `primitive` distinguishes builtins per repl/spec.md §4.1.7; \
         got:\n{display}"
    );
}

// spec: design/int/bare-primitive-value-path.md §2 (three paths) + §5
//       (expected output) — anti-divergence guard between bare-value /
//       introspection / call paths. Cross-ref design/int/dual-path-persistence-collapse.md
//       (dual-path anti-pattern).
// (carry: legacy/sprint61_bare_primitive.rs::bare_primitive_parallel_paths_converge_on_same_attribution)
#[test]
fn bare_primitive_parallel_paths_converge_on_same_attribution() {
    // All three paths driven through one REPL invocation so they share
    // session state. /sig prints a sig card; bare add-i64 prints a value
    // card; (add-i64 2 3) prints "5" (or `:primitives/Int 5`).
    let out = repl_prims("/sig add-i64\nadd-i64\n(add-i64 2 3)\n");
    let combined = &out.stdout;

    // Path A — introspection: /sig must attribute to primitives/add-i64.
    // Path B — bare value: same attribution.
    assert!(
        combined.contains("primitives/add-i64"),
        "Both /sig add-i64 and bare add-i64 MUST attribute to \
         primitives/add-i64 per spec/08-modules.md §8.9; got:\n{combined}"
    );
    // Bare display must additionally carry the qualified function type.
    assert!(
        combined.contains("(Fn ["),
        "bare `add-i64` MUST carry the `:(Fn [...] ...)` type prefix; \
         got:\n{combined}"
    );
    // Path C — call evaluates to 5.
    assert!(
        combined.contains("5"),
        "(add-i64 2 3) MUST evaluate to 5 on the call path; got:\n{combined}"
    );
}

// spec: spec/08-modules.md §8.9 — re-export provenance generalises across
//       the primitives surface (≥ 5 primitives covered)
// (carry: legacy/sprint61_bare_primitive.rs::bare_primitive_surface_resolves_identically_across_five_plus_symbols)
#[test]
fn bare_primitive_surface_resolves_identically_across_five_plus_symbols() {
    // Pipe one bare reference per primitive in a single REPL session.
    let input = "add-i64\neq-i64\nmul-i64\nsub-i64\nnot\nstr-concat\n";
    let out = repl_prims(input);
    let combined = &out.stdout;

    for name in ["add-i64", "eq-i64", "mul-i64", "sub-i64", "not", "str-concat"] {
        let fqn = format!("primitives/{name}");
        assert!(
            combined.contains(&fqn),
            "bare `{name}` MUST resolve to `{fqn}` per \
             spec/08-modules.md §8.9; got:\n{combined}"
        );
    }
    assert!(
        !combined.contains("undefined variable"),
        "no bare primitive reference MAY surface an `undefined variable` \
         error (bare-primitive-value-path.md §1 regression); got:\n{combined}"
    );
    // Classification must be `; primitive` somewhere in the output.
    assert!(
        combined.contains("; primitive"),
        "bare primitive references MUST classify as `; primitive` per \
         repl/spec.md §4.1.1; got:\n{combined}"
    );
}

// spec: repl/spec.md §1.1 (negative complement) — unknown bare symbol
//       MUST NOT silently dispatch to a similarly-named primitive
// (carry: legacy/sprint61_bare_primitive.rs::bare_primitive_unknown_name_produces_undefined_error_neg)
//
// Passes in BOTH builds (arch ruling e3f7d57, §5.3/§7.4): under the default
// `--features agent` posture the agent is DORMANT (no provider), so the U1
// classifier's `Classify::Agent` route falls back to today's deterministic
// "undefined name" display — byte-identical to the feature-OFF build. The agent
// only intercepts a bare UNBOUND symbol when it is ACTIVE (a reachable provider);
// that complement is `bare_primitive_unknown_name_routes_to_agent` below (an
// ACTIVE stub). The Wave-2 `#[cfg(not(feature = "agent"))]` gate is removed: the
// dormant fall-through restores this default-build guarantee in the agent build.
#[test]
fn bare_primitive_unknown_name_produces_undefined_error_neg() {
    let out = repl_prims("unknown-primitive-name-zzzz\n");
    let combined = format!("{}\n{}", out.stdout, out.stderr);

    // Must surface an error.
    assert!(
        combined.contains("undefined") || combined.contains("not found"),
        "unknown bare symbol MUST produce an `undefined variable` or \
         `not found` error per spec §1.1 negative complement; \
         got:\n{combined}"
    );
    // Must NOT silently resolve to a nearby symbol — guards against an
    // over-broad Slice 1 fix.
    assert!(
        !combined.contains("primitives/add-i64"),
        "unknown bare symbol MUST NOT silently dispatch to `add-i64` \
         (guards against over-broad Slice 1 fix); got:\n{combined}"
    );
    // Bare symbol must literally appear in the error to be actionable.
    assert!(
        combined.contains("unknown-primitive-name-zzzz"),
        "error message MUST name the unknown symbol to be actionable; \
         got:\n{combined}"
    );
}

// spec: repl/spec.md §17.1 — under `--features agent` with an ACTIVE provider the
//       U1 resolution-aware dispatch classifier routes a bare UNBOUND symbol to
//       the agent (not the §4 "undefined name" display). Per arch ruling e3f7d57
//       (§5.3/§7.4) the route fires only when the agent is ACTIVE — so this drives
//       an ACTIVE stub (`CRANELISP_AGENT_PROVIDER=stub`). The unknown symbol
//       reaches `agent_turn`, which renders the stub's framed prose (`▌`). The
//       load-bearing assertion is the SAME negative guard the default build makes:
//       the unknown symbol MUST NOT silently dispatch to a nearby primitive
//       (`add-i64`). This is the active-agent complement of
//       `bare_primitive_unknown_name_produces_undefined_error_neg` (the dormant
//       fall-through, today's display).
#[cfg(feature = "agent")]
#[test]
fn bare_primitive_unknown_name_routes_to_agent() {
    use helpers::e2e::PreludeVariant;
    let cl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .cli_flag("--agent");
    let script_path = cl.tmpdir_path().join("agent_script.txt");
    std::fs::write(&script_path, "done: that is not a defined symbol\n").unwrap();
    let out = cl
        .env("CRANELISP_AGENT_PROVIDER", "stub")
        .env("CRANELISP_AGENT_STUB_SCRIPT", script_path.to_str().unwrap())
        .stdin("unknown-primitive-name-zzzz\n")
        .output();
    let combined = format!("{}\n{}", out.stdout, out.stderr);

    // The bare unbound symbol reaches the ACTIVE agent (U1) — the agent prose
    // frame (`▌`) is the observable signal the line was diverted, not described.
    assert!(
        combined.contains('\u{258c}'),
        "under --features agent + an ACTIVE provider a bare UNBOUND symbol MUST \
         route to the agent (the `\u{258c}` prose frame) per repl/spec.md §17.1 \
         + arch ruling e3f7d57; got:\n{combined}"
    );
    // The negative guard is preserved across both builds: the unknown symbol
    // MUST NOT silently dispatch to a nearby primitive (over-broad-fix guard).
    assert!(
        !combined.contains("primitives/add-i64"),
        "unknown bare symbol MUST NOT silently dispatch to `add-i64` \
         (guards against over-broad Slice 1 fix); got:\n{combined}"
    );
}

// spec: design/int/bare-primitive-value-path.md §"Post-implementation note"
//       + spec/08-modules.md §8.9 — re-export chain transitivity (the
//       resolver MUST walk user → prelude → primitives and land on the
//       terminal Def)
// (carry: legacy/sprint61_bare_primitive.rs::bare_primitive_two_hop_reexport_chain_lands_on_terminal_def)
#[test]
fn bare_primitive_two_hop_reexport_chain_lands_on_terminal_def() {
    // Decoupled from real stdlib (was:
    // `use_workspace_stdlib_for_stdlib_conformance_only`, which broke when the
    // real stdlib momentarily stopped compiling — FIXME 0312/0314, since CLOSED
    // in S78 Wave 6 via the `fn.option`/`fn.result`/`collections.pair`
    // re-export of the canonical `primitives` ADTs). The chain this test pins is
    // a LANGUAGE rule, not a stdlib fact: a prelude that re-exports primitives
    // (`(export [primitives [*]])`) creates the user → prelude → primitives
    // hop, and a bare reference MUST resolve to the terminal `primitives` Def.
    //
    // `PreludeVariant::PrimitivesOnly` IS exactly that re-export prelude
    // (`tests/fixtures/preludes/primitives-only.cl` = `(export [primitives
    // [*]])`), dropped as `prelude.cl` in the per-test cwd (shadowing stdlib
    // §8.8.2). So the bare `add-i64` walks user → prelude → primitives with a
    // test-owned, spec-clean prelude and never loads real stdlib.
    let out = repl_prims("add-i64\n");
    let display = &out.stdout;

    // The resolver MUST walk user → prelude → primitives and produce the
    // terminal Def's qualified name.
    assert!(
        display.contains("primitives/add-i64"),
        "two-hop re-export chain (user → prelude → primitives) MUST resolve \
         to `primitives/add-i64` per spec/08-modules.md §8.9 + \
         bare-primitive-value-path.md post-impl note; got:\n{display}"
    );
    // Full signature must be present; threading through `resolved_module`
    // means the chain lands on the terminal Def.
    assert!(
        display.contains("(Fn ["),
        "two-hop resolver MUST surface the function signature, not just the \
         name (would indicate truncation at intermediate Reexport); \
         got:\n{display}"
    );
    // Negative face: MUST NOT be attributed to user/ or prelude/.
    assert!(
        !display.contains("user/add-i64"),
        "bare `add-i64` MUST NOT be attributed to the `user` module \
         (spec §8.9 — re-export provenance is the original defining module); \
         got:\n{display}"
    );
    // Display types MUST be qualified per repl/spec.md §1.1.
    assert!(
        display.contains("primitives/Int"),
        "display types MUST be qualified (`primitives/Int`), not bare `Int`, \
         per repl/spec.md §1.1; got:\n{display}"
    );
}

// =============================================================================
// Sprint 64 Wave 6 batch 5 — Defect 3 docstring separator
// =============================================================================

// spec: repl/spec.md §1.1 — universal output format mandates a DASH
//       separator between the classification word and the docstring's
//       first line, NOT a semicolon
// REGRESSION-GUARD: Sprint 58 Wave 6 Defect 3 — `append_docstring_comment`
//       used to emit `; defn ; <doc>` (semicolon separator); spec mandates
//       `; defn - <doc>`. /int fix landed; this guard prevents regression.
// (carry: legacy/wave6_demo_repros.rs::display_defn_with_docstring_uses_dash_separator)
#[test]
fn display_defn_with_docstring_uses_dash_separator() {
    let out = repl_prims(
        "(defn double \"Multiply by 2\" [:Int x] (add-i64 x x))\ndouble\n",
    );
    let combined = format!("{}\n{}", out.stdout, out.stderr);
    assert!(
        combined.contains("; defn - Multiply by 2"),
        "REPL output MUST use DASH separator per repl/spec.md §1.1 \
         (`; defn - Multiply by 2`); semicolon-separator form \
         (`; defn ; Multiply by 2`) is the pre-fix shape that MUST NOT \
         regress. Combined:\n{combined}"
    );
}

// =============================================================================
// FIXME 0108 — display.rs relocation backend → int (Sprint 66 Phase 5 Stage 1)
// =============================================================================
//
// Authored failing-not-ignored at Phase-5 Stage-1 open per /qa Phase-5
// obligation. FIXME 0108 relocates `crates/cranelisp-backend/src/display.rs`
// into the int binary. The relocation is pure source-move; output bytes for
// /sig, /info, /type, REPL eval-result formatting MUST be byte-identical
// pre/post relocation. The negative test additionally asserts (via
// `cargo public-api` baseline) that backend's public surface no longer
// exposes `display::*` symbols.
//
// Per `tests/plan/implementation-slice-s66.md §5.7`.

// spec: repl/spec.md §1.1 — universal output format `:Type value` is
// spec-pinned; relocation MUST NOT shift output bytes.
// FIXME(/dev int FIXME 0108) — fails if the relocation shifts output bytes.
#[test]
fn display_format_eval_result_after_relocation_unchanged() {
    let out = repl_prims(
        "(defn id [x] x)\n\
         /sig id\n\
         /info id\n\
         (id 7)\n",
    );
    let combined = format!("{}\n{}", out.stdout, out.stderr);
    assert!(
        combined.contains(":primitives/Int 7"),
        "REPL eval result MUST format as `:primitives/Int 7` per repl/spec.md §1.1; \
         display.rs relocation must not shift output bytes. Combined:\n{combined}"
    );
    assert!(
        combined.contains("Fn") && combined.contains("id"),
        "/sig id MUST surface Fn type for id per repl/spec.md §3; \
         display.rs relocation must not shift output bytes. Combined:\n{combined}"
    );
    assert!(
        combined.contains("; defn"),
        "/info MUST surface `; defn` classification per repl/spec.md §3; \
         display.rs relocation must not shift output bytes. Combined:\n{combined}"
    );
}

// spec: structural — FIXME 0108 closure: backend's public surface MUST NOT
// list `display::*` post-relocation. Negative test verified via the
// committed `cargo public-api` baseline.
// FIXME(/dev int FIXME 0108 + /dev backend baseline regenerated post-relocation).
#[test]
fn public_api_check_backend_display_absent_neg() {
    use std::path::PathBuf;
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let backend_baseline = root.join("crates/cranelisp-backend/public-api.txt");
    assert!(
        backend_baseline.exists(),
        "backend public-api baseline must exist per /qa slice §1.1; path: {}",
        backend_baseline.display()
    );
    let s = std::fs::read_to_string(&backend_baseline)
        .unwrap_or_else(|e| panic!("read {}: {e}", backend_baseline.display()));
    // After FIXME 0108 lands, no `display::` path should appear in
    // backend's public API surface. Conservative match: a public-surface
    // line containing the `display` module name signals the relocation
    // hasn't completed.
    let has_display_pub = s.lines().any(|line| {
        let t = line.trim();
        t.contains("::display::") || t.contains("pub mod display")
            || t.contains("pub use cranelisp_backend::display")
    });
    assert!(
        !has_display_pub,
        "backend public surface MUST NOT expose `display::*` post-FIXME-0108; \
         baseline at {}:\n{}",
        backend_baseline.display(),
        s
    );
}

// =============================================================================
// §4.1.5 / §3.6 — Special-form self-documentation gaps (FIXME 0338, S81 close)
//
// FAILING-NOT-IGNORED repros. Two self-documenting-REPL gaps for special forms:
//   (1) bare `trace` at the prompt MUST carry the `:Type` prefix like every
//       other special form (e.g. bare `if` → `:(Fn [primitives/Bool a a] a) if
//       ; special form - …`). Today bare `trace` drops the `:Type` prefix.
//   (2) `/info <special-form>` and `/sig <special-form>` MUST resolve, not
//       return `unknown symbol` — for ALL special forms (`trace`, `if`,
//       `match`, …). Today every special form is unreachable via /info /sig.
//
// Owning skill: /int (REPL display + introspection dispatch). Flips green
// when the fix lands.
// =============================================================================

// spec: repl/spec.md §4.1.5 — bare special form `trace` MUST display the
//   type-annotated form (`:Type ... ; special form - ...`), consistent with
//   bare `if`. FIXME(/int 0338).
#[test]
fn bare_trace_special_form_carries_type_prefix() {
    let out = repl("trace\n");
    // CORRECT: bare `trace` shows the `:(Fn [a] ...Trace...) trace` form like
    // other special forms. Today it prints `trace ; special form - ...` with
    // NO `:Type` prefix.
    out.assert_stdout_contains_all(&[":(Fn", "trace", "special form"]);
}

// spec: repl/spec.md §4.1.5 — control: bare `if` already carries the `:Type`
//   prefix; this pins the expected shape that `trace` must match. Today this
//   PASSES (it is the working reference); kept alongside the `trace` repro so
//   the pair documents the inconsistency. FIXME(/int 0338).
#[test]
fn bare_if_special_form_carries_type_prefix_control() {
    repl("if\n").assert_stdout_contains_all(&[
        ":(Fn [primitives/Bool a a] a) if",
        "special form",
    ]);
}

// spec: repl/spec.md §3.6 — `/info trace` MUST resolve and display details,
//   not return `unknown symbol`. FIXME(/int 0338).
#[test]
fn info_resolves_trace_special_form() {
    let out = repl("/info trace\n");
    // CORRECT: /info names `trace` and classifies it as a special form. Today
    // it returns `unknown symbol 'trace'`.
    out.assert_stdout_contains("trace")
        .assert_stdout_does_not_contain("unknown symbol");
}

// spec: repl/spec.md §3.6 — `/info if` MUST resolve a representative second
//   special form, not return `unknown symbol`. FIXME(/int 0338).
#[test]
fn info_resolves_if_special_form() {
    let out = repl("/info if\n");
    out.assert_stdout_contains("if")
        .assert_stdout_does_not_contain("unknown symbol");
}

// spec: repl/spec.md §3.1 — `/sig trace` MUST resolve the special form's
//   signature, not return `unknown symbol`. FIXME(/int 0338).
#[test]
fn sig_resolves_trace_special_form() {
    let out = repl("/sig trace\n");
    out.assert_stdout_contains("trace")
        .assert_stdout_does_not_contain("unknown symbol");
}

// =============================================================================
// S82 harvest from tests/legacy/repl_experience.rs (FIXME 0124) — Ring-1/Ring-2A
// display GAPs re-expressed as e2e REPL-capture.
//
// The legacy file asserted these via the deleted `ReplSession::eval()` Rust API
// (`result.ty()` / `result.value()` / `format_result(value, &Type)` /
// `repl_eval_display`). The active suite already covered the bulk (int/float/
// bool/string display, defn/deftype/closure display, type-var normalization,
// trait operators, dot-notation ctor display, error recovery, recursion,
// lifecycle). The tests below are the genuine, user-observable display gaps that
// had NO active e2e equivalent. Each re-expresses the legacy assertion as a
// single REPL capture asserting the `:Type value` display (which captures BOTH
// the inferred type AND the value in one shape).
// =============================================================================

// spec: repl/spec.md §1.5.1 — Bare Polymorphic Values — Type Display via
// Introspection. A bare empty `[]` (type `∀a. (Vec a)`) entered at the REPL
// DISPLAYS the `(primitives/Vec a)` type prefix + `[]` value, not a raw pointer.
// This is a type-display disposition (spec §3.11.2), NOT an ambiguity error.
// SPEC-CORRECT under the §3.11 ruling (FIXME 0378) — MUST stay GREEN; the
// /dev relay keeps it green via introspection after the slot-less reshape.
// (harvest: legacy/repl_experience.rs::display_vec_empty)
#[test]
fn display_empty_vec_value() {
    let out = repl("[]\n");
    assert!(
        out.stdout.contains("primitives/Vec") && out.stdout.contains("[]"),
        "empty Vec MUST display the Vec type prefix and `[]` value per §1.5; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.5 — a product ADT value with MULTIPLE fields displays
// every field recursively (`(Named "alice" 42)`), not a raw pointer. Distinct
// from the single-field product carry `data_constructor_product_no_dot_notation_display`.
// (harvest: legacy/repl_experience.rs::display_product_adt_string_field)
#[test]
fn display_product_adt_multi_field_value() {
    let out = repl(
        "(import [primitives [Int String]])\n\
         (deftype Named [:String name :Int value])\n\
         (Named \"alice\" 42)\n",
    );
    assert!(
        out.stdout.contains("(Named \"alice\" 42)"),
        "multi-field product ADT MUST render every field per §1.5; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":user/Named"),
        "multi-field product ADT MUST carry the `:user/Named` type tag; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.5 — a polymorphic ADT value with MULTIPLE fields of
// distinct types displays both fields AND the fully-instantiated type
// `(user/Pair primitives/Int primitives/String)`. Distinct from the
// single-type-arg `(Option.Some 42)` carry.
// (harvest: legacy/repl_experience.rs::u1_9_polymorphic_adt_multi_field_display)
#[test]
fn display_polymorphic_adt_multi_field_value() {
    let out = repl(
        "(import [primitives [Int String]])\n\
         (deftype (Pair a b) (MkPair [:a fst :b snd]))\n\
         (MkPair 42 \"hi\")\n",
    );
    assert!(
        out.stdout.contains("42") && out.stdout.contains("\"hi\""),
        "multi-field polymorphic ADT MUST render both fields per §1.5; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("(user/Pair primitives/Int primitives/String)"),
        "type MUST be the fully-instantiated `(user/Pair primitives/Int \
         primitives/String)`; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.5 — a NESTED ADT field displays recursively: the inner
// constructor and its payload both appear (`(Some (Some 42))` shows `Some`
// twice and `42`), not a raw pointer for the inner value.
// (harvest: legacy/repl_experience.rs::display_adt_nested_adt_field)
#[test]
fn display_nested_adt_field_value() {
    let out = repl(
        "(deftype (Option a) None (Some [:a val]))\n\
         (Some (Some 42))\n",
    );
    assert!(
        out.stdout.matches("Some").count() >= 2 && out.stdout.contains("42"),
        "nested ADT field MUST display the inner constructor and payload \
         recursively per §1.5; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.3 — a polymorphic fn that returns a parameterized ADT
// displays the type-var-preserving signature `(Fn [a] (user/Option a))`, not a
// monomorphized or `t0`-leaking shape.
// (harvest: legacy/repl_experience.rs::ring1_defn_polymorphic_adt_return_type)
#[test]
fn display_defn_polymorphic_adt_return_type() {
    let out = repl(
        "(deftype (Option a) None (Some [:a val]))\n\
         (defn wrap [x] (Some x))\n",
    );
    assert!(
        out.stdout.contains(":(Fn [a] (user/Option a)) user/wrap"),
        "polymorphic fn returning a parameterized ADT MUST display \
         `:(Fn [a] (user/Option a)) user/wrap` per §1.3; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.1 — a bare lookup of an OVERLOADED fn displays ALL
// variant signatures (one line per clause), not just the first. This was a
// known /int gap in the legacy era (the legacy test was failing-not-ignored);
// the current implementation surfaces both variants.
// (harvest: legacy/repl_experience.rs::display_overloaded_fn_shows_all_variants)
#[test]
fn display_overloaded_fn_shows_all_variants() {
    let out = repl_prims(
        "(defn pick ([:Int x] x) ([:Int x :Int y] (add-i64 x y)))\n\
         pick\n",
    );
    let has_1_arg = out.stdout.contains("[primitives/Int]");
    let has_2_arg = out.stdout.contains("[primitives/Int primitives/Int]");
    assert!(
        has_1_arg && has_2_arg,
        "overloaded fn MUST show BOTH variant signatures on bare lookup per \
         §4.1.1; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.3 — bare lookup of a type with trait impls lists the
// implementing trait names under an `; impl:` section. Distinct from
// `bare_type_lookup_includes_match_section` (which covers the `; match:` ctors
// section only).
// (harvest: legacy/repl_experience.rs::display_type_shows_related_trait_impls)
#[test]
fn display_type_lookup_shows_impl_section() {
    let out = repl(
        "(deftype Color Red Green Blue)\n\
         (deftrait Shade (brightness [self] Int))\n\
         (impl Shade Color (defn brightness [c] 1))\n\
         Color\n",
    );
    assert!(
        out.stdout.contains("; impl:") && out.stdout.contains("Shade"),
        "type lookup MUST list implementing traits under `; impl:` per §4.1.3; \
         got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.3 (negative) — a type with NO trait impls MUST NOT
// render an `; impl:` section (empty categories are omitted).
// (harvest: legacy/repl_experience.rs::display_type_no_impls_omits_impl_section)
#[test]
fn display_type_lookup_neg_no_impl_section_when_none() {
    let out = repl("(deftype Lonely Alone)\nLonely\n");
    assert!(
        !out.stdout.contains("; impl:"),
        "type with no impls MUST NOT render an `; impl:` section per §4.1.3; \
         got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.5 — a non-empty user-defined List value displays its
// elements (the generic ADT recursive `(List.Cons h t)` form), with the empty
// tail showing `List.Nil` — not a raw heap pointer. Tests define List inline
// (no stdlib dependency per tests/CLAUDE.md isolation).
// (harvest: legacy/repl_experience.rs::display_list_non_empty_shows_elements + display_list_nil)
#[test]
fn display_user_list_value_shows_elements_and_nil() {
    let out = repl_prims(
        "(deftype (List a) Nil (Cons [:a h :(List a) t]))\n\
         (Cons 1 (Cons 2 (Cons 3 Nil)))\n\
         Nil\n",
    );
    for elem in ["1", "2", "3"] {
        assert!(
            out.stdout.contains(elem),
            "list display MUST contain element {elem} per §1.5; got:\n{}",
            out.stdout
        );
    }
    assert!(
        out.stdout.contains("List.Nil"),
        "empty list MUST display as `List.Nil` per §1.5; got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("<closure>"),
        "list value MUST NOT display as `<closure>` per §1.5; got:\n{}",
        out.stdout
    );
    // STRENGTHENED (S101 6b guard batch, FIXME 0493): the presence-only
    // assertions above stayed green over garbled output — the renderer emits
    // the nested instance's TYPE ARGUMENT plus a premature `)` instead of
    // recursing (`(List.Cons 1 primitives/Int) (List.Cons 2 primitives/Int)
    // (List.Cons 3 List.Nil)))` observed on HEAD). §1.5's List row pins the
    // generic ADT recursive form as normative, so assert the exact nested
    // string. RED on HEAD — deliberate (the strengthening IS the guard);
    // resolver TBD (/int display seam or /backend show path), FIXME 0493.
    assert!(
        out.stdout
            .contains("(List.Cons 1 (List.Cons 2 (List.Cons 3 List.Nil)))"),
        "nested generic ADT value MUST render in the §1.5 recursive form \
         `(List.Cons 1 (List.Cons 2 (List.Cons 3 List.Nil)))` (FIXME 0493); got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("(List.Cons 1 primitives/Int)"),
        "list value display MUST NOT interleave type tokens into the value \
         form (FIXME 0493); got:\n{}",
        out.stdout
    );
}

// =============================================================================
// FIXME 0493 (S101 Phase 6b, /repl) — nested parameterized-ADT payload display
// is garbled: instead of recursing into a nested PARAMETERIZED constructor,
// the renderer emits the nested instance's type argument followed by a
// premature `)`, leaving the line with unbalanced parens. Concrete payloads
// (and non-generic ADT payloads inside a generic wrapper) render correctly —
// the single-level control below pins that boundary. Resolver TBD (/int
// display seam or /backend). Ledger: tests/plan/ledger.md §"Sprint 101 Phase
// 6a/6b defect set".
// =============================================================================

// spec: repl/spec.md §1.5 — ADT fields MUST be recursively formatted; a
// parameterized ADT instance nested as a field renders as the nested
// constructor form. Expected: `:(user/Wrap (user/Wrap primitives/Int))
// (Wrap.MkWrap (Wrap.MkWrap 7))`. RED on HEAD (FIXME 0493): renders
// `(Wrap.MkWrap primitives/Int) (Wrap.MkWrap 7))` — type token + unbalanced
// parens.
#[test]
fn display_nested_parameterized_adt_value_recursive_form() {
    let out = repl("(deftype (Wrap a) (MkWrap [:a v]))\n(MkWrap (MkWrap 7))\n");
    assert!(
        out.stdout.contains("(Wrap.MkWrap (Wrap.MkWrap 7))"),
        "nested parameterized ADT payload MUST render recursively as \
         `(Wrap.MkWrap (Wrap.MkWrap 7))` per §1.5 (FIXME 0493); got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("(Wrap.MkWrap primitives/Int)"),
        "value display MUST NOT emit the nested instance's type argument in \
         place of the nested constructor (FIXME 0493); got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.5 — CONTROL (GREEN on HEAD): a single-level
// parameterized ADT with a primitive payload renders correctly
// (`(Wrap.MkWrap 7)`), pinning the 0493 boundary to PARAMETERIZED payloads.
#[test]
fn display_single_level_parameterized_adt_value_control() {
    repl("(deftype (Wrap a) (MkWrap [:a v]))\n(MkWrap 7)\n")
        .assert_stdout_contains(":(user/Wrap primitives/Int) (Wrap.MkWrap 7)");
}

// =============================================================================
// FIXME 0486 (S101 Phase 6a, /docs) — evaluating a defined symbol BARE at the
// prompt corrupts that symbol's in-session introspection source: every
// subsequent `/info <name>` and `/source <name>` renders the definition
// source as the bare lookup text instead of the `(defn …)` form. The trigger
// is the bare-lookup turn only (a call form does not corrupt; the no-lookup
// control below is GREEN); the backing file stays correct and a restart
// self-heals — the corruption is live-session introspection metadata only
// (the lookup form appears to be recorded as the symbol's latest source).
// Likely owner /int (bare-lookup evaluation path recording); the
// `info_definition_source` display seam renders what introspection hands it.
// Ledger: tests/plan/ledger.md §"Sprint 101 Phase 6a/6b defect set".
// =============================================================================

// spec: repl/spec.md §3.6 — `/info` MUST display the definition source; §3.1
// — `/source` shows the original source text. A prior bare lookup of the
// symbol MUST NOT change what they display. RED on HEAD (FIXME 0486): after
// the bare `solo` turn, both render the source line as `solo`.
#[test]
fn bare_lookup_does_not_corrupt_info_and_source_definition_display() {
    let out = repl_prims(
        "(defn solo [x] (mul-i64 x 3))\n\
         solo\n\
         /info solo\n\
         /source solo\n",
    );
    let src_occurrences = out.stdout.matches("(defn solo [x] (mul-i64 x 3))").count();
    assert!(
        src_occurrences >= 2,
        "after a bare lookup, /info AND /source MUST still show the defn form \
         `(defn solo [x] (mul-i64 x 3))` (expected ≥2 occurrences, got {src_occurrences}) \
         — FIXME 0486; stdout:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.6 — CONTROL (GREEN on HEAD): without the bare-lookup
// turn, `/info` and `/source` both show the defn form. Pins the 0486 trigger
// boundary to the bare-lookup turn.
#[test]
fn info_and_source_show_defn_form_without_prior_bare_lookup_control() {
    let out = repl_prims(
        "(defn solo [x] (mul-i64 x 3))\n\
         /info solo\n\
         /source solo\n",
    );
    let src_occurrences = out.stdout.matches("(defn solo [x] (mul-i64 x 3))").count();
    assert!(
        src_occurrences >= 2,
        "control: /info + /source MUST show the defn form (expected ≥2 \
         occurrences, got {src_occurrences}); stdout:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.5 — a lazy/infinite user-defined Seq value displays
// without HANGING: the head element renders and the thunked tail shows as
// `<closure>` (the tail is NOT forced). The key invariant is termination.
// (harvest: legacy/repl_experience.rs::display_seq_infinite_does_not_hang)
#[test]
fn display_infinite_seq_value_does_not_hang() {
    let out = repl_prims(
        "(deftype (Seq a) SeqNil (SeqCons [:a h :(Fn [] (Seq a)) rest]))\n\
         (defn range-from [n] (SeqCons n (fn [] (range-from (add-i64 n 1)))))\n\
         (range-from 7)\n",
    );
    // Did not hang (the harness has a timeout); head element 7 is present and
    // the thunked tail is shown unforced as `<closure>`.
    assert!(
        out.stdout.contains("7"),
        "Seq display MUST show the head element without forcing the tail per \
         §1.5; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("<closure>"),
        "Seq thunked tail MUST display unforced as `<closure>` per §1.5; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.2 — Float infinity displays with an `inf` token (not a
// raw NaN-boxed integer). Produced via `(div-f64 1.0 0.0)`.
// (harvest: legacy/repl_experience.rs::display_float_infinity)
#[test]
fn display_float_infinity_value() {
    let out = repl_prims("(div-f64 1.0 0.0)\n");
    assert!(
        out.stdout.contains("inf"),
        "Float infinity MUST display an `inf` token per §1.2; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.2 — Float NaN displays with a `NaN` token. Produced via
// `(div-f64 0.0 0.0)`.
// (harvest: legacy/repl_experience.rs::display_float_nan)
#[test]
fn display_float_nan_value() {
    let out = repl_prims("(div-f64 0.0 0.0)\n");
    assert!(
        out.stdout.contains("NaN"),
        "Float NaN MUST display a `NaN` token per §1.2; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Pillar 1 — the `/syntax` cheat-sheet command (S90, tests/plan/s90-test-plan.md
// §P1). RED-FIRST: `/syntax` is unimplemented on HEAD (the REPL replies
// "unknown command '/syntax'"), so every row below fails until /dev 1d wires the
// `ReplCommand::Syntax` variant + dispatch + the `src/syntax/cheatsheet.txt`
// asset parser. `/syntax` is NOT feature-gated — it is a deterministic
// static-asset command usable on the DEFAULT (non-`agent`) build (§17.17.3), so
// these default-build rows live here (the deterministic-command home), NOT in
// the `--features agent` lane. The agent-pull row (P1.6) lives in `tests/agent.rs`.
//
// Mechanism vs. content: these guard the COMMAND BEHAVIOUR + the asset's machine
// contract (the `=== topic: <name> ===` delimiter, the index-never-drifts-from-
// content invariant, one sampled example compiling). The cheat-sheet PROSE
// accuracy is `/docs`-owned (verified-compiling discipline) + `/spec`-validated;
// `/qa` does not assert prose here. The shipped asset is
// `src/syntax/cheatsheet.txt` (28 topics; commit e4920dc).
// =============================================================================

/// Path to the shipped cheat-sheet asset, read-only on project_root (per
/// `tests/CLAUDE.md` — locating a checked-in asset, never written). Lets the
/// asset-contract guard (P1.7) and the sampled-example guard (P1.8) reference
/// the SAME source `/dev`'s parser and `/docs`'s authoring share.
// read-only on project_root
fn cheatsheet_asset() -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/syntax/cheatsheet.txt");
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("the cheat-sheet asset must exist at {path:?}: {e}"))
}

/// Parse the `=== topic: <name> ===` delimiter lines out of the asset, in order.
/// The asset's machine contract: every topic block opens with this exact line
/// shape; the bare `/syntax` index is exactly these names (P1.7).
fn cheatsheet_topic_names(asset: &str) -> Vec<String> {
    asset
        .lines()
        .filter_map(|l| {
            let l = l.trim();
            let inner = l.strip_prefix("=== topic:")?.strip_suffix("===")?;
            Some(inner.trim().to_string())
        })
        .collect()
}

// spec: repl/spec.md §17.17.1 — bare `/syntax` lists the available topic NAMES
// (the scannable index) AND names how to drill in (`/syntax <topic>` …). The
// output is NOT the agent-prose frame (the `▌` gutter is absent — it is curated
// deterministic output, §17.17.2). RED on HEAD: `/syntax` is an unknown command.
#[test]
fn syntax_bare_lists_topics() {
    let out = repl("/syntax\n");
    // The index lists topic names — at least one known topic name from the
    // shipped asset must appear (mechanism, not exhaustive content).
    let names = cheatsheet_topic_names(&cheatsheet_asset());
    assert!(!names.is_empty(), "the asset must declare at least one topic");
    assert!(
        out.stdout.contains(&names[0]),
        "bare /syntax must list topic names (expected e.g. {:?}), stdout={}",
        names[0],
        out.stdout
    );
    // The drill-in hint names the `/syntax <topic>` form (self-documenting index).
    assert!(
        out.stdout.contains("/syntax") && out.stdout.contains("topic"),
        "bare /syntax must name how to drill in (/syntax <topic>), stdout={}",
        out.stdout
    );
    // +shape: NOT framed as agent prose — `/syntax` is deterministic output.
    assert!(
        !out.stdout.contains('\u{258c}'),
        "/syntax is deterministic output, NOT the agent prose frame, stdout={}",
        out.stdout
    );
    // The "unknown command" error must be gone once implemented.
    assert!(
        !out.stdout.contains("unknown command"),
        "/syntax must be a known command, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.17.1 — `/syntax <topic>` (a KNOWN topic) returns that
// topic's dense content block: a known marker from the block (the `TOPIC <name>`
// header the asset uses, plus a `SPEC` cross-link line). Content present, no
// opaque error. RED on HEAD. Uses `match` (a real shipped topic).
#[test]
fn syntax_topic_returns_content() {
    let out = repl("/syntax match\n");
    // A known marker from the `match` topic block: the `TOPIC match` header line
    // the asset's blocks open with under the delimiter.
    assert!(
        out.stdout.contains("TOPIC match") || out.stdout.contains("match"),
        "/syntax match must print the topic's content block, stdout={}",
        out.stdout
    );
    // The block carries the `SPEC` cross-link line the asset uses (`SPEC  06 …`).
    assert!(
        out.stdout.contains("SPEC"),
        "/syntax <topic> content must carry the SPEC cross-link line, stdout={}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("unknown command"),
        "/syntax match must be a known command, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.17.1 — +neg: `/syntax <unknown>` MUST NOT error
// opaquely. It re-prints the topic index (as bare /syntax does) with a short
// "not one of them" note — the self-documenting floor (a wrong name teaches the
// right vocabulary, never a dead end). RED on HEAD. The +neg: NO opaque
// `unknown` error AND no empty/dead-end output.
#[test]
fn syntax_unknown_topic_relists_no_dead_end_neg() {
    let out = repl("/syntax no-such-topic-xyzzy\n");
    let names = cheatsheet_topic_names(&cheatsheet_asset());
    // It re-prints the index: a known real topic name must appear.
    assert!(
        out.stdout.contains(&names[0]),
        "an unknown /syntax topic must re-print the topic index (expected {:?}), stdout={}",
        names[0],
        out.stdout
    );
    // +neg: the dead-end "unknown command" error must NOT appear (the topic was
    // simply not in the set; the index is the helpful re-prompt).
    assert!(
        !out.stdout.contains("unknown command"),
        "an unknown /syntax topic must NOT be a dead-end error, stdout={}",
        out.stdout
    );
    // +neg: the output is not empty/dead-end — the index re-print has content
    // beyond the bare echoed prompt.
    assert!(
        out.stdout.len() > "0+0ms; user> \n".len(),
        "an unknown /syntax topic must re-list, not produce empty output, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.17.3 — `/syntax` works on a plain (non-`agent`) binary:
// it is NOT behind the `agent` feature (LLM-free static asset, the §17.17.3
// "works with the agent absent or feature-off" contract). This default-suite
// test IS the Lane-B-family build guard — it runs on the default build, so a
// green result here is proof the command is unconditional like `/help`. RED on
// HEAD (unknown command); green when /dev 1d wires it (unconditionally, not
// `#[cfg(feature = "agent")]`).
#[test]
fn syntax_works_on_default_build_not_feature_gated() {
    let out = repl("/syntax match\n");
    assert!(
        !out.stdout.contains("unknown command"),
        "/syntax must work on the DEFAULT build (not agent-gated), stdout={}",
        out.stdout
    );
    // Returns real content, not a notice — proves it is a live command here.
    assert!(
        out.stdout.contains("SPEC") || out.stdout.contains("TOPIC"),
        "/syntax on the default build must return cheat-sheet content, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.17.2 — +neg: `/syntax <topic>` under `--no-color`
// (piped / non-TTY) degrades cleanly — NO literal `\x1b[` SGR escape anywhere,
// and the block reads as plain-indented text (mirrors the S89 §17.13.3 ANSI-leak
// floor). RED on HEAD. Uses `hkt`, a real shipped topic whose example carries a
// nested form the pretty-printer would otherwise colourise.
#[test]
fn syntax_degrades_clean_under_no_color_neg() {
    let out = Cranelisp::new()
        .repl()
        .cli_flag("--no-color")
        .stdin("/syntax hkt\n")
        .output();
    // +neg (a): no literal SGR introducer leaks into piped output.
    assert!(
        !out.stdout.contains("\u{1b}["),
        "/syntax under --no-color must carry NO literal ANSI escape (\\x1b[), stdout={:?}",
        out.stdout
    );
    // The content still rendered (so the absence above is real coverage).
    assert!(
        out.stdout.contains("SPEC") || out.stdout.contains("hkt"),
        "/syntax hkt under --no-color must still render its content, stdout={}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("unknown command"),
        "/syntax must be a known command, stdout={}",
        out.stdout
    );
}

// spec: repl/spec.md §17.17.1 — the asset-mechanism guard: the shipped
// `src/syntax/cheatsheet.txt` parses by the `=== topic: <name> ===` delimiter
// (every delimiter line is well-formed and followed by a `TOPIC` line), AND bare
// `/syntax` lists EXACTLY the delimiter-named topics — the index never drifts
// from the content. This is the contract `/dev`'s parser and `/docs`' authoring
// share (cheatsheet-plan §5). RED on HEAD: bare `/syntax` is an unknown command,
// so the index-vs-asset cross-check cannot hold.
#[test]
fn cheatsheet_asset_parses_by_delimiter() {
    let asset = cheatsheet_asset();
    let names = cheatsheet_topic_names(&asset);
    assert!(
        names.len() >= 2,
        "the asset must declare multiple topics via the delimiter; got {names:?}"
    );
    // Every `=== topic: <name> ===` delimiter is immediately followed by a
    // `TOPIC <name>` line (the block-open contract the parser relies on).
    let lines: Vec<&str> = asset.lines().collect();
    for (i, l) in lines.iter().enumerate() {
        let t = l.trim();
        if t.starts_with("=== topic:") && t.ends_with("===") {
            let next = lines.get(i + 1).map(|s| s.trim()).unwrap_or("");
            assert!(
                next.starts_with("TOPIC"),
                "delimiter at line {} must be followed by a TOPIC line, got {next:?}",
                i + 1
            );
        }
    }
    // The bare `/syntax` index lists EXACTLY the delimiter-named topics (no drift,
    // no missing, no extra): every asset topic name appears in the index output.
    let out = repl("/syntax\n");
    for name in &names {
        assert!(
            out.stdout.contains(name),
            "the bare /syntax index must list asset topic {name:?} (index must not \
             drift from content), stdout={}",
            out.stdout
        );
    }
}

// spec: repl/spec.md §17.17.1 — a SAMPLED cheat-sheet example compiles via the
// REPL: this guards the verified-compiling MECHANISM (examples are live Lisp),
// not exhaustive content (that is `/docs`' Phase-5 gate). The sampled example is
// the `defn` topic's `(defn square [x] (* x x))` / `(square 5)` pair, verified
// live to yield `:primitives/Int 25` under the TestStandard prelude (operators
// in scope). Driven straight through the REPL — independent of whether `/syntax`
// is wired, so it pins the example-compiles invariant even pre-1d. (It is in the
// §P1 row set because the mechanism it guards is `/syntax`'s reason to exist.)
#[test]
fn cheatsheet_sampled_example_compiles() {
    // The sampled `defn`-topic example, verbatim from src/syntax/cheatsheet.txt.
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin("(defn square [x] (* x x))\n(square 5)\n")
        .output();
    assert!(
        out.stdout.contains(":primitives/Int 25"),
        "the sampled cheat-sheet example must eval cleanly to :primitives/Int 25, \
         stdout={}",
        out.stdout
    );
    // +neg: no error surfaced — the example is verified-compiling Lisp.
    assert!(
        !out.stdout.to_lowercase().contains("error"),
        "the sampled cheat-sheet example must NOT produce a compile/type error, \
         stdout={}",
        out.stdout
    );
}

// =============================================================================
// S103 increment-II — L-S1 session-history preamble grid (qa plan
// `tests/plan/s103-test-plan.md` §1.6; FIXME 0499 L-S1, the deferred
// capacity-gated tail). A self-documenting introspection outcome MUST be
// invariant to what preceded it in the session — the generalization to the
// surfaces 6a did NOT burn (the 0486 bare-lookup-corruption / 0491 __expr /
// 0484 import-shadow cells already have dedicated guards). The grid prepends
// each of {∅, bare lookup, expression turn, prior failed turn, /reset} to the
// body and asserts the outcome holds every time, so a history-sensitivity bug
// is caught on whichever surface it burns. GREEN-expected (robustness
// generalizations); a RED here is a real history-sensitivity defect.
// =============================================================================

/// The L-S1 preamble grid: (label, stdin-prefix) prepended to a test body.
const LS1_PREAMBLES: &[(&str, &str)] = &[
    ("empty", ""),
    ("bare_lookup", "add-i64\n"),
    ("expression_turn", "(add-i64 1 2)\n"),
    ("prior_failed_turn", "(undefined-symbol-xyz 1)\n"),
    ("reset", "/reset\n"),
];

/// Run `body` under each preamble (PrimitivesOnly REPL) and assert `needle`
/// appears in stdout regardless of session history.
fn assert_preamble_invariant(body: &str, needle: &str) {
    for (label, pre) in LS1_PREAMBLES {
        let cap = repl_prims(&format!("{pre}{body}"));
        assert!(
            cap.stdout.contains(needle),
            "L-S1 preamble `{label}`: expected `{needle}` in stdout regardless \
             of session history; stdout:\n{}\nstderr:\n{}",
            cap.stdout,
            cap.stderr
        );
    }
}

// spec: repl/spec.md §18.4 — `/sig` on a defined fn shows its qualified name
// regardless of session history (L-S1 generalization of the §18.4 surface).
#[test]
fn ls1_sig_of_defn_invariant_to_session_history() {
    assert_preamble_invariant(
        "(defn foo [:Int x] (add-i64 x 1))\n/sig foo\n",
        "user/foo",
    );
}

// spec: repl/spec.md §1.4 — bare-name lookup of a user type resolves to its
// qualified name regardless of session history.
#[test]
fn ls1_bare_lookup_of_type_invariant_to_session_history() {
    assert_preamble_invariant(
        "(deftype Color (Red) (Green))\nColor\n",
        "user/Color",
    );
}

// spec: repl/spec.md §18.4 — `/info` on a defn includes its definition source
// regardless of session history (the 0486 source-corruption class,
// generalized to a healthy defn).
#[test]
fn ls1_info_of_defn_shows_source_invariant_to_session_history() {
    assert_preamble_invariant(
        "(defn bar [:Int y] (mul-i64 y 2))\n/info bar\n",
        "(defn bar",
    );
}

// spec: repl/spec.md §1.2 — an expression result displays identically
// regardless of session history.
#[test]
fn ls1_expression_result_invariant_to_session_history() {
    assert_preamble_invariant("(add-i64 2 3)\n", ":primitives/Int 5");
}

// =============================================================================
// S106 — L-S1 preamble-grid GENERALIZATION beyond the 6a-burned cells
// (FIXME 0499). The S103 grid pinned `/sig`/`/info`/bare-lookup/expression; the
// S106 generalization extends the invariant to the surfaces 6a did NOT burn:
// `/source` exact source, and the `/list` enumeration-layout body. GREEN-expected
// robustness guards (a RED is a real session-history-sensitivity defect).
// =============================================================================

/// Run `body` under each L-S1 preamble and assert the Fns-category layout body is
/// IDENTICAL regardless of session history (the enumeration surface generalization).
fn assert_list_layout_invariant(body: &str) {
    let mut baseline: Option<Vec<String>> = None;
    for (label, pre) in LS1_PREAMBLES {
        let cap = repl_prims(&format!("{pre}{body}"));
        let fns = category_body_lines(&cap.stdout, "Fns");
        match &baseline {
            None => baseline = Some(fns),
            Some(b) => assert_eq!(
                &fns, b,
                "L-S1 preamble `{label}`: the /list Fns layout MUST be invariant to \
                 session history; baseline={b:?} got={fns:?}\nstdout:\n{}",
                cap.stdout
            ),
        }
    }
}

// spec: repl/spec.md §18.4 — `/source` on a defn shows its definition source
// regardless of session history (the 0486 corruption class, generalized to the
// `/source` surface 6a did NOT burn).
#[test]
fn ls1_source_of_defn_invariant_to_session_history() {
    assert_preamble_invariant(
        "(defn baz [:Int z] (add-i64 z 3))\n/source baz\n",
        "(defn baz",
    );
}

// spec: repl/spec.md §3.3 — the `/list` enumeration layout is byte-identical under
// every preamble (generalizes L-S1 to the enumeration/layout surface — couples
// with the 0545/0546 layout goldens).
#[test]
fn ls1_list_layout_invariant_to_session_history() {
    assert_list_layout_invariant(
        "(defn abs [] 1)\n(defn add [] 1)\n(defn ceil [] 1)\n\
         (defn concat [] 1)\n(defn double [] 1)\n(defn drop [] 1)\n/list\n",
    );
}

// spec: repl/spec.md §3.3 — a bare user-type lookup renders its qualified name
// identically under every preamble (bare-lookup type-display generalization).
#[test]
fn ls1_bare_type_display_invariant_to_session_history() {
    assert_preamble_invariant(
        "(deftype Shade (Dark) (Light))\nShade\n",
        "user/Shade",
    );
}

// =============================================================================
// S106 — FIXME 0542: bare trait lookup MUST surface the `; impl:` section
// =============================================================================

// spec: repl/spec.md §4.1.4 — a bare user-module trait lookup MUST surface the
// `; impl:` (implementing-types) section per §4.1.4, even when the trait has no
// impls yet. RED on HEAD (FIXME 0542): the bare-lookup path emits `; defn:` but
// omits `; impl:` entirely when there are no impls.
#[test]
fn bare_user_trait_lookup_shows_impl_section() {
    let out = repl_prims("(deftrait (Display a) (show [a] String))\nDisplay\n");
    assert!(
        out.stdout.contains("; deftrait"),
        "bare trait 'Display' MUST surface '; deftrait'; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("; defn:") && out.stdout.contains("show"),
        "bare trait 'Display' MUST surface the '; defn:' method section; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("; impl:"),
        "a bare user-module trait lookup MUST surface the '; impl:' section per \
         §4.1.4 (FIXME 0542), even when the trait has no impls yet; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §4.1.4 — [Tested+Neg] with impls: the `; impl:` section lists
// the implementing type and does NOT leak unrelated types. Currently GREEN when an
// impl exists (the section appears with impls); pins the +neg boundary.
#[test]
fn bare_user_trait_lookup_impl_section_lists_type_not_others() {
    let out = repl_prims(
        "(deftrait (Display a) (show [a] String))\n\
         (impl Display Int (defn show [x] \"i\"))\n\
         Display\n",
    );
    // Locate the `; impl:` section body (the indented `;  <Type>` comment lines).
    let impl_body: Vec<String> = out
        .stdout
        .lines()
        .skip_while(|l| l.trim() != "; impl:")
        .skip(1)
        .take_while(|l| l.trim_start().starts_with(';'))
        .map(|l| l.trim_start_matches(';').trim().to_string())
        .collect();
    assert!(
        impl_body.iter().any(|l| l.split_whitespace().any(|t| t == "Int")),
        "the '; impl:' section MUST list the implementing type `Int` (§4.1.4); \
         impl body={impl_body:?}\nstdout:\n{}",
        out.stdout
    );
    // +neg: no unrelated type (e.g. `Bool`) leaks into the impl section.
    assert!(
        !impl_body.iter().any(|l| l.split_whitespace().any(|t| t == "Bool")),
        "the '; impl:' section MUST NOT leak an unrelated type `Bool` (§4.1.4 +neg); \
         impl body={impl_body:?}\nstdout:\n{}",
        out.stdout
    );
}

// =============================================================================
// S106 — FIXME 0546: `/imports` "Prelude (implicit)" group MUST use the shared
// layout (not one symbol per line)
// =============================================================================

/// Collect the indented body lines of the `Prelude (implicit)` group. The header
/// carries a trailing `; …` comment, so it is matched by substring, then the
/// following `  `-indented lines are the group body.
fn prelude_group_body(stdout: &str) -> Vec<String> {
    let mut lines = stdout.lines();
    while let Some(line) = lines.next() {
        if line.contains("Prelude (implicit)") {
            let mut body = Vec::new();
            for next in lines.by_ref() {
                if let Some(rest) = next.strip_prefix("  ") {
                    body.push(rest.to_string());
                } else {
                    break;
                }
            }
            return body;
        }
    }
    Vec::new()
}

/// Pipe `lines` to a REPL whose project-root prelude re-exports primitives and
/// defines a sentinel, so the `Prelude (implicit)` group is populated.
fn repl_prelude_imports(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .prelude("(export [primitives [*]])\n(defn gulp [x] (add-i64 x 1))\n")
        .repl()
        .stdin(lines)
        .output()
}

// spec: repl/spec.md §3.3 — the `/imports` "Prelude (implicit)" group MUST render
// through the SHARED multi-column layout (L0–L4), byte-identical to its sibling
// groups — NOT one symbol per line. RED on HEAD (FIXME 0546): the prelude group
// does its own one-name-per-line loop instead of routing through
// `format_symbol_layout`.
#[test]
fn imports_prelude_group_uses_shared_layout() {
    let out = repl_prelude_imports("/imports\n");
    let body = prelude_group_body(&out.stdout);
    assert!(
        !body.is_empty(),
        "the `Prelude (implicit)` group MUST be present and populated; stdout:\n{}",
        out.stdout
    );
    // The shared layout packs multiple names per line (≤6/line); one-per-line is the
    // defect. At least one body line MUST carry two or more names.
    let has_multi = body.iter().any(|l| l.split_whitespace().count() >= 2);
    assert!(
        has_multi,
        "the `Prelude (implicit)` group MUST use the SHARED multi-column layout \
         (§3.3), NOT one symbol per line (FIXME 0546); prelude body:\n{body:?}\n\
         full stdout:\n{}",
        out.stdout
    );
    // And no line may exceed the 6-per-line cap.
    for l in &body {
        assert!(
            l.split_whitespace().count() <= 6,
            "a shared-layout row MUST hold at most 6 names (§3.3 L2/L4); row={l:?}\n\
             full stdout:\n{}",
            out.stdout
        );
    }
}

// spec: repl/spec.md §3.4 — [Tested+Neg]: the fix preserves the group's header
// suffix comment AND applies the shared layout (both, in one output). RED on HEAD
// (the layout is one-per-line today; FIXME 0546).
#[test]
fn imports_prelude_group_preserves_header_suffix_comment() {
    let out = repl_prelude_imports("/imports\n");
    // The header suffix comment is preserved.
    assert!(
        out.stdout.contains("Prelude (implicit)")
            && out.stdout.contains("available via the prelude"),
        "the `Prelude (implicit)` header suffix comment MUST be preserved (§3.4); \
         stdout:\n{}",
        out.stdout
    );
    // +neg: NOT one-per-line — some body row packs multiple names.
    let body = prelude_group_body(&out.stdout);
    assert!(
        body.iter().any(|l| l.split_whitespace().count() >= 2),
        "the header comment MUST be preserved AND the shared layout applied — the \
         body MUST NOT be one-name-per-line (§3.3/§3.4, FIXME 0546); body:\n{body:?}\n\
         full stdout:\n{}",
        out.stdout
    );
}

// =============================================================================
// S106 — FIXME 0545: §3.3 L3 letter-group packing reconcile (pack-to-six across
// letter groups). GREEN guards pinning the reconciled §3.3 rule + corrected
// example (the L3 rule wins; the flawed eager-per-letter example was replaced).
// =============================================================================

// spec: repl/spec.md §3.3 — L3 packs letter groups to six across group boundaries:
// the previously-unpinned `current_count(4) + next_group_size(2) == 6` boundary the
// existing `list_layout_l3_letter_group_early_break` did NOT cover. Groups
// a=2,c=2,d=2 pack onto ONE row (`abs add ceil concat double drop`).
#[test]
fn list_layout_l3_pack_to_six_across_letter_groups() {
    let out = repl(
        "(defn abs [] 1)
(defn add [] 1)
(defn ceil [] 1)
(defn concat [] 1)
(defn double [] 1)
(defn drop [] 1)
/list
",
    );
    let body = category_body_lines(&out.stdout, "Fns");
    assert_eq!(
        body,
        vec!["abs add ceil concat double drop".to_string()],
        "L3: letter groups MUST pack to six across group boundaries (4+2=6 stays on \
         one row) per the reconciled §3.3 rule (FIXME 0545); got body:\n{:?}\n\
         full stdout:\n{}",
        body,
        out.stdout
    );
}

// spec: repl/spec.md §3.3 — L3 negative boundary: a group that would push
// `current_count + group_size` to 7 MUST flush first (never straddle). Groups
// a=2,b=2 fill to 4; c=3 → 4+3=7>6 → c flushes to a fresh row.
#[test]
fn list_layout_l3_neg_boundary_no_straddle() {
    let out = repl(
        "(defn abs [] 1)
(defn add [] 1)
(defn ball [] 1)
(defn bat [] 1)
(defn cat [] 1)
(defn cave [] 1)
(defn cog [] 1)
/list
",
    );
    let body = category_body_lines(&out.stdout, "Fns");
    assert_eq!(
        body,
        vec!["abs add ball bat".to_string(), "cat cave cog".to_string()],
        "L3 negative: a group that would push the row past six MUST flush first \
         (4+3=7>6 → `cat cave cog` on a fresh row), never straddle (§3.3, FIXME \
         0545); got body:\n{:?}\nfull stdout:\n{}",
        body,
        out.stdout
    );
}
