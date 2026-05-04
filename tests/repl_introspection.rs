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

use helpers::e2e::Cranelisp;

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

// spec: repl/spec.md §1.5 — bare nullary constructor lookup displays in dot
// notation `Type.Ctor` form (the value-display shape, distinct from the
// definition display covered by `deftype_display_enum`).
// (carry: legacy/e2e.rs::e2e_s1_5_nullary_ctor_dot_notation)
#[test]
fn nullary_constructor_bare_lookup_dot_notation() {
    repl("(deftype Color Red Green Blue)
Red
")
    .assert_stdout_contains("Color.Red");
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

// spec: repl/spec.md §1.5 — prelude-Option `None` value displays as
// `Option.None`; MUST NOT render the *definition* drawer (`; deftype` /
// `fn.option/` qualified path) when bare `None` is evaluated as a value.
// REGRESSION-GUARD: legacy test marked "BUG"; current implementation shows
// the value-display correctly.
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
