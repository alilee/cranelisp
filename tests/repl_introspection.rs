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
