// repl_negative.rs — REPL negative paths (Sprint 64 Wave 3 Batch 7).
//
// Carries forward the negative-coverage assertions from the integration-tier
// `repl_negative.rs` (~31 tests), `repl_experience.rs` (error subset),
// and `ring3_repl.rs` (defmacro negative paths). Per
// `tests/plan/PLAN.md §"Mode canonicalisation"` REPL is canonical.
//
// What this file covers (per `repl/spec.md §5` error model):
//   - Type errors at the REPL produce clear messages mentioning expected/actual
//   - Parse errors produce clear messages with source location
//   - Unbound symbols / functions produce clear messages
//   - Wrong arity calls produce clear messages
//   - Constructor pattern shape errors (wrong arg count, undefined, etc.)
//   - Defmacro shape errors (missing params, missing body, numeric name, ...)
//   - Type-error categorisation (display does NOT contain qualified symbols
//     where unqualified is required, etc.)
//
// The negative tests assert that error messages mention enough information
// to fix the problem (substring matches), and that the REPL session
// continues alive after each error (assert_ok on the binary exit).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

// Test-authoring shortcuts: see `tests/helpers/e2e.rs`
// `Cranelisp::repl_capture` / `repl_prims_capture`.
fn repl(lines: &str) -> helpers::e2e::CrOutput { Cranelisp::repl_capture(lines) }
fn repl_prims(lines: &str) -> helpers::e2e::CrOutput { Cranelisp::repl_prims_capture(lines) }

// =============================================================================
// Type errors — repl/spec.md §5.1
// =============================================================================

// spec: repl/spec.md §5.1 — type error mentions the issue
#[test]
fn type_error_arg_mismatch() {
    let out = repl_prims("(add-i64 1 \"hello\")\n");
    assert!(
        out.stdout.contains("type error") || out.stdout.contains("Error"),
        "type error must surface a 'type error' message; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §5.1 — if-condition wrong type
#[test]
fn type_error_if_condition_wrong_type() {
    let out = repl_prims("(if 5 1 0)\n");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "if with non-Bool condition must error; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §5.1 — if-branch type mismatch
#[test]
fn type_error_if_branches_mismatch() {
    let out = repl_prims("(if (eq-i64 1 1) 1 \"two\")\n");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "if with mismatched branches must error; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Parse errors — repl/spec.md §5.1
// =============================================================================

// spec: repl/spec.md §5.1 — stray closing paren is a parse error
#[test]
fn parse_error_stray_close() {
    let out = repl(")bad\n");
    assert!(
        out.stdout.to_lowercase().contains("parse error"),
        "stray close paren must produce parse error; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §5.1 — parse error has source location
#[test]
fn parse_error_has_location() {
    let out = repl(")bad\n");
    // Error format: `parse error at SPAN: ...`
    assert!(
        out.stdout.contains("parse error at"),
        "parse error must include 'at SPAN' location; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Unbound symbol errors — repl/spec.md §5.1
// =============================================================================

// spec: repl/spec.md §5.1 — unbound symbol produces clear error
#[test]
fn unbound_symbol_clear_error() {
    let out = repl_prims("(this-name-does-not-exist 42)\n");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "unbound symbol must produce error; got:\n{}",
        out.stdout
    );
    // Either "undefined" or the name itself in the error message.
    assert!(
        out.stdout.contains("this-name-does-not-exist") || out.stdout.contains("undefined"),
        "unbound error must mention the name or 'undefined'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §5.1 — unbound bare symbol produces error
#[test]
fn unbound_bare_symbol_error() {
    let out = repl("nonexistent-bare\n");
    assert!(
        out.stdout.to_lowercase().contains("error") || out.stdout.contains("undefined"),
        "bare unbound symbol must error or report undefined; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Arity errors — repl/spec.md §5.1
// =============================================================================

// spec: repl/spec.md §5.1 — too many args produces clear error
#[test]
fn wrong_arity_too_many_args() {
    let out = repl_prims("(defn foo [x] x)
(foo 1 2 3)
");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "wrong arity must error; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §5.1 — too few args produces auto-curry (NOT an error)
#[test]
fn auto_curry_too_few_args_not_error() {
    let out = repl_prims("(defn add [x y] (add-i64 x y))
(add 1)
");
    // `add 1` partial application returns a closure — the type display has Fn.
    assert!(
        out.stdout.contains("Fn"),
        "auto-curry must produce a Fn closure, not an error; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Constructor errors — repl/spec.md §5.1
// =============================================================================

// spec: repl/spec.md §5.1 — undefined constructor produces clear error
#[test]
fn undefined_constructor_error() {
    let out = repl("(deftype Color Red Green Blue)
NotAConstructor
");
    assert!(
        out.stdout.to_lowercase().contains("error") || out.stdout.contains("undefined"),
        "undefined constructor must error; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §5.1 — constructor wrong arg count
#[test]
fn constructor_wrong_arg_count_error() {
    let out = repl("(deftype Pair (Pair [a b]))
(Pair 1)
");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "constructor with wrong arg count must error; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// defmacro shape errors — spec/09-macros.md §9.9 (Macro Errors)
// =============================================================================

// spec: spec/09-macros.md §9.9 — defmacro missing params is an error
#[test]
fn defmacro_missing_params_error() {
    let out = repl("(defmacro double)\n");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "defmacro without params must error; got:\n{}",
        out.stdout
    );
}

// spec: spec/09-macros.md §9.9 — defmacro with numeric name is an error
#[test]
fn defmacro_numeric_name_error() {
    let out = repl("(defmacro 42 [] `42)\n");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "defmacro with numeric name must error; got:\n{}",
        out.stdout
    );
}

// spec: spec/09-macros.md §9.9 — defmacro missing body is an error
#[test]
fn defmacro_missing_body_error() {
    let out = repl("(defmacro foo [x])\n");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "defmacro without body must error; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Macro call errors — spec/09-macros.md §9.9
// =============================================================================

// spec: spec/09-macros.md §9.9 — macro call with wrong arity
#[test]
fn macro_wrong_arity_error() {
    let out = repl("(defmacro double [x] `(add-i64 ~x ~x))
(double 1 2)
");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "macro with wrong arity must error; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// /list category boundaries — repl/spec.md §3.3 (negative)
// =============================================================================

// spec: repl/spec.md §3.3 (neg) — /list MUST NOT show primitives in user module
#[test]
fn list_neg_no_primitives_in_user() {
    // Empty user module — primitives belong in primitives module, not user.
    repl("/list\n")
        .assert_stdout_does_not_contain("add-i64")
        .assert_stdout_does_not_contain("mul-i64");
}

// spec: repl/spec.md §3.3 (neg) — /list does NOT include the constructor in Fns
#[test]
fn list_neg_constructors_not_in_fns() {
    let out = repl("(deftype Color Red Green Blue)
/list
");
    // Constructors should NOT appear under "Fns:" label.
    let stdout = out.stdout.clone();
    if let Some(fns_pos) = stdout.find("Fns:") {
        let after_fns = &stdout[fns_pos..];
        assert!(
            !after_fns.contains("Red"),
            "/list Fns: section MUST NOT contain constructor 'Red'; got:\n{}",
            stdout
        );
    }
    // (If there's no Fns section at all, the test trivially passes — the
    // intent is that 'Red' is NOT classified as a Fn.)
}

// =============================================================================
// Display format — repl/spec.md §1.2 (negative)
// =============================================================================

// spec: repl/spec.md §1.2 (neg) — Bool display is a word, not a number
#[test]
fn display_neg_bool_not_numeric() {
    // The display must contain "true" word (this expression evaluates to true),
    // and MUST NOT show raw `:primitives/Bool 1` or `:primitives/Bool 0`.
    repl_prims("(eq-i64 1 1)\n")
        .assert_stdout_contains(":primitives/Bool true")
        .assert_stdout_does_not_contain(":primitives/Bool 1")
        .assert_stdout_does_not_contain(":primitives/Bool 0");
}

// spec: repl/spec.md §1.3 (neg) — defn display does NOT say "closure"
#[test]
fn display_neg_defn_not_closure() {
    let out = repl_prims("(defn foo [] 42)\n");
    assert!(
        !out.stdout.contains("closure"),
        "top-level defn MUST NOT display as 'closure'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.3 (neg) — type vars are normalized (no t0/t1/etc.)
#[test]
fn display_neg_type_vars_normalized() {
    // Internal type vars t0, t1, ... must NOT leak into display.
    // Use space-prefixed needle to avoid false-match against words like
    // `t01` if a future renderer used dense numbering.
    repl("(defn id [x] x)\n")
        .assert_stdout_does_not_contain(" t0")
        .assert_stdout_does_not_contain(" t1");
}

// =============================================================================
// REPL must continue alive after errors — repl/spec.md §5.2
// =============================================================================

// spec: repl/spec.md §5.2 — REPL exits 0 even after errors
#[test]
fn repl_exits_clean_after_errors() {
    repl_prims("(undefined-name)
)bad
(this-also-fails)
")
    .assert_ok();
}

// spec: repl/spec.md §5.2 — error followed by valid form: form succeeds
#[test]
fn error_then_valid_form_succeeds() {
    let out = repl_prims("(undefined-name)
(add-i64 1 2)
");
    assert!(
        out.stdout.contains(":primitives/Int 3"),
        "after error, next valid form must succeed; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Slash command negative paths — repl/spec.md §5.2
// =============================================================================

// spec: repl/spec.md §5.2 — unknown slash command is graceful
#[test]
fn unknown_slash_command_graceful() {
    let out = repl("/this-is-not-a-command\n").assert_ok();
    assert!(
        out.stdout.to_lowercase().contains("unknown") || out.stdout.contains("/help"),
        "unknown slash command must produce a guidance message; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.1 — /sig of unknown name does not crash
#[test]
fn sig_unknown_name_graceful() {
    repl("/sig nonexistent-name\n").assert_ok();
}

// spec: repl/spec.md §3.1 — /info of unknown name does not crash
#[test]
fn info_unknown_name_graceful() {
    repl("/info nonexistent-name\n").assert_ok();
}

// spec: repl/spec.md §3.1 — /doc of unknown name does not crash
#[test]
fn doc_unknown_name_graceful() {
    repl("/doc nonexistent-name\n").assert_ok();
}

// =============================================================================
// Slash command nonexistent-name graceful handling — Wave 5.5 GAP-COVER
//
// Each of /source /sexp /ast /clif /disasm must handle nonexistent symbol
// gracefully (no crash, no SIGILL). Coverage was previously held only in
// tests/legacy/e2e.rs.
// =============================================================================

// spec: repl/spec.md §3.1 — /source of unknown name does not crash
// (carry: legacy/e2e.rs::e2e_s3_1_source_neg_nonexistent)
#[test]
fn source_unknown_name_graceful() {
    repl("/source nonexistent-name\n").assert_ok();
}

// spec: repl/spec.md §3.1 — /sexp of unknown name does not crash
// (carry: legacy/e2e.rs::e2e_s3_1_sexp_neg_nonexistent)
#[test]
fn sexp_unknown_name_graceful() {
    repl("/sexp nonexistent-name\n").assert_ok();
}

// spec: repl/spec.md §3.1 — /ast of unknown name does not crash
// (carry: legacy/e2e.rs::e2e_s3_1_ast_neg_nonexistent)
#[test]
fn ast_unknown_name_graceful() {
    repl("/ast nonexistent-name\n").assert_ok();
}

// spec: repl/spec.md §3.1 — /clif of unknown name does not crash
// (carry: legacy/e2e.rs::e2e_s3_1_clif_neg_nonexistent)
#[test]
fn clif_unknown_name_graceful() {
    repl("/clif nonexistent-name\n").assert_ok();
}

// spec: repl/spec.md §3.1 — /disasm of unknown name does not crash
// (carry: legacy/e2e.rs::e2e_s3_1_disasm_neg_nonexistent)
#[test]
fn disasm_unknown_name_graceful() {
    repl("/disasm nonexistent-name\n").assert_ok();
}

// =============================================================================
// Failed defn must NOT register — repl/spec.md §5.2
// =============================================================================

// spec: repl/spec.md §5.2 (neg) — failed defn does NOT enter symbol table
#[test]
fn failed_defn_neg_no_partial_binding() {
    let out = repl_prims("(defn broken [x] (add-i64 x \"oops\"))
(broken 5)
");
    // Calling broken should produce an "undefined" error, not run the defn.
    assert!(
        !out.stdout.contains(":primitives/Int"),
        "failed defn must not register; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §5.2 (neg) — failed redefn preserves original
#[test]
fn failed_redefn_neg_original_preserved() {
    let out = repl_prims("(defn foo [x] (add-i64 x 1))
(defn foo [x] (add-i64 x \"oops\"))
(foo 10)
");
    // After the failed redef, original `foo` (x+1) survives.
    assert!(
        out.stdout.contains(":primitives/Int 11"),
        "failed redef must preserve original; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Duplicate parameter names — Wave 5.6 dedupe-recovery carry
// =============================================================================

// spec: spec/05-definitions.md §5.1.1 — `(defn f [x x] ...)` rejected: a
// parameter list MUST NOT contain duplicate names. The REPL surfaces an
// error diagnostic and does NOT register a binding for `bad`.
// (carry: legacy/ring0.rs::error_duplicate_param_names)
#[test]
fn duplicate_param_names_neg() {
    let out = repl_prims("(defn bad [x x] (add-i64 x x))
(bad 1)
");
    let combined = format!("{}{}", out.stdout, out.stderr);
    // The defn must fail with a diagnostic (not silently bind one of
    // the params). The follow-up `(bad 1)` then errors on unbound name.
    assert!(
        combined.to_lowercase().contains("error")
            || combined.to_lowercase().contains("duplicate")
            || combined.to_lowercase().contains("undefined")
            || combined.to_lowercase().contains("unbound"),
        "duplicate parameter names MUST produce a diagnostic; got:\n\
         stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    // Negative-of-binding: the failed defn does NOT register; calling
    // `bad` returns no `:primitives/Int 2` result.
    assert!(
        !out.stdout.contains(":primitives/Int 2"),
        "duplicate-param defn must NOT register; got stdout:\n{}",
        out.stdout
    );
}

// =============================================================================
// Unclosed paren — Wave 5.6 dedupe-recovery supplement
// =============================================================================

// spec: repl/spec.md §5.1 — unclosed `(` is a parse error, distinct from
// the stray-close paren case (covered by `parse_error_stray_close`). The
// REPL's parser must report a parse error rather than silently consuming
// further input or executing the partial form.
// (carry: legacy/ring0.rs::error_parse_error_unclosed_paren)
// FIXME(/int): see design/arch/fixmes/0142-int-repl-unclosed-paren-on-eof-silent.md —
// REPL silently exits on EOF when an unclosed `(` is pending, instead of
// flushing the accumulated input through the parser and emitting a
// parse-error diagnostic. Asymmetric vs `parse_error_stray_close` (which
// passes). Failing un-ignored per parity rule.
#[test]
fn parse_error_unclosed_paren_neg() {
    // Unclosed `(`: REPL multi-line continuation will keep reading until
    // EOF. Pipe a single line with one open paren and no matching close.
    let out = repl_prims("(add-i64 1 2\n");
    let combined = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    // The unclosed form must produce a parse error diagnostic, not a
    // successful evaluation result.
    assert!(
        combined.contains("parse error")
            || combined.contains("unexpected eof")
            || combined.contains("unclosed")
            || combined.contains("error"),
        "unclosed `(` must produce a parse error; got:\nstdout={}\nstderr={}",
        out.stdout,
        out.stderr
    );
    // Negative-of-success: the partial expression must NOT evaluate to 3.
    assert!(
        !out.stdout.contains(":primitives/Int 3"),
        "unclosed `(` must NOT evaluate to a result; got stdout:\n{}",
        out.stdout
    );
}
