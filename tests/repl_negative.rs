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

// spec: repl/spec.md §5.2 — typecheck-path error recovery (vs the parse-path
// covered by `error_then_valid_form_succeeds`). A type error from
// `(add-i64 1 true)` MUST not corrupt the session; the next valid form
// succeeds. Distinct from the parse-error recovery shape because the error
// arises in the type-checker, not the reader.
// (carry: legacy/sketch_port.rs::sketch_repl_type_error_recovers)
#[test]
fn type_error_recovery_continues_session() {
    let out = repl_prims("(add-i64 1 true)
(add-i64 1 2)
");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "type error MUST surface a diagnostic; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":primitives/Int 3"),
        "after type error, next valid form must succeed; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §5.1 — bare reference to a constrained polymorphic
// function as a first-class value (without an instantiating call site at
// the reference) MUST error. The compiler restriction: a constrained fn
// must be called with arguments at its reference site so the constraint
// can be instantiated; binding it to a let and calling later loses the
// instantiation context. Diagnostic per the implementation: "constrained
// function '<name>' cannot be used as a value — it must be called with
// arguments". REPL session continues after the error.
// (carry: legacy/sketch_port.rs::sketch_constrained_fn_as_value_errors)
#[test]
fn constrained_fn_as_value_neg() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("(defn add [x y] (+ x y))\n(let [f add] (f 1 2))\n")
        .output();
    assert!(
        out.stdout.to_lowercase().contains("error")
            || out.stdout.contains("cannot be used as a value")
            || out.stdout.contains("constrained"),
        "constrained fn as let-bound value MUST error per the compiler \
         restriction; got:\n{}",
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

// =============================================================================
// Wave 5.6 file 6 e2e.rs chunk-1 GAP-COVER carry-forward — Sprint 61
// Slice 5 H neg-coverage promotion (#1) on §5.1 stderr-leak prevention
// + session survival.
// =============================================================================

// spec: repl/spec.md §5.1 — REGRESSION-GUARD: error bodies (e.g. "type
// mismatch", "Error:") MUST be on stdout, not stderr. Stderr is reserved
// for traces (which are silent in the harness's clean-env default). The
// REPL session MUST survive an error and process subsequent valid input.
// This is the negative companion to `type_error_arg_mismatch` (positive
// path: error on stdout) and `type_error_recovery_continues_session`
// (recovery path): the explicit stderr-clean assertion plus end-to-end
// recovery in one test.
// (carry: legacy/e2e.rs::e2e_s5_1_errors_on_stdout_neg_stderr_empty)
#[test]
fn type_error_neg_stderr_empty_and_session_survives() {
    let out = repl_prims("(add-i64 2 true)
(add-i64 1 2)
");
    // (a) Error body MUST NOT appear on stderr.
    assert!(
        !out.stderr.contains("type mismatch"),
        "Error body 'type mismatch' leaked to stderr — spec §5.1 mandates \
         errors on stdout. stderr:\n{}\nstdout:\n{}",
        out.stderr,
        out.stdout
    );
    assert!(
        !out.stderr.contains("Error:"),
        "`Error:` prefix leaked to stderr — spec §5.1 reserves stderr for \
         traces. stderr:\n{}\nstdout:\n{}",
        out.stderr,
        out.stdout
    );
    // (b) Session survives the error and processes the subsequent valid
    // expression. `(add-i64 1 2)` = 3.
    assert!(
        out.stdout.contains(":primitives/Int 3"),
        "Session MUST NOT crash on error per §5.1 last clause. \
         Expected `:primitives/Int 3` after recovery; stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

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

// =============================================================================
// Harvested from tests/legacy/repl_negative_old.rs (FIXME 0124) — S82 Wave 2.
//
// The classification helpers + display-format assertions in the legacy file
// inspected Rust-internal state (`format_result`, `session.shared.symbol_tables`).
// The genuinely-uncovered NEGATIVE assertions are re-expressed here as e2e
// REPL captures against the live binary's `/list` + definition-display surface.
// Items already covered in the active suite (defn-display normalization,
// module-scoping refusal, enum-constructor classification) are NOT re-ported —
// see tests/plan/s82-harvest-repl_negative_old.md for the per-test disposition.
// =============================================================================

// spec: repl/spec.md §3.3 (neg) — no symbol appears in two /list categories.
// A defn classifies under Fns ONLY; a deftype name under Types ONLY. The two
// must be disjoint: 'foo' must not leak into the Types section, 'Color' must
// not leak into the Fns section.
// (carry: legacy/repl_negative_old.rs::list_neg_no_item_in_two_categories)
#[test]
fn list_neg_no_item_in_two_categories() {
    let out = repl_prims("(defn foo [x] x)
(deftype Color Red Green Blue)
/list
");
    let stdout = out.stdout.clone();
    // Isolate the Types section (from "Types:" up to the next category header).
    let types_section = stdout
        .find("Types:")
        .map(|i| {
            let rest = &stdout[i..];
            let end = rest[1..].find("Fns:").map(|j| j + 1).unwrap_or(rest.len());
            &rest[..end]
        })
        .unwrap_or("");
    assert!(
        !types_section.contains("foo"),
        "function 'foo' MUST NOT appear in the Types section of /list; got:\n{}",
        stdout
    );
    // Isolate the Fns section (from "Fns:" to end).
    let fns_section = stdout.find("Fns:").map(|i| &stdout[i..]).unwrap_or("");
    assert!(
        !fns_section.contains("Color"),
        "type 'Color' MUST NOT appear in the Fns section of /list; got:\n{}",
        stdout
    );
}

// spec: repl/spec.md §1.4 (neg) — type names in a definition display MUST be
// fully qualified; a bare unqualified `Int` MUST NOT appear in type position.
// (carry: legacy/repl_negative_old.rs::display_neg_type_always_qualified
//        + display_neg_defn_monomorphic_fully_qualified)
#[test]
fn display_neg_type_always_qualified() {
    let out = repl_prims("(import [primitives [mul-i64]])
(defn double [x] (mul-i64 x 2))
");
    // Positive: the qualified form appears.
    assert!(
        out.stdout.contains("primitives/Int"),
        "defn display MUST use qualified 'primitives/Int'; got:\n{}",
        out.stdout
    );
    // Negative: with every qualified occurrence stripped, no bare 'Int' remains.
    let stripped = out.stdout.replace("primitives/Int", "");
    assert!(
        !stripped.contains("Int"),
        "defn display MUST NOT contain a bare unqualified 'Int'; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.4 (neg) — defn returning Bool shows BOTH param and
// return types fully qualified (`primitives/Int`, `primitives/Bool`).
// (carry: legacy/repl_negative_old.rs::display_neg_defn_bool_return_fully_qualified)
#[test]
fn display_neg_defn_bool_return_fully_qualified() {
    let out = repl_prims("(import [primitives [gt-i64]])
(defn is-pos [x] (gt-i64 x 0))
");
    out.assert_stdout_contains("primitives/Bool")
        .assert_stdout_contains("primitives/Int");
}

// spec: repl/spec.md §1.4 (neg) — a multi-parameter polymorphic defn normalizes
// ALL type variables to consecutive letters; no internal `tN` names leak.
// (carry: legacy/repl_negative_old.rs::display_neg_type_vars_normalized_multi_param)
#[test]
fn display_neg_type_vars_normalized_multi_param() {
    let out = repl("(defn konst [x y] x)\n");
    let stdout = out.stdout.clone();
    for i in 0..20 {
        assert!(
            !stdout.contains(&format!("t{i}")),
            "multi-param poly defn MUST NOT show internal var 't{i}'; got:\n{}",
            stdout
        );
    }
    // Positive: the normalized scheme is present (two distinct letters).
    assert!(
        stdout.contains("user/konst"),
        "defn display should name 'user/konst'; got:\n{}",
        stdout
    );
}

// spec: repl/spec.md §1.4 (neg) — a polymorphic function returning an ADT MUST
// NOT show raw type-variable ids (`tN`) in its display.
// (carry: legacy/repl_negative_old.rs::display_neg_polymorphic_adt_return_no_raw_vars)
#[test]
fn display_neg_polymorphic_adt_return_no_raw_vars() {
    let out = repl("(deftype (Option a) None (Some [:a val]))
(defn wrap [x] (Some x))
");
    let stdout = out.stdout.clone();
    for i in 0..30 {
        assert!(
            !stdout.contains(&format!("t{i}")),
            "polymorphic ADT-return defn MUST NOT show raw var 't{i}'; got:\n{}",
            stdout
        );
    }
}

// spec: repl/spec.md §1.3 (neg) — an enum `deftype` display shows the type name,
// NOT a function-like `(Fn ...)` type. (A product-type ctor legitimately shows a
// constructor `(Fn ...)` per S79 dual-facet — only the enum case is asserted
// here; the legacy product-type Fn-absence assertion is superseded by design.)
// (carry: legacy/repl_negative_old.rs::display_neg_deftype_not_function
//        + display_neg_deftype_with_fields_not_function [positive part only])
#[test]
fn display_neg_deftype_enum_not_function() {
    let out = repl("(deftype Color Red Green Blue)\n");
    out.assert_stdout_contains(":user/Color ; deftype")
        .assert_stdout_does_not_contain("(Fn")
        .assert_stdout_does_not_contain("closure");
}

// spec: repl/spec.md §1.3 — a product `deftype` display names the qualified type.
// (carry: legacy/repl_negative_old.rs::display_neg_deftype_with_fields_not_function)
#[test]
fn display_deftype_with_fields_qualified_name() {
    // `repl_prims` brings primitive type names (`Int`) into scope so the
    // product-type field annotations resolve.
    repl_prims("(deftype Point [:Int x :Int y])\n")
        .assert_stdout_contains("user/Point");
}

// spec: repl/spec.md §5.1 (neg) — using a type name as a function MUST error,
// and the error MUST NOT corrupt the session (the next expression succeeds).
// (carry: legacy/repl_negative_old.rs::module_neg_type_name_not_callable)
#[test]
fn module_neg_type_name_not_callable() {
    let out = repl_prims("(Int 42)
42
");
    let combined = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        combined.contains("error"),
        "calling a type name 'Int' as a function MUST error; got:\nstdout={}\nstderr={}",
        out.stdout,
        out.stderr
    );
    // Session survives: the following bare integer still evaluates.
    out.assert_stdout_contains(":primitives/Int 42");
}

// spec: repl/spec.md §3.3 (neg) — a parameterized data constructor (`Some`,
// taking a field) MUST NOT appear under the Fns category of /list, even though
// it is function-like in application position.
// (carry: legacy/repl_negative_old.rs::list_neg_data_constructor_not_in_functions)
#[test]
fn list_neg_data_constructor_not_in_fns() {
    let out = repl("(deftype (Option a) None (Some [:a val]))
/list
");
    let stdout = out.stdout.clone();
    if let Some(fns_pos) = stdout.find("Fns:") {
        let after_fns = &stdout[fns_pos..];
        for ctor in ["None", "Some"] {
            assert!(
                !after_fns.contains(ctor),
                "/list Fns: section MUST NOT contain data constructor '{ctor}'; got:\n{}",
                stdout
            );
        }
    }
    // (If there's no Fns section at all, the intent — ctors are not Fns — holds.)
}

// spec: repl/spec.md §1.4 — /list normalizes type variables, no raw tN
// FIXME 0352: `/list` rendered polymorphic schemes with raw internal
// type-variable ids (`id : (Fn [t1] t1)`) and unqualified primitive names
// (`double : (Fn [Int] Int)`) instead of the normalized `(Fn [a] a)` +
// fully-qualified `primitives/Int` that `/sig` / definition-display produce.
// Root: `handle_list` formatted `scheme.ty` via the raw `Type::Display`
// rather than the normalize+qualify renderer. Both the `t1`→`a` and
// `Int`→`primitives/Int` leaks are closed by routing through the shared
// `display::format_scheme_type` renderer.
#[test]
fn list_neg_no_raw_type_vars() {
    let out = repl_prims(
        "(defn id [x] x)\n\
         (defn twice [x] (add-i64 x x))\n\
         /list\n",
    );
    // No raw internal type variable ids leak into /list output.
    assert!(
        !out.stdout.contains("t1"),
        "/list leaked a raw internal type var `t1` (violates §1.4 \
         normalization); got:\n{}",
        out.stdout
    );
    // Polymorphic scheme normalized to consecutive lowercase letters.
    assert!(
        out.stdout.contains("(Fn [a] a)"),
        "/list MUST render the polymorphic identity scheme normalized as \
         `(Fn [a] a)` per §1.4; got:\n{}",
        out.stdout
    );
    // Monomorphic case: primitive type names are fully qualified.
    assert!(
        out.stdout.contains("primitives/Int"),
        "/list MUST render primitive type names fully-qualified as \
         `primitives/Int` per §1.4, not bare `Int`; got:\n{}",
        out.stdout
    );
}
