//! S102 Phase-5 Stage-1 — lane L-N1: display-exact + lane L-N2's new
//! diagnostic-shape guards (`tests/plan/s102-test-plan.md` §1.4;
//! `tests/plan/coverage-audit-s101.md` §2.4 L-N1/L-N2, curing miss-patterns
//! P1 assertion-too-weak and P6 diagnostic-surface exemption).
//!
//! The audit quantified the suite at ~99.3% presence-style assertions vs 13
//! exact-output sites; four S101 defects (0492, 0493, trap-format,
//! 0491-secondary) passed THROUGH existing assertions. This lane gives every
//! spec-pinned display class an EXACT assertion:
//!
//!   - **answer-line exactness** — `assert_answer_line`: the REPL transcript
//!     is stripped of the banner and prompt fragments, and a whole line must
//!     equal the pinned bytes (garbling, prefix noise, and unbalanced parens
//!     all fail where substring needles passed);
//!   - **transcript-block exactness** — `assert_golden_masked` (first real
//!     adoption) with the timing mask, for the §18.3 cascade report as a
//!     whole block;
//!   - **the L-N2 negative vocabulary** — `assert_no_internal_artifacts`
//!     (new harness helper, first adoption here + retrofits in
//!     `tests/repl_negative.rs`), banning Debug reprs, internal spans,
//!     synthetic wrapper names, `at 0..0`, and the `'...'` placeholder.
//!
//! Draft-time polarity (probed 2026-07-03 on the CS-A binary):
//!   RED ×9 — exact-shape cells over the open Block-A5 defects (the fixes'
//!   exact-shape acceptance; the 7 existing A5 guards remain the
//!   substring-level record and flip with the same fixes):
//!     display_exact_nested_parameterized_adt_wrap_in_wrap      (0493)
//!     display_exact_option_in_option_value_line                (0493)
//!     display_exact_vec_of_parameterized_adt_value_line        (0493)
//!     display_exact_user_list_recursive_form_whole_line        (0493)
//!     sig_info_bare_lookup_primary_line_agreement_healthy      (0492/§3.8)
//!     trap_answer_line_exact_normative_format                  (§18.5)
//!     macro_arity_diagnostic_carries_no_internal_artifacts     (0485)
//!     macro_arity_diagnostic_plain_call_no_debug_repr          (0485)
//!     qualified_ref_missing_member_diagnostic_names_real_module (0490)
//!   GREEN ×7 exact pins (value/type/defn/error/cascade-block classes).
//! Ledger: tests/plan/ledger.md §"Sprint 102 Phase-5 Stage-1 QA-first RED set".

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;
use helpers::regex::compiler;

fn repl(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::repl_capture(lines)
}

fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::repl_prims_capture(lines)
}

/// Strip the banner and every prompt fragment; return the transcript's
/// answer lines. Prompts are emitted inline (input-only turns leave their
/// prompt as a prefix of the next answer line), so stripping is by regex,
/// not line filtering.
fn answer_lines(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .filter(|l| !l.starts_with("cranelisp REPL"))
        .map(|l| compiler::prompt_fragment().replace_all(l, "").into_owned())
        .filter(|l| !l.trim().is_empty())
        .collect()
}

/// Assert some whole answer line equals `expected` EXACTLY (L-N1 exactness:
/// a garbled sibling containing the expected bytes as a substring fails).
fn assert_answer_line(out: &helpers::e2e::CrOutput, expected: &str) {
    let lines = answer_lines(&out.stdout);
    assert!(
        lines.iter().any(|l| l == expected),
        "no answer line is exactly {expected:?} (L-N1 display-exact)\n\
         answer lines: {lines:#?}\nraw stdout:\n{}",
        out.stdout
    );
}

// =============================================================================
// GREEN exact pins — the display classes that render correctly today
// =============================================================================

// spec: repl/spec.md §1.2 — expression results, exact answer lines for the
// primitive classes (`:QualifiedType value`, nothing else on the line).
#[test]
fn display_exact_primitive_value_lines() {
    let out = repl("42\ntrue\n3.5\n\"hi\"\n").assert_ok();
    assert_answer_line(&out, ":primitives/Int 42");
    assert_answer_line(&out, ":primitives/Bool true");
    assert_answer_line(&out, ":primitives/Float 3.5");
    assert_answer_line(&out, ":primitives/String \"hi\"");
}

// spec: repl/spec.md §1.5 — nullary constructor (`Type.Ctor`) and
// single-level parameterized constructor value lines, exact.
#[test]
fn display_exact_nullary_and_single_level_adt_value_lines() {
    let out = repl(
        "(deftype Color Red Green Blue)\n\
         Red\n\
         (deftype (Wrap a) (MkWrap [:a v]))\n\
         (MkWrap 7)\n",
    )
    .assert_ok();
    assert_answer_line(&out, ":user/Color Color.Red");
    assert_answer_line(&out, ":(user/Wrap primitives/Int) (Wrap.MkWrap 7)");
}

// spec: repl/spec.md §1.5 — Vec display `[elem1 elem2 ...]` with the §1.4
// fully-qualified type prefix, exact — flat and nested-Vec forms.
#[test]
fn display_exact_vec_value_lines() {
    let out = repl("[1 2 3]\n[[1 2] [3]]\n").assert_ok();
    assert_answer_line(&out, ":(primitives/Vec primitives/Int) [1 2 3]");
    assert_answer_line(
        &out,
        ":(primitives/Vec (primitives/Vec primitives/Int)) [[1 2] [3]]",
    );
}

// spec: repl/spec.md §1.3 — the definition confirmation line: FQ type, FQ
// name, classification + docstring drawer, exact.
#[test]
fn display_exact_defn_confirmation_line() {
    let out = repl_prims("(defn double \"Multiply by 2\" [:Int x] (mul-i64 x 2))\n").assert_ok();
    assert_answer_line(
        &out,
        ":(Fn [primitives/Int] primitives/Int) user/double ; defn - Multiply by 2",
    );
}

// spec: repl/spec.md §5.1 — the error line as one exact answer line:
// category + span + message with fully-qualified types (§5.3). Deterministic
// span for fixed input.
#[test]
fn display_exact_type_error_line() {
    let out = repl_prims("(add-i64 1 \"x\")\n").assert_ok();
    assert_answer_line(
        &out,
        "Error: type error at 0..15: type mismatch: expected primitives/Int, got primitives/String",
    );
}

// spec: repl/spec.md §4.1.10 — unbound-name response, exact line.
#[test]
fn display_exact_unbound_symbol_error_line() {
    let out = repl("nosuch\n").assert_ok();
    assert_answer_line(&out, "Error: type error at 0..6: undefined variable: nosuch");
}

// spec: repl/spec.md §18.3 — the cascade report as a WHOLE BLOCK: golden
// transcript (first real `assert_golden_masked` adoption; timing stamps are
// the only masked bytes). Confirmation line + `recompiled:` + `broken:`
// sections, layout and ordering byte-pinned. GREEN (the report is
// spec-conformant today; the golden freezes it).
#[test]
fn display_exact_cascade_report_block_golden() {
    repl_prims(
        "(defn callee [:Int x] (add-i64 x 1))\n\
         (defn caller-a [:Int x] (callee x))\n\
         (defn caller-p [x] (callee x))\n\
         (defn callee [:String s] (str-len s))\n",
    )
    .assert_ok()
    .assert_golden_masked("cascade_report_block", &[compiler::prompt_timing()]);
}

// =============================================================================
// RED exact cells — the Block-A5 fixes' exact-shape acceptance
// =============================================================================

// spec: repl/spec.md §1.5 — ADT fields MUST be recursively formatted: a
// parameterized ADT nested as a field renders as the nested constructor
// form, whole line exact. RED on HEAD (FIXME 0493): renders
// `:(user/Wrap (user/Wrap primitives/Int)) (Wrap.MkWrap primitives/Int) (Wrap.MkWrap 7))`
// — type token in place of the nested constructor + unbalanced parens.
#[test]
fn display_exact_nested_parameterized_adt_wrap_in_wrap() {
    let out = repl("(deftype (Wrap a) (MkWrap [:a v]))\n(MkWrap (MkWrap 7))\n").assert_ok();
    assert_answer_line(
        &out,
        ":(user/Wrap (user/Wrap primitives/Int)) (Wrap.MkWrap (Wrap.MkWrap 7))",
    );
}

// spec: repl/spec.md §1.5 — the same class through the compiler-seeded
// Option: `(Some (Some 42))`, whole line exact. RED on HEAD (FIXME 0493).
#[test]
fn display_exact_option_in_option_value_line() {
    let out = repl("(Some (Some 42))\n").assert_ok();
    assert_answer_line(
        &out,
        ":(primitives/Option (primitives/Option primitives/Int)) (Option.Some (Option.Some 42))",
    );
}

// spec: repl/spec.md §1.5 — a parameterized ADT as a Vec ELEMENT recurses
// through the Vec formatter, whole line exact. RED on HEAD (FIXME 0493
// class × Vec; probed: `[primitives/Int) (Wrap.MkWrap 7)]`).
#[test]
fn display_exact_vec_of_parameterized_adt_value_line() {
    let out = repl("(deftype (Wrap a) (MkWrap [:a v]))\n[(MkWrap 7)]\n").assert_ok();
    assert_answer_line(
        &out,
        ":(primitives/Vec (user/Wrap primitives/Int)) [(Wrap.MkWrap 7)]",
    );
}

// spec: repl/spec.md §1.5 — the List row's generic ADT recursive form as ONE
// exact answer line (type prefix + full nested value). RED on HEAD (FIXME
// 0493; the substring-level record is
// tests/repl_introspection.rs::display_user_list_value_shows_elements_and_nil).
#[test]
fn display_exact_user_list_recursive_form_whole_line() {
    let out = repl(
        "(deftype (List a) Nil (Cons [:a h :(List a) t]))\n\
         (Cons 1 (Cons 2 Nil))\n",
    )
    .assert_ok();
    assert_answer_line(
        &out,
        ":(user/List primitives/Int) (List.Cons 1 (List.Cons 2 List.Nil))",
    );
}

// spec: repl/spec.md §3.8 — `/sig`, `/info`, and bare lookup MUST render the
// IDENTICAL primary line (byte-identity asserted, not three substrings).
// RED on HEAD (FIXME 0492): `/sig` renders the short form
// `:(Fn [Int] Int) double ; defn - Multiply by 2` — unqualified in both
// positions, a §3.8 named non-conformance. Order note: bare lookup runs
// LAST so the 0486 bare-lookup corruption cannot affect the /info turn.
#[test]
fn sig_info_bare_lookup_primary_line_agreement_healthy() {
    let expected = ":(Fn [primitives/Int] primitives/Int) user/double ; defn - Multiply by 2";
    let out = repl_prims(
        "(defn double \"Multiply by 2\" [:Int x] (mul-i64 x 2))\n\
         /sig double\n\
         /info double\n\
         double\n",
    )
    .assert_ok();
    let lines = answer_lines(&out.stdout);
    let occurrences = lines.iter().filter(|l| *l == expected).count();
    // defn confirmation + /sig + /info + bare lookup = 4 identical renderings.
    assert!(
        occurrences >= 4,
        "/sig, /info, and bare lookup MUST all render the identical §3.8 \
         primary line {expected:?}; found it {occurrences} times (expected ≥4: \
         defn echo + /sig + /info + bare) — FIXME 0492\nanswer lines: {lines:#?}",
    );
}

// spec: repl/spec.md §18.5 — the trap as ONE exact answer line: the
// `runtime error: ` category prefix directly followed by the trap message,
// no wrapper chain, no synthetic span. RED on HEAD (the §18.5 [S102] MUST;
// the substring-level record is tests/repl_redefinition.rs::
// trap_presented_in_normative_runtime_error_format). The embedded span
// (24..34) is the original error's — deterministic for this fixed source.
#[test]
fn trap_answer_line_exact_normative_format() {
    let out = repl_prims(
        "(defn callee [:Int x] (add-i64 x 1))\n\
         (defn caller-a [:Int x] (callee x))\n\
         (defn callee [:String s] (str-len s))\n\
         (caller-a 1)\n",
    )
    .assert_ok();
    assert_answer_line(
        &out,
        "runtime error: user/caller-a is broken by the redefinition of user/callee: \
         type error at 24..34: type mismatch: expected primitives/String, got primitives/Int",
    );
}

// =============================================================================
// L-N2 — new diagnostic-shape guards (the 0485/0490 classes; the negative
// vocabulary is the assertion)
// =============================================================================

// spec: repl/spec.md §5.1 — a diagnostic is category + USER-source location
// + human-readable message: no Rust Debug reprs, no expansion-buffer spans.
// RED on HEAD (FIXME 0485, reduced stdlib-free): a recursive macro's
// clause-exhaustion reports `at 1000069..1000069` + `FQSymbol { module:
// ModuleFullPath("user"), symbol: Symbol("mycond") }` + the recursion-bottom
// arity ("1 argument(s)") instead of the user's call.
#[test]
fn macro_arity_diagnostic_carries_no_internal_artifacts() {
    repl(
        "(defmacro mycond ([] 0) ([t b &rest] `(if ~t ~b (mycond ~@rest))))\n\
         (mycond true 1 false)\n",
    )
    .assert_ok()
    .assert_stdout_contains("user/mycond") // the macro named by display FQ name…
    // …with the accepted clause arities surfaced (derived from the clause set:
    // `([] …)` → 0, `([t b &rest] …)` → 2+), so the recursion-bottom grain is
    // interpretable rather than an opaque "0 argument(s)" (FIXME 0485 cure)…
    .assert_stdout_contains("clauses accept 0 or 2+")
    .assert_no_internal_artifacts(); // …with no Debug repr / internal span
}

// spec: repl/spec.md §5.1 — the non-recursive sibling: a plain wrong-arity
// macro call's diagnostic uses the display FQ name, not the Debug repr.
// RED on HEAD (FIXME 0485 class; the span here is already the user's call).
#[test]
fn macro_arity_diagnostic_plain_call_no_debug_repr() {
    repl(
        "(defmacro m2 [a b] `(add-i64 ~a ~b))\n\
         (m2 1)\n",
    )
    .assert_ok()
    .assert_stdout_contains("user/m2")
    .assert_no_internal_artifacts();
}

// spec: repl/spec.md §5.1 — a qualified reference to a non-existent member
// of a REAL module reports against that module with the member the user
// typed: no phantom `<current>.<qualifier>` module, no `'...'` placeholder,
// no `at 0..0` span. RED on HEAD (FIXME 0490): `module 'user.primitives'
// referenced by 'user.primitives/...' not found` at 0..0.
#[test]
fn qualified_ref_missing_member_diagnostic_names_real_module() {
    repl_prims("(primitives/nosuchfn 1 2)\n")
        .assert_ok()
        .assert_stdout_contains("nosuchfn") // the member the user typed is named
        .assert_stdout_does_not_contain("user.primitives") // no phantom module
        .assert_no_internal_artifacts(); // no 0..0 span, no '...' placeholder
}
