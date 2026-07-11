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

use helpers::e2e::{Cranelisp, PreludeVariant};
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

// spec: repl/spec.md §1.5 — the same nested-parameterized-ADT class through
// the primitives-seeded `Option`: `(Some (Some 42))`, whole line exact. The
// nested-ADT display mechanism is already GREEN (sibling
// `display_exact_nested_parameterized_adt_wrap_in_wrap` proves it, ex-0493);
// this test needs `Some`/`Option` in scope, so it uses `repl_prims` (the
// primitives-only prelude re-exports the bootstrap-seeded `primitives/Option`)
// rather than the bare `repl` preset, which omits it.
#[test]
fn display_exact_option_in_option_value_line() {
    let out = repl_prims("(Some (Some 42))\n").assert_ok();
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

// =============================================================================
// S103 Defect 1 — R5 value-layout ADT display (owner /backend; FIXME(/backend))
//
// The Wave-3a `value_layout` optimisation flattened single-constructor,
// single-SCALAR-field ADTs (`(deftype Box (Box [:Int v]))`) to a bare
// unboxed representation. The REPL auto-display formatter (`src/display.rs`)
// was NOT taught this shape: it renders the flattened payload as an opaque
// `<tag:N>` sentinel instead of the constructor form, and for a `:Float`
// field it dereferences the f64 bit-pattern AS A HEAP POINTER — a SIGSEGV
// (exit 139 release / SIGABRT misaligned-deref in debug at src/display.rs).
// Construct/match/extract are SOUND (the GREEN control below proves it); the
// defect is display-only. RED on HEAD; flips GREEN when /backend teaches the
// formatter the value_layout shape.
// spec: repl/spec.md §1.5 + spec/12-runtime.md §12.9.
// =============================================================================

// spec: repl/spec.md §1.5 — a value_layout-eligible single-scalar-field ADT
// MUST render as the constructor form `(Box 99)`, not the `<tag:99>` sentinel.
// RED on HEAD (FIXME(/backend)): renders `:user/Box <tag:99>`.
#[test]
fn display_r5_value_layout_int_shows_constructor_form() {
    let out = repl_prims("(deftype Box (Box [:Int v]))\n(Box 99)\n").assert_ok();
    assert_answer_line(&out, ":user/Box (Box 99)");
}

// spec: repl/spec.md §1.5 — the same value_layout class over a `:Bool` field:
// MUST render `(B true)`, not `<tag:1>` (the raw discriminant of the bool).
// RED on HEAD (FIXME(/backend)): renders `:user/B <tag:1>`.
#[test]
fn display_r5_value_layout_bool_shows_constructor_form() {
    let out = repl_prims("(deftype B (B [:Bool b]))\n(B true)\n").assert_ok();
    assert_answer_line(&out, ":user/B (B true)");
}

// spec: spec/12-runtime.md §12.9 — the value_layout class over a `:Float`
// field: the formatter MUST NOT deref the f64 bit-pattern as a pointer. MUST
// render `(F 3.14)` with exit 0. RED on HEAD (FIXME(/backend)): the process
// crashes (SIGSEGV release / misaligned-pointer SIGABRT in debug at
// src/display.rs:463 — the f64 bits `0x40091eb851eb852f` deref'd as a ptr).
// This is the most severe cell of the class — a display of a sound value
// aborts the REPL.
#[test]
fn display_r5_value_layout_float_does_not_crash() {
    let out = repl_prims("(deftype F (F [:Float x]))\n(F 3.14)\n").assert_ok();
    assert_answer_line(&out, ":user/F (F 3.14)");
}

// spec: repl/spec.md §1.5 — a value_layout ADT nested as a FIELD of an outer
// (non-value_layout) ADT MUST recurse to its constructor form: the inner
// `(Box 5)` renders as `(Box 5)`, not `<tag:5>`. The outer `Wrap` already
// renders correctly (its 2-field shape is not value_layout); only the nested
// value_layout field is wrong. RED on HEAD (FIXME(/backend)): renders
// `:user/Wrap (Wrap <tag:5> 7)`.
#[test]
fn display_r5_value_layout_nested_field_shows_constructor_form() {
    let out = repl_prims(
        "(deftype Box (Box [:Int v]))\n\
         (deftype Wrap (Wrap [:Box b :Int n]))\n\
         (Wrap (Box 5) 7)\n",
    )
    .assert_ok();
    assert_answer_line(&out, ":user/Wrap (Wrap (Box 5) 7)");
}

// spec: spec/12-runtime.md §12.9 — GREEN control proving value semantics are
// SOUND: constructing a value_layout `:Float` ADT, matching it, and extracting
// the field yields the correct primitive value with NO crash. This isolates
// the defect to the DISPLAY formatter — construct/match/extract are correct.
// GREEN on HEAD (stays green; the sibling display tests above are the RED).
#[test]
fn r5_value_layout_construct_match_extract_is_sound() {
    let out = repl_prims(
        "(deftype F (F [:Float x]))\n\
         (defn unf [f] (match f [(F v) v]))\n\
         (unf (F 3.14))\n",
    )
    .assert_ok();
    assert_answer_line(&out, ":primitives/Float 3.14");
}

// =============================================================================
// S107 item 2 — FIXME 0554: `/sexp` & `/source` aligned `let`/`match` column
// layout (repl/spec.md §3.11). Byte-reproducible MUST (colour-off). The §3.11
// worked `rotate` example is the assertion target; the P0/P5 edge rules get
// their own guards. `/source` and `/sexp` share `crate::pretty::pretty_print`,
// so both MUST emit the same bytes. Home: this file (byte-exact block asserts).
//
// RED on HEAD: `src/pretty.rs` is pair-unaware and SMEARS the binding pairs
// across lines; the aligned two-column layout does not exist yet. Flips GREEN
// when the pair-awareness lands. G-3 drafting rule: the non-TTY REPL writes the
// `user> ` prompt verbatim, so the pinned block is asserted as a byte-exact
// SUBSTRING of stdout (the pretty-printer emits it as contiguous clean lines),
// not whole-stdout equality.
// =============================================================================

/// TestStandard-prelude REPL capture — the `rotate` fixture needs the operators
/// `-` / `+` / `<` (Num/Ord), which the standard test prelude provides.
fn repl_std(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin(lines)
        .output()
}

/// The §3.11 `rotate` fixture: the worked-example `defn` plus the free-standing
/// supporting definitions it references (`L`/`R` constructors, `Position`,
/// `pos`). The pretty-printed bytes of `rotate` depend only on `rotate`'s own
/// parsed form, so the surrounding definitions do not perturb the block.
const ROTATE_FIXTURE: &str = "\
(deftype Rotation (L [:Int l]) (R [:Int r]))
(deftype Position [:Int p])
(defn pos [x] (match x [(Position n) n]))
(defn rotate [p r] (let [d (match r [(L l) (- 0 l) (R r) r]) new-pos (+ (pos p) d) final-pos (if (< new-pos 0) (+ new-pos 100) new-pos)] (Position final-pos)))
";

/// The byte-exact §3.11 worked-output block for `/sexp rotate` (colour-off) —
/// copied verbatim from repl/spec.md §3.11 lines 992–1000: the aligned `let`
/// left column at 8 / right column at 18, the nested two-arm `match` arm column
/// at 28 / right column at 34, and the multi-line `if` body at column 20. No
/// trailing newline — asserted as a contiguous byte-exact substring.
const ROTATE_SEXP_BLOCK: &str = concat!(
    "(defn rotate\n",
    "  [p r]\n",
    "  (let [d         (match r [(L l) (- 0 l)\n",
    "                            (R r) r])\n",
    "        new-pos   (+ (pos p) d)\n",
    "        final-pos (if (< new-pos 0)\n",
    "                    (+ new-pos 100)\n",
    "                    new-pos)]\n",
    "    (Position final-pos)))",
);

// spec: repl/spec.md §3.11 — `/sexp rotate` MUST render the aligned `let`/`match`
// column layout byte-for-byte (the §3.11 worked example). Byte-exact SUBSTRING
// assertion of the pinned 9-line block (G-3: the `user> ` prompt interleaves, so
// the block is a substring, not whole-stdout). RED on HEAD (the pre-S107 printer
// smears the binding pairs); GREEN when `src/pretty.rs` pair-awareness lands.
#[test]
fn sexp_rotate_aligned_let_match_byte_exact() {
    let out = repl_std(&format!("{ROTATE_FIXTURE}/sexp rotate\n"));
    assert!(
        out.stdout.contains(ROTATE_SEXP_BLOCK),
        "/sexp rotate MUST emit the §3.11 byte-exact aligned block:\n\
         --- expected (byte-exact substring) ---\n{ROTATE_SEXP_BLOCK}\n\
         --- actual stdout ---\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.11 — `/source rotate` shares `crate::pretty::pretty_print`
// with `/sexp`, so it MUST emit the IDENTICAL byte-exact aligned block (the two
// commands must not diverge). RED on HEAD (same smear); GREEN with the shared
// pair-awareness fix.
#[test]
fn source_rotate_aligned_matches_sexp_byte_exact() {
    let out = repl_std(&format!("{ROTATE_FIXTURE}/source rotate\n"));
    assert!(
        out.stdout.contains(ROTATE_SEXP_BLOCK),
        "/source rotate MUST emit the SAME §3.11 byte-exact aligned block as \
         /sexp (shared pretty_print path):\n\
         --- expected (byte-exact substring) ---\n{ROTATE_SEXP_BLOCK}\n\
         --- actual stdout ---\n{}",
        out.stdout
    );
}

/// The byte-exact §3.11 aligned block for `/sexp f` where
/// `f = (defn f [r] (match r [(L l) l (R r) r]))`. The two-arm `match` is forced
/// multi-line (P0), which propagates to the enclosing flat-fitting `defn` (P0
/// force-multiline propagation, FIXME 0554). The arm PATTERNS sit in the left
/// column (col 12, after `(match r [`), byte-aligned one above the other, and
/// the arm BODIES sit at the aligned right column (col 18 = leftCol 12 + W 5 + 1).
/// Byte-exact substring captures BOTH the pattern left-column alignment AND the
/// body right-column alignment (§3.11 P1–P3) — a smeared or mis-columned layout
/// fails where a mere "not on the same line" needle would pass. Cross-checked
/// against `src/pretty.rs::p0_parent_of_two_arm_match_forces_multiline_aligned`.
const MATCH_F_SEXP_BLOCK: &str = concat!(
    "(defn f\n",
    "  [r]\n",
    "  (match r [(L l) l\n",
    "            (R r) r]))",
);

// spec: repl/spec.md §3.11 — P0/P1 trigger: a two-arm `match` that would fit a
// flat line MUST render multi-line aligned; the arms MUST NOT be collapsed onto
// one line (the pre-S107 smear), AND the arm patterns/bodies MUST be COLUMN-
// ALIGNED (patterns in the left column, bodies at the shared right column). The
// former guard only asserted the two patterns were not on one line — a false
// green that did not pin alignment (the /review IMPORTANT). This now asserts the
// byte-exact aligned block, which encodes both the pattern left-column and body
// right-column positions. GREEN with the S107 pair-awareness fix.
#[test]
fn sexp_two_arm_match_forces_multiline_neg() {
    let out = repl_std(
        "(deftype Rotation (L [:Int l]) (R [:Int r]))\n\
         (defn f [r] (match r [(L l) l (R r) r]))\n\
         /sexp f\n",
    );
    // (1) The patterns MUST NOT share a line (the pre-S107 smear).
    let shared = out
        .stdout
        .lines()
        .any(|l| l.contains("(L l)") && l.contains("(R r)"));
    assert!(
        !shared,
        "a two-arm `match` MUST render multi-line aligned (P0/P1) — the two arm \
         patterns `(L l)` and `(R r)` MUST NOT share a line (the pre-S107 smear); \
         got:\n{}",
        out.stdout
    );
    // (2) The arms MUST be COLUMN-ALIGNED — asserted byte-exact (§3.11 P1–P3).
    // This is the strengthening the false-green guard was missing: the layout
    // must be column-aligned, not merely split across lines.
    assert!(
        out.stdout.contains(MATCH_F_SEXP_BLOCK),
        "a two-arm `match` MUST render COLUMN-ALIGNED (§3.11 P1–P3): the arm \
         patterns share a left column and the bodies share the right column. \
         Byte-exact substring assertion:\n\
         --- expected (byte-exact substring) ---\n{MATCH_F_SEXP_BLOCK}\n\
         --- actual stdout ---\n{}",
        out.stdout
    );
}

/// The byte-exact §3.11 aligned block for `/sexp g` where
/// `g = (defn g [x] (let [a 1 bb 2] a))` — the FLAT-PARENT case the S107 Blocker
/// (FIXME 0554) was about. The enclosing `defn` fits flat (≤40 cols) but contains
/// a ≥2-pair `let`, so P0 forces the `let` multi-line and that force PROPAGATES to
/// the enclosing `defn`: it too renders multi-line so the `let`'s right column
/// aligns to its true INDENTED position (col 13 = leftCol 8 + W 3 + 1), never the
/// flat-parent column-0 smear that the Blocker exhibited. Cross-checked against
/// `src/pretty.rs::p0_parent_of_two_pair_let_forces_multiline_aligned` (byte-exact).
const FLAT_PARENT_LET_BLOCK: &str = concat!(
    "(defn g\n",
    "  [x]\n",
    "  (let [a  1\n",
    "        bb 2]\n",
    "    a))",
);

// spec: repl/spec.md §3.11 — P0 force-multiline PROPAGATION to a flat-fitting
// parent (FIXME 0554, the S107 Blocker). `(defn g [x] (let [a 1 bb 2] a))` fits
// flat but wraps a ≥2-pair `let`; the `let` forces itself multi-line+aligned and
// that force propagates up so the enclosing `defn` also renders multi-line and
// the `let`'s two-column layout aligns to its true indented position — NOT the
// column-0 smear the pre-fix flat-parent path produced. Byte-exact SUBSTRING (G-3:
// the non-TTY `user> ` prompt interleaves, so the block is a substring). GREEN
// with the S107 fix in `src/pretty.rs` — the Blocker's e2e regression guard.
#[test]
fn sexp_flat_parent_two_pair_let_forces_multiline_aligned() {
    let out = repl("(defn g [x] (let [a 1 bb 2] a))\n/sexp g\n");
    assert!(
        out.stdout.contains(FLAT_PARENT_LET_BLOCK),
        "a flat-fitting `defn` wrapping a ≥2-pair `let` MUST render multi-line so \
         the `let` two-column layout aligns to its indented position (§3.11 P0 \
         force-multiline propagation), NOT a column-0 smear. Byte-exact substring:\n\
         --- expected (byte-exact substring) ---\n{FLAT_PARENT_LET_BLOCK}\n\
         --- actual stdout ---\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.11 — P0/P5 edge (stability guard): a `let` with ONE
// binding pair has nothing to align, so it MUST follow the pre-existing
// flat/threshold layout UNCHANGED — it MUST NOT be forced into the two-column
// layout. GREEN today and MUST stay GREEN across the fix (proves P0's "≥2 pairs"
// trigger does not over-reach to single-pair lets).
#[test]
fn sexp_single_pair_let_flat_fallback() {
    let out = repl_std("(defn g [] (let [x 5] x))\n/sexp g\n");
    // The single binding pair stays flat: name and value share the line.
    let flat = out.stdout.lines().any(|l| l.contains("(let [x 5]"));
    assert!(
        flat,
        "a single-pair `let` MUST stay flat (P0 requires ≥2 pairs to align) — \
         `[x 5]` must not be split into two-column layout; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.11 — P5 graceful fallback (robustness guard): a `match`
// with an ODD element count (malformed, not cleanly pairable) MUST be handled
// gracefully — no crash, no panic, the session survives. Today this is rejected
// cleanly at parse time (`match arms must have an even number of elements`); the
// guard pins that the pair-aware printer, once it lands, still cannot be driven
// to a panic / signal-kill by an odd-count vector. GREEN today; stability guard.
#[test]
fn sexp_odd_count_match_arm_no_crash_neg() {
    let out = repl_std(
        "(deftype Rotation (L [:Int l]) (R [:Int r]))\n\
         (defn od [r] (match r [(L l) (R r) r]))\n\
         (+ 2 3)\n",
    );
    // Not signal-killed (no SIGSEGV / SIGABRT panic on the odd-count vector).
    assert!(
        out.status.code().is_some(),
        "an odd-count `match` MUST NOT crash the process (P5 graceful fallback); \
         the process was signalled. stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    // A clean diagnostic is produced (the odd count is reported, not swallowed).
    assert!(
        out.stdout.to_lowercase().contains("even number of elements")
            || out.stdout.to_lowercase().contains("error"),
        "an odd-count `match` MUST produce a clean diagnostic, not a panic; got:\n{}",
        out.stdout
    );
    // The session SURVIVES: the following form still evals (no crash, no drop).
    assert!(
        out.stdout.contains(":primitives/Int 5"),
        "the REPL MUST survive an odd-count `match` — the following `(+ 2 3)` must \
         eval to `:primitives/Int 5`; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §3.11 — 0-pair edge (stability guard): an empty binding
// vector `(let [] body)` has nothing to align and MUST render without a crash and
// with no spurious alignment padding. GREEN today (`(let [] 7)` renders flat);
// stability guard that the pair-aware printer handles the empty vector.
#[test]
fn sexp_empty_let_binding_no_crash() {
    let out = repl_std("(defn e [] (let [] 7))\n/sexp e\n");
    assert!(
        out.status.code().is_some(),
        "an empty-binding `let` MUST NOT crash the process; the process was \
         signalled. stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    // The empty-binding let renders with no spurious padding — `(let [] 7)` flat.
    assert!(
        out.stdout.lines().any(|l| l.contains("(let [] 7)")),
        "an empty-binding `let` MUST render `(let [] 7)` flat with no spurious \
         alignment padding; got:\n{}",
        out.stdout
    );
}
