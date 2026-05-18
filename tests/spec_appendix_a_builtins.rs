// spec_appendix_a_builtins.rs — Builtin primitive surface (Sprint 64 Wave 5
// Batch 2).
//
// Covers `spec/appendix-a-builtins.md`. Carries forward language-behaviour
// assertions from legacy integration-tier `tests/ring0.rs`, `tests/ring1.rs`,
// `tests/sketch_port.rs`, and `tests/e2e.rs`. REPL canonical with
// PrimitivesOnly prelude per
// `tests/plan/PLAN.md §"Mode canonicalisation"`.
//
// What this file covers:
//   - §A.1 primitive types — covered surface in spec_03_types.rs
//   - §A.2 compound types — Vec basics
//   - §A.3 inline primitives — Int/Float arithmetic + comparison + Bool
//   - §A.3 extern primitives — string ops, Vec ops, conversion
//   - §A.4 special forms — covered in repl_*.rs files

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

// =============================================================================
// §A.3 Integer arithmetic
// =============================================================================

// spec: spec/appendix-a-builtins.md §A.3 — add-i64
#[test]
fn primitive_add_i64() {
    repl_prims("(add-i64 3 4)\n").assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/appendix-a-builtins.md §A.3 — sub-i64
#[test]
fn primitive_sub_i64() {
    repl_prims("(sub-i64 10 3)\n").assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/appendix-a-builtins.md §A.3 — mul-i64
#[test]
fn primitive_mul_i64() {
    repl_prims("(mul-i64 6 7)\n").assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/appendix-a-builtins.md §A.3 — div-i64
#[test]
fn primitive_div_i64() {
    repl_prims("(div-i64 20 4)\n").assert_stdout_contains(":primitives/Int 5");
}

// =============================================================================
// §A.3 Integer comparison
// =============================================================================

// spec: spec/appendix-a-builtins.md §A.3 — eq-i64
#[test]
fn primitive_eq_i64_true() {
    repl_prims("(eq-i64 5 5)\n").assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/appendix-a-builtins.md §A.3 — eq-i64 false
#[test]
fn primitive_eq_i64_false() {
    repl_prims("(eq-i64 1 2)\n").assert_stdout_contains(":primitives/Bool false");
}

// spec: spec/appendix-a-builtins.md §A.3 — lt-i64
#[test]
fn primitive_lt_i64() {
    repl_prims("(lt-i64 1 2)\n").assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/appendix-a-builtins.md §A.3 — gt-i64
#[test]
fn primitive_gt_i64() {
    repl_prims("(gt-i64 5 3)\n").assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/appendix-a-builtins.md §A.3 — le-i64
#[test]
fn primitive_le_i64() {
    repl_prims("(le-i64 5 5)\n").assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/appendix-a-builtins.md §A.3 — ge-i64
#[test]
fn primitive_ge_i64() {
    repl_prims("(ge-i64 5 5)\n").assert_stdout_contains(":primitives/Bool true");
}

// =============================================================================
// §A.3 Float arithmetic
// =============================================================================

// spec: spec/appendix-a-builtins.md §A.3 — add-f64
#[test]
fn primitive_add_f64() {
    repl_prims("(add-f64 1.5 2.5)\n").assert_stdout_contains(":primitives/Float");
}

// spec: spec/appendix-a-builtins.md §A.3 — float comparison lt-f64
#[test]
fn primitive_lt_f64() {
    repl_prims("(lt-f64 1.0 2.0)\n").assert_stdout_contains(":primitives/Bool true");
}

// =============================================================================
// §A.3 Boolean
// =============================================================================

// spec: spec/appendix-a-builtins.md §A.3 — not true → false; also
//       design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md
//       §"The invariant" — `not` is authored as a primitive per Decision C1; from
//       S68 onward the dispatch path is functionally equivalent to any other
//       module (GOT-indirect via PRIMITIVES_TABLE). Assertion is unchanged —
//       the behaviour must hold under both the pre-S68 inline/force-link path
//       and the post-S68 statically-constructed-table path.
#[test]
fn primitive_not_true() {
    repl_prims("(not true)\n").assert_stdout_contains(":primitives/Bool false");
}

// spec: spec/appendix-a-builtins.md §A.3 — not false → true; also
//       design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md
//       §"The invariant" — `not` is authored as a primitive per Decision C1.
#[test]
fn primitive_not_false() {
    repl_prims("(not false)\n").assert_stdout_contains(":primitives/Bool true");
}

// =============================================================================
// §A.3 Type conversion
// =============================================================================

// spec: spec/appendix-a-builtins.md §A.3 — int-to-string
#[test]
fn primitive_int_to_string() {
    repl_prims("(int-to-string 42)\n").assert_stdout_contains(":primitives/String");
}

// spec: spec/appendix-a-builtins.md §A.3 — bool-to-string true
#[test]
fn primitive_bool_to_string() {
    repl_prims("(bool-to-string true)\n").assert_stdout_contains(":primitives/String");
}

// =============================================================================
// §A.3 String ops
// =============================================================================

// spec: spec/appendix-a-builtins.md §A.3 — str-concat
#[test]
fn primitive_str_concat() {
    repl_prims("(str-concat \"foo\" \"bar\")\n").assert_stdout_contains(":primitives/String");
}

// spec: spec/appendix-a-builtins.md §A.3 — str-eq same
#[test]
fn primitive_str_eq_true() {
    repl_prims("(str-eq \"foo\" \"foo\")\n").assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/appendix-a-builtins.md §A.3 — str-eq diff
#[test]
fn primitive_str_eq_false() {
    repl_prims("(str-eq \"foo\" \"bar\")\n").assert_stdout_contains(":primitives/Bool false");
}

// spec: spec/appendix-a-builtins.md §A.3 — str-len
#[test]
fn primitive_str_len() {
    repl_prims("(str-len \"hello\")\n").assert_stdout_contains(":primitives/Int 5");
}

// =============================================================================
// §A.3 Vec ops
// =============================================================================

// spec: spec/appendix-a-builtins.md §A.3 — vec-len
#[test]
fn primitive_vec_len() {
    repl_prims("(vec-len [1 2 3])\n").assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/appendix-a-builtins.md §A.3 — vec-get
#[test]
fn primitive_vec_get_first() {
    repl_prims("(vec-get [10 20 30] 0)\n").assert_stdout_contains(":primitives/Int 10");
}

// spec: spec/appendix-a-builtins.md §A.3 — vec-push appends
#[test]
fn primitive_vec_push_increases_len() {
    repl_prims("(vec-len (vec-push [1 2] 3))\n").assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/appendix-a-builtins.md §A.3 — vec-set produces equivalent-length Vec
#[test]
fn primitive_vec_set_preserves_len() {
    repl_prims("(vec-len (vec-set [1 2 3] 1 99))\n").assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/appendix-a-builtins.md §A.3 — vec-push places the new value at
// the last index. Distinct from `primitive_vec_push_increases_len` (which only
// observes the length); this confirms the value was actually written.
// (carry: legacy/sketch_port.rs::sketch_vec_push_value)
#[test]
fn primitive_vec_push_value_at_last_index() {
    repl_prims("(vec-get (vec-push [1 2 3] 99) 3)\n")
        .assert_stdout_contains(":primitives/Int 99");
}

// spec: spec/appendix-a-builtins.md §A.3 — vec value flows through a `let`
// binding and out via `vec-get`. Distinct from inline-literal access; the
// vec escapes the literal context, gets bound, and is then accessed.
// (carry: legacy/sketch_port.rs::sketch_vec_in_let)
#[test]
fn primitive_vec_let_bound_then_get() {
    repl_prims("(let [xs [10 20 30]] (vec-get xs 0))\n")
        .assert_stdout_contains(":primitives/Int 10");
}

// spec: spec/appendix-a-builtins.md §A.3 — push onto an empty vec literal
// (boundary case: zero-element start). Verifies that `[]` is a valid input
// to `vec-push` and that the resulting vec has the pushed value at index 0.
// (carry: legacy/sketch_port.rs::sketch_vec_push_empty)
#[test]
fn primitive_vec_push_onto_empty() {
    repl_prims("(vec-get (vec-push [] 42) 0)\n")
        .assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// §A.3 String slicing / introspection — Wave 5.5 GAP-COVER
//
// These primitives are spec'd in `appendix-a-builtins §A.3` but had zero
// e2e carry-forward after Wave 5 dedupe. Coverage was previously held
// only in `tests/legacy/ring1.rs` (now quarantined).
// =============================================================================

// spec: spec/appendix-a-builtins.md §A.3 — substring extracts [start, end)
// (carry: legacy/ring1.rs::string_substring_basic)
#[test]
fn primitive_substring_basic() {
    repl_prims("(str-len (substring \"hello world\" 6 11))\n")
        .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/appendix-a-builtins.md §A.3 — substring clamps out-of-bounds end
// (carry: legacy/ring1.rs::string_substring_clamps_end)
#[test]
fn primitive_substring_clamps_end() {
    repl_prims("(str-len (substring \"hello\" 0 100))\n")
        .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/appendix-a-builtins.md §A.3 — char-at returns single-char string
// (carry: legacy/ring1.rs::string_char_at_valid_index)
#[test]
fn primitive_char_at_valid() {
    repl_prims("(str-eq (char-at \"hello\" 1) \"e\")\n")
        .assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/appendix-a-builtins.md §A.3 — char-at OOB returns empty
// (carry: legacy/ring1.rs::string_char_at_out_of_bounds_empty)
#[test]
fn primitive_char_at_out_of_bounds_empty() {
    repl_prims("(str-len (char-at \"hello\" 100))\n")
        .assert_stdout_contains(":primitives/Int 0");
}

// spec: spec/appendix-a-builtins.md §A.3 — trim strips leading/trailing whitespace
// (carry: legacy/ring1.rs::string_trim_whitespace)
#[test]
fn primitive_trim_whitespace() {
    repl_prims("(str-eq (trim \"  hello  \") \"hello\")\n")
        .assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/appendix-a-builtins.md §A.3 — trim preserves interior whitespace
// (carry: legacy/ring1.rs::string_trim_interior_preserved)
#[test]
fn primitive_trim_interior_preserved() {
    repl_prims("(str-len (trim \"  hi there  \"))\n")
        .assert_stdout_contains(":primitives/Int 8");
}

// spec: spec/appendix-a-builtins.md §A.3 — to-upper converts ASCII letters
// (carry: legacy/ring1.rs::string_to_upper_ascii)
#[test]
fn primitive_to_upper_ascii() {
    repl_prims("(str-eq (to-upper \"hello\") \"HELLO\")\n")
        .assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/appendix-a-builtins.md §A.3 — to-lower converts ASCII letters
// (carry: legacy/ring1.rs::string_to_lower_ascii)
#[test]
fn primitive_to_lower_ascii() {
    repl_prims("(str-eq (to-lower \"HELLO\") \"hello\")\n")
        .assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/appendix-a-builtins.md §A.3 — starts-with? prefix match
// (carry: legacy/ring1.rs::string_starts_with_true)
#[test]
fn primitive_starts_with_true() {
    repl_prims("(starts-with? \"hello world\" \"hello\")\n")
        .assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/appendix-a-builtins.md §A.3 — starts-with? rejects non-prefix
// (carry: legacy/ring1.rs::string_starts_with_false)
#[test]
fn primitive_starts_with_false() {
    repl_prims("(starts-with? \"hello\" \"world\")\n")
        .assert_stdout_contains(":primitives/Bool false");
}

// spec: spec/appendix-a-builtins.md §A.3 — ends-with? suffix match
// (carry: legacy/ring1.rs::string_ends_with_true)
#[test]
fn primitive_ends_with_true() {
    repl_prims("(ends-with? \"hello world\" \"world\")\n")
        .assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/appendix-a-builtins.md §A.3 — ends-with? rejects non-suffix
// (carry: legacy/ring1.rs::string_ends_with_false)
#[test]
fn primitive_ends_with_false() {
    repl_prims("(ends-with? \"hello\" \"world\")\n")
        .assert_stdout_contains(":primitives/Bool false");
}

// spec: spec/appendix-a-builtins.md §A.3 — contains? substring search
// (carry: legacy/ring1.rs::string_contains_true)
#[test]
fn primitive_contains_true() {
    repl_prims("(contains? \"hello world\" \"lo wo\")\n")
        .assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/appendix-a-builtins.md §A.3 — contains? rejects absent substring
// (carry: legacy/ring1.rs::string_contains_false)
#[test]
fn primitive_contains_false() {
    repl_prims("(contains? \"hello\" \"xyz\")\n")
        .assert_stdout_contains(":primitives/Bool false");
}

// spec: spec/appendix-a-builtins.md §A.3 — replace substitutes occurrences
// (carry: legacy/ring1.rs::string_replace_multiple)
#[test]
fn primitive_replace_multiple() {
    repl_prims("(str-eq (replace \"foo bar foo\" \"foo\" \"baz\") \"baz bar baz\")\n")
        .assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/appendix-a-builtins.md §A.3 — replace with absent needle is no-op
// (carry: legacy/ring1.rs::string_replace_missing_needle)
#[test]
fn primitive_replace_missing_needle() {
    repl_prims("(str-eq (replace \"hello\" \"xyz\" \"abc\") \"hello\")\n")
        .assert_stdout_contains(":primitives/Bool true");
}

// spec: spec/appendix-a-builtins.md §A.3 — split partitions by separator
// (carry: legacy/ring1.rs::string_split_produces_parts)
#[test]
fn primitive_split_produces_parts() {
    repl_prims("(vec-len (split \"a,b,c\" \",\"))\n")
        .assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/appendix-a-builtins.md §A.3 — join inverse of split
// (carry: legacy/ring1.rs::string_join_reassembles)
#[test]
fn primitive_join_reassembles() {
    repl_prims("(str-eq (join \",\" (split \"a,b,c\" \",\")) \"a,b,c\")\n")
        .assert_stdout_contains(":primitives/Bool true");
}

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forwards (chunks 1-3)
// =============================================================================

// spec: spec/appendix-a-builtins.md §A.3 — chained str-concat exercises
// nested str-concat through two invocations: `(str-concat (str-concat "a"
// "b") "c")` produces "abc". Distinct from `primitive_str_concat` (single
// invocation) and `let_heap_typed_results_string_concat` in
// spec_04_expressions.rs (let-bound composition through bindings).
// (carry: legacy/ring1.rs::string_concat_chained)
#[test]
fn primitive_str_concat_chained_two_levels() {
    repl_prims("(str-len (str-concat (str-concat \"a\" \"b\") \"c\"))\n")
        .assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/appendix-a-builtins.md §A.3 — parse-int returns
// `(Some n)` for a numeric string. Zero parse-int coverage existed
// in any e2e file; parse-int is normatively a primitive returning
// `(primitives/Option Int)`.
// (carry: legacy/ring1.rs::parse_int_valid)
#[test]
fn primitive_parse_int_valid() {
    // `parse-int` returns `primitives/Option`; the imported `Some`/`None`
    // come from the PrimitivesOnly prelude and dispatch against the
    // primitive Option variants directly (no user-defined `Option` here).
    repl_prims(
        "(match (parse-int \"42\") [(Some n) n None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/appendix-a-builtins.md §A.3 — parse-int returns `None`
// for a non-numeric string. Negative companion to
// `primitive_parse_int_valid`; the None-returning path is the
// spec-mandated failure mode of a pure parse primitive.
// (carry: legacy/ring1.rs::parse_int_invalid)
#[test]
fn primitive_parse_int_invalid() {
    repl_prims(
        "(match (parse-int \"not-a-number\") [(Some n) n None (sub-i64 0 1)])\n",
    )
    .assert_stdout_contains(":primitives/Int -1");
}

// spec: spec/appendix-a-builtins.md §A.3 — vec-set leaves non-target
// positions untouched. Distinct from `primitive_vec_set_preserves_len`
// (length only) and from `vec_set_cow_preserves_original` in
// spec_12_runtime.rs (asserts the ORIGINAL vec is untouched, not the
// new vec's other positions). The other-positions-of-the-set-result
// angle is a distinct positive shape.
// (carry: legacy/ring1.rs::vec_set_preserves_other_elements)
#[test]
fn primitive_vec_set_other_positions_preserved() {
    repl_prims(
        "(let [v (vec-set [10 20 30] 1 99)] (add-i64 (vec-get v 0) (vec-get v 2)))\n",
    )
    .assert_stdout_contains(":primitives/Int 40");
}

// spec: spec/appendix-a-builtins.md §A.3 — vec-get returns the element
// at a heap-typed-element vec position. `primitive_vec_get_first` uses
// Int elements; the Vec-of-String shape exercises a distinct
// RC-aware angle (the get must increment the String's RC and pass
// ownership to the caller).
// (carry: legacy/ring1.rs::vec_of_strings_get)
#[test]
fn primitive_vec_get_string_element() {
    repl_prims("(str-len (vec-get [\"hello\" \"world\"] 0))\n")
        .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/appendix-a-builtins.md §A.3 — vec-get at a middle index.
// `primitive_vec_get_first` covers index 0 only; the middle-vs-end
// positional indexing is conventionally coverage-distinct (the
// first/middle/last triple). Mild ambiguity per audit /sprint flag —
// `/sprint` retained as GAP-COVER for the family-completeness shape.
// (carry: legacy/ring1.rs::vec_get_middle)
#[test]
fn primitive_vec_get_middle_index() {
    repl_prims("(vec-get [10 20 30] 1)\n")
        .assert_stdout_contains(":primitives/Int 20");
}

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forwards (chunk 4)
// =============================================================================

// spec: spec/appendix-a-builtins.md §A.3 — vec-set at the LAST index.
// `primitive_vec_set_preserves_len` covers index 1 only;
// `primitive_vec_set_other_positions_preserved` covers untouched-positions
// after a middle-index set. The first/middle/last positional triple
// convention completes coverage with the last-index angle. Mild
// ambiguity per audit /sprint flag — retained as GAP-COVER for
// family-completeness with chunk-3 `primitive_vec_get_middle_index`.
// (carry: legacy/ring1.rs::vec_set_last)
#[test]
fn primitive_vec_set_last_index() {
    repl_prims("(vec-get (vec-set [1 2 3] 2 99) 2)\n")
        .assert_stdout_contains(":primitives/Int 99");
}

// spec: spec/appendix-a-builtins.md §A.3 — chained vec-push through three
// nested levels onto an empty vec literal. `primitive_vec_push_onto_empty`
// covers a single push onto `[]`; the 3-level chain `(vec-push (vec-push
// (vec-push [] 1) 2) 3)` exercises repeat allocation through the
// empty → 1-elem → 2-elem → 3-elem growth chain (RC + cap-growth at
// each step). Mirror of chunk-1 `primitive_str_concat_chained_two_levels`
// but for the Vec/heap-backed-collection growth path.
// (carry: legacy/ring1.rs::vec_push_chain)
#[test]
fn primitive_vec_push_chain_three_levels() {
    repl_prims("(vec-len (vec-push (vec-push (vec-push [] 1) 2) 3))\n")
        .assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/appendix-a-builtins.md §A.3 — `string-identity` is a
// normative primitive (the entry on line 92 of appendix-a-builtins.md
// explicitly cites this exact test name). It is the identity function on
// `String`, used by the Display impl. Zero spec-anchored e2e coverage
// existed before this carry — the Wave 5.6 ring1.rs audit flagged the
// gap in cluster Y3.
// (carry: legacy/ring1.rs::string_identity_returns_same)
#[test]
fn primitive_string_identity_returns_same() {
    repl_prims("(str-len (string-identity \"hello\"))\n")
        .assert_stdout_contains(":primitives/Int 5");
}
