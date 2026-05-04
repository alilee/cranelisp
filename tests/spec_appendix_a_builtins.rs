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

// spec: spec/appendix-a-builtins.md §A.3 — not true → false
#[test]
fn primitive_not_true() {
    repl_prims("(not true)\n").assert_stdout_contains(":primitives/Bool false");
}

// spec: spec/appendix-a-builtins.md §A.3 — not false → true
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
