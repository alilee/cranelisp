// spec_appendix_a_bitwise.rs — bitwise integer intrinsics (Sprint 91, Thread C
// FIXME 0416). RED-first e2e: these compile and fail at RUNTIME today because the
// `bit-and`/`bit-or`/`bit-xor`/`bit-not`/`shl`/`shr`/`popcount` primitives are not
// yet registered (Wave 4 lands the primitive rows + 1:1 CLIF lowering). The
// failure shape is "unbound/undefined `bit-and`" until then.
//
// Spec: appendix-a-builtins.md §A.3 — Bitwise integer operations. Int is signed
// 64-bit two's-complement (§A.1). `shr` is arithmetic (sign-extending) for the
// current signed `Int`; shift count is taken modulo 64; `bit-not` complements all
// 64 bits; `popcount` counts set bits across all 64.
//
// The language has only DECIMAL integer literals (spec §1.3.1 — no `0b`/`0x`),
// so bit patterns are written as their decimal values:
//   0b1100 = 12,  0b1010 = 10,  AND = 8,  OR = 14,  XOR = 6,  0b1011 = 11.
//
// Free-standing: PrimitivesOnly prelude (the bitwise primitives live in the
// synthetic `primitives` module alongside `add-i64`); zero stdlib dependency.

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

// spec: spec/appendix-a-builtins.md §A.3 — `bit-and` `(Fn [Int Int] Int)` (CLIF
// `band`). 12 & 10 = 8; AND with 0 = 0; AND with -1 (all bits set) = identity.
#[test]
fn bit_and_basic_and_edge() {
    repl_prims(
        "(bit-and 12 10)\n\
         (bit-and 12 0)\n\
         (bit-and 12 -1)\n",
    )
    .assert_stdout_contains_all(&[
        ":primitives/Int 8",
        ":primitives/Int 0",
        ":primitives/Int 12",
    ]);
}

// spec: spec/appendix-a-builtins.md §A.3 — `bit-or` `(Fn [Int Int] Int)` (CLIF `bor`).
// 12 | 10 = 14; OR with 0 = identity; OR with -1 = -1.
#[test]
fn bit_or_basic_and_edge() {
    repl_prims(
        "(bit-or 12 10)\n\
         (bit-or 12 0)\n\
         (bit-or 12 -1)\n",
    )
    .assert_stdout_contains_all(&[
        ":primitives/Int 14",
        ":primitives/Int 12",
        ":primitives/Int -1",
    ]);
}

// spec: spec/appendix-a-builtins.md §A.3 — `bit-xor` `(Fn [Int Int] Int)` (CLIF
// `bxor`). 12 ^ 10 = 6; XOR self = 0; XOR -1 = bit-not (here ~12 = -13).
#[test]
fn bit_xor_basic_and_edge() {
    repl_prims(
        "(bit-xor 12 10)\n\
         (bit-xor 12 12)\n\
         (bit-xor 12 -1)\n",
    )
    .assert_stdout_contains_all(&[
        ":primitives/Int 6",
        ":primitives/Int 0",
        ":primitives/Int -13",
    ]);
}

// spec: spec/appendix-a-builtins.md §A.3 — `bit-not` `(Fn [Int] Int)` (CLIF `bnot`):
// full-width 64-bit complement; `(bit-not x)` = `(- (- x) 1)`. `(bit-not 0)` = -1,
// `(bit-not 12)` = -13, `(bit-not -1)` = 0.
#[test]
fn bit_not_full_width_twos_complement() {
    repl_prims(
        "(bit-not 0)\n\
         (bit-not 12)\n\
         (bit-not -1)\n",
    )
    .assert_stdout_contains_all(&[
        ":primitives/Int -1",
        ":primitives/Int -13",
        ":primitives/Int 0",
    ]);
}

// spec: spec/appendix-a-builtins.md §A.3 — `shl` `(Fn [Int Int] Int)` (CLIF `ishl`):
// left shift, vacated low bits zero-filled. `(shl 1 3)` = 8; shifting a bit into
// bit 63 produces a negative value (the sign bit). `(shl 1 63)` = i64::MIN =
// -9223372036854775808.
#[test]
fn shl_zero_fill_and_sign_bit() {
    repl_prims(
        "(shl 1 3)\n\
         (shl 1 63)\n",
    )
    .assert_stdout_contains_all(&[":primitives/Int 8", ":primitives/Int -9223372036854775808"]);
}

// spec: spec/appendix-a-builtins.md §A.3 — `shr` `(Fn [Int Int] Int)` is ARITHMETIC
// for signed `Int` (sign replicated; CLIF `sshr`). `(shr -8 1)` = -4 (NOT a large
// positive value, which a logical shift would give); `(shr 8 1)` = 4.
#[test]
fn shr_arithmetic_signed_int() {
    repl_prims(
        "(shr -8 1)\n\
         (shr 8 1)\n",
    )
    .assert_stdout_contains_all(&[":primitives/Int -4", ":primitives/Int 4"])
    // Negative: an arithmetic shift of -8 must NOT produce the logical-shift
    // result (a huge positive value); the sign bit is replicated.
    .assert_stdout_does_not_contain(":primitives/Int 9223372036854775804");
}

// spec: spec/appendix-a-builtins.md §A.3 — "Shift count" — the shift amount is taken
// modulo 64. `(shl 1 64)` ≡ `(shl 1 0)` = 1.
#[test]
fn shift_count_mod_64() {
    repl_prims(
        "(shl 1 64)\n\
         (shl 1 0)\n",
    )
    .assert_stdout_contains_all(&[":primitives/Int 1"]);
}

// spec: spec/appendix-a-builtins.md §A.3 — `popcount` `(Fn [Int] Int)` (CLIF
// `popcnt`): set-bit count across the full 64 bits. `(popcount 0)` = 0;
// `(popcount -1)` = 64 (all bits set); `(popcount 11)` = 3 (0b1011).
#[test]
fn popcount_basic_and_full_width() {
    repl_prims(
        "(popcount 0)\n\
         (popcount -1)\n\
         (popcount 11)\n",
    )
    .assert_stdout_contains_all(&[
        ":primitives/Int 0",
        ":primitives/Int 64",
        ":primitives/Int 3",
    ]);
}

// spec: spec/appendix-a-builtins.md §A.3 — a bitwise expression is mode-equivalent
// across REPL / `--run` / `--link`. Floor: the inline primitive must lower
// identically in every mode. `(bit-or (shl 1 3) (bit-and 12 10))` = 8 | 8 = 8.
//
// `main` MUST return `(Fn [] (IO _))` for `--run`/`--link` (a bare `Int` return
// type-errors in batch mode), so the bitwise result is wrapped in `(Pure …)` —
// the same `main` shape `tests/build_confidence.rs::mode_equiv_primitive_arithmetic`
// uses. The `run_through_all_modes` helper observes the wrapped value as the exit
// code in `--run`/`--link` and as the `:primitives/Int` echo in the REPL; the
// assertion that the bitwise op produces 8 in EVERY mode is preserved.
#[test]
fn bitwise_run_through_all_modes() {
    helpers::e2e::run_through_all_modes(
        "(defn main [] (Pure (bit-or (shl 1 3) (bit-and 12 10))))",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(8);
}
