//! Ring 0 monomorphic primitive Rust shim fns — user-callable.
//!
//! Per Decision 43 + FIXME 0174 (`design/arch/fixmes/0174-...uniform-primitive-dispatch.md`) +
//! `design/arch/facades/backend.md` §"Non-goals / forbidden patterns": every
//! Ring 0 primitive (`add-i64` … `not`) MUST be addressable as an ordinary
//! `ModuleEntry::Def` in the synthetic `primitives` symbol table — with a
//! `got_slot: Some(_)` and a code pointer registered in that slot. The standard
//! GOT-indirect call codegen path resolves the call to the Def, reads the slot,
//! emits `call_indirect`. The pre-D43 shape (backend name-matching `"add-i64"`
//! and emitting inline IR as the ONLY emission path) is forbidden — it
//! broke mappable paths like `(let [f not] (f true))` because the primitive
//! had no symbol-table entry to capture.
//!
//! These Rust shims are the **fallback** emission targets — when backend's
//! `primitives_inline.rs` does not match the call site's symbol, the GOT
//! slot points to one of these shims and `call_indirect` lands here. When
//! backend DOES match the symbol (`primitives_inline.rs::try_emit_inline_primitive`
//! returns `Some(value)`), the call site emits inline Cranelift IR instead
//! — semantics identical, code-size and dispatch-cost different.
//!
//! ## ABI / encoding
//!
//! Every Ring 0 primitive operates on i64 at the Cranelift boundary:
//! - `Int` values: native i64.
//! - `Float` values: f64 bitcast to i64 (same memory, different type discipline).
//!   Backend bitcasts at call boundaries; the shim does so internally.
//! - `Bool` values: 0 (false) or 1 (true) as i64.
//!
//! Comparison ops return `1` (true) or `0` (false) as i64 — matching the
//! Cranelift `icmp` / `fcmp` `uextend i64` shape that `primitives_inline.rs`
//! emits.
//!
//! ## Division-by-zero
//!
//! `div-i64` panics on `b == 0` or on the `i64::MIN / -1` overflow case via
//! `cranelisp_intrinsics::panic::runtime_panic`. The inline-substitution
//! path emits a `runtime_panic` call directly (see `primitives_inline.rs`).
//! The shim must produce the same observable behaviour — store a panic
//! message on the thread-local error slot, return `0` as a dummy. The
//! REPL/`--run` driver checks `take_runtime_error()` after JIT-call return.

use cranelisp_intrinsics::panic::runtime_panic;

// =============================================================================
// Integer arithmetic — Type::Fn([Int, Int], Int)
// =============================================================================

#[unsafe(export_name = "add-i64")]
pub(crate) extern "C" fn add_i64(a: i64, b: i64) -> i64 {
    a.wrapping_add(b)
}

#[unsafe(export_name = "sub-i64")]
pub(crate) extern "C" fn sub_i64(a: i64, b: i64) -> i64 {
    a.wrapping_sub(b)
}

#[unsafe(export_name = "mul-i64")]
pub(crate) extern "C" fn mul_i64(a: i64, b: i64) -> i64 {
    a.wrapping_mul(b)
}

/// Checked integer division. Matches `primitives_inline.rs::emit_checked_div`
/// semantics: panic on `b == 0` and on the `i64::MIN / -1` overflow case.
#[unsafe(export_name = "div-i64")]
pub(crate) extern "C" fn div_i64(a: i64, b: i64) -> i64 {
    if b == 0 {
        let msg = b"division by zero";
        // runtime_panic is `pub extern "C"`; the call itself is safe — it
        // copies into a thread-local error slot.
        runtime_panic(msg.as_ptr(), msg.len());
        return 0;
    }
    if a == i64::MIN && b == -1 {
        // The inline path uses the same "division by zero" message for the
        // overflow case (see `emit_checked_div`); match that exactly so the
        // mappable-path and inline-path error strings are observable-equivalent.
        let msg = b"division by zero";
        runtime_panic(msg.as_ptr(), msg.len());
        return 0;
    }
    a / b
}

// =============================================================================
// Float arithmetic — Type::Fn([Float, Float], Float)
//
// At the Cranelift boundary floats live in i64 registers (bitcast). The shim
// bitcasts back to f64, performs the operation, and bitcasts the result back
// to i64. f64::from_bits / f64::to_bits are total, well-defined, and free of
// NaN-normalisation surprises (they preserve bit patterns).
// =============================================================================

#[unsafe(export_name = "add-f64")]
pub(crate) extern "C" fn add_f64(a: i64, b: i64) -> i64 {
    let result = f64::from_bits(a as u64) + f64::from_bits(b as u64);
    result.to_bits() as i64
}

#[unsafe(export_name = "sub-f64")]
pub(crate) extern "C" fn sub_f64(a: i64, b: i64) -> i64 {
    let result = f64::from_bits(a as u64) - f64::from_bits(b as u64);
    result.to_bits() as i64
}

#[unsafe(export_name = "mul-f64")]
pub(crate) extern "C" fn mul_f64(a: i64, b: i64) -> i64 {
    let result = f64::from_bits(a as u64) * f64::from_bits(b as u64);
    result.to_bits() as i64
}

#[unsafe(export_name = "div-f64")]
pub(crate) extern "C" fn div_f64(a: i64, b: i64) -> i64 {
    let result = f64::from_bits(a as u64) / f64::from_bits(b as u64);
    result.to_bits() as i64
}

// =============================================================================
// Integer comparison — Type::Fn([Int, Int], Bool); return 1 / 0 as i64.
// =============================================================================

#[unsafe(export_name = "eq-i64")]
pub(crate) extern "C" fn eq_i64(a: i64, b: i64) -> i64 {
    (a == b) as i64
}

#[unsafe(export_name = "lt-i64")]
pub(crate) extern "C" fn lt_i64(a: i64, b: i64) -> i64 {
    (a < b) as i64
}

#[unsafe(export_name = "gt-i64")]
pub(crate) extern "C" fn gt_i64(a: i64, b: i64) -> i64 {
    (a > b) as i64
}

#[unsafe(export_name = "le-i64")]
pub(crate) extern "C" fn le_i64(a: i64, b: i64) -> i64 {
    (a <= b) as i64
}

#[unsafe(export_name = "ge-i64")]
pub(crate) extern "C" fn ge_i64(a: i64, b: i64) -> i64 {
    (a >= b) as i64
}

#[unsafe(export_name = "neq-i64")]
pub(crate) extern "C" fn neq_i64(a: i64, b: i64) -> i64 {
    (a != b) as i64
}

// =============================================================================
// Float comparison — Type::Fn([Float, Float], Bool); return 1 / 0 as i64.
// =============================================================================

#[unsafe(export_name = "eq-f64")]
pub(crate) extern "C" fn eq_f64(a: i64, b: i64) -> i64 {
    (f64::from_bits(a as u64) == f64::from_bits(b as u64)) as i64
}

#[unsafe(export_name = "lt-f64")]
pub(crate) extern "C" fn lt_f64(a: i64, b: i64) -> i64 {
    (f64::from_bits(a as u64) < f64::from_bits(b as u64)) as i64
}

#[unsafe(export_name = "gt-f64")]
pub(crate) extern "C" fn gt_f64(a: i64, b: i64) -> i64 {
    (f64::from_bits(a as u64) > f64::from_bits(b as u64)) as i64
}

#[unsafe(export_name = "le-f64")]
pub(crate) extern "C" fn le_f64(a: i64, b: i64) -> i64 {
    (f64::from_bits(a as u64) <= f64::from_bits(b as u64)) as i64
}

#[unsafe(export_name = "ge-f64")]
pub(crate) extern "C" fn ge_f64(a: i64, b: i64) -> i64 {
    (f64::from_bits(a as u64) >= f64::from_bits(b as u64)) as i64
}

#[unsafe(export_name = "neq-f64")]
pub(crate) extern "C" fn neq_f64(a: i64, b: i64) -> i64 {
    (f64::from_bits(a as u64) != f64::from_bits(b as u64)) as i64
}

// =============================================================================
// Boolean — Type::Fn([Bool], Bool) / Type::Fn([Bool, Bool], Bool).
// =============================================================================

/// XOR with 1 flips 0 ↔ 1; mask with 1 keeps Bool encoding strict in case the
/// caller hands in a "truthy" non-canonical bool. Matches the inline IR
/// (`bxor args[0] 1`) in `primitives_inline.rs::emit_not`.
#[unsafe(export_name = "not")]
pub(crate) extern "C" fn not(b: i64) -> i64 {
    (b ^ 1) & 1
}

#[unsafe(export_name = "eq-bool")]
pub(crate) extern "C" fn eq_bool(a: i64, b: i64) -> i64 {
    (a == b) as i64
}

#[unsafe(export_name = "neq-bool")]
pub(crate) extern "C" fn neq_bool(a: i64, b: i64) -> i64 {
    (a != b) as i64
}

// =============================================================================
// JIT-registration table — RETIRED at S68 Wave 4.
//
// `ring0_jit_symbols()` is gone. The (kebab-case symbol name → raw fn ptr)
// mapping is harvested by `crate::extern_shims()` (called from
// `PRIMITIVES_TABLE`'s `LazyLock` initialiser) — Decision 0048 §"Shape"
// places the canonical fn-ptr storage in the per-module `GotTable`, indexed
// by `ModuleEntry::Def.got_slot`. Backend reaches primitives through the
// standard GOT-indirect cross-module dispatch path (Decision 23 two-GOT
// model + Decision 31 GOT-indirect dispatch), enforced structurally by the
// `cranelisp-backend → cranelisp-primitives` dep-ban (Decision 0048
// §"Structural invariant — backend dep-ban").
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_i64_basic() {
        assert_eq!(add_i64(2, 3), 5);
        assert_eq!(add_i64(-1, 1), 0);
    }

    #[test]
    fn sub_i64_basic() {
        assert_eq!(sub_i64(5, 2), 3);
        assert_eq!(sub_i64(0, 7), -7);
    }

    #[test]
    fn mul_i64_basic() {
        assert_eq!(mul_i64(3, 4), 12);
        assert_eq!(mul_i64(-2, 3), -6);
    }

    #[test]
    fn div_i64_basic() {
        assert_eq!(div_i64(10, 2), 5);
        assert_eq!(div_i64(-7, 2), -3); // truncated toward zero (matches sdiv)
    }

    #[test]
    fn add_f64_round_trip() {
        let a: f64 = 1.5;
        let b: f64 = 2.25;
        let r = add_f64(a.to_bits() as i64, b.to_bits() as i64);
        assert_eq!(f64::from_bits(r as u64), 3.75);
    }

    #[test]
    fn eq_i64_returns_bool_i64() {
        assert_eq!(eq_i64(3, 3), 1);
        assert_eq!(eq_i64(3, 4), 0);
    }

    #[test]
    fn lt_i64_basic() {
        assert_eq!(lt_i64(1, 2), 1);
        assert_eq!(lt_i64(2, 1), 0);
        assert_eq!(lt_i64(1, 1), 0);
    }

    #[test]
    fn not_flips_bool() {
        assert_eq!(not(0), 1);
        assert_eq!(not(1), 0);
    }

    #[test]
    fn eq_bool_basic() {
        assert_eq!(eq_bool(1, 1), 1);
        assert_eq!(eq_bool(0, 1), 0);
    }

    #[test]
    fn neq_f64_basic() {
        let a: f64 = 1.5;
        let b: f64 = 2.5;
        assert_eq!(neq_f64(a.to_bits() as i64, b.to_bits() as i64), 1);
        assert_eq!(neq_f64(a.to_bits() as i64, a.to_bits() as i64), 0);
    }
}
