//! Operator wrapper functions — backend-emitted-call targets.
//!
//! Per Decision 43 + `design/arch/facades/intrinsics.md`: these are NOT
//! user-callable primitives. They are wrappers the backend emits direct
//! `Linkage::Import` calls to when an operator is referenced as a
//! first-class value (`(let [f +] (f 1 2))`, spec §7.6). The JIT registers
//! them under `cranelisp_op_*` names (`is_runtime: true` — not visible in
//! the synthetic `primitives` module's symbol table; addressed only by the
//! backend's operator-as-value codegen path in
//! `crates/cranelisp-backend/src/compiler/literals.rs::operator_extern_name`).
//!
//! Per `facades/primitives.md` invariant 3, these parallel forms are
//! "retired by D43's Phase 4" — the user-callable `add-i64`-style names
//! become the canonical addressable form. Until that retirement lands they
//! live here in intrinsics, alongside the other backend-emitted-call
//! targets. Wave 3b-2d.2b lifted them from
//! `cranelisp-runtime/src/primitives/int.rs`; `cranelisp-runtime` keeps a
//! thin re-export shim until that crate retires per FIXME 0150 Phase 5.

#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_op_add(a: i64, b: i64) -> i64 {
    a.wrapping_add(b)
}

#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_op_sub(a: i64, b: i64) -> i64 {
    a.wrapping_sub(b)
}

#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_op_mul(a: i64, b: i64) -> i64 {
    a.wrapping_mul(b)
}

#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_op_div(a: i64, b: i64) -> i64 {
    if b == 0 {
        eprintln!("panic: integer division by zero");
        std::process::exit(1);
    }
    // Guard against Int.MIN / -1 overflow.
    if a == i64::MIN && b == -1 {
        eprintln!("panic: integer overflow in /");
        std::process::exit(1);
    }
    a / b
}

#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_op_eq(a: i64, b: i64) -> i64 {
    if a == b { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_op_neq(a: i64, b: i64) -> i64 {
    if a != b { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_op_lt(a: i64, b: i64) -> i64 {
    if a < b { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_op_gt(a: i64, b: i64) -> i64 {
    if a > b { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_op_le(a: i64, b: i64) -> i64 {
    if a <= b { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_op_ge(a: i64, b: i64) -> i64 {
    if a >= b { 1 } else { 0 }
}
