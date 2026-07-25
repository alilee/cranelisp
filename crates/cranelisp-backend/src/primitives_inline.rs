//! Ring 0 inline-substitution table — a name-keyed dispatch optimisation.
//!
//! Per Decision 43 + `design/arch/facades/backend.md` §"Non-goals / forbidden
//! patterns": this file holds ONLY the name-keyed inline-Cranelift-IR emission
//! table for the Ring 0 primitives. It is **not** a dispatch path — the
//! dispatch path is the standard `compile_direct_call` keyed entry fetch
//! (`entry_at` → `callable_got_slot()`) -> GOT-indirect call that every user
//! function uses (the S110-W1-deleted `resolve_got_target` scan no longer runs).
//! `try_emit_inline_primitive`
//! is consulted **before** that fallback as an opportunistic optimisation: if
//! the call site's symbol matches the inline table, emit inline CLIF; if not,
//! return `None` and let the caller fall through to the standard path.
//!
//! Backend has no trait knowledge: the substitution is keyed on `Symbol` only,
//! never on `(trait, method, type)` triples (forbidden pattern). The GOT slot
//! for each primitive is always populated, so mappable paths
//! (`(let [f not] (f true))`) and call-by-symbol work whether or not the call
//! site is in the inline table — the inline path is a code-size + dispatch-cost
//! win, not a correctness requirement.
//!
//! Ring 0 primitives covered (the 30 names that participate in inline
//! substitution):
//! ```text
//!   add-i64, sub-i64, mul-i64, div-i64
//!   add-f64, sub-f64, mul-f64, div-f64
//!   eq-i64, lt-i64, gt-i64, le-i64, ge-i64, neq-i64
//!   eq-f64, lt-f64, gt-f64, le-f64, ge-f64, neq-f64
//!   not, eq-bool, neq-bool
//!   bit-and, bit-or, bit-xor, bit-not, shl, shr, popcount
//! ```

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use cranelisp_types::{CranelispError, ErrorLocation, Span};

/// Try to emit inline Cranelift IR for a Ring 0 primitive call.
///
/// Returns:
/// - `Some(Ok(value))` — the symbol matched the inline table; `value` is the
///   result of the inline emission.
/// - `Some(Err(_))` — the symbol matched but inline emission failed (e.g.,
///   arity mismatch, `panic_func_id` missing for `div-i64`).
/// - `None` — the symbol is NOT in the inline table; the caller MUST fall
///   through to the standard GOT-indirect call path. This is not an error.
///
/// The `name` is a monomorphic primitive name such as `add-i64` or `mul-f64`.
/// The name alone determines which Cranelift instruction is emitted — no
/// separate operand type is needed.
///
/// All values are i64 at the Cranelift boundary; floats are bitcast to/from
/// i64 as needed.
///
/// Forbidden-patterns clause (`facades/backend.md`): callers MUST handle the
/// `None` case by falling through to GOT-indirect dispatch — they MUST NOT
/// raise an error on `None`. Returning an error on `None` would re-introduce
/// the name-keyed dispatch-only shape that this rename eliminated.
///
/// Narrowed to `pub(crate)` in S75 W3 — codegen-site inline-substitution
/// emitter; in-crate callers only (`compiler::apply`, `compiler::control_flow`).
pub(crate) fn try_emit_inline_primitive<M: Module>(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[Value],
    span: Span,
    module: &mut M,
    panic_func_id: Option<FuncId>,
) -> Option<Result<Value, CranelispError>> {
    let result = match name {
        // Integer arithmetic
        "add-i64" => emit_binary_int(builder, name, args, span, |b, l, r| b.ins().iadd(l, r)),
        "sub-i64" => emit_binary_int(builder, name, args, span, |b, l, r| b.ins().isub(l, r)),
        "mul-i64" => emit_binary_int(builder, name, args, span, |b, l, r| b.ins().imul(l, r)),
        "div-i64" => emit_checked_div(builder, name, args, span, module, panic_func_id),

        // Float arithmetic
        "add-f64" => emit_binary_float(builder, name, args, span, |b, l, r| b.ins().fadd(l, r)),
        "sub-f64" => emit_binary_float(builder, name, args, span, |b, l, r| b.ins().fsub(l, r)),
        "mul-f64" => emit_binary_float(builder, name, args, span, |b, l, r| b.ins().fmul(l, r)),
        "div-f64" => emit_binary_float(builder, name, args, span, |b, l, r| b.ins().fdiv(l, r)),

        // Integer comparisons (return Bool as i64)
        "eq-i64" => emit_int_cmp(builder, name, args, IntCC::Equal, span),
        "lt-i64" => emit_int_cmp(builder, name, args, IntCC::SignedLessThan, span),
        "gt-i64" => emit_int_cmp(builder, name, args, IntCC::SignedGreaterThan, span),
        "le-i64" => emit_int_cmp(builder, name, args, IntCC::SignedLessThanOrEqual, span),
        "ge-i64" => emit_int_cmp(builder, name, args, IntCC::SignedGreaterThanOrEqual, span),

        // Float comparisons (return Bool as i64)
        "eq-f64" => emit_float_cmp(builder, name, args, FloatCC::Equal, span),
        "lt-f64" => emit_float_cmp(builder, name, args, FloatCC::LessThan, span),
        "gt-f64" => emit_float_cmp(builder, name, args, FloatCC::GreaterThan, span),
        "le-f64" => emit_float_cmp(builder, name, args, FloatCC::LessThanOrEqual, span),
        "ge-f64" => emit_float_cmp(builder, name, args, FloatCC::GreaterThanOrEqual, span),

        // Boolean not
        "not" => emit_not(builder, args, span),

        // Boolean equality (Ring 2A): icmp eq on i64 0/1 values.
        "eq-bool" => emit_int_cmp(builder, name, args, IntCC::Equal, span),

        // Inequality (default method for Eq.!=)
        "neq-i64" => emit_int_cmp(builder, name, args, IntCC::NotEqual, span),
        "neq-f64" => emit_float_cmp(builder, name, args, FloatCC::NotEqual, span),
        "neq-bool" => emit_int_cmp(builder, name, args, IntCC::NotEqual, span),

        // Bitwise integer operations (FIXME 0416, S91). Each maps 1:1 to a
        // Cranelift instruction over i64 (the `Int` representation; no bitcast).
        // All are total over i64 — no panic guard, `module`/`panic_func_id`
        // unused. Shift counts are masked mod 64 by Cranelift's `ishl`/`sshr`,
        // so codegen does NOT emit an explicit `band(amt, 63)`.
        "bit-and" => emit_binary_int(builder, name, args, span, |b, l, r| b.ins().band(l, r)),
        "bit-or" => emit_binary_int(builder, name, args, span, |b, l, r| b.ins().bor(l, r)),
        "bit-xor" => emit_binary_int(builder, name, args, span, |b, l, r| b.ins().bxor(l, r)),
        "shl" => emit_binary_int(builder, name, args, span, |b, v, amt| b.ins().ishl(v, amt)),
        // `shr` → arithmetic (sign-extending) shift, because the only int type
        // today is signed `Int`. The right-shift kind is determined by operand
        // representation, not the op name — a future unsigned type mints its own
        // monomorphic name (e.g. `ushr-u64` → `ushr`).
        "shr" => emit_binary_int(builder, name, args, span, |b, v, amt| b.ins().sshr(v, amt)),
        "bit-not" => emit_unary_int(builder, name, args, span, |b, x| b.ins().bnot(x)),
        "popcount" => emit_unary_int(builder, name, args, span, |b, x| b.ins().popcnt(x)),

        // Not in the inline table — caller falls through to GOT-indirect.
        _ => return None,
    };
    Some(result)
}

/// Check if a name is a known inline builtin primitive.
///
/// Returns true for names handled by `try_emit_inline_primitive`. Names not
/// in this set are either extern primitives (Ring 1 `str-concat`, …) or
/// user-defined fns — both resolved via the standard GOT-indirect path.
///
/// Retained as a callable predicate for backend dispatch sites that need to
/// branch BEFORE calling `try_emit_inline_primitive` (e.g., to choose an arg
/// compilation strategy — NeverHeap inline operands vs consuming heap externs).
/// New callers should prefer matching on the `Option` return of
/// `try_emit_inline_primitive` directly.
///
/// Narrowed to `pub(crate)` in S75 W3 — codegen-site predicate; in-crate only.
pub(crate) fn is_known_builtin(name: &str) -> bool {
    matches!(
        name,
        "add-i64"
            | "sub-i64"
            | "mul-i64"
            | "div-i64"
            | "add-f64"
            | "sub-f64"
            | "mul-f64"
            | "div-f64"
            | "eq-i64"
            | "lt-i64"
            | "gt-i64"
            | "le-i64"
            | "ge-i64"
            | "eq-f64"
            | "lt-f64"
            | "gt-f64"
            | "le-f64"
            | "ge-f64"
            | "not"
            | "eq-bool"
            | "neq-i64"
            | "neq-f64"
            | "neq-bool"
            | "bit-and"
            | "bit-or"
            | "bit-xor"
            | "bit-not"
            | "shl"
            | "shr"
            | "popcount"
    )
}

// --- Binary integer helpers ---

/// Emit a binary integer operation. The closure receives the builder and two
/// i64 operands and returns the i64 result.
fn emit_binary_int(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[Value],
    span: Span,
    op: impl FnOnce(&mut FunctionBuilder, Value, Value) -> Value,
) -> Result<Value, CranelispError> {
    require_args(name, args, 2, span)?;
    Ok(op(builder, args[0], args[1]))
}

/// Emit a binary float operation. Bitcasts i64→f64 before the operation and
/// f64→i64 after. The closure receives the builder and two f64 operands and
/// returns the f64 result.
fn emit_binary_float(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[Value],
    span: Span,
    op: impl FnOnce(&mut FunctionBuilder, Value, Value) -> Value,
) -> Result<Value, CranelispError> {
    require_args(name, args, 2, span)?;
    let lhs = builder.ins().bitcast(types::F64, MemFlags::new(), args[0]);
    let rhs = builder.ins().bitcast(types::F64, MemFlags::new(), args[1]);
    let result_f64 = op(builder, lhs, rhs);
    Ok(builder
        .ins()
        .bitcast(types::I64, MemFlags::new(), result_f64))
}

// --- Comparison helpers ---

/// Emit an integer comparison. Returns Bool (0 or 1) as i64.
fn emit_int_cmp(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[Value],
    cc: IntCC,
    span: Span,
) -> Result<Value, CranelispError> {
    require_args(name, args, 2, span)?;
    // icmp returns i8 (0 or 1); extend to i64.
    let cmp = builder.ins().icmp(cc, args[0], args[1]);
    Ok(builder.ins().uextend(types::I64, cmp))
}

/// Emit a float comparison. Bitcasts i64→f64, compares, returns Bool as i64.
fn emit_float_cmp(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[Value],
    cc: FloatCC,
    span: Span,
) -> Result<Value, CranelispError> {
    require_args(name, args, 2, span)?;
    let lhs = builder.ins().bitcast(types::F64, MemFlags::new(), args[0]);
    let rhs = builder.ins().bitcast(types::F64, MemFlags::new(), args[1]);
    // fcmp returns i8; extend to i64.
    let cmp = builder.ins().fcmp(cc, lhs, rhs);
    Ok(builder.ins().uextend(types::I64, cmp))
}

// --- Unary operations ---

/// Emit a unary integer operation. The closure receives the builder and one
/// i64 operand and returns the i64 result. Sibling of `emit_binary_int` for the
/// 1-arg bitwise ops (`bit-not`, `popcount`); mirrors `emit_not` minus the
/// boolean XOR-with-1 specialisation.
fn emit_unary_int(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[Value],
    span: Span,
    op: impl FnOnce(&mut FunctionBuilder, Value) -> Value,
) -> Result<Value, CranelispError> {
    require_args(name, args, 1, span)?;
    Ok(op(builder, args[0]))
}

/// Emit boolean `not`: XOR with 1 flips 0↔1.
fn emit_not(
    builder: &mut FunctionBuilder,
    args: &[Value],
    span: Span,
) -> Result<Value, CranelispError> {
    require_args("not", args, 1, span)?;
    let one = builder.ins().iconst(types::I64, 1);
    Ok(builder.ins().bxor(args[0], one))
}

// --- Checked division ---

/// Emit a checked integer division with two guards:
///
/// 1. Zero divisor -- panic "division by zero"
/// 2. `i64::MIN / -1` -- panic "division by zero" (overflow)
///
/// Otherwise emit `sdiv`. See spec 12.7.3 and `design/backend/hkt-codegen.md` SS2.
fn emit_checked_div<M: Module>(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[Value],
    span: Span,
    module: &mut M,
    panic_func_id: Option<FuncId>,
) -> Result<Value, CranelispError> {
    require_args(name, args, 2, span)?;

    let panic_id = panic_func_id.ok_or_else(|| CranelispError::CodegenError {
        message: "runtime/panic not declared".into(),
        location: ErrorLocation::from_span(span),
    })?;

    let lhs = args[0];
    let rhs = args[1];

    // Check 1: division by zero
    let zero = builder.ins().iconst(types::I64, 0);
    let is_zero = builder.ins().icmp(IntCC::Equal, rhs, zero);

    let check_overflow_block = builder.create_block();
    let panic_divzero_block = builder.create_block();

    builder
        .ins()
        .brif(is_zero, panic_divzero_block, &[], check_overflow_block, &[]);

    // Panic path (division by zero): call runtime_panic.
    builder.switch_to_block(panic_divzero_block);
    builder.seal_block(panic_divzero_block);
    emit_panic_return(builder, module, panic_id, b"division by zero", span)?;

    // Check 2: i64::MIN / -1 overflow
    builder.switch_to_block(check_overflow_block);
    builder.seal_block(check_overflow_block);

    let min_val = builder.ins().iconst(types::I64, i64::MIN);
    let neg1 = builder.ins().iconst(types::I64, -1i64);
    let is_min = builder.ins().icmp(IntCC::Equal, lhs, min_val);
    let is_neg1 = builder.ins().icmp(IntCC::Equal, rhs, neg1);
    let both = builder.ins().band(is_min, is_neg1);

    let ok_block = builder.create_block();
    let panic_overflow_block = builder.create_block();

    builder
        .ins()
        .brif(both, panic_overflow_block, &[], ok_block, &[]);

    // Panic path (MIN / -1 overflow): call runtime_panic.
    builder.switch_to_block(panic_overflow_block);
    builder.seal_block(panic_overflow_block);
    emit_panic_return(builder, module, panic_id, b"division by zero", span)?;

    // OK path: emit sdiv.
    builder.switch_to_block(ok_block);
    builder.seal_block(ok_block);

    Ok(builder.ins().sdiv(lhs, rhs))
}

/// Emit a panic call with a message and return a dummy 0 value.
///
/// Helper for checked division panic blocks. Declares an anonymous data
/// section for the message string, calls runtime_panic, and returns 0.
fn emit_panic_return<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    panic_func_id: FuncId,
    msg: &[u8],
    span: Span,
) -> Result<(), CranelispError> {
    let data_id =
        module
            .declare_anonymous_data(false, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare panic data: {e}"),
                location: ErrorLocation::from_span(span),
            })?;
    let mut desc = cranelift_module::DataDescription::new();
    desc.define(msg.to_vec().into_boxed_slice());
    module
        .define_data(data_id, &desc)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to define panic data: {e}"),
            location: ErrorLocation::from_span(span),
        })?;

    let gv = module.declare_data_in_func(data_id, builder.func);
    let msg_ptr = builder.ins().global_value(types::I64, gv);
    let msg_len = builder.ins().iconst(types::I64, msg.len() as i64);

    let panic_ref = module.declare_func_in_func(panic_func_id, builder.func);
    builder.ins().call(panic_ref, &[msg_ptr, msg_len]);

    // runtime_panic sets a thread-local error flag and returns.
    // Return a dummy 0 value — the caller checks take_runtime_error().
    let dummy = builder.ins().iconst(types::I64, 0);
    builder.ins().return_(&[dummy]);

    Ok(())
}

// Per Decision 43 + FIXME 0185: backend has no trait knowledge. The
// pre-D43 `primitive_for_trait_method((TraitName, Symbol, TypeName)) ->
// Option<&'static str>` dispatch table — which mapped `(Num, "+", Int)` →
// `add-i64`, etc. — has been deleted. Trait-impl dispatch now flows
// uniformly through the impl's mangled name (e.g., `Num.+$Int`) via the
// GOT-indirect path; the inline-substitution optimisation
// (`try_emit_inline_primitive`) is keyed on Symbol only and applies when
// the typecheck stage emits `ResolvedCall::BuiltinFn { name: "add-i64" }`
// directly. FIXME 0185 tracks the typecheck-side migration that restores
// inline optimisation for primitive-implemented trait methods.

// --- Utility ---

/// Return an error if `args.len() != expected`.
fn require_args(
    name: &str,
    args: &[Value],
    expected: usize,
    span: Span,
) -> Result<(), CranelispError> {
    if args.len() != expected {
        return Err(CranelispError::CodegenError {
            message: format!(
                "primitive '{name}' requires {expected} argument(s), got {}",
                args.len()
            ),
            location: ErrorLocation::from_span(span),
        });
    }
    Ok(())
}

// Per Decision 43 + FIXME 0185: the `primitive_for_trait_method` test
// suite (14 tests) has been retired alongside the function — backend has
// no trait knowledge, so test coverage for the `(TraitName, Symbol,
// TypeName)` mapping moves to whichever crate owns the resolution
// (typecheck, per FIXME 0185).

#[cfg(test)]
mod tests {
    //! Inline-primitive lowering tests (FIXME 0416, S91 — bitwise intrinsics).
    //!
    //! Each test builds a tiny standalone JIT function whose body is exactly the
    //! `try_emit_inline_primitive` emission for one bitwise op over the function
    //! parameters, finalises it, and executes it on the host. This exercises the
    //! real CLIF lowering (`band`/`bor`/`bxor`/`ishl`/`sshr`/`bnot`/`popcnt`)
    //! end-to-end — including the Cranelift-implicit shift-count masking, which
    //! is the whole point of the mod-64 edge cases.

    use super::*;
    use crate::cache::object::build_isa;
    use cranelift_jit::{JITBuilder, JITModule};
    use cranelift_module::Linkage;

    /// Build a fresh, empty JITModule for a one-off test function.
    fn fresh_module() -> JITModule {
        // `is_pic=false` is the JIT-mode ISA (absolute addresses).
        let isa = build_isa(false).expect("host ISA");
        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        JITModule::new(builder)
    }

    /// JIT-compile and run `(name a b)` for a binary inline primitive.
    fn run_binary(name: &str, a: i64, b: i64) -> i64 {
        let mut module = fresh_module();
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let func_id = module
            .declare_function("test_binary", Linkage::Export, &sig)
            .unwrap();

        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        let mut fb_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fb_ctx);
            let block = builder.create_block();
            builder.append_block_params_for_function_params(block);
            builder.switch_to_block(block);
            builder.seal_block(block);
            let params: Vec<Value> = builder.block_params(block).to_vec();
            let result = try_emit_inline_primitive(
                &mut builder,
                name,
                &params,
                Span::new(0, 0),
                &mut module,
                None,
            )
            .expect("name in inline table")
            .expect("inline emission succeeds");
            builder.ins().return_(&[result]);
            builder.finalize();
        }
        module.define_function(func_id, &mut ctx).unwrap();
        module.clear_context(&mut ctx);
        module.finalize_definitions().unwrap();
        let code = module.get_finalized_function(func_id);
        let f: extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(code) };
        f(a, b)
    }

    /// JIT-compile and run `(name x)` for a unary inline primitive.
    fn run_unary(name: &str, x: i64) -> i64 {
        let mut module = fresh_module();
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let func_id = module
            .declare_function("test_unary", Linkage::Export, &sig)
            .unwrap();

        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        let mut fb_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fb_ctx);
            let block = builder.create_block();
            builder.append_block_params_for_function_params(block);
            builder.switch_to_block(block);
            builder.seal_block(block);
            let params: Vec<Value> = builder.block_params(block).to_vec();
            let result = try_emit_inline_primitive(
                &mut builder,
                name,
                &params,
                Span::new(0, 0),
                &mut module,
                None,
            )
            .expect("name in inline table")
            .expect("inline emission succeeds");
            builder.ins().return_(&[result]);
            builder.finalize();
        }
        module.define_function(func_id, &mut ctx).unwrap();
        module.clear_context(&mut ctx);
        module.finalize_definitions().unwrap();
        let code = module.get_finalized_function(func_id);
        let f: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(code) };
        f(x)
    }

    // --- Per-op happy path (one each) ---

    // spec: appendix-a-builtins §A.3 — bit-and → CLIF band. 12 & 10 = 8.
    #[test]
    fn bit_and_happy() {
        assert_eq!(run_binary("bit-and", 12, 10), 8);
    }

    // spec: appendix-a-builtins §A.3 — bit-or → CLIF bor. 12 | 10 = 14.
    #[test]
    fn bit_or_happy() {
        assert_eq!(run_binary("bit-or", 12, 10), 14);
    }

    // spec: appendix-a-builtins §A.3 — bit-xor → CLIF bxor. 12 ^ 10 = 6.
    #[test]
    fn bit_xor_happy() {
        assert_eq!(run_binary("bit-xor", 12, 10), 6);
    }

    // spec: appendix-a-builtins §A.3 — shl → CLIF ishl. 1 << 4 = 16.
    #[test]
    fn shl_happy() {
        assert_eq!(run_binary("shl", 1, 4), 16);
    }

    // spec: appendix-a-builtins §A.3 — shr → CLIF sshr. 16 >> 2 = 4.
    #[test]
    fn shr_happy() {
        assert_eq!(run_binary("shr", 16, 2), 4);
    }

    // spec: appendix-a-builtins §A.3 — bit-not → CLIF bnot. ~0 = -1.
    #[test]
    fn bit_not_happy() {
        assert_eq!(run_unary("bit-not", 0), -1);
    }

    // spec: appendix-a-builtins §A.3 — popcount → CLIF popcnt. popcount(7) = 3.
    #[test]
    fn popcount_happy() {
        assert_eq!(run_unary("popcount", 7), 3);
    }

    // --- Sign-bit / arithmetic shr (sshr, NOT ushr) ---

    // spec: appendix-a-builtins §A.3 — shr is ARITHMETIC for signed Int: the
    // sign bit replicates. (shr -8 1) = -4 (a logical shift would give a huge
    // positive); (shr -1 63) = -1.
    #[test]
    fn shr_arithmetic_sign_bit() {
        assert_eq!(run_binary("shr", -8, 1), -4);
        assert_eq!(run_binary("shr", -1, 63), -1);
    }

    // --- bit-not full 64-bit width ---

    // spec: appendix-a-builtins §A.3 — bit-not complements all 64 bits;
    // (bit-not x) = (- (- x) 1). (bit-not 0) = -1, (bit-not 5) = -6,
    // (bit-not -1) = 0.
    #[test]
    fn bit_not_full_width() {
        assert_eq!(run_unary("bit-not", 0), -1);
        assert_eq!(run_unary("bit-not", 5), -6);
        assert_eq!(run_unary("bit-not", -1), 0);
    }

    // --- Shift count mod 64 (Cranelift-implicit masking) ---

    // spec: appendix-a-builtins §A.3 — "Shift count" is taken modulo 64.
    // (shl 1 64) = (shl 1 0) = 1; (shr 256 64) = 256; (shl 1 65) = (shl 1 1) = 2.
    // If a target ISA diverged, these would fail and an explicit band(amt,63)
    // would be needed in the shift emit closures.
    #[test]
    fn shift_count_mod_64() {
        assert_eq!(run_binary("shl", 1, 64), 1);
        assert_eq!(run_binary("shr", 256, 64), 256);
        assert_eq!(run_binary("shl", 1, 65), 2);
    }

    // --- is_known_builtin coverage for the new names ---

    // spec: appendix-a-builtins §A.3 — the seven bitwise names are recognised
    // inline builtins (drives the arg-compilation strategy branch).
    #[test]
    fn bitwise_names_are_known_builtins() {
        for name in [
            "bit-and", "bit-or", "bit-xor", "bit-not", "shl", "shr", "popcount",
        ] {
            assert!(is_known_builtin(name), "{name} should be a known builtin");
        }
    }
}
