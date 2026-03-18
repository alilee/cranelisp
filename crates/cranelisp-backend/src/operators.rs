// Builtin primitive codegen.
//
// Uses the monomorphic primitive names from ring0_primitives() in cranelisp-types.
// The primitive name alone encodes the operand types — no operand_type parameter
// is needed. For example, `add-i64` is always Int+Int→Int and `add-f64` is
// always Float+Float→Float.
//
// The 19 Ring 0 primitives:
//   add-i64, sub-i64, mul-i64, div-i64
//   add-f64, sub-f64, mul-f64, div-f64
//   eq-i64, lt-i64, gt-i64, le-i64, ge-i64
//   eq-f64, lt-f64, gt-f64, le-f64, ge-f64
//   not

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use cranelisp_types::{CranelispError, Span, Symbol, TraitName, TypeName};

/// Emit inline Cranelift IR for a builtin primitive.
///
/// The `name` is a monomorphic primitive name such as `add-i64` or
/// `mul-f64`. The name alone determines which Cranelift instruction
/// is emitted — no separate operand type is needed.
///
/// Returns the result Value. All values are i64 at the Cranelift boundary;
/// floats are bitcast to/from i64 as needed.
pub fn emit_builtin_op(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[Value],
    span: Span,
    module: &mut cranelift_jit::JITModule,
    panic_func_id: Option<FuncId>,
) -> Result<Value, CranelispError> {
    match name {
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
        _ => Err(CranelispError::CodegenError {
            message: format!("unknown builtin primitive: {name}"),
            span,
        }),
    }
}

/// Check if a name is a known inline builtin primitive.
///
/// Returns true for names handled by `emit_builtin_op`. Names not in this
/// set are assumed to be extern calls (e.g., platform effect functions).
pub fn is_known_builtin(name: &str) -> bool {
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
    Ok(builder.ins().bitcast(types::I64, MemFlags::new(), result_f64))
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

/// Emit a checked integer division: branch on zero divisor to a panic block
/// that calls `runtime_panic("division by zero")`, otherwise emit `sdiv`.
fn emit_checked_div(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[Value],
    span: Span,
    module: &mut cranelift_jit::JITModule,
    panic_func_id: Option<FuncId>,
) -> Result<Value, CranelispError> {
    require_args(name, args, 2, span)?;

    let panic_id = panic_func_id.ok_or_else(|| CranelispError::CodegenError {
        message: "runtime/panic not declared".into(),
        span,
    })?;

    let rhs = args[1];
    let zero = builder.ins().iconst(types::I64, 0);
    let is_zero = builder.ins().icmp(IntCC::Equal, rhs, zero);

    let ok_block = builder.create_block();
    let panic_block = builder.create_block();

    builder
        .ins()
        .brif(is_zero, panic_block, &[], ok_block, &[]);

    // Panic path: call runtime_panic with "division by zero".
    builder.switch_to_block(panic_block);
    builder.seal_block(panic_block);

    let msg = b"division by zero";
    let data_id = module
        .declare_anonymous_data(false, false)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare panic data: {e}"),
            span,
        })?;
    let mut desc = cranelift_module::DataDescription::new();
    desc.define(msg.to_vec().into_boxed_slice());
    module
        .define_data(data_id, &desc)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to define panic data: {e}"),
            span,
        })?;

    let gv = module.declare_data_in_func(data_id, builder.func);
    let msg_ptr = builder.ins().global_value(types::I64, gv);
    let msg_len = builder.ins().iconst(types::I64, msg.len() as i64);

    let panic_ref = module.declare_func_in_func(panic_id, builder.func);
    builder.ins().call(panic_ref, &[msg_ptr, msg_len]);

    // runtime_panic sets a thread-local error flag and returns.
    // Return a dummy 0 value — the caller checks take_runtime_error().
    let dummy = builder.ins().iconst(types::I64, 0);
    builder.ins().return_(&[dummy]);

    // OK path: emit sdiv.
    builder.switch_to_block(ok_block);
    builder.seal_block(ok_block);

    Ok(builder.ins().sdiv(args[0], args[1]))
}

// --- Primitive trait method mapping ---

/// Check if a trait method implementation corresponds to a known primitive.
///
/// Returns the primitive name that should be emitted inline (e.g., "add-i64")
/// if this is a known primitive impl. Returns None for user-defined impls,
/// which should be compiled as normal function calls.
///
/// Static mapping from (TraitName, method_name, impl_type) to primitive name.
/// Per arch decision 14: typecheck emits TraitMethod, backend maps to primitives.
pub fn primitive_for_trait_method(
    trait_name: &TraitName,
    method_name: &Symbol,
    impl_type: &TypeName,
) -> Option<&'static str> {
    let t = trait_name.as_ref();
    let m = method_name.as_ref();
    let i = impl_type.as_ref();

    match (t, m, i) {
        // Num trait: arithmetic operators
        ("Num", "+", "Int") => Some("add-i64"),
        ("Num", "-", "Int") => Some("sub-i64"),
        ("Num", "*", "Int") => Some("mul-i64"),
        ("Num", "/", "Int") => Some("div-i64"),
        ("Num", "+", "Float") => Some("add-f64"),
        ("Num", "-", "Float") => Some("sub-f64"),
        ("Num", "*", "Float") => Some("mul-f64"),
        ("Num", "/", "Float") => Some("div-f64"),

        // Eq trait: equality operators
        ("Eq", "=", "Int") => Some("eq-i64"),
        ("Eq", "=", "Float") => Some("eq-f64"),
        ("Eq", "=", "Bool") => Some("eq-bool"),
        ("Eq", "=", "String") => Some("str-eq"),

        // Ord trait: comparison operators
        ("Ord", "<", "Int") => Some("lt-i64"),
        ("Ord", "<", "Float") => Some("lt-f64"),
        ("Ord", ">", "Int") => Some("gt-i64"),
        ("Ord", ">", "Float") => Some("gt-f64"),
        ("Ord", "<=", "Int") => Some("le-i64"),
        ("Ord", "<=", "Float") => Some("le-f64"),
        ("Ord", ">=", "Int") => Some("ge-i64"),
        ("Ord", ">=", "Float") => Some("ge-f64"),

        // Eq trait: inequality (default method)
        ("Eq", "!=", "Int") => Some("neq-i64"),
        ("Eq", "!=", "Float") => Some("neq-f64"),
        ("Eq", "!=", "Bool") => Some("neq-bool"),
        ("Eq", "!=", "String") => Some("neq-string"),

        // Display trait: show (string conversion)
        ("Display", "show", "Int") => Some("int-to-string"),
        ("Display", "show", "Float") => Some("float-to-string"),
        ("Display", "show", "Bool") => Some("bool-to-string"),
        ("Display", "show", "String") => Some("string-identity"),

        _ => None,
    }
}

// --- Utility ---

/// Return an error if `args.len() != expected`.
fn require_args(name: &str, args: &[Value], expected: usize, span: Span) -> Result<(), CranelispError> {
    if args.len() != expected {
        return Err(CranelispError::CodegenError {
            message: format!(
                "primitive '{name}' requires {expected} argument(s), got {}",
                args.len()
            ),
            span,
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- primitive_for_trait_method tests ---

    // spec: appendix-a-builtins §A.3 — Num.+ on Int maps to add-i64 inline primitive
    #[test]
    fn test_num_add_int_maps_to_add_i64() {
        let result = primitive_for_trait_method(
            &TraitName::from("Num"),
            &Symbol::from("+"),
            &TypeName::from("Int"),
        );
        assert_eq!(result, Some("add-i64"));
    }

    // spec: appendix-a-builtins §A.3 — Num.+ on Float maps to add-f64 inline primitive
    #[test]
    fn test_num_add_float_maps_to_add_f64() {
        let result = primitive_for_trait_method(
            &TraitName::from("Num"),
            &Symbol::from("+"),
            &TypeName::from("Float"),
        );
        assert_eq!(result, Some("add-f64"));
    }

    // spec: appendix-a-builtins §A.3 — all Num trait Int methods map to i64 primitives
    #[test]
    fn test_num_all_int_methods() {
        let ops = vec![("+", "add-i64"), ("-", "sub-i64"), ("*", "mul-i64"), ("/", "div-i64")];
        for (method, expected) in ops {
            let result = primitive_for_trait_method(
                &TraitName::from("Num"),
                &Symbol::from(method),
                &TypeName::from("Int"),
            );
            assert_eq!(result, Some(expected), "Num.{method}$Int");
        }
    }

    // spec: appendix-a-builtins §A.3 — Eq.= on Int maps to eq-i64
    #[test]
    fn test_eq_int_maps_to_eq_i64() {
        let result = primitive_for_trait_method(
            &TraitName::from("Eq"),
            &Symbol::from("="),
            &TypeName::from("Int"),
        );
        assert_eq!(result, Some("eq-i64"));
    }

    // spec: appendix-a-builtins §A.3 — Eq.= on Bool maps to eq-bool
    #[test]
    fn test_eq_bool_maps_to_eq_bool() {
        let result = primitive_for_trait_method(
            &TraitName::from("Eq"),
            &Symbol::from("="),
            &TypeName::from("Bool"),
        );
        assert_eq!(result, Some("eq-bool"));
    }

    // spec: appendix-a-builtins §A.3 — Eq.= on String maps to str-eq
    #[test]
    fn test_eq_string_maps_to_str_eq() {
        let result = primitive_for_trait_method(
            &TraitName::from("Eq"),
            &Symbol::from("="),
            &TypeName::from("String"),
        );
        assert_eq!(result, Some("str-eq"));
    }

    // spec: appendix-a-builtins §A.3 — Ord.< on Int maps to lt-i64
    #[test]
    fn test_ord_lt_int_maps_to_lt_i64() {
        let result = primitive_for_trait_method(
            &TraitName::from("Ord"),
            &Symbol::from("<"),
            &TypeName::from("Int"),
        );
        assert_eq!(result, Some("lt-i64"));
    }

    // spec: 07-traits §7.7 — Display.show on Int maps to int-to-string
    #[test]
    fn test_display_show_int_maps_to_int_to_string() {
        let result = primitive_for_trait_method(
            &TraitName::from("Display"),
            &Symbol::from("show"),
            &TypeName::from("Int"),
        );
        assert_eq!(result, Some("int-to-string"));
    }

    // spec: 07-traits §7.7 — Display.show on Float maps to float-to-string
    #[test]
    fn test_display_show_float_maps_to_float_to_string() {
        let result = primitive_for_trait_method(
            &TraitName::from("Display"),
            &Symbol::from("show"),
            &TypeName::from("Float"),
        );
        assert_eq!(result, Some("float-to-string"));
    }

    // spec: 07-traits §7.7 — Display.show on Bool maps to bool-to-string
    #[test]
    fn test_display_show_bool_maps_to_bool_to_string() {
        let result = primitive_for_trait_method(
            &TraitName::from("Display"),
            &Symbol::from("show"),
            &TypeName::from("Bool"),
        );
        assert_eq!(result, Some("bool-to-string"));
    }

    // spec: 07-traits §7.7 — Display.show on String maps to string-identity
    #[test]
    fn test_display_show_string_maps_to_string_identity() {
        let result = primitive_for_trait_method(
            &TraitName::from("Display"),
            &Symbol::from("show"),
            &TypeName::from("String"),
        );
        assert_eq!(result, Some("string-identity"));
    }

    // spec: 07-traits §7.7 — unknown trait has no inline primitive mapping
    #[test]
    fn test_unknown_trait_returns_none() {
        let result = primitive_for_trait_method(
            &TraitName::from("Hashable"),
            &Symbol::from("hash"),
            &TypeName::from("Int"),
        );
        assert_eq!(result, None);
    }

    // spec: 07-traits §7.7 — unknown impl type has no inline primitive mapping
    #[test]
    fn test_unknown_impl_type_returns_none() {
        let result = primitive_for_trait_method(
            &TraitName::from("Num"),
            &Symbol::from("+"),
            &TypeName::from("Color"),
        );
        assert_eq!(result, None);
    }
}
