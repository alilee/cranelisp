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
) -> Result<Value, CranelispError> {
    match name {
        // Integer arithmetic
        "add-i64" => emit_binary_int(builder, name, args, span, |b, l, r| b.ins().iadd(l, r)),
        "sub-i64" => emit_binary_int(builder, name, args, span, |b, l, r| b.ins().isub(l, r)),
        "mul-i64" => emit_binary_int(builder, name, args, span, |b, l, r| b.ins().imul(l, r)),
        "div-i64" => emit_binary_int(builder, name, args, span, |b, l, r| b.ins().sdiv(l, r)),

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

        _ => Err(CranelispError::CodegenError {
            message: format!("unknown builtin primitive: {name}"),
            span,
        }),
    }
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

    #[test]
    fn test_num_add_int_maps_to_add_i64() {
        let result = primitive_for_trait_method(
            &TraitName::from("Num"),
            &Symbol::from("+"),
            &TypeName::from("Int"),
        );
        assert_eq!(result, Some("add-i64"));
    }

    #[test]
    fn test_num_add_float_maps_to_add_f64() {
        let result = primitive_for_trait_method(
            &TraitName::from("Num"),
            &Symbol::from("+"),
            &TypeName::from("Float"),
        );
        assert_eq!(result, Some("add-f64"));
    }

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

    #[test]
    fn test_eq_int_maps_to_eq_i64() {
        let result = primitive_for_trait_method(
            &TraitName::from("Eq"),
            &Symbol::from("="),
            &TypeName::from("Int"),
        );
        assert_eq!(result, Some("eq-i64"));
    }

    #[test]
    fn test_eq_bool_maps_to_eq_bool() {
        let result = primitive_for_trait_method(
            &TraitName::from("Eq"),
            &Symbol::from("="),
            &TypeName::from("Bool"),
        );
        assert_eq!(result, Some("eq-bool"));
    }

    #[test]
    fn test_eq_string_maps_to_str_eq() {
        let result = primitive_for_trait_method(
            &TraitName::from("Eq"),
            &Symbol::from("="),
            &TypeName::from("String"),
        );
        assert_eq!(result, Some("str-eq"));
    }

    #[test]
    fn test_ord_lt_int_maps_to_lt_i64() {
        let result = primitive_for_trait_method(
            &TraitName::from("Ord"),
            &Symbol::from("<"),
            &TypeName::from("Int"),
        );
        assert_eq!(result, Some("lt-i64"));
    }

    #[test]
    fn test_unknown_trait_returns_none() {
        let result = primitive_for_trait_method(
            &TraitName::from("Display"),
            &Symbol::from("show"),
            &TypeName::from("Int"),
        );
        assert_eq!(result, None);
    }

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
