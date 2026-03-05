//! Ring 0 monomorphic primitive definitions.
//!
//! 19 monomorphic named primitives replace 10 polymorphic operators.
//! Each primitive has a fixed concrete type — no polymorphic type variables,
//! no `operand_type` disambiguation needed.
//!
//! The primitive name uniquely encodes both operand types and the Cranelift instruction.
//! `add-i64` is always Int, `add-f64` is always Float — no lookup tables.
//!
//! Ring 2 will add `Num.+` which dispatches to `add-i64`/`add-f64` via trait resolution.
//! These primitives survive permanently as the foundation for that dispatch.

use crate::{Symbol, Type};

/// A Ring 0 monomorphic primitive definition.
///
/// Each primitive has a fixed concrete type — all fields are compile-time constants.
/// Registered as `DefKind::Primitive { primitive_kind: PrimitiveKind::Inline }` in the
/// symbol table.
#[derive(Debug, Clone)]
pub struct PrimitiveDef {
    /// The name used in source (e.g. `add-i64`, `add-f64`, `not`).
    pub name: Symbol,
    /// The concrete monomorphic type of this primitive.
    /// Always a `Type::Fn` with concrete parameter and return types.
    pub ty: Type,
    /// The Cranelift instruction emitted at call sites.
    /// The backend matches on this string to emit the correct IR.
    pub cranelift_op: &'static str,
    /// Parameter names for REPL display (e.g. `[lhs rhs]`).
    pub param_names: Vec<Symbol>,
}

/// The complete Ring 0 primitive table.
///
/// Single authoritative source — typechecker and backend both reference this.
/// The typechecker registers these with monomorphic schemes (`mono(prim.ty)`).
/// The backend matches on `cranelift_op` to emit inline Cranelift IR.
pub fn ring0_primitives() -> Vec<PrimitiveDef> {
    vec![
        // --- Int arithmetic: (Fn [Int Int] Int) ---
        PrimitiveDef {
            name: Symbol::from("add-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            cranelift_op: "iadd",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        PrimitiveDef {
            name: Symbol::from("sub-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            cranelift_op: "isub",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        PrimitiveDef {
            name: Symbol::from("mul-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            cranelift_op: "imul",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        PrimitiveDef {
            name: Symbol::from("div-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            cranelift_op: "sdiv",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        // --- Float arithmetic: (Fn [Float Float] Float) ---
        PrimitiveDef {
            name: Symbol::from("add-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)),
            cranelift_op: "fadd",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        PrimitiveDef {
            name: Symbol::from("sub-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)),
            cranelift_op: "fsub",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        PrimitiveDef {
            name: Symbol::from("mul-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)),
            cranelift_op: "fmul",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        PrimitiveDef {
            name: Symbol::from("div-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)),
            cranelift_op: "fdiv",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        // --- Int comparison: (Fn [Int Int] Bool) ---
        PrimitiveDef {
            name: Symbol::from("eq-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            cranelift_op: "icmp_eq",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        PrimitiveDef {
            name: Symbol::from("lt-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            cranelift_op: "icmp_slt",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        PrimitiveDef {
            name: Symbol::from("gt-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            cranelift_op: "icmp_sgt",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        PrimitiveDef {
            name: Symbol::from("le-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            cranelift_op: "icmp_sle",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        PrimitiveDef {
            name: Symbol::from("ge-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            cranelift_op: "icmp_sge",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        // --- Float comparison: (Fn [Float Float] Bool) ---
        PrimitiveDef {
            name: Symbol::from("eq-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            cranelift_op: "fcmp_eq",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        PrimitiveDef {
            name: Symbol::from("lt-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            cranelift_op: "fcmp_lt",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        PrimitiveDef {
            name: Symbol::from("gt-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            cranelift_op: "fcmp_gt",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        PrimitiveDef {
            name: Symbol::from("le-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            cranelift_op: "fcmp_le",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        PrimitiveDef {
            name: Symbol::from("ge-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            cranelift_op: "fcmp_ge",
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
        },
        // --- Boolean: (Fn [Bool] Bool) ---
        PrimitiveDef {
            name: Symbol::from("not"),
            ty: Type::Fn(vec![Type::Bool], Box::new(Type::Bool)),
            cranelift_op: "bxor", // XOR with 1 to flip bool
            param_names: vec![Symbol::from("b")],
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ring0_primitive_count() {
        let prims = ring0_primitives();
        assert_eq!(prims.len(), 19, "Ring 0 should define exactly 19 primitives");
    }

    #[test]
    fn test_int_arithmetic_types() {
        let prims = ring0_primitives();
        let int_arith: Vec<_> = prims
            .iter()
            .filter(|p| ["add-i64", "sub-i64", "mul-i64", "div-i64"].contains(&p.name.as_ref()))
            .collect();
        assert_eq!(int_arith.len(), 4, "4 int arithmetic primitives");
        for p in &int_arith {
            match &p.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 2, "{} takes 2 params", p.name);
                    assert_eq!(params[0], Type::Int, "{} param[0] is Int", p.name);
                    assert_eq!(params[1], Type::Int, "{} param[1] is Int", p.name);
                    assert_eq!(**ret, Type::Int, "{} returns Int", p.name);
                }
                _ => panic!("{} should have Fn type", p.name),
            }
        }
    }

    #[test]
    fn test_float_arithmetic_types() {
        let prims = ring0_primitives();
        let float_arith: Vec<_> = prims
            .iter()
            .filter(|p| {
                ["add-f64", "sub-f64", "mul-f64", "div-f64"].contains(&p.name.as_ref())
            })
            .collect();
        assert_eq!(float_arith.len(), 4, "4 float arithmetic primitives");
        for p in &float_arith {
            match &p.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params[0], Type::Float, "{} param[0] is Float", p.name);
                    assert_eq!(params[1], Type::Float, "{} param[1] is Float", p.name);
                    assert_eq!(**ret, Type::Float, "{} returns Float", p.name);
                }
                _ => panic!("{} should have Fn type", p.name),
            }
        }
    }

    #[test]
    fn test_int_comparison_types() {
        let prims = ring0_primitives();
        let int_cmp: Vec<_> = prims
            .iter()
            .filter(|p| {
                ["eq-i64", "lt-i64", "gt-i64", "le-i64", "ge-i64"].contains(&p.name.as_ref())
            })
            .collect();
        assert_eq!(int_cmp.len(), 5, "5 int comparison primitives");
        for p in &int_cmp {
            match &p.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params[0], Type::Int, "{} param[0] is Int", p.name);
                    assert_eq!(params[1], Type::Int, "{} param[1] is Int", p.name);
                    assert_eq!(**ret, Type::Bool, "{} returns Bool", p.name);
                }
                _ => panic!("{} should have Fn type", p.name),
            }
        }
    }

    #[test]
    fn test_float_comparison_types() {
        let prims = ring0_primitives();
        let float_cmp: Vec<_> = prims
            .iter()
            .filter(|p| {
                ["eq-f64", "lt-f64", "gt-f64", "le-f64", "ge-f64"]
                    .contains(&p.name.as_ref())
            })
            .collect();
        assert_eq!(float_cmp.len(), 5, "5 float comparison primitives");
        for p in &float_cmp {
            match &p.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params[0], Type::Float, "{} param[0] is Float", p.name);
                    assert_eq!(params[1], Type::Float, "{} param[1] is Float", p.name);
                    assert_eq!(**ret, Type::Bool, "{} returns Bool", p.name);
                }
                _ => panic!("{} should have Fn type", p.name),
            }
        }
    }

    #[test]
    fn test_not_type() {
        let prims = ring0_primitives();
        let not = prims.iter().find(|p| p.name.as_ref() == "not").unwrap();
        assert_eq!(
            not.ty,
            Type::Fn(vec![Type::Bool], Box::new(Type::Bool)),
            "not: (Fn [Bool] Bool)"
        );
        assert_eq!(not.cranelift_op, "bxor");
    }

    #[test]
    fn test_all_primitives_have_fn_type() {
        for p in ring0_primitives() {
            assert!(
                matches!(&p.ty, Type::Fn(_, _)),
                "primitive {} should have Fn type",
                p.name
            );
        }
    }

    #[test]
    fn test_all_primitives_have_param_names() {
        for p in ring0_primitives() {
            match &p.ty {
                Type::Fn(params, _) => {
                    assert_eq!(
                        p.param_names.len(),
                        params.len(),
                        "primitive {} param_names length must match param count",
                        p.name
                    );
                }
                _ => panic!("{} should have Fn type", p.name),
            }
        }
    }

    #[test]
    fn test_no_type_vars_in_primitives() {
        for p in ring0_primitives() {
            match &p.ty {
                Type::Fn(params, ret) => {
                    for param in params {
                        assert!(
                            !matches!(param, Type::Var(_)),
                            "primitive {} should have no type vars, got {:?}",
                            p.name,
                            param
                        );
                    }
                    assert!(
                        !matches!(ret.as_ref(), Type::Var(_)),
                        "primitive {} return type should not be a Var",
                        p.name
                    );
                }
                _ => {}
            }
        }
    }

    #[test]
    fn test_cranelift_op_nonempty() {
        for p in ring0_primitives() {
            assert!(
                !p.cranelift_op.is_empty(),
                "primitive {} should have a cranelift_op",
                p.name
            );
        }
    }
}
