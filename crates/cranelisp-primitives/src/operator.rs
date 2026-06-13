//! Primitive constructor inputs for `PRIMITIVES_TABLE` initialisation.
//!
//! Per Decision 0048 the primitives module is a `SymbolTable` like any other —
//! these `PrimitiveDef` rows and the `ring{0,1,3}_primitives()` builders exist
//! only as input data for the static `PRIMITIVES_TABLE` population in
//! `lib.rs::build_primitives_table()`. They are crate-private; consumers reach
//! the same data via `ModuleEntry::Def { kind: DefKind::Primitive { … } }`
//! entries in `PRIMITIVES_TABLE.symbols`.
//!
//! Relocated from `cranelisp-types` Sprint 69 (types audit H1 stronger
//! disposition): the public boundary type is `ModuleEntry::Def`, not
//! `PrimitiveDef`, so these definitions leave the cross-crate surface.
//!
//! Historical context: 19 monomorphic named primitives replace 10 polymorphic
//! operators. Each primitive has a fixed concrete type — no polymorphic type
//! variables, no `operand_type` disambiguation. The primitive name uniquely
//! encodes both operand types and the Cranelift instruction. `add-i64` is
//! always Int, `add-f64` is always Float. Ring 2's `Num.+` dispatches to
//! `add-i64`/`add-f64` via trait resolution.

use cranelisp_types::{ModuleFullPath, Symbol, Type, TypeName};

/// A Ring 0 monomorphic primitive definition.
///
/// Each primitive has a fixed concrete type — all fields are compile-time constants.
/// Registered as a payload-free `DefKind::Primitive` entry in the symbol table
/// (S69 Submission 36 — the prior `{ primitive_kind, jit_name }` payload retired).
#[derive(Debug, Clone)]
pub(crate) struct PrimitiveDef {
    /// The name used in source (e.g. `add-i64`, `add-f64`, `not`).
    pub name: Symbol,
    /// The concrete monomorphic type of this primitive.
    /// Always a `Type::Fn` with concrete parameter and return types.
    pub ty: Type,
    /// Parameter names for REPL display (e.g. `[lhs rhs]`).
    pub param_names: Vec<Symbol>,
    /// The runtime docstring — the Description-column text from
    /// `spec/appendix-a-builtins.md` §A.3, surfaced via `/doc` + the
    /// `; classification - docstring` REPL suffix (§A.5 MUST). Registered onto
    /// the primitive's `ModuleEntry::Def.docstring` so int reads it through the
    /// canonical symbol-table entry rather than a parallel host-side table
    /// (FIXME 0308 — single source of truth, Principle 7).
    pub docstring: &'static str,
}

/// The complete Ring 0 primitive table.
///
/// Single authoritative source — typechecker and backend both reference this.
/// The typechecker registers these with monomorphic schemes (`mono(prim.ty)`).
/// The backend owns its own inline-substitution table (`primitives_inline.rs`)
/// keyed by primitive name (`primitives ⟂ backend`, S73).
pub(crate) fn ring0_primitives() -> Vec<PrimitiveDef> {
    vec![
        // --- Int arithmetic: (Fn [Int Int] Int) ---
        PrimitiveDef {
            name: Symbol::from("add-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Add",
        },
        PrimitiveDef {
            name: Symbol::from("sub-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Subtract",
        },
        PrimitiveDef {
            name: Symbol::from("mul-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Multiply",
        },
        PrimitiveDef {
            name: Symbol::from("div-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Integer division",
        },
        // --- Float arithmetic: (Fn [Float Float] Float) ---
        PrimitiveDef {
            name: Symbol::from("add-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Add",
        },
        PrimitiveDef {
            name: Symbol::from("sub-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Subtract",
        },
        PrimitiveDef {
            name: Symbol::from("mul-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Multiply",
        },
        PrimitiveDef {
            name: Symbol::from("div-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Division",
        },
        // --- Int comparison: (Fn [Int Int] Bool) ---
        PrimitiveDef {
            name: Symbol::from("eq-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Equality",
        },
        PrimitiveDef {
            name: Symbol::from("lt-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Less than",
        },
        PrimitiveDef {
            name: Symbol::from("gt-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Greater than",
        },
        PrimitiveDef {
            name: Symbol::from("le-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Less than or equal",
        },
        PrimitiveDef {
            name: Symbol::from("ge-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Greater than or equal",
        },
        // --- Float comparison: (Fn [Float Float] Bool) ---
        PrimitiveDef {
            name: Symbol::from("eq-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Equality",
        },
        PrimitiveDef {
            name: Symbol::from("lt-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Less than",
        },
        PrimitiveDef {
            name: Symbol::from("gt-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Greater than",
        },
        PrimitiveDef {
            name: Symbol::from("le-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Less than or equal",
        },
        PrimitiveDef {
            name: Symbol::from("ge-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Greater than or equal",
        },
        // --- Boolean: (Fn [Bool] Bool) ---
        PrimitiveDef {
            name: Symbol::from("not"),
            ty: Type::Fn(vec![Type::Bool], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("b")],
            docstring: "Boolean negation",
        },
        // --- Boolean equality: (Fn [Bool Bool] Bool) ---
        PrimitiveDef {
            name: Symbol::from("eq-bool"),
            ty: Type::Fn(vec![Type::Bool, Type::Bool], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Equality",
        },
    ]
}

/// Ring 1 extern primitive definitions.
///
/// These are string and type conversion functions implemented as extern "C"
/// functions in `cranelisp-runtime`. They are NOT inlined as Cranelift IR
/// at call sites -- the backend emits `call` instructions to the JIT-registered
/// function pointers, keyed by the primitive name (same as the spec name).
pub(crate) fn ring1_primitives() -> Vec<PrimitiveDef> {
    vec![
        PrimitiveDef {
            name: Symbol::from("str-concat"),
            ty: Type::Fn(vec![Type::String, Type::String], Box::new(Type::String)),
            param_names: vec![Symbol::from("a"), Symbol::from("b")],
            docstring: "Concatenate two strings",
        },
        PrimitiveDef {
            name: Symbol::from("str-eq"),
            ty: Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("a"), Symbol::from("b")],
            docstring: "String equality (byte-wise)",
        },
        PrimitiveDef {
            name: Symbol::from("str-len"),
            ty: Type::Fn(vec![Type::String], Box::new(Type::Int)),
            param_names: vec![Symbol::from("s")],
            docstring: "String length in bytes",
        },
        PrimitiveDef {
            name: Symbol::from("string-identity"),
            ty: Type::Fn(vec![Type::String], Box::new(Type::String)),
            param_names: vec![Symbol::from("s")],
            docstring: "Identity for String (used by Display impl)",
        },
        PrimitiveDef {
            name: Symbol::from("int-to-string"),
            ty: Type::Fn(vec![Type::Int], Box::new(Type::String)),
            param_names: vec![Symbol::from("n")],
            docstring: "Convert integer to decimal string",
        },
        PrimitiveDef {
            name: Symbol::from("float-to-string"),
            ty: Type::Fn(vec![Type::Float], Box::new(Type::String)),
            param_names: vec![Symbol::from("f")],
            docstring: "Convert float to string",
        },
        PrimitiveDef {
            name: Symbol::from("bool-to-string"),
            ty: Type::Fn(vec![Type::Bool], Box::new(Type::String)),
            param_names: vec![Symbol::from("b")],
            docstring: "\"true\" or \"false\"",
        },
        PrimitiveDef {
            name: Symbol::from("parse-int"),
            ty: Type::Fn(
                vec![Type::String],
                Box::new(Type::adt(ModuleFullPath::from("primitives"), TypeName::from("Option"), vec![Type::Int])),
            ),
            param_names: vec![Symbol::from("s")],
            docstring: "Parse decimal integer; None on failure",
        },
        // --- Ring 1 extended string primitives ---
        PrimitiveDef {
            name: Symbol::from("substring"),
            ty: Type::Fn(vec![Type::String, Type::Int, Type::Int], Box::new(Type::String)),
            param_names: vec![Symbol::from("s"), Symbol::from("start"), Symbol::from("end")],
            docstring: "Extract substring from start (inclusive) to end (exclusive); \
                        clamps out-of-bounds indices",
        },
        PrimitiveDef {
            name: Symbol::from("char-at"),
            ty: Type::Fn(vec![Type::String, Type::Int], Box::new(Type::String)),
            param_names: vec![Symbol::from("s"), Symbol::from("idx")],
            docstring: "Character at byte index as single-character string; empty \
                        string if out of bounds",
        },
        PrimitiveDef {
            name: Symbol::from("split"),
            ty: Type::Fn(
                vec![Type::String, Type::String],
                Box::new(Type::adt(ModuleFullPath::from("primitives"), TypeName::from("Vec"), vec![Type::String])),
            ),
            param_names: vec![Symbol::from("s"), Symbol::from("sep")],
            docstring: "Split string by separator",
        },
        PrimitiveDef {
            name: Symbol::from("join"),
            ty: Type::Fn(
                vec![Type::String, Type::adt(ModuleFullPath::from("primitives"), TypeName::from("Vec"), vec![Type::String])],
                Box::new(Type::String),
            ),
            param_names: vec![Symbol::from("sep"), Symbol::from("parts")],
            docstring: "Join strings with separator",
        },
        PrimitiveDef {
            name: Symbol::from("replace"),
            ty: Type::Fn(vec![Type::String, Type::String, Type::String], Box::new(Type::String)),
            param_names: vec![Symbol::from("s"), Symbol::from("from"), Symbol::from("to")],
            docstring: "Replace all occurrences of from with to",
        },
        PrimitiveDef {
            name: Symbol::from("trim"),
            ty: Type::Fn(vec![Type::String], Box::new(Type::String)),
            param_names: vec![Symbol::from("s")],
            docstring: "Trim leading and trailing whitespace",
        },
        PrimitiveDef {
            name: Symbol::from("starts-with?"),
            ty: Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("s"), Symbol::from("prefix")],
            docstring: "Test if string starts with prefix",
        },
        PrimitiveDef {
            name: Symbol::from("ends-with?"),
            ty: Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("s"), Symbol::from("suffix")],
            docstring: "Test if string ends with suffix",
        },
        PrimitiveDef {
            name: Symbol::from("contains?"),
            ty: Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("s"), Symbol::from("needle")],
            docstring: "Test if string contains substring",
        },
        PrimitiveDef {
            name: Symbol::from("to-upper"),
            ty: Type::Fn(vec![Type::String], Box::new(Type::String)),
            param_names: vec![Symbol::from("s")],
            docstring: "Convert to uppercase",
        },
        PrimitiveDef {
            name: Symbol::from("to-lower"),
            ty: Type::Fn(vec![Type::String], Box::new(Type::String)),
            param_names: vec![Symbol::from("s")],
            docstring: "Convert to lowercase",
        },
    ]
}

/// Ring 3 extern primitive definitions.
///
/// These are macro-infrastructure primitives that depend on the synthetic
/// `Sexp` type from the `macros` module. They must be registered AFTER
/// `register_macros_module()` populates the type definition for `Sexp`.
///
/// `quote-sexp` converts a runtime Sexp value into a quoted form suitable
/// for splicing into macro output.
pub(crate) fn ring3_primitives() -> Vec<PrimitiveDef> {
    let sexp_type = Type::adt(ModuleFullPath::from("macros"), TypeName::from("Sexp"), vec![]);
    vec![
        PrimitiveDef {
            name: Symbol::from("quote-sexp"),
            ty: Type::Fn(vec![sexp_type.clone()], Box::new(sexp_type)),
            param_names: vec![Symbol::from("sexp")],
            docstring: "Convert a runtime Sexp value to constructor source code",
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ring0_primitive_count() {
        let prims = ring0_primitives();
        assert_eq!(prims.len(), 20, "Ring 0 should define exactly 20 primitives (19 + eq-bool)");
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
            if let Type::Fn(params, ret) = &p.ty {
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
        }
    }

    // spec: appendix-a-builtins §A.4 — ring3 primitives count
    #[test]
    fn test_ring3_primitive_count() {
        let prims = ring3_primitives();
        assert_eq!(prims.len(), 1, "Ring 3 should define exactly 1 primitive (quote-sexp)");
    }

    // spec: appendix-a-builtins §A.4 — quote-sexp type is (Fn [Sexp] Sexp)
    #[test]
    fn test_quote_sexp_type() {
        let prims = ring3_primitives();
        let qs = prims.iter().find(|p| p.name.as_ref() == "quote-sexp").unwrap();
        let sexp_type = Type::adt(ModuleFullPath::from("macros"), TypeName::from("Sexp"), vec![]);
        assert_eq!(
            qs.ty,
            Type::Fn(vec![sexp_type.clone()], Box::new(sexp_type)),
            "quote-sexp: (Fn [Sexp] Sexp)"
        );
    }
}
