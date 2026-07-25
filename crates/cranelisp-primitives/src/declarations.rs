//! Single declaration inventory for the primitive table and linker harvest.

use cranelisp_types::{
    DefKind, Mode, ModeSummary, ModuleEntry, ModuleFullPath, PrimitiveBody, Scheme, Symbol,
    SymbolTable, Type, TypeName,
};

use crate::ownership_facts;

#[derive(Debug, Clone)]
pub(crate) struct PrimitiveDef {
    pub(crate) name: Symbol,
    pub(crate) ty: Type,
    pub(crate) param_names: Vec<Symbol>,
    pub(crate) docstring: &'static str,
}

#[derive(Clone)]
pub(crate) enum PrimitiveDecl {
    UserExtern {
        name: &'static str,
        scheme: Box<Scheme>,
        param_names: Vec<Symbol>,
        docstring: &'static str,
        ownership: ModeSummary,
        shim_name: &'static str,
        shim: *const u8,
    },
    UserInline {
        name: &'static str,
        scheme: Box<Scheme>,
        param_names: Vec<Symbol>,
        docstring: &'static str,
        ownership: ModeSummary,
    },
    HarvestExtern {
        name: &'static str,
        shim_name: &'static str,
        shim: *const u8,
    },
}

const A: cranelisp_types::TypeId = 0;

fn vec_a() -> Type {
    Type::adt(
        ModuleFullPath::from("primitives"),
        TypeName::from("Vec"),
        vec![Type::Var(A)],
    )
}

fn sexp_type() -> Type {
    Type::adt(
        ModuleFullPath::from("macros"),
        TypeName::from("Sexp"),
        vec![],
    )
}

include!("declaration_macro.rs");

primitive_declarations! {
        user_extern {
            name: "add-i64",
            shim: shim_add_i64(a: i64, b: i64) => crate::ring0::add_i64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("add-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Add",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)))
        }
        user_extern {
            name: "sub-i64",
            shim: shim_sub_i64(a: i64, b: i64) => crate::ring0::sub_i64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("sub-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Subtract",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)))
        }
        user_extern {
            name: "mul-i64",
            shim: shim_mul_i64(a: i64, b: i64) => crate::ring0::mul_i64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("mul-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Multiply",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)))
        }
        user_extern {
            name: "div-i64",
            shim: shim_div_i64(a: i64, b: i64) => crate::ring0::div_i64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("div-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Integer division",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)))
        }
        user_extern {
            name: "add-f64",
            shim: shim_add_f64(a: i64, b: i64) => crate::ring0::add_f64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("add-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Add",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)))
        }
        user_extern {
            name: "sub-f64",
            shim: shim_sub_f64(a: i64, b: i64) => crate::ring0::sub_f64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("sub-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Subtract",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)))
        }
        user_extern {
            name: "mul-f64",
            shim: shim_mul_f64(a: i64, b: i64) => crate::ring0::mul_f64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("mul-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Multiply",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)))
        }
        user_extern {
            name: "div-f64",
            shim: shim_div_f64(a: i64, b: i64) => crate::ring0::div_f64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("div-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Division",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)))
        }
        user_extern {
            name: "eq-i64",
            shim: shim_eq_i64(a: i64, b: i64) => crate::ring0::eq_i64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("eq-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Equality",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)))
        }
        user_extern {
            name: "lt-i64",
            shim: shim_lt_i64(a: i64, b: i64) => crate::ring0::lt_i64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("lt-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Less than",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)))
        }
        user_extern {
            name: "gt-i64",
            shim: shim_gt_i64(a: i64, b: i64) => crate::ring0::gt_i64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("gt-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Greater than",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)))
        }
        user_extern {
            name: "le-i64",
            shim: shim_le_i64(a: i64, b: i64) => crate::ring0::le_i64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("le-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Less than or equal",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)))
        }
        user_extern {
            name: "ge-i64",
            shim: shim_ge_i64(a: i64, b: i64) => crate::ring0::ge_i64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("ge-i64"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Greater than or equal",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)))
        }
        user_extern {
            name: "eq-f64",
            shim: shim_eq_f64(a: i64, b: i64) => crate::ring0::eq_f64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("eq-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Equality",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)))
        }
        user_extern {
            name: "lt-f64",
            shim: shim_lt_f64(a: i64, b: i64) => crate::ring0::lt_f64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("lt-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Less than",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)))
        }
        user_extern {
            name: "gt-f64",
            shim: shim_gt_f64(a: i64, b: i64) => crate::ring0::gt_f64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("gt-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Greater than",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)))
        }
        user_extern {
            name: "le-f64",
            shim: shim_le_f64(a: i64, b: i64) => crate::ring0::le_f64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("le-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Less than or equal",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)))
        }
        user_extern {
            name: "ge-f64",
            shim: shim_ge_f64(a: i64, b: i64) => crate::ring0::ge_f64, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("ge-f64"),
            ty: Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Greater than or equal",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool)))
        }
        user_extern {
            name: "not",
            shim: shim_not(b: i64) => crate::ring0::not, call: (b),
            metadata: PrimitiveDef {
            name: Symbol::from("not"),
            ty: Type::Fn(vec![Type::Bool], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("b")],
            docstring: "Boolean negation",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Bool], Box::new(Type::Bool)))
        }
        user_extern {
            name: "eq-bool",
            shim: shim_eq_bool(a: i64, b: i64) => crate::ring0::eq_bool, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("eq-bool"),
            ty: Type::Fn(vec![Type::Bool, Type::Bool], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Equality",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Bool, Type::Bool], Box::new(Type::Bool)))
        }
        user_extern {
            name: "bit-and",
            shim: shim_bit_and(a: i64, b: i64) => crate::ring0::bit_and, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("bit-and"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Bitwise AND",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)))
        }
        user_extern {
            name: "bit-or",
            shim: shim_bit_or(a: i64, b: i64) => crate::ring0::bit_or, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("bit-or"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Bitwise OR",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)))
        }
        user_extern {
            name: "bit-xor",
            shim: shim_bit_xor(a: i64, b: i64) => crate::ring0::bit_xor, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("bit-xor"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
            docstring: "Bitwise XOR",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)))
        }
        user_extern {
            name: "bit-not",
            shim: shim_bit_not(x: i64) => crate::ring0::bit_not, call: (x),
            metadata: PrimitiveDef {
            name: Symbol::from("bit-not"),
            ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("x")],
            docstring: "Bitwise complement over the full 64-bit two's-complement representation",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int], Box::new(Type::Int)))
        }
        user_extern {
            name: "shl",
            shim: shim_shl(v: i64, amt: i64) => crate::ring0::shl, call: (v, amt),
            metadata: PrimitiveDef {
            name: Symbol::from("shl"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("v"), Symbol::from("amt")],
            docstring: "Left shift; vacated low bits are zero-filled",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)))
        }
        user_extern {
            name: "shr",
            shim: shim_shr(v: i64, amt: i64) => crate::ring0::shr, call: (v, amt),
            metadata: PrimitiveDef {
            name: Symbol::from("shr"),
            ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("v"), Symbol::from("amt")],
            docstring: "Right shift; arithmetic (sign-extending) for signed Int",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)))
        }
        user_extern {
            name: "popcount",
            shim: shim_popcount(x: i64) => crate::ring0::popcount, call: (x),
            metadata: PrimitiveDef {
            name: Symbol::from("popcount"),
            ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
            param_names: vec![Symbol::from("x")],
            docstring: "Population count — number of set bits in the 64-bit representation",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int], Box::new(Type::Int)))
        }
        user_extern {
            name: "str-concat",
            shim: shim_str_concat(a: i64, b: i64) => crate::string::str_concat, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("str-concat"),
            ty: Type::Fn(vec![Type::String, Type::String], Box::new(Type::String)),
            param_names: vec![Symbol::from("a"), Symbol::from("b")],
            docstring: "Concatenate two strings",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![Type::String, Type::String], Box::new(Type::String)), Mode::Owned)
        }
        user_extern {
            name: "str-eq",
            shim: shim_str_eq(a: i64, b: i64) => crate::string::str_eq, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("str-eq"),
            ty: Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("a"), Symbol::from("b")],
            docstring: "String equality (byte-wise)",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)), Mode::Borrowed)
        }
        user_extern {
            name: "neq-string",
            shim: shim_neq_string(a: i64, b: i64) => crate::string::neq_string, call: (a, b),
            metadata: PrimitiveDef {
            name: Symbol::from("neq-string"),
            ty: Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("a"), Symbol::from("b")],
            docstring: "String inequality (byte-wise)",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)), Mode::Borrowed)
        }
        user_extern {
            name: "str-len",
            shim: shim_str_len(s: i64) => crate::string::str_len, call: (s),
            metadata: PrimitiveDef {
            name: Symbol::from("str-len"),
            ty: Type::Fn(vec![Type::String], Box::new(Type::Int)),
            param_names: vec![Symbol::from("s")],
            docstring: "String length in bytes",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![Type::String], Box::new(Type::Int)), Mode::Borrowed)
        }
        user_extern {
            name: "string-identity",
            shim: shim_string_identity(s: i64) => crate::string::string_identity, call: (s),
            metadata: PrimitiveDef {
            name: Symbol::from("string-identity"),
            ty: Type::Fn(vec![Type::String], Box::new(Type::String)),
            param_names: vec![Symbol::from("s")],
            docstring: "Identity for String (used by Display impl)",
        },
            type_vars: vec![],
            ownership: ownership_facts::alias_of_zero()
        }
        user_extern {
            name: "int-to-string",
            shim: shim_int_to_string(n: i64) => crate::int::int_to_string, call: (n),
            metadata: PrimitiveDef {
            name: Symbol::from("int-to-string"),
            ty: Type::Fn(vec![Type::Int], Box::new(Type::String)),
            param_names: vec![Symbol::from("n")],
            docstring: "Convert integer to decimal string",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Int], Box::new(Type::String)))
        }
        user_extern {
            name: "float-to-string",
            shim: shim_float_to_string(f_bits: i64) => crate::float::float_to_string, call: (f_bits),
            metadata: PrimitiveDef {
            name: Symbol::from("float-to-string"),
            ty: Type::Fn(vec![Type::Float], Box::new(Type::String)),
            param_names: vec![Symbol::from("f")],
            docstring: "Convert float to string",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Float], Box::new(Type::String)))
        }
        user_extern {
            name: "bool-to-string",
            shim: shim_bool_to_string(b: i64) => crate::bool::bool_to_string, call: (b),
            metadata: PrimitiveDef {
            name: Symbol::from("bool-to-string"),
            ty: Type::Fn(vec![Type::Bool], Box::new(Type::String)),
            param_names: vec![Symbol::from("b")],
            docstring: "\"true\" or \"false\"",
        },
            type_vars: vec![],
            ownership: ownership_facts::copy_fresh_for_type(&Type::Fn(vec![Type::Bool], Box::new(Type::String)))
        }
        user_extern {
            name: "parse-int",
            shim: shim_parse_int(s: i64) => crate::int::parse_int, call: (s),
            metadata: PrimitiveDef {
            name: Symbol::from("parse-int"),
            ty: Type::Fn(
                vec![Type::String],
                Box::new(Type::adt(ModuleFullPath::from("primitives"), TypeName::from("Option"), vec![Type::Int])),
            ),
            param_names: vec![Symbol::from("s")],
            docstring: "Parse decimal integer; None on failure",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(
                vec![Type::String],
                Box::new(Type::adt(ModuleFullPath::from("primitives"), TypeName::from("Option"), vec![Type::Int])),
            ), Mode::Owned)
        }
        user_extern {
            name: "substring",
            shim: shim_str_substring(s: i64, start: i64, end: i64) => crate::string::str_substring, call: (s, start, end),
            metadata: PrimitiveDef {
            name: Symbol::from("substring"),
            ty: Type::Fn(vec![Type::String, Type::Int, Type::Int], Box::new(Type::String)),
            param_names: vec![Symbol::from("s"), Symbol::from("start"), Symbol::from("end")],
            docstring: "Extract substring from start (inclusive) to end (exclusive); \
                        clamps out-of-bounds indices",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![Type::String, Type::Int, Type::Int], Box::new(Type::String)), Mode::Owned)
        }
        user_extern {
            name: "char-at",
            shim: shim_str_char_at(s: i64, idx: i64) => crate::string::str_char_at, call: (s, idx),
            metadata: PrimitiveDef {
            name: Symbol::from("char-at"),
            ty: Type::Fn(vec![Type::String, Type::Int], Box::new(Type::String)),
            param_names: vec![Symbol::from("s"), Symbol::from("idx")],
            docstring: "Character at byte index as single-character string; empty \
                        string if out of bounds",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![Type::String, Type::Int], Box::new(Type::String)), Mode::Owned)
        }
        user_extern {
            name: "split",
            shim: shim_str_split(s: i64, sep: i64) => crate::string::str_split, call: (s, sep),
            metadata: PrimitiveDef {
            name: Symbol::from("split"),
            ty: Type::Fn(
                vec![Type::String, Type::String],
                Box::new(Type::adt(ModuleFullPath::from("primitives"), TypeName::from("Vec"), vec![Type::String])),
            ),
            param_names: vec![Symbol::from("s"), Symbol::from("sep")],
            docstring: "Split string by separator",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(
                vec![Type::String, Type::String],
                Box::new(Type::adt(ModuleFullPath::from("primitives"), TypeName::from("Vec"), vec![Type::String])),
            ), Mode::Owned)
        }
        user_extern {
            name: "join",
            shim: shim_str_join(sep: i64, vec: i64) => crate::string::str_join, call: (sep, vec),
            metadata: PrimitiveDef {
            name: Symbol::from("join"),
            ty: Type::Fn(
                vec![Type::String, Type::adt(ModuleFullPath::from("primitives"), TypeName::from("Vec"), vec![Type::String])],
                Box::new(Type::String),
            ),
            param_names: vec![Symbol::from("sep"), Symbol::from("parts")],
            docstring: "Join strings with separator",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(
                vec![Type::String, Type::adt(ModuleFullPath::from("primitives"), TypeName::from("Vec"), vec![Type::String])],
                Box::new(Type::String),
            ), Mode::Owned)
        }
        user_extern {
            name: "replace",
            shim: shim_str_replace(s: i64, from: i64, to: i64) => crate::string::str_replace, call: (s, from, to),
            metadata: PrimitiveDef {
            name: Symbol::from("replace"),
            ty: Type::Fn(vec![Type::String, Type::String, Type::String], Box::new(Type::String)),
            param_names: vec![Symbol::from("s"), Symbol::from("from"), Symbol::from("to")],
            docstring: "Replace all occurrences of from with to",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![Type::String, Type::String, Type::String], Box::new(Type::String)), Mode::Owned)
        }
        user_extern {
            name: "trim",
            shim: shim_str_trim(s: i64) => crate::string::str_trim, call: (s),
            metadata: PrimitiveDef {
            name: Symbol::from("trim"),
            ty: Type::Fn(vec![Type::String], Box::new(Type::String)),
            param_names: vec![Symbol::from("s")],
            docstring: "Trim leading and trailing whitespace",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![Type::String], Box::new(Type::String)), Mode::Owned)
        }
        user_extern {
            name: "starts-with?",
            shim: shim_str_starts_with(s: i64, prefix: i64) => crate::string::str_starts_with, call: (s, prefix),
            metadata: PrimitiveDef {
            name: Symbol::from("starts-with?"),
            ty: Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("s"), Symbol::from("prefix")],
            docstring: "Test if string starts with prefix",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)), Mode::Borrowed)
        }
        user_extern {
            name: "ends-with?",
            shim: shim_str_ends_with(s: i64, suffix: i64) => crate::string::str_ends_with, call: (s, suffix),
            metadata: PrimitiveDef {
            name: Symbol::from("ends-with?"),
            ty: Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("s"), Symbol::from("suffix")],
            docstring: "Test if string ends with suffix",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)), Mode::Borrowed)
        }
        user_extern {
            name: "contains?",
            shim: shim_str_contains(s: i64, needle: i64) => crate::string::str_contains, call: (s, needle),
            metadata: PrimitiveDef {
            name: Symbol::from("contains?"),
            ty: Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)),
            param_names: vec![Symbol::from("s"), Symbol::from("needle")],
            docstring: "Test if string contains substring",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)), Mode::Borrowed)
        }
        user_extern {
            name: "to-upper",
            shim: shim_str_to_upper(s: i64) => crate::string::str_to_upper, call: (s),
            metadata: PrimitiveDef {
            name: Symbol::from("to-upper"),
            ty: Type::Fn(vec![Type::String], Box::new(Type::String)),
            param_names: vec![Symbol::from("s")],
            docstring: "Convert to uppercase",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![Type::String], Box::new(Type::String)), Mode::Owned)
        }
        user_extern {
            name: "to-lower",
            shim: shim_str_to_lower(s: i64) => crate::string::str_to_lower, call: (s),
            metadata: PrimitiveDef {
            name: Symbol::from("to-lower"),
            ty: Type::Fn(vec![Type::String], Box::new(Type::String)),
            param_names: vec![Symbol::from("s")],
            docstring: "Convert to lowercase",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![Type::String], Box::new(Type::String)), Mode::Owned)
        }
        user_extern {
            name: "quote-sexp",
            shim: shim_quote_sexp(val: i64) => crate::marshal::quote_sexp, call: (val),
            metadata: PrimitiveDef {
            name: Symbol::from("quote-sexp"),
            ty: Type::Fn(vec![sexp_type()], Box::new(sexp_type())),
            param_names: vec![Symbol::from("sexp")],
            docstring: "Convert a runtime Sexp value to constructor source code",
        },
            type_vars: vec![],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![sexp_type()], Box::new(sexp_type())), Mode::Owned)
        }
        user_extern {
            name: "vec-len",
            shim: shim_vec_len(vec: i64) => crate::vec::vec_len, call: (vec),
            metadata: PrimitiveDef {
    name: Symbol::from("vec-len"),
    ty: Type::Fn(vec![vec_a()], Box::new(Type::Int)),
    param_names: vec![Symbol::from("v")],
    docstring: "Number of elements",
},
            type_vars: vec![A],
            ownership: ownership_facts::uniform_for_type(&Type::Fn(vec![vec_a()], Box::new(Type::Int)), Mode::Borrowed)
        }
        user_inline {
            name: "vec-get",
            metadata: PrimitiveDef {
    name: Symbol::from("vec-get"),
    ty: Type::Fn(vec![vec_a(), Type::Int], Box::new(Type::Var(A))),
    param_names: vec![Symbol::from("v"), Symbol::from("idx")],
    docstring: "Index (bounds-checked; panics on out-of-bounds)",
},
            type_vars: vec![A],
            ownership: ownership_facts::vec_get()
        }
        user_inline {
            name: "vec-set",
            metadata: PrimitiveDef {
    name: Symbol::from("vec-set"),
    ty: Type::Fn(vec![vec_a(), Type::Int, Type::Var(A)], Box::new(vec_a())),
    param_names: vec![Symbol::from("v"), Symbol::from("idx"), Symbol::from("val")],
    docstring: "Return new Vec with element at index replaced",
},
            type_vars: vec![A],
            ownership: ownership_facts::vec_set()
        }
        user_inline {
            name: "vec-push",
            metadata: PrimitiveDef {
    name: Symbol::from("vec-push"),
    ty: Type::Fn(vec![vec_a(), Type::Var(A)], Box::new(vec_a())),
    param_names: vec![Symbol::from("v"), Symbol::from("val")],
    docstring: "Return new Vec with element appended",
},
            type_vars: vec![A],
            ownership: ownership_facts::vec_push()
        }
        harvest_only {
            name: "neq-i64",
            shim: shim_neq_i64(a: i64, b: i64) => crate::ring0::neq_i64, call: (a, b)
        }
        harvest_only {
            name: "neq-f64",
            shim: shim_neq_f64(a: i64, b: i64) => crate::ring0::neq_f64, call: (a, b)
        }
        harvest_only {
            name: "neq-bool",
            shim: shim_neq_bool(a: i64, b: i64) => crate::ring0::neq_bool, call: (a, b)
        }
        harvest_only {
            name: "sconcat",
            shim: shim_sconcat(xs: i64, ys: i64) => crate::marshal::sconcat, call: (xs, ys)
        }
}

pub(crate) fn build_table(table: &mut SymbolTable<(), ()>, declarations: &[PrimitiveDecl]) {
    let mut names = std::collections::HashSet::new();
    for declaration in declarations {
        let (name, scheme, param_names, docstring, ownership, body) = match declaration {
            PrimitiveDecl::UserExtern {
                name,
                scheme,
                param_names,
                docstring,
                ownership,
                shim,
                ..
            } => {
                let slot = table
                    .allocate_got_slot()
                    .expect("fresh primitive GOT cannot be exhausted");
                table.got.store_slot(slot, *shim);
                (
                    *name,
                    scheme,
                    param_names,
                    docstring,
                    ownership,
                    PrimitiveBody::Extern {
                        got_slot: slot,
                        borrowed_sibling_slot: None,
                    },
                )
            }
            PrimitiveDecl::UserInline {
                name,
                scheme,
                param_names,
                docstring,
                ownership,
            } => (
                *name,
                scheme,
                param_names,
                docstring,
                ownership,
                PrimitiveBody::Inline,
            ),
            PrimitiveDecl::HarvestExtern { name, .. } => {
                assert!(
                    names.insert(*name),
                    "duplicate primitive declaration: {}",
                    name
                );
                continue;
            }
        };
        assert!(
            names.insert(name),
            "duplicate primitive declaration: {}",
            name
        );
        table.insert(
            Symbol::from(name),
            ModuleEntry::def(
                scheme.as_ref().clone(),
                DefKind::Primitive {
                    body,
                    mode_summary: Some(ownership.clone()),
                },
            )
            .param_names(param_names.clone())
            .docstring(*docstring)
            .build(),
        );
    }
}

pub(crate) fn harvest_shims(
    declarations: &[PrimitiveDecl],
) -> std::collections::HashMap<&'static str, *const u8> {
    let mut shims = std::collections::HashMap::new();
    for declaration in declarations {
        let Some((name, shim)) = (match declaration {
            PrimitiveDecl::UserExtern {
                name,
                shim,
                shim_name,
                ..
            }
            | PrimitiveDecl::HarvestExtern {
                name,
                shim,
                shim_name,
            } => {
                assert!(
                    shim_name.starts_with("shim_"),
                    "generated primitive wrapper must use the shim_ prefix"
                );
                Some((*name, *shim))
            }
            PrimitiveDecl::UserInline { .. } => None,
        }) else {
            continue;
        };
        assert!(
            shims.insert(name, shim).is_none(),
            "duplicate harvested primitive: {}",
            name
        );
    }
    shims
}

#[cfg(test)]
mod tests;
