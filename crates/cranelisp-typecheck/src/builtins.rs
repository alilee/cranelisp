//! Register Ring 0 primitives and special forms in the typechecker.
//!
//! Ring 0: 19 monomorphic named primitives (add-i64, add-f64, eq-i64, ..., not).
//! Ring 2 adds trait-dispatched Num.+ etc. on top of these.
//!
//! Primitives are registered as ordinary symbol table entries with monomorphic
//! schemes and `DefKind::Primitive { primitive_kind: PrimitiveKind::Inline }`.
//! No `builtin_operators` HashSet is needed — the DefKind is sufficient for lookup.

use cranelisp_types::{ring0_primitives, DefKind, ModuleEntry, PrimitiveKind, Symbol, Type, Visibility};

use crate::checker::TypeChecker;
use crate::scheme::mono;

impl TypeChecker {
    /// Register all Ring 0 builtins: primitives and special forms.
    pub(crate) fn register_builtins(&mut self) {
        self.register_primitives();
        self.register_special_forms();
    }

    /// Register Ring 0 primitives from the authoritative table.
    ///
    /// Each primitive gets a monomorphic scheme (`mono(prim.ty)`) — no type variables.
    /// The backend recognises these via `ResolvedCall::BuiltinFn` and emits inline
    /// Cranelift IR for the `cranelift_op` field.
    fn register_primitives(&mut self) {
        for prim in ring0_primitives() {
            let scheme = mono(prim.ty.clone());

            self.symbol_table.insert(
                prim.name.clone(),
                ModuleEntry::Def {
                    scheme,
                    visibility: Visibility::Public,
                    docstring: None,
                    param_names: prim.param_names.clone(),
                    kind: Box::new(DefKind::Primitive {
                        primitive_kind: PrimitiveKind::Inline,
                        jit_name: None,
                    }),
                },
            );
        }
    }

    /// Register special form entries for REPL introspection.
    fn register_special_forms(&mut self) {
        let special_forms = vec![
            ("if", "conditional: (if cond then else)"),
            ("let", "local binding: (let [x e] body)"),
            ("fn", "lambda: (fn [params] body)"),
            ("defn", "function definition: (defn name [params] body)"),
            ("deftype", "type definition: (deftype Name ctor1 ctor2 ...)"),
            ("match", "pattern matching: (match expr [pat body] ...)"),
        ];

        for (name, desc) in special_forms {
            self.symbol_table.insert(
                Symbol::from(name),
                ModuleEntry::Def {
                    // Special forms don't have meaningful type schemes.
                    // Use a dummy scheme that won't be instantiated.
                    scheme: mono(Type::Int),
                    visibility: Visibility::Public,
                    docstring: Some(desc.to_string()),
                    param_names: vec![],
                    kind: Box::new(DefKind::SpecialForm {
                        description: desc.to_string(),
                    }),
                },
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{ring0_primitives, ModuleEntry, Type};

    #[test]
    fn test_primitives_registered() {
        let tc = TypeChecker::new();
        // All 19 primitives should be in the symbol table
        for prim in ring0_primitives() {
            assert!(
                tc.symbol_table.get(prim.name.as_ref()).is_some(),
                "primitive {} should be in symbol table",
                prim.name
            );
        }
    }

    #[test]
    fn test_add_i64_scheme() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("add-i64") {
            // Monomorphic: no quantified vars
            assert!(scheme.vars.is_empty(), "add-i64 should have no quantified vars");
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
                "add-i64: (Fn [Int Int] Int)"
            );
        } else {
            panic!("add-i64 not found in symbol table");
        }
    }

    #[test]
    fn test_add_f64_scheme() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("add-f64") {
            assert!(scheme.vars.is_empty(), "add-f64 should have no quantified vars");
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float)),
                "add-f64: (Fn [Float Float] Float)"
            );
        } else {
            panic!("add-f64 not found in symbol table");
        }
    }

    #[test]
    fn test_eq_i64_scheme() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("eq-i64") {
            assert!(scheme.vars.is_empty(), "eq-i64 should have no quantified vars");
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
                "eq-i64: (Fn [Int Int] Bool)"
            );
        } else {
            panic!("eq-i64 not found in symbol table");
        }
    }

    #[test]
    fn test_not_scheme() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("not") {
            assert!(scheme.vars.is_empty(), "not should have no quantified vars");
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Bool], Box::new(Type::Bool)),
                "not: (Fn [Bool] Bool)"
            );
        } else {
            panic!("not not found in symbol table");
        }
    }

    #[test]
    fn test_primitives_are_inline_kind() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { kind, .. }) = tc.symbol_table.get("add-i64") {
            assert!(
                matches!(
                    kind.as_ref(),
                    DefKind::Primitive { primitive_kind: PrimitiveKind::Inline, .. }
                ),
                "add-i64 should be Primitive::Inline"
            );
        } else {
            panic!("add-i64 not found");
        }
    }

    #[test]
    fn test_special_forms_registered() {
        let tc = TypeChecker::new();
        let forms = ["if", "let", "fn", "defn", "deftype", "match"];
        for name in forms {
            let entry = tc.symbol_table.get(name);
            assert!(entry.is_some(), "special form {name} should be registered");
            if let Some(ModuleEntry::Def { kind, .. }) = entry {
                assert!(
                    matches!(kind.as_ref(), DefKind::SpecialForm { .. }),
                    "{name} should be a SpecialForm"
                );
            }
        }
    }

    #[test]
    fn test_primitive_count() {
        let prims = ring0_primitives();
        // Count by name suffix which maps directly to the primitive categories
        let int_arith = prims
            .iter()
            .filter(|p| {
                matches!(p.name.as_ref(), "add-i64" | "sub-i64" | "mul-i64" | "div-i64")
            })
            .count();
        let float_arith = prims
            .iter()
            .filter(|p| {
                matches!(
                    p.name.as_ref(),
                    "add-f64" | "sub-f64" | "mul-f64" | "div-f64"
                )
            })
            .count();
        let int_cmp = prims
            .iter()
            .filter(|p| {
                matches!(p.name.as_ref(), "eq-i64" | "lt-i64" | "gt-i64" | "le-i64" | "ge-i64")
            })
            .count();
        let float_cmp = prims
            .iter()
            .filter(|p| {
                matches!(
                    p.name.as_ref(),
                    "eq-f64" | "lt-f64" | "gt-f64" | "le-f64" | "ge-f64"
                )
            })
            .count();
        let bool_op = prims.iter().filter(|p| p.name.as_ref() == "not").count();
        assert_eq!(int_arith, 4, "4 int arithmetic ops (add-i64/sub-i64/mul-i64/div-i64)");
        assert_eq!(float_arith, 4, "4 float arithmetic ops (add-f64/sub-f64/mul-f64/div-f64)");
        assert_eq!(int_cmp, 5, "5 int comparisons");
        assert_eq!(float_cmp, 5, "5 float comparisons");
        assert_eq!(bool_op, 1, "1 boolean op (not)");
    }

    #[test]
    fn test_old_operator_names_not_registered() {
        let tc = TypeChecker::new();
        // Old polymorphic operator names should NOT be in the symbol table
        let old_ops = ["+", "-", "*", "/", "=", "<", ">", "<=", ">="];
        for name in old_ops {
            assert!(
                tc.symbol_table.get(name).is_none(),
                "old operator {name} should NOT be registered (replaced by named primitives)"
            );
        }
    }
}
