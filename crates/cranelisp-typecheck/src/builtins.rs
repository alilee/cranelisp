//! Register Ring 0 primitives and special forms in the typechecker.
//!
//! Ring 0: 19 monomorphic named primitives (add-i64, add-f64, eq-i64, ..., not).
//! Ring 1: 8 monomorphic string/conversion externs + 4 polymorphic Vec externs.
//! Ring 2 adds trait-dispatched Num.+ etc. on top of these.
//!
//! Primitives are registered as ordinary symbol table entries with monomorphic
//! schemes and `DefKind::Primitive { primitive_kind: PrimitiveKind::Inline }`.
//! Vec primitives use polymorphic schemes with quantified type variables.
//! No `builtin_operators` HashSet is needed — the DefKind is sufficient for lookup.

use std::collections::HashMap;

use cranelisp_types::{
    ring0_primitives, ring1_primitives, DefKind, JitSymbol, ModuleEntry, PrimitiveKind,
    Scheme, Span, Symbol, TraitDecl, TraitMethodSig, TraitName, Type, TypeExpr, TypeName,
    Visibility,
};

use crate::checker::TypeChecker;
use crate::scheme::mono;

impl TypeChecker {
    /// Register all builtins: Ring 0 + Ring 1 primitives, special forms,
    /// Ring 2 core traits and builtin impls.
    pub(crate) fn register_builtins(&mut self) {
        self.register_primitives();
        self.register_ring1_primitives();
        self.register_vec_primitives();
        self.register_special_forms();
        self.register_core_traits();
        self.register_builtin_impls();
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

    /// Register Ring 1 extern primitives from the authoritative table.
    ///
    /// These are string and type conversion functions implemented as extern "C"
    /// functions. The backend calls them via JIT symbol references, not inline IR.
    fn register_ring1_primitives(&mut self) {
        for prim in ring1_primitives() {
            let scheme = mono(prim.ty.clone());

            self.symbol_table.insert(
                prim.name.clone(),
                ModuleEntry::Def {
                    scheme,
                    visibility: Visibility::Public,
                    docstring: None,
                    param_names: prim.param_names.clone(),
                    kind: Box::new(DefKind::Primitive {
                        primitive_kind: PrimitiveKind::Extern,
                        jit_name: Some(JitSymbol::from(prim.name.as_ref())),
                    }),
                },
            );
        }
    }

    /// Register Vec primitives with polymorphic type schemes.
    ///
    /// Vec primitives are polymorphic over the element type:
    /// - `vec-get  :: forall a. (Fn [(Vec a) Int] a)`
    /// - `vec-set  :: forall a. (Fn [(Vec a) Int a] (Vec a))`
    /// - `vec-push :: forall a. (Fn [(Vec a) a] (Vec a))`
    /// - `vec-len  :: forall a. (Fn [(Vec a)] Int)`
    ///
    /// Unlike Ring 1 string primitives (monomorphic), these require quantified
    /// type variables so the typechecker can instantiate them at each call site.
    fn register_vec_primitives(&mut self) {
        // Allocate a fresh type variable ID for the polymorphic parameter 'a'.
        // This ensures the scheme's Var(a) won't collide with any Var already
        // in use by the typechecker, preventing infinite recursion in `apply`
        // when `instantiate` maps Var(a) to a fresh var.
        let (_, a) = self.fresh_var_id();
        let vec_a = Type::ADT(TypeName::from("Vec"), vec![Type::Var(a)]);

        let vec_prims: Vec<(&str, Vec<Symbol>, Scheme)> = vec![
            // vec-get :: forall a. (Fn [(Vec a) Int] a)
            (
                "vec-get",
                vec![Symbol::from("v"), Symbol::from("idx")],
                Scheme {
                    vars: vec![a],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![vec_a.clone(), Type::Int], Box::new(Type::Var(a))),
                },
            ),
            // vec-set :: forall a. (Fn [(Vec a) Int a] (Vec a))
            (
                "vec-set",
                vec![Symbol::from("v"), Symbol::from("idx"), Symbol::from("val")],
                Scheme {
                    vars: vec![a],
                    constraints: HashMap::new(),
                    ty: Type::Fn(
                        vec![vec_a.clone(), Type::Int, Type::Var(a)],
                        Box::new(vec_a.clone()),
                    ),
                },
            ),
            // vec-push :: forall a. (Fn [(Vec a) a] (Vec a))
            (
                "vec-push",
                vec![Symbol::from("v"), Symbol::from("val")],
                Scheme {
                    vars: vec![a],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![vec_a.clone(), Type::Var(a)], Box::new(vec_a.clone())),
                },
            ),
            // vec-len :: forall a. (Fn [(Vec a)] Int)
            (
                "vec-len",
                vec![Symbol::from("v")],
                Scheme {
                    vars: vec![a],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![vec_a.clone()], Box::new(Type::Int)),
                },
            ),
        ];

        for (name, param_names, scheme) in vec_prims {
            self.symbol_table.insert(
                Symbol::from(name),
                ModuleEntry::Def {
                    scheme,
                    visibility: Visibility::Public,
                    docstring: None,
                    param_names,
                    kind: Box::new(DefKind::Primitive {
                        primitive_kind: PrimitiveKind::Extern,
                        jit_name: Some(JitSymbol::from(name)),
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
            ("deftrait", "trait declaration: (deftrait (TraitName a) (method [a ...] ret) ...)"),
            ("impl", "trait implementation: (impl TraitName Type (method [params] body) ...)"),
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

    /// Register core traits: Num, Eq, Ord.
    ///
    /// These are registered at startup, not from stdlib files.
    /// See interfaces.md Ring 2A for the authoritative trait table.
    fn register_core_traits(&mut self) {
        self.register_num_trait();
        self.register_eq_trait();
        self.register_ord_trait();
    }

    /// Register the Num trait: + - * / :: (Fn [a a] a)
    fn register_num_trait(&mut self) {
        let methods: Vec<(&str, &[&str])> = vec![
            ("+", &["lhs", "rhs"]),
            ("-", &["lhs", "rhs"]),
            ("*", &["lhs", "rhs"]),
            ("/", &["lhs", "rhs"]),
        ];

        let method_sigs: Vec<TraitMethodSig> = methods
            .into_iter()
            .map(|(name, params)| self.make_aa_a_method(name, params))
            .collect();

        let decl = TraitDecl {
            name: TraitName::from("Num"),
            docstring: Some("Numeric operations".to_string()),
            type_params: vec![Symbol::from("a")],
            methods: method_sigs,
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };

        // Use register_trait_decl which handles method registration
        self.register_trait_decl(&decl)
            .unwrap_or_else(|e| {
                unreachable!("invariant: core trait Num registration failed: {e}")
            });
    }

    /// Register the Eq trait: = != :: (Fn [a a] Bool)
    fn register_eq_trait(&mut self) {
        let eq_method = self.make_aa_bool_method("=", &["lhs", "rhs"]);
        let neq_method = self.make_aa_bool_method_with_default(
            "!=",
            &["x", "y"],
        );

        let decl = TraitDecl {
            name: TraitName::from("Eq"),
            docstring: Some("Equality".to_string()),
            type_params: vec![Symbol::from("a")],
            methods: vec![eq_method, neq_method],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };

        self.register_trait_decl(&decl)
            .unwrap_or_else(|e| {
                unreachable!("invariant: core trait Eq registration failed: {e}")
            });
    }

    /// Register the Ord trait: < > <= >= :: (Fn [a a] Bool)
    fn register_ord_trait(&mut self) {
        let lt_method = self.make_aa_bool_method("<", &["lhs", "rhs"]);
        let gt_method = self.make_aa_bool_method_with_default(
            ">",
            &["x", "y"],
        );
        let le_method = self.make_aa_bool_method_with_default(
            "<=",
            &["x", "y"],
        );
        let ge_method = self.make_aa_bool_method_with_default(
            ">=",
            &["x", "y"],
        );

        let decl = TraitDecl {
            name: TraitName::from("Ord"),
            docstring: Some("Ordering".to_string()),
            type_params: vec![Symbol::from("a")],
            methods: vec![lt_method, gt_method, le_method, ge_method],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };

        self.register_trait_decl(&decl)
            .unwrap_or_else(|e| {
                unreachable!("invariant: core trait Ord registration failed: {e}")
            });
    }

    /// Helper: build a method sig of shape (Fn [a a] a) — for Num ops.
    fn make_aa_a_method(
        &self,
        name: &str,
        param_names: &[&str],
    ) -> TraitMethodSig {
        TraitMethodSig {
            name: Symbol::from(name),
            docstring: None,
            params: vec![
                TypeExpr::TypeVar(Symbol::from("a")),
                TypeExpr::TypeVar(Symbol::from("a")),
            ],
            ret_type: TypeExpr::TypeVar(Symbol::from("a")),
            span: Span::SYNTHETIC,
            hkt_param_index: None,
            default_param_names: param_names
                .iter()
                .map(|s| Symbol::from(*s))
                .collect(),
            default_body: None,
        }
    }

    /// Helper: build a method sig of shape (Fn [a a] Bool) — for Eq/Ord.
    fn make_aa_bool_method(
        &self,
        name: &str,
        param_names: &[&str],
    ) -> TraitMethodSig {
        TraitMethodSig {
            name: Symbol::from(name),
            docstring: None,
            params: vec![
                TypeExpr::TypeVar(Symbol::from("a")),
                TypeExpr::TypeVar(Symbol::from("a")),
            ],
            ret_type: TypeExpr::Named(TypeName::from("Bool")),
            span: Span::SYNTHETIC,
            hkt_param_index: None,
            default_param_names: param_names
                .iter()
                .map(|s| Symbol::from(*s))
                .collect(),
            default_body: None,
        }
    }

    /// Helper: method sig of shape (Fn [a a] Bool) with a default body marker.
    fn make_aa_bool_method_with_default(
        &self,
        name: &str,
        param_names: &[&str],
    ) -> TraitMethodSig {
        // The default body is represented as a Sexp placeholder.
        // Actual default method generation happens in impl registration.
        TraitMethodSig {
            name: Symbol::from(name),
            docstring: None,
            params: vec![
                TypeExpr::TypeVar(Symbol::from("a")),
                TypeExpr::TypeVar(Symbol::from("a")),
            ],
            ret_type: TypeExpr::Named(TypeName::from("Bool")),
            span: Span::SYNTHETIC,
            hkt_param_index: None,
            default_param_names: param_names
                .iter()
                .map(|s| Symbol::from(*s))
                .collect(),
            default_body: Some(cranelisp_types::Sexp::Symbol(
                "default".to_string(),
                Span::SYNTHETIC,
            )),
        }
    }

    /// Register builtin trait implementations.
    ///
    /// See interfaces.md Ring 2A for the authoritative impl table.
    fn register_builtin_impls(&mut self) {
        // Num for Int
        self.register_builtin_impl(
            TraitName::from("Num"),
            TypeName::from("Int"),
            vec![
                (Symbol::from("+"), Symbol::from("add-i64")),
                (Symbol::from("-"), Symbol::from("sub-i64")),
                (Symbol::from("*"), Symbol::from("mul-i64")),
                (Symbol::from("/"), Symbol::from("div-i64")),
            ],
        );

        // Num for Float
        self.register_builtin_impl(
            TraitName::from("Num"),
            TypeName::from("Float"),
            vec![
                (Symbol::from("+"), Symbol::from("add-f64")),
                (Symbol::from("-"), Symbol::from("sub-f64")),
                (Symbol::from("*"), Symbol::from("mul-f64")),
                (Symbol::from("/"), Symbol::from("div-f64")),
            ],
        );

        // Eq for Int
        self.register_builtin_impl(
            TraitName::from("Eq"),
            TypeName::from("Int"),
            vec![(Symbol::from("="), Symbol::from("eq-i64"))],
        );

        // Eq for Float
        self.register_builtin_impl(
            TraitName::from("Eq"),
            TypeName::from("Float"),
            vec![(Symbol::from("="), Symbol::from("eq-f64"))],
        );

        // Eq for Bool
        self.register_builtin_impl(
            TraitName::from("Eq"),
            TypeName::from("Bool"),
            vec![(Symbol::from("="), Symbol::from("eq-bool"))],
        );

        // Eq for String
        self.register_builtin_impl(
            TraitName::from("Eq"),
            TypeName::from("String"),
            vec![(Symbol::from("="), Symbol::from("str-eq"))],
        );

        // Ord for Int
        self.register_builtin_impl(
            TraitName::from("Ord"),
            TypeName::from("Int"),
            vec![(Symbol::from("<"), Symbol::from("lt-i64"))],
        );

        // Ord for Float
        self.register_builtin_impl(
            TraitName::from("Ord"),
            TypeName::from("Float"),
            vec![(Symbol::from("<"), Symbol::from("lt-f64"))],
        );
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{ring0_primitives, ModuleEntry, Type};

    #[test]
    fn test_primitives_registered() {
        let tc = TypeChecker::new();
        // All 20 primitives should be in the symbol table
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
        let forms = ["if", "let", "fn", "defn", "deftype", "match", "deftrait", "impl"];
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
        let bool_cmp = prims.iter().filter(|p| p.name.as_ref() == "eq-bool").count();
        assert_eq!(int_arith, 4, "4 int arithmetic ops (add-i64/sub-i64/mul-i64/div-i64)");
        assert_eq!(float_arith, 4, "4 float arithmetic ops (add-f64/sub-f64/mul-f64/div-f64)");
        assert_eq!(int_cmp, 5, "5 int comparisons");
        assert_eq!(float_cmp, 5, "5 float comparisons");
        assert_eq!(bool_op, 1, "1 boolean op (not)");
        assert_eq!(bool_cmp, 1, "1 boolean comparison (eq-bool)");
    }

    #[test]
    fn test_vec_primitives_registered() {
        let tc = TypeChecker::new();
        let vec_ops = ["vec-get", "vec-set", "vec-push", "vec-len"];
        for name in vec_ops {
            assert!(
                tc.symbol_table.get(name).is_some(),
                "Vec primitive {name} should be in symbol table"
            );
        }
    }

    #[test]
    fn test_vec_get_scheme_is_polymorphic() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, kind, .. }) = tc.symbol_table.get("vec-get") {
            assert_eq!(scheme.vars.len(), 1, "vec-get should have 1 quantified var");
            // Type: (Fn [(Vec a) Int] a)
            if let Type::Fn(params, ret) = &scheme.ty {
                assert_eq!(params.len(), 2);
                assert!(matches!(&params[0], Type::ADT(name, _) if name.as_ref() == "Vec"));
                assert_eq!(params[1], Type::Int);
                assert!(matches!(ret.as_ref(), Type::Var(_)));
            } else {
                panic!("vec-get should be a function type");
            }
            assert!(
                matches!(kind.as_ref(), DefKind::Primitive { primitive_kind: PrimitiveKind::Extern, .. }),
                "vec-get should be Primitive::Extern"
            );
        } else {
            panic!("vec-get not found");
        }
    }

    #[test]
    fn test_vec_set_scheme_is_polymorphic() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("vec-set") {
            assert_eq!(scheme.vars.len(), 1, "vec-set should have 1 quantified var");
            if let Type::Fn(params, ret) = &scheme.ty {
                assert_eq!(params.len(), 3, "vec-set takes (Vec a), Int, a");
                assert!(matches!(&params[0], Type::ADT(name, _) if name.as_ref() == "Vec"));
                assert_eq!(params[1], Type::Int);
                // ret is (Vec a)
                assert!(matches!(ret.as_ref(), Type::ADT(name, _) if name.as_ref() == "Vec"));
            } else {
                panic!("vec-set should be a function type");
            }
        } else {
            panic!("vec-set not found");
        }
    }

    #[test]
    fn test_vec_push_scheme_is_polymorphic() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("vec-push") {
            assert_eq!(scheme.vars.len(), 1, "vec-push should have 1 quantified var");
            if let Type::Fn(params, ret) = &scheme.ty {
                assert_eq!(params.len(), 2, "vec-push takes (Vec a), a");
                assert!(matches!(ret.as_ref(), Type::ADT(name, _) if name.as_ref() == "Vec"));
            } else {
                panic!("vec-push should be a function type");
            }
        } else {
            panic!("vec-push not found");
        }
    }

    #[test]
    fn test_vec_len_scheme_is_polymorphic() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("vec-len") {
            assert_eq!(scheme.vars.len(), 1, "vec-len should have 1 quantified var");
            if let Type::Fn(params, ret) = &scheme.ty {
                assert_eq!(params.len(), 1, "vec-len takes (Vec a)");
                assert!(matches!(&params[0], Type::ADT(name, _) if name.as_ref() == "Vec"));
                assert_eq!(*ret.as_ref(), Type::Int);
            } else {
                panic!("vec-len should be a function type");
            }
        } else {
            panic!("vec-len not found");
        }
    }

    #[test]
    fn test_operator_names_registered_as_trait_methods() {
        let tc = TypeChecker::new();
        // Ring 2A: operators are now registered as trait method entries
        let ops = ["+", "-", "*", "/", "=", "!=", "<", ">", "<=", ">="];
        for name in ops {
            assert!(
                tc.symbol_table.get(name).is_some(),
                "operator {name} should be registered as a trait method"
            );
        }
    }
}
