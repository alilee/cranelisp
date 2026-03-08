//! Register Ring 0-3 primitives, special forms, and synthetic modules.
//!
//! Ring 0: 20 monomorphic named primitives (add-i64, add-f64, eq-i64, ..., not, eq-bool).
//! Ring 1: 8 monomorphic string/conversion externs + 4 polymorphic Vec externs.
//! Ring 3: Synthetic `macros` module (Sexp, SList ADTs + sconcat extern) +
//!         `quote-sexp` extern in `primitives`.
//!
//! Traits (Num, Eq, Ord, Display) and their impls are ordinary Cranelisp
//! defined in prelude `.cl` files, NOT compiler-seeded. Tests that need
//! operators should either load the prelude or define traits inline.
//! See design/arch/CLAUDE.md Decision 17.
//!
//! Registration order (per pipeline-orchestration.md §3):
//! 1. register_primitives()          — types + Ring 0 inline prims
//! 2. register_ring1_primitives()    — str-concat, int-to-string, etc.
//! 3. register_vec_primitives()      — vec-get, vec-set, etc.
//! 4. register_special_forms()       — defn, let, if, match, deftrait, impl, defmacro, etc.
//! 5. register_macros_module()       — Sexp, SList ADTs + sconcat extern in `macros` module
//! 6. register_ring3_primitives()    — quote-sexp in `primitives` (requires Sexp from step 5)
//! 7. import_primitives_into_user()  — copy genuine primitives -> user

use std::collections::HashMap;

use cranelisp_types::{
    ring0_primitives, ring1_primitives, ring3_primitives, ConstructorDef, DefKind, FieldDef,
    JitSymbol, ModuleEntry, ModuleFullPath, PrimitiveKind, Scheme, Span, Symbol,
    Type, TypeDefInfo, TypeExpr, TypeName, Visibility,
};

use crate::checker::TypeChecker;
use crate::scheme::mono;

impl TypeChecker {
    /// Register all builtins: Ring 0-3 primitives, special forms, synthetic modules.
    ///
    /// Registration order per pipeline-orchestration.md §3:
    /// 1. register_primitives()          — types + Ring 0 inline prims
    /// 2. register_ring1_primitives()    — str-concat, int-to-string, etc.
    /// 3. register_vec_primitives()      — vec-get, vec-set, etc.
    /// 4. register_special_forms()       — defn, let, if, match, deftrait, impl, defmacro, etc.
    /// 5. register_macros_module()       — Sexp, SList ADTs + sconcat extern in `macros` module
    /// 6. register_ring3_primitives()    — quote-sexp in `primitives` (requires Sexp from step 5)
    /// 7. import_primitives_into_user()  — copy genuine primitives -> user
    ///
    /// Traits (Num, Eq, Ord, Display) are NOT registered here — they come from
    /// prelude `.cl` files loaded through the normal module pipeline.
    pub(crate) fn register_builtins(&mut self) {
        // Ensure the `primitives` synthetic module exists.
        // Ring 3 primitives (quote-sexp) are registered there; other ring
        // primitives are registered directly in the current module (user).
        let primitives_path = ModuleFullPath::from("primitives");
        if !self.modules.contains_key(&primitives_path) {
            self.modules.insert(
                primitives_path.clone(),
                cranelisp_types::SymbolTable::new(primitives_path.clone()),
            );
        }

        self.register_primitives();
        self.register_ring1_primitives();
        self.register_vec_primitives();
        self.register_special_forms();

        // Ring 3: Seed synthetic `macros` module with SList and Sexp ADTs + sconcat.
        // Must come after primitives registration (references Int, Bool, Float, String).
        self.register_macros_module();

        // Ring 3: quote-sexp in `primitives` — must come after register_macros_module()
        // because the type references Sexp.
        self.register_ring3_primitives();

        // Copy entries from `primitives` into `user` module (quote-sexp, etc.).
        self.import_primitives_into_user(&primitives_path);
    }

    /// Copy all entries from the `primitives` module into the `user` module.
    ///
    /// Makes named primitives (add-i64, str-concat, quote-sexp, etc.), types
    /// (Vec, Option), and special forms visible in `user` as direct entries.
    /// Does NOT copy entries from `macros` — those are accessed via qualified
    /// names (`macros/sconcat`) or explicit import.
    fn import_primitives_into_user(&mut self, primitives_path: &ModuleFullPath) {
        let user_path = ModuleFullPath::from("user");

        // Collect entries to copy (avoid borrowing self.modules while mutating).
        let entries_to_copy: Vec<(Symbol, ModuleEntry)> = self
            .modules
            .get(primitives_path)
            .map(|table| {
                table
                    .all_symbols()
                    .map(|(name, entry)| (name.clone(), entry.clone()))
                    .collect()
            })
            .unwrap_or_default();

        // Insert copies into user module.
        if let Some(user_table) = self.modules.get_mut(&user_path) {
            for (name, entry) in entries_to_copy {
                // Don't overwrite existing entries (e.g. primitives already in user).
                if user_table.get(name.as_ref()).is_none() {
                    user_table.insert(name, entry);
                }
            }
        }
    }

    /// Register Ring 0 primitives from the authoritative table.
    ///
    /// Each primitive gets a monomorphic scheme (`mono(prim.ty)`) — no type variables.
    /// The backend recognises these via `ResolvedCall::BuiltinFn` and emits inline
    /// Cranelift IR for the `cranelift_op` field.
    fn register_primitives(&mut self) {
        for prim in ring0_primitives() {
            let scheme = mono(prim.ty.clone());

            self.current_symbol_table_mut().insert(
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

            self.current_symbol_table_mut().insert(
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
            self.current_symbol_table_mut().insert(
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
            self.current_symbol_table_mut().insert(
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

    /// Register Ring 3 extern primitives in the `primitives` module.
    ///
    /// These depend on the `Sexp` type from `register_macros_module()` and
    /// MUST be called after it. Currently contains `quote-sexp`.
    ///
    /// Registered in `primitives` (not `user`) so that `import_primitives_into_user()`
    /// copies them into `user` alongside Ring 0-1 primitives.
    fn register_ring3_primitives(&mut self) {
        let primitives_path = ModuleFullPath::from("primitives");
        let primitives_table = self
            .modules
            .get_mut(&primitives_path)
            .expect("primitives module should exist");

        for prim in ring3_primitives() {
            let scheme = mono(prim.ty.clone());

            primitives_table.insert(
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

    /// Register the synthetic `macros` module with SList and Sexp ADTs + sconcat extern.
    ///
    /// The `macros` module is compiler-seeded (like `primitives`) and contains
    /// the S-expression types used by the macro system (spec §9.1):
    ///
    /// ```clojure
    /// (deftype (SList a) SNil (SCons [:a shead :(SList a) stail]))
    /// (deftype Sexp
    ///   (SexpInt [:Int sval])
    ///   (SexpFloat [:Float sval])
    ///   (SexpBool [:Bool sval])
    ///   (SexpStr [:String sval])
    ///   (SexpSym [:String sname])
    ///   (SexpList [:(SList Sexp) sitems])
    ///   (SexpBracket [:(SList Sexp) sitems]))
    /// ```
    ///
    /// Also registers `sconcat` as an extern primitive in this module:
    /// ```clojure
    /// sconcat :: (Fn [(SList Sexp) (SList Sexp)] (SList Sexp))
    /// ```
    ///
    /// These are NOT auto-imported into `user`. Access is via qualified names
    /// (`macros/SexpSym`, `macros/SCons`, `macros/sconcat`, etc.) or explicit import.
    fn register_macros_module(&mut self) {
        // Switch to the synthetic `macros` module.
        let saved_module = self.current_module_path().clone();
        let macros_path = ModuleFullPath::from("macros");
        self.set_current_module(macros_path);

        self.register_slist_type();
        self.register_sexp_type();
        self.register_sconcat();

        // Restore the original module context.
        self.set_current_module(saved_module);
    }

    /// Register `sconcat` as an extern primitive in the `macros` module.
    ///
    /// Type: `(Fn [(SList Sexp) (SList Sexp)] (SList Sexp))`
    /// The quasiquote expander emits `macros/sconcat` calls to concatenate
    /// S-expression lists during macro expansion.
    fn register_sconcat(&mut self) {
        let slist_sexp = Type::ADT(
            TypeName::from("SList"),
            vec![Type::ADT(TypeName::from("Sexp"), vec![])],
        );
        let sconcat_type = Type::Fn(
            vec![slist_sexp.clone(), slist_sexp.clone()],
            Box::new(slist_sexp),
        );

        self.current_symbol_table_mut().insert(
            Symbol::from("sconcat"),
            ModuleEntry::Def {
                scheme: mono(sconcat_type),
                visibility: Visibility::Public,
                docstring: Some("Concatenate two SList Sexp values".to_string()),
                param_names: vec![Symbol::from("a"), Symbol::from("b")],
                kind: Box::new(DefKind::Primitive {
                    primitive_kind: PrimitiveKind::Extern,
                    jit_name: Some(JitSymbol::from("sconcat")),
                }),
            },
        );
    }

    /// Register `(deftype (SList a) SNil (SCons [:a shead :(SList a) stail]))`.
    fn register_slist_type(&mut self) {
        // Pre-seed SList in type_defs so SCons's self-referential stail field resolves.
        self.type_defs.type_defs.insert(
            TypeName::from("SList"),
            TypeDefInfo {
                name: TypeName::from("SList"),
                type_params: vec![Symbol::from("a")],
                constructors: vec![],
                docstring: None,
            },
        );

        let slist_ctors = vec![
            // SNil: nullary constructor (tag 0)
            ConstructorDef {
                name: Symbol::from("SNil"),
                docstring: None,
                fields: vec![],
                span: Span::SYNTHETIC,
            },
            // SCons: data constructor (tag 1) — shead: :a, stail: :(SList a)
            ConstructorDef {
                name: Symbol::from("SCons"),
                docstring: None,
                fields: vec![
                    FieldDef {
                        name: Symbol::from("shead"),
                        type_expr: TypeExpr::TypeVar(Symbol::from("a")),
                    },
                    FieldDef {
                        name: Symbol::from("stail"),
                        type_expr: TypeExpr::Applied(
                            TypeName::from("SList"),
                            vec![TypeExpr::TypeVar(Symbol::from("a"))],
                        ),
                    },
                ],
                span: Span::SYNTHETIC,
            },
        ];

        self.register_type_def(
            &TypeName::from("SList"),
            &None,
            &[Symbol::from("a")],
            &slist_ctors,
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap_or_else(|e| {
            unreachable!("invariant: SList type registration failed: {e}")
        });
    }

    /// Register the Sexp type with 7 data constructors (SexpInt through SexpBracket).
    fn register_sexp_type(&mut self) {
        // Pre-seed Sexp so SexpList/SexpBracket's :(SList Sexp) fields resolve.
        self.type_defs.type_defs.insert(
            TypeName::from("Sexp"),
            TypeDefInfo {
                name: TypeName::from("Sexp"),
                type_params: vec![],
                constructors: vec![],
                docstring: None,
            },
        );

        let slist_sexp = TypeExpr::Applied(
            TypeName::from("SList"),
            vec![TypeExpr::Named(TypeName::from("Sexp"))],
        );

        let sexp_ctors = vec![
            Self::sexp_ctor("SexpInt", "sval", TypeExpr::Named(TypeName::from("Int"))),
            Self::sexp_ctor("SexpFloat", "sval", TypeExpr::Named(TypeName::from("Float"))),
            Self::sexp_ctor("SexpBool", "sval", TypeExpr::Named(TypeName::from("Bool"))),
            Self::sexp_ctor("SexpStr", "sval", TypeExpr::Named(TypeName::from("String"))),
            Self::sexp_ctor("SexpSym", "sname", TypeExpr::Named(TypeName::from("String"))),
            Self::sexp_ctor("SexpList", "sitems", slist_sexp.clone()),
            Self::sexp_ctor("SexpBracket", "sitems", slist_sexp),
        ];

        self.register_type_def(
            &TypeName::from("Sexp"),
            &None,
            &[],
            &sexp_ctors,
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap_or_else(|e| {
            unreachable!("invariant: Sexp type registration failed: {e}")
        });
    }

    /// Build a single-field Sexp constructor definition.
    fn sexp_ctor(name: &str, field: &str, type_expr: TypeExpr) -> ConstructorDef {
        ConstructorDef {
            name: Symbol::from(name),
            docstring: None,
            fields: vec![FieldDef {
                name: Symbol::from(field),
                type_expr,
            }],
            span: Span::SYNTHETIC,
        }
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{ring0_primitives, ModuleEntry, Type};

    // spec: appendix-a-builtins §A.2 — all ring-0 primitives registered in symbol table
    #[test]
    fn test_primitives_registered() {
        let tc = TypeChecker::new();
        // All 20 primitives should be in the symbol table
        for prim in ring0_primitives() {
            assert!(
                tc.symbol_table().get(prim.name.as_ref()).is_some(),
                "primitive {} should be in symbol table",
                prim.name
            );
        }
    }

    // spec: appendix-a-builtins §A.2 — add-i64 has monomorphic (Fn [Int Int] Int) scheme
    #[test]
    fn test_add_i64_scheme() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-i64") {
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

    // spec: appendix-a-builtins §A.2 — add-f64 has monomorphic (Fn [Float Float] Float) scheme
    #[test]
    fn test_add_f64_scheme() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-f64") {
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

    // spec: appendix-a-builtins §A.2 — eq-i64 has monomorphic (Fn [Int Int] Bool) scheme
    #[test]
    fn test_eq_i64_scheme() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("eq-i64") {
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

    // spec: appendix-a-builtins §A.3 — not has monomorphic (Fn [Bool] Bool) scheme
    #[test]
    fn test_not_scheme() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("not") {
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

    // spec: appendix-a-builtins §A.2 — arithmetic primitives are inline kind
    #[test]
    fn test_primitives_are_inline_kind() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { kind, .. }) = tc.symbol_table().get("add-i64") {
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

    // spec: appendix-a-builtins §A.1 — special forms registered in symbol table
    #[test]
    fn test_special_forms_registered() {
        let tc = TypeChecker::new();
        let forms = ["if", "let", "fn", "defn", "deftype", "match", "deftrait", "impl"];
        for name in forms {
            let entry = tc.symbol_table().get(name);
            assert!(entry.is_some(), "special form {name} should be registered");
            if let Some(ModuleEntry::Def { kind, .. }) = entry {
                assert!(
                    matches!(kind.as_ref(), DefKind::SpecialForm { .. }),
                    "{name} should be a SpecialForm"
                );
            }
        }
    }

    // spec: appendix-a-builtins §A.2 — primitive count by category matches spec
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

    // spec: 03-types §3.2.4 — Vec primitive operations registered
    #[test]
    fn test_vec_primitives_registered() {
        let tc = TypeChecker::new();
        let vec_ops = ["vec-get", "vec-set", "vec-push", "vec-len"];
        for name in vec_ops {
            assert!(
                tc.symbol_table().get(name).is_some(),
                "Vec primitive {name} should be in symbol table"
            );
        }
    }

    // spec: 03-types §3.2.4 — vec-get is polymorphic (Fn [(Vec a) Int] a)
    #[test]
    fn test_vec_get_scheme_is_polymorphic() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, kind, .. }) = tc.symbol_table().get("vec-get") {
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

    // spec: 03-types §3.2.4 — vec-set is polymorphic (Fn [(Vec a) Int a] (Vec a))
    #[test]
    fn test_vec_set_scheme_is_polymorphic() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("vec-set") {
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

    // spec: 03-types §3.2.4 — vec-push is polymorphic (Fn [(Vec a) a] (Vec a))
    #[test]
    fn test_vec_push_scheme_is_polymorphic() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("vec-push") {
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

    // spec: 03-types §3.2.4 — vec-len is polymorphic (Fn [(Vec a)] Int)
    #[test]
    fn test_vec_len_scheme_is_polymorphic() {
        let tc = TypeChecker::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("vec-len") {
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

    // -----------------------------------------------------------------------
    // Decision 17 elimination: traits NOT compiler-seeded
    // -----------------------------------------------------------------------

    // spec: pipeline-orchestration §5 — no traits registered at startup
    #[test]
    fn test_no_traits_at_startup() {
        let tc = TypeChecker::new();
        assert!(
            tc.trait_registry.decls.is_empty(),
            "no traits should be registered at startup (Decision 17 eliminated)"
        );
        assert!(
            tc.impl_registry.impls.is_empty(),
            "no impls should be registered at startup"
        );
    }

    // spec: pipeline-orchestration §5 — operator symbols NOT in symbol table at startup
    #[test]
    fn test_no_operator_symbols_at_startup() {
        let tc = TypeChecker::new();
        let ops = ["+", "-", "*", "/", "=", "!=", "<", ">", "<=", ">=", "show"];
        for name in ops {
            assert!(
                tc.symbol_table().get(name).is_none(),
                "operator {name} should NOT be in symbol table at startup \
                 (traits come from prelude .cl files)"
            );
        }
    }

    // -----------------------------------------------------------------------
    // Synthetic macros module tests (Ring 3, spec §9.1)
    // -----------------------------------------------------------------------

    // spec: 09-macros §9.1 — macros module exists after initialization
    #[test]
    fn test_macros_module_exists() {
        let tc = TypeChecker::new();
        let macros_path = ModuleFullPath::from("macros");
        assert!(
            tc.modules.get(&macros_path).is_some(),
            "macros module should exist after TypeChecker initialization"
        );
    }

    // spec: 09-macros §9.1.1 — SList type registered in macros module
    #[test]
    fn test_slist_type_registered() {
        let tc = TypeChecker::new();
        let info = tc.type_defs.get(&TypeName::from("SList"));
        assert!(info.is_some(), "SList type should be registered");
        let info = info.unwrap();
        assert_eq!(info.type_params.len(), 1, "SList has 1 type parameter");
        assert_eq!(info.type_params[0].as_ref(), "a");
        assert_eq!(info.constructors.len(), 2, "SList has 2 constructors: SNil, SCons");
    }

    // spec: 09-macros §9.1.1 — SNil is nullary constructor (tag 0)
    #[test]
    fn test_snil_is_nullary() {
        let tc = TypeChecker::new();
        let macros_path = ModuleFullPath::from("macros");
        let macros_table = tc.modules.get(&macros_path).unwrap();
        if let Some(ModuleEntry::Constructor { info, scheme, .. }) = macros_table.get("SNil") {
            assert_eq!(info.tag, 0, "SNil should be tag 0");
            assert!(info.fields.is_empty(), "SNil should have no fields");
            assert_eq!(scheme.vars.len(), 1, "SNil should have 1 quantified var (polymorphic)");
            // SNil :: forall [a]. (SList a)
            match &scheme.ty {
                Type::ADT(name, args) => {
                    assert_eq!(name.as_ref(), "SList");
                    assert_eq!(args.len(), 1);
                    assert!(matches!(args[0], Type::Var(_)));
                }
                _ => panic!("SNil should have ADT type, got {:?}", scheme.ty),
            }
        } else {
            panic!("SNil should be a Constructor entry in macros module");
        }
    }

    // spec: 09-macros §9.1.1 — SCons constructor: (Fn [a (SList a)] (SList a))
    #[test]
    fn test_scons_constructor_type() {
        let tc = TypeChecker::new();
        let macros_path = ModuleFullPath::from("macros");
        let macros_table = tc.modules.get(&macros_path).unwrap();
        if let Some(ModuleEntry::Constructor { info, scheme, .. }) = macros_table.get("SCons") {
            assert_eq!(info.tag, 1, "SCons should be tag 1");
            assert_eq!(info.fields.len(), 2, "SCons has 2 fields: shead, stail");
            assert_eq!(info.fields[0].name.as_ref(), "shead");
            assert_eq!(info.fields[1].name.as_ref(), "stail");
            assert_eq!(scheme.vars.len(), 1, "SCons should have 1 quantified var");
            // SCons :: forall [a]. (Fn [a (SList a)] (SList a))
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 2);
                    // First param: a (type var)
                    assert!(matches!(params[0], Type::Var(_)), "first param should be type var");
                    // Second param: (SList a)
                    match &params[1] {
                        Type::ADT(name, args) => {
                            assert_eq!(name.as_ref(), "SList");
                            assert_eq!(args.len(), 1);
                            // SList's type arg should be the same var as the first param
                            assert_eq!(params[0], args[0]);
                        }
                        _ => panic!("second SCons param should be (SList a)"),
                    }
                    // Return: (SList a)
                    match ret.as_ref() {
                        Type::ADT(name, args) => {
                            assert_eq!(name.as_ref(), "SList");
                            assert_eq!(args.len(), 1);
                            assert_eq!(params[0], args[0]);
                        }
                        _ => panic!("SCons return should be (SList a)"),
                    }
                }
                _ => panic!("SCons should have Fn type, got {:?}", scheme.ty),
            }
        } else {
            panic!("SCons should be a Constructor entry in macros module");
        }
    }

    // spec: 09-macros §9.1.2 — Sexp type registered with 7 constructors
    #[test]
    fn test_sexp_type_registered() {
        let tc = TypeChecker::new();
        let info = tc.type_defs.get(&TypeName::from("Sexp"));
        assert!(info.is_some(), "Sexp type should be registered");
        let info = info.unwrap();
        assert!(info.type_params.is_empty(), "Sexp has 0 type parameters");
        assert_eq!(info.constructors.len(), 7, "Sexp has 7 constructors");

        // Verify tag order matches spec: SexpInt=0 through SexpBracket=6
        let expected_names = [
            "SexpInt", "SexpFloat", "SexpBool", "SexpStr",
            "SexpSym", "SexpList", "SexpBracket",
        ];
        for (i, name) in expected_names.iter().enumerate() {
            assert_eq!(
                info.constructors[i].name.as_ref(), *name,
                "constructor at tag {i} should be {name}"
            );
            assert_eq!(info.constructors[i].tag, i, "{name} should have tag {i}");
        }
    }

    // spec: 09-macros §9.1.2 — SexpSym constructor: (Fn [String] Sexp)
    #[test]
    fn test_sexpsym_constructor_type() {
        let tc = TypeChecker::new();
        let macros_path = ModuleFullPath::from("macros");
        let macros_table = tc.modules.get(&macros_path).unwrap();
        if let Some(ModuleEntry::Constructor { scheme, .. }) = macros_table.get("SexpSym") {
            assert!(scheme.vars.is_empty(), "SexpSym should be monomorphic");
            assert_eq!(
                scheme.ty,
                Type::Fn(
                    vec![Type::String],
                    Box::new(Type::ADT(TypeName::from("Sexp"), vec![]))
                ),
                "SexpSym :: (Fn [String] Sexp)"
            );
        } else {
            panic!("SexpSym should be a Constructor entry in macros module");
        }
    }

    // spec: 09-macros §9.1.2 — all 7 Sexp constructors have correct field types
    #[test]
    fn test_all_sexp_constructor_field_types() {
        let tc = TypeChecker::new();
        let macros_path = ModuleFullPath::from("macros");
        let macros_table = tc.modules.get(&macros_path).unwrap();

        let sexp_type = Type::ADT(TypeName::from("Sexp"), vec![]);
        let slist_sexp_type = Type::ADT(
            TypeName::from("SList"),
            vec![Type::ADT(TypeName::from("Sexp"), vec![])],
        );

        // (SexpInt [:Int sval]) -> (Fn [Int] Sexp)
        check_sexp_ctor(&macros_table, "SexpInt", &[("sval", &Type::Int)], &sexp_type);
        // (SexpFloat [:Float sval]) -> (Fn [Float] Sexp)
        check_sexp_ctor(&macros_table, "SexpFloat", &[("sval", &Type::Float)], &sexp_type);
        // (SexpBool [:Bool sval]) -> (Fn [Bool] Sexp)
        check_sexp_ctor(&macros_table, "SexpBool", &[("sval", &Type::Bool)], &sexp_type);
        // (SexpStr [:String sval]) -> (Fn [String] Sexp)
        check_sexp_ctor(&macros_table, "SexpStr", &[("sval", &Type::String)], &sexp_type);
        // (SexpSym [:String sname]) -> (Fn [String] Sexp)
        check_sexp_ctor(&macros_table, "SexpSym", &[("sname", &Type::String)], &sexp_type);
        // (SexpList [:(SList Sexp) sitems]) -> (Fn [(SList Sexp)] Sexp)
        check_sexp_ctor(&macros_table, "SexpList", &[("sitems", &slist_sexp_type)], &sexp_type);
        // (SexpBracket [:(SList Sexp) sitems]) -> (Fn [(SList Sexp)] Sexp)
        check_sexp_ctor(&macros_table, "SexpBracket", &[("sitems", &slist_sexp_type)], &sexp_type);
    }

    /// Helper: verify a Sexp constructor has the expected fields and function type.
    fn check_sexp_ctor(
        table: &cranelisp_types::SymbolTable,
        name: &str,
        expected_fields: &[(&str, &Type)],
        ret_type: &Type,
    ) {
        if let Some(ModuleEntry::Constructor { info, scheme, .. }) = table.get(name) {
            assert_eq!(
                info.fields.len(),
                expected_fields.len(),
                "{name}: field count mismatch"
            );
            for (i, (fname, ftype)) in expected_fields.iter().enumerate() {
                assert_eq!(
                    info.fields[i].name.as_ref(), *fname,
                    "{name}: field {i} name"
                );
                assert_eq!(
                    &info.fields[i].ty, *ftype,
                    "{name}: field {i} type"
                );
            }
            // Check the constructor scheme
            assert!(scheme.vars.is_empty(), "{name} should be monomorphic");
            let param_types: Vec<Type> = expected_fields.iter().map(|(_, t)| (*t).clone()).collect();
            assert_eq!(
                scheme.ty,
                Type::Fn(param_types, Box::new(ret_type.clone())),
                "{name}: constructor scheme"
            );
        } else {
            panic!("{name} should be a Constructor entry");
        }
    }

    // spec: 09-macros §9.1.3 — qualified access macros/SexpSym works from user module
    #[test]
    fn test_qualified_access_from_user() {
        let tc = TypeChecker::new();
        // The TypeChecker's current module is "user" by default.
        // Qualified lookup: "macros/SexpSym" should resolve.
        let scheme = tc.lookup("macros/SexpSym");
        assert!(
            scheme.is_some(),
            "macros/SexpSym should be resolvable from user module"
        );
        let scheme = scheme.unwrap();
        assert_eq!(
            scheme.ty,
            Type::Fn(
                vec![Type::String],
                Box::new(Type::ADT(TypeName::from("Sexp"), vec![]))
            ),
            "macros/SexpSym :: (Fn [String] Sexp)"
        );

        // Also check qualified access to SCons and SNil
        assert!(
            tc.lookup("macros/SCons").is_some(),
            "macros/SCons should be resolvable"
        );
        assert!(
            tc.lookup("macros/SNil").is_some(),
            "macros/SNil should be resolvable"
        );
    }

    // -----------------------------------------------------------------------
    // sconcat extern in macros module (P1, pipeline-orchestration §3)
    // -----------------------------------------------------------------------

    // spec: pipeline-orchestration §3 — sconcat registered as extern primitive in macros module
    #[test]
    fn test_sconcat_registered_in_macros() {
        let tc = TypeChecker::new();
        let macros_path = ModuleFullPath::from("macros");
        let macros_table = tc.modules.get(&macros_path).unwrap();
        let entry = macros_table.get("sconcat");
        assert!(entry.is_some(), "sconcat should be in macros module");

        if let Some(ModuleEntry::Def { scheme, kind, .. }) = entry {
            // Type: (Fn [(SList Sexp) (SList Sexp)] (SList Sexp))
            let slist_sexp = Type::ADT(
                TypeName::from("SList"),
                vec![Type::ADT(TypeName::from("Sexp"), vec![])],
            );
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![slist_sexp.clone(), slist_sexp.clone()], Box::new(slist_sexp)),
                "sconcat :: (Fn [(SList Sexp) (SList Sexp)] (SList Sexp))"
            );
            assert!(scheme.vars.is_empty(), "sconcat should be monomorphic");
            assert!(
                matches!(
                    kind.as_ref(),
                    DefKind::Primitive { primitive_kind: PrimitiveKind::Extern, .. }
                ),
                "sconcat should be Primitive::Extern"
            );
        } else {
            panic!("sconcat should be a Def entry");
        }
    }

    // spec: pipeline-orchestration §3 — sconcat accessible via qualified name macros/sconcat
    #[test]
    fn test_sconcat_qualified_access() {
        let tc = TypeChecker::new();
        let scheme = tc.lookup("macros/sconcat");
        assert!(
            scheme.is_some(),
            "macros/sconcat should be resolvable from user module"
        );
    }

    // spec: pipeline-orchestration §3 — sconcat NOT imported into user module
    #[test]
    fn test_sconcat_not_in_user() {
        let tc = TypeChecker::new();
        assert!(
            tc.symbol_table().get("sconcat").is_none(),
            "sconcat should NOT be in user module (it's in macros, not primitives)"
        );
    }

    // -----------------------------------------------------------------------
    // quote-sexp extern in primitives module (P2, pipeline-orchestration §3)
    // -----------------------------------------------------------------------

    // spec: pipeline-orchestration §3 — quote-sexp registered as extern primitive
    #[test]
    fn test_quote_sexp_registered() {
        let tc = TypeChecker::new();
        let entry = tc.symbol_table().get("quote-sexp");
        assert!(entry.is_some(), "quote-sexp should be in user symbol table (imported from primitives)");

        if let Some(ModuleEntry::Def { scheme, kind, .. }) = entry {
            let sexp_type = Type::ADT(TypeName::from("Sexp"), vec![]);
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![sexp_type.clone()], Box::new(sexp_type)),
                "quote-sexp :: (Fn [Sexp] Sexp)"
            );
            assert!(scheme.vars.is_empty(), "quote-sexp should be monomorphic");
            assert!(
                matches!(
                    kind.as_ref(),
                    DefKind::Primitive { primitive_kind: PrimitiveKind::Extern, .. }
                ),
                "quote-sexp should be Primitive::Extern"
            );
        } else {
            panic!("quote-sexp should be a Def entry");
        }
    }

    // spec: pipeline-orchestration §3 — quote-sexp also in primitives module directly
    #[test]
    fn test_quote_sexp_in_primitives_module() {
        let tc = TypeChecker::new();
        let primitives_path = ModuleFullPath::from("primitives");
        let primitives_table = tc.modules.get(&primitives_path).unwrap();
        assert!(
            primitives_table.get("quote-sexp").is_some(),
            "quote-sexp should be in primitives module"
        );
    }

    // -----------------------------------------------------------------------
    // Registration order (pipeline-orchestration §3)
    // -----------------------------------------------------------------------

    // spec: pipeline-orchestration §3 — registration order: primitives -> macros -> ring3 -> import
    #[test]
    fn test_registration_order_no_panic() {
        // TypeChecker::new() exercises the full registration sequence.
        // If the ordering is wrong (e.g. quote-sexp before macros module),
        // it would either panic or produce invalid types.
        let tc = TypeChecker::new();

        // Verify all expected modules exist
        assert!(tc.modules.get(&ModuleFullPath::from("user")).is_some());
        assert!(tc.modules.get(&ModuleFullPath::from("primitives")).is_some());
        assert!(tc.modules.get(&ModuleFullPath::from("macros")).is_some());

        // Verify quote-sexp has the correct type referencing Sexp (proves ordering)
        let sexp_type = Type::ADT(TypeName::from("Sexp"), vec![]);
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("quote-sexp") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![sexp_type.clone()], Box::new(sexp_type)),
            );
        } else {
            panic!("quote-sexp should be registered after macros module");
        }
    }
}
