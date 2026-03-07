//! Register Ring 0 primitives and special forms in the typechecker.
//!
//! Ring 0: 19 monomorphic named primitives (add-i64, add-f64, eq-i64, ..., not).
//! Ring 1: 8 monomorphic string/conversion externs + 4 polymorphic Vec externs.
//!
//! <!-- FIXME(/typecheck): Decision 17 — remove register_core_trait_decls(),
//!      register_core_trait_impls(), and import_primitives_into_user(). Only genuinely
//!      primitive things should be compiler-seeded (types, named primitives, special forms,
//!      synthetic modules). Traits (Num, Eq, Ord, Display) and their impls are ordinary
//!      Cranelisp expressible via deftrait/impl — they belong in the prelude (Ring 3), not
//!      in builtins. Until the prelude exists, tests/examples/demos that need operators
//!      define the traits themselves inline. See design/arch/CLAUDE.md Decision 17. -->
//!
//! Primitives are registered as ordinary symbol table entries with monomorphic
//! schemes and `DefKind::Primitive { primitive_kind: PrimitiveKind::Inline }`.
//! Vec primitives use polymorphic schemes with quantified type variables.
//! No `builtin_operators` HashSet is needed — the DefKind is sufficient for lookup.
//!
//! Primitives are registered as ordinary symbol table entries with monomorphic
//! schemes and `DefKind::Primitive { primitive_kind: PrimitiveKind::Inline }`.
//! Vec primitives use polymorphic schemes with quantified type variables.
//! No `builtin_operators` HashSet is needed — the DefKind is sufficient for lookup.

use std::collections::HashMap;

use cranelisp_types::{
    ring0_primitives, ring1_primitives, ConstructorDef, DefKind, Defn, Expr, FieldDef,
    JitSymbol, ModuleEntry, ModuleFullPath, PrimitiveKind, Scheme, Sexp, Span, Symbol,
    TraitDecl, TraitImpl, TraitMethodSig, TraitName, Type, TypeDefInfo, TypeExpr, TypeName,
    Visibility,
};

use crate::checker::TypeChecker;
use crate::scheme::mono;

impl TypeChecker {
    /// Register all builtins: Ring 0 + Ring 1 primitives, special forms,
    /// Ring 2 core traits and trait impls, Ring 3 synthetic macros module.
    pub(crate) fn register_builtins(&mut self) {
        self.register_primitives();
        self.register_ring1_primitives();
        self.register_vec_primitives();
        self.register_special_forms();

        // Core traits belong in the `primitives` module, not `user`.
        // Save current module, switch to primitives, register, then restore.
        let saved_module = self.current_module_path().clone();
        let primitives_path = ModuleFullPath::from("primitives");
        self.set_current_module(primitives_path.clone());
        self.register_core_trait_decls();
        self.register_core_trait_impls();
        self.set_current_module(saved_module);

        // Import all trait-related entries from `primitives` into `user` so they
        // are visible at the REPL and propagated to new modules via set_current_module.
        self.import_primitives_into_user(&primitives_path);

        // Ring 3: Seed synthetic `macros` module with SList and Sexp ADTs.
        // Must come after primitives registration (references Int, Bool, Float, String).
        self.register_macros_module();

        // Clear transient state accumulated during core trait impl type-checking.
        // register_trait_impl() type-checks method bodies (e.g. `(add-i64 x y)`),
        // which populates expr_types, method_resolutions, and subst with entries
        // keyed at Span::SYNTHETIC. These must not leak into user program checking.
        self.clear_transient_state();
    }

    /// Copy all entries from the `primitives` module into the `user` module.
    ///
    /// After core traits are registered in `primitives`, this makes trait methods
    /// (+, -, =, show, etc.) and trait decls (Num, Eq, Ord, Display) visible in
    /// `user` as direct entries (not imports). This ensures `set_current_module`
    /// propagates them to new modules, and `/list` displays them correctly.
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

    /// Register the synthetic `macros` module with SList and Sexp ADTs.
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
    /// These are NOT auto-imported into `user`. Access is via qualified names
    /// (`macros/SexpSym`, `macros/SCons`, etc.) or explicit import.
    fn register_macros_module(&mut self) {
        // Switch to the synthetic `macros` module.
        let saved_module = self.current_module_path().clone();
        let macros_path = ModuleFullPath::from("macros");
        self.set_current_module(macros_path);

        self.register_slist_type();
        self.register_sexp_type();

        // Restore the original module context.
        self.set_current_module(saved_module);
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

    /// Register core trait declarations: Num, Eq, Ord, Display.
    ///
    /// Constructs `TraitDecl` AST structs and routes them through the normal
    /// `register_trait_decl()` pipeline — the same path used for user-defined traits.
    ///
    /// Equivalent Cranelisp:
    /// ```clojure
    /// (deftrait (Num a) (+ [a a] a) (- [a a] a) (* [a a] a) (/ [a a] a))
    /// (deftrait (Eq a) (= [a a] Bool) (!= [x y] Bool (not (= x y))))
    /// (deftrait (Ord a) (< [a a] Bool) (> [x y] Bool (< y x))
    ///                   (<= [x y] Bool (not (< y x))) (>= [x y] Bool (not (< x y))))
    /// (deftrait (Display a) (show [a] String))
    /// ```
    fn register_core_trait_decls(&mut self) {
        // --- Num: + - * / :: (Fn [a a] a) ---
        let num_decl = TraitDecl {
            name: TraitName::from("Num"),
            docstring: Some("Numeric operations".to_string()),
            type_params: vec![Symbol::from("a")],
            methods: ["+", "-", "*", "/"]
                .iter()
                .map(|op| make_aa_a_sig(op, &["lhs", "rhs"]))
                .collect(),
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        self.register_trait_decl(&num_decl)
            .unwrap_or_else(|e| unreachable!("invariant: core trait Num registration failed: {e}"));

        // --- Eq: = :: (Fn [a a] Bool), != with default body ---
        let eq_decl = TraitDecl {
            name: TraitName::from("Eq"),
            docstring: Some("Equality".to_string()),
            type_params: vec![Symbol::from("a")],
            methods: vec![
                make_aa_bool_sig("=", &["lhs", "rhs"], false),
                make_aa_bool_sig("!=", &["x", "y"], true),
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        self.register_trait_decl(&eq_decl)
            .unwrap_or_else(|e| unreachable!("invariant: core trait Eq registration failed: {e}"));

        // --- Ord: < :: (Fn [a a] Bool), > <= >= with default bodies ---
        let ord_decl = TraitDecl {
            name: TraitName::from("Ord"),
            docstring: Some("Ordering".to_string()),
            type_params: vec![Symbol::from("a")],
            methods: vec![
                make_aa_bool_sig("<", &["lhs", "rhs"], false),
                make_aa_bool_sig(">", &["x", "y"], true),
                make_aa_bool_sig("<=", &["x", "y"], true),
                make_aa_bool_sig(">=", &["x", "y"], true),
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        self.register_trait_decl(&ord_decl)
            .unwrap_or_else(|e| unreachable!("invariant: core trait Ord registration failed: {e}"));

        // --- Display: show :: (Fn [a] String) ---
        let display_decl = TraitDecl {
            name: TraitName::from("Display"),
            docstring: Some("String representation".to_string()),
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("show"),
                docstring: None,
                params: vec![TypeExpr::TypeVar(Symbol::from("a"))],
                ret_type: TypeExpr::Named(TypeName::from("String")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_param_names: vec![Symbol::from("self")],
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        self.register_trait_decl(&display_decl)
            .unwrap_or_else(|e| unreachable!("invariant: core trait Display registration failed: {e}"));
    }

    /// Register core trait implementations for primitive types.
    ///
    /// Constructs `TraitImpl` AST structs with real method bodies that delegate
    /// to named primitives, then routes them through the normal `register_trait_impl()`
    /// pipeline. The returned `Defn` nodes are discarded — the backend's
    /// `primitive_for_trait_method()` short-circuits all core methods to inline IR.
    ///
    /// Equivalent Cranelisp:
    /// ```clojure
    /// (impl Num Int  (+ [x y] (add-i64 x y)) (- [x y] (sub-i64 x y)) ...)
    /// (impl Num Float (+ [x y] (add-f64 x y)) ...)
    /// (impl Eq Int   (= [x y] (eq-i64 x y)))
    /// (impl Eq Float (= [x y] (eq-f64 x y)))
    /// (impl Eq Bool  (= [x y] (eq-bool x y)))
    /// (impl Eq String (= [x y] (str-eq x y)))
    /// (impl Ord Int  (< [x y] (lt-i64 x y)))
    /// (impl Ord Float (< [x y] (lt-f64 x y)))
    /// (impl Display Int    (show [x] (int-to-string x)))
    /// (impl Display Float  (show [x] (float-to-string x)))
    /// (impl Display Bool   (show [x] (bool-to-string x)))
    /// (impl Display String (show [x] (string-identity x)))
    /// ```
    fn register_core_trait_impls(&mut self) {
        // --- Num impls ---
        let num_methods = ["+", "-", "*", "/"];

        // Num for Int: + → add-i64, - → sub-i64, * → mul-i64, / → div-i64
        let int_prims = ["add-i64", "sub-i64", "mul-i64", "div-i64"];
        self.register_core_impl(
            "Num",
            "Int",
            &num_methods.iter().zip(int_prims.iter())
                .map(|(m, p)| (*m, *p, &["x", "y"] as &[&str]))
                .collect::<Vec<_>>(),
        );

        // Num for Float: + → add-f64, - → sub-f64, * → mul-f64, / → div-f64
        let float_prims = ["add-f64", "sub-f64", "mul-f64", "div-f64"];
        self.register_core_impl(
            "Num",
            "Float",
            &num_methods.iter().zip(float_prims.iter())
                .map(|(m, p)| (*m, *p, &["x", "y"] as &[&str]))
                .collect::<Vec<_>>(),
        );

        // --- Eq impls (only `=` required; `!=` has default body) ---
        self.register_core_impl("Eq", "Int",    &[("=", "eq-i64", &["x", "y"])]);
        self.register_core_impl("Eq", "Float",  &[("=", "eq-f64", &["x", "y"])]);
        self.register_core_impl("Eq", "Bool",   &[("=", "eq-bool", &["x", "y"])]);
        self.register_core_impl("Eq", "String", &[("=", "str-eq", &["x", "y"])]);

        // --- Ord impls (only `<` required; `>` `<=` `>=` have default bodies) ---
        self.register_core_impl("Ord", "Int",   &[("<", "lt-i64", &["x", "y"])]);
        self.register_core_impl("Ord", "Float", &[("<", "lt-f64", &["x", "y"])]);

        // --- Display impls ---
        self.register_core_impl("Display", "Int",    &[("show", "int-to-string", &["x"])]);
        self.register_core_impl("Display", "Float",  &[("show", "float-to-string", &["x"])]);
        self.register_core_impl("Display", "Bool",   &[("show", "bool-to-string", &["x"])]);
        self.register_core_impl("Display", "String", &[("show", "string-identity", &["x"])]);
    }

    /// Register a single core trait implementation via the normal pipeline.
    ///
    /// Each entry in `methods` is `(method_name, primitive_name, param_names)`.
    /// The body of each method is `(primitive_name param1 param2 ...)`.
    fn register_core_impl(
        &mut self,
        trait_name: &str,
        target_type: &str,
        methods: &[(&str, &str, &[&str])],
    ) {
        let method_defns: Vec<Defn> = methods
            .iter()
            .map(|(method_name, prim_name, param_names)| {
                let params: Vec<Symbol> = param_names
                    .iter()
                    .map(|p| Symbol::from(*p))
                    .collect();
                let args: Vec<Expr> = param_names
                    .iter()
                    .map(|p| Expr::Var {
                        name: Symbol::from(*p),
                        span: Span::SYNTHETIC,
                    })
                    .collect();

                Defn {
                    name: Symbol::from(*method_name),
                    docstring: None,
                    params,
                    param_annotations: vec![None; param_names.len()],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from(*prim_name),
                            span: Span::SYNTHETIC,
                        }),
                        args,
                        span: Span::SYNTHETIC,
                    },
                    visibility: Visibility::Public,
                    span: Span::SYNTHETIC,
                }
            })
            .collect();

        let impl_ = TraitImpl {
            trait_name: TraitName::from(trait_name),
            target_type: TypeName::from(target_type),
            type_args: vec![],
            type_constraints: vec![],
            methods: method_defns,
            span: Span::SYNTHETIC,
        };

        // Route through the normal pipeline; discard returned Defn nodes.
        // The backend's primitive_for_trait_method() handles codegen.
        let _defns = self.register_trait_impl(&impl_)
            .unwrap_or_else(|e| {
                unreachable!(
                    "invariant: core impl {trait_name} for {target_type} registration failed: {e}"
                )
            });
    }
}

// --- Standalone helper functions for building trait method signatures ---

/// Build a method signature of shape `(Fn [a a] a)` — for Num arithmetic ops.
fn make_aa_a_sig(name: &str, param_names: &[&str]) -> TraitMethodSig {
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

/// Build a method signature of shape `(Fn [a a] Bool)` — for Eq/Ord ops.
///
/// If `has_default` is true, a placeholder `default_body` is set so that
/// `register_trait_impl()` generates the hard-coded default body.
fn make_aa_bool_sig(name: &str, param_names: &[&str], has_default: bool) -> TraitMethodSig {
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
        default_body: if has_default {
            Some(Sexp::Symbol("default".to_string(), Span::SYNTHETIC))
        } else {
            None
        },
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

    // spec: 07-traits §7.5 — operator symbols registered as trait method entries
    #[test]
    fn test_operator_names_registered_as_trait_methods() {
        let tc = TypeChecker::new();
        // Ring 2A: operators are now registered as trait method entries
        let ops = ["+", "-", "*", "/", "=", "!=", "<", ">", "<=", ">="];
        for name in ops {
            assert!(
                tc.symbol_table().get(name).is_some(),
                "operator {name} should be registered as a trait method"
            );
        }
    }

    // -----------------------------------------------------------------------
    // Decision 17 elimination: core traits via normal pipeline
    // -----------------------------------------------------------------------

    // spec: 07-traits §7.7 — core traits registered via register_trait_decl (check trait_registry.decls)
    #[test]
    fn test_core_traits_registered_via_trait_decl() {
        let tc = TypeChecker::new();
        let core_traits = ["Num", "Eq", "Ord", "Display"];
        for name in core_traits {
            assert!(
                tc.trait_registry.decls.contains_key(&TraitName::from(name)),
                "core trait {name} should be in trait_registry.decls"
            );
        }
    }

    // spec: 07-traits §7.7 — all 12 core impl entries registered in impl_registry
    #[test]
    fn test_all_12_core_impls_registered() {
        let tc = TypeChecker::new();
        let expected: Vec<(&str, &str)> = vec![
            // Num: Int, Float
            ("Num", "Int"), ("Num", "Float"),
            // Eq: Int, Float, Bool, String
            ("Eq", "Int"), ("Eq", "Float"), ("Eq", "Bool"), ("Eq", "String"),
            // Ord: Int, Float
            ("Ord", "Int"), ("Ord", "Float"),
            // Display: Int, Float, Bool, String
            ("Display", "Int"), ("Display", "Float"), ("Display", "Bool"), ("Display", "String"),
        ];
        for (trait_name, impl_type) in &expected {
            assert!(
                tc.impl_registry.has_impl(
                    &TraitName::from(*trait_name),
                    &TypeName::from(*impl_type),
                ),
                "impl {trait_name} for {impl_type} should be registered"
            );
        }
        // Count total entries
        let total: usize = tc.impl_registry.impls.values()
            .map(|inner| inner.len())
            .sum();
        assert_eq!(total, 12, "exactly 12 core impl entries expected");
    }

    // spec: 07-traits §7.7 — default methods (!=, >, <=, >=) resolve correctly
    #[test]
    fn test_default_methods_resolve_correctly() {
        let mut tc = TypeChecker::new();

        // != should resolve for Int (default via Eq)
        let neq_result = tc.try_resolve_trait_method(
            &Symbol::from("!="),
            &[Type::Int, Type::Int],
            Span::SYNTHETIC,
        );
        assert!(neq_result.is_some(), "!= should resolve for Int");

        // > should resolve for Int (default via Ord)
        let gt_result = tc.try_resolve_trait_method(
            &Symbol::from(">"),
            &[Type::Int, Type::Int],
            Span::SYNTHETIC,
        );
        assert!(gt_result.is_some(), "> should resolve for Int");

        // <= should resolve for Float (default via Ord)
        let le_result = tc.try_resolve_trait_method(
            &Symbol::from("<="),
            &[Type::Float, Type::Float],
            Span::SYNTHETIC,
        );
        assert!(le_result.is_some(), "<= should resolve for Float");

        // >= should resolve for Float (default via Ord)
        let ge_result = tc.try_resolve_trait_method(
            &Symbol::from(">="),
            &[Type::Float, Type::Float],
            Span::SYNTHETIC,
        );
        assert!(ge_result.is_some(), ">= should resolve for Float");
    }

    // spec: 07-traits §7.7 — bootstrap: impl bodies reference named primitives in scope
    #[test]
    fn test_bootstrap_impl_bodies_typecheck() {
        // This test verifies that register_trait_impl() succeeds for core impls,
        // which means the method bodies (e.g., `(add-i64 x y)`) type-check
        // against named primitives already registered by register_primitives().
        //
        // The fact that TypeChecker::new() does not panic proves this — but
        // we verify the impl exists and the trait method resolves correctly.
        let mut tc = TypeChecker::new();

        // Num.+ for Int should resolve (body was `(add-i64 x y)`)
        let plus_result = tc.try_resolve_trait_method(
            &Symbol::from("+"),
            &[Type::Int, Type::Int],
            Span::SYNTHETIC,
        );
        assert!(plus_result.is_some(), "Num.+ should resolve for Int");

        // Display.show for Bool should resolve (body was `(bool-to-string x)`)
        let show_result = tc.try_resolve_trait_method(
            &Symbol::from("show"),
            &[Type::Bool],
            Span::SYNTHETIC,
        );
        assert!(show_result.is_some(), "Display.show should resolve for Bool");

        // Eq.= for String should resolve (body was `(str-eq x y)`)
        let eq_result = tc.try_resolve_trait_method(
            &Symbol::from("="),
            &[Type::String, Type::String],
            Span::SYNTHETIC,
        );
        assert!(eq_result.is_some(), "Eq.= should resolve for String");
    }

    // spec: 07-traits §7.7 — Display.show registered as trait method
    #[test]
    fn test_show_registered_as_trait_method() {
        let tc = TypeChecker::new();
        assert!(
            tc.symbol_table().get("show").is_some(),
            "show should be registered as a trait method"
        );
        assert!(
            tc.trait_registry.method_to_trait.get(&Symbol::from("show"))
                == Some(&TraitName::from("Display")),
            "show should map to Display trait"
        );
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
}
