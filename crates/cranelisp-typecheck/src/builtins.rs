//! Register Ring 0-4 primitives, special forms, and synthetic modules.
//!
//! Ring 0: 20 monomorphic named primitives (add-i64, add-f64, eq-i64, ..., not, eq-bool).
//! Ring 1: 8 monomorphic string/conversion externs + 4 polymorphic Vec externs.
//! Ring 3: Synthetic `macros` module (Sexp, SList ADTs + sconcat extern) +
//!         `quote-sexp` extern in `primitives`.
//! Ring 4: IO ADT (Pure, Effect, Bind) + `bind` inline primitive in `primitives`.
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
//! 7. register_io_type()            — IO ADT (Pure, Effect, Bind) in `primitives`
//! 8. register_bind_primitive()     — bind inline primitive in `primitives`
//! 9. import_primitives_into_user()  — copy genuine primitives -> user

use std::collections::HashMap;

use cranelisp_types::{
    ring0_primitives, ring1_primitives, ring3_primitives, ConstructorDef, ConstructorInfo,
    DefKind, FQTypeName, FieldDef, FieldInfo, JitSymbol, ModuleEntry, ModuleFullPath,
    PrimitiveKind, Scheme, Span, Symbol, Type, TypeDefInfo, TypeExpr, TypeName, Visibility,
};

/// Helper: create FQTypeName in the "primitives" module.
fn primitives_fqtn(name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from(name))
}

/// Helper: create FQTypeName in the "macros" module.
fn macros_fqtn(name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("macros"), TypeName::from(name))
}

use crate::checker::{CheckState, TypeCheckEnv};
use crate::scheme::mono;

/// Register all builtins into the given modules map.
///
/// This is a free function — the caller owns the `DashMap` and `AtomicU32`.
/// Called once during session startup before constructing `TypeCheckEnv`.
///
/// Seeds the "user" and "primitives" modules with Ring 0-4 primitives,
/// special forms, and synthetic modules (macros, IO, Trace, TestResult).
///
/// Traits (Num, Eq, Ord, Display) are NOT registered here — they come from
/// prelude `.cl` files loaded through the normal module pipeline.
pub fn register_builtins(
    modules: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable>,
    next_id: &std::sync::atomic::AtomicU32,
) {
    let env = TypeCheckEnv::new(modules, next_id);
    let mut state = CheckState::new(ModuleFullPath::from("user"));

    // Ensure the `primitives` synthetic module exists.
    let primitives_path = ModuleFullPath::from("primitives");
    if !modules.contains_key(&primitives_path) {
        modules.insert(
            primitives_path.clone(),
            cranelisp_types::SymbolTable::new(primitives_path.clone()),
        );
    }

    env.register_primitives();
    env.register_ring1_primitives();
    env.register_vec_primitives();
    env.register_special_forms(&state);
    env.register_builtin_type_names();

    // Ring 3: Seed synthetic `macros` module with SList and Sexp ADTs + sconcat.
    env.register_macros_module(&mut state);

    // Ring 3: quote-sexp in `primitives` — must come after macros module
    env.register_ring3_primitives();

    // Ring 1: Option ADT in `primitives` (needed by parse-int return type).
    env.register_option_type(&mut state);

    // Ring 4: IO ADT and bind primitive in `primitives`.
    env.register_io_type(&mut state);
    env.register_bind_primitive();

    // Ring 4: Trace ADT (TraceCall) + field accessors in `primitives`.
    env.register_trace_type(&mut state);

    // Ring 4: TestResult root type + test special forms in `user`.
    env.register_test_infrastructure(&mut state);
}

impl TypeCheckEnv<'_> {
    /// (Kept for reference — registration order documented above in register_builtins)
    /// Copy non-named-primitive entries from the `primitives` module into `user`.
    ///
    /// Register Ring 0 primitives from the authoritative table.
    ///
    /// Each primitive gets a monomorphic scheme (`mono(prim.ty)`) — no type variables.
    /// The backend recognises these via `ResolvedCall::BuiltinFn` and emits inline
    /// Cranelift IR for the `cranelift_op` field.
    ///
    /// Docstrings are taken from spec appendix-a-builtins.md §A.3.
    fn register_primitives(&self) {
        let primitives_path = ModuleFullPath::from("primitives");
        let mut primitives_table = self
            .modules
            .get_mut(&primitives_path)
            .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));

        for prim in ring0_primitives() {
            let scheme = mono(prim.ty.clone());
            let docstring = builtin_docstring(prim.name.as_ref());

            primitives_table.insert(
                prim.name.clone(),
                ModuleEntry::Def {
                    scheme,
                    visibility: Visibility::Public,
                    docstring,
                    param_names: prim.param_names.clone(),
                    kind: Box::new(DefKind::Primitive {
                        primitive_kind: PrimitiveKind::Inline,
                        jit_name: None,
                    }),
                    callees: Vec::new(),
                    got_slot: None,
                    trait_origin: None,
                ast: None,
                },
            );
        }
    }

    /// Register Ring 1 extern primitives from the authoritative table.
    ///
    /// These are string and type conversion functions implemented as extern "C"
    /// functions. The backend calls them via JIT symbol references, not inline IR.
    ///
    /// Docstrings are taken from spec appendix-a-builtins.md §A.3.
    fn register_ring1_primitives(&self) {
        let primitives_path = ModuleFullPath::from("primitives");
        let mut primitives_table = self
            .modules
            .get_mut(&primitives_path)
            .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));

        for prim in ring1_primitives() {
            let scheme = mono(prim.ty.clone());
            let docstring = builtin_docstring(prim.name.as_ref());

            primitives_table.insert(
                prim.name.clone(),
                ModuleEntry::Def {
                    scheme,
                    visibility: Visibility::Public,
                    docstring,
                    param_names: prim.param_names.clone(),
                    kind: Box::new(DefKind::Primitive {
                        primitive_kind: PrimitiveKind::Extern,
                        jit_name: Some(JitSymbol::from(prim.name.as_ref())),
                    }),
                    callees: Vec::new(),
                    got_slot: None,
                    trait_origin: None,
                ast: None,
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
    fn register_vec_primitives(&self) {
        // Allocate a fresh type variable ID for the polymorphic parameter 'a'.
        // This ensures the scheme's Var(a) won't collide with any Var already
        // in use by the typechecker, preventing infinite recursion in `apply`
        // when `instantiate` maps Var(a) to a fresh var.
        let (_, a) = self.fresh_var_id();
        let vec_a = Type::ADT(primitives_fqtn("Vec"), vec![Type::Var(a)]);

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

        let primitives_path = ModuleFullPath::from("primitives");
        let mut primitives_table = self
            .modules
            .get_mut(&primitives_path)
            .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));

        for (name, param_names, scheme) in vec_prims {
            let docstring = builtin_docstring(name);
            primitives_table.insert(
                Symbol::from(name),
                ModuleEntry::Def {
                    scheme,
                    visibility: Visibility::Public,
                    docstring,
                    param_names,
                    kind: Box::new(DefKind::Primitive {
                        primitive_kind: PrimitiveKind::Extern,
                        jit_name: Some(JitSymbol::from(name)),
                    }),
                    callees: Vec::new(),
                    got_slot: None,
                    trait_origin: None,
                ast: None,
                },
            );
        }

        // Register Vec as a known type with 1 type parameter (no constructors).
        // This allows `split` to return `(Vec String)` without the typechecker
        // complaining about an unknown type.
        primitives_table.insert(
            Symbol::from("Vec"),
            ModuleEntry::TypeDef {
                info: TypeDefInfo {
                    name: primitives_fqtn("Vec"),
                    type_params: vec![Symbol::from("a")],
                    constructors: vec![],
                    docstring: None,
                },
                visibility: Visibility::Public,
                constructor_scheme: None,
                sexp: None,
            },
        );
    }

    /// Register special form entries for REPL introspection.
    fn register_special_forms(&self, state: &CheckState) {
        let special_forms = vec![
            ("if", "conditional: (if cond then else)"),
            ("let", "local binding: (let [x e] body)"),
            ("fn", "lambda: (fn [params] body)"),
            ("defn", "function definition: (defn name [params] body)"),
            ("deftype", "type definition: (deftype Name ctor1 ctor2 ...)"),
            ("match", "pattern matching: (match expr [pat body] ...)"),
            ("deftrait", "trait declaration: (deftrait (TraitName a) (method [a ...] ret) ...)"),
            ("impl", "trait implementation: (impl TraitName Type (method [params] body) ...)"),
            ("defmacro", "macro definition: (defmacro name [params] body)"),
        ];

        for (name, desc) in special_forms {
            self.current_symbol_table_mut(state).insert(
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
                    callees: Vec::new(),
                    got_slot: None,
                    trait_origin: None,
                ast: None,
                },
            );
        }
    }

    /// Register builtin type names in the root module (user at init).
    ///
    /// Primitive type names (Int, Bool, Float, String, Vec) are part of the
    /// root module — universally available for type annotations without import.
    /// Registered in `user` (the root module) so they get seeded into every
    /// new module via `ensure_module_exists`.
    fn register_builtin_type_names(&self) {
        let builtin_types = vec![
            ("Int", "builtin integer type"),
            ("Bool", "builtin boolean type"),
            ("Float", "builtin floating-point type"),
            ("String", "builtin string type"),
            ("Vec", "builtin vector type"),
        ];

        // Per spec §8.9.1: builtin types live in `primitives` and require
        // explicit import. They are NOT seeded into `user`.
        let primitives_path = ModuleFullPath::from("primitives");
        let mut primitives_table = self
            .modules
            .get_mut(&primitives_path)
            .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));

        for (name, desc) in builtin_types {
            primitives_table.insert(
                Symbol::from(name),
                ModuleEntry::TypeDef {
                    info: TypeDefInfo {
                        name: primitives_fqtn(name),
                        type_params: vec![],
                        constructors: vec![],
                        docstring: Some(desc.to_string()),
                    },
                    visibility: Visibility::Public,
                    constructor_scheme: None,
                    sexp: None,
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
    fn register_ring3_primitives(&self) {
        let primitives_path = ModuleFullPath::from("primitives");
        let mut primitives_table = self
            .modules
            .get_mut(&primitives_path)
            .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));

        for prim in ring3_primitives() {
            let scheme = mono(prim.ty.clone());
            let docstring = builtin_docstring(prim.name.as_ref());

            primitives_table.insert(
                prim.name.clone(),
                ModuleEntry::Def {
                    scheme,
                    visibility: Visibility::Public,
                    docstring,
                    param_names: prim.param_names.clone(),
                    kind: Box::new(DefKind::Primitive {
                        primitive_kind: PrimitiveKind::Extern,
                        jit_name: Some(JitSymbol::from(prim.name.as_ref())),
                    }),
                    callees: Vec::new(),
                    got_slot: None,
                    trait_origin: None,
                ast: None,
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
    fn register_macros_module(&self, state: &mut CheckState) {
        // Switch to the synthetic `macros` module.
        let saved_module = state.current_module.clone();
        let macros_path = ModuleFullPath::from("macros");
        self.ensure_module_exists(&macros_path);
        state.current_module = macros_path;

        self.register_slist_type(state);
        self.register_sexp_type(state);
        self.register_sconcat(state);

        // Restore the original module context.
        state.current_module = saved_module;
    }

    /// Register `sconcat` as an extern primitive in the `macros` module.
    ///
    /// Type: `(Fn [(SList Sexp) (SList Sexp)] (SList Sexp))`
    /// The quasiquote expander emits `macros/sconcat` calls to concatenate
    /// S-expression lists during macro expansion.
    fn register_sconcat(&self, state: &CheckState) {
        let slist_sexp = Type::ADT(
            macros_fqtn("SList"),
            vec![Type::ADT(macros_fqtn("Sexp"), vec![])],
        );
        let sconcat_type = Type::Fn(
            vec![slist_sexp.clone(), slist_sexp.clone()],
            Box::new(slist_sexp),
        );

        self.current_symbol_table_mut(state).insert(
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
                callees: Vec::new(),
                got_slot: None,
                trait_origin: None,
                ast: None,
            },
        );
    }

    /// Register `(deftype (SList a) SNil (SCons [:a shead :(SList a) stail]))`.
    fn register_slist_type(&self, state: &mut CheckState) {
        // Pre-seed SList in macros module's SymbolTable so SCons's self-referential
        // stail field resolves during build_constructor_infos.
        {
            let macros_path = ModuleFullPath::from("macros");
            let mut macros_table = self.modules.get_mut(&macros_path)
                .unwrap_or_else(|| unreachable!("invariant: macros module should exist"));
            macros_table.insert(
                Symbol::from("SList"),
                ModuleEntry::TypeDef {
                    info: TypeDefInfo {
                        name: macros_fqtn("SList"),
                        type_params: vec![Symbol::from("a")],
                        constructors: vec![],
                        docstring: None,
                    },
                    visibility: Visibility::Public,
                    constructor_scheme: None,
                    sexp: None,
                },
            );
        }

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

        self.register_type_def(state,
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
    fn register_sexp_type(&self, state: &mut CheckState) {
        // Pre-seed Sexp in macros module's SymbolTable so SexpList/SexpBracket's
        // :(SList Sexp) fields resolve during build_constructor_infos.
        {
            let macros_path = ModuleFullPath::from("macros");
            let mut macros_table = self.modules.get_mut(&macros_path)
                .unwrap_or_else(|| unreachable!("invariant: macros module should exist"));
            macros_table.insert(
                Symbol::from("Sexp"),
                ModuleEntry::TypeDef {
                    info: TypeDefInfo {
                        name: macros_fqtn("Sexp"),
                        type_params: vec![],
                        constructors: vec![],
                        docstring: None,
                    },
                    visibility: Visibility::Public,
                    constructor_scheme: None,
                    sexp: None,
                },
            );
        }

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

        self.register_type_def(state,
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

    /// Register the `Option` ADT in the `primitives` module.
    ///
    /// `(deftype (Option a) None (Some [:a val]))`
    ///
    /// This is needed for `parse-int` which returns `(Option Int)`.
    /// Constructors `None` and `Some` are registered in the primitives module
    /// and become available to user code via `(import [primitives [*]])`.
    fn register_option_type(&self, state: &mut CheckState) {
        let saved_module = state.current_module.clone();
        let primitives_path = ModuleFullPath::from("primitives");
        self.ensure_module_exists(&primitives_path);
        state.current_module = primitives_path;

        let option_ctors = vec![
            // None (tag=0): nullary
            ConstructorDef {
                name: Symbol::from("None"),
                docstring: Some("Absent value".to_string()),
                fields: vec![],
                span: Span::SYNTHETIC,
            },
            // Some (tag=1): field `val` of type `a`
            ConstructorDef {
                name: Symbol::from("Some"),
                docstring: Some("Present value".to_string()),
                fields: vec![FieldDef {
                    name: Symbol::from("val"),
                    type_expr: TypeExpr::TypeVar(Symbol::from("a")),
                }],
                span: Span::SYNTHETIC,
            },
        ];

        self.register_type_def(
            state,
            &TypeName::from("Option"),
            &Some("Optional value — None or (Some val)".to_string()),
            &[Symbol::from("a")],
            &option_ctors,
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap_or_else(|e| {
            unreachable!("invariant: Option type registration failed: {e}")
        });

        state.current_module = saved_module;
    }

    /// Register the IO ADT in the `primitives` module.
    ///
    /// IO is an ordinary ADT with three constructors:
    /// - `Pure` (tag=0): wraps a value — field `ioval` of type `a`
    /// - `Effect` (tag=1): wraps a thunk — field `thunk` typed as `a`
    /// - `Bind` (tag=2, internal): chains IO actions — fields `inner: (IO b)`,
    ///   `cont: (Fn [b] (IO a))`, where `b` is an existential type var
    ///
    /// Pure and Effect are registered through `register_type_def()`.
    /// Bind is added manually afterward as an internal constructor — it is
    /// NOT registered in the symbol table (users cannot construct or match on it).
    ///
    /// See `design/typecheck/io-types.md` §2-3 for the full design rationale.
    fn register_io_type(&self, state: &mut CheckState) {
        // Switch to the synthetic `primitives` module.
        let saved_module = state.current_module.clone();
        let primitives_path = ModuleFullPath::from("primitives");
        if !self.modules.contains_key(&primitives_path) {
            self.modules.insert(primitives_path.clone(), cranelisp_types::SymbolTable::new(primitives_path.clone()));
        }
        self.ensure_module_exists(&primitives_path);
        state.current_module = primitives_path;

        // Define Pure and Effect constructors via the normal registration path.
        let io_ctors = vec![
            // Pure (tag=0): field `ioval` of type `a`
            ConstructorDef {
                name: Symbol::from("Pure"),
                docstring: Some("Lift a value into IO".to_string()),
                fields: vec![FieldDef {
                    name: Symbol::from("ioval"),
                    type_expr: TypeExpr::TypeVar(Symbol::from("a")),
                }],
                span: Span::SYNTHETIC,
            },
            // Effect (tag=1): field `thunk` typed as `a` (see design doc §2 for why)
            ConstructorDef {
                name: Symbol::from("Effect"),
                docstring: Some("Deferred effectful computation".to_string()),
                fields: vec![FieldDef {
                    name: Symbol::from("thunk"),
                    type_expr: TypeExpr::TypeVar(Symbol::from("a")),
                }],
                span: Span::SYNTHETIC,
            },
        ];

        self.register_type_def(state,
            &TypeName::from("IO"),
            &Some("Deferred IO computation tree".to_string()),
            &[Symbol::from("a")],
            &io_ctors,
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap_or_else(|e| {
            unreachable!("invariant: IO type registration failed: {e}")
        });

        // Add Bind as an internal constructor (tag=2).
        self.add_internal_bind_constructor();

        // Restore the original module context.
        state.current_module = saved_module;
    }

    /// Add the internal Bind constructor to the IO TypeDefInfo.
    ///
    /// Bind has fields with types involving an existential type variable `b`
    /// that is independent of IO's type parameter `a`. HM inference cannot
    /// express existentials, so Bind bypasses the normal constructor registration.
    ///
    /// The Bind constructor appears in `TypeDefInfo.constructors` for REPL
    /// introspection (`/info IO` shows all three constructors) but is NOT
    /// resolvable as a name in the type environment.
    fn add_internal_bind_constructor(&self) {
        // Allocate fresh type vars for the existential types.
        let (_, a_id) = self.fresh_var_id();
        let (_, b_id) = self.fresh_var_id();

        // inner :: (IO b)
        let io_b = Type::ADT(primitives_fqtn("IO"), vec![Type::Var(b_id)]);
        // cont :: (Fn [b] (IO a))
        let io_a = Type::ADT(primitives_fqtn("IO"), vec![Type::Var(a_id)]);
        let cont_ty = Type::Fn(vec![Type::Var(b_id)], Box::new(io_a));

        let bind_ctor = ConstructorInfo {
            name: Symbol::from("Bind"),
            tag: 2,
            fields: vec![
                FieldInfo {
                    name: Symbol::from("inner"),
                    ty: io_b,
                },
                FieldInfo {
                    name: Symbol::from("cont"),
                    ty: cont_ty,
                },
            ],
            docstring: Some(
                "Chain IO actions (internal — constructed by bind primitive)".to_string(),
            ),
            internal: true,
        };

        // Append Bind to the IO TypeDefInfo in the primitives module's SymbolTable.
        let primitives_path = ModuleFullPath::from("primitives");
        let mut primitives_table = self.modules.get_mut(&primitives_path)
            .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));
        if let Some(ModuleEntry::TypeDef { info, .. }) = primitives_table.symbols.get_mut(&Symbol::from("IO")) {
            info.constructors.push(bind_ctor);
        } else {
            unreachable!("invariant: IO type should be registered before adding Bind");
        }

        // Do NOT register Bind in the symbol table — it is not user-constructable.
        // Do NOT register in constructor_to_type — Bind should not be resolvable by name.
    }

    /// Register `bind` as an inline primitive in the `primitives` module.
    ///
    /// Type: `forall a b. (Fn [(IO a) (Fn [a] (IO b))] (IO b))`
    ///
    /// `bind` is the IO sequencing primitive. At each call site, the backend
    /// emits inline Cranelift IR to allocate a Bind node: `[tag=2, io_ptr, cont_ptr]`.
    ///
    /// See `design/typecheck/io-types.md` §4 for the type scheme construction.
    fn register_bind_primitive(&self) {
        let primitives_path = ModuleFullPath::from("primitives");

        // Allocate fresh type vars for the polymorphic parameters.
        let (_, a_id) = self.fresh_var_id();
        let (_, b_id) = self.fresh_var_id();

        // Build the type: (Fn [(IO a) (Fn [a] (IO b))] (IO b))
        let io_a = Type::ADT(primitives_fqtn("IO"), vec![Type::Var(a_id)]);
        let io_b = Type::ADT(primitives_fqtn("IO"), vec![Type::Var(b_id)]);
        let cont_ty = Type::Fn(vec![Type::Var(a_id)], Box::new(io_b.clone()));
        let bind_ty = Type::Fn(vec![io_a, cont_ty], Box::new(io_b));

        let bind_scheme = Scheme {
            vars: vec![a_id, b_id],
            constraints: HashMap::new(),
            ty: bind_ty,
        };

        let mut primitives_table = self
            .modules
            .get_mut(&primitives_path)
            .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));

        primitives_table.insert(
            Symbol::from("bind"),
            ModuleEntry::Def {
                scheme: bind_scheme,
                visibility: Visibility::Public,
                docstring: Some(
                    "Chain IO actions: extract value from first IO, pass to continuation"
                        .to_string(),
                ),
                param_names: vec![Symbol::from("io"), Symbol::from("f")],
                kind: Box::new(DefKind::Primitive {
                    primitive_kind: PrimitiveKind::Inline,
                    jit_name: None,
                }),
                callees: Vec::new(),
                got_slot: None,
                trait_origin: None,
                ast: None,
            },
        );
    }

    /// Register the Trace ADT and field accessors in the `primitives` module.
    ///
    /// Trace is a monomorphic ADT (no type parameters) with a single constructor:
    ///
    /// ```clojure
    /// (deftype Trace
    ///   (TraceCall [:String name
    ///               :String params
    ///               :String result
    ///               :Int    children
    ///               :Int    nanos]))
    /// ```
    ///
    /// Per spec §3.2.4 and §4.12.4, Trace, TraceCall, and field accessors are
    /// NOT auto-imported into user scope. Users must explicitly import them:
    ///   `(import [primitives [Trace TraceCall name params result children nanos]])`
    ///
    /// Field accessors are registered as monomorphic Def entries:
    ///   name     :: (Fn [Trace] String)
    ///   params   :: (Fn [Trace] String)
    ///   result   :: (Fn [Trace] String)
    ///   children :: (Fn [Trace] Int)
    ///   nanos    :: (Fn [Trace] Int)
    fn register_trace_type(&self, state: &mut CheckState) {
        // Switch to the synthetic `primitives` module.
        let saved_module = state.current_module.clone();
        let primitives_path = ModuleFullPath::from("primitives");
        self.ensure_module_exists(&primitives_path);
        state.current_module = primitives_path.clone();

        // Define the TraceCall constructor via the normal registration path.
        let trace_ctors = vec![ConstructorDef {
            name: Symbol::from("TraceCall"),
            docstring: Some("Trace call tree node".to_string()),
            fields: vec![
                FieldDef {
                    name: Symbol::from("name"),
                    type_expr: TypeExpr::Named(TypeName::from("String")),
                },
                FieldDef {
                    name: Symbol::from("params"),
                    type_expr: TypeExpr::Applied(
                        TypeName::from("SList"),
                        vec![TypeExpr::Named(TypeName::from("String"))],
                    ),
                },
                FieldDef {
                    name: Symbol::from("result"),
                    type_expr: TypeExpr::Named(TypeName::from("String")),
                },
                FieldDef {
                    name: Symbol::from("children"),
                    type_expr: TypeExpr::Applied(
                        TypeName::from("SList"),
                        vec![TypeExpr::Named(TypeName::from("Trace"))],
                    ),
                },
                FieldDef {
                    name: Symbol::from("nanos"),
                    type_expr: TypeExpr::Named(TypeName::from("Int")),
                },
            ],
            span: Span::SYNTHETIC,
        }];

        self.register_type_def(state,
            &TypeName::from("Trace"),
            &Some("Recorded execution call tree from (trace expr)".to_string()),
            &[], // monomorphic — no type parameters
            &trace_ctors,
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap_or_else(|e| {
            unreachable!("invariant: Trace type registration failed: {e}")
        });

        // Register field accessor functions as monomorphic Def entries.
        // These allow destructuring via function application rather than match.
        let trace_type = Type::ADT(primitives_fqtn("Trace"), vec![]);

        let accessor_defs: Vec<(&str, &str, Type)> = vec![
            (
                "name",
                "Fully qualified function name from trace call",
                Type::String,
            ),
            (
                "params",
                "Formatted parameter values from trace call",
                Type::ADT(macros_fqtn("SList"), vec![Type::String]),
            ),
            (
                "result",
                "Formatted result value from trace call",
                Type::String,
            ),
            (
                "children",
                "Child calls in trace node",
                Type::ADT(
                    macros_fqtn("SList"),
                    vec![Type::ADT(primitives_fqtn("Trace"), vec![])],
                ),
            ),
            ("nanos", "Wall-clock nanoseconds for trace call", Type::Int),
        ];

        for (field_name, docstring, return_ty) in accessor_defs {
            let scheme = Scheme {
                vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![trace_type.clone()], Box::new(return_ty)),
            };

            self.current_symbol_table_mut(state).insert(
                Symbol::from(field_name),
                ModuleEntry::Def {
                    scheme,
                    visibility: Visibility::Public,
                    docstring: Some(docstring.to_string()),
                    param_names: vec![Symbol::from("t")],
                    kind: Box::new(DefKind::Primitive {
                        primitive_kind: PrimitiveKind::Extern,
                        jit_name: Some(JitSymbol::from(
                            format!("cranelisp_trace_{field_name}").as_str(),
                        )),
                    }),
                    callees: Vec::new(),
                    got_slot: None,
                    trait_origin: None,
                ast: None,
                },
            );
        }

        // Register `trace` as a module-scoped special form in `primitives`.
        // Unlike parser keywords (let, if, fn), `trace` has regular call syntax
        // and is resolved through the module system (arch Principle 10).
        self.current_symbol_table_mut(state).insert(
            Symbol::from("trace"),
            ModuleEntry::Def {
                scheme: Scheme {
                    vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(
                        vec![Type::Var(0)], // any expression type
                        Box::new(Type::ADT(primitives_fqtn("Trace"), vec![])),
                    ),
                },
                visibility: Visibility::Public,
                docstring: Some(
                    "Execution trace: (trace expr) — evaluates expr with call instrumentation, returns Trace ADT"
                        .to_string(),
                ),
                param_names: vec![Symbol::from("expr")],
                kind: Box::new(DefKind::SpecialForm {
                    description: "Execution trace: (trace expr) — evaluates expr with call instrumentation, returns Trace ADT".to_string(),
                }),
                callees: Vec::new(),
                got_slot: None,
                trait_origin: None,
                ast: None,
            },
        );

        // Restore the original module context.
        state.current_module = saved_module;
    }

    /// Register the TestResult type and test primitives in `primitives`.
    ///
    /// Per spec §8.9.1, builtin types live in `primitives` and require
    /// explicit import. TestResult, discover-tests, and run-test are NOT
    /// seeded into `user` — they must be imported explicitly.
    fn register_test_infrastructure(&self, state: &mut CheckState) {
        // Switch to the `primitives` module for registration.
        let saved_module = state.current_module.clone();
        self.ensure_module_exists(&ModuleFullPath::from("primitives"));
        state.current_module = ModuleFullPath::from("primitives");

        // TestResult type: TestPass, TestFail constructors.
        let test_result_ctors = vec![
            ConstructorDef {
                name: Symbol::from("TestPass"),
                docstring: Some("Test passed".to_string()),
                fields: vec![
                    FieldDef {
                        name: Symbol::from("name"),
                        type_expr: TypeExpr::Named(TypeName::from("String")),
                    },
                    FieldDef {
                        name: Symbol::from("nanos"),
                        type_expr: TypeExpr::Named(TypeName::from("Int")),
                    },
                ],
                span: Span::SYNTHETIC,
            },
            ConstructorDef {
                name: Symbol::from("TestFail"),
                docstring: Some("Test failed (no trace)".to_string()),
                fields: vec![
                    FieldDef {
                        name: Symbol::from("name"),
                        type_expr: TypeExpr::Named(TypeName::from("String")),
                    },
                    FieldDef {
                        name: Symbol::from("nanos"),
                        type_expr: TypeExpr::Named(TypeName::from("Int")),
                    },
                    FieldDef {
                        name: Symbol::from("reason"),
                        type_expr: TypeExpr::Named(TypeName::from("String")),
                    },
                ],
                span: Span::SYNTHETIC,
            },
        ];

        self.register_type_def(state,
            &TypeName::from("TestResult"),
            &Some("Test execution result".to_string()),
            &[], // monomorphic
            &test_result_ctors,
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap_or_else(|e| {
            unreachable!("invariant: TestResult type registration failed: {e}")
        });

        // Register discover-tests and run-test as special forms.
        let sexp_type = Type::ADT(macros_fqtn("Sexp"), vec![]);
        let slist_sexp = Type::ADT(macros_fqtn("SList"), vec![sexp_type.clone()]);
        let test_result_type = Type::ADT(primitives_fqtn("TestResult"), vec![]);
        let io_slist_sexp = Type::ADT(primitives_fqtn("IO"), vec![slist_sexp]);
        let io_test_result = Type::ADT(primitives_fqtn("IO"), vec![test_result_type]);

        self.current_symbol_table_mut(state).insert(
            Symbol::from("discover-tests"),
            ModuleEntry::Def {
                scheme: Scheme {
                    vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![Type::String], Box::new(io_slist_sexp)),
                },
                visibility: Visibility::Public,
                docstring: Some(
                    "Discover test-* functions: (discover-tests) or (discover-tests module)"
                        .to_string(),
                ),
                param_names: vec![Symbol::from("module")],
                kind: Box::new(DefKind::Primitive {
                    primitive_kind: PrimitiveKind::Extern,
                    jit_name: Some(JitSymbol::from("discover-tests")),
                }),
                callees: Vec::new(),
                got_slot: None,
                trait_origin: None,
                ast: None,
            },
        );

        self.current_symbol_table_mut(state).insert(
            Symbol::from("run-test"),
            ModuleEntry::Def {
                scheme: Scheme {
                    vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![sexp_type.clone()], Box::new(io_test_result.clone())),
                },
                visibility: Visibility::Public,
                docstring: Some(
                    "Run a single test without tracing: (run-test name)"
                        .to_string(),
                ),
                param_names: vec![Symbol::from("name")],
                kind: Box::new(DefKind::Primitive {
                    primitive_kind: PrimitiveKind::Extern,
                    jit_name: Some(JitSymbol::from("run-test")),
                }),
                callees: Vec::new(),
                got_slot: None,
                trait_origin: None,
                ast: None,
            },
        );

        // Restore the original module context.
        state.current_module = saved_module;
    }
}

/// Look up the spec-mandated docstring for a builtin primitive.
///
/// Docstrings are taken verbatim from the Description column in
/// `spec/appendix-a-builtins.md` §A.3. Section A.5 requires all
/// primitive functions to have docstrings available at runtime.
///
/// Returns `Some(docstring)` for known primitives, `None` otherwise.
fn builtin_docstring(name: &str) -> Option<String> {
    let doc = match name {
        // --- Integer arithmetic ---
        "add-i64" => "Add",
        "sub-i64" => "Subtract",
        "mul-i64" => "Multiply",
        "div-i64" => "Integer division",
        // --- Float arithmetic ---
        "add-f64" => "Add",
        "sub-f64" => "Subtract",
        "mul-f64" => "Multiply",
        "div-f64" => "Division",
        // --- Integer comparison ---
        "eq-i64" => "Equality",
        "lt-i64" => "Less than",
        "gt-i64" => "Greater than",
        "le-i64" => "Less than or equal",
        "ge-i64" => "Greater than or equal",
        // --- Float comparison ---
        "eq-f64" => "Equality",
        "lt-f64" => "Less than",
        "gt-f64" => "Greater than",
        "le-f64" => "Less than or equal",
        "ge-f64" => "Greater than or equal",
        // --- Boolean ---
        "not" => "Boolean negation",
        "eq-bool" => "Boolean equality",
        // --- Type conversion ---
        "int-to-string" => "Convert integer to decimal string",
        "float-to-string" => "Convert float to string",
        "bool-to-string" => "\"true\" or \"false\"",
        "string-identity" => "Identity for String (used by Display impl)",
        // --- String operations ---
        "str-concat" => "Concatenate two strings",
        "str-eq" => "String equality (byte-wise)",
        "str-len" => "String length in bytes",
        "parse-int" => "Parse decimal integer; None on failure",
        "substring" => "Extract substring from start (inclusive) to end (exclusive); clamps out-of-bounds indices",
        "char-at" => "Character at byte index as single-character string; empty string if out of bounds",
        "split" => "Split string by separator",
        "join" => "Join strings with separator",
        "replace" => "Replace all occurrences of from with to",
        "trim" => "Trim leading and trailing whitespace",
        "starts-with?" => "Test if string starts with prefix",
        "ends-with?" => "Test if string ends with suffix",
        "contains?" => "Test if string contains substring",
        "to-upper" => "Convert to uppercase",
        "to-lower" => "Convert to lowercase",
        // --- Macro support ---
        "quote-sexp" => "Convert a runtime Sexp value to constructor source code",
        // --- Vec operations ---
        "vec-get" => "Index (bounds-checked; panics on out-of-bounds)",
        "vec-set" => "Return new Vec with element at index replaced",
        "vec-push" => "Return new Vec with element appended",
        "vec-len" => "Number of elements",
        "vec-map" => "Map function over elements",
        "vec-reduce" => "Left fold over elements",
        _ => return None,
    };
    Some(doc.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::checker::TestFixture;
    use cranelisp_types::{ring0_primitives, ModuleEntry, Type};

    /// Helper: get the `primitives` module's symbol table from a TestFixture.
    fn primitives_table(tf: &TestFixture) -> dashmap::mapref::one::Ref<'_, ModuleFullPath, cranelisp_types::SymbolTable> {
        let path = ModuleFullPath::from("primitives");
        tf.modules
            .get(&path)
            .expect("primitives module should exist")
    }

    // spec: appendix-a-builtins §A.2 — all ring-0 primitives registered in primitives module
    #[test]
    fn test_primitives_registered() {
        let tf = TestFixture::new();
        let pt = primitives_table(&tf);
        // All 20 primitives should be in the primitives module
        for prim in ring0_primitives() {
            assert!(
                pt.get(prim.name.as_ref()).is_some(),
                "primitive {} should be in primitives module",
                prim.name
            );
        }
    }

    // spec: appendix-a-builtins §A.2 — add-i64 has monomorphic (Fn [Int Int] Int) scheme
    #[test]
    fn test_add_i64_scheme() {
        let tf = TestFixture::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = primitives_table(&tf).get("add-i64") {
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
        let tf = TestFixture::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = primitives_table(&tf).get("add-f64") {
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
        let tf = TestFixture::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = primitives_table(&tf).get("eq-i64") {
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
        let tf = TestFixture::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = primitives_table(&tf).get("not") {
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
        let tf = TestFixture::new();
        if let Some(ModuleEntry::Def { kind, .. }) = primitives_table(&tf).get("add-i64") {
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
        let tf = TestFixture::new();
        let forms = ["if", "let", "fn", "defn", "deftype", "match", "deftrait", "impl"];
        for name in forms {
            let table_guard = tf.symbol_table();
            let entry = table_guard.get(name);
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
        let tf = TestFixture::new();
        let pt = primitives_table(&tf);
        let vec_ops = ["vec-get", "vec-set", "vec-push", "vec-len"];
        for name in vec_ops {
            assert!(
                pt.get(name).is_some(),
                "Vec primitive {name} should be in primitives module"
            );
        }
    }

    // spec: 03-types §3.2.4 — vec-get is polymorphic (Fn [(Vec a) Int] a)
    #[test]
    fn test_vec_get_scheme_is_polymorphic() {
        let tf = TestFixture::new();
        if let Some(ModuleEntry::Def { scheme, kind, .. }) = primitives_table(&tf).get("vec-get") {
            assert_eq!(scheme.vars.len(), 1, "vec-get should have 1 quantified var");
            // Type: (Fn [(Vec a) Int] a)
            if let Type::Fn(params, ret) = &scheme.ty {
                assert_eq!(params.len(), 2);
                assert!(matches!(&params[0], Type::ADT(name, _) if name.name.as_ref() == "Vec"));
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
        let tf = TestFixture::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = primitives_table(&tf).get("vec-set") {
            assert_eq!(scheme.vars.len(), 1, "vec-set should have 1 quantified var");
            if let Type::Fn(params, ret) = &scheme.ty {
                assert_eq!(params.len(), 3, "vec-set takes (Vec a), Int, a");
                assert!(matches!(&params[0], Type::ADT(name, _) if name.name.as_ref() == "Vec"));
                assert_eq!(params[1], Type::Int);
                // ret is (Vec a)
                assert!(matches!(ret.as_ref(), Type::ADT(name, _) if name.name.as_ref() == "Vec"));
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
        let tf = TestFixture::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = primitives_table(&tf).get("vec-push") {
            assert_eq!(scheme.vars.len(), 1, "vec-push should have 1 quantified var");
            if let Type::Fn(params, ret) = &scheme.ty {
                assert_eq!(params.len(), 2, "vec-push takes (Vec a), a");
                assert!(matches!(ret.as_ref(), Type::ADT(name, _) if name.name.as_ref() == "Vec"));
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
        let tf = TestFixture::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = primitives_table(&tf).get("vec-len") {
            assert_eq!(scheme.vars.len(), 1, "vec-len should have 1 quantified var");
            if let Type::Fn(params, ret) = &scheme.ty {
                assert_eq!(params.len(), 1, "vec-len takes (Vec a)");
                assert!(matches!(&params[0], Type::ADT(name, _) if name.name.as_ref() == "Vec"));
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
        let tf = TestFixture::new();
        assert!(
            tf.env().lookup_trait_decl(&cranelisp_types::TraitName::from("Num")).is_none(),
            "no traits should be registered at startup (Decision 17 eliminated)"
        );
        assert!(
            !tf.env().has_impl(&cranelisp_types::TraitName::from("Num"), &cranelisp_types::TypeName::from("Int")),
            "no impls should be registered at startup"
        );
    }

    // spec: pipeline-orchestration §5 — operator symbols NOT in symbol table at startup
    #[test]
    fn test_no_operator_symbols_at_startup() {
        let tf = TestFixture::new();
        let ops = ["+", "-", "*", "/", "=", "!=", "<", ">", "<=", ">=", "show"];
        for name in ops {
            assert!(
                tf.symbol_table().get(name).is_none(),
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
        let tf = TestFixture::new();
        let macros_path = ModuleFullPath::from("macros");
        assert!(
            tf.modules.get(&macros_path).is_some(),
            "macros module should exist after TypeChecker initialization"
        );
    }

    // spec: 09-macros §9.1.1 — SList type registered in macros module
    #[test]
    fn test_slist_type_registered() {
        let tf = TestFixture::new();
        let info = tf.env().lookup_type_def(&TypeName::from("SList"));
        assert!(info.is_some(), "SList type should be registered");
        let info = info.unwrap();
        assert_eq!(info.type_params.len(), 1, "SList has 1 type parameter");
        assert_eq!(info.type_params[0].as_ref(), "a");
        assert_eq!(info.constructors.len(), 2, "SList has 2 constructors: SNil, SCons");
    }

    // spec: 09-macros §9.1.1 — SNil is nullary constructor (tag 0)
    #[test]
    fn test_snil_is_nullary() {
        let tf = TestFixture::new();
        let macros_path = ModuleFullPath::from("macros");
        let macros_table = tf.modules.get(&macros_path).unwrap();
        if let Some(ModuleEntry::Constructor { info, scheme, .. }) = macros_table.get("SNil") {
            assert_eq!(info.tag, 0, "SNil should be tag 0");
            assert!(info.fields.is_empty(), "SNil should have no fields");
            assert_eq!(scheme.vars.len(), 1, "SNil should have 1 quantified var (polymorphic)");
            // SNil :: forall [a]. (SList a)
            match &scheme.ty {
                Type::ADT(name, args) => {
                    assert_eq!(name.name.as_ref(), "SList");
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
        let tf = TestFixture::new();
        let macros_path = ModuleFullPath::from("macros");
        let macros_table = tf.modules.get(&macros_path).unwrap();
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
                            assert_eq!(name.name.as_ref(), "SList");
                            assert_eq!(args.len(), 1);
                            // SList's type arg should be the same var as the first param
                            assert_eq!(params[0], args[0]);
                        }
                        _ => panic!("second SCons param should be (SList a)"),
                    }
                    // Return: (SList a)
                    match ret.as_ref() {
                        Type::ADT(name, args) => {
                            assert_eq!(name.name.as_ref(), "SList");
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
        let tf = TestFixture::new();
        let info = tf.env().lookup_type_def(&TypeName::from("Sexp"));
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
        let tf = TestFixture::new();
        let macros_path = ModuleFullPath::from("macros");
        let macros_table = tf.modules.get(&macros_path).unwrap();
        if let Some(ModuleEntry::Constructor { scheme, .. }) = macros_table.get("SexpSym") {
            assert!(scheme.vars.is_empty(), "SexpSym should be monomorphic");
            assert_eq!(
                scheme.ty,
                Type::Fn(
                    vec![Type::String],
                    Box::new(Type::ADT(macros_fqtn("Sexp"), vec![]))
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
        let tf = TestFixture::new();
        let macros_path = ModuleFullPath::from("macros");
        let macros_table = tf.modules.get(&macros_path).unwrap();

        let sexp_type = Type::ADT(macros_fqtn("Sexp"), vec![]);
        let slist_sexp_type = Type::ADT(
            macros_fqtn("SList"),
            vec![Type::ADT(macros_fqtn("Sexp"), vec![])],
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
        let tf = TestFixture::new();
        // The TypeChecker's current module is "user" by default.
        // Qualified lookup: "macros/SexpSym" should resolve.
        let scheme = tf.lookup("macros/SexpSym");
        assert!(
            scheme.is_some(),
            "macros/SexpSym should be resolvable from user module"
        );
        let scheme = scheme.unwrap();
        assert_eq!(
            scheme.ty,
            Type::Fn(
                vec![Type::String],
                Box::new(Type::ADT(macros_fqtn("Sexp"), vec![]))
            ),
            "macros/SexpSym :: (Fn [String] Sexp)"
        );

        // Also check qualified access to SCons and SNil
        assert!(
            tf.lookup("macros/SCons").is_some(),
            "macros/SCons should be resolvable"
        );
        assert!(
            tf.lookup("macros/SNil").is_some(),
            "macros/SNil should be resolvable"
        );
    }

    // -----------------------------------------------------------------------
    // sconcat extern in macros module (P1, pipeline-orchestration §3)
    // -----------------------------------------------------------------------

    // spec: pipeline-orchestration §3 — sconcat registered as extern primitive in macros module
    #[test]
    fn test_sconcat_registered_in_macros() {
        let tf = TestFixture::new();
        let macros_path = ModuleFullPath::from("macros");
        let macros_table = tf.modules.get(&macros_path).unwrap();
        let entry = macros_table.get("sconcat");
        assert!(entry.is_some(), "sconcat should be in macros module");

        if let Some(ModuleEntry::Def { scheme, kind, .. }) = entry {
            // Type: (Fn [(SList Sexp) (SList Sexp)] (SList Sexp))
            let slist_sexp = Type::ADT(
                macros_fqtn("SList"),
                vec![Type::ADT(macros_fqtn("Sexp"), vec![])],
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
        let tf = TestFixture::new();
        let scheme = tf.lookup("macros/sconcat");
        assert!(
            scheme.is_some(),
            "macros/sconcat should be resolvable from user module"
        );
    }

    // spec: pipeline-orchestration §3 — sconcat NOT imported into user module
    #[test]
    fn test_sconcat_not_in_user() {
        let tf = TestFixture::new();
        assert!(
            tf.symbol_table().get("sconcat").is_none(),
            "sconcat should NOT be in user module (it's in macros, not primitives)"
        );
    }

    // -----------------------------------------------------------------------
    // quote-sexp extern in primitives module (P2, pipeline-orchestration §3)
    // -----------------------------------------------------------------------

    // spec: pipeline-orchestration §3 — quote-sexp registered as extern primitive
    #[test]
    fn test_quote_sexp_registered() {
        let tf = TestFixture::new();
        let prims = primitives_table(&tf);
        let entry = prims.get("quote-sexp");
        assert!(entry.is_some(), "quote-sexp should be in primitives module");

        if let Some(ModuleEntry::Def { scheme, kind, .. }) = entry {
            let sexp_type = Type::ADT(macros_fqtn("Sexp"), vec![]);
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
        let tf = TestFixture::new();
        let primitives_path = ModuleFullPath::from("primitives");
        let primitives_table = tf.modules.get(&primitives_path).unwrap();
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
        let tf = TestFixture::new();

        // Verify all expected modules exist
        assert!(tf.modules.get(&ModuleFullPath::from("user")).is_some());
        assert!(tf.modules.get(&ModuleFullPath::from("primitives")).is_some());
        assert!(tf.modules.get(&ModuleFullPath::from("macros")).is_some());

        // Verify quote-sexp has the correct type referencing Sexp (proves ordering)
        let sexp_type = Type::ADT(macros_fqtn("Sexp"), vec![]);
        if let Some(ModuleEntry::Def { scheme, .. }) = primitives_table(&tf).get("quote-sexp") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![sexp_type.clone()], Box::new(sexp_type)),
            );
        } else {
            panic!("quote-sexp should be registered after macros module");
        }
    }

    // -----------------------------------------------------------------------
    // IO ADT type registration (Ring 4, spec §10.1, design/typecheck/io-types.md)
    // -----------------------------------------------------------------------

    // spec: 10-io §10.1 — IO type registered in primitives module
    #[test]
    fn test_io_type_registered() {
        let tf = TestFixture::new();
        let info = tf.env().lookup_type_def(&TypeName::from("IO"));
        assert!(info.is_some(), "IO type should be registered");
        let info = info.unwrap();
        assert_eq!(info.type_params.len(), 1, "IO has 1 type parameter");
        assert_eq!(info.type_params[0].as_ref(), "a");
        assert_eq!(
            info.constructors.len(), 3,
            "IO has 3 constructors: Pure, Effect, Bind"
        );
        assert_eq!(
            info.docstring.as_deref(),
            Some("Deferred IO computation tree")
        );
    }

    // spec: 10-io §10.1 — Pure constructor: tag=0, field `ioval` of type `a`
    #[test]
    fn test_pure_constructor() {
        let tf = TestFixture::new();
        let primitives_path = ModuleFullPath::from("primitives");
        let primitives_table = tf.modules.get(&primitives_path).unwrap();

        if let Some(ModuleEntry::Constructor { info, scheme, .. }) =
            primitives_table.get("Pure")
        {
            assert_eq!(info.tag, 0, "Pure should be tag 0");
            assert_eq!(info.fields.len(), 1, "Pure has 1 field");
            assert_eq!(info.fields[0].name.as_ref(), "ioval");
            assert!(!info.internal, "Pure is not internal");
            assert_eq!(scheme.vars.len(), 1, "Pure should have 1 quantified var");
            // Pure :: forall [a]. (Fn [a] (IO a))
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 1);
                    assert!(matches!(params[0], Type::Var(_)), "param should be type var");
                    match ret.as_ref() {
                        Type::ADT(name, args) => {
                            assert_eq!(name.name.as_ref(), "IO");
                            assert_eq!(args.len(), 1);
                            assert_eq!(params[0], args[0], "param var should match IO's type arg");
                        }
                        _ => panic!("Pure return should be (IO a), got {:?}", ret),
                    }
                }
                _ => panic!("Pure should have Fn type, got {:?}", scheme.ty),
            }
        } else {
            panic!("Pure should be a Constructor entry in primitives module");
        }
    }

    // spec: 10-io §10.1 — Effect constructor: tag=1, field `thunk` of type `a`
    #[test]
    fn test_effect_constructor() {
        let tf = TestFixture::new();
        let primitives_path = ModuleFullPath::from("primitives");
        let primitives_table = tf.modules.get(&primitives_path).unwrap();

        if let Some(ModuleEntry::Constructor { info, scheme, .. }) =
            primitives_table.get("Effect")
        {
            assert_eq!(info.tag, 1, "Effect should be tag 1");
            assert_eq!(info.fields.len(), 1, "Effect has 1 field");
            assert_eq!(info.fields[0].name.as_ref(), "thunk");
            assert!(!info.internal, "Effect is not internal");
            assert_eq!(scheme.vars.len(), 1, "Effect should have 1 quantified var");
            // Effect :: forall [a]. (Fn [a] (IO a))
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 1);
                    match ret.as_ref() {
                        Type::ADT(name, args) => {
                            assert_eq!(name.name.as_ref(), "IO");
                            assert_eq!(args.len(), 1);
                            assert_eq!(params[0], args[0]);
                        }
                        _ => panic!("Effect return should be (IO a)"),
                    }
                }
                _ => panic!("Effect should have Fn type, got {:?}", scheme.ty),
            }
        } else {
            panic!("Effect should be a Constructor entry in primitives module");
        }
    }

    // spec: 10-io §10.1 — Bind constructor: tag=2, internal=true, not in symbol table
    #[test]
    fn test_bind_constructor_internal() {
        let tf = TestFixture::new();

        // Bind should be in TypeDefInfo but NOT in the symbol table.
        let info = tf.env().lookup_type_def(&TypeName::from("IO")).unwrap();
        let bind_ctor = &info.constructors[2];
        assert_eq!(bind_ctor.name.as_ref(), "Bind");
        assert_eq!(bind_ctor.tag, 2);
        assert!(bind_ctor.internal, "Bind must be internal");
        assert_eq!(bind_ctor.fields.len(), 2, "Bind has 2 fields: inner, cont");
        assert_eq!(bind_ctor.fields[0].name.as_ref(), "inner");
        assert_eq!(bind_ctor.fields[1].name.as_ref(), "cont");

        // inner :: (IO b)
        match &bind_ctor.fields[0].ty {
            Type::ADT(name, args) => {
                assert_eq!(name.name.as_ref(), "IO");
                assert_eq!(args.len(), 1);
                assert!(matches!(args[0], Type::Var(_)));
            }
            _ => panic!("Bind.inner should be (IO b), got {:?}", bind_ctor.fields[0].ty),
        }

        // cont :: (Fn [b] (IO a))
        match &bind_ctor.fields[1].ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1);
                assert!(matches!(params[0], Type::Var(_)));
                match ret.as_ref() {
                    Type::ADT(name, args) => {
                        assert_eq!(name.name.as_ref(), "IO");
                        assert_eq!(args.len(), 1);
                        assert!(matches!(args[0], Type::Var(_)));
                    }
                    _ => panic!("Bind.cont return should be (IO a)"),
                }
                // b in cont's param should match b in inner's IO type arg
                let inner_b = match &bind_ctor.fields[0].ty {
                    Type::ADT(_, args) => &args[0],
                    _ => panic!("already checked"),
                };
                assert_eq!(&params[0], inner_b, "b should be the same type var in inner and cont");
            }
            _ => panic!("Bind.cont should be Fn type, got {:?}", bind_ctor.fields[1].ty),
        }

        // Bind should NOT be in the primitives symbol table.
        let primitives_path = ModuleFullPath::from("primitives");
        let primitives_table = tf.modules.get(&primitives_path).unwrap();
        assert!(
            primitives_table.get("Bind").is_none(),
            "Bind should NOT be in symbol table (it is internal)"
        );

        // Bind should NOT be in constructor_to_type.
        assert!(
            tf.env().lookup_constructor_type("Bind").is_none(),
            "Bind should NOT be in constructor_to_type"
        );
    }

    // spec: 10-io §10.1 — Pure and Effect registered as constructors in primitives module
    #[test]
    fn test_io_constructors_in_primitives_module() {
        let tf = TestFixture::new();
        let primitives_path = ModuleFullPath::from("primitives");
        let primitives_table = tf.modules.get(&primitives_path).unwrap();

        assert!(
            primitives_table.get("Pure").is_some(),
            "Pure should be in primitives module"
        );
        assert!(
            primitives_table.get("Effect").is_some(),
            "Effect should be in primitives module"
        );

        // IO type itself should be registered
        assert!(
            primitives_table.get("IO").is_some(),
            "IO type should be in primitives module"
        );
    }

    // spec: 10-io §10.1 — IO constructors in primitives module
    #[test]
    fn test_io_constructors_in_primitives() {
        let tf = TestFixture::new();
        let prims_path = ModuleFullPath::from("primitives");
        let prims_table = tf.modules.get(&prims_path).unwrap();
        assert!(
            prims_table.get("Pure").is_some(),
            "Pure should be in primitives module"
        );
        assert!(
            prims_table.get("Effect").is_some(),
            "Effect should be in primitives module"
        );
        // NOT in user module without import
        assert!(
            tf.symbol_table().get("Pure").is_none(),
            "Pure should NOT be bare in user"
        );
    }

    // -----------------------------------------------------------------------
    // bind primitive (Ring 4, design/typecheck/io-types.md §4)
    // -----------------------------------------------------------------------

    // spec: 10-io §10.2 — bind registered as inline primitive in primitives module
    #[test]
    fn test_bind_primitive_registered() {
        let tf = TestFixture::new();
        let prims_path = ModuleFullPath::from("primitives");
        let table_guard = tf.modules.get(&prims_path).unwrap();
        let entry = table_guard.get("bind");
        assert!(entry.is_some(), "bind should be in primitives symbol table");

        if let Some(ModuleEntry::Def { scheme, kind, docstring, .. }) = entry {
            // bind :: forall [a, b]. (Fn [(IO a) (Fn [a] (IO b))] (IO b))
            assert_eq!(scheme.vars.len(), 2, "bind should have 2 quantified vars (a, b)");

            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 2, "bind takes 2 params");

                    // First param: (IO a)
                    match &params[0] {
                        Type::ADT(name, args) => {
                            assert_eq!(name.name.as_ref(), "IO");
                            assert_eq!(args.len(), 1);
                            assert!(matches!(args[0], Type::Var(_)));
                        }
                        _ => panic!("bind param[0] should be (IO a), got {:?}", params[0]),
                    }

                    // Second param: (Fn [a] (IO b))
                    match &params[1] {
                        Type::Fn(cont_params, cont_ret) => {
                            assert_eq!(cont_params.len(), 1);
                            assert!(matches!(cont_params[0], Type::Var(_)));
                            match cont_ret.as_ref() {
                                Type::ADT(name, args) => {
                                    assert_eq!(name.name.as_ref(), "IO");
                                    assert_eq!(args.len(), 1);
                                    assert!(matches!(args[0], Type::Var(_)));
                                }
                                _ => panic!("bind cont return should be (IO b)"),
                            }
                            // a in param[0] should match a in cont param
                            let io_a_var = match &params[0] {
                                Type::ADT(_, args) => &args[0],
                                _ => unreachable!(),
                            };
                            assert_eq!(
                                &cont_params[0], io_a_var,
                                "a in (IO a) should match a in (Fn [a] ...)"
                            );
                        }
                        _ => panic!("bind param[1] should be Fn type"),
                    }

                    // Return: (IO b)
                    match ret.as_ref() {
                        Type::ADT(name, args) => {
                            assert_eq!(name.name.as_ref(), "IO");
                            assert_eq!(args.len(), 1);
                            // b in return should match b in cont's return
                            let cont_ret_b = match &params[1] {
                                Type::Fn(_, cr) => match cr.as_ref() {
                                    Type::ADT(_, args) => &args[0],
                                    _ => unreachable!(),
                                },
                                _ => unreachable!(),
                            };
                            assert_eq!(
                                &args[0], cont_ret_b,
                                "b in return (IO b) should match b in cont return"
                            );
                        }
                        _ => panic!("bind return should be (IO b)"),
                    }
                }
                _ => panic!("bind should have Fn type, got {:?}", scheme.ty),
            }

            assert!(
                matches!(
                    kind.as_ref(),
                    DefKind::Primitive { primitive_kind: PrimitiveKind::Inline, .. }
                ),
                "bind should be Primitive::Inline"
            );

            assert!(docstring.is_some(), "bind should have a docstring");
        } else {
            panic!("bind should be a Def entry");
        }
    }

    // spec: 10-io §10.2 — bind also in primitives module
    #[test]
    fn test_bind_in_primitives_module() {
        let tf = TestFixture::new();
        let primitives_path = ModuleFullPath::from("primitives");
        let primitives_table = tf.modules.get(&primitives_path).unwrap();
        assert!(
            primitives_table.get("bind").is_some(),
            "bind should be in primitives module"
        );
    }

    // -----------------------------------------------------------------------
    // Builtin docstrings (spec appendix-a-builtins §A.5)
    // -----------------------------------------------------------------------

    // spec: appendix-a-builtins §A.5 — all Ring 0 primitives have docstrings
    #[test]
    fn test_ring0_primitives_have_docstrings() {
        let tf = TestFixture::new();
        let pt = primitives_table(&tf);
        for prim in ring0_primitives() {
            if let Some(ModuleEntry::Def { docstring, .. }) =
                pt.get(prim.name.as_ref())
            {
                assert!(
                    docstring.is_some(),
                    "Ring 0 primitive {} should have a docstring",
                    prim.name
                );
            } else {
                panic!("Ring 0 primitive {} not found", prim.name);
            }
        }
    }

    // spec: appendix-a-builtins §A.5 — all Ring 1 primitives have docstrings
    #[test]
    fn test_ring1_primitives_have_docstrings() {
        let tf = TestFixture::new();
        let pt = primitives_table(&tf);
        for prim in ring1_primitives() {
            if let Some(ModuleEntry::Def { docstring, .. }) =
                pt.get(prim.name.as_ref())
            {
                assert!(
                    docstring.is_some(),
                    "Ring 1 primitive {} should have a docstring",
                    prim.name
                );
            } else {
                panic!("Ring 1 primitive {} not found", prim.name);
            }
        }
    }

    // spec: appendix-a-builtins §A.5 — Vec primitives have docstrings
    #[test]
    fn test_vec_primitives_have_docstrings() {
        let tf = TestFixture::new();
        let pt = primitives_table(&tf);
        for name in &["vec-get", "vec-set", "vec-push", "vec-len"] {
            if let Some(ModuleEntry::Def { docstring, .. }) = pt.get(*name) {
                assert!(
                    docstring.is_some(),
                    "Vec primitive {name} should have a docstring"
                );
            } else {
                panic!("Vec primitive {name} not found");
            }
        }
    }

    // spec: appendix-a-builtins §A.5 — specific docstring text matches spec
    #[test]
    fn test_docstring_text_matches_spec() {
        let tf = TestFixture::new();
        let pt = primitives_table(&tf);

        let check = |name: &str, expected: &str| {
            if let Some(ModuleEntry::Def { docstring, .. }) = pt.get(name) {
                assert_eq!(
                    docstring.as_deref(),
                    Some(expected),
                    "{name} docstring mismatch"
                );
            } else {
                panic!("{name} not found");
            }
        };

        check("not", "Boolean negation");
        check("add-i64", "Add");
        check("div-i64", "Integer division");
        check("str-concat", "Concatenate two strings");
        check("parse-int", "Parse decimal integer; None on failure");
        check("vec-get", "Index (bounds-checked; panics on out-of-bounds)");
        check("vec-set", "Return new Vec with element at index replaced");
        check("vec-push", "Return new Vec with element appended");
        check("vec-len", "Number of elements");
        check("quote-sexp", "Convert a runtime Sexp value to constructor source code");
    }

    // -----------------------------------------------------------------------
    // Trace ADT (Ring 4, spec §3.2.4 / §4.12)
    // -----------------------------------------------------------------------

    // spec: 03-types §3.2.4 — Trace type registered as monomorphic ADT
    #[test]
    fn test_trace_type_registered() {
        let tf = TestFixture::new();
        let info = tf.env().lookup_type_def(&TypeName::from("Trace"));
        assert!(info.is_some(), "Trace type should be registered");
        let info = info.unwrap();
        assert!(info.type_params.is_empty(), "Trace has no type parameters (monomorphic)");
        assert_eq!(info.constructors.len(), 1, "Trace has 1 constructor: TraceCall");
        assert_eq!(
            info.docstring.as_deref(),
            Some("Recorded execution call tree from (trace expr)")
        );
    }

    // spec: 03-types §3.2.4 — TraceCall constructor with 5 fields
    #[test]
    fn test_trace_call_constructor() {
        let tf = TestFixture::new();
        let primitives_path = ModuleFullPath::from("primitives");
        let primitives_table = tf.modules.get(&primitives_path).unwrap();

        if let Some(ModuleEntry::Constructor { info, scheme, .. }) =
            primitives_table.get("TraceCall")
        {
            assert_eq!(info.tag, 0, "TraceCall should be tag 0");
            assert_eq!(info.fields.len(), 5, "TraceCall has 5 fields");
            assert_eq!(info.fields[0].name.as_ref(), "name");
            assert_eq!(info.fields[1].name.as_ref(), "params");
            assert_eq!(info.fields[2].name.as_ref(), "result");
            assert_eq!(info.fields[3].name.as_ref(), "children");
            assert_eq!(info.fields[4].name.as_ref(), "nanos");

            // Field types: String, (SList String), String, (SList Trace), Int
            let slist_string = Type::ADT(macros_fqtn("SList"), vec![Type::String]);
            let slist_trace = Type::ADT(
                macros_fqtn("SList"),
                vec![Type::ADT(primitives_fqtn("Trace"), vec![])],
            );
            assert_eq!(info.fields[0].ty, Type::String);
            assert_eq!(info.fields[1].ty, slist_string); // params: SList of String
            assert_eq!(info.fields[2].ty, Type::String);
            assert_eq!(info.fields[3].ty, slist_trace); // children: SList of Trace
            assert_eq!(info.fields[4].ty, Type::Int);

            // Monomorphic scheme: no quantified vars
            assert!(scheme.vars.is_empty(), "TraceCall scheme should be monomorphic");
            // TraceCall :: (Fn [String (SList String) String (SList Trace) Int] Trace)
            let slist_string = Type::ADT(macros_fqtn("SList"), vec![Type::String]);
            let slist_trace = Type::ADT(
                macros_fqtn("SList"),
                vec![Type::ADT(primitives_fqtn("Trace"), vec![])],
            );
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 5);
                    assert_eq!(params[0], Type::String);
                    assert_eq!(params[1], slist_string);
                    assert_eq!(params[2], Type::String);
                    assert_eq!(params[3], slist_trace);
                    assert_eq!(params[4], Type::Int);
                    match ret.as_ref() {
                        Type::ADT(name, args) => {
                            assert_eq!(name.name.as_ref(), "Trace");
                            assert!(args.is_empty());
                        }
                        _ => panic!("TraceCall return should be Trace, got {:?}", ret),
                    }
                }
                _ => panic!("TraceCall should have Fn type, got {:?}", scheme.ty),
            }
        } else {
            panic!("TraceCall should be a Constructor entry in primitives module");
        }
    }

    // spec: 03-types §3.2.4 — Trace names in primitives module
    #[test]
    fn test_trace_in_primitives_module() {
        let tf = TestFixture::new();
        let primitives_path = ModuleFullPath::from("primitives");
        let primitives_table = tf.modules.get(&primitives_path).unwrap();

        assert!(primitives_table.get("Trace").is_some(), "Trace type in primitives");
        assert!(primitives_table.get("TraceCall").is_some(), "TraceCall constructor in primitives");
        // Field accessors
        assert!(primitives_table.get("name").is_some(), "name accessor in primitives");
        assert!(primitives_table.get("params").is_some(), "params accessor in primitives");
        assert!(primitives_table.get("result").is_some(), "result accessor in primitives");
        assert!(primitives_table.get("children").is_some(), "children accessor in primitives");
        assert!(primitives_table.get("nanos").is_some(), "nanos accessor in primitives");
    }

    // spec: 03-types §3.2.4 — Trace names NOT auto-imported into user module
    #[test]
    fn test_trace_not_auto_imported() {
        let tf = TestFixture::new();
        let user_table = tf.symbol_table();

        assert!(user_table.get("Trace").is_none(), "Trace must NOT be auto-imported");
        assert!(user_table.get("TraceCall").is_none(), "TraceCall must NOT be auto-imported");
        assert!(user_table.get("name").is_none(), "name accessor must NOT be auto-imported");
        assert!(user_table.get("params").is_none(), "params accessor must NOT be auto-imported");
        assert!(user_table.get("result").is_none(), "result accessor must NOT be auto-imported");
        assert!(user_table.get("children").is_none(), "children accessor must NOT be auto-imported");
        assert!(user_table.get("nanos").is_none(), "nanos accessor must NOT be auto-imported");
    }

    // spec: 03-types §3.2.4 — Trace field accessor types
    #[test]
    fn test_trace_field_accessors() {
        let tf = TestFixture::new();
        let primitives_path = ModuleFullPath::from("primitives");
        let primitives_table = tf.modules.get(&primitives_path).unwrap();
        let trace_type = Type::ADT(primitives_fqtn("Trace"), vec![]);

        let check_accessor = |name: &str, expected_ret: &Type| {
            if let Some(ModuleEntry::Def { scheme, .. }) = primitives_table.get(name) {
                assert!(scheme.vars.is_empty(), "{name} should be monomorphic");
                match &scheme.ty {
                    Type::Fn(params, ret) => {
                        assert_eq!(params.len(), 1, "{name} takes 1 param");
                        assert_eq!(&params[0], &trace_type, "{name} param should be Trace");
                        assert_eq!(ret.as_ref(), expected_ret, "{name} return type mismatch");
                    }
                    _ => panic!("{name} should have Fn type"),
                }
            } else {
                panic!("{name} should be a Def entry in primitives");
            }
        };

        let slist_string = Type::ADT(macros_fqtn("SList"), vec![Type::String]);
        let slist_trace = Type::ADT(
            macros_fqtn("SList"),
            vec![Type::ADT(primitives_fqtn("Trace"), vec![])],
        );
        check_accessor("name", &Type::String);
        check_accessor("params", &slist_string);
        check_accessor("result", &Type::String);
        check_accessor("children", &slist_trace);
        check_accessor("nanos", &Type::Int);
    }
}
