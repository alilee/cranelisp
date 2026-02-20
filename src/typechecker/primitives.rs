use crate::ast::Visibility;
use crate::module::CompiledModule;
use crate::names::{JitSymbol, ModuleFullPath, Symbol};
use crate::types::*;

use super::{PrimitiveKind, SymbolMeta, TypeChecker};

impl TypeChecker {
    /// Register a builtin under a synthetic module (qualified-only, no bare name).
    fn register_builtin(&mut self, module: &str, name: &str, scheme: Scheme, meta: SymbolMeta) {
        let mod_path = ModuleFullPath::from(module);
        let cm = self
            .modules
            .entry(mod_path.clone())
            .or_insert_with(|| CompiledModule::new(mod_path));
        cm.insert_def(
            Symbol::from(name),
            scheme,
            Visibility::Public,
            Some(meta),
        );
    }

    /// Register a builtin with an explicit JIT symbol name.
    fn register_builtin_with_jit_name(
        &mut self,
        module: &str,
        name: &str,
        scheme: Scheme,
        meta: SymbolMeta,
        jit_name: &str,
    ) {
        self.register_builtin(module, name, scheme, meta);
        let mod_path = ModuleFullPath::from(module);
        if let Some(cm) = self.modules.get_mut(&mod_path) {
            cm.set_jit_name(name, JitSymbol::from(jit_name));
        }
    }

    /// Register inline and extern primitives in the type environment.
    /// Inline primitives (add-i64, etc.) compile to inline Cranelift IR.
    /// Extern primitives (int-to-string, etc.) compile to Rust FFI calls.
    /// Also populates operator_methods set for early resolution.
    pub(crate) fn register_primitives(&mut self) {
        self.module_names
            .insert(crate::names::ModuleFullPath::from("primitives"));

        // Inline primitives: (Int, Int) -> Int
        for (name, doc) in &[
            ("add-i64", "Add two integers"),
            ("sub-i64", "Subtract two integers"),
            ("mul-i64", "Multiply two integers"),
            ("div-i64", "Integer division"),
        ] {
            self.register_builtin(
                "primitives",
                name,
                Scheme::mono(Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int))),
                SymbolMeta::Primitive {
                    kind: PrimitiveKind::Inline,
                    docstring: doc.to_string(),
                    param_names: vec!["a".into(), "b".into()],
                },
            );
        }

        // Inline primitives: (Int, Int) -> Bool
        for (name, doc) in &[
            ("eq-i64", "Test integer equality"),
            ("lt-i64", "Test integer less-than"),
            ("gt-i64", "Test integer greater-than"),
            ("le-i64", "Test integer less-than-or-equal"),
            ("ge-i64", "Test integer greater-than-or-equal"),
        ] {
            self.register_builtin(
                "primitives",
                name,
                Scheme::mono(Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool))),
                SymbolMeta::Primitive {
                    kind: PrimitiveKind::Inline,
                    docstring: doc.to_string(),
                    param_names: vec!["a".into(), "b".into()],
                },
            );
        }

        // Inline primitives: (Float, Float) -> Float
        for (name, doc) in &[
            ("add-f64", "Add two floats"),
            ("sub-f64", "Subtract two floats"),
            ("mul-f64", "Multiply two floats"),
            ("div-f64", "Float division"),
        ] {
            self.register_builtin(
                "primitives",
                name,
                Scheme::mono(Type::Fn(
                    vec![Type::Float, Type::Float],
                    Box::new(Type::Float),
                )),
                SymbolMeta::Primitive {
                    kind: PrimitiveKind::Inline,
                    docstring: doc.to_string(),
                    param_names: vec!["a".into(), "b".into()],
                },
            );
        }

        // Inline primitives: (Float, Float) -> Bool
        for (name, doc) in &[
            ("eq-f64", "Test float equality"),
            ("lt-f64", "Test float less-than"),
            ("gt-f64", "Test float greater-than"),
            ("le-f64", "Test float less-than-or-equal"),
            ("ge-f64", "Test float greater-than-or-equal"),
        ] {
            self.register_builtin(
                "primitives",
                name,
                Scheme::mono(Type::Fn(
                    vec![Type::Float, Type::Float],
                    Box::new(Type::Bool),
                )),
                SymbolMeta::Primitive {
                    kind: PrimitiveKind::Inline,
                    docstring: doc.to_string(),
                    param_names: vec!["a".into(), "b".into()],
                },
            );
        }

        // Extern primitives — JIT name matches user name for all extern primitives
        self.register_builtin_with_jit_name(
            "primitives",
            "int-to-string",
            Scheme::mono(Type::Fn(vec![Type::Int], Box::new(Type::String))),
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Extern,
                docstring: "Convert integer to string".into(),
                param_names: vec!["i".into()],
            },
            "int-to-string",
        );

        self.register_builtin_with_jit_name(
            "primitives",
            "bool-to-string",
            Scheme::mono(Type::Fn(vec![Type::Bool], Box::new(Type::String))),
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Extern,
                docstring: "Convert boolean to string".into(),
                param_names: vec!["b".into()],
            },
            "bool-to-string",
        );

        self.register_builtin_with_jit_name(
            "primitives",
            "string-identity",
            Scheme::mono(Type::Fn(vec![Type::String], Box::new(Type::String))),
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Extern,
                docstring: "Return string unchanged".into(),
                param_names: vec!["s".into()],
            },
            "string-identity",
        );

        self.register_builtin_with_jit_name(
            "primitives",
            "float-to-string",
            Scheme::mono(Type::Fn(vec![Type::Float], Box::new(Type::String))),
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Extern,
                docstring: "Convert float to string".into(),
                param_names: vec!["f".into()],
            },
            "float-to-string",
        );

        self.register_builtin_with_jit_name(
            "primitives",
            "quote-sexp",
            Scheme::mono(Type::Fn(
                vec![Type::ADT("Sexp".to_string(), vec![])],
                Box::new(Type::ADT("Sexp".to_string(), vec![])),
            )),
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Extern,
                docstring: "Convert Sexp value to constructor source code".into(),
                param_names: vec!["s".into()],
            },
            "quote-sexp",
        );

        self.register_builtin_with_jit_name(
            "primitives",
            "str-concat",
            Scheme::mono(Type::Fn(
                vec![Type::String, Type::String],
                Box::new(Type::String),
            )),
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Extern,
                docstring: "Concatenate two strings".into(),
                param_names: vec!["a".into(), "b".into()],
            },
            "str-concat",
        );

        self.register_builtin_with_jit_name(
            "primitives",
            "parse-int",
            Scheme::mono(Type::Fn(
                vec![Type::String],
                Box::new(Type::ADT("Option".to_string(), vec![Type::Int])),
            )),
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Extern,
                docstring: "Parse string as integer, returns None on failure".into(),
                param_names: vec!["s".into()],
            },
            "parse-int",
        );

        // Vec operations — polymorphic (quantified over element type var)
        self.register_vec_primitives();
    }

    fn register_vec_primitives(&mut self) {
        // vec-get :: forall a. (Vec a, Int) -> a
        let a1 = self.fresh_var();
        let vec_a1 = Type::ADT("Vec".to_string(), vec![a1.clone()]);
        let vec_get_ty = Type::Fn(vec![vec_a1, Type::Int], Box::new(a1.clone()));
        let a1_id = match &a1 {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        self.register_builtin_with_jit_name(
            "primitives",
            "vec-get",
            Scheme {
                vars: vec![a1_id],
                constraints: std::collections::HashMap::new(),
                ty: vec_get_ty,
            },
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Extern,
                docstring: "Return element at index".into(),
                param_names: vec!["v".into(), "i".into()],
            },
            "vec-get",
        );

        // vec-set :: forall a. (Vec a, Int, a) -> (Vec a)
        let a2 = self.fresh_var();
        let vec_a2 = Type::ADT("Vec".to_string(), vec![a2.clone()]);
        let vec_set_ty = Type::Fn(
            vec![vec_a2.clone(), Type::Int, a2.clone()],
            Box::new(vec_a2),
        );
        let a2_id = match &a2 {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        self.register_builtin_with_jit_name(
            "primitives",
            "vec-set",
            Scheme {
                vars: vec![a2_id],
                constraints: std::collections::HashMap::new(),
                ty: vec_set_ty,
            },
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Extern,
                docstring: "Return new vec with element at index replaced".into(),
                param_names: vec!["v".into(), "i".into(), "val".into()],
            },
            "vec-set",
        );

        // vec-push :: forall a. (Vec a, a) -> (Vec a)
        let a3 = self.fresh_var();
        let vec_a3 = Type::ADT("Vec".to_string(), vec![a3.clone()]);
        let vec_push_ty = Type::Fn(vec![vec_a3.clone(), a3.clone()], Box::new(vec_a3));
        let a3_id = match &a3 {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        self.register_builtin_with_jit_name(
            "primitives",
            "vec-push",
            Scheme {
                vars: vec![a3_id],
                constraints: std::collections::HashMap::new(),
                ty: vec_push_ty,
            },
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Extern,
                docstring: "Return new vec with element appended".into(),
                param_names: vec!["v".into(), "val".into()],
            },
            "vec-push",
        );

        // vec-len :: forall a. (Vec a) -> Int
        let a4 = self.fresh_var();
        let a4_id = match &a4 {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        let vec_a4 = Type::ADT("Vec".to_string(), vec![a4]);
        let vec_len_ty = Type::Fn(vec![vec_a4], Box::new(Type::Int));
        self.register_builtin_with_jit_name(
            "primitives",
            "vec-len",
            Scheme {
                vars: vec![a4_id],
                constraints: std::collections::HashMap::new(),
                ty: vec_len_ty,
            },
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Extern,
                docstring: "Return number of elements in vec".into(),
                param_names: vec!["v".into()],
            },
            "vec-len",
        );

        // vec-map :: forall a b. ((fn [a] b), (Vec a)) -> (Vec b)
        let a5 = self.fresh_var();
        let b5 = self.fresh_var();
        let a5_id = match &a5 {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        let b5_id = match &b5 {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        let vec_a5 = Type::ADT("Vec".to_string(), vec![a5.clone()]);
        let vec_b5 = Type::ADT("Vec".to_string(), vec![b5.clone()]);
        let mapper = Type::Fn(vec![a5], Box::new(b5));
        let vec_map_ty = Type::Fn(vec![mapper, vec_a5], Box::new(vec_b5));
        self.register_builtin_with_jit_name(
            "primitives",
            "vec-map",
            Scheme {
                vars: vec![a5_id, b5_id],
                constraints: std::collections::HashMap::new(),
                ty: vec_map_ty,
            },
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Extern,
                docstring: "Apply function to each element, return new vec".into(),
                param_names: vec!["f".into(), "v".into()],
            },
            "vec-map",
        );

        // vec-reduce :: forall a b. ((fn [b a] b), b, (Vec a)) -> b
        let a6 = self.fresh_var();
        let b6 = self.fresh_var();
        let a6_id = match &a6 {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        let b6_id = match &b6 {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        let vec_a6 = Type::ADT("Vec".to_string(), vec![a6.clone()]);
        let reducer = Type::Fn(vec![b6.clone(), a6], Box::new(b6.clone()));
        let vec_reduce_ty = Type::Fn(vec![reducer, b6.clone(), vec_a6], Box::new(b6));
        self.register_builtin_with_jit_name(
            "primitives",
            "vec-reduce",
            Scheme {
                vars: vec![a6_id, b6_id],
                constraints: std::collections::HashMap::new(),
                ty: vec_reduce_ty,
            },
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Extern,
                docstring: "Reduce vec to single value with function and initial accumulator"
                    .into(),
                param_names: vec!["f".into(), "init".into(), "v".into()],
            },
            "vec-reduce",
        );
    }

    /// Register builtin functions and special forms in the type environment.
    pub fn init_builtins(&mut self) {
        self.register_primitives();
        self.register_special_forms();
        self.register_builtin_types();
        self.register_macro_types();
        self.register_io_type();
    }

    /// Register macro-system types (SList, Sexp) in the synthetic `macros` module.
    /// These are immutable language types needed by the macro system.
    /// SList is polymorphic (ready for future HKT trait impls).
    fn register_macro_types(&mut self) {
        use crate::ast::*;

        let saved_module = self.current_module_path.clone();
        self.current_module_path = ModuleFullPath::from("macros");

        self.module_names
            .insert(ModuleFullPath::from("macros"));

        // Register SList first (Sexp references it)
        let slist_def = TopLevel::TypeDef {
            name: "SList".to_string(),
            docstring: Some("List type for macro sexp manipulation".to_string()),
            type_params: vec!["a".to_string()],
            constructors: vec![
                ConstructorDef {
                    name: "SNil".to_string(),
                    docstring: Some("Empty SList".to_string()),
                    fields: vec![],
                    span: (0, 0),
                },
                ConstructorDef {
                    name: "SCons".to_string(),
                    docstring: Some("SList node with head and tail".to_string()),
                    fields: vec![
                        FieldDef {
                            name: "shead".to_string(),
                            type_expr: TypeExpr::TypeVar("a".to_string()),
                        },
                        FieldDef {
                            name: "stail".to_string(),
                            type_expr: TypeExpr::Applied(
                                "SList".to_string(),
                                vec![TypeExpr::TypeVar("a".to_string())],
                            ),
                        },
                    ],
                    span: (0, 0),
                },
            ],
            visibility: Visibility::Public,
            span: (0, 0),
        };
        self.register_type_def(&slist_def);

        // Register Sexp (references SList)
        let sexp_def = TopLevel::TypeDef {
            name: "Sexp".to_string(),
            docstring: Some("S-expression for macro manipulation".to_string()),
            type_params: vec![],
            constructors: vec![
                ConstructorDef {
                    name: "SexpSym".to_string(),
                    docstring: Some("A symbol".to_string()),
                    fields: vec![FieldDef {
                        name: "sname".to_string(),
                        type_expr: TypeExpr::Named("String".to_string()),
                    }],
                    span: (0, 0),
                },
                ConstructorDef {
                    name: "SexpInt".to_string(),
                    docstring: Some("An integer literal".to_string()),
                    fields: vec![FieldDef {
                        name: "sval".to_string(),
                        type_expr: TypeExpr::Named("Int".to_string()),
                    }],
                    span: (0, 0),
                },
                ConstructorDef {
                    name: "SexpFloat".to_string(),
                    docstring: Some("A float literal".to_string()),
                    fields: vec![FieldDef {
                        name: "sval".to_string(),
                        type_expr: TypeExpr::Named("Float".to_string()),
                    }],
                    span: (0, 0),
                },
                ConstructorDef {
                    name: "SexpBool".to_string(),
                    docstring: Some("A boolean literal".to_string()),
                    fields: vec![FieldDef {
                        name: "sval".to_string(),
                        type_expr: TypeExpr::Named("Bool".to_string()),
                    }],
                    span: (0, 0),
                },
                ConstructorDef {
                    name: "SexpStr".to_string(),
                    docstring: Some("A string literal".to_string()),
                    fields: vec![FieldDef {
                        name: "sval".to_string(),
                        type_expr: TypeExpr::Named("String".to_string()),
                    }],
                    span: (0, 0),
                },
                ConstructorDef {
                    name: "SexpList".to_string(),
                    docstring: Some("A parenthesized list".to_string()),
                    fields: vec![FieldDef {
                        name: "sitems".to_string(),
                        type_expr: TypeExpr::Applied(
                            "SList".to_string(),
                            vec![TypeExpr::Named("Sexp".to_string())],
                        ),
                    }],
                    span: (0, 0),
                },
                ConstructorDef {
                    name: "SexpBracket".to_string(),
                    docstring: Some("A bracketed list".to_string()),
                    fields: vec![FieldDef {
                        name: "sitems".to_string(),
                        type_expr: TypeExpr::Applied(
                            "SList".to_string(),
                            vec![TypeExpr::Named("Sexp".to_string())],
                        ),
                    }],
                    span: (0, 0),
                },
            ],
            visibility: Visibility::Public,
            span: (0, 0),
        };
        self.register_type_def(&sexp_def);

        self.current_module_path = saved_module;
    }

    /// Register IO type as a compiler-seeded ADT in the `primitives` module.
    /// IO is a single-constructor ADT: `(deftype (IO a) (IOVal [:a ioval]))`.
    /// Field name `ioval` (not `val`) to avoid collision with user types.
    fn register_io_type(&mut self) {
        use crate::ast::*;

        let saved_module = self.current_module_path.clone();
        self.current_module_path = ModuleFullPath::from("primitives");

        let io_def = TopLevel::TypeDef {
            name: "IO".to_string(),
            docstring: Some("Monadic IO wrapper".to_string()),
            type_params: vec!["a".to_string()],
            constructors: vec![ConstructorDef {
                name: "IOVal".to_string(),
                docstring: Some("Wraps an IO result value".to_string()),
                fields: vec![FieldDef {
                    name: "ioval".to_string(),
                    type_expr: TypeExpr::TypeVar("a".to_string()),
                }],
                span: (0, 0),
            }],
            visibility: Visibility::Public,
            span: (0, 0),
        };
        self.register_type_def(&io_def);

        self.current_module_path = saved_module;
    }

    /// Register all special forms with descriptions and docstrings.
    /// The Rust type system enforces that every special form has both fields.
    fn register_special_forms(&mut self) {
        let forms: &[(&str, &str, &str)] = &[
            ("if", "if :: special form: (Fn [Bool a a] a)", "Conditional branch: evaluates then-branch if condition is true, else-branch otherwise"),
            ("let", "let :: special form: (let [name val ...] body) — bind local variables", "Bind local variables in body scope"),
            ("fn", "fn :: special form: (fn [params...] body) — create anonymous function", "Create anonymous function (lambda)"),
            ("defmacro", "defmacro :: special form: (defmacro name [params...] body) — define compile-time macro", "Define a macro that transforms S-expressions at compile time"),
            ("defn", "defn :: top-level form: (defn name [params...] body)", "Define a named function"),
            ("deftrait", "deftrait :: top-level form: (deftrait Name (method [Self ...] ReturnType) ...)", "Declare a trait with method signatures"),
            ("impl", "impl :: top-level form: (impl TraitName Type (method [params...] body) ...)", "Implement a trait for a type"),
            ("deftype", "deftype :: top-level form: (deftype Name [fields...]) or (deftype Name Ctor1 (Ctor2 [fields...]) ...)", "Define an algebraic data type"),
            ("match", "match :: special form: (match expr [pattern body ...]) — pattern match on ADTs", "Pattern match on algebraic data types"),
            ("mod", "mod :: module form: (mod name) — declare a module dependency", "Declare a dependency on another module"),
            ("import", "import :: module form: (import [module [names...]]) — import names from a module", "Import names from a module into the current scope"),
            ("export", "export :: module form: (export [module [names...]]) — re-export names from a module", "Re-export names from a dependency for downstream consumers"),
            ("platform", "platform :: module form: (platform name) or (platform name \"path\")", "Load a platform DLL and create a platform.<name> module. Use (import [platform.<name> [*]]) to bring functions into scope."),
        ];

        let root_path = ModuleFullPath::root();
        let root_cm = self
            .modules
            .entry(root_path.clone())
            .or_insert_with(|| CompiledModule::new(root_path));

        for (name, description, docstring) in forms {
            let meta = SymbolMeta::SpecialForm {
                description: description.to_string(),
                docstring: docstring.to_string(),
            };

            // Dual-write into CompiledModule (root module for special forms).
            // Special forms don't have a meaningful scheme; use Int as placeholder.
            root_cm.insert_def(
                Symbol::from(*name),
                Scheme::mono(Type::Int),
                Visibility::Public,
                Some(meta),
            );
        }
    }

    /// Register builtin type names (Int, Bool, String, Float, Vec) in the primitives
    /// module so they flow through imports like other symbols.
    fn register_builtin_types(&mut self) {
        let mod_path = ModuleFullPath::from("primitives");
        let cm = self
            .modules
            .entry(mod_path.clone())
            .or_insert_with(|| CompiledModule::new(mod_path));
        for name in &["Int", "Bool", "String", "Float", "Vec"] {
            // Placeholder Def entry — describe_symbol handles these via impls_for_type()
            cm.insert_def(
                Symbol::from(*name),
                Scheme::mono(Type::Int),
                Visibility::Public,
                None,
            );
        }
        // No separate register_module_name needed — insert_def above already writes
        // to CompiledModule, which is the sole source of truth for public_names().
    }

    /// Install bare names for all synthetic modules (primitives, macros, platform.*).
    /// Used by `check_program` (no-module path) and test helpers.
    /// Creates Import entries in the current module's CompiledModule
    /// so module-walk resolution can find them.
    pub fn install_synthetic_bare_names(&mut self) {
        // Install primitives
        let names = self.get_module_public_names("primitives");
        let imports: Vec<(String, String)> = names
            .into_iter()
            .map(|n| (n, "primitives".to_string()))
            .collect();
        self.install_imported_names(&imports);

        // Install macros (SList, Sexp, constructors)
        let names = self.get_module_public_names("macros");
        let imports: Vec<(String, String)> = names
            .into_iter()
            .map(|n| (n, "macros".to_string()))
            .collect();
        self.install_imported_names(&imports);

        // Install any dynamically registered platform modules (platform.stdio, etc.)
        let platform_modules: Vec<String> = self
            .module_names
            .iter()
            .filter(|m| m.0.starts_with("platform."))
            .map(|m| m.0.clone())
            .collect();
        for module in platform_modules {
            let names = self.get_module_public_names(&module);
            let imports: Vec<(String, String)> =
                names.into_iter().map(|n| (n, module.clone())).collect();
            self.install_imported_names(&imports);
        }
    }

    /// Install macros module bare names (SList, Sexp, constructors, accessors)
    /// into the current module scope. Used by REPL so compile_macro can resolve
    /// Sexp type annotations without exposing all primitives.
    pub fn install_macros_bare_names(&mut self) {
        let names = self.get_module_public_names("macros");
        let imports: Vec<(String, String)> = names
            .into_iter()
            .map(|n| (n, "macros".to_string()))
            .collect();
        self.install_imported_names(&imports);
    }

    /// Install bare names for a specific platform module into the current module scope.
    /// Use after loading a platform DLL to make its functions available without import.
    pub fn install_platform_bare_names(&mut self, platform_name: &str) {
        let module = format!("platform.{}", platform_name);
        let names = self.get_module_public_names(&module);
        let imports: Vec<(String, String)> = names
            .into_iter()
            .map(|n| (n, module.clone()))
            .collect();
        self.install_imported_names(&imports);
    }

    /// Register platform functions from owned descriptors into a scoped module.
    /// Creates `platform.<scope>` module with entries for each function.
    pub fn register_platform(
        &mut self,
        scope: &str,
        descriptors: &[crate::platform::OwnedPlatformFnDescriptor],
    ) -> Result<(), crate::error::CranelispError> {
        let module_name = format!("platform.{}", scope);
        let module_path = ModuleFullPath::from(module_name.as_str());

        self.module_names.insert(module_path.clone());
        let cm = self
            .modules
            .entry(module_path)
            .or_insert_with(|| CompiledModule::new(ModuleFullPath::from(module_name.as_str())));

        for desc in descriptors {
            // Parse the type signature from its S-expression string
            let ty = parse_type_sig(&desc.type_sig).map_err(|msg| {
                crate::error::CranelispError::TypeError {
                    message: format!(
                        "invalid type signature for platform fn '{}': {}",
                        desc.name, msg
                    ),
                    span: (0, 0),
                }
            })?;

            // Validate: return type must be wrapped in IO (platform boundary rule)
            validate_io_return(&desc.name, &ty)?;

            let scheme = Scheme::mono(ty);
            let meta = SymbolMeta::Primitive {
                kind: PrimitiveKind::Platform,
                docstring: desc.docstring.clone(),
                param_names: desc.param_names.clone(),
            };

            cm.insert_def(
                Symbol::from(desc.name.as_str()),
                scheme,
                Visibility::Public,
                Some(meta),
            );
            cm.set_jit_name(
                &desc.name,
                crate::names::JitSymbol::from(desc.jit_name.as_str()),
            );
        }

        Ok(())
    }
}

/// Parse a type signature S-expression string into a Type.
/// Handles: Int, Bool, String, Float, (IO T), (Fn [params] ret), (Name args...).
fn parse_type_sig(sig: &str) -> Result<Type, String> {
    let sexp = crate::sexp::parse_sexp(sig).map_err(|e| format!("parse error: {}", e))?;
    sexp_to_type(&sexp)
}

/// Convert a Sexp into a Type for type signature parsing.
fn sexp_to_type(sexp: &crate::sexp::Sexp) -> Result<Type, String> {
    use crate::sexp::Sexp;

    match sexp {
        Sexp::Symbol(name, _) => match name.as_str() {
            "Int" => Ok(Type::Int),
            "Bool" => Ok(Type::Bool),
            "String" => Ok(Type::String),
            "Float" => Ok(Type::Float),
            _ => {
                // Could be a type variable or ADT name
                if name.chars().next().is_some_and(|c| c.is_uppercase()) {
                    Ok(Type::ADT(name.clone(), vec![]))
                } else {
                    Err(format!("unsupported type name in platform signature: {}", name))
                }
            }
        },
        Sexp::List(children, _) => {
            if children.is_empty() {
                return Err("empty type expression".to_string());
            }
            if let Sexp::Symbol(head, _) = &children[0] {
                match head.as_str() {
                    "Fn" => {
                        if children.len() != 3 {
                            return Err("Fn requires [param types] and return type".to_string());
                        }
                        let params = match &children[1] {
                            Sexp::Bracket(items, _) => items
                                .iter()
                                .map(sexp_to_type)
                                .collect::<Result<Vec<_>, _>>()?,
                            _ => {
                                return Err("Fn param list must be in brackets".to_string());
                            }
                        };
                        let ret = sexp_to_type(&children[2])?;
                        Ok(Type::Fn(params, Box::new(ret)))
                    }
                    _ => {
                        // Applied type: (Name arg1 arg2 ...)
                        let name = head.clone();
                        let args = children[1..]
                            .iter()
                            .map(sexp_to_type)
                            .collect::<Result<Vec<_>, _>>()?;
                        Ok(Type::ADT(name, args))
                    }
                }
            } else {
                Err("type expression list must start with a symbol".to_string())
            }
        }
        _ => Err(format!("invalid type expression: {:?}", sexp)),
    }
}

/// Validate that a platform function's type has an IO return type.
fn validate_io_return(
    name: &str,
    ty: &Type,
) -> Result<(), crate::error::CranelispError> {
    let ret = match ty {
        Type::Fn(_, ret) => ret.as_ref(),
        _ => {
            return Err(crate::error::CranelispError::TypeError {
                message: format!(
                    "platform function '{}' must have a function type, got: {}",
                    name, ty
                ),
                span: (0, 0),
            });
        }
    };
    match ret {
        Type::ADT(name, _) if name == "IO" => Ok(()),
        _ => Err(crate::error::CranelispError::TypeError {
            message: format!(
                "platform function '{}' must return IO type, got: {}",
                name, ret
            ),
            span: (0, 0),
        }),
    }
}

#[cfg(test)]
mod platform_tests {
    use super::*;
    use crate::platform::OwnedPlatformFnDescriptor;

    #[test]
    fn parse_type_sig_fn_string_to_io_int() {
        let ty = parse_type_sig("(Fn [String] (IO Int))").unwrap();
        assert_eq!(
            ty,
            Type::Fn(
                vec![Type::String],
                Box::new(Type::ADT("IO".to_string(), vec![Type::Int]))
            )
        );
    }

    #[test]
    fn parse_type_sig_fn_no_params_io_string() {
        let ty = parse_type_sig("(Fn [] (IO String))").unwrap();
        assert_eq!(
            ty,
            Type::Fn(
                vec![],
                Box::new(Type::ADT("IO".to_string(), vec![Type::String]))
            )
        );
    }

    #[test]
    fn parse_type_sig_bare_int() {
        let ty = parse_type_sig("Int").unwrap();
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn parse_type_sig_applied_option_int() {
        let ty = parse_type_sig("(Option Int)").unwrap();
        assert_eq!(ty, Type::ADT("Option".to_string(), vec![Type::Int]));
    }

    #[test]
    fn validate_io_return_ok() {
        let ty = Type::Fn(
            vec![Type::String],
            Box::new(Type::ADT("IO".to_string(), vec![Type::Int])),
        );
        assert!(validate_io_return("print", &ty).is_ok());
    }

    #[test]
    fn validate_io_return_missing_io() {
        let ty = Type::Fn(vec![Type::String], Box::new(Type::Int));
        assert!(validate_io_return("bad", &ty).is_err());
    }

    #[test]
    fn validate_io_return_not_fn() {
        let ty = Type::Int;
        assert!(validate_io_return("bad", &ty).is_err());
    }

    #[test]
    fn register_platform_creates_module_with_entries() {
        let mut tc = crate::typechecker::TypeChecker::new();
        let descriptors = vec![
            OwnedPlatformFnDescriptor {
                name: "print".to_string(),
                jit_name: "cranelisp_print".to_string(),
                ptr: std::ptr::null(),
                param_count: 1,
                type_sig: "(Fn [String] (IO Int))".to_string(),
                docstring: "Print a string".to_string(),
                param_names: vec!["s".to_string()],
            },
            OwnedPlatformFnDescriptor {
                name: "read-line".to_string(),
                jit_name: "cranelisp_read_line".to_string(),
                ptr: std::ptr::null(),
                param_count: 0,
                type_sig: "(Fn [] (IO String))".to_string(),
                docstring: "Read a line".to_string(),
                param_names: vec![],
            },
        ];
        tc.register_platform("test", &descriptors).unwrap();

        // Check module was created
        let mod_path = ModuleFullPath::from("platform.test");
        assert!(tc.modules.contains_key(&mod_path));

        // Check entries exist
        let cm = tc.modules.get(&mod_path).unwrap();
        assert!(cm.get("print").is_some());
        assert!(cm.get("read-line").is_some());
    }

    #[test]
    fn register_platform_rejects_non_io_return() {
        let mut tc = crate::typechecker::TypeChecker::new();
        let descriptors = vec![OwnedPlatformFnDescriptor {
            name: "bad-fn".to_string(),
            jit_name: "cranelisp_bad".to_string(),
            ptr: std::ptr::null(),
            param_count: 1,
            type_sig: "(Fn [Int] Int)".to_string(),
            docstring: "Bad function".to_string(),
            param_names: vec!["x".to_string()],
        }];
        let result = tc.register_platform("test", &descriptors);
        assert!(result.is_err());
    }
}
