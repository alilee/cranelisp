//! TEST-ONLY synthetic-module + primitive seeders for the typecheck unit suite.
//!
//! Production session-init no longer assembles primitives or synthetic modules
//! here. Per `facades/typecheck.md` §"Builtin registration — removed from
//! typecheck", synthetic-module assembly (seeding the `primitives`/`macros`
//! modules and the `Option`/`IO`/`Trace`/`TestResult` ADTs) is content
//! construction, NOT type-checking — it left typecheck's bounded context. The
//! production mount is reconstructed by `int` at session init (FIXME 0242);
//! the prior `register_builtins` body is recoverable from git history.
//!
//! What remains in this file is `#[cfg(test)]` test-support: the typecheck
//! crate's own unit tests need plausible primitive-shaped Defs and synthetic
//! ADTs to exercise inference / trait dispatch / ADT / monomorphisation flows
//! WITHOUT depending on any other workspace crate (typecheck imports only
//! `cranelisp-types` — facade §"Consumed surface"). These seeders are the
//! FIXME 0239 "test-oracle" surface; see that FIXME for the relocation plan.
//!
//! The surface is a composable Tier-3 fixture builder (`FixtureBuilder`,
//! `#[cfg(test)]`). A test declares exactly the starting position it needs by
//! composing OPT-IN content presets (`FixtureContent`) instead of forcing the
//! all-on world. The named presets — each a slice carved out of the prior
//! monolith — are:
//! - `with_special_forms` — special-form metadata at root `""`.
//! - `with_builtin_type_names` — Int/Bool/Float/String/Vec in `primitives`.
//! - `with_macros_sexp` — synthetic `macros` module (Sexp/SList ADTs + sconcat).
//! - `with_io` — the `IO` ADT (Pure/Effect/Bind) + `bind` primitive.
//! - `with_primitives` — the Ring 0/1/3 primitive `Def`s
//!   (arithmetic/comparison/bool/string/vec/quote-sexp) whose schemes match the
//!   spec contract (Appendix A.2/A.3/A.5).
//!
//! `FixtureBuilder::full()` composes all presets in bootstrap-valid order —
//! the world the prior `seed_synthetic_modules` + `seed_test_primitives` pair
//! produced; `TestFixture::new()` delegates to it. The per-preset CONTENT
//! (schemes, ADT shapes) is typecheck-owned and stays here; entries are built
//! through `cranelisp_types::ModuleEntry::def` (Tier 1) — no raw struct
//! literals.
//!
//! Traits (Num, Eq, Ord, Display) and their impls are ordinary Cranelisp
//! defined in prelude `.cl` files, NOT seeded here. Tests that need operators
//! define traits inline (see `register_num_trait_inline` in the program tests).

#[cfg(test)]
use std::collections::HashMap;

#[cfg(test)]
use cranelisp_types::{
    ConstructorDef, DefKind, FQTypeName, FieldDef,
    ModuleEntry, ModuleFullPath, Scheme, Span, Symbol, Type, TypeDefInfo, TypeExpr,
    TypeName, Visibility,
};
#[cfg(test)]
use cranelisp_types::TypeId;

/// Helper: create FQTypeName in the "primitives" module.
#[cfg(test)]
fn primitives_fqtn(name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from(name))
}

/// Helper: create FQTypeName in the "macros" module.
#[cfg(test)]
fn macros_fqtn(name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("macros"), TypeName::from(name))
}

#[cfg(test)]
use crate::checker::{CheckState, TypeCheckEnv};
#[cfg(test)]
use crate::scheme::mono;

/// TEST-ONLY: Tier-3 composable content presets for the typecheck unit suite.
///
/// Each variant is a NAMED slice carved out of the prior all-or-nothing
/// synthetic world. A test composes exactly the starting position it needs via
/// [`FixtureContent`] / [`FixtureBuilder`] instead of forcing the entire world.
///
/// The CONTENT each preset seeds (schemes per spec Appendix A.2/A.3/A.5, ADT
/// shapes per spec §9.1 / §10) is typecheck-specific and spec-mandated — it
/// stays here. The generic per-table assembly machinery lives in
/// `cranelisp_types::test_support` (Tier 2); the Tier-1 `ModuleEntry::def`
/// builder constructs the entries.
///
/// Ordering matters at compose time (bootstrap dependencies):
/// - `BuiltinTypeNames` must precede `MacrosSexp` (Sexp/SList fields reference
///   `primitives/Int` etc.) and `Primitives` (`Option`/`Vec` schemes).
/// - `MacrosSexp` must precede `Primitives` (`quote-sexp` references
///   `macros/Sexp`).
/// - `Io` registers `primitives/Option`-independent IO ADT; order-free w.r.t.
///   the others except it needs the `primitives` module to exist.
///
/// Option/Trace/TestResult assembly is NOT a preset — tests that need `Option`
/// register it inline via their own `register_option` helpers (constructed
/// values through `register_type_def_self`, which is already clean). Per
/// Decision 0040, `Trace` relocated in full to `int`; there is no Trace preset.
#[cfg(test)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum FixtureContent {
    /// Special-form introspection metadata at root `""` (Principle 17 / FIXME
    /// 0193). `if`/`let`/`fn`/`defn`/`deftype`/`match`/`deftrait`/`impl`/`defmacro`.
    SpecialForms,
    /// Builtin type names in `primitives`: `Int`/`Bool`/`Float`/`String`
    /// (`IntrinsicType`) + `Vec` (`TypeDef`). Spec §3.1, §8.9.1.
    BuiltinTypeNames,
    /// Ring 0/1/3 primitive `Def`s (arithmetic / comparison / bool / string /
    /// vec) whose schemes match the spec contract (Appendix A.2/A.3/A.5).
    Primitives,
    /// Synthetic `macros` module: `SList`/`Sexp` ADTs + `sconcat` (spec §9.1).
    MacrosSexp,
    /// `IO` ADT (`Pure`/`Effect`/`Bind`) + `bind` primitive in `primitives`
    /// (spec §10; backs IO exhaustiveness tests in adt.rs).
    Io,
}

/// TEST-ONLY: composable Tier-3 fixture-content builder.
///
/// Declare exactly the presets a test starts from:
/// ```ignore
/// let modules = DashMap::new();
/// let next_id = AtomicU32::new(0);
/// FixtureBuilder::new()
///     .with_special_forms()
///     .with_builtin_type_names()
///     .with_primitives()
///     .seed(&modules, &next_id);
/// ```
/// [`FixtureBuilder::full`] composes ALL presets (the prior all-on world);
/// `TestFixture::new()` delegates to it so existing call sites stay green.
#[cfg(test)]
#[derive(Default)]
pub(crate) struct FixtureBuilder {
    contents: Vec<FixtureContent>,
}

#[cfg(test)]
impl FixtureBuilder {
    /// Begin an empty builder — no presets selected.
    pub(crate) fn new() -> Self {
        FixtureBuilder { contents: Vec::new() }
    }

    /// All presets composed in bootstrap-valid order — the full synthetic
    /// world the prior `seed_synthetic_modules` + `seed_test_primitives` pair
    /// produced. `TestFixture::new()` uses this.
    pub(crate) fn full() -> Self {
        FixtureBuilder::new()
            .with_special_forms()
            .with_builtin_type_names()
            .with_macros_sexp()
            .with_io()
            .with_primitives()
    }

    /// Add the special-form metadata preset (root `""`).
    pub(crate) fn with_special_forms(mut self) -> Self {
        self.contents.push(FixtureContent::SpecialForms);
        self
    }

    /// Add the builtin type-name preset (`Int`/`Bool`/`Float`/`String`/`Vec`).
    pub(crate) fn with_builtin_type_names(mut self) -> Self {
        self.contents.push(FixtureContent::BuiltinTypeNames);
        self
    }

    /// Add the Ring 0/1/3 primitive `Def` preset.
    pub(crate) fn with_primitives(mut self) -> Self {
        self.contents.push(FixtureContent::Primitives);
        self
    }

    /// Add the synthetic `macros` module preset (Sexp/SList + sconcat).
    pub(crate) fn with_macros_sexp(mut self) -> Self {
        self.contents.push(FixtureContent::MacrosSexp);
        self
    }

    /// Add the `IO` ADT + `bind` preset.
    pub(crate) fn with_io(mut self) -> Self {
        self.contents.push(FixtureContent::Io);
        self
    }

    /// Seed the selected presets into `modules`. Presets are applied in the
    /// order requested; [`FixtureBuilder::full`] orders them for bootstrap
    /// validity. The `primitives` and root `""` modules are created on demand.
    pub(crate) fn seed<C, L>(
        self,
        modules: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable<C, L>>,
        next_id: &std::sync::atomic::AtomicU32,
    )
    where
        C: cranelisp_types::CodeStore,
        L: cranelisp_types::LinkerStore,
    {
        let module_aliases = cranelisp_types::ModuleAliases::default();
        let prelude_fallback = crate::checker::PreludeFallback::default();
        let env = TypeCheckEnv::new(modules, next_id, &module_aliases, &prelude_fallback);
        let mut state = CheckState::new(ModuleFullPath::from("user"));

        // Ensure the always-needed synthetic modules exist before any preset
        // touches them.
        let primitives_path = ModuleFullPath::from("primitives");
        if !modules.contains_key(&primitives_path) {
            modules.insert(
                primitives_path.clone(),
                cranelisp_types::SymbolTable::<C, L>::new_with_params(primitives_path.clone()),
            );
        }
        let root_path = ModuleFullPath::from("");
        if !modules.contains_key(&root_path) {
            modules.insert(
                root_path.clone(),
                cranelisp_types::SymbolTable::<C, L>::new_with_params(root_path.clone()),
            );
        }

        for content in self.contents {
            match content {
                FixtureContent::SpecialForms => env.register_special_forms(),
                FixtureContent::BuiltinTypeNames => env.register_builtin_type_names(),
                FixtureContent::MacrosSexp => env.register_macros_module(&mut state),
                FixtureContent::Io => {
                    env.register_io_type(&mut state);
                    env.register_bind_primitive();
                }
                FixtureContent::Primitives => {
                    seed_test_primitives(modules, next_id);
                }
            }
        }
    }
}

#[cfg(test)]
impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {



    /// Register special form entries for REPL introspection.
    ///
    /// Per Principle 17 amendment (FIXME 0193): special-form metadata lives
    /// at root `""`. Other modules do NOT inherit, import, or seed from `""`;
    /// these entries are never reached by short-name resolution (special
    /// forms bypass resolution entirely — they're recognized by the
    /// parser/expander and lowered into AST nodes). The root's SymbolTable
    /// serves exactly one purpose: providing a uniform location for
    /// `/info`/`/doc` introspection of special-form metadata.
    fn register_special_forms(&self) {
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

        let root_path = ModuleFullPath::from("");
        let mut root_table = self
            .modules
            .get_mut(&root_path)
            .unwrap_or_else(|| unreachable!("invariant: root `\"\"` module should exist (bootstrap)"));

        for (name, desc) in special_forms {
            root_table.insert(
                Symbol::from(name),
                ModuleEntry::SpecialForm {
                    // Special forms don't have meaningful type schemes.
                    // Use a dummy scheme that won't be instantiated.
                    scheme: mono(Type::Int),
                    param_names: vec![],
                    docstring: Some(desc.to_string()),
                    description: desc.to_string(),
                    visibility: Visibility::Public,
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
        // Phase B Part 1: the four intrinsic scalars (`Int`, `Bool`, `Float`,
        // `String`) register as `ModuleEntry::IntrinsicType` carrying their
        // direct `Type` variant. `Vec` stays as `TypeDef` because no
        // `Type::Vec` variant exists — vec is encoded via
        // `Type::ADT(primitives/Vec, [elem])`.
        let intrinsic_scalars: Vec<(&str, Type, &str)> = vec![
            ("Int", Type::Int, "Machine-word signed integer (spec §3.1)."),
            ("Bool", Type::Bool, "Boolean truth value: true or false (spec §3.1)."),
            ("Float", Type::Float, "Double-precision floating-point number (spec §3.1)."),
            ("String", Type::String, "Immutable UTF-8 text value (spec §3.1)."),
        ];
        let typedef_builtins: Vec<(&str, &str)> = vec![
            ("Vec", "builtin vector type"),
        ];

        // Per spec §8.9.1: builtin types live in `primitives` and require
        // explicit import. They are NOT seeded into `user`.
        let primitives_path = ModuleFullPath::from("primitives");
        let mut primitives_table = self
            .modules
            .get_mut(&primitives_path)
            .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));

        for (name, ty, desc) in intrinsic_scalars {
            primitives_table.insert(
                Symbol::from(name),
                ModuleEntry::IntrinsicType {
                    ty,
                    visibility: Visibility::Public,
                    docstring: Some(desc.to_string()),
                },
            );
        }

        for (name, desc) in typedef_builtins {
            primitives_table.insert(
                Symbol::from(name),
                ModuleEntry::TypeDef {
                    info: TypeDefInfo {
                        name: primitives_fqtn(name),
                        type_params: vec![],
                        constructors: vec![],
                    },
                    visibility: Visibility::Public,
                    docstring: Some(desc.to_string()),
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
        state.current_module = macros_path.clone();

        // Phase B Part 2b: the Sexp/SList type definitions reference bare
        // `Int`/`Bool`/`Float`/`String` in their field types. With the Tier 2
        // universe walk deleted, bare-name resolution is import-scoped per
        // Principle 17 — so we must explicitly import the intrinsic scalars
        // from `primitives` into `macros`. (`Int` etc. are
        // `ModuleEntry::IntrinsicType` post-Part-1; the import edge resolves
        // via `resolve_terminal_entry_and_home`.)
        let primitives_path = ModuleFullPath::from("primitives");
        for sym in ["Int", "Bool", "Float", "String"] {
            let source = cranelisp_types::FQSymbol {
                module: primitives_path.clone(),
                symbol: Symbol::from(sym),
            };
            self.current_symbol_table_mut(state).insert(
                Symbol::from(sym),
                ModuleEntry::Import {
                    source,
                    visibility: Visibility::Private,
                },
            );
        }

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
            ModuleEntry::def(mono(sconcat_type), DefKind::Primitive)
                .docstring("Concatenate two SList Sexp values")
                .param_names(vec![Symbol::from("a"), Symbol::from("b")])
                .build(),
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
                    },
                    visibility: Visibility::Public,
                    docstring: None,
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
                        span: Span::SYNTHETIC,
                    },
                    FieldDef {
                        name: Symbol::from("stail"),
                        type_expr: TypeExpr::Applied(cranelisp_types::TypeRef::new(None, TypeName::from("SList")),
                            vec![TypeExpr::TypeVar(Symbol::from("a"))],
                        ),
                        span: Span::SYNTHETIC,
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
                    },
                    visibility: Visibility::Public,
                    docstring: None,
                },
            );
        }

        let slist_sexp = TypeExpr::Applied(cranelisp_types::TypeRef::new(None, TypeName::from("SList")),
            vec![TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Sexp")))],
        );

        let sexp_ctors = vec![
            Self::sexp_ctor("SexpInt", "sval", TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))),
            Self::sexp_ctor("SexpFloat", "sval", TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Float")))),
            Self::sexp_ctor("SexpBool", "sval", TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Bool")))),
            Self::sexp_ctor("SexpStr", "sval", TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("String")))),
            Self::sexp_ctor("SexpSym", "sname", TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("String")))),
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
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        }
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
            self.modules.insert(
                primitives_path.clone(),
                cranelisp_types::SymbolTable::<C, L>::new_with_params(primitives_path.clone()),
            );
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
                    span: Span::SYNTHETIC,
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
                    span: Span::SYNTHETIC,
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

        // Per S70 retirement of `ConstructorInfo` + `ModuleEntry::Constructor`:
        // The Bind constructor is now a `ModuleEntry::Def` with
        // `kind: DefKind::Constructor { type_name, tag, field_count,
        // internal: true }`. The name is appended to the IO TypeDef's
        // constructor-name list. Bind is internal — `internal: true` excludes
        // it from exhaustiveness checks and from user-visible introspection.
        let io_fqtn = primitives_fqtn("IO");
        let bind_param_names = vec![Symbol::from("inner"), Symbol::from("cont")];
        let bind_field_count = 2;
        let bind_ctor_scheme = Scheme {
            type_vars: vec![a_id, b_id],
            constraints: HashMap::new(),
            ty: Type::Fn(
                vec![io_b.clone(), cont_ty.clone()],
                Box::new(Type::ADT(io_fqtn.clone(), vec![Type::Var(a_id)])),
            ),
        };
        let body_span = Span::SYNTHETIC;
        let synth_params: Vec<(Symbol, Option<TypeExpr>)> = bind_param_names
            .iter().cloned().map(|n| (n, None)).collect();
        let synth_body = cranelisp_types::Expr::ConstrADT {
            type_name: io_fqtn.clone(),
            tag: 2,
            fields: bind_param_names.iter().map(|n| cranelisp_types::Expr::var(n.clone(), body_span)).collect(),
            span: body_span,
            inferred_type: None,
        };

        // Append Bind name to IO TypeDef's constructor list and register the
        // ctor Def in primitives.
        let primitives_path = ModuleFullPath::from("primitives");
        let mut primitives_table = self.modules.get_mut(&primitives_path)
            .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));
        if let Some(ModuleEntry::TypeDef { info, .. }) = primitives_table.symbols.get_mut(&Symbol::from("IO")) {
            info.constructors.push(Symbol::from("Bind"));
        } else {
            unreachable!("invariant: IO type should be registered before adding Bind");
        }
        primitives_table.insert(
            Symbol::from("Bind"),
            ModuleEntry::def(
                bind_ctor_scheme,
                DefKind::Constructor {
                    type_name: io_fqtn,
                    tag: 2,
                    field_count: bind_field_count,
                    internal: true,
                    // `Bind` is a sum ctor of `IO` (Pure/Effect/Bind), not a
                    // product type — it has no type facet (S79 Option 3a).
                    type_def: None,
                },
            )
            .docstring("Chain IO actions (internal — constructed by bind primitive)")
            .param_names(bind_param_names)
            .ast(cranelisp_types::DefnVariant {
                params: synth_params,
                body: synth_body,
                span: body_span,
            })
            .build(),
        );
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
            type_vars: vec![a_id, b_id],
            constraints: HashMap::new(),
            ty: bind_ty,
        };

        let mut primitives_table = self
            .modules
            .get_mut(&primitives_path)
            .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));

        primitives_table.insert(
            Symbol::from("bind"),
            ModuleEntry::def(bind_scheme, DefKind::Primitive)
                .docstring("Chain IO actions: extract value from first IO, pass to continuation")
                .param_names(vec![Symbol::from("io"), Symbol::from("f")])
                .build(),
        );
    }

}

/// Look up the spec-mandated docstring for a builtin primitive.
///
/// Docstrings are taken verbatim from the Description column in
/// `spec/appendix-a-builtins.md` §A.3. Section A.5 requires all
/// primitive functions to have docstrings available at runtime.
///
/// Returns `Some(docstring)` for known primitives, `None` otherwise.
///
/// Retained alongside the test suite as a docstring-shape oracle — primitive
/// registration itself was retired in Sprint 72 Wave 1 (Trigger 1 — per
/// Decision 0048, primitives now flow from `cranelisp-primitives`'
/// `PRIMITIVES_TABLE` Arc-cloned into session at startup; typecheck no
/// longer registers primitive Defs). Tests in this module still exercise
/// the shape to verify the spec §A.5 contract.
#[cfg(test)]
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
        "string-length" => "String length in bytes",
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

// ---------------------------------------------------------------------------
// Test-only: synthesize primitive Defs in the `primitives` module
// ---------------------------------------------------------------------------
//
// Per Decision 0048, the production session sources primitive Defs from
// `cranelisp-primitives::PRIMITIVES_TABLE` (Arc-cloned at startup); typecheck
// itself no longer registers primitive Defs. The typecheck crate has NO
// dependency on `cranelisp-primitives` (not even dev-dep).
//
// Typecheck's own tests still need plausible primitive-shaped Defs to exercise
// inference / trait dispatch / multi-sig / monomorphisation flows. This module
// seeds the `primitives` module with synthetic Defs whose schemes match the
// spec contract (Appendix A.2 / A.3 / A.5) — same schemes the real
// `PRIMITIVES_TABLE` carries at the production boundary.
//
// This is a test fixture, not a production registration path. Coverage is
// scoped to the set the unit-tests reference: arithmetic / comparison / bool /
// string / vec / quote-sexp. If a future test needs a primitive not listed
// here, extend `seed_test_primitives` or insert inline at the test.
#[cfg(test)]
pub(crate) fn seed_test_primitives<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable<C, L>>,
    next_id: &std::sync::atomic::AtomicU32,
)
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    use std::sync::atomic::Ordering;

    let primitives_path = ModuleFullPath::from("primitives");

    // Build a flat list of (name, scheme, param_names) tuples. All Ring 0/1/3
    // primitives are monomorphic except Vec ops + quote-sexp's polymorphic ret.
    let int_binop = Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int));
    let float_binop = Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float));
    let int_cmp = Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool));
    let float_cmp = Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Bool));
    let bool_unary = Type::Fn(vec![Type::Bool], Box::new(Type::Bool));
    let bool_binop = Type::Fn(vec![Type::Bool, Type::Bool], Box::new(Type::Bool));
    let lhs_rhs = vec![Symbol::from("lhs"), Symbol::from("rhs")];

    let mono_primitives: Vec<(&str, Type, Vec<Symbol>)> = vec![
        // Int arithmetic
        ("add-i64", int_binop.clone(), lhs_rhs.clone()),
        ("sub-i64", int_binop.clone(), lhs_rhs.clone()),
        ("mul-i64", int_binop.clone(), lhs_rhs.clone()),
        ("div-i64", int_binop.clone(), lhs_rhs.clone()),
        // Float arithmetic
        ("add-f64", float_binop.clone(), lhs_rhs.clone()),
        ("sub-f64", float_binop.clone(), lhs_rhs.clone()),
        ("mul-f64", float_binop.clone(), lhs_rhs.clone()),
        ("div-f64", float_binop.clone(), lhs_rhs.clone()),
        // Int comparison
        ("eq-i64", int_cmp.clone(), lhs_rhs.clone()),
        ("lt-i64", int_cmp.clone(), lhs_rhs.clone()),
        ("gt-i64", int_cmp.clone(), lhs_rhs.clone()),
        ("le-i64", int_cmp.clone(), lhs_rhs.clone()),
        ("ge-i64", int_cmp.clone(), lhs_rhs.clone()),
        // Float comparison
        ("eq-f64", float_cmp.clone(), lhs_rhs.clone()),
        ("lt-f64", float_cmp.clone(), lhs_rhs.clone()),
        ("gt-f64", float_cmp.clone(), lhs_rhs.clone()),
        ("le-f64", float_cmp.clone(), lhs_rhs.clone()),
        ("ge-f64", float_cmp.clone(), lhs_rhs.clone()),
        // Boolean
        ("not", bool_unary, vec![Symbol::from("b")]),
        ("eq-bool", bool_binop, lhs_rhs.clone()),
        // Ring 1 string / conversion
        (
            "str-concat",
            Type::Fn(vec![Type::String, Type::String], Box::new(Type::String)),
            vec![Symbol::from("a"), Symbol::from("b")],
        ),
        (
            "str-eq",
            Type::Fn(vec![Type::String, Type::String], Box::new(Type::Bool)),
            vec![Symbol::from("a"), Symbol::from("b")],
        ),
        (
            "str-len",
            Type::Fn(vec![Type::String], Box::new(Type::Int)),
            vec![Symbol::from("s")],
        ),
        (
            "string-identity",
            Type::Fn(vec![Type::String], Box::new(Type::String)),
            vec![Symbol::from("s")],
        ),
        (
            "int-to-string",
            Type::Fn(vec![Type::Int], Box::new(Type::String)),
            vec![Symbol::from("n")],
        ),
        (
            "float-to-string",
            Type::Fn(vec![Type::Float], Box::new(Type::String)),
            vec![Symbol::from("f")],
        ),
        (
            "bool-to-string",
            Type::Fn(vec![Type::Bool], Box::new(Type::String)),
            vec![Symbol::from("b")],
        ),
        (
            "parse-int",
            Type::Fn(
                vec![Type::String],
                Box::new(Type::ADT(primitives_fqtn("Option"), vec![Type::Int])),
            ),
            vec![Symbol::from("s")],
        ),
        // Ring 1 extended string ops
        (
            "substring",
            Type::Fn(vec![Type::String, Type::Int, Type::Int], Box::new(Type::String)),
            vec![Symbol::from("s"), Symbol::from("start"), Symbol::from("end")],
        ),
        (
            "char-at",
            Type::Fn(vec![Type::String, Type::Int], Box::new(Type::String)),
            vec![Symbol::from("s"), Symbol::from("idx")],
        ),
        (
            "string-length",
            Type::Fn(vec![Type::String], Box::new(Type::Int)),
            vec![Symbol::from("s")],
        ),
        // Macro support (Ring 3) — quote-sexp is monomorphic (Fn [Sexp] Sexp).
        // Seeded only if macros module's `Sexp` type is available (it is —
        // register_builtins seeds the macros module before this helper runs).
        (
            "quote-sexp",
            Type::Fn(
                vec![Type::ADT(macros_fqtn("Sexp"), vec![])],
                Box::new(Type::ADT(macros_fqtn("Sexp"), vec![])),
            ),
            vec![Symbol::from("sexp")],
        ),
    ];

    // Acquire a write guard for the primitives module and insert each
    // monomorphic primitive as a `DefKind::Primitive` Def.
    {
        let mut prims = modules
            .get_mut(&primitives_path)
            .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));
        for (name, ty, param_names) in mono_primitives {
            let mut builder = ModuleEntry::def(mono(ty), DefKind::Primitive)
                .param_names(param_names);
            if let Some(doc) = builtin_docstring(name) {
                builder = builder.docstring(doc);
            }
            prims.insert(Symbol::from(name), builder.build());
        }
    }

    // Polymorphic Vec primitives — each carries a fresh quantified type var
    // `a`. Pattern matches `register_bind_primitive` shape.
    let vec_fqtn = primitives_fqtn("Vec");
    let vec_primitives: Vec<(&str, fn(TypeId, &FQTypeName) -> Type, Vec<Symbol>)> = vec![
        // vec-get :: forall [a]. (Fn [(Vec a) Int] a)
        (
            "vec-get",
            |a, vec_fqtn| {
                Type::Fn(
                    vec![
                        Type::ADT(vec_fqtn.clone(), vec![Type::Var(a)]),
                        Type::Int,
                    ],
                    Box::new(Type::Var(a)),
                )
            },
            vec![Symbol::from("v"), Symbol::from("idx")],
        ),
        // vec-set :: forall [a]. (Fn [(Vec a) Int a] (Vec a))
        (
            "vec-set",
            |a, vec_fqtn| {
                let va = Type::ADT(vec_fqtn.clone(), vec![Type::Var(a)]);
                Type::Fn(
                    vec![va.clone(), Type::Int, Type::Var(a)],
                    Box::new(va),
                )
            },
            vec![Symbol::from("v"), Symbol::from("idx"), Symbol::from("val")],
        ),
        // vec-push :: forall [a]. (Fn [(Vec a) a] (Vec a))
        (
            "vec-push",
            |a, vec_fqtn| {
                let va = Type::ADT(vec_fqtn.clone(), vec![Type::Var(a)]);
                Type::Fn(
                    vec![va.clone(), Type::Var(a)],
                    Box::new(va),
                )
            },
            vec![Symbol::from("v"), Symbol::from("val")],
        ),
        // vec-len :: forall [a]. (Fn [(Vec a)] Int)
        (
            "vec-len",
            |a, vec_fqtn| {
                Type::Fn(
                    vec![Type::ADT(vec_fqtn.clone(), vec![Type::Var(a)])],
                    Box::new(Type::Int),
                )
            },
            vec![Symbol::from("v")],
        ),
    ];

    {
        let mut prims = modules
            .get_mut(&primitives_path)
            .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));
        for (name, ty_build, param_names) in vec_primitives {
            let a_id = next_id.fetch_add(1, Ordering::SeqCst);
            let ty = ty_build(a_id, &vec_fqtn);
            let scheme = Scheme {
                type_vars: vec![a_id],
                constraints: HashMap::new(),
                ty,
            };
            let mut builder = ModuleEntry::def(scheme, DefKind::Primitive)
                .param_names(param_names);
            if let Some(doc) = builtin_docstring(name) {
                builder = builder.docstring(doc);
            }
            prims.insert(Symbol::from(name), builder.build());
        }
    }

    // NOT auto-imported into `user` — per spec, primitives/constructors are
    // explicitly imported. Tests that need bare-name resolution of `add-i64`
    // etc. in their current module should either (a) switch to a module that
    // imports primitives (see `tc_with_prims` in program/infer test modules),
    // or (b) look up primitives by qualified path (`primitives/add-i64`) or
    // direct module probe.
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::checker::TestFixture;
    use cranelisp_types::{ModuleEntry, Type};

    /// Helper: get the `primitives` module's symbol table from a TestFixture.
    fn primitives_table(tf: &TestFixture) -> dashmap::mapref::one::Ref<'_, ModuleFullPath, cranelisp_types::SymbolTable> {
        let path = ModuleFullPath::from("primitives");
        tf.modules
            .get(&path)
            .expect("primitives module should exist")
    }

    // spec: design/arch/fixmes/0239 — Tier-3 presets compose opt-in, not all-on.
    // A builder with only `with_primitives` seeds the primitive Defs but NOT
    // the special-form metadata; this guards the preset boundary (negative).
    #[test]
    fn test_primitives_preset_seeds_without_special_forms() {
        let tf = TestFixture::with_content(FixtureBuilder::new().with_primitives());
        // Primitive Defs are present.
        assert!(primitives_table(&tf).get("add-i64").is_some());
        // Special-form metadata at root `""` is absent (preset not selected).
        let root_path = ModuleFullPath::from("");
        let root = tf.modules.get(&root_path).expect("root `\"\"` always exists");
        assert!(
            root.get("if").is_none(),
            "with_primitives must NOT seed special forms"
        );
    }

    // spec: design/arch/fixmes/0241 — Tier-2 SymbolTableBuilder resolves in the
    // typecheck test build (test-support feature) and round-trips an entry built
    // via the Tier-1 ModuleEntry::def constructor.
    #[test]
    fn test_tier2_symbol_table_builder_visible() {
        use cranelisp_types::test_support::SymbolTableBuilder;
        use cranelisp_types::{DefKind, Symbol};
        let table: cranelisp_types::SymbolTable = SymbolTableBuilder::new(ModuleFullPath::from("t"))
            .entry(
                Symbol::from("k"),
                ModuleEntry::def(crate::scheme::mono(Type::Int), DefKind::Primitive)
                    .docstring("const")
                    .build(),
            )
            .build();
        assert!(table.get("k").is_some());
    }

    /// Spec-mandated Ring 0 primitive names (spec appendix-a-builtins §A.2).
    /// Replaces the prior import of `cranelisp_primitives::ring0_primitives()`
    /// (now `pub(crate)` per Decision 0048). This crate has no `cranelisp-primitives`
    /// dep; the spec names are the durable contract being tested.
    const RING0_PRIMITIVE_NAMES: &[&str] = &[
        // Int arithmetic
        "add-i64", "sub-i64", "mul-i64", "div-i64",
        // Float arithmetic
        "add-f64", "sub-f64", "mul-f64", "div-f64",
        // Int comparisons
        "eq-i64", "lt-i64", "gt-i64", "le-i64", "ge-i64",
        // Float comparisons
        "eq-f64", "lt-f64", "gt-f64", "le-f64", "ge-f64",
        // Bool ops
        "not", "eq-bool",
    ];

    /// Spec-mandated Ring 1 primitive names (spec appendix-a-builtins §A.3).
    const RING1_PRIMITIVE_NAMES: &[&str] = &[
        "str-concat", "string-length", "substring", "char-at",
        "int-to-string", "float-to-string", "bool-to-string",
        "parse-int",
    ];

    /// Read constructor metadata (tag, field count, internal) from a Def entry's
    /// `DefKind::Constructor`. Post-S70: per-ctor metadata lives on the Def, not
    /// on a separate `ConstructorInfo`.
    fn read_ctor_kind(
        table: &cranelisp_types::SymbolTable,
        name: &str,
    ) -> Option<(usize, usize, bool, FQTypeName)> {
        match table.get(name)? {
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                DefKind::Constructor { tag, field_count, internal, type_name, .. } => {
                    Some((*tag, *field_count, *internal, type_name.clone()))
                }
                _ => None,
            },
            _ => None,
        }
    }

    // spec: appendix-a-builtins §A.2 — all ring-0 primitives registered in primitives module
    #[test]
    fn test_primitives_registered() {
        let tf = TestFixture::new();
        let pt = primitives_table(&tf);
        // All Ring 0 primitives should be in the primitives module
        for name in RING0_PRIMITIVE_NAMES {
            assert!(
                pt.get(*name).is_some(),
                "primitive {name} should be in primitives module",
            );
        }
    }

    // spec: appendix-a-builtins §A.2 — add-i64 has monomorphic (Fn [Int Int] Int) scheme
    #[test]
    fn test_add_i64_scheme() {
        let tf = TestFixture::new();
        if let Some(ModuleEntry::Def { scheme, .. }) = primitives_table(&tf).get("add-i64") {
            // Monomorphic: no quantified vars
            assert!(scheme.type_vars.is_empty(), "add-i64 should have no quantified vars");
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
            assert!(scheme.type_vars.is_empty(), "add-f64 should have no quantified vars");
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
            assert!(scheme.type_vars.is_empty(), "eq-i64 should have no quantified vars");
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
            assert!(scheme.type_vars.is_empty(), "not should have no quantified vars");
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
                    DefKind::Primitive
                ),
                "add-i64 should be Primitive::Inline"
            );
        } else {
            panic!("add-i64 not found");
        }
    }

    // spec: appendix-a-builtins §A.1 — special forms registered in root `""` table
    // Per Principle 17 amendment (FIXME 0193): special-form metadata lives at
    // the root module `""`, not seeded into every module.
    #[test]
    fn test_special_forms_registered() {
        // Narrowed to the minimal preset this test consumes: just the
        // special-form metadata, no primitives / macros / IO world.
        let tf = TestFixture::with_content(FixtureBuilder::new().with_special_forms());
        let forms = ["if", "let", "fn", "defn", "deftype", "match", "deftrait", "impl"];
        let root_path = ModuleFullPath::from("");
        let root_table = tf.modules.get(&root_path)
            .expect("root `\"\"` module should exist (bootstrap)");
        for name in forms {
            let entry = root_table.get(name);
            assert!(entry.is_some(), "special form {name} should be registered in root \"\"");
            assert!(
                matches!(entry, Some(ModuleEntry::SpecialForm { .. })),
                "{name} should be a SpecialForm"
            );
        }
    }

    // spec: appendix-a-builtins §A.2 — primitive count by category matches spec
    #[test]
    fn test_primitive_count() {
        let prims = RING0_PRIMITIVE_NAMES;
        // Count by name which maps directly to the primitive categories
        let int_arith = prims
            .iter()
            .filter(|name| matches!(**name, "add-i64" | "sub-i64" | "mul-i64" | "div-i64"))
            .count();
        let float_arith = prims
            .iter()
            .filter(|name| matches!(**name, "add-f64" | "sub-f64" | "mul-f64" | "div-f64"))
            .count();
        let int_cmp = prims
            .iter()
            .filter(|name| matches!(**name, "eq-i64" | "lt-i64" | "gt-i64" | "le-i64" | "ge-i64"))
            .count();
        let float_cmp = prims
            .iter()
            .filter(|name| matches!(**name, "eq-f64" | "lt-f64" | "gt-f64" | "le-f64" | "ge-f64"))
            .count();
        let bool_op = prims.iter().filter(|name| **name == "not").count();
        let bool_cmp = prims.iter().filter(|name| **name == "eq-bool").count();
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
            assert_eq!(scheme.type_vars.len(), 1, "vec-get should have 1 quantified var");
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
                matches!(kind.as_ref(), DefKind::Primitive),
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
            assert_eq!(scheme.type_vars.len(), 1, "vec-set should have 1 quantified var");
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
            assert_eq!(scheme.type_vars.len(), 1, "vec-push should have 1 quantified var");
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
            assert_eq!(scheme.type_vars.len(), 1, "vec-len should have 1 quantified var");
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
            tf.env()
                .lookup_trait_decl_in_module(
                    &cranelisp_types::ModuleFullPath::from("user"),
                    &cranelisp_types::TraitName::from("Num"),
                )
                .is_none(),
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
        let macros_path = ModuleFullPath::from("macros");
        let info = tf.lookup_type_def_in_module(&macros_path, &TypeName::from("SList"));
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
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = macros_table.get("SNil") {
            if let DefKind::Constructor { tag, field_count, .. } = kind.as_ref() {
                assert_eq!(*tag, 0, "SNil should be tag 0");
                assert_eq!(*field_count, 0, "SNil should have no fields");
            } else {
                panic!("SNil should be DefKind::Constructor, got {:?}", kind);
            }
            assert_eq!(scheme.type_vars.len(), 1, "SNil should have 1 quantified var (polymorphic)");
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
            panic!("SNil should be a Def entry (Constructor kind) in macros module");
        }
    }

    // spec: 09-macros §9.1.1 — SCons constructor: (Fn [a (SList a)] (SList a))
    #[test]
    fn test_scons_constructor_type() {
        let tf = TestFixture::new();
        let macros_path = ModuleFullPath::from("macros");
        let macros_table = tf.modules.get(&macros_path).unwrap();
        if let Some(ModuleEntry::Def { kind, scheme, param_names, .. }) = macros_table.get("SCons") {
            if let DefKind::Constructor { tag, field_count, .. } = kind.as_ref() {
                assert_eq!(*tag, 1, "SCons should be tag 1");
                assert_eq!(*field_count, 2, "SCons has 2 fields");
            } else {
                panic!("SCons should be DefKind::Constructor");
            }
            assert_eq!(param_names.len(), 2, "SCons has 2 fields: shead, stail");
            assert_eq!(param_names[0].as_ref(), "shead");
            assert_eq!(param_names[1].as_ref(), "stail");
            assert_eq!(scheme.type_vars.len(), 1, "SCons should have 1 quantified var");
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
            panic!("SCons should be a Def entry (Constructor kind) in macros module");
        }
    }

    // spec: 09-macros §9.1.2 — Sexp type registered with 7 constructors
    #[test]
    fn test_sexp_type_registered() {
        let tf = TestFixture::new();
        let macros_path = ModuleFullPath::from("macros");
        let info = tf.lookup_type_def_in_module(&macros_path, &TypeName::from("Sexp"));
        assert!(info.is_some(), "Sexp type should be registered");
        let info = info.unwrap();
        assert!(info.type_params.is_empty(), "Sexp has 0 type parameters");
        assert_eq!(info.constructors.len(), 7, "Sexp has 7 constructors");

        // Verify tag order matches spec: SexpInt=0 through SexpBracket=6
        let expected_names = [
            "SexpInt", "SexpFloat", "SexpBool", "SexpStr",
            "SexpSym", "SexpList", "SexpBracket",
        ];
        let macros_path = ModuleFullPath::from("macros");
        let macros_table = tf.modules.get(&macros_path).unwrap();
        for (i, name) in expected_names.iter().enumerate() {
            assert_eq!(
                info.constructors[i].as_ref(), *name,
                "constructor at tag {i} should be {name}"
            );
            let (tag, _, _, _) = read_ctor_kind(&macros_table, name)
                .unwrap_or_else(|| panic!("{name} should be a Def(Constructor) in macros module"));
            assert_eq!(tag, i, "{name} should have tag {i}");
        }
    }

    // spec: 09-macros §9.1.2 — SexpSym constructor: (Fn [String] Sexp)
    #[test]
    fn test_sexpsym_constructor_type() {
        let tf = TestFixture::new();
        let macros_path = ModuleFullPath::from("macros");
        let macros_table = tf.modules.get(&macros_path).unwrap();
        if let Some(ModuleEntry::Def { scheme, kind, .. }) = macros_table.get("SexpSym")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert!(scheme.type_vars.is_empty(), "SexpSym should be monomorphic");
            assert_eq!(
                scheme.ty,
                Type::Fn(
                    vec![Type::String],
                    Box::new(Type::ADT(macros_fqtn("Sexp"), vec![]))
                ),
                "SexpSym :: (Fn [String] Sexp)"
            );
        } else {
            panic!("SexpSym should be a Def(Constructor) entry in macros module");
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
        if let Some(ModuleEntry::Def { kind, scheme, param_names, .. }) = table.get(name) {
            let field_count = if let DefKind::Constructor { field_count, .. } = kind.as_ref() {
                *field_count
            } else {
                panic!("{name} should be DefKind::Constructor, got {:?}", kind);
            };
            assert_eq!(
                field_count,
                expected_fields.len(),
                "{name}: field count mismatch"
            );
            assert_eq!(param_names.len(), expected_fields.len(), "{name}: param_names count");
            // Read param types from the scheme's Fn signature (per S70: field types fold into scheme).
            let scheme_params = match &scheme.ty {
                Type::Fn(p, _) => p.clone(),
                _ => panic!("{name} scheme should be Fn"),
            };
            for (i, (fname, ftype)) in expected_fields.iter().enumerate() {
                assert_eq!(
                    param_names[i].as_ref(), *fname,
                    "{name}: field {i} name"
                );
                assert_eq!(
                    &scheme_params[i], *ftype,
                    "{name}: field {i} type"
                );
            }
            // Check the constructor scheme
            assert!(scheme.type_vars.is_empty(), "{name} should be monomorphic");
            let param_types: Vec<Type> = expected_fields.iter().map(|(_, t)| (*t).clone()).collect();
            assert_eq!(
                scheme.ty,
                Type::Fn(param_types, Box::new(ret_type.clone())),
                "{name}: constructor scheme"
            );
        } else {
            panic!("{name} should be a Def entry");
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
            assert!(scheme.type_vars.is_empty(), "sconcat should be monomorphic");
            assert!(
                matches!(
                    kind.as_ref(),
                    DefKind::Primitive
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
            assert!(scheme.type_vars.is_empty(), "quote-sexp should be monomorphic");
            assert!(
                matches!(
                    kind.as_ref(),
                    DefKind::Primitive
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
        let primitives_path = ModuleFullPath::from("primitives");
        let info = tf.lookup_type_def_in_module(&primitives_path, &TypeName::from("IO"));
        assert!(info.is_some(), "IO type should be registered");
        let info = info.unwrap();
        assert_eq!(info.type_params.len(), 1, "IO has 1 type parameter");
        assert_eq!(info.type_params[0].as_ref(), "a");
        assert_eq!(
            info.constructors.len(), 3,
            "IO has 3 constructors: Pure, Effect, Bind"
        );
        assert_eq!(
            tf.lookup_type_def_docstring_in_module(&primitives_path, &TypeName::from("IO"))
                .as_deref(),
            Some("Deferred IO computation tree")
        );
    }

    // spec: 10-io §10.1 — Pure constructor: tag=0, field `ioval` of type `a`
    #[test]
    fn test_pure_constructor() {
        let tf = TestFixture::new();
        let primitives_path = ModuleFullPath::from("primitives");
        let primitives_table = tf.modules.get(&primitives_path).unwrap();

        if let Some(ModuleEntry::Def { kind, scheme, param_names, .. }) =
            primitives_table.get("Pure")
        {
            if let DefKind::Constructor { tag, field_count, internal, .. } = kind.as_ref() {
                assert_eq!(*tag, 0, "Pure should be tag 0");
                assert_eq!(*field_count, 1, "Pure has 1 field");
                assert!(!*internal, "Pure is not internal");
            } else {
                panic!("Pure should be DefKind::Constructor");
            }
            assert_eq!(param_names.len(), 1);
            assert_eq!(param_names[0].as_ref(), "ioval");
            assert_eq!(scheme.type_vars.len(), 1, "Pure should have 1 quantified var");
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
            panic!("Pure should be a Def(Constructor) entry in primitives module");
        }
    }

    // spec: 10-io §10.1 — Effect constructor: tag=1, field `thunk` of type `a`
    #[test]
    fn test_effect_constructor() {
        let tf = TestFixture::new();
        let primitives_path = ModuleFullPath::from("primitives");
        let primitives_table = tf.modules.get(&primitives_path).unwrap();

        if let Some(ModuleEntry::Def { kind, scheme, param_names, .. }) =
            primitives_table.get("Effect")
        {
            if let DefKind::Constructor { tag, field_count, internal, .. } = kind.as_ref() {
                assert_eq!(*tag, 1, "Effect should be tag 1");
                assert_eq!(*field_count, 1, "Effect has 1 field");
                assert!(!*internal, "Effect is not internal");
            } else {
                panic!("Effect should be DefKind::Constructor");
            }
            assert_eq!(param_names.len(), 1);
            assert_eq!(param_names[0].as_ref(), "thunk");
            assert_eq!(scheme.type_vars.len(), 1, "Effect should have 1 quantified var");
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
            panic!("Effect should be a Def(Constructor) entry in primitives module");
        }
    }

    // spec: 10-io §10.1 — Bind constructor: tag=2, internal=true
    //
    // S70 retired `ConstructorInfo` + `ModuleEntry::Constructor`; the Bind
    // constructor is now a `ModuleEntry::Def { kind: DefKind::Constructor {
    // internal: true, .. }, .. }` in the primitives symbol table per the
    // migration map (check.rs §"ConstructorInfo retired"). The `internal: true`
    // discriminator (not absence-from-table) gates exhaustiveness checks and
    // user-visible introspection. Bind's field types involving the existential
    // type variable `b` live in the synthesised constructor scheme's Fn signature.
    #[test]
    fn test_bind_constructor_internal() {
        let tf = TestFixture::new();
        let primitives_path = ModuleFullPath::from("primitives");

        // Bind name appears in IO's TypeDefInfo.constructors list at index 2.
        let info = tf
            .lookup_type_def_in_module(&primitives_path, &TypeName::from("IO"))
            .unwrap();
        assert_eq!(info.constructors[2].as_ref(), "Bind");

        // The Bind Def carries tag, field_count, internal discriminator.
        let primitives_table = tf.modules.get(&primitives_path).unwrap();
        let (tag, field_count, internal, type_name) = read_ctor_kind(&primitives_table, "Bind")
            .expect("Bind should be a Def(Constructor) in primitives");
        assert_eq!(tag, 2, "Bind tag should be 2");
        assert_eq!(field_count, 2, "Bind has 2 fields: inner, cont");
        assert!(internal, "Bind must be internal");
        assert_eq!(type_name.name.as_ref(), "IO");

        // Inspect the synthesised Def: param_names + scheme.ty (Fn).
        if let Some(ModuleEntry::Def { param_names, scheme, .. }) = primitives_table.get("Bind") {
            assert_eq!(param_names.len(), 2);
            assert_eq!(param_names[0].as_ref(), "inner");
            assert_eq!(param_names[1].as_ref(), "cont");

            // Bind scheme :: forall [a, b]. (Fn [(IO b) (Fn [b] (IO a))] (IO a))
            match &scheme.ty {
                Type::Fn(params, _ret) => {
                    assert_eq!(params.len(), 2);
                    // inner: (IO b)
                    let inner_b = match &params[0] {
                        Type::ADT(name, args) => {
                            assert_eq!(name.name.as_ref(), "IO");
                            assert_eq!(args.len(), 1);
                            assert!(matches!(args[0], Type::Var(_)));
                            args[0].clone()
                        }
                        _ => panic!("Bind.inner should be (IO b), got {:?}", params[0]),
                    };
                    // cont: (Fn [b] (IO a))
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
                                _ => panic!("Bind.cont return should be (IO a)"),
                            }
                            // b in cont's param should match b in inner's IO type arg
                            assert_eq!(cont_params[0], inner_b,
                                "b should be the same type var in inner and cont");
                        }
                        _ => panic!("Bind.cont should be Fn type, got {:?}", params[1]),
                    }
                }
                _ => panic!("Bind scheme should be Fn, got {:?}", scheme.ty),
            }
        } else {
            panic!("Bind should be a Def(Constructor) entry in primitives module");
        }

        // Bind is registered as a Constructor Def in primitives — the
        // `internal: true` discriminator on `DefKind::Constructor` (not absence
        // from the symbol table) gates user-visible introspection. Phase B
        // Part 2b: `lookup_constructor_type` is current-module-only per
        // Principle 17 (no universe walk), so the assertion probes the
        // primitives module directly via `lookup_constructor_type_in_module`.
        assert!(
            tf.env()
                .lookup_constructor_type_in_module(&primitives_path, "Bind")
                .is_some(),
            "Bind should be a Constructor entry in the primitives module \
             (internal discriminator is on the Def, not absence from the table)"
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
            assert_eq!(scheme.type_vars.len(), 2, "bind should have 2 quantified vars (a, b)");

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
                    DefKind::Primitive
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
        for name in RING0_PRIMITIVE_NAMES {
            if let Some(ModuleEntry::Def { docstring, .. }) = pt.get(*name) {
                assert!(
                    docstring.is_some(),
                    "Ring 0 primitive {name} should have a docstring",
                );
            } else {
                panic!("Ring 0 primitive {name} not found");
            }
        }
    }

    // spec: appendix-a-builtins §A.5 — all Ring 1 primitives have docstrings
    #[test]
    fn test_ring1_primitives_have_docstrings() {
        let tf = TestFixture::new();
        let pt = primitives_table(&tf);
        for name in RING1_PRIMITIVE_NAMES {
            if let Some(ModuleEntry::Def { docstring, .. }) = pt.get(*name) {
                assert!(
                    docstring.is_some(),
                    "Ring 1 primitive {name} should have a docstring",
                );
            } else {
                panic!("Ring 1 primitive {name} not found");
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

    // -----------------------------------------------------------------------
    // Wave 3a-α redo Sub-D — α-wave invariant tests
    // -----------------------------------------------------------------------
    //
    // These tests guard the locality-correctness invariants established by
    // Wave 3a-α (Decision 45 + Decision 46 + Principle 17). See
    // `design/typecheck/implementation-slice-s66.md §5` for the test surface
    // plan.

    // spec: arch Principle 17 + slice §1.A α13 — synthetic modules have empty
    // imports/exports by invariant. Negative invariant guards against any
    // future defensive `(import [macros [*]])` re-injection into primitives.
    #[test]
    fn test_synthetic_modules_have_empty_imports_exports() {
        let tf = TestFixture::new();

        let primitives_path = ModuleFullPath::from("primitives");
        let primitives_table = tf
            .modules
            .get(&primitives_path)
            .expect("primitives module should exist");
        assert!(
            primitives_table.imports.is_empty(),
            "primitives.imports MUST be empty (Principle 17 + α13); found {} entries",
            primitives_table.imports.len()
        );
        assert!(
            primitives_table.exports.is_empty(),
            "primitives.exports MUST be empty (Principle 17 + α13); found {} entries",
            primitives_table.exports.len()
        );
        // Release this guard before acquiring the next.
        drop(primitives_table);

        let macros_path = ModuleFullPath::from("macros");
        let macros_table = tf
            .modules
            .get(&macros_path)
            .expect("macros module should exist");
        assert!(
            macros_table.imports.is_empty(),
            "macros.imports MUST be empty (Principle 17 + α13); found {} entries",
            macros_table.imports.len()
        );
        assert!(
            macros_table.exports.is_empty(),
            "macros.exports MUST be empty (Principle 17 + α13); found {} entries",
            macros_table.exports.len()
        );
    }

    // spec: arch Decision 46 + slice §1.A α14 — the retired closure-walk
    // function (name composed from three lowercase tokens joined with
    // underscores, see `forbidden` below) MUST NOT exist anywhere in the
    // typecheck crate's source. It was retired with Decision 45 Pattern B
    // (chain-follow replaces the closure walk). Permanent regression guard
    // against re-introduction.
    //
    // To avoid this guard self-tripping on its own source bytes, the
    // forbidden symbol is constructed at runtime from token parts; no
    // literal occurrence of the joined string appears anywhere in this
    // file (verified by the test itself — if it did, the test would fail
    // immediately).
    #[test]
    fn test_no_retired_closure_walk_fn_in_typecheck_src() {
        // Compile-time `include_str!` against every typecheck source file
        // we know contained or could plausibly contain the symbol. A
        // brand-new typecheck source file that ever defines or calls the
        // retired function MUST be added to this list — that
        // expansion-friction is intentional (forces a deliberate review
        // before the symbol can re-enter the crate).
        const SOURCES: &[(&str, &str)] = &[
            ("adt.rs", include_str!("adt.rs")),
            ("builtins.rs", include_str!("builtins.rs")),
            ("checker.rs", include_str!("checker.rs")),
            ("infer.rs", include_str!("infer.rs")),
            ("lib.rs", include_str!("lib.rs")),
            ("program.rs", include_str!("program.rs")),
            ("resolve.rs", include_str!("resolve.rs")),
            ("result.rs", include_str!("result.rs")),
            ("scheme.rs", include_str!("scheme.rs")),
            ("scope.rs", include_str!("scope.rs")),
            ("trace.rs", include_str!("trace.rs")),
            ("traits.rs", include_str!("traits.rs")),
            ("unify.rs", include_str!("unify.rs")),
        ];
        // Construct the forbidden symbol at runtime so this very test
        // file's literal mention of the substring (in panic messages,
        // doc-comments, the SOURCES list itself) does not self-trigger.
        let forbidden: String = ["transitive", "import", "closure"].join("_");

        for (name, body) in SOURCES {
            // Count occurrences; this test file itself constructs the
            // symbol at runtime so its source bytes never spell it
            // literally. Any literal occurrence is a regression.
            assert!(
                !body.contains(forbidden.as_str()),
                "`{forbidden}` MUST NOT appear in crates/cranelisp-typecheck/src/{name} \
                 — retired by Decision 45 Pattern B; chain-follow is THE navigation primitive \
                 (Principle 17). See design/typecheck/implementation-slice-s66.md §1.A α14."
            );
        }
    }
}
