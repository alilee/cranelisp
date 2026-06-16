//! Resolve TypeExpr (source annotations) to Type.
//!
//! All resolution returns Result, never panics (addresses audit HIGH-4).
//!
//! Resolution matches directly on the terminal [`ModuleEntry`] reached by the
//! injected `resolve_terminal` closure — no intermediate snapshot map. The
//! closure (built by the caller, which owns the symbol table) performs the
//! current-module lookup + import chain-follow and hands back the terminal
//! entry; this module reads everything it needs off that entry: ADT
//! `FQTypeName` and arity from `TypeDef`, the bare `Type` variant from
//! `IntrinsicType`. Keeping resolve.rs on the boundary type `ModuleEntry`
//! (rather than the checker's internals) preserves its decoupling.

use std::collections::HashMap;

use cranelisp_types::{
    CodeStore, ModuleEntry, ResolveError, Span, Symbol, Type, TypeExpr, TypeId, TypeRef,
};

use crate::checker::type_def_view_of;

/// Resolve a type expression to a concrete type.
///
/// `var_map` maps type variable names (e.g., `:a`) to their allocated TypeIds.
/// `resolve_terminal` resolves a [`TypeRef`] to its terminal [`ModuleEntry`]
/// via the caller's symbol table (current-module lookup + import chain-follow),
/// returning `None` when the name is not reachable.
pub fn resolve_type_expr<C: CodeStore>(
    texpr: &TypeExpr,
    var_map: &HashMap<Symbol, TypeId>,
    resolve_terminal: &dyn Fn(&TypeRef) -> Option<ModuleEntry<C>>,
    span: Span,
) -> Result<Type, ResolveError> {
    match texpr {
        TypeExpr::Named(name) => resolve_named(name, resolve_terminal, span),

        TypeExpr::FnType(params, ret) => {
            let param_types: Result<Vec<Type>, _> = params
                .iter()
                .map(|p| resolve_type_expr(p, var_map, resolve_terminal, span))
                .collect();
            let ret_type = resolve_type_expr(ret, var_map, resolve_terminal, span)?;
            Ok(Type::Fn(param_types?, Box::new(ret_type)))
        }

        TypeExpr::TypeVar(name) => var_map
            .get(name)
            .map(|&id| Type::Var(id))
            .ok_or_else(|| ResolveError::TypeNotFound {
                name: cranelisp_types::TypeName::from(name.as_ref()),
                from_module: cranelisp_types::ModuleFullPath::from(""),
                span,
            }),

        TypeExpr::SelfType => Err(ResolveError::TypeNotFound {
            name: cranelisp_types::TypeName::from("Self"),
            from_module: cranelisp_types::ModuleFullPath::from(""),
            span,
        }),

        TypeExpr::Applied(name, args) => {
            resolve_applied(name, args, var_map, resolve_terminal, span)
        }

        // A `Bounds([..])` annotation is NOT a concrete type — it is "an
        // unspecified type satisfying these trait bounds" (spec §3.9.2/§3.9.3,
        // FIXME 0346). It resolves to a *fresh constrained type variable*, not
        // to a `Type`, and the constraint must be accumulated onto the binder's
        // `Scheme.constraints`. That requires a fresh-var allocator and a
        // constraint sink (`active_constraints`) — neither of which this pure
        // `TypeExpr -> Type` resolver owns. The owning consumer
        // (`program.rs::register_defn_signature`, the try-type-then-trait site)
        // therefore intercepts `Bounds` *before* delegating here, so a `Bounds`
        // never reaches this arm in practice. Reaching it is an internal routing
        // bug; surface it rather than silently fabricating a concrete type.
        TypeExpr::Bounds(_) => Err(ResolveError::TypeNotFound {
            name: cranelisp_types::TypeName::from("<trait-bounds>"),
            from_module: cranelisp_types::ModuleFullPath::from(""),
            span,
        }),
    }
}

fn type_not_found(name: &TypeRef, span: Span) -> ResolveError {
    ResolveError::TypeNotFound {
        name: name.name.clone(),
        from_module: name
            .module
            .clone()
            .unwrap_or_else(|| cranelisp_types::ModuleFullPath::from("")),
        span,
    }
}

/// Resolve a named type by matching its terminal `ModuleEntry`.
///
/// A `TypeDef` (sum/enum) OR a single-ctor **product**'s ctor `Def`
/// (`Constructor { type_def: Some(..) }`, S79 dual facet) resolves to
/// `Type::ADT(info.name, [])` via [`type_def_view_of`]; `IntrinsicType` returns
/// its bare `Type` variant (`Type::Int`, etc.) directly.
fn resolve_named<C: CodeStore>(
    name: &TypeRef,
    resolve_terminal: &dyn Fn(&TypeRef) -> Option<ModuleEntry<C>>,
    span: Span,
) -> Result<Type, ResolveError> {
    match resolve_terminal(name) {
        Some(ModuleEntry::IntrinsicType { ty, .. }) => Ok(ty),
        Some(entry) => match type_def_view_of(&entry) {
            Some(info) => Ok(Type::ADT(info.name.clone(), vec![])),
            None => Err(type_not_found(name, span)),
        },
        None => Err(type_not_found(name, span)),
    }
}

/// Resolve an applied type constructor: `(Option Int)`, `(List :a)`.
///
/// Validates that the number of type arguments matches the ADT's declared
/// type-parameter count (`info.type_params.len()`).
fn resolve_applied<C: CodeStore>(
    name: &TypeRef,
    args: &[TypeExpr],
    var_map: &HashMap<Symbol, TypeId>,
    resolve_terminal: &dyn Fn(&TypeRef) -> Option<ModuleEntry<C>>,
    span: Span,
) -> Result<Type, ResolveError> {
    match resolve_terminal(name) {
        // Intrinsics are zero-arity; applied form short-circuits to the bare
        // `Type` (the parser can emit `Applied` with empty args).
        Some(ModuleEntry::IntrinsicType { ty, .. }) => Ok(ty),
        // `TypeDef` (sum/enum) OR a product ctor's type facet (S79 dual facet)
        // both answer as a type via `type_def_view_of`.
        Some(entry) => match type_def_view_of(&entry) {
            Some(info) => {
                // FIXME 0385: the builtin `Vec` (`primitives/Vec`) is genuinely
                // arity-1 (`(Vec a)`, spec §3.2.7) but is seeded with empty
                // `type_params` (no surface ctor / declared params — see
                // `src/bootstrap.rs` + `builtins.rs`). Its element type is carried
                // structurally in inference (`infer_vec_lit` builds
                // `Type::ADT(primitives/Vec, [elem])`), not via a declared param.
                // Without this carve-out `:(Vec Int)` fails the arity gate below
                // ("unknown type `Vec`"), leaving the §3.11.1 worked-example
                // disambiguation `(id :(Vec Int) [])` unfixable. Accept exactly one
                // type argument for the builtin `Vec` regardless of its (empty)
                // declared arity, resolving to `Type::ADT(primitives/Vec, [arg])`.
                if info.name.module.as_ref() == "primitives"
                    && info.name.name.as_ref() == "Vec"
                    && info.type_params.is_empty()
                {
                    if args.len() != 1 {
                        return Err(ResolveError::TypeNotFound {
                            name: name.name.clone(),
                            from_module: name
                                .module
                                .clone()
                                .unwrap_or_else(|| cranelisp_types::ModuleFullPath::from("")),
                            span,
                        });
                    }
                    let elem = resolve_type_expr(&args[0], var_map, resolve_terminal, span)?;
                    return Ok(Type::ADT(info.name.clone(), vec![elem]));
                }
                let expected_arity = info.type_params.len();
                if args.len() != expected_arity {
                    return Err(ResolveError::TypeNotFound {
                        name: name.name.clone(),
                        from_module: name
                            .module
                            .clone()
                            .unwrap_or_else(|| cranelisp_types::ModuleFullPath::from("")),
                        span,
                    });
                }
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| resolve_type_expr(a, var_map, resolve_terminal, span))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Type::ADT(info.name.clone(), resolved_args))
            }
            None => Err(type_not_found(name, span)),
        },
        None => Err(type_not_found(name, span)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{
        DefKind, FQTypeName, ModuleFullPath, Scheme, TypeDefInfo, TypeName, Visibility,
    };
    use std::collections::HashMap as StdHashMap;

    /// Test entry type: the unit `CodeStore` marker used in the crate's
    /// other unit tests for `ModuleEntry<()>`.
    type Entry = ModuleEntry<()>;

    fn test_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("test"), TypeName::from(name))
    }

    fn prim_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from(name))
    }

    /// Build an `IntrinsicType` entry carrying `ty`.
    fn intrinsic_entry(ty: Type) -> Entry {
        ModuleEntry::IntrinsicType {
            ty,
            visibility: Visibility::Public,
            docstring: None,
        }
    }

    /// Build a `TypeDef` entry with the given arity (type-param count).
    fn typedef_entry(name: &str, arity: usize) -> Entry {
        ModuleEntry::TypeDef {
            info: TypeDefInfo {
                name: test_fqtn(name),
                type_params: (0..arity)
                    .map(|i| Symbol::from(format!("t{i}")))
                    .collect(),
                constructors: vec![],
            },
            visibility: Visibility::Public,
            docstring: None,
        }
    }

    /// Build a single-ctor **product** entry: a got-slotted ctor `Def`
    /// carrying the type facet (`type_def: Some(..)`), per the S79 dual-facet
    /// model. The entry answers as its own type via `type_def_view_of`.
    fn product_ctor_entry(name: &str, arity: usize) -> Entry {
        let info = TypeDefInfo {
            name: test_fqtn(name),
            type_params: (0..arity)
                .map(|i| Symbol::from(format!("t{i}")))
                .collect(),
            constructors: vec![],
        };
        ModuleEntry::def(
            Scheme {
                type_vars: vec![],
                constraints: StdHashMap::new(),
                ty: Type::ADT(test_fqtn(name), vec![]),
            },
            DefKind::Constructor {
                got_slot: 0,
                type_name: test_fqtn(name),
                tag: 0,
                field_count: 0,
                internal: false,
                type_def: Some(Box::new(info)),
            },
        )
        .build()
    }

    /// A resolver closure backed by a small fixture map keyed on bare name.
    /// Mirrors the production chain-follow's terminal-entry result without
    /// needing a full `TypeCheckEnv`.
    fn resolver<'a>(
        map: &'a HashMap<&'static str, Entry>,
    ) -> impl Fn(&TypeRef) -> Option<Entry> + 'a {
        move |r: &TypeRef| map.get(r.name.as_ref()).cloned()
    }

    fn intrinsics_map() -> HashMap<&'static str, Entry> {
        let mut m = HashMap::new();
        m.insert("Int", intrinsic_entry(Type::Int));
        m.insert("Bool", intrinsic_entry(Type::Bool));
        m.insert("Float", intrinsic_entry(Type::Float));
        m.insert("String", intrinsic_entry(Type::String));
        m
    }

    fn named(name: &str) -> TypeExpr {
        TypeExpr::Named(TypeRef::new(None, TypeName::from(name)))
    }

    // spec: 03-types §3.1 — resolve primitive type names to bare Type values
    #[test]
    fn test_resolve_primitives() {
        let var_map = HashMap::new();
        let map = intrinsics_map();
        let r = resolver(&map);
        let span = Span::SYNTHETIC;

        for (name, expected) in [
            ("Int", Type::Int),
            ("Bool", Type::Bool),
            ("Float", Type::Float),
            ("String", Type::String),
        ] {
            assert_eq!(
                resolve_type_expr(&named(name), &var_map, &r, span).unwrap(),
                expected
            );
        }
    }

    // spec: 03-types §3.1 — intrinsic FQ identity does not leak into the bare
    // resolved Type (regression: a prior `KnownTypeKind::Intrinsic.fqtn` field
    // was dead — the resolved value is the bare variant, never an ADT wrap).
    #[test]
    fn test_intrinsic_resolves_to_bare_not_adt() {
        let var_map = HashMap::new();
        let mut map = intrinsics_map();
        // Even with an FQ home of `primitives`, resolution yields `Type::Int`.
        map.insert("Int", intrinsic_entry(Type::Int));
        let _ = prim_fqtn("Int"); // FQ identity is irrelevant to the result.
        let r = resolver(&map);

        let ty = resolve_type_expr(&named("Int"), &var_map, &r, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::Int);
        assert!(!matches!(ty, Type::ADT(..)));
    }

    // spec: 03-types §3.9.3 — unknown type name produces error
    #[test]
    fn test_resolve_unknown_type() {
        let var_map = HashMap::new();
        let map: HashMap<&'static str, Entry> = HashMap::new();
        let r = resolver(&map);

        let err = resolve_type_expr(&named("Foo"), &var_map, &r, Span::SYNTHETIC).unwrap_err();
        assert!(matches!(err, ResolveError::TypeNotFound { .. }));
    }

    // spec: 03-types §3.2.2 — resolve user-defined ADT name to ADT type
    #[test]
    fn test_resolve_user_defined_adt() {
        let var_map = HashMap::new();
        let mut map: HashMap<&'static str, Entry> = HashMap::new();
        map.insert("Color", typedef_entry("Color", 0));
        let r = resolver(&map);

        let ty = resolve_type_expr(&named("Color"), &var_map, &r, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::ADT(test_fqtn("Color"), vec![]));
    }

    // spec: 03-types §3.2.1 — resolve function type expression
    #[test]
    fn test_resolve_fn_type() {
        let var_map = HashMap::new();
        let map = intrinsics_map();
        let r = resolver(&map);

        let fn_texpr = TypeExpr::FnType(vec![named("Int")], Box::new(named("Bool")));
        let ty = resolve_type_expr(&fn_texpr, &var_map, &r, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::Fn(vec![Type::Int], Box::new(Type::Bool)));
    }

    // spec: 03-types §3.3 — resolve type variable to Var from var_map
    #[test]
    fn test_resolve_type_var() {
        let mut var_map = HashMap::new();
        var_map.insert(Symbol::from("a"), 42u32);
        let map: HashMap<&'static str, Entry> = HashMap::new();
        let r = resolver(&map);

        let ty = resolve_type_expr(
            &TypeExpr::TypeVar(Symbol::from("a")),
            &var_map,
            &r,
            Span::SYNTHETIC,
        )
        .unwrap();
        assert_eq!(ty, Type::Var(42));
    }

    // spec: 03-types §3.3 — unresolved type variable produces error
    #[test]
    fn test_resolve_unknown_type_var() {
        let var_map = HashMap::new();
        let map: HashMap<&'static str, Entry> = HashMap::new();
        let r = resolver(&map);

        let err = resolve_type_expr(
            &TypeExpr::TypeVar(Symbol::from("a")),
            &var_map,
            &r,
            Span::SYNTHETIC,
        )
        .unwrap_err();
        assert!(matches!(err, ResolveError::TypeNotFound { .. }));
    }

    // spec: 07-traits §7.1.1 — Self type outside trait context is error
    #[test]
    fn test_resolve_self_type_error() {
        let var_map = HashMap::new();
        let map: HashMap<&'static str, Entry> = HashMap::new();
        let r = resolver(&map);

        assert!(resolve_type_expr(&TypeExpr::SelfType, &var_map, &r, Span::SYNTHETIC).is_err());
    }

    // spec: 03-types §3.2.2 — resolve applied type :(Option Int) to ADT
    #[test]
    fn test_resolve_applied_valid() {
        let var_map = HashMap::new();
        let mut map = intrinsics_map();
        map.insert("Option", typedef_entry("Option", 1));
        let r = resolver(&map);

        let texpr = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Option")),
            vec![named("Int")],
        );
        let ty = resolve_type_expr(&texpr, &var_map, &r, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::ADT(test_fqtn("Option"), vec![Type::Int]));
    }

    // spec: 03-types §3.2.2 — applied type with wrong arity fails (both
    // over- and under-application), flexing the arity gate.
    #[test]
    fn test_resolve_applied_arity_mismatch() {
        let var_map = HashMap::new();
        let mut map = intrinsics_map();
        map.insert("Option", typedef_entry("Option", 1));
        let r = resolver(&map);

        let too_many = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Option")),
            vec![named("Int"), named("Bool")],
        );
        assert!(matches!(
            resolve_type_expr(&too_many, &var_map, &r, Span::SYNTHETIC).unwrap_err(),
            ResolveError::TypeNotFound { .. }
        ));

        let too_few = TypeExpr::Applied(TypeRef::new(None, TypeName::from("Option")), vec![]);
        assert!(matches!(
            resolve_type_expr(&too_few, &var_map, &r, Span::SYNTHETIC).unwrap_err(),
            ResolveError::TypeNotFound { .. }
        ));
    }

    // spec: 03-types §3.9.3 — applied unknown type name fails
    #[test]
    fn test_resolve_applied_unknown_type() {
        let var_map = HashMap::new();
        let map: HashMap<&'static str, Entry> = HashMap::new();
        let r = resolver(&map);

        let texpr = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Foo")),
            vec![named("Int")],
        );
        assert!(resolve_type_expr(&texpr, &var_map, &r, Span::SYNTHETIC).is_err());
    }

    // spec: 03-types §3.3 — applied type with type variable argument
    #[test]
    fn test_resolve_applied_with_type_var() {
        let mut var_map = HashMap::new();
        var_map.insert(Symbol::from("a"), 5u32);
        let mut map = intrinsics_map();
        map.insert("Option", typedef_entry("Option", 1));
        let r = resolver(&map);

        let texpr = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Option")),
            vec![TypeExpr::TypeVar(Symbol::from("a"))],
        );
        let ty = resolve_type_expr(&texpr, &var_map, &r, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::ADT(test_fqtn("Option"), vec![Type::Var(5)]));
    }

    // spec: 03-types §3.2.2 — applied type with multiple parameters validates
    // arity 2 and threads both args positionally.
    #[test]
    fn test_resolve_applied_multi_param() {
        let var_map = HashMap::new();
        let mut map = intrinsics_map();
        map.insert("Either", typedef_entry("Either", 2));
        let r = resolver(&map);

        let texpr = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Either")),
            vec![named("Int"), named("String")],
        );
        let ty = resolve_type_expr(&texpr, &var_map, &r, Span::SYNTHETIC).unwrap();
        assert_eq!(
            ty,
            Type::ADT(test_fqtn("Either"), vec![Type::Int, Type::String])
        );
    }

    // spec: 03-types §3.2.2 — a single-ctor PRODUCT type used in TYPE position
    // resolves to its ADT. Its symbol-table entry is the got-slotted ctor `Def`
    // carrying the type facet (S79 dual facet), NOT a `TypeDef`; resolution must
    // route through `type_def_view_of` so the product type answers as a type.
    #[test]
    fn test_resolve_product_ctor_as_type() {
        let var_map = HashMap::new();
        let mut map: HashMap<&'static str, Entry> = HashMap::new();
        // `(deftype Box [:Int n])` — type-name == ctor-name == "Box".
        map.insert("Box", product_ctor_entry("Box", 0));
        let r = resolver(&map);

        let ty = resolve_type_expr(&named("Box"), &var_map, &r, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::ADT(test_fqtn("Box"), vec![]));
    }

    // spec: 03-types §3.2.2 — applied form of a parametric single-ctor product
    // type resolves with arity validation, again via the ctor `Def` type facet.
    #[test]
    fn test_resolve_applied_product_ctor_as_type() {
        let var_map = HashMap::new();
        let mut map = intrinsics_map();
        // `(deftype (Wrap a) (Wrap [:a inner]))` — product, arity 1.
        map.insert("Wrap", product_ctor_entry("Wrap", 1));
        let r = resolver(&map);

        let texpr = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Wrap")),
            vec![named("Int")],
        );
        let ty = resolve_type_expr(&texpr, &var_map, &r, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::ADT(test_fqtn("Wrap"), vec![Type::Int]));

        // Wrong arity on a product type still fails the arity gate.
        let bad = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Wrap")),
            vec![named("Int"), named("Bool")],
        );
        assert!(matches!(
            resolve_type_expr(&bad, &var_map, &r, Span::SYNTHETIC).unwrap_err(),
            ResolveError::TypeNotFound { .. }
        ));
    }

    /// Build the builtin `Vec` entry as it is seeded in production
    /// (`src/bootstrap.rs`) and the test fixture (`builtins.rs`): a
    /// `primitives/Vec` `TypeDef` with EMPTY `type_params` (no declared arity),
    /// even though `Vec` is genuinely arity-1 (`(Vec a)`, spec §3.2.7).
    fn builtin_vec_entry() -> Entry {
        ModuleEntry::TypeDef {
            info: TypeDefInfo {
                name: prim_fqtn("Vec"),
                type_params: vec![],
                constructors: vec![],
            },
            visibility: Visibility::Public,
            docstring: Some("builtin vector type".to_string()),
        }
    }

    // spec: 03-types §3.11.1 / §3.2.7 — the builtin `Vec` resolves as an applied
    // type constructor `:(Vec Int)` in annotation position even though it is
    // seeded with empty `type_params`. This is the FIXME-0385 carve-out: without
    // it `(id :(Vec Int) [])` (the §3.11.1 worked-example disambiguation) is
    // unfixable ("unknown type `Vec`").
    #[test]
    fn test_resolve_applied_builtin_vec_one_arg() {
        let var_map = HashMap::new();
        let mut map = intrinsics_map();
        map.insert("Vec", builtin_vec_entry());
        let r = resolver(&map);

        let texpr = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Vec")),
            vec![named("Int")],
        );
        let ty = resolve_type_expr(&texpr, &var_map, &r, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::ADT(prim_fqtn("Vec"), vec![Type::Int]));
    }

    // spec: 03-types §3.2.7 — the builtin `Vec` carve-out still requires exactly
    // one type argument. Zero or two args is rejected (`:Vec`/`(Vec Int Bool)`).
    #[test]
    fn test_resolve_applied_builtin_vec_wrong_arity() {
        let var_map = HashMap::new();
        let mut map = intrinsics_map();
        map.insert("Vec", builtin_vec_entry());
        let r = resolver(&map);

        let too_many = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Vec")),
            vec![named("Int"), named("Bool")],
        );
        assert!(matches!(
            resolve_type_expr(&too_many, &var_map, &r, Span::SYNTHETIC).unwrap_err(),
            ResolveError::TypeNotFound { .. }
        ));

        let zero = TypeExpr::Applied(TypeRef::new(None, TypeName::from("Vec")), vec![]);
        assert!(matches!(
            resolve_type_expr(&zero, &var_map, &r, Span::SYNTHETIC).unwrap_err(),
            ResolveError::TypeNotFound { .. }
        ));
    }
}
