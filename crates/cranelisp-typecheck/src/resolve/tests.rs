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
                mode_summary: None,
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
        let mut var_map = HashMap::new();
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
                resolve_type_expr(&named(name), &mut var_map, &r, None, span).unwrap(),
                expected
            );
        }
    }

    // spec: 03-types §3.1 — intrinsic FQ identity does not leak into the bare
    // resolved Type (regression: a prior `KnownTypeKind::Intrinsic.fqtn` field
    // was dead — the resolved value is the bare variant, never an ADT wrap).
    #[test]
    fn test_intrinsic_resolves_to_bare_not_adt() {
        let mut var_map = HashMap::new();
        let mut map = intrinsics_map();
        // Even with an FQ home of `primitives`, resolution yields `Type::Int`.
        map.insert("Int", intrinsic_entry(Type::Int));
        let _ = prim_fqtn("Int"); // FQ identity is irrelevant to the result.
        let r = resolver(&map);

        let ty = resolve_type_expr(&named("Int"), &mut var_map, &r, None, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::Int);
        assert!(!matches!(ty, Type::ADT(..)));
    }

    // spec: 03-types §3.9.3 — unknown type name produces error
    #[test]
    fn test_resolve_unknown_type() {
        let mut var_map = HashMap::new();
        let map: HashMap<&'static str, Entry> = HashMap::new();
        let r = resolver(&map);

        let err = resolve_type_expr(&named("Foo"), &mut var_map, &r, None, Span::SYNTHETIC).unwrap_err();
        assert!(matches!(err, ResolveError::TypeNotFound { .. }));
    }

    // spec: 03-types §3.2.2 — resolve user-defined ADT name to ADT type
    #[test]
    fn test_resolve_user_defined_adt() {
        let mut var_map = HashMap::new();
        let mut map: HashMap<&'static str, Entry> = HashMap::new();
        map.insert("Color", typedef_entry("Color", 0));
        let r = resolver(&map);

        let ty = resolve_type_expr(&named("Color"), &mut var_map, &r, None, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::ADT(test_fqtn("Color"), vec![]));
    }

    // spec: 03-types §3.2.1 — resolve function type expression
    #[test]
    fn test_resolve_fn_type() {
        let mut var_map = HashMap::new();
        let map = intrinsics_map();
        let r = resolver(&map);

        let fn_texpr = TypeExpr::FnType(vec![named("Int")], Box::new(named("Bool")));
        let ty = resolve_type_expr(&fn_texpr, &mut var_map, &r, None, Span::SYNTHETIC).unwrap();
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
            &mut var_map,
            &r,
            None,
            Span::SYNTHETIC,
        )
        .unwrap();
        assert_eq!(ty, Type::Var(42));
    }

    // spec: 03-types §3.3 — unresolved type variable produces error
    #[test]
    fn test_resolve_unknown_type_var() {
        let mut var_map = HashMap::new();
        let map: HashMap<&'static str, Entry> = HashMap::new();
        let r = resolver(&map);

        let err = resolve_type_expr(
            &TypeExpr::TypeVar(Symbol::from("a")),
            &mut var_map,
            &r,
            None,
            Span::SYNTHETIC,
        )
        .unwrap_err();
        assert!(matches!(err, ResolveError::TypeNotFound { .. }));
    }

    // spec: 07-traits §7.1.1 — Self type outside trait context is error
    #[test]
    fn test_resolve_self_type_error() {
        let mut var_map = HashMap::new();
        let map: HashMap<&'static str, Entry> = HashMap::new();
        let r = resolver(&map);

        assert!(resolve_type_expr(&TypeExpr::SelfType, &mut var_map, &r, None, Span::SYNTHETIC).is_err());
    }

    // spec: 03-types §3.2.2 — resolve applied type :(Option Int) to ADT
    #[test]
    fn test_resolve_applied_valid() {
        let mut var_map = HashMap::new();
        let mut map = intrinsics_map();
        map.insert("Option", typedef_entry("Option", 1));
        let r = resolver(&map);

        let texpr = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Option")),
            vec![named("Int")],
        );
        let ty = resolve_type_expr(&texpr, &mut var_map, &r, None, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::ADT(test_fqtn("Option"), vec![Type::Int]));
    }

    // spec: 03-types §3.2.2 — applied type with wrong arity fails (both
    // over- and under-application), flexing the arity gate.
    #[test]
    fn test_resolve_applied_arity_mismatch() {
        let mut var_map = HashMap::new();
        let mut map = intrinsics_map();
        map.insert("Option", typedef_entry("Option", 1));
        let r = resolver(&map);

        let too_many = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Option")),
            vec![named("Int"), named("Bool")],
        );
        assert!(matches!(
            resolve_type_expr(&too_many, &mut var_map, &r, None, Span::SYNTHETIC).unwrap_err(),
            ResolveError::TypeNotFound { .. }
        ));

        let too_few = TypeExpr::Applied(TypeRef::new(None, TypeName::from("Option")), vec![]);
        assert!(matches!(
            resolve_type_expr(&too_few, &mut var_map, &r, None, Span::SYNTHETIC).unwrap_err(),
            ResolveError::TypeNotFound { .. }
        ));
    }

    // spec: 03-types §3.9.3 — applied unknown type name fails
    #[test]
    fn test_resolve_applied_unknown_type() {
        let mut var_map = HashMap::new();
        let map: HashMap<&'static str, Entry> = HashMap::new();
        let r = resolver(&map);

        let texpr = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Foo")),
            vec![named("Int")],
        );
        assert!(resolve_type_expr(&texpr, &mut var_map, &r, None, Span::SYNTHETIC).is_err());
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
        let ty = resolve_type_expr(&texpr, &mut var_map, &r, None, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::ADT(test_fqtn("Option"), vec![Type::Var(5)]));
    }

    // spec: 03-types §3.2.2 — applied type with multiple parameters validates
    // arity 2 and threads both args positionally.
    #[test]
    fn test_resolve_applied_multi_param() {
        let mut var_map = HashMap::new();
        let mut map = intrinsics_map();
        map.insert("Either", typedef_entry("Either", 2));
        let r = resolver(&map);

        let texpr = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Either")),
            vec![named("Int"), named("String")],
        );
        let ty = resolve_type_expr(&texpr, &mut var_map, &r, None, Span::SYNTHETIC).unwrap();
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
        let mut var_map = HashMap::new();
        let mut map: HashMap<&'static str, Entry> = HashMap::new();
        // `(deftype Box [:Int n])` — type-name == ctor-name == "Box".
        map.insert("Box", product_ctor_entry("Box", 0));
        let r = resolver(&map);

        let ty = resolve_type_expr(&named("Box"), &mut var_map, &r, None, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::ADT(test_fqtn("Box"), vec![]));
    }

    // spec: 03-types §3.2.2 — applied form of a parametric single-ctor product
    // type resolves with arity validation, again via the ctor `Def` type facet.
    #[test]
    fn test_resolve_applied_product_ctor_as_type() {
        let mut var_map = HashMap::new();
        let mut map = intrinsics_map();
        // `(deftype (Wrap a) (Wrap [:a inner]))` — product, arity 1.
        map.insert("Wrap", product_ctor_entry("Wrap", 1));
        let r = resolver(&map);

        let texpr = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Wrap")),
            vec![named("Int")],
        );
        let ty = resolve_type_expr(&texpr, &mut var_map, &r, None, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::ADT(test_fqtn("Wrap"), vec![Type::Int]));

        // Wrong arity on a product type still fails the arity gate.
        let bad = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Wrap")),
            vec![named("Int"), named("Bool")],
        );
        assert!(matches!(
            resolve_type_expr(&bad, &mut var_map, &r, None, Span::SYNTHETIC).unwrap_err(),
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
        let mut var_map = HashMap::new();
        let mut map = intrinsics_map();
        map.insert("Vec", builtin_vec_entry());
        let r = resolver(&map);

        let texpr = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Vec")),
            vec![named("Int")],
        );
        let ty = resolve_type_expr(&texpr, &mut var_map, &r, None, Span::SYNTHETIC).unwrap();
        assert_eq!(ty, Type::ADT(prim_fqtn("Vec"), vec![Type::Int]));
    }

    // spec: 03-types §3.2.7 — the builtin `Vec` carve-out still requires exactly
    // one type argument. Zero or two args is rejected (`:Vec`/`(Vec Int Bool)`).
    #[test]
    fn test_resolve_applied_builtin_vec_wrong_arity() {
        let mut var_map = HashMap::new();
        let mut map = intrinsics_map();
        map.insert("Vec", builtin_vec_entry());
        let r = resolver(&map);

        let too_many = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Vec")),
            vec![named("Int"), named("Bool")],
        );
        assert!(matches!(
            resolve_type_expr(&too_many, &mut var_map, &r, None, Span::SYNTHETIC).unwrap_err(),
            ResolveError::TypeNotFound { .. }
        ));

        let zero = TypeExpr::Applied(TypeRef::new(None, TypeName::from("Vec")), vec![]);
        assert!(matches!(
            resolve_type_expr(&zero, &mut var_map, &r, None, Span::SYNTHETIC).unwrap_err(),
            ResolveError::TypeNotFound { .. }
        ));
    }

    // --- S109 §L.1 unit tier: written free type-var minting (spec §3.3) ---
    //
    // These pin the RESOLVE-layer mechanism: on a `var_map` miss in annotation
    // context the resolver mints a fresh `Type::Var` and records it for
    // co-reference. Whether that var is RIGID or flexible is the CALLER's
    // decision (the checker; see the program-seam u1/u7 and the unify-seam u6
    // cells) — the resolver only mints and records. A qualified name (`user/int`,
    // contains `/`) never mints (u8).

    /// A counter-backed fresh-`TypeId` allocator, standing in for the checker's
    /// `fresh_var_id`. IDs start high (500) to keep them distinct from the
    /// hand-picked ids used elsewhere in this module.
    fn minter(start: u32) -> impl Fn() -> TypeId {
        let next = std::cell::Cell::new(start);
        move || {
            let id = next.get();
            next.set(id + 1);
            id
        }
    }

    // spec: 03-types §3.3 [S109] (u1 resolve-half) — a free lowercase type var
    // that MISSES `var_map` mints a fresh variable when a `mint_free_var`
    // allocator is supplied (annotation context), instead of erroring, and the
    // minted id is recorded in `var_map`. (RIGIDITY of that var is asserted by
    // the caller — see the program-seam `u1_written_param_var_is_rigid_*` cell.)
    #[test]
    fn u1_free_var_mints_fresh_when_allocator_present() {
        let mut var_map = HashMap::new();
        let map: HashMap<&'static str, Entry> = HashMap::new();
        let r = resolver(&map);
        let mint = minter(500);

        let ty = resolve_type_expr(
            &TypeExpr::TypeVar(Symbol::from("a")),
            &mut var_map,
            &r,
            Some(&mint),
            Span::SYNTHETIC,
        )
        .unwrap();
        assert_eq!(ty, Type::Var(500));
        // The minted var is recorded for later co-reference.
        assert_eq!(var_map.get(&Symbol::from("a")).copied(), Some(500));
    }

    // spec: 03-types §3.3 [S109] (u2) — within ONE resolution scope (one shared
    // `var_map`), the SAME identifier resolves to the SAME var (so `[:a x :a y]`
    // unifies x and y), while a DISTINCT identifier gets a fresh var.
    #[test]
    fn u2_same_ident_same_var_distinct_ident_fresh() {
        let mut var_map = HashMap::new();
        let map: HashMap<&'static str, Entry> = HashMap::new();
        let r = resolver(&map);
        let mint = minter(500);

        let a1 = resolve_type_expr(
            &TypeExpr::TypeVar(Symbol::from("a")),
            &mut var_map,
            &r,
            Some(&mint),
            Span::SYNTHETIC,
        )
        .unwrap();
        let a2 = resolve_type_expr(
            &TypeExpr::TypeVar(Symbol::from("a")),
            &mut var_map,
            &r,
            Some(&mint),
            Span::SYNTHETIC,
        )
        .unwrap();
        let b = resolve_type_expr(
            &TypeExpr::TypeVar(Symbol::from("b")),
            &mut var_map,
            &r,
            Some(&mint),
            Span::SYNTHETIC,
        )
        .unwrap();

        assert_eq!(a1, Type::Var(500));
        assert_eq!(a2, Type::Var(500), "repeated `a` must co-refer");
        assert_eq!(b, Type::Var(501), "`b` is a distinct, fresh var");
    }

    // spec: 03-types §3.3 [S109] × 05-definitions §5.1.2 (u3) — the var scope is
    // the `var_map` INSTANCE. Two independent maps (as a fresh per-arity-clause
    // signature receives — each clause routes through its own
    // `register_defn_signature` call, which builds a fresh map) mint INDEPENDENT
    // vars for the same identifier: `:a` in clause 1 is unrelated to `:a` in
    // clause 2.
    #[test]
    fn u3_fresh_scope_per_map_instance() {
        let map: HashMap<&'static str, Entry> = HashMap::new();
        let r = resolver(&map);
        let mint = minter(500);

        let mut clause1 = HashMap::new();
        let c1 = resolve_type_expr(
            &TypeExpr::TypeVar(Symbol::from("a")),
            &mut clause1,
            &r,
            Some(&mint),
            Span::SYNTHETIC,
        )
        .unwrap();

        let mut clause2 = HashMap::new();
        let c2 = resolve_type_expr(
            &TypeExpr::TypeVar(Symbol::from("a")),
            &mut clause2,
            &r,
            Some(&mint),
            Span::SYNTHETIC,
        )
        .unwrap();

        assert_eq!(c1, Type::Var(500));
        assert_eq!(
            c2,
            Type::Var(501),
            "a fresh var scope mints an independent var for `a`"
        );
    }

    // spec: 03-types §3.3 [S109] / §3.9.3 (u4) — case discrimination. Minting is
    // keyed on `TypeExpr::TypeVar` (a lowercase-leading identifier). An UNKNOWN
    // uppercase-shaped name arrives as `TypeExpr::Named` and STILL errors
    // `TypeNotFound` even when a `mint_free_var` allocator is present — the fix
    // must not swallow genuine unknown-type errors (the over-broadening guard).
    #[test]
    fn u4_case_discrimination_lowercase_mints_uppercase_errors() {
        let mut var_map = HashMap::new();
        let map: HashMap<&'static str, Entry> = HashMap::new();
        let r = resolver(&map);
        let mint = minter(500);

        // Lowercase `TypeVar` mints.
        let mints = resolve_type_expr(
            &TypeExpr::TypeVar(Symbol::from("a")),
            &mut var_map,
            &r,
            Some(&mint),
            Span::SYNTHETIC,
        );
        assert_eq!(mints.unwrap(), Type::Var(500));

        // Unknown uppercase `Named` still errors, mint allocator notwithstanding.
        let err = resolve_type_expr(
            &named("Foo"),
            &mut var_map,
            &r,
            Some(&mint),
            Span::SYNTHETIC,
        )
        .unwrap_err();
        assert!(matches!(err, ResolveError::TypeNotFound { .. }));

        // …including nested inside an applied annotation `:(Option Foo)`.
        let mut m2 = intrinsics_map();
        m2.insert("Option", typedef_entry("Option", 1));
        let r2 = resolver(&m2);
        let nested = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Option")),
            vec![named("Foo")],
        );
        assert!(matches!(
            resolve_type_expr(&nested, &mut var_map, &r2, Some(&mint), Span::SYNTHETIC)
                .unwrap_err(),
            ResolveError::TypeNotFound { .. }
        ));
    }

    // spec: 03-types §3.3 [S109] — a free var nested in an applied annotation
    // `:(Pair a a)` mints (the recursion threads the allocator + shared map), so
    // both `a` positions co-refer. This is the nested-position facet of the
    // single-seam fix (FV-4/FV-5).
    #[test]
    fn nested_applied_annotation_free_var_mints_and_corefers() {
        let mut var_map = HashMap::new();
        let mut map = intrinsics_map();
        map.insert("Pair", typedef_entry("Pair", 2));
        let r = resolver(&map);
        let mint = minter(500);

        let texpr = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Pair")),
            vec![
                TypeExpr::TypeVar(Symbol::from("a")),
                TypeExpr::TypeVar(Symbol::from("a")),
            ],
        );
        let ty = resolve_type_expr(&texpr, &mut var_map, &r, Some(&mint), Span::SYNTHETIC).unwrap();
        assert_eq!(
            ty,
            Type::ADT(test_fqtn("Pair"), vec![Type::Var(500), Type::Var(500)]),
            "both `a` positions co-refer to one minted var"
        );
    }

    // spec: 03-types §3.3 [S109] / §3.9.3 (u8) — a QUALIFIED lowercase name
    // (`user/int`, contains `/`) is a module-qualified reference, NEVER a type
    // variable (a var is a BARE lowercase identifier, §3.3). It MUST NOT mint
    // even when a `mint_free_var` allocator is present — it falls to the
    // `TypeNotFound` error naming the qualified string (F2/0589). Together with
    // u4 (uppercase) this fences the minting rule to exactly bare-lowercase.
    #[test]
    fn u8_qualified_lowercase_name_does_not_mint() {
        let mut var_map = HashMap::new();
        let map: HashMap<&'static str, Entry> = HashMap::new();
        let r = resolver(&map);
        let mint = minter(500);

        // `:user/int` arrives (frontend-mis-tagged) as a `TypeVar` carrying the
        // full qualified string. With a mint allocator present it STILL errors.
        let err = resolve_type_expr(
            &TypeExpr::TypeVar(Symbol::from("user/int")),
            &mut var_map,
            &r,
            Some(&mint),
            Span::SYNTHETIC,
        )
        .unwrap_err();
        assert!(matches!(err, ResolveError::TypeNotFound { .. }));
        // It was NOT minted into the scope.
        assert!(var_map.is_empty(), "a qualified name must not be recorded as a var");

        // A BARE lowercase sibling in the same call DOES mint (control).
        let ok = resolve_type_expr(
            &TypeExpr::TypeVar(Symbol::from("a")),
            &mut var_map,
            &r,
            Some(&mint),
            Span::SYNTHETIC,
        )
        .unwrap();
        assert_eq!(ok, Type::Var(500));
    }
