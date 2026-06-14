//! ADT type definitions: registration, constructor lookup, exhaustiveness checking.
//!
//! Handles both enum-only ADTs (nullary constructors, Ring 0) and parameterized
//! ADTs with data constructor fields (Ring 1). Polymorphic types produce
//! polymorphic constructor schemes via `build_constructor_scheme`.
//!
//! Type definitions are stored on per-module SymbolTables as `ModuleEntry::TypeDef`
//! entries. The old `TypeDefRegistry` global cache has been eliminated — all lookups
//! go through the module system.

use std::collections::HashMap;

use cranelisp_types::{ErrorLocation,
    ConstructorDef, CranelispError, DefKind, DefnVariant, Expr, FQTypeName, FieldInfo,
    ModuleEntry, ModuleFullPath, Scheme, Span, Symbol, Type, TypeDefInfo, TypeId, TypeName,
    Visibility,
};

use crate::checker::{CheckState, TypeCheckEnv};

/// Local typecheck-internal intermediate: a constructor with its resolved field
/// types, used during `register_type_def` to build per-constructor `Def`
/// entries. Not part of the cranelisp-types surface — the canonical store is
/// the per-ctor `ModuleEntry::Def { kind: DefKind::Constructor, .. }` entry.
#[derive(Clone)]
pub(crate) struct CtorBuild {
    pub name: Symbol,
    pub tag: usize,
    pub fields: Vec<FieldInfo>,
    pub docstring: Option<String>,
    pub internal: bool,
}

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Register a type definition from a TopLevel::TypeDef.
    ///
    /// Handles both nullary enums (Ring 0) and parameterized ADTs with data
    /// constructor fields (Ring 1). Allocates fresh type vars for type parameters,
    /// resolves field types, and produces polymorphic constructor schemes.
    ///
    /// **FQTypeName exception 2 (receiver-pinned).** `name: &TypeName` is
    /// correct here per `design/arch/facades/types.md` §"FQTypeName migration
    /// plan (Sprint 67)" §"typecheck" row 269 — the writer's module context
    /// is supplied by `state.current_module`; the `FQTypeName` is constructed
    /// inside this function at line 42 (`FQTypeName::new(state.current_module
    /// .clone(), name.clone())`). The bare-name parameter encodes the
    /// post-resolution lift point itself.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn register_type_def(
        &self,
        state: &mut CheckState,
        name: &TypeName,
        docstring: &Option<String>,
        type_params: &[Symbol],
        constructors: &[ConstructorDef],
        visibility: Visibility,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Allocate fresh type vars for type parameters
        let (var_map, type_var_ids) = self.allocate_type_params(type_params);

        // Build the fully-qualified type name
        let fqtn = FQTypeName::new(state.current_module.clone(), name.clone());

        // Pre-seed the type name in the symbol table so recursive constructor
        // fields (e.g., `:(List a) tail` inside a `(deftype (List a) ...)`) can
        // resolve the type during `build_constructor_infos`. The full TypeDefInfo
        // replaces this placeholder below.
        self.current_symbol_table_mut(state).insert(
            Symbol::from(name.as_ref()),
            ModuleEntry::TypeDef {
                info: TypeDefInfo {
                    name: fqtn.clone(),
                    type_params: type_params.to_vec(),
                    constructors: vec![],
                },
                visibility,
                docstring: None,
            },
        );

        // Build constructor infos with resolved field types.
        // If resolution fails, remove the pre-seeded placeholder so it
        // doesn't pollute known_types for subsequent definitions.
        let ctor_infos = match self.build_constructor_infos(
            state, name, constructors, &var_map, span,
        ) {
            Ok(infos) => infos,
            Err(e) => {
                self.current_symbol_table_mut(state)
                    .symbols.remove(&Symbol::from(name.as_ref()));
                return Err(e);
            }
        };

        self.register_type_def_with_ctor_infos(
            state,
            name,
            docstring,
            type_params,
            &type_var_ids,
            ctor_infos,
            visibility,
        );

        Ok(())
    }

    /// Register a type definition using pre-resolved constructor builds.
    ///
    /// This is the synthetic-bootstrap path used when a type's constructor
    /// fields reference types in foreign synthetic modules (e.g. `Trace` in
    /// `primitives` referencing `macros/SList`). Per Principle 17, synthetic
    /// modules have empty imports, so short-name resolution via TypeExpr
    /// cannot reach foreign-module type names — the caller must construct
    /// FQ field types directly using `*_fqtn(...)` helpers and supply them
    /// here as already-built `CtorBuild`s.
    ///
    /// Caller's responsibility: `type_var_ids` MUST correspond positionally
    /// to `type_params` (i.e. the type vars that should be quantified in
    /// each constructor's scheme).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn register_type_def_with_ctor_infos(
        &self,
        state: &mut CheckState,
        name: &TypeName,
        docstring: &Option<String>,
        type_params: &[Symbol],
        type_var_ids: &[TypeId],
        ctor_infos: Vec<CtorBuild>,
        visibility: Visibility,
    ) {
        let fqtn = FQTypeName::new(state.current_module.clone(), name.clone());
        let type_args: Vec<Type> = type_var_ids.iter().map(|&id| Type::Var(id)).collect();
        let adt_type = Type::ADT(fqtn.clone(), type_args);

        // Capture ctor names for the TypeDefInfo before consuming ctor_infos
        // during per-ctor Def registration.
        let ctor_names: Vec<Symbol> =
            ctor_infos.iter().map(|c| c.name.clone()).collect();

        let type_def_info = TypeDefInfo {
            name: fqtn.clone(),
            type_params: type_params.to_vec(),
            constructors: ctor_names,
        };

        // **Product/sum split (S79 Option 3a, FIXME 0319).** A single-ctor
        // **product** type has type-name == ctor-name, so the type and its
        // constructor collide on one symbol-table key (`"Rectangle"`). Rather
        // than overwrite the got-slotted ctor `Def` with a `ModuleEntry::TypeDef`
        // (the prior model — which dropped the ctor's `param_names` field names
        // and broke product-ctor-as-first-class-value), the surviving entry is
        // the **got-slotted ctor `Def`** carrying a **type facet**
        // (`DefKind::Constructor { type_def: Some(..) }`) so it ALSO answers as
        // its own type. A sum/enum type registers a separate `ModuleEntry::TypeDef`
        // under its distinct key and its ctors carry `type_def: None`.
        let is_product = ctor_infos.len() == 1
            && ctor_infos[0].name.as_ref() == name.as_ref();
        let product_type_def: Option<TypeDefInfo> =
            is_product.then(|| type_def_info.clone());

        if !is_product {
            // Sum/enum: pre-seed the type entry (the `register_type_def` path
            // pre-seeds; direct callers may not have, so do it here
            // defensively) so recursive ctor-field resolution can see the type
            // while constructors register.
            self.current_symbol_table_mut(state).insert(
                Symbol::from(name.as_ref()),
                ModuleEntry::TypeDef {
                    info: TypeDefInfo {
                        name: fqtn.clone(),
                        type_params: type_params.to_vec(),
                        constructors: vec![],
                    },
                    visibility,
                    docstring: None,
                },
            );
        }

        // Register each constructor as a ModuleEntry::Def with
        // kind: DefKind::Constructor { type_name, tag, field_count, internal,
        // type_def } and a synthesised DefnVariant body wrapping Expr::ConstrADT.
        // The product ctor receives the type facet (`type_def: Some(..)`); every
        // sum/enum ctor receives `type_def: None`.
        self.register_constructors(
            state,
            &fqtn,
            &ctor_infos,
            &adt_type,
            type_var_ids,
            visibility,
            product_type_def.as_ref(),
            docstring,
        );

        // Register the sum/enum type's separate `TypeDef` entry. The product
        // case has NO `TypeDef` entry — its type facet lives on the ctor `Def`
        // registered just above, under the shared `"Rectangle"` key.
        if !is_product {
            self.current_symbol_table_mut(state).insert(
                Symbol::from(name.as_ref()),
                ModuleEntry::TypeDef {
                    info: type_def_info,
                    visibility,
                    docstring: docstring.clone(),
                },
            );
        }
    }

    /// Allocate fresh type variables for type parameters.
    /// Returns a var_map (param name -> TypeId) and the ordered list of TypeIds.
    fn allocate_type_params(
        &self,
        type_params: &[Symbol],
    ) -> (HashMap<Symbol, TypeId>, Vec<TypeId>) {
        let mut var_map = HashMap::new();
        let mut type_var_ids = Vec::new();
        for param in type_params {
            let (_, id) = self.fresh_var_id();
            var_map.insert(param.clone(), id);
            type_var_ids.push(id);
        }
        (var_map, type_var_ids)
    }

    /// Build CtorBuild entries with resolved field types.
    fn build_constructor_infos(
        &self,
        state: &CheckState,
        type_name: &TypeName,
        constructors: &[ConstructorDef],
        var_map: &HashMap<Symbol, TypeId>,
        span: Span,
    ) -> Result<Vec<CtorBuild>, CranelispError> {
        constructors
            .iter()
            .enumerate()
            .map(|(tag, ctor)| {
                self.build_single_ctor_info(
                    state, type_name, ctor, tag, var_map, span,
                )
            })
            .collect()
    }

    /// Build a single CtorBuild with resolved field types.
    fn build_single_ctor_info(
        &self,
        state: &CheckState,
        _type_name: &TypeName,
        ctor: &ConstructorDef,
        tag: usize,
        var_map: &HashMap<Symbol, TypeId>,
        span: Span,
    ) -> Result<CtorBuild, CranelispError> {
        let fields: Vec<FieldInfo> = ctor
            .fields
            .iter()
            .map(|field| {
                let ty = self.resolve_type_expr_in_module(
                    &field.type_expr, var_map, &state.current_module, span,
                )?;
                Ok(FieldInfo {
                    name: field.name.clone(),
                    ty,
                })
            })
            .collect::<Result<Vec<_>, CranelispError>>()?;

        Ok(CtorBuild {
            name: ctor.name.clone(),
            tag,
            fields,
            docstring: ctor.docstring.clone(),
            internal: false,
        })
    }

    /// Register constructors in the current module's symbol table.
    ///
    /// Each constructor becomes a `ModuleEntry::Def` with
    /// `kind: DefKind::Constructor { type_name, tag, field_count, internal,
    /// type_def }` and a synthesised `DefnVariant` body whose body expression is
    /// `Expr::ConstrADT { type_name, tag, fields, span }` (per S69 Submission 35
    /// and `DefKind::Constructor` rustdoc in `cranelisp_types::module`).
    ///
    /// **Product type facet (S79 Option 3a, FIXME 0319).** When
    /// `product_type_def` is `Some`, this registration is for a single-ctor
    /// **product** type (type-name == ctor-name); the lone ctor's `Def` carries
    /// `type_def: Some(..)` so the shared `"Rectangle"` entry answers both as a
    /// got-slotted ctor `Def` AND as its own type. Sum/enum ctors pass `None`
    /// and carry `type_def: None`. `type_docstring` is the deftype-level
    /// docstring, applied to the product ctor's `Def` when the ctor itself has
    /// none (the product `Def` has no separate `TypeDef` entry to hold it).
    #[allow(clippy::too_many_arguments)]
    fn register_constructors(
        &self,
        state: &mut CheckState,
        fqtn: &FQTypeName,
        ctor_builds: &[CtorBuild],
        adt_type: &Type,
        type_var_ids: &[TypeId],
        visibility: Visibility,
        product_type_def: Option<&TypeDefInfo>,
        type_docstring: &Option<String>,
    ) {
        for ctor in ctor_builds {
            // The product type facet (if any) attaches to the ctor whose name
            // matches the type name — for a product that is the single ctor.
            let ctor_type_def: Option<Box<TypeDefInfo>> = product_type_def
                .filter(|td| td.name.name.as_ref() == ctor.name.as_ref())
                .map(|td| Box::new(td.clone()));
            let ctor_scheme = build_constructor_scheme(
                ctor, adt_type, type_var_ids,
            );
            let param_names: Vec<Symbol> =
                ctor.fields.iter().map(|f| f.name.clone()).collect();
            // Synthesise a DefnVariant body whose body expression is
            // Expr::ConstrADT. Per `DefKind::Constructor` rustdoc — the
            // backend lowers `Expr::ConstrADT` directly; the ctor's metadata
            // (type_name, tag, field_count) lives on `DefKind::Constructor`.
            let body_span = Span::SYNTHETIC;
            let synth_params: Vec<(Symbol, Option<cranelisp_types::TypeExpr>)> =
                param_names.iter().cloned().map(|n| (n, None)).collect();
            let synth_body = Expr::ConstrADT {
                type_name: fqtn.clone(),
                tag: ctor.tag,
                fields: param_names
                    .iter()
                    .map(|n| Expr::var(n.clone(), body_span))
                    .collect(),
                span: body_span,
                inferred_type: None,
            };
            let ast = DefnVariant {
                params: synth_params,
                body: synth_body,
                span: body_span,
            };

            // 0249-a: constructors are GOT-slotted callable values, exactly
            // like user fns (program.rs user-fn slotting). Without a slot, a
            // constructor reached *as a value* (`(map Some xs)`, `(let [f None]
            // f)`) has no address to load — BC §3's minimal-JIT-setup boundary
            // assumes the slot exists on the entry before int enumerates the
            // name into the compile batch (0249-b). Allocated at registration
            // (Decision 0048 primitives-got-slotting precedent). Nullary
            // constructors are slotted too — addressability does not depend on
            // arity. The slot is allocated before the entry is built; the
            // `&mut` guard is dropped before the later `.insert` re-acquires it.
            let slot = self.current_symbol_table_mut(state).allocate_got_slot();
            let is_product_ctor = ctor_type_def.is_some();
            let mut builder = ModuleEntry::def(
                ctor_scheme,
                DefKind::Constructor {
                    type_name: fqtn.clone(),
                    tag: ctor.tag,
                    field_count: ctor.fields.len(),
                    internal: ctor.internal,
                    type_def: ctor_type_def,
                },
            )
            .visibility(visibility)
            .param_names(param_names)
            .ast(ast)
            .got_slot(slot);
            // Ctor docstring wins; for the product ctor (which has no separate
            // `TypeDef` entry) fall back to the deftype-level docstring.
            let doc = ctor.docstring.clone().or_else(|| {
                if is_product_ctor { type_docstring.clone() } else { None }
            });
            if let Some(doc) = doc {
                builder = builder.docstring(doc);
            }
            self.current_symbol_table_mut(state).insert(ctor.name.clone(), builder.build());
        }
    }

}

/// Build a type scheme for a constructor.
///
/// Nullary constructors: `forall [vars]. ADT_Type`
/// Data constructors:    `forall [vars]. (Fn [field_types] ADT_Type)`
///
/// If there are no type parameters (vars is empty), the scheme is monomorphic.
fn build_constructor_scheme(
    ctor: &CtorBuild,
    adt_type: &Type,
    type_var_ids: &[TypeId],
) -> Scheme {
    let type_vars: Vec<TypeId> = type_var_ids.to_vec();

    let ty = if ctor.fields.is_empty() {
        // Nullary constructor: just the ADT type
        adt_type.clone()
    } else {
        // Data constructor: Fn([field types...], ADT type)
        let param_types: Vec<Type> = ctor
            .fields
            .iter()
            .map(|f| f.ty.clone())
            .collect();
        Type::Fn(param_types, Box::new(adt_type.clone()))
    };

    Scheme {
        type_vars,
        constraints: HashMap::new(),
        ty,
    }
}

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Check exhaustiveness of match arms against an ADT type.
    ///
    /// Returns Ok(()) if the match is exhaustive, Err with details otherwise.
    /// A match is exhaustive if:
    /// 1. All constructors of the ADT are covered, OR
    /// 2. A wildcard or variable pattern is present.
    #[allow(dead_code)] // default-rooted accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn check_exhaustiveness(
        &self,
        type_name: &TypeName,
        covered_ctors: &[Symbol],
        has_wildcard: bool,
        span: Span,
    ) -> Result<(), CranelispError> {
        self.check_exhaustiveness_in_module(
            &cranelisp_types::FQTypeName::new(ModuleFullPath::from("user"), type_name.clone()),
            covered_ctors,
            has_wildcard,
            span,
        )
    }

    /// Module-rooted variant of [`Self::check_exhaustiveness`].
    ///
    /// **FQTypeName migration (Sprint 67 Wave 3 — FIXME 0151).** Takes
    /// `&FQTypeName` per `design/arch/facades/types.md` §"FQTypeName migration
    /// plan (Sprint 67)" §"typecheck" — match-arm checks are post-resolution,
    /// so the type identifier carries its module context binding.
    pub(crate) fn check_exhaustiveness_in_module(
        &self,
        fq_type_name: &cranelisp_types::FQTypeName,
        covered_ctors: &[Symbol],
        has_wildcard: bool,
        span: Span,
    ) -> Result<(), CranelispError> {
        if has_wildcard {
            return Ok(());
        }

        let type_def = self.lookup_type_def_in_module(&fq_type_name.module, &fq_type_name.name).ok_or_else(|| {
            CranelispError::TypeError {
                message: format!("unknown type in match: {}", fq_type_name.name),
                location: ErrorLocation::from_span(span),
            }
        })?;

        // Exclude internal constructors from exhaustiveness — user code cannot
        // and need not cover them (design/typecheck/io-types.md §1). Per-ctor
        // `internal` lives on `DefKind::Constructor.internal`; resolve each
        // name to its Def in the type's defining module.
        let ctor_internal_flags: Vec<(Symbol, bool)> = type_def
            .constructors
            .iter()
            .map(|ctor_sym| {
                let internal = self
                    .probe_module_entry_owned(&fq_type_name.module, ctor_sym.as_ref())
                    .and_then(|e| match e {
                        ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                            DefKind::Constructor { internal, .. } => Some(*internal),
                            _ => None,
                        },
                        _ => None,
                    })
                    .unwrap_or(false);
                (ctor_sym.clone(), internal)
            })
            .collect();
        let all_ctors: std::collections::HashSet<String> = ctor_internal_flags
            .iter()
            .filter(|(_, internal)| !*internal)
            .map(|(name, _)| name.as_ref().to_string())
            .collect();

        // Strip optional module prefix from covered constructor names so FQ
        // pattern names (`macros/SCons`) compare equal to type_def's bare
        // constructor names (`SCons`). FQ constructor references are valid
        // under Principle 17 cross-module navigation.
        let covered: std::collections::HashSet<String> = covered_ctors
            .iter()
            .map(|c| {
                let s = c.as_ref();
                s.rsplit('/').next().unwrap_or(s).to_string()
            })
            .collect();

        let missing: Vec<String> = all_ctors.difference(&covered).cloned().collect();

        if missing.is_empty() {
            Ok(())
        } else {
            let mut missing_sorted = missing;
            missing_sorted.sort();
            Err(CranelispError::TypeError {
                message: format!(
                    "non-exhaustive match on {}: missing constructor(s) {}",
                    fq_type_name.name,
                    missing_sorted.join(", ")
                ),
                location: ErrorLocation::from_span(span),
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtins::FixtureBuilder;
    use crate::checker::TestFixture;
    use cranelisp_types::{ConstructorDef, ModuleFullPath};

    /// Minimal fixture for the ADT-registration tests (FIXME 0243 narrowing).
    ///
    /// These tests register their OWN ADTs via `register_type_def_self` and,
    /// where a constructor field is a builtin scalar (`:Int`/`:Bool`/…), seed
    /// the corresponding `primitives` import edge into the user module inline
    /// (see `test_register_product_type_with_fields`). None of them consult the
    /// heavy `full()` world (special forms, seeded primitives, the `macros`
    /// module, the IO ADT). An empty builder is the minimal starting position;
    /// `user` is the current module exactly as under `TestFixture::new()`.
    fn tf() -> TestFixture {
        TestFixture::with_content(FixtureBuilder::new())
    }

    /// Minimal fixture for the internal-constructor tests (FIXME 0243
    /// narrowing). These consult the seeded `IO` ADT in `primitives` (whose
    /// `Bind` constructor carries `internal: true`); `with_io()` seeds it and
    /// requires `with_builtin_type_names()` first (bootstrap order — IO's field
    /// types reference builtin scalars). Nothing heavier (special forms, the
    /// Ring 0/1/3 primitive `Def`s, the `macros` module) is consulted.
    fn tf_io() -> TestFixture {
        TestFixture::with_content(
            FixtureBuilder::new().with_builtin_type_names().with_io(),
        )
    }

    /// Test helper: create an FQTypeName in the "user" module (default current
    /// module for both `TestFixture::new()` and the narrowed `tf()`).
    fn user_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("user"), TypeName::from(name))
    }

    fn make_ctor(name: &str) -> ConstructorDef {
        ConstructorDef {
            name: Symbol::from(name),
            docstring: None,
            fields: vec![],
            span: Span::SYNTHETIC,
        }
    }

    // spec: 05-definitions §5.2.3 — enum type registers constructors in symbol table
    #[test]
    fn test_register_enum_type() {
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Color"),
            &None,
            &[],
            &[make_ctor("Red"), make_ctor("Green"), make_ctor("Blue")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // Type should be registered in symbol table
        assert!(tc.lookup_type_def(&TypeName::from("Color")).is_some());

        // Constructors should be in symbol table
        assert!(tc.symbol_table().get("Red").is_some());
        assert!(tc.symbol_table().get("Green").is_some());
        assert!(tc.symbol_table().get("Blue").is_some());

        // Constructor type lookup
        assert_eq!(
            tc.lookup_constructor_type("Red"),
            Some(TypeName::from("Color"))
        );
    }

    // spec: 05-definitions §5.2.7 — nullary constructor scheme is ADT type
    #[test]
    fn test_constructor_scheme_is_adt_type() {
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Bool2"),
            &None,
            &[],
            &[make_ctor("True2"), make_ctor("False2")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("True2")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert_eq!(scheme.ty, Type::ADT(user_fqtn("Bool2"), vec![]));
        } else {
            panic!("True2 should be a Constructor entry");
        }
    }

    // spec: 05-definitions §5.2.2 — polymorphic sum type: None and Some constructors
    #[test]
    fn test_register_polymorphic_option() {
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Option"),
            &None,
            &[Symbol::from("a")],
            &[
                make_ctor("None"),
                ConstructorDef {
                    name: Symbol::from("Some"),
                    docstring: None,
                    fields: vec![cranelisp_types::FieldDef {
                        name: Symbol::from("val"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                        span: Span::SYNTHETIC,
                    }],
                    span: Span::SYNTHETIC,
                },
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // None should be polymorphic: forall [a]. (Option a)
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("None")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert_eq!(scheme.type_vars.len(), 1, "None should have 1 quantified var");
            match &scheme.ty {
                Type::ADT(name, args) => {
                    assert_eq!(name.name.as_ref(), "Option");
                    assert_eq!(args.len(), 1);
                    assert!(matches!(args[0], Type::Var(_)));
                }
                _ => panic!("None should have ADT type, got {:?}", scheme.ty),
            }
        } else {
            panic!("None should be a Constructor entry");
        }

        // Some should be polymorphic: forall [a]. (Fn [a] (Option a))
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("Some")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert_eq!(scheme.type_vars.len(), 1, "Some should have 1 quantified var");
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 1);
                    assert!(matches!(params[0], Type::Var(_)));
                    match ret.as_ref() {
                        Type::ADT(name, args) => {
                            assert_eq!(name.name.as_ref(), "Option");
                            assert_eq!(args.len(), 1);
                            // The type var in Fn param should match the one in ADT args
                            assert_eq!(params[0], args[0]);
                        }
                        _ => panic!("Some return should be ADT"),
                    }
                }
                _ => panic!("Some should have Fn type, got {:?}", scheme.ty),
            }
        } else {
            panic!("Some should be a Constructor entry");
        }
    }

    // spec: 05-definitions §5.2.1 — product type constructor is function from fields to ADT
    #[test]
    fn test_register_product_type_with_fields() {
        // This test's product ctor has `:Int`/`:Bool` fields and seeds the
        // matching `primitives` Import edges inline, so the `Int`/`Bool`
        // IntrinsicType entries must exist in the `primitives` module —
        // `with_builtin_type_names()` seeds them (FIXME 0243: the one adt.rs
        // test that genuinely needs builtin scalar field types in scope).
        let mut tc = TestFixture::with_content(FixtureBuilder::new().with_builtin_type_names());
        // Phase B Part 2b: bare `Int`/`Bool` references in field types
        // require explicit import per Principle 17 (no Tier 2 universe walk).
        // Import registration is no longer a typecheck concern (facade
        // `typecheck.md` §"Import/export registration is not a typecheck
        // concern"); seed the needed `Int`/`Bool` import edges directly into
        // the user module's symbol table, mirroring what the orchestrator's
        // import installer would land.
        {
            let mut user = tc.symbol_table_mut();
            for ty in ["Int", "Bool"] {
                user.insert(
                    Symbol::from(ty),
                    cranelisp_types::ModuleEntry::Import {
                        source: cranelisp_types::FQSymbol {
                            module: cranelisp_types::ModuleFullPath::from("primitives"),
                            symbol: Symbol::from(ty),
                        },
                        visibility: Visibility::Public,
                    },
                );
            }
        }
        tc.register_type_def_self(
            &TypeName::from("Pair"),
            &None,
            &[],
            &[ConstructorDef {
                name: Symbol::from("MkPair"),
                docstring: None,
                fields: vec![
                    cranelisp_types::FieldDef {
                        name: Symbol::from("x"),
                        type_expr: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::FieldDef {
                        name: Symbol::from("y"),
                        type_expr: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Bool"))),
                        span: Span::SYNTHETIC,
                    },
                ],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // MkPair :: (Fn [Int Bool] Pair)
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("MkPair")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert!(scheme.type_vars.is_empty(), "MkPair should be monomorphic");
            assert_eq!(
                scheme.ty,
                Type::Fn(
                    vec![Type::Int, Type::Bool],
                    Box::new(Type::ADT(user_fqtn("Pair"), vec![]))
                )
            );
        } else {
            panic!("MkPair should be a Constructor entry");
        }

        // Per S70: TypeDefInfo.constructors is Vec<Symbol>; per-ctor metadata
        // (param_names, field types from scheme.ty) lives on the ctor's Def.
        let info = tc.lookup_type_def(&TypeName::from("Pair")).unwrap();
        assert_eq!(info.constructors.len(), 1);
        assert_eq!(info.constructors[0].as_ref(), "MkPair");
        if let Some(ModuleEntry::Def { kind, scheme, param_names, .. }) =
            tc.symbol_table().get("MkPair")
        {
            if let DefKind::Constructor { field_count, .. } = kind.as_ref() {
                assert_eq!(*field_count, 2);
            } else {
                panic!("MkPair should be DefKind::Constructor");
            }
            assert_eq!(param_names.len(), 2);
            assert_eq!(param_names[0].as_ref(), "x");
            assert_eq!(param_names[1].as_ref(), "y");
            let field_types = match &scheme.ty {
                Type::Fn(p, _) => p.clone(),
                _ => panic!("MkPair scheme should be Fn"),
            };
            assert_eq!(field_types[0], Type::Int);
            assert_eq!(field_types[1], Type::Bool);
        } else {
            panic!("MkPair should be a Def in symbol table");
        }
    }

    // spec: 06-pattern-matching §6.5.1 — all constructors covered passes exhaustiveness
    #[test]
    fn test_exhaustiveness_all_covered() {
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Color"),
            &None,
            &[],
            &[make_ctor("Red"), make_ctor("Green"), make_ctor("Blue")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        let covered = vec![
            Symbol::from("Red"),
            Symbol::from("Green"),
            Symbol::from("Blue"),
        ];
        assert!(tc
            .check_exhaustiveness(&TypeName::from("Color"), &covered, false, Span::SYNTHETIC)
            .is_ok());
    }

    // spec: 06-pattern-matching §6.5.1 — missing constructor fails exhaustiveness check
    #[test]
    fn test_exhaustiveness_missing_constructor() {
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Color"),
            &None,
            &[],
            &[make_ctor("Red"), make_ctor("Green"), make_ctor("Blue")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        let covered = vec![Symbol::from("Red"), Symbol::from("Green")];
        let err = tc
            .check_exhaustiveness(&TypeName::from("Color"), &covered, false, Span::SYNTHETIC)
            .unwrap_err();
        assert!(err.message().contains("Blue"));
    }

    // spec: 06-pattern-matching §6.5.1 — wildcard pattern covers all constructors
    #[test]
    fn test_exhaustiveness_wildcard_covers_all() {
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Color"),
            &None,
            &[],
            &[make_ctor("Red"), make_ctor("Green"), make_ctor("Blue")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // Empty covered but has wildcard -- ok
        assert!(tc
            .check_exhaustiveness(&TypeName::from("Color"), &[], true, Span::SYNTHETIC)
            .is_ok());
    }

    // spec: 05-definitions §5.2.7 — constructors receive sequential integer tags
    #[test]
    fn test_constructor_tags() {
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Dir"),
            &None,
            &[],
            &[
                make_ctor("North"),
                make_ctor("South"),
                make_ctor("East"),
                make_ctor("West"),
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        let info = tc.lookup_type_def(&TypeName::from("Dir")).unwrap();
        // Per S70: info.constructors is Vec<Symbol>; tag lives on the ctor's
        // ModuleEntry::Def's DefKind::Constructor.
        let table = tc.symbol_table();
        for (i, name) in ["North", "South", "East", "West"].iter().enumerate() {
            assert_eq!(info.constructors[i].as_ref(), *name);
            if let Some(ModuleEntry::Def { kind, .. }) = table.get(*name) {
                if let DefKind::Constructor { tag, .. } = kind.as_ref() {
                    assert_eq!(*tag, i, "{name} should have tag {i}");
                } else {
                    panic!("{name} should be DefKind::Constructor");
                }
            } else {
                panic!("{name} should be a Def in symbol table");
            }
        }
    }

    // --- Ring 1: Polymorphic ADT tests ---

    /// Helper: register (Option a) with None and Some[:a val].
    fn register_option(tc: &mut TestFixture) {
        tc.register_type_def_self(
            &TypeName::from("Option"),
            &None,
            &[Symbol::from("a")],
            &[
                make_ctor("None"),
                ConstructorDef {
                    name: Symbol::from("Some"),
                    docstring: None,
                    fields: vec![cranelisp_types::FieldDef {
                        name: Symbol::from("val"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                        span: Span::SYNTHETIC,
                    }],
                    span: Span::SYNTHETIC,
                },
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
    }

    // spec: 05-definitions §5.2.2 — polymorphic type parameters recorded in TypeDefInfo
    #[test]
    fn test_polymorphic_type_params_recorded() {
        let mut tc = tf();
        register_option(&mut tc);

        let info = tc.lookup_type_def(&TypeName::from("Option")).unwrap();
        assert_eq!(info.type_params.len(), 1);
        assert_eq!(info.type_params[0].as_ref(), "a");
    }

    // spec: 05-definitions §5.2.7 — polymorphic ADT constructors receive sequential tags
    #[test]
    fn test_polymorphic_constructor_tags() {
        let mut tc = tf();
        register_option(&mut tc);

        let info = tc.lookup_type_def(&TypeName::from("Option")).unwrap();
        // Per S70: info.constructors is Vec<Symbol>; tags live on the per-ctor
        // ModuleEntry::Def's DefKind::Constructor.
        assert_eq!(info.constructors[0].as_ref(), "None");
        assert_eq!(info.constructors[1].as_ref(), "Some");
        let table = tc.symbol_table();
        for (i, name) in ["None", "Some"].iter().enumerate() {
            if let Some(ModuleEntry::Def { kind, .. }) = table.get(*name)
                && let DefKind::Constructor { tag, .. } = kind.as_ref()
            {
                assert_eq!(*tag, i, "{name} should have tag {i}");
            } else {
                panic!("{name} should be Def(Constructor)");
            }
        }
    }

    // spec: 04-adt §4.2 — constructors are GOT-slotted callable values (0249-a)
    //
    // Every synthesised `DefKind::Constructor` entry must carry a `got_slot`,
    // exactly like a user fn — a constructor reached as a value (`(map Some
    // xs)`, `(let [f None] f)`) needs an address to load. Distinct
    // constructors get distinct slots (monotonic allocator, no aliasing). The
    // +Neg facet: the nullary `None` is slotted too — addressability does not
    // depend on arity, so a naive "only data ctors need slots" implementation
    // (which would leave `None` at `None`) is rejected.
    #[test]
    fn constructors_get_got_slots() {
        let mut tc = tf();
        register_option(&mut tc);

        let table = tc.symbol_table();
        let slot_of = |name: &str| -> Option<usize> {
            match table.get(name) {
                Some(ModuleEntry::Def { got_slot, kind, .. }) => {
                    assert!(
                        matches!(kind.as_ref(), DefKind::Constructor { .. }),
                        "{name} should be a Constructor entry"
                    );
                    *got_slot
                }
                _ => panic!("{name} should be a Def(Constructor) entry"),
            }
        };

        // Data constructor `Some` is slotted.
        let some_slot = slot_of("Some").expect("Some must have a GOT slot");
        // +Neg: the nullary constructor `None` is slotted too — not left at
        // `None` by an arity-gated implementation.
        let none_slot = slot_of("None").expect("nullary None must have a GOT slot");

        // Distinct constructors get distinct slots (monotonic allocator).
        assert_ne!(
            some_slot, none_slot,
            "distinct constructors must not alias the same GOT slot"
        );
    }

    // spec: 03-types §3.3 — polymorphic field type resolves to type variable
    #[test]
    fn test_polymorphic_field_has_var_type() {
        let mut tc = tf();
        register_option(&mut tc);

        let info = tc.lookup_type_def(&TypeName::from("Option")).unwrap();
        // Per S70: info.constructors[i] is Symbol; field metadata lives on the
        // ctor's Def — param_names + scheme.ty's Fn signature.
        assert_eq!(info.constructors[1].as_ref(), "Some");
        if let Some(ModuleEntry::Def { kind, scheme, param_names, .. }) =
            tc.symbol_table().get("Some")
        {
            if let DefKind::Constructor { field_count, .. } = kind.as_ref() {
                assert_eq!(*field_count, 1);
            } else {
                panic!("Some should be DefKind::Constructor");
            }
            assert_eq!(param_names.len(), 1);
            assert_eq!(param_names[0].as_ref(), "val");
            // Field type should be a type variable (the allocated ID)
            match &scheme.ty {
                Type::Fn(params, _) => {
                    assert_eq!(params.len(), 1);
                    assert!(matches!(params[0], Type::Var(_)));
                }
                _ => panic!("Some scheme should be Fn"),
            }
        } else {
            panic!("Some should be a Def in symbol table");
        }
    }

    // spec: 06-pattern-matching §6.5.1 — exhaustiveness with mixed nullary and data constructors
    #[test]
    fn test_exhaustiveness_with_mixed_constructors() {
        let mut tc = tf();
        register_option(&mut tc);

        // Missing None
        let covered = vec![Symbol::from("Some")];
        let err = tc
            .check_exhaustiveness(
                &TypeName::from("Option"),
                &covered,
                false,
                Span::SYNTHETIC,
            )
            .unwrap_err();
        assert!(err.message().contains("None"));

        // Missing Some
        let covered = vec![Symbol::from("None")];
        let err = tc
            .check_exhaustiveness(
                &TypeName::from("Option"),
                &covered,
                false,
                Span::SYNTHETIC,
            )
            .unwrap_err();
        assert!(err.message().contains("Some"));

        // Both covered
        let covered = vec![Symbol::from("None"), Symbol::from("Some")];
        assert!(tc
            .check_exhaustiveness(
                &TypeName::from("Option"),
                &covered,
                false,
                Span::SYNTHETIC,
            )
            .is_ok());
    }

    // spec: 05-definitions §5.2.4 — shortcut product type with bare field names gets type vars
    #[test]
    fn test_shortcut_product_type() {
        // (deftype Pair [first second]) -- bare field names with type vars
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Pair"),
            &None,
            &[Symbol::from("a"), Symbol::from("b")],
            &[ConstructorDef {
                name: Symbol::from("MkPair"),
                docstring: None,
                fields: vec![
                    cranelisp_types::FieldDef {
                        name: Symbol::from("first"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::FieldDef {
                        name: Symbol::from("second"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("b")),
                        span: Span::SYNTHETIC,
                    },
                ],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // MkPair :: forall [a, b]. (Fn [a b] (Pair a b))
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("MkPair")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert_eq!(scheme.type_vars.len(), 2, "MkPair should have 2 quantified vars");
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 2);
                    match ret.as_ref() {
                        Type::ADT(fqtn, args) => {
                            assert_eq!(fqtn.name.as_ref(), "Pair");
                            assert_eq!(args.len(), 2);
                            // param vars should match the ADT arg vars
                            assert_eq!(params[0], args[0]);
                            assert_eq!(params[1], args[1]);
                        }
                        _ => panic!("MkPair return should be ADT"),
                    }
                }
                _ => panic!("MkPair should have Fn type"),
            }
        } else {
            panic!("MkPair should be a Constructor entry");
        }
    }

    // spec: 05-definitions §5.2.2 — multi-parameter polymorphic ADT registration
    #[test]
    fn test_register_multi_param_type() {
        // (deftype (Either a b) (Left [:a val]) (Right [:b val]))
        let mut tc = tf();
        tc.register_type_def_self(
            &TypeName::from("Either"),
            &None,
            &[Symbol::from("a"), Symbol::from("b")],
            &[
                ConstructorDef {
                    name: Symbol::from("Left"),
                    docstring: None,
                    fields: vec![cranelisp_types::FieldDef {
                        name: Symbol::from("val"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                        span: Span::SYNTHETIC,
                    }],
                    span: Span::SYNTHETIC,
                },
                ConstructorDef {
                    name: Symbol::from("Right"),
                    docstring: None,
                    fields: vec![cranelisp_types::FieldDef {
                        name: Symbol::from("val"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("b")),
                        span: Span::SYNTHETIC,
                    }],
                    span: Span::SYNTHETIC,
                },
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        let info = tc.lookup_type_def(&TypeName::from("Either")).unwrap();
        assert_eq!(info.type_params.len(), 2);
        assert_eq!(info.constructors.len(), 2);

        // Both constructors should have 2 quantified vars
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("Left")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert_eq!(scheme.type_vars.len(), 2);
        } else {
            panic!("Left should be a Constructor entry");
        }
    }

    // spec: 03-types §3.2.2 — type-expr resolution validates ADT arity against
    // the registered TypeDef's type-parameter count.
    #[test]
    fn test_resolution_validates_registered_arity() {
        use cranelisp_types::{TypeExpr, TypeRef};

        let mut tc = tf();
        register_option(&mut tc);
        tc.register_type_def_self(
            &TypeName::from("Color"),
            &None,
            &[],
            &[make_ctor("Red")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // `Option` has arity 1: `(Option Color)` resolves; applying it with
        // zero args is rejected. (`Color` is registered in `user`; `Int` lives
        // in `primitives` and is not import-reachable from `user` here.)
        let opt_color = TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Option")),
            vec![TypeExpr::Named(TypeRef::new(None, TypeName::from("Color")))],
        );
        assert!(tc.resolve_type_expr_in_user(&opt_color).is_ok());

        let opt_zero =
            TypeExpr::Applied(TypeRef::new(None, TypeName::from("Option")), vec![]);
        assert!(tc.resolve_type_expr_in_user(&opt_zero).is_err());

        // `Color` has arity 0: bare `Color` resolves to its ADT type.
        let color = TypeExpr::Named(TypeRef::new(None, TypeName::from("Color")));
        assert!(tc.resolve_type_expr_in_user(&color).is_ok());

        // Unknown type name errors.
        let bogus = TypeExpr::Named(TypeRef::new(None, TypeName::from("Nope")));
        assert!(tc.resolve_type_expr_in_user(&bogus).is_err());
    }

    // spec: 05-definitions §5.2.7 — nullary monomorphic constructor scheme is bare ADT type
    #[test]
    fn test_build_constructor_scheme_nullary_mono() {
        let ctor = CtorBuild {
            name: Symbol::from("Red"),
            tag: 0,
            fields: vec![],
            docstring: None,
            internal: false,
        };
        let adt_type = Type::ADT(user_fqtn("Color"), vec![]);
        let scheme = build_constructor_scheme(&ctor, &adt_type, &[]);

        assert!(scheme.type_vars.is_empty());
        assert_eq!(scheme.ty, Type::ADT(user_fqtn("Color"), vec![]));
    }

    // spec: 05-definitions §5.2.1 — data constructor scheme is Fn from fields to ADT
    #[test]
    fn test_build_constructor_scheme_data_mono() {
        let ctor = CtorBuild {
            name: Symbol::from("Point"),
            tag: 0,
            fields: vec![
                FieldInfo { name: Symbol::from("x"), ty: Type::Int },
                FieldInfo { name: Symbol::from("y"), ty: Type::Int },
            ],
            docstring: None,
            internal: false,
        };
        let adt_type = Type::ADT(user_fqtn("Point"), vec![]);
        let scheme = build_constructor_scheme(&ctor, &adt_type, &[]);

        assert!(scheme.type_vars.is_empty());
        assert_eq!(
            scheme.ty,
            Type::Fn(
                vec![Type::Int, Type::Int],
                Box::new(Type::ADT(user_fqtn("Point"), vec![]))
            )
        );
    }

    // spec: 05-definitions §5.2.2 — polymorphic constructor scheme quantifies over type params
    #[test]
    fn test_build_constructor_scheme_polymorphic() {
        let ctor = CtorBuild {
            name: Symbol::from("Some"),
            tag: 1,
            fields: vec![
                FieldInfo { name: Symbol::from("val"), ty: Type::Var(42) },
            ],
            docstring: None,
            internal: false,
        };
        let adt_type = Type::ADT(user_fqtn("Option"), vec![Type::Var(42)]);
        let scheme = build_constructor_scheme(&ctor, &adt_type, &[42]);

        assert_eq!(scheme.type_vars, vec![42]);
        assert_eq!(
            scheme.ty,
            Type::Fn(
                vec![Type::Var(42)],
                Box::new(Type::ADT(user_fqtn("Option"), vec![Type::Var(42)]))
            )
        );
    }

    // spec: 10-io §10.1 — is_internal_constructor returns true for internal ctors
    #[test]
    fn test_is_internal_constructor() {
        let tc = tf_io();
        let primitives_path = ModuleFullPath::from("primitives");
        let env = tc.env();
        // Bind carries `internal: true` on its `DefKind::Constructor`. Rooted
        // at its home module (primitives), the check resolves the Constructor
        // Def and reads the discriminator.
        assert!(
            env.is_internal_constructor_check_in_module(&primitives_path, "Bind"),
            "Bind must be reported internal"
        );
        // Non-internal IO constructors return false.
        assert!(!env.is_internal_constructor_check_in_module(&primitives_path, "Pure"));
        assert!(!env.is_internal_constructor_check_in_module(&primitives_path, "Effect"));
        // Unknown constructors return false.
        assert!(!env.is_internal_constructor_check_in_module(&primitives_path, "NoSuchCtor"));
    }

    // spec: 10-io §10.1 — internal-ctor check chain-follows Import entries.
    //
    // Regression for the Wave-4c enforcement defect: when `Bind` is reachable
    // from a module via a glob import (the realistic shape — `user`/`test`
    // imports `primitives`), the `internal` discriminator must still be read
    // through the Import entry. A direct probe returned the Import (not the
    // Constructor Def) and silently reported `false`, so `(Bind …)` resolved
    // and compiled in user code.
    #[test]
    fn test_is_internal_constructor_through_import() {
        use cranelisp_types::{ModuleEntry, Symbol, FQSymbol, Visibility};
        let tc = tf_io();
        let user_path = ModuleFullPath::from("user");
        // Seed user-module Imports of `Bind` and its parent `IO` type from
        // primitives — what a glob import of primitives materialises (both the
        // constructor name and the type name land as Import entries).
        {
            let mut user_tbl = tc.modules.get_mut(&user_path).unwrap();
            for name in ["Bind", "IO"] {
                user_tbl.insert(
                    Symbol::from(name),
                    ModuleEntry::Import {
                        source: FQSymbol {
                            module: ModuleFullPath::from("primitives"),
                            symbol: Symbol::from(name),
                        },
                        visibility: Visibility::Public,
                    },
                );
            }
        }
        let env = tc.env();
        assert!(
            env.is_internal_constructor_check_in_module(&user_path, "Bind"),
            "Bind imported into user must still be reported internal \
             (chain-follow the Import to the primitives Constructor Def)"
        );
    }

    // spec: 10-io §10.1 — exhaustiveness excludes internal constructors
    #[test]
    fn test_exhaustiveness_excludes_internal_constructors() {
        let tc = tf_io();
        let primitives_path = ModuleFullPath::from("primitives");
        // IO has Pure (tag=0), Effect (tag=1), Bind (tag=2, internal).
        // Exhaustiveness should only require Pure and Effect.
        let covered = vec![Symbol::from("Pure"), Symbol::from("Effect")];
        assert!(tc
            .check_exhaustiveness_in_module(
                &primitives_path,
                &TypeName::from("IO"),
                &covered,
                false,
                Span::SYNTHETIC,
            )
            .is_ok(),
            "matching Pure + Effect should be exhaustive (Bind is internal)"
        );

        // Missing Effect should fail.
        let covered = vec![Symbol::from("Pure")];
        let err = tc
            .check_exhaustiveness_in_module(
                &primitives_path,
                &TypeName::from("IO"),
                &covered,
                false,
                Span::SYNTHETIC,
            )
            .unwrap_err();
        assert!(err.message().contains("Effect"), "should report missing Effect, got: {}", err.message());
        // Should NOT mention Bind.
        assert!(!err.message().contains("Bind"), "should not mention internal Bind");
    }
}
