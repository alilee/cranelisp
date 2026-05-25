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
    ConstructorDef, ConstructorInfo, CranelispError, FQTypeName, FieldInfo, ModuleEntry,
    ModuleFullPath, Scheme, Span, Symbol, Type, TypeDefInfo, TypeId, TypeName, Visibility,
};

use crate::checker::{CheckState, TypeCheckEnv};
use crate::resolve::resolve_type_expr;

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
                    docstring: None,
                },
                visibility,
                constructor_scheme: None,
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

    /// Register a type definition using pre-resolved `ConstructorInfo`s.
    ///
    /// This is the synthetic-bootstrap path used when a type's constructor
    /// fields reference types in foreign synthetic modules (e.g. `Trace` in
    /// `primitives` referencing `macros/SList`). Per Principle 17, synthetic
    /// modules have empty imports, so short-name resolution via TypeExpr
    /// cannot reach foreign-module type names — the caller must construct
    /// FQ field types directly using `*_fqtn(...)` helpers and supply them
    /// here as already-built `ConstructorInfo`s.
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
        ctor_infos: Vec<ConstructorInfo>,
        visibility: Visibility,
    ) {
        let fqtn = FQTypeName::new(state.current_module.clone(), name.clone());
        let type_args: Vec<Type> = type_var_ids.iter().map(|&id| Type::Var(id)).collect();
        let adt_type = Type::ADT(fqtn.clone(), type_args);

        // Ensure the type is pre-seeded (the `register_type_def` path pre-seeds;
        // direct callers may not have, so do it here defensively).
        self.current_symbol_table_mut(state).insert(
            Symbol::from(name.as_ref()),
            ModuleEntry::TypeDef {
                info: TypeDefInfo {
                    name: fqtn.clone(),
                    type_params: type_params.to_vec(),
                    constructors: vec![],
                    docstring: None,
                },
                visibility,
                constructor_scheme: None,
            },
        );

        let type_def_info = TypeDefInfo {
            name: fqtn.clone(),
            type_params: type_params.to_vec(),
            constructors: ctor_infos,
            docstring: docstring.clone(),
        };

        // Register each constructor with its scheme
        self.register_constructors(
            state,
            name,
            &type_def_info,
            &adt_type,
            type_var_ids,
            visibility,
        );

        // If a single constructor has the same name as the type (product type),
        // store its scheme so lookups find the constructor through the TypeDef.
        let ctor_scheme = self.find_same_name_constructor_scheme(state, name);

        // Register the type in the symbol table
        self.current_symbol_table_mut(state).insert(
            Symbol::from(name.as_ref()),
            ModuleEntry::TypeDef {
                info: type_def_info,
                visibility,
                constructor_scheme: ctor_scheme,
            },
        );
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

    /// Build ConstructorInfo entries with resolved field types.
    fn build_constructor_infos(
        &self,
        state: &CheckState,
        type_name: &TypeName,
        constructors: &[ConstructorDef],
        var_map: &HashMap<Symbol, TypeId>,
        span: Span,
    ) -> Result<Vec<ConstructorInfo>, CranelispError> {
        let known_types = self.known_type_names_with_state(state);

        constructors
            .iter()
            .enumerate()
            .map(|(tag, ctor)| {
                self.build_single_ctor_info(
                    type_name, ctor, tag, var_map, &known_types, span,
                )
            })
            .collect()
    }

    /// Build a single ConstructorInfo with resolved field types.
    fn build_single_ctor_info(
        &self,
        _type_name: &TypeName,
        ctor: &ConstructorDef,
        tag: usize,
        var_map: &HashMap<Symbol, TypeId>,
        known_types: &crate::resolve::KnownTypes,
        span: Span,
    ) -> Result<ConstructorInfo, CranelispError> {
        let fields: Vec<FieldInfo> = ctor
            .fields
            .iter()
            .map(|field| {
                let ty = resolve_type_expr(
                    &field.type_expr, var_map, known_types, span,
                )?;
                Ok(FieldInfo {
                    name: field.name.clone(),
                    ty,
                })
            })
            .collect::<Result<Vec<_>, CranelispError>>()?;

        Ok(ConstructorInfo {
            name: ctor.name.clone(),
            tag,
            fields,
            docstring: ctor.docstring.clone(),
            internal: false,
        })
    }

    /// If a constructor has the same name as the type, return its scheme.
    /// This supports product-type syntax like `(deftype Point [:Int x :Int y])`.
    fn find_same_name_constructor_scheme(
        &self,
        state: &CheckState,
        type_name: &TypeName,
    ) -> Option<Scheme> {
        let ctor_sym = Symbol::from(type_name.as_ref());
        let r = self.current_symbol_table(state);
        let v = r.view();
        if let Some(ModuleEntry::Constructor { scheme, .. }) = v.lookup(&ctor_sym) {
            Some(scheme.clone())
        } else {
            None
        }
    }

    /// Register constructors in the current module's symbol table.
    fn register_constructors(
        &self,
        state: &mut CheckState,
        _name: &TypeName,
        type_def_info: &TypeDefInfo,
        adt_type: &Type,
        type_var_ids: &[TypeId],
        visibility: Visibility,
    ) {
        let fqtn = type_def_info.name.clone();
        for ctor_info in &type_def_info.constructors {
            let ctor_scheme = build_constructor_scheme(
                ctor_info, adt_type, type_var_ids,
            );

            self.current_symbol_table_mut(state).insert(
                ctor_info.name.clone(),
                ModuleEntry::Constructor {
                    type_name: fqtn.clone(),
                    info: ctor_info.clone(),
                    scheme: ctor_scheme,
                    visibility,
                },
            );
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
    ctor_info: &ConstructorInfo,
    adt_type: &Type,
    type_var_ids: &[TypeId],
) -> Scheme {
    let vars: Vec<TypeId> = type_var_ids.to_vec();

    let ty = if ctor_info.fields.is_empty() {
        // Nullary constructor: just the ADT type
        adt_type.clone()
    } else {
        // Data constructor: Fn([field types...], ADT type)
        let param_types: Vec<Type> = ctor_info
            .fields
            .iter()
            .map(|f| f.ty.clone())
            .collect();
        Type::Fn(param_types, Box::new(adt_type.clone()))
    };

    Scheme {
        vars,
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
        // and need not cover them (design/typecheck/io-types.md §1).
        let all_ctors: std::collections::HashSet<&str> = type_def
            .constructors
            .iter()
            .filter(|c| !c.internal)
            .map(|c| c.name.as_ref())
            .collect();

        // Strip optional module prefix from covered constructor names so FQ
        // pattern names (`macros/SCons`) compare equal to type_def's bare
        // constructor names (`SCons`). FQ constructor references are valid
        // under Principle 17 cross-module navigation.
        let covered: std::collections::HashSet<&str> = covered_ctors
            .iter()
            .map(|c| {
                let s = c.as_ref();
                s.rsplit('/').next().unwrap_or(s)
            })
            .collect();

        let missing: Vec<&str> = all_ctors.difference(&covered).copied().collect();

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
    use crate::checker::TestFixture;
    use cranelisp_types::{ConstructorDef, ModuleFullPath};

    /// Test helper: create an FQTypeName in the "user" module (default for TestFixture::new()).
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
        let mut tc = TestFixture::new();
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
        let mut tc = TestFixture::new();
        tc.register_type_def_self(
            &TypeName::from("Bool2"),
            &None,
            &[],
            &[make_ctor("True2"), make_ctor("False2")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        if let Some(ModuleEntry::Constructor { scheme, .. }) = tc.symbol_table().get("True2") {
            assert_eq!(scheme.ty, Type::ADT(user_fqtn("Bool2"), vec![]));
        } else {
            panic!("True2 should be a Constructor entry");
        }
    }

    // spec: 05-definitions §5.2.2 — polymorphic sum type: None and Some constructors
    #[test]
    fn test_register_polymorphic_option() {
        let mut tc = TestFixture::new();
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
                    }],
                    span: Span::SYNTHETIC,
                },
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // None should be polymorphic: forall [a]. (Option a)
        if let Some(ModuleEntry::Constructor { scheme, .. }) = tc.symbol_table().get("None") {
            assert_eq!(scheme.vars.len(), 1, "None should have 1 quantified var");
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
        if let Some(ModuleEntry::Constructor { scheme, .. }) = tc.symbol_table().get("Some") {
            assert_eq!(scheme.vars.len(), 1, "Some should have 1 quantified var");
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
        let mut tc = TestFixture::new();
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
                        type_expr: cranelisp_types::TypeExpr::Named(TypeName::from("Int")),
                    },
                    cranelisp_types::FieldDef {
                        name: Symbol::from("y"),
                        type_expr: cranelisp_types::TypeExpr::Named(TypeName::from("Bool")),
                    },
                ],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // MkPair :: (Fn [Int Bool] Pair)
        if let Some(ModuleEntry::Constructor { scheme, .. }) = tc.symbol_table().get("MkPair") {
            assert!(scheme.vars.is_empty(), "MkPair should be monomorphic");
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

        // TypeDefInfo should have the fields recorded
        let info = tc.lookup_type_def(&TypeName::from("Pair")).unwrap();
        assert_eq!(info.constructors.len(), 1);
        assert_eq!(info.constructors[0].fields.len(), 2);
        assert_eq!(info.constructors[0].fields[0].name.as_ref(), "x");
        assert_eq!(info.constructors[0].fields[0].ty, Type::Int);
        assert_eq!(info.constructors[0].fields[1].name.as_ref(), "y");
        assert_eq!(info.constructors[0].fields[1].ty, Type::Bool);
    }

    // spec: 06-pattern-matching §6.5.1 — all constructors covered passes exhaustiveness
    #[test]
    fn test_exhaustiveness_all_covered() {
        let mut tc = TestFixture::new();
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
        let mut tc = TestFixture::new();
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
        let mut tc = TestFixture::new();
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
        let mut tc = TestFixture::new();
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
        assert_eq!(info.constructors[0].tag, 0);
        assert_eq!(info.constructors[1].tag, 1);
        assert_eq!(info.constructors[2].tag, 2);
        assert_eq!(info.constructors[3].tag, 3);
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
        let mut tc = TestFixture::new();
        register_option(&mut tc);

        let info = tc.lookup_type_def(&TypeName::from("Option")).unwrap();
        assert_eq!(info.type_params.len(), 1);
        assert_eq!(info.type_params[0].as_ref(), "a");
    }

    // spec: 05-definitions §5.2.7 — polymorphic ADT constructors receive sequential tags
    #[test]
    fn test_polymorphic_constructor_tags() {
        let mut tc = TestFixture::new();
        register_option(&mut tc);

        let info = tc.lookup_type_def(&TypeName::from("Option")).unwrap();
        assert_eq!(info.constructors[0].name.as_ref(), "None");
        assert_eq!(info.constructors[0].tag, 0);
        assert_eq!(info.constructors[1].name.as_ref(), "Some");
        assert_eq!(info.constructors[1].tag, 1);
    }

    // spec: 03-types §3.3 — polymorphic field type resolves to type variable
    #[test]
    fn test_polymorphic_field_has_var_type() {
        let mut tc = TestFixture::new();
        register_option(&mut tc);

        let info = tc.lookup_type_def(&TypeName::from("Option")).unwrap();
        let some_ctor = &info.constructors[1];
        assert_eq!(some_ctor.fields.len(), 1);
        assert_eq!(some_ctor.fields[0].name.as_ref(), "val");
        // Field type should be a type variable (the allocated ID)
        assert!(matches!(some_ctor.fields[0].ty, Type::Var(_)));
    }

    // spec: 06-pattern-matching §6.5.1 — exhaustiveness with mixed nullary and data constructors
    #[test]
    fn test_exhaustiveness_with_mixed_constructors() {
        let mut tc = TestFixture::new();
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
        let mut tc = TestFixture::new();
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
                    },
                    cranelisp_types::FieldDef {
                        name: Symbol::from("second"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("b")),
                    },
                ],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // MkPair :: forall [a, b]. (Fn [a b] (Pair a b))
        if let Some(ModuleEntry::Constructor { scheme, .. }) = tc.symbol_table().get("MkPair") {
            assert_eq!(scheme.vars.len(), 2, "MkPair should have 2 quantified vars");
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
        let mut tc = TestFixture::new();
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
                    }],
                    span: Span::SYNTHETIC,
                },
                ConstructorDef {
                    name: Symbol::from("Right"),
                    docstring: None,
                    fields: vec![cranelisp_types::FieldDef {
                        name: Symbol::from("val"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("b")),
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
        if let Some(ModuleEntry::Constructor { scheme, .. }) = tc.symbol_table().get("Left") {
            assert_eq!(scheme.vars.len(), 2);
        } else {
            panic!("Left should be a Constructor entry");
        }
    }

    // spec: 03-types §3.2.2 — known_types tracks type parameter count for arity validation
    #[test]
    fn test_known_types_includes_param_count() {
        let mut tc = TestFixture::new();
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

        let known = tc.known_type_names();
        assert_eq!(known.get(&TypeName::from("Option")).map(|t| t.1), Some(1));
        assert_eq!(known.get(&TypeName::from("Color")).map(|t| t.1), Some(0));
    }

    // spec: 05-definitions §5.2.7 — nullary monomorphic constructor scheme is bare ADT type
    #[test]
    fn test_build_constructor_scheme_nullary_mono() {
        let ctor = ConstructorInfo {
            name: Symbol::from("Red"),
            tag: 0,
            fields: vec![],
            docstring: None,
            internal: false,
        };
        let adt_type = Type::ADT(user_fqtn("Color"), vec![]);
        let scheme = build_constructor_scheme(&ctor, &adt_type, &[]);

        assert!(scheme.vars.is_empty());
        assert_eq!(scheme.ty, Type::ADT(user_fqtn("Color"), vec![]));
    }

    // spec: 05-definitions §5.2.1 — data constructor scheme is Fn from fields to ADT
    #[test]
    fn test_build_constructor_scheme_data_mono() {
        let ctor = ConstructorInfo {
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

        assert!(scheme.vars.is_empty());
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
        let ctor = ConstructorInfo {
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

        assert_eq!(scheme.vars, vec![42]);
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
        let tc = TestFixture::new();
        // Bind is internal but NOT registered in constructor_to_type,
        // so this returns false (enforcement is name-resolution-based).
        // If Bind were in constructor_to_type, this would return true.
        assert!(!tc.is_internal_constructor_check("Bind"));
        // Non-internal constructors return false.
        assert!(!tc.is_internal_constructor_check("Pure"));
        assert!(!tc.is_internal_constructor_check("Effect"));
        // Unknown constructors return false.
        assert!(!tc.is_internal_constructor_check("NoSuchCtor"));
    }

    // spec: 10-io §10.1 — exhaustiveness excludes internal constructors
    #[test]
    fn test_exhaustiveness_excludes_internal_constructors() {
        let tc = TestFixture::new();
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
