//! ADT type definitions: registration, constructor lookup, exhaustiveness checking.
//!
//! Handles both enum-only ADTs (nullary constructors, Ring 0) and parameterized
//! ADTs with data constructor fields (Ring 1). Polymorphic types produce
//! polymorphic constructor schemes via `build_constructor_scheme`.

use std::collections::HashMap;

use cranelisp_types::{
    ConstructorDef, ConstructorInfo, CranelispError, FieldInfo, ModuleEntry,
    Scheme, Span, Symbol, Type, TypeDefInfo, TypeId, TypeName, Visibility,
};

use crate::checker::TypeChecker;
use crate::resolve::resolve_type_expr;

/// Registry of user-defined type definitions.
#[derive(Debug, Clone)]
pub struct TypeDefRegistry {
    /// Type definitions keyed by type name.
    pub(crate) type_defs: HashMap<TypeName, TypeDefInfo>,
    /// Map from constructor name to its parent type name.
    pub(crate) constructor_to_type: HashMap<Symbol, TypeName>,
}

impl TypeDefRegistry {
    pub fn new() -> Self {
        TypeDefRegistry {
            type_defs: HashMap::new(),
            constructor_to_type: HashMap::new(),
        }
    }

    /// Get type definition info by name.
    pub fn get(&self, name: &TypeName) -> Option<&TypeDefInfo> {
        self.type_defs.get(name)
    }

    /// Get the parent type name for a constructor.
    pub fn constructor_type(&self, ctor_name: &str) -> Option<&TypeName> {
        self.constructor_to_type.get(ctor_name)
    }

    /// Build a map of known type names with their type parameter counts.
    /// Used by `resolve_type_expr` for ADT lookup and arity validation.
    pub fn known_types(&self) -> crate::resolve::KnownTypes {
        self.type_defs
            .iter()
            .map(|(k, info)| (k.clone(), info.type_params.len()))
            .collect()
    }
}

impl Default for TypeDefRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeChecker {
    /// Register a type definition from a TopLevel::TypeDef.
    ///
    /// Handles both nullary enums (Ring 0) and parameterized ADTs with data
    /// constructor fields (Ring 1). Allocates fresh type vars for type parameters,
    /// resolves field types, and produces polymorphic constructor schemes.
    pub(crate) fn register_type_def(
        &mut self,
        name: &TypeName,
        docstring: &Option<String>,
        type_params: &[Symbol],
        constructors: &[ConstructorDef],
        visibility: Visibility,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Allocate fresh type vars for type parameters
        let (var_map, type_var_ids) = self.allocate_type_params(type_params);

        // Build the ADT result type using the type parameter vars
        let type_args: Vec<Type> = type_var_ids.iter().map(|&id| Type::Var(id)).collect();
        let adt_type = Type::ADT(name.clone(), type_args);

        // Pre-seed the type name so recursive constructor fields (e.g.,
        // `:(List a) tail` inside a `(deftype (List a) ...)`) can resolve
        // the type during `build_constructor_infos`. The full TypeDefInfo
        // replaces this placeholder below.
        self.type_defs.type_defs.insert(
            name.clone(),
            TypeDefInfo {
                name: name.clone(),
                type_params: type_params.to_vec(),
                constructors: vec![],
                docstring: None,
            },
        );

        // Build constructor infos with resolved field types.
        // If resolution fails, remove the pre-seeded placeholder so it
        // doesn't pollute known_types for subsequent definitions.
        let ctor_infos = match self.build_constructor_infos(
            name, constructors, &var_map, span,
        ) {
            Ok(infos) => infos,
            Err(e) => {
                self.type_defs.type_defs.remove(name);
                return Err(e);
            }
        };

        let type_def_info = TypeDefInfo {
            name: name.clone(),
            type_params: type_params.to_vec(),
            constructors: ctor_infos,
            docstring: docstring.clone(),
        };

        // Register the type definition
        self.type_defs
            .type_defs
            .insert(name.clone(), type_def_info.clone());

        // Register each constructor with its scheme
        self.register_constructors(
            name, &type_def_info, &adt_type, &type_var_ids, visibility,
        );

        // If a single constructor has the same name as the type (product type),
        // store its scheme so lookups find the constructor through the TypeDef.
        let ctor_scheme = self.find_same_name_constructor_scheme(name);

        // Register the type in the symbol table
        self.current_symbol_table_mut().insert(
            Symbol::from(name.as_ref()),
            ModuleEntry::TypeDef {
                info: type_def_info,
                visibility,
                constructor_scheme: ctor_scheme,
                sexp: None,
            },
        );

        Ok(())
    }

    /// Allocate fresh type variables for type parameters.
    /// Returns a var_map (param name -> TypeId) and the ordered list of TypeIds.
    fn allocate_type_params(
        &mut self,
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
        type_name: &TypeName,
        constructors: &[ConstructorDef],
        var_map: &HashMap<Symbol, TypeId>,
        span: Span,
    ) -> Result<Vec<ConstructorInfo>, CranelispError> {
        let known_types = self.known_type_names();

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
        })
    }

    /// If a constructor has the same name as the type, return its scheme.
    /// This supports product-type syntax like `(deftype Point [:Int x :Int y])`.
    fn find_same_name_constructor_scheme(
        &self,
        type_name: &TypeName,
    ) -> Option<Scheme> {
        let ctor_sym = Symbol::from(type_name.as_ref());
        if let Some(ModuleEntry::Constructor { scheme, .. }) =
            self.current_symbol_table().get(ctor_sym.as_ref())
        {
            Some(scheme.clone())
        } else {
            None
        }
    }

    /// Register constructors in symbol table and constructor_to_type map.
    fn register_constructors(
        &mut self,
        name: &TypeName,
        type_def_info: &TypeDefInfo,
        adt_type: &Type,
        type_var_ids: &[TypeId],
        visibility: Visibility,
    ) {
        for ctor_info in &type_def_info.constructors {
            let ctor_scheme = build_constructor_scheme(
                ctor_info, adt_type, type_var_ids,
            );

            self.current_symbol_table_mut().insert(
                ctor_info.name.clone(),
                ModuleEntry::Constructor {
                    type_name: Symbol::from(name.as_ref()),
                    info: ctor_info.clone(),
                    scheme: ctor_scheme,
                    visibility,
                },
            );

            self.type_defs
                .constructor_to_type
                .insert(ctor_info.name.clone(), name.clone());
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

impl TypeChecker {
    /// Check exhaustiveness of match arms against an ADT type.
    ///
    /// Returns Ok(()) if the match is exhaustive, Err with details otherwise.
    /// A match is exhaustive if:
    /// 1. All constructors of the ADT are covered, OR
    /// 2. A wildcard or variable pattern is present.
    pub(crate) fn check_exhaustiveness(
        &self,
        type_name: &TypeName,
        covered_ctors: &[Symbol],
        has_wildcard: bool,
        span: Span,
    ) -> Result<(), CranelispError> {
        if has_wildcard {
            return Ok(());
        }

        let type_def = self.type_defs.get(type_name).ok_or_else(|| {
            CranelispError::TypeError {
                message: format!("unknown type in match: {type_name}"),
                span,
            }
        })?;

        let all_ctors: std::collections::HashSet<&str> = type_def
            .constructors
            .iter()
            .map(|c| c.name.as_ref())
            .collect();

        let covered: std::collections::HashSet<&str> =
            covered_ctors.iter().map(|c| c.as_ref()).collect();

        let missing: Vec<&str> = all_ctors.difference(&covered).copied().collect();

        if missing.is_empty() {
            Ok(())
        } else {
            let mut missing_sorted = missing;
            missing_sorted.sort();
            Err(CranelispError::TypeError {
                message: format!(
                    "non-exhaustive match on {type_name}: missing constructor(s) {}",
                    missing_sorted.join(", ")
                ),
                span,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::ConstructorDef;

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
        let mut tc = TypeChecker::new();
        tc.register_type_def(
            &TypeName::from("Color"),
            &None,
            &[],
            &[make_ctor("Red"), make_ctor("Green"), make_ctor("Blue")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // Type should be registered
        assert!(tc.type_defs.get(&TypeName::from("Color")).is_some());

        // Constructors should be in symbol table
        assert!(tc.symbol_table().get("Red").is_some());
        assert!(tc.symbol_table().get("Green").is_some());
        assert!(tc.symbol_table().get("Blue").is_some());

        // Constructor type lookup
        assert_eq!(
            tc.type_defs.constructor_type("Red"),
            Some(&TypeName::from("Color"))
        );
    }

    // spec: 05-definitions §5.2.7 — nullary constructor scheme is ADT type
    #[test]
    fn test_constructor_scheme_is_adt_type() {
        let mut tc = TypeChecker::new();
        tc.register_type_def(
            &TypeName::from("Bool2"),
            &None,
            &[],
            &[make_ctor("True2"), make_ctor("False2")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        if let Some(ModuleEntry::Constructor { scheme, .. }) = tc.symbol_table().get("True2") {
            assert_eq!(scheme.ty, Type::ADT(TypeName::from("Bool2"), vec![]));
        } else {
            panic!("True2 should be a Constructor entry");
        }
    }

    // spec: 05-definitions §5.2.2 — polymorphic sum type: None and Some constructors
    #[test]
    fn test_register_polymorphic_option() {
        let mut tc = TypeChecker::new();
        tc.register_type_def(
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
                    assert_eq!(name.as_ref(), "Option");
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
                            assert_eq!(name.as_ref(), "Option");
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
        let mut tc = TypeChecker::new();
        tc.register_type_def(
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
                    Box::new(Type::ADT(TypeName::from("Pair"), vec![]))
                )
            );
        } else {
            panic!("MkPair should be a Constructor entry");
        }

        // TypeDefInfo should have the fields recorded
        let info = tc.type_defs.get(&TypeName::from("Pair")).unwrap();
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
        let mut tc = TypeChecker::new();
        tc.register_type_def(
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
        let mut tc = TypeChecker::new();
        tc.register_type_def(
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
        let mut tc = TypeChecker::new();
        tc.register_type_def(
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
        let mut tc = TypeChecker::new();
        tc.register_type_def(
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

        let info = tc.type_defs.get(&TypeName::from("Dir")).unwrap();
        assert_eq!(info.constructors[0].tag, 0);
        assert_eq!(info.constructors[1].tag, 1);
        assert_eq!(info.constructors[2].tag, 2);
        assert_eq!(info.constructors[3].tag, 3);
    }

    // --- Ring 1: Polymorphic ADT tests ---

    /// Helper: register (Option a) with None and Some[:a val].
    fn register_option(tc: &mut TypeChecker) {
        tc.register_type_def(
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
        let mut tc = TypeChecker::new();
        register_option(&mut tc);

        let info = tc.type_defs.get(&TypeName::from("Option")).unwrap();
        assert_eq!(info.type_params.len(), 1);
        assert_eq!(info.type_params[0].as_ref(), "a");
    }

    // spec: 05-definitions §5.2.7 — polymorphic ADT constructors receive sequential tags
    #[test]
    fn test_polymorphic_constructor_tags() {
        let mut tc = TypeChecker::new();
        register_option(&mut tc);

        let info = tc.type_defs.get(&TypeName::from("Option")).unwrap();
        assert_eq!(info.constructors[0].name.as_ref(), "None");
        assert_eq!(info.constructors[0].tag, 0);
        assert_eq!(info.constructors[1].name.as_ref(), "Some");
        assert_eq!(info.constructors[1].tag, 1);
    }

    // spec: 03-types §3.3 — polymorphic field type resolves to type variable
    #[test]
    fn test_polymorphic_field_has_var_type() {
        let mut tc = TypeChecker::new();
        register_option(&mut tc);

        let info = tc.type_defs.get(&TypeName::from("Option")).unwrap();
        let some_ctor = &info.constructors[1];
        assert_eq!(some_ctor.fields.len(), 1);
        assert_eq!(some_ctor.fields[0].name.as_ref(), "val");
        // Field type should be a type variable (the allocated ID)
        assert!(matches!(some_ctor.fields[0].ty, Type::Var(_)));
    }

    // spec: 06-pattern-matching §6.5.1 — exhaustiveness with mixed nullary and data constructors
    #[test]
    fn test_exhaustiveness_with_mixed_constructors() {
        let mut tc = TypeChecker::new();
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
        let mut tc = TypeChecker::new();
        tc.register_type_def(
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
                        Type::ADT(name, args) => {
                            assert_eq!(name.as_ref(), "Pair");
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
        let mut tc = TypeChecker::new();
        tc.register_type_def(
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

        let info = tc.type_defs.get(&TypeName::from("Either")).unwrap();
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
        let mut tc = TypeChecker::new();
        register_option(&mut tc);
        tc.register_type_def(
            &TypeName::from("Color"),
            &None,
            &[],
            &[make_ctor("Red")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        let known = tc.known_type_names();
        assert_eq!(known.get(&TypeName::from("Option")), Some(&1));
        assert_eq!(known.get(&TypeName::from("Color")), Some(&0));
    }

    // spec: 05-definitions §5.2.7 — nullary monomorphic constructor scheme is bare ADT type
    #[test]
    fn test_build_constructor_scheme_nullary_mono() {
        let ctor = ConstructorInfo {
            name: Symbol::from("Red"),
            tag: 0,
            fields: vec![],
            docstring: None,
        };
        let adt_type = Type::ADT(TypeName::from("Color"), vec![]);
        let scheme = build_constructor_scheme(&ctor, &adt_type, &[]);

        assert!(scheme.vars.is_empty());
        assert_eq!(scheme.ty, Type::ADT(TypeName::from("Color"), vec![]));
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
        };
        let adt_type = Type::ADT(TypeName::from("Point"), vec![]);
        let scheme = build_constructor_scheme(&ctor, &adt_type, &[]);

        assert!(scheme.vars.is_empty());
        assert_eq!(
            scheme.ty,
            Type::Fn(
                vec![Type::Int, Type::Int],
                Box::new(Type::ADT(TypeName::from("Point"), vec![]))
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
        };
        let adt_type = Type::ADT(TypeName::from("Option"), vec![Type::Var(42)]);
        let scheme = build_constructor_scheme(&ctor, &adt_type, &[42]);

        assert_eq!(scheme.vars, vec![42]);
        assert_eq!(
            scheme.ty,
            Type::Fn(
                vec![Type::Var(42)],
                Box::new(Type::ADT(TypeName::from("Option"), vec![Type::Var(42)]))
            )
        );
    }
}
