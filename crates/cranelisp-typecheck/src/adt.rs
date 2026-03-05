//! ADT type definitions: registration, constructor lookup, exhaustiveness checking.
//!
//! Ring 0 handles enum-only ADTs (all constructors nullary, no type params).
//! Ring 1 extends to handle data constructors with fields and type parameters.

use std::collections::HashMap;

use cranelisp_types::{
    ConstructorDef, ConstructorInfo, CranelispError, ModuleEntry,
    Span, Symbol, Type, TypeDefInfo, TypeName, Visibility,
};

use crate::checker::TypeChecker;
use crate::scheme::mono;

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

    /// Build a map of known type names (for type expression resolution).
    pub fn known_types(&self) -> HashMap<TypeName, ()> {
        self.type_defs.keys().map(|k| (k.clone(), ())).collect()
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
    /// Ring 0: enum-only (all constructors nullary, no type params).
    /// Validates that Ring 0 constraints are met.
    pub(crate) fn register_type_def(
        &mut self,
        name: &TypeName,
        docstring: &Option<String>,
        type_params: &[Symbol],
        constructors: &[ConstructorDef],
        visibility: Visibility,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Ring 0: no type parameters
        if !type_params.is_empty() {
            return Err(CranelispError::TypeError {
                message: format!(
                    "type {name}: parameterized types not supported in Ring 0"
                ),
                span,
            });
        }

        // Validate constructors (Ring 0: all nullary) and build info
        for ctor in constructors {
            if !ctor.fields.is_empty() {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "constructor {} of type {name}: data constructors with fields not supported in Ring 0",
                        ctor.name
                    ),
                    span: ctor.span,
                });
            }
        }

        let ctor_infos: Vec<ConstructorInfo> = constructors
            .iter()
            .enumerate()
            .map(|(tag, ctor)| ConstructorInfo {
                name: ctor.name.clone(),
                tag,
                fields: vec![],
                docstring: ctor.docstring.clone(),
            })
            .collect();

        let type_def_info = TypeDefInfo {
            name: name.clone(),
            type_params: vec![],
            constructors: ctor_infos,
            docstring: docstring.clone(),
        };

        // Register the type definition
        self.type_defs
            .type_defs
            .insert(name.clone(), type_def_info.clone());

        // Register each constructor
        let adt_type = Type::ADT(name.clone(), vec![]);
        for ctor_info in &type_def_info.constructors {
            // Nullary constructors have type: ADT_name (no args)
            let ctor_scheme = mono(adt_type.clone());

            self.symbol_table.insert(
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

        // Register the type in the symbol table (after constructors, consuming type_def_info)
        self.symbol_table.insert(
            Symbol::from(name.as_ref()),
            ModuleEntry::TypeDef {
                info: type_def_info,
                visibility,
                constructor_scheme: None,
                sexp: None,
            },
        );

        Ok(())
    }

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
        assert!(tc.symbol_table.get("Red").is_some());
        assert!(tc.symbol_table.get("Green").is_some());
        assert!(tc.symbol_table.get("Blue").is_some());

        // Constructor type lookup
        assert_eq!(
            tc.type_defs.constructor_type("Red"),
            Some(&TypeName::from("Color"))
        );
    }

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

        if let Some(ModuleEntry::Constructor { scheme, .. }) = tc.symbol_table.get("True2") {
            assert_eq!(scheme.ty, Type::ADT(TypeName::from("Bool2"), vec![]));
        } else {
            panic!("True2 should be a Constructor entry");
        }
    }

    #[test]
    fn test_reject_type_params_in_ring_0() {
        let mut tc = TypeChecker::new();
        let err = tc
            .register_type_def(
                &TypeName::from("Option"),
                &None,
                &[Symbol::from("a")],
                &[make_ctor("None"), make_ctor("Some")],
                Visibility::Public,
                Span::SYNTHETIC,
            )
            .unwrap_err();
        assert!(err.message().contains("parameterized types"));
    }

    #[test]
    fn test_reject_data_constructors_in_ring_0() {
        let mut tc = TypeChecker::new();
        let err = tc
            .register_type_def(
                &TypeName::from("Pair"),
                &None,
                &[],
                &[ConstructorDef {
                    name: Symbol::from("MkPair"),
                    docstring: None,
                    fields: vec![cranelisp_types::FieldDef {
                        name: Symbol::from("x"),
                        type_expr: cranelisp_types::TypeExpr::Named(TypeName::from("Int")),
                    }],
                    span: Span::SYNTHETIC,
                }],
                Visibility::Public,
                Span::SYNTHETIC,
            )
            .unwrap_err();
        assert!(err.message().contains("data constructors with fields"));
    }

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
}
