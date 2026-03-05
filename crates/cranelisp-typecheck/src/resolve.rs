//! Resolve TypeExpr (source annotations) to Type.
//!
//! All resolution returns Result, never panics (addresses audit HIGH-4).

use std::collections::HashMap;

use cranelisp_types::{CranelispError, Span, Symbol, Type, TypeExpr, TypeId, TypeName};

/// Resolve a type expression to a concrete type.
///
/// `var_map` maps type variable names (e.g., `:a`) to their allocated TypeIds.
/// `known_types` maps type names to () for user-defined ADT lookup.
///
/// Ring 0 handles: Named, FnType, TypeVar.
/// SelfType and Applied return errors (Ring 2+ / Ring 1+).
pub fn resolve_type_expr(
    texpr: &TypeExpr,
    var_map: &HashMap<Symbol, TypeId>,
    known_types: &HashMap<TypeName, ()>,
    span: Span,
) -> Result<Type, CranelispError> {
    match texpr {
        TypeExpr::Named(name) => resolve_named(name, known_types, span),

        TypeExpr::FnType(params, ret) => {
            let param_types: Result<Vec<Type>, _> = params
                .iter()
                .map(|p| resolve_type_expr(p, var_map, known_types, span))
                .collect();
            let ret_type = resolve_type_expr(ret, var_map, known_types, span)?;
            Ok(Type::Fn(param_types?, Box::new(ret_type)))
        }

        TypeExpr::TypeVar(name) => {
            var_map
                .get(name)
                .map(|&id| Type::Var(id))
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!("unresolved type variable: :{name}"),
                    span,
                })
        }

        TypeExpr::SelfType => Err(CranelispError::TypeError {
            message: "Self type is not available in Ring 0".into(),
            span,
        }),

        TypeExpr::Applied(name, _args) => Err(CranelispError::TypeError {
            message: format!("parameterized type {name} is not available in Ring 0"),
            span,
        }),
    }
}

/// Resolve a named type: check primitives first, then user-defined ADTs.
fn resolve_named(
    name: &TypeName,
    known_types: &HashMap<TypeName, ()>,
    span: Span,
) -> Result<Type, CranelispError> {
    // Check primitive types first
    if let Some(ty) = Type::from_name(name) {
        return Ok(ty);
    }

    // Check user-defined ADT types
    if known_types.contains_key(name) {
        return Ok(Type::ADT(name.clone(), vec![]));
    }

    Err(CranelispError::TypeError {
        message: format!("unknown type: {name}"),
        span,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resolve_primitives() {
        let var_map = HashMap::new();
        let known = HashMap::new();
        let span = Span::SYNTHETIC;

        assert_eq!(
            resolve_type_expr(&TypeExpr::Named(TypeName::from("Int")), &var_map, &known, span)
                .unwrap(),
            Type::Int
        );
        assert_eq!(
            resolve_type_expr(&TypeExpr::Named(TypeName::from("Bool")), &var_map, &known, span)
                .unwrap(),
            Type::Bool
        );
        assert_eq!(
            resolve_type_expr(&TypeExpr::Named(TypeName::from("Float")), &var_map, &known, span)
                .unwrap(),
            Type::Float
        );
        assert_eq!(
            resolve_type_expr(
                &TypeExpr::Named(TypeName::from("String")),
                &var_map,
                &known,
                span
            )
            .unwrap(),
            Type::String
        );
    }

    #[test]
    fn test_resolve_unknown_type() {
        let var_map = HashMap::new();
        let known = HashMap::new();
        let span = Span::SYNTHETIC;

        let err = resolve_type_expr(
            &TypeExpr::Named(TypeName::from("Foo")),
            &var_map,
            &known,
            span,
        )
        .unwrap_err();
        assert!(err.message().contains("unknown type"));
    }

    #[test]
    fn test_resolve_user_defined_adt() {
        let var_map = HashMap::new();
        let mut known = HashMap::new();
        known.insert(TypeName::from("Color"), ());
        let span = Span::SYNTHETIC;

        let ty = resolve_type_expr(
            &TypeExpr::Named(TypeName::from("Color")),
            &var_map,
            &known,
            span,
        )
        .unwrap();
        assert_eq!(ty, Type::ADT(TypeName::from("Color"), vec![]));
    }

    #[test]
    fn test_resolve_fn_type() {
        let var_map = HashMap::new();
        let known = HashMap::new();
        let span = Span::SYNTHETIC;

        let fn_texpr = TypeExpr::FnType(
            vec![TypeExpr::Named(TypeName::from("Int"))],
            Box::new(TypeExpr::Named(TypeName::from("Bool"))),
        );
        let ty = resolve_type_expr(&fn_texpr, &var_map, &known, span).unwrap();
        assert_eq!(ty, Type::Fn(vec![Type::Int], Box::new(Type::Bool)));
    }

    #[test]
    fn test_resolve_type_var() {
        let mut var_map = HashMap::new();
        var_map.insert(Symbol::from("a"), 42u32);
        let known = HashMap::new();
        let span = Span::SYNTHETIC;

        let ty = resolve_type_expr(
            &TypeExpr::TypeVar(Symbol::from("a")),
            &var_map,
            &known,
            span,
        )
        .unwrap();
        assert_eq!(ty, Type::Var(42));
    }

    #[test]
    fn test_resolve_unknown_type_var() {
        let var_map = HashMap::new();
        let known = HashMap::new();
        let span = Span::SYNTHETIC;

        let err = resolve_type_expr(
            &TypeExpr::TypeVar(Symbol::from("a")),
            &var_map,
            &known,
            span,
        )
        .unwrap_err();
        assert!(err.message().contains("unresolved type variable"));
    }

    #[test]
    fn test_resolve_self_type_error() {
        let var_map = HashMap::new();
        let known = HashMap::new();
        let span = Span::SYNTHETIC;

        assert!(resolve_type_expr(&TypeExpr::SelfType, &var_map, &known, span).is_err());
    }
}
