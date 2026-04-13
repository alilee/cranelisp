//! Resolve TypeExpr (source annotations) to Type.
//!
//! All resolution returns Result, never panics (addresses audit HIGH-4).

use std::collections::HashMap;

use cranelisp_types::{CranelispError, FQTypeName, Span, Symbol, Type, TypeExpr, TypeId, TypeName};

/// Map of known user-defined type names to their FQTypeName and type parameter count.
/// Used by `resolve_type_expr` for ADT lookup and arity validation.
pub type KnownTypes = HashMap<TypeName, (FQTypeName, usize)>;

/// Resolve a type expression to a concrete type.
///
/// `var_map` maps type variable names (e.g., `:a`) to their allocated TypeIds.
/// `known_types` maps type names to their type parameter count.
pub fn resolve_type_expr(
    texpr: &TypeExpr,
    var_map: &HashMap<Symbol, TypeId>,
    known_types: &KnownTypes,
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
            message: "Self type not available outside trait implementations".into(),
            span,
        }),

        TypeExpr::Applied(name, args) => {
            resolve_applied(name, args, var_map, known_types, span)
        }
    }
}

/// Resolve a named type: check primitives first, then user-defined ADTs.
fn resolve_named(
    name: &TypeName,
    known_types: &KnownTypes,
    span: Span,
) -> Result<Type, CranelispError> {
    // Check primitive types first
    if let Some(ty) = Type::from_name(name) {
        return Ok(ty);
    }

    // Check user-defined ADT types (named without type args => zero-arg ADT)
    if let Some((fqtn, _arity)) = known_types.get(name) {
        return Ok(Type::ADT(fqtn.clone(), vec![]));
    }

    Err(CranelispError::TypeError {
        message: format!("unknown type: {name}"),
        span,
    })
}

/// Resolve an applied type constructor: `(Option Int)`, `(List :a)`.
///
/// Validates that the number of type arguments matches the declared
/// type parameter count. Returns `TypeError` on arity mismatch.
fn resolve_applied(
    name: &TypeName,
    args: &[TypeExpr],
    var_map: &HashMap<Symbol, TypeId>,
    known_types: &KnownTypes,
    span: Span,
) -> Result<Type, CranelispError> {
    let (fqtn, expected_arity) = known_types.get(name).ok_or_else(|| {
        CranelispError::TypeError {
            message: format!("unknown type: {name}"),
            span,
        }
    })?;

    if args.len() != *expected_arity {
        return Err(CranelispError::TypeError {
            message: format!(
                "type {name} expects {expected_arity} type argument(s), got {}",
                args.len()
            ),
            span,
        });
    }

    let resolved_args: Vec<Type> = args
        .iter()
        .map(|a| resolve_type_expr(a, var_map, known_types, span))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(Type::ADT(fqtn.clone(), resolved_args))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::ModuleFullPath;

    /// Test helper: create an FQTypeName in a "test" module.
    fn test_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("test"), TypeName::from(name))
    }

    // spec: 03-types §3.1 — resolve primitive type names to Type values
    #[test]
    fn test_resolve_primitives() {
        let var_map = HashMap::new();
        let known = KnownTypes::new();
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

    // spec: 03-types §3.9.3 — unknown type name produces error
    #[test]
    fn test_resolve_unknown_type() {
        let var_map = HashMap::new();
        let known = KnownTypes::new();
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

    // spec: 03-types §3.2.2 — resolve user-defined ADT name to ADT type
    #[test]
    fn test_resolve_user_defined_adt() {
        let var_map = HashMap::new();
        let mut known = KnownTypes::new();
        known.insert(TypeName::from("Color"), (test_fqtn("Color"), 0));
        let span = Span::SYNTHETIC;

        let ty = resolve_type_expr(
            &TypeExpr::Named(TypeName::from("Color")),
            &var_map,
            &known,
            span,
        )
        .unwrap();
        assert_eq!(ty, Type::ADT(test_fqtn("Color"), vec![]));
    }

    // spec: 03-types §3.2.1 — resolve function type expression
    #[test]
    fn test_resolve_fn_type() {
        let var_map = HashMap::new();
        let known = KnownTypes::new();
        let span = Span::SYNTHETIC;

        let fn_texpr = TypeExpr::FnType(
            vec![TypeExpr::Named(TypeName::from("Int"))],
            Box::new(TypeExpr::Named(TypeName::from("Bool"))),
        );
        let ty = resolve_type_expr(&fn_texpr, &var_map, &known, span).unwrap();
        assert_eq!(ty, Type::Fn(vec![Type::Int], Box::new(Type::Bool)));
    }

    // spec: 03-types §3.3 — resolve type variable to Var from var_map
    #[test]
    fn test_resolve_type_var() {
        let mut var_map = HashMap::new();
        var_map.insert(Symbol::from("a"), 42u32);
        let known = KnownTypes::new();
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

    // spec: 03-types §3.3 — unresolved type variable produces error
    #[test]
    fn test_resolve_unknown_type_var() {
        let var_map = HashMap::new();
        let known = KnownTypes::new();
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

    // spec: 07-traits §7.1.1 — Self type outside trait context is error
    #[test]
    fn test_resolve_self_type_error() {
        let var_map = HashMap::new();
        let known = KnownTypes::new();
        let span = Span::SYNTHETIC;

        assert!(resolve_type_expr(&TypeExpr::SelfType, &var_map, &known, span).is_err());
    }

    // spec: 03-types §3.2.2 — resolve applied type :(Option Int) to ADT
    #[test]
    fn test_resolve_applied_valid() {
        let var_map = HashMap::new();
        let mut known = KnownTypes::new();
        known.insert(TypeName::from("Option"), (test_fqtn("Option"), 1));
        let span = Span::SYNTHETIC;

        let texpr = TypeExpr::Applied(
            TypeName::from("Option"),
            vec![TypeExpr::Named(TypeName::from("Int"))],
        );
        let ty = resolve_type_expr(&texpr, &var_map, &known, span).unwrap();
        assert_eq!(
            ty,
            Type::ADT(test_fqtn("Option"), vec![Type::Int])
        );
    }

    // spec: 03-types §3.2.2 — applied type with wrong arity fails
    #[test]
    fn test_resolve_applied_arity_mismatch() {
        let var_map = HashMap::new();
        let mut known = KnownTypes::new();
        known.insert(TypeName::from("Option"), (test_fqtn("Option"), 1));
        let span = Span::SYNTHETIC;

        // Too many args
        let texpr = TypeExpr::Applied(
            TypeName::from("Option"),
            vec![
                TypeExpr::Named(TypeName::from("Int")),
                TypeExpr::Named(TypeName::from("Bool")),
            ],
        );
        let err = resolve_type_expr(&texpr, &var_map, &known, span).unwrap_err();
        assert!(err.message().contains("expects 1 type argument"));

        // Too few args (zero)
        let texpr_zero = TypeExpr::Applied(TypeName::from("Option"), vec![]);
        let err = resolve_type_expr(&texpr_zero, &var_map, &known, span).unwrap_err();
        assert!(err.message().contains("expects 1 type argument"));
    }

    // spec: 03-types §3.9.3 — applied unknown type name fails
    #[test]
    fn test_resolve_applied_unknown_type() {
        let var_map = HashMap::new();
        let known = KnownTypes::new();
        let span = Span::SYNTHETIC;

        let texpr = TypeExpr::Applied(
            TypeName::from("Foo"),
            vec![TypeExpr::Named(TypeName::from("Int"))],
        );
        let err = resolve_type_expr(&texpr, &var_map, &known, span).unwrap_err();
        assert!(err.message().contains("unknown type"));
    }

    // spec: 03-types §3.3 — applied type with type variable argument
    #[test]
    fn test_resolve_applied_with_type_var() {
        let mut var_map = HashMap::new();
        var_map.insert(Symbol::from("a"), 5u32);
        let mut known = KnownTypes::new();
        known.insert(TypeName::from("Option"), (test_fqtn("Option"), 1));
        let span = Span::SYNTHETIC;

        let texpr = TypeExpr::Applied(
            TypeName::from("Option"),
            vec![TypeExpr::TypeVar(Symbol::from("a"))],
        );
        let ty = resolve_type_expr(&texpr, &var_map, &known, span).unwrap();
        assert_eq!(
            ty,
            Type::ADT(test_fqtn("Option"), vec![Type::Var(5)])
        );
    }

    // spec: 03-types §3.2.2 — applied type with multiple parameters
    #[test]
    fn test_resolve_applied_multi_param() {
        let var_map = HashMap::new();
        let mut known = KnownTypes::new();
        known.insert(TypeName::from("Either"), (test_fqtn("Either"), 2));
        let span = Span::SYNTHETIC;

        let texpr = TypeExpr::Applied(
            TypeName::from("Either"),
            vec![
                TypeExpr::Named(TypeName::from("Int")),
                TypeExpr::Named(TypeName::from("String")),
            ],
        );
        let ty = resolve_type_expr(&texpr, &var_map, &known, span).unwrap();
        assert_eq!(
            ty,
            Type::ADT(
                test_fqtn("Either"),
                vec![Type::Int, Type::String]
            )
        );
    }
}
