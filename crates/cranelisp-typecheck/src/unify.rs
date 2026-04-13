//! Unification engine for Hindley-Milner type inference.
//!
//! Core functions take explicit `&mut Subst` and `&mut TypeId` parameters
//! (borrow-splitting pattern) to avoid &mut self conflicts in the TypeChecker.

use cranelisp_types::{CranelispError, Span, Subst, Type, TypeId, apply, free_vars};

/// Unify two types, updating the substitution.
///
/// Uses `Span::SYNTHETIC` for error origins; callers wrap with real spans.
pub fn unify(subst: &mut Subst, t1: &Type, t2: &Type) -> Result<(), CranelispError> {
    let t1 = apply(subst, t1);
    let t2 = apply(subst, t2);

    match (&t1, &t2) {
        // Identical primitives
        (Type::Int, Type::Int)
        | (Type::Bool, Type::Bool)
        | (Type::Float, Type::Float)
        | (Type::String, Type::String) => Ok(()),

        // Var on left: bind
        (Type::Var(id), _) => bind_var(subst, *id, &t2),

        // Var on right: bind
        (_, Type::Var(id)) => bind_var(subst, *id, &t1),

        // Function types: check arity, unify pairwise
        (Type::Fn(params1, ret1), Type::Fn(params2, ret2)) => {
            if params1.len() != params2.len() {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "function arity mismatch: expected {} parameters, got {}",
                        params1.len(),
                        params2.len()
                    ),
                    span: Span::SYNTHETIC,
                });
            }
            for (p1, p2) in params1.iter().zip(params2.iter()) {
                unify(subst, p1, p2)?;
            }
            unify(subst, ret1, ret2)
        }

        // ADT types: check name, unify args pairwise
        (Type::ADT(name1, args1), Type::ADT(name2, args2)) => {
            if name1 != name2 {
                return Err(CranelispError::TypeError {
                    message: format!("type mismatch: {name1} vs {name2}"),
                    span: Span::SYNTHETIC,
                });
            }
            if args1.len() != args2.len() {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "type argument count mismatch for {name1}: expected {}, got {}",
                        args1.len(),
                        args2.len()
                    ),
                    span: Span::SYNTHETIC,
                });
            }
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                unify(subst, a1, a2)?;
            }
            Ok(())
        }

        // TyConApp(f, args) vs ADT(name, args2): bind f -> ADT(name, []), unify args
        (Type::TyConApp(f_id, args1), Type::ADT(name, args2))
        | (Type::ADT(name, args2), Type::TyConApp(f_id, args1)) => {
            let f_id = *f_id;
            if args1.len() != args2.len() {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "type constructor arity mismatch: expected {} args, got {}",
                        args1.len(),
                        args2.len()
                    ),
                    span: Span::SYNTHETIC,
                });
            }
            // Bind constructor variable to bare ADT constructor
            bind_var(subst, f_id, &Type::ADT(name.clone(), vec![]))?;
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                unify(subst, a1, a2)?;
            }
            Ok(())
        }

        // TyConApp(f1, args1) vs TyConApp(f2, args2): bind f1 -> Var(f2), unify args
        (Type::TyConApp(f1, args1), Type::TyConApp(f2, args2)) => {
            let f1 = *f1;
            let f2 = *f2;
            if args1.len() != args2.len() {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "type constructor arity mismatch: expected {} args, got {}",
                        args1.len(),
                        args2.len()
                    ),
                    span: Span::SYNTHETIC,
                });
            }
            if f1 != f2 {
                bind_var(subst, f1, &Type::Var(f2))?;
            }
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                unify(subst, a1, a2)?;
            }
            Ok(())
        }

        // Everything else is a type mismatch
        _ => Err(CranelispError::TypeError {
            message: format!("type mismatch: expected {t1}, got {t2}"),
            span: Span::SYNTHETIC,
        }),
    }
}

/// Bind a type variable to a type, with occurs check.
fn bind_var(subst: &mut Subst, id: TypeId, ty: &Type) -> Result<(), CranelispError> {
    // Var(id) unifying with itself is a no-op
    if let Type::Var(other_id) = ty
        && id == *other_id
    {
        return Ok(());
    }

    // Occurs check: prevent infinite types
    if occurs_check(subst, id, ty) {
        return Err(CranelispError::TypeError {
            message: format!("infinite type: t{id} occurs in {ty}"),
            span: Span::SYNTHETIC,
        });
    }

    subst.insert(id, ty.clone());
    Ok(())
}

/// Check if type variable `id` occurs free in `ty` (after applying subst).
pub fn occurs_check(subst: &Subst, id: TypeId, ty: &Type) -> bool {
    let resolved = apply(subst, ty);
    let fv = free_vars(&resolved);
    fv.contains(&id)
}

/// Generate a fresh type variable, incrementing the counter.
pub fn fresh_var(next_id: &mut TypeId) -> Type {
    let id = *next_id;
    *next_id += 1;
    Type::Var(id)
}

/// Generate a fresh type variable and return both the type and the id.
/// Ring 0: not yet used in production (reserved for Ring 2 constrained polymorphism).
#[allow(dead_code)]
pub fn fresh_var_id(next_id: &mut TypeId) -> (Type, TypeId) {
    let id = *next_id;
    *next_id += 1;
    (Type::Var(id), id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{FQTypeName, ModuleFullPath, TypeName};

    /// Test helper: create an FQTypeName in a "test" module.
    fn test_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("test"), TypeName::from(name))
    }

    // spec: 03-types §3.8.1 — trivial unification of identical primitives
    #[test]
    fn test_unify_same_primitives() {
        let mut subst = Subst::new();
        assert!(unify(&mut subst, &Type::Int, &Type::Int).is_ok());
        assert!(unify(&mut subst, &Type::Bool, &Type::Bool).is_ok());
        assert!(unify(&mut subst, &Type::Float, &Type::Float).is_ok());
        assert!(unify(&mut subst, &Type::String, &Type::String).is_ok());
    }

    // spec: 03-types §3.8.6 — incompatible primitive types fail unification
    #[test]
    fn test_unify_different_primitives_fails() {
        let mut subst = Subst::new();
        assert!(unify(&mut subst, &Type::Int, &Type::Bool).is_err());
        assert!(unify(&mut subst, &Type::Float, &Type::String).is_err());
    }

    // spec: 03-types §3.8.2 — variable binding: Var(id) binds to concrete type
    #[test]
    fn test_unify_var_with_concrete() {
        let mut subst = Subst::new();
        unify(&mut subst, &Type::Var(0), &Type::Int).unwrap();
        assert_eq!(apply(&subst, &Type::Var(0)), Type::Int);
    }

    // spec: 03-types §3.8.2 — variable binding is symmetric
    #[test]
    fn test_unify_concrete_with_var() {
        let mut subst = Subst::new();
        unify(&mut subst, &Type::Int, &Type::Var(0)).unwrap();
        assert_eq!(apply(&subst, &Type::Var(0)), Type::Int);
    }

    // spec: 03-types §3.8.2 — two distinct type variables unify by merging
    #[test]
    fn test_unify_var_with_var() {
        let mut subst = Subst::new();
        unify(&mut subst, &Type::Var(0), &Type::Var(1)).unwrap();
        // One should be bound to the other
        let t0 = apply(&subst, &Type::Var(0));
        let t1 = apply(&subst, &Type::Var(1));
        assert_eq!(t0, t1);
    }

    // spec: 03-types §3.8.2 — same variable unifies with itself (no-op)
    #[test]
    fn test_unify_var_with_self() {
        let mut subst = Subst::new();
        // Var(0) unifying with Var(0) is ok (no binding needed)
        assert!(unify(&mut subst, &Type::Var(0), &Type::Var(0)).is_ok());
        assert!(subst.is_empty());
    }

    // spec: 03-types §3.8.3 — function types unify pairwise by params and return
    #[test]
    fn test_unify_fn_types() {
        let mut subst = Subst::new();
        let fn1 = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
        let fn2 = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
        assert!(unify(&mut subst, &fn1, &fn2).is_ok());
    }

    // spec: 03-types §3.8.3 — function type unification resolves type variables
    #[test]
    fn test_unify_fn_types_with_vars() {
        let mut subst = Subst::new();
        let fn1 = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(1)));
        let fn2 = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
        unify(&mut subst, &fn1, &fn2).unwrap();
        assert_eq!(apply(&subst, &Type::Var(0)), Type::Int);
        assert_eq!(apply(&subst, &Type::Var(1)), Type::Bool);
    }

    // spec: 03-types §3.8.3 — function arity mismatch fails unification
    #[test]
    fn test_unify_fn_arity_mismatch() {
        let mut subst = Subst::new();
        let fn1 = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let fn2 = Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int));
        let err = unify(&mut subst, &fn1, &fn2).unwrap_err();
        assert!(err.message().contains("arity mismatch"));
    }

    // spec: 03-types §3.8.4 — ADTs with same name unify
    #[test]
    fn test_unify_adt_same_name() {
        let mut subst = Subst::new();
        let a1 = Type::ADT(test_fqtn("Color"), vec![]);
        let a2 = Type::ADT(test_fqtn("Color"), vec![]);
        assert!(unify(&mut subst, &a1, &a2).is_ok());
    }

    // spec: 03-types §3.8.4 — ADTs with different names fail unification
    #[test]
    fn test_unify_adt_different_names() {
        let mut subst = Subst::new();
        let a1 = Type::ADT(test_fqtn("Color"), vec![]);
        let a2 = Type::ADT(test_fqtn("Shape"), vec![]);
        let err = unify(&mut subst, &a1, &a2).unwrap_err();
        assert!(err.message().contains("Color"));
        assert!(err.message().contains("Shape"));
    }

    // spec: 03-types §3.8.2 — occurs check prevents infinite types
    #[test]
    fn test_occurs_check_prevents_infinite_type() {
        let mut subst = Subst::new();
        // t0 = Fn([t0], t0) would be infinite
        let infinite_fn = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0)));
        let err = unify(&mut subst, &Type::Var(0), &infinite_fn).unwrap_err();
        assert!(err.message().contains("infinite type"));
    }

    // spec: 03-types §3.8.2 — occurs check detects variable in function type
    #[test]
    fn test_occurs_check_function() {
        let subst = Subst::new();
        let ty = Type::Fn(vec![Type::Var(0)], Box::new(Type::Int));
        assert!(occurs_check(&subst, 0, &ty));
        assert!(!occurs_check(&subst, 1, &ty));
    }

    // spec: 03-types §3.5.1 — fresh_var creates unique unification variables
    #[test]
    fn test_fresh_var() {
        let mut next_id: TypeId = 0;
        let t1 = fresh_var(&mut next_id);
        let t2 = fresh_var(&mut next_id);
        assert_eq!(t1, Type::Var(0));
        assert_eq!(t2, Type::Var(1));
        assert_eq!(next_id, 2);
    }

    // spec: 03-types §3.5.1 — fresh_var_id returns both type and id
    #[test]
    fn test_fresh_var_id() {
        let mut next_id: TypeId = 5;
        let (ty, id) = fresh_var_id(&mut next_id);
        assert_eq!(ty, Type::Var(5));
        assert_eq!(id, 5);
        assert_eq!(next_id, 6);
    }

    // spec: 03-types §3.5.1 — apply resolves transitive variable chains
    #[test]
    fn test_unify_transitive_vars() {
        let mut subst = Subst::new();
        // t0 = t1, t1 = Int => t0 = Int
        unify(&mut subst, &Type::Var(0), &Type::Var(1)).unwrap();
        unify(&mut subst, &Type::Var(1), &Type::Int).unwrap();
        assert_eq!(apply(&subst, &Type::Var(0)), Type::Int);
    }

    // spec: 03-types §3.8.3 — function param type mismatch fails unification
    #[test]
    fn test_unify_fn_param_type_mismatch() {
        let mut subst = Subst::new();
        let fn1 = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let fn2 = Type::Fn(vec![Type::Bool], Box::new(Type::Int));
        assert!(unify(&mut subst, &fn1, &fn2).is_err());
    }
}
