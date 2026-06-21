//! Unification engine for Hindley-Milner type inference.
//!
//! Core functions take explicit `&mut Subst` and `&mut TypeId` parameters
//! (borrow-splitting pattern) to avoid &mut self conflicts in the TypeChecker.

use cranelisp_types::{ErrorLocation, CranelispError, Span, Subst, Type, TypeId, apply, free_vars};

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
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
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
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            }
            if args1.len() != args2.len() {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "type argument count mismatch for {name1}: expected {}, got {}",
                        args1.len(),
                        args2.len()
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
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
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
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
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
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
            message: format!(
                "type mismatch: expected {}, got {}",
                format_type_fq(&t1),
                format_type_fq(&t2)
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
    }
}

/// Render a type with primitive variants fully qualified (`primitives/Int`),
/// for use ONLY in typecheck error-message rendering (per `repl/spec.md` §5.3,
/// design `typecheck.md` §8.3).
///
/// Crate-private and the structural twin of `Type`'s bare `Display` impl: it
/// maps the four primitive variants to their canonical `primitives/…` strings,
/// renders `Type::ADT` through `FQTypeName`'s already-qualified Display, and
/// recurses on `Fn`/args. `Var`/`TyConApp` are rendered exactly as `Display`
/// does (type variables are not the §5.3 FQ concern).
///
/// This deliberately duplicates the primitive→`primitives/…` mapping rather
/// than reusing the value-display path (`src/display.rs`) — the two renderers
/// are kept structurally distinct, converging only on the FQ output convention
/// (design §8.3, /arch Phase-2 keep-distinct advisory).
fn format_type_fq(ty: &Type) -> String {
    match ty {
        Type::Int => "primitives/Int".to_string(),
        Type::Bool => "primitives/Bool".to_string(),
        Type::String => "primitives/String".to_string(),
        Type::Float => "primitives/Float".to_string(),
        Type::Fn(params, ret) => {
            let params_str = params
                .iter()
                .map(format_type_fq)
                .collect::<Vec<_>>()
                .join(" ");
            format!("(Fn [{}] {})", params_str, format_type_fq(ret))
        }
        Type::ADT(fqtn, args) => {
            if args.is_empty() {
                format!("{fqtn}")
            } else {
                let args_str = args
                    .iter()
                    .map(format_type_fq)
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("({fqtn} {args_str})")
            }
        }
        Type::Var(id) => format!("t{id}"),
        Type::TyConApp(id, args) => {
            let args_str = args
                .iter()
                .map(format_type_fq)
                .collect::<Vec<_>>()
                .join(" ");
            if args_str.is_empty() {
                format!("(TyCon t{id})")
            } else {
                format!("(TyCon t{id} {args_str})")
            }
        }
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
            message: format!("infinite type: t{id} occurs in {}", format_type_fq(ty)),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
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
mod tests;
