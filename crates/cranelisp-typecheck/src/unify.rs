//! Unification engine for Hindley-Milner type inference.
//!
//! Core functions take explicit `&mut Subst` and `&mut TypeId` parameters
//! (borrow-splitting pattern) to avoid &mut self conflicts in the TypeChecker.

use std::collections::HashSet;

use cranelisp_types::{
    ErrorLocation, CranelispError, PrimitiveNaming, Span, Subst, Type, TypeId, VarNaming, apply,
    free_vars, render_type,
};

/// Unify two types honouring the **rigid written-type-variable** asymmetry
/// (spec §3.3 [S109]).
///
/// `rigid` is the set of `TypeId`s that are RIGID skolems — written free type
/// variables that are *fixed-but-unknown* within the definition body currently
/// being checked (see `CheckState::rigid_vars`). The asymmetry the checker MUST
/// honour, realized entirely in [`unify_var`]:
///
/// - a **flexible** inference variable (any `TypeId` NOT in `rigid`) MAY unify
///   with a rigid one — the flexible side binds to the rigid var (this is how an
///   unannotated parameter *acquires* a written type);
/// - a **rigid** variable MUST NOT unify with a concrete type (**skolem-escape**)
///   nor with a *distinct* rigid variable; only with the *same* rigid var.
///
/// The set is threaded through every recursive arm so the guard reaches into
/// `Fn`/`ADT` arguments (e.g. `(Box a)` with rigid `a`).
pub fn unify_with_rigid(
    subst: &mut Subst,
    rigid: &HashSet<TypeId>,
    t1: &Type,
    t2: &Type,
) -> Result<(), CranelispError> {
    let t1 = apply(subst, t1);
    let t2 = apply(subst, t2);

    match (&t1, &t2) {
        // Identical primitives
        (Type::Int, Type::Int)
        | (Type::Bool, Type::Bool)
        | (Type::Float, Type::Float)
        | (Type::String, Type::String) => Ok(()),

        // Var on left: bind (rigid-aware)
        (Type::Var(id), _) => unify_var(subst, rigid, *id, &t2),

        // Var on right: bind (rigid-aware)
        (_, Type::Var(id)) => unify_var(subst, rigid, *id, &t1),

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
                unify_with_rigid(subst, rigid, p1, p2)?;
            }
            unify_with_rigid(subst, rigid, ret1, ret2)
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
                unify_with_rigid(subst, rigid, a1, a2)?;
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
            // Bind constructor variable to bare ADT constructor. HKT constructor
            // variables are never written skolems, so they are never in `rigid`.
            bind_var(subst, f_id, &Type::ADT(name.clone(), vec![]))?;
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                unify_with_rigid(subst, rigid, a1, a2)?;
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
                unify_with_rigid(subst, rigid, a1, a2)?;
            }
            Ok(())
        }

        // Everything else is a type mismatch. Error-message rendering uses the
        // shared `render_type` walk with `Qualified` primitives (`primitives/Int`,
        // repl/spec.md §5.3) + `Numbered` vars — reproducing the former
        // crate-private `format_type_fq` byte-for-byte (S87 consolidation,
        // FIXME 0420; the cross-crate `Type` re-walk is eliminated).
        _ => Err(CranelispError::TypeError {
            message: format!(
                "type mismatch: expected {}, got {}",
                render_type(&t1, PrimitiveNaming::Qualified, VarNaming::Numbered),
                render_type(&t2, PrimitiveNaming::Qualified, VarNaming::Numbered),
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
    }
}

/// Unify a type variable `id` (already substitution-resolved to an unbound
/// `Var`) with `other` (already substitution-resolved), honouring the rigid
/// asymmetry (spec §3.3 [S109], MUST-4).
///
/// - If `id` is FLEXIBLE (not in `rigid`): ordinary [`bind_var`] — binds `id` to
///   `other`. When `other` is itself a rigid var, this binds the flexible side to
///   the rigid one, which is exactly how a parameter *acquires* a written type.
/// - If `id` is RIGID: it may unify only with the *same* rigid var. Unifying it
///   with a concrete type, or with a *distinct* rigid var, is a **skolem-escape**
///   type error (the body may not choose what a written variable is). When
///   `other` is a *flexible* var, the flexible side binds to this rigid var
///   (again the acquisition direction — never binding the rigid var itself).
fn unify_var(
    subst: &mut Subst,
    rigid: &HashSet<TypeId>,
    id: TypeId,
    other: &Type,
) -> Result<(), CranelispError> {
    if rigid.contains(&id) {
        match other {
            // Same rigid variable — trivially unifies.
            Type::Var(other_id) if *other_id == id => Ok(()),
            // A DISTINCT rigid variable — skolem-escape (two written variables
            // are independent fixed-but-unknowns; unifying them would collapse
            // `(Fn [a b] …)` to `(Fn [a a] …)`).
            Type::Var(other_id) if rigid.contains(other_id) => {
                Err(skolem_escape_distinct_rigid())
            }
            // A FLEXIBLE variable — bind the flexible side to this rigid var (the
            // parameter-acquisition direction; the rigid var itself is never bound).
            Type::Var(other_id) => bind_var(subst, *other_id, &Type::Var(id)),
            // A concrete type — skolem-escape (the body may not pin the written
            // variable to a concrete type, by ascription OR by use).
            other => Err(skolem_escape_concrete(other)),
        }
    } else {
        bind_var(subst, id, other)
    }
}

/// Skolem-escape error: a rigid written type variable was forced to a concrete
/// type. Deliberately worded to be a plain type error — never an "unknown type"
/// (§3.3 MUST-2). Span is `SYNTHETIC`; the checker re-wraps with the real span.
fn skolem_escape_concrete(other: &Type) -> CranelispError {
    CranelispError::TypeError {
        message: format!(
            "type mismatch: a written type variable is rigid within its definition \
             and cannot be constrained to the concrete type {} — it is fixed-but-unknown, \
             chosen only by the caller at each use site (spec §3.3)",
            render_type(other, PrimitiveNaming::Qualified, VarNaming::Numbered),
        ),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    }
}

/// Skolem-escape error: two *distinct* rigid written type variables were forced
/// to unify. A plain type error, never "unknown type" (§3.3 MUST-2/MUST-4).
fn skolem_escape_distinct_rigid() -> CranelispError {
    CranelispError::TypeError {
        message: "type mismatch: two distinct rigid written type variables cannot \
                  be unified — each is an independent rigid skolem (spec §3.3)"
            .to_string(),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
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
            message: format!(
                "infinite type: t{id} occurs in {}",
                render_type(ty, PrimitiveNaming::Qualified, VarNaming::Numbered)
            ),
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
