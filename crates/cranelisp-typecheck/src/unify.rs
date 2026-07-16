//! Unification engine for Hindley-Milner type inference.
//!
//! Core functions take explicit `&mut Subst` and `&mut TypeId` parameters
//! (borrow-splitting pattern) to avoid &mut self conflicts in the TypeChecker.

use std::collections::HashSet;

use cranelisp_types::{
    ErrorLocation, CranelispError, PrimitiveNaming, Span, Subst, Type, TypeId, VarNaming, apply,
    free_vars, render_type,
};

/// Unify two types honouring the **constraint-abstract (rigid) type-variable**
/// asymmetry (spec §3.3.2 [S109] W6.3).
///
/// `rigid` is the set of `TypeId`s held ABSTRACT for the definition body being
/// checked — under W6.3 these are ONLY the ASSERTED-constraint parameter vars
/// (`:C x`), NOT bare written vars (a bare `:a` is an ordinary flexible
/// inference var; W6.3 backs out the W6.2 rigid-bare model). See
/// `CheckState::rigid_vars`. The asymmetry, realized entirely in [`unify_var`]:
///
/// - a **flexible** inference variable (any `TypeId` NOT in `rigid`) MAY unify
///   with a rigid one — the flexible side binds to the rigid var (how a use
///   acquires the constraint-abstract type);
/// - a **rigid** variable MUST NOT unify with a **concrete type** — the body
///   narrowing a held-abstract constraint var is a **skolem escape** (row 6);
/// - two **rigid** variables MERGE (both stay abstract — `(defn assert-eq
///   [:Eq a :Eq b] (= a b))` is a constraint-polymorphic scheme, not an error).
///
/// The set is threaded through every recursive arm so the guard reaches into
/// `Fn`/`ADT` arguments (e.g. `(Box a)` with a constraint-abstract `a`).
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
/// `Var`) with `other` (already substitution-resolved), honouring the
/// constraint-abstract asymmetry (spec §3.3.2 [S109] W6.3).
///
/// - If `id` is FLEXIBLE (not in `rigid`): ordinary [`bind_var`] — binds `id` to
///   `other`. When `other` is itself a rigid var, this binds the flexible side to
///   the rigid one, exactly how a use *acquires* the constraint-abstract type.
/// - If `id` is RIGID (a constraint-abstract param var): unifying it with a
///   **concrete type** is a **skolem escape** (the body may not narrow a
///   held-abstract constraint to a concrete type, row 6). Another rigid var
///   MERGES (both stay abstract); a *flexible* var binds to this rigid var (the
///   acquisition direction — the rigid var itself is never bound to a concrete).
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
            // Another rigid (constraint-abstract) variable — MERGE, not escape.
            // Two held-abstract constraint params unifying (`(defn assert-eq
            // [:Eq a :Eq b] (= a b))`) stay abstract: binding one to the other
            // keeps a constraint-polymorphic scheme. (W6.3 removes the W6.2
            // distinct-rigid-escape rule, which existed only to keep BARE
            // written vars distinct — bare vars are no longer rigid, and two
            // bare vars tied by the body now MERGE too, spec §3.3.1 C-1.)
            Type::Var(other_id) if rigid.contains(other_id) => {
                bind_var(subst, id, &Type::Var(*other_id))
            }
            // A FLEXIBLE variable — bind the flexible side to this rigid var (the
            // parameter-acquisition direction; the rigid var itself is never bound).
            Type::Var(other_id) => bind_var(subst, *other_id, &Type::Var(id)),
            // A concrete type — skolem-escape (spec §3.3.2 MUST (b), row 6): a
            // constraint at a parameter position is held abstract over its trait
            // for the body-check, so the body narrowing it to a concrete type
            // (by ascription OR by use) is rejected — the caller relies on the
            // CONSTRAINT, not a concrete choice made by the body.
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
///
/// Test-only since FIXME 0590: the last production caller (the deleted
/// `resolve_trait_type_expr` mirror) routed through the atomic `&self`
/// allocator; the remaining users are unit tests + `scheme::instantiate`
/// (itself `#[cfg(test)]`).
#[cfg(test)]
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
