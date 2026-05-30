//! Scheme operations: instantiation, generalization, monomorphic scheme.

use std::collections::HashMap;

use cranelisp_types::{Scheme, Subst, Type, TypeId, apply, free_vars};

#[cfg(test)]
use crate::unify::fresh_var;

/// Create a monomorphic scheme (no quantified variables).
pub fn mono(ty: Type) -> Scheme {
    Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty,
    }
}

/// Instantiate a scheme by replacing each quantified variable with a fresh variable.
///
/// Takes `next_id` explicitly (borrow-splitting pattern).
#[cfg(test)]
pub fn instantiate(scheme: &Scheme, next_id: &mut TypeId) -> Type {
    if scheme.type_vars.is_empty() {
        return scheme.ty.clone();
    }

    let mut inst_subst = Subst::new();
    for &var_id in &scheme.type_vars {
        let fresh = fresh_var(next_id);
        inst_subst.insert(var_id, fresh);
    }

    apply(&inst_subst, &scheme.ty)
}

/// Generalize a type into a scheme by quantifying over free variables
/// that are NOT free in the environment (scope stack + symbol table free vars).
///
/// `subst` is applied to `ty` before collecting free vars.
/// `env_free_vars` should contain all free vars from the scope stack and symbol table.
pub fn generalize(subst: &Subst, ty: &Type, env_free_vars: &std::collections::HashSet<TypeId>) -> Scheme {
    let resolved = apply(subst, ty);
    let ty_fv = free_vars(&resolved);

    // Quantify variables that are free in the type but NOT in the environment
    let mut type_vars: Vec<TypeId> = ty_fv
        .into_iter()
        .filter(|v| !env_free_vars.contains(v))
        .collect();

    // Sort for deterministic output
    type_vars.sort();

    Scheme {
        type_vars,
        constraints: HashMap::new(),
        ty: resolved,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // spec: 03-types §3.4 — monomorphic scheme has no quantified vars
    #[test]
    fn test_mono_scheme() {
        let s = mono(Type::Int);
        assert!(s.type_vars.is_empty());
        assert!(s.constraints.is_empty());
        assert_eq!(s.ty, Type::Int);
    }

    // spec: 03-types §3.5.1 — instantiate on monomorphic scheme is identity
    #[test]
    fn test_instantiate_mono() {
        let s = mono(Type::Int);
        let mut next_id: TypeId = 0;
        let ty = instantiate(&s, &mut next_id);
        assert_eq!(ty, Type::Int);
        // No fresh vars created for monomorphic scheme
        assert_eq!(next_id, 0);
    }

    // spec: 03-types §3.5.1 — instantiate replaces quantified vars with fresh vars
    #[test]
    fn test_instantiate_polymorphic() {
        // forall [0]. Fn([t0], t0) -- identity
        let s = Scheme {
            type_vars: vec![0],
            constraints: HashMap::new(),
            ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
        };
        let mut next_id: TypeId = 10;
        let ty = instantiate(&s, &mut next_id);
        // Should have replaced t0 with t10
        assert_eq!(
            ty,
            Type::Fn(vec![Type::Var(10)], Box::new(Type::Var(10)))
        );
        assert_eq!(next_id, 11);
    }

    // spec: 03-types §3.5.1 — instantiate handles multiple quantified vars
    #[test]
    fn test_instantiate_multi_var() {
        // forall [0, 1]. Fn([t0, t1], t0)
        let s = Scheme {
            type_vars: vec![0, 1],
            constraints: HashMap::new(),
            ty: Type::Fn(vec![Type::Var(0), Type::Var(1)], Box::new(Type::Var(0))),
        };
        let mut next_id: TypeId = 5;
        let ty = instantiate(&s, &mut next_id);
        assert_eq!(
            ty,
            Type::Fn(vec![Type::Var(5), Type::Var(6)], Box::new(Type::Var(5)))
        );
        assert_eq!(next_id, 7);
    }

    // spec: 03-types §3.5.1 — generalize quantifies all free vars not in env
    #[test]
    fn test_generalize_all_free() {
        let subst = Subst::new();
        let env_fv = std::collections::HashSet::new();
        // Fn([t0], t0) with no env vars -> forall [0]. Fn([t0], t0)
        let ty = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0)));
        let scheme = generalize(&subst, &ty, &env_fv);
        assert_eq!(scheme.type_vars, vec![0]);
    }

    // spec: 03-types §3.5.1 — generalize skips vars free in the environment
    #[test]
    fn test_generalize_some_in_env() {
        let subst = Subst::new();
        let mut env_fv = std::collections::HashSet::new();
        env_fv.insert(0); // t0 is free in env
        // Fn([t0], t1) with t0 in env -> forall [1]. Fn([t0], t1)
        let ty = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(1)));
        let scheme = generalize(&subst, &ty, &env_fv);
        assert_eq!(scheme.type_vars, vec![1]);
    }

    // spec: 03-types §3.4 — generalize on concrete type produces mono scheme
    #[test]
    fn test_generalize_none_free() {
        let subst = Subst::new();
        let env_fv = std::collections::HashSet::new();
        // Int has no free vars -> mono
        let scheme = generalize(&subst, &Type::Int, &env_fv);
        assert!(scheme.type_vars.is_empty());
        assert_eq!(scheme.ty, Type::Int);
    }

    // spec: 03-types §3.5.1 — generalize applies substitution before quantifying
    #[test]
    fn test_generalize_applies_subst() {
        let mut subst = Subst::new();
        subst.insert(0, Type::Int);
        let env_fv = std::collections::HashSet::new();
        let ty = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(1)));
        let scheme = generalize(&subst, &ty, &env_fv);
        // t0 resolved to Int, t1 is still free
        assert_eq!(scheme.type_vars, vec![1]);
        assert_eq!(
            scheme.ty,
            Type::Fn(vec![Type::Int], Box::new(Type::Var(1)))
        );
    }
}
