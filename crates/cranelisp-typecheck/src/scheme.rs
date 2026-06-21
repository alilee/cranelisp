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
mod tests;
