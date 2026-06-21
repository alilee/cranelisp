use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use crate::{FQTraitName, FQTypeName, ModuleFullPath, TypeName};

/// Type variable identifier. Narrow to u32 -- 4 billion type vars sufficient.
pub type TypeId = u32;

/// Concrete type.
///
/// All variants exist from Ring 0. Ring 0 exercises Int, Bool, Float, simple Fn, Var,
/// and ADT (enum-only). Ring 1 adds String, ADT with fields, Fn-with-closures.
/// Ring 2 adds constrained Var usage and TyConApp.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Type {
    Int,
    Bool,
    String,
    Float,
    /// Function type: param types -> return type
    Fn(Vec<Type>, Box<Type>),
    /// Algebraic data type: fully-qualified type name + type arguments.
    /// Module context embedded at construction time — eliminates `build_type_modules()`.
    ADT(FQTypeName, Vec<Type>),
    /// Unification variable (inference internal; resolved before codegen)
    Var(TypeId),
    /// Type constructor application (higher-kinded types, Ring 2+)
    TyConApp(TypeId, Vec<Type>),
}

impl Type {
    /// Check whether this type is `IO _`.
    pub fn is_io(&self) -> bool {
        matches!(self, Type::ADT(fqtn, _) if fqtn.module == "primitives" && fqtn.name == "IO")
    }

    /// Extract the inner type from `IO T`.
    ///
    /// Returns a borrow of the inner type (e.g., `&Int` from `IO Int`).
    /// If the type is not IO or has no type arguments, returns `self` unchanged.
    pub fn unwrap_io(&self) -> &Type {
        match self {
            Type::ADT(_, args) if !args.is_empty() => &args[0],
            _ => self,
        }
    }

    /// Create a named ADT type with module qualification.
    pub fn adt(module: ModuleFullPath, name: TypeName, args: Vec<Type>) -> Type {
        Type::ADT(FQTypeName::new(module, name), args)
    }

    /// Returns true if this type contains any unresolved type variable (`Type::Var`).
    /// Used in `debug_assert!` to verify all types are fully resolved before codegen.
    pub fn contains_var(&self) -> bool {
        match self {
            Type::Var(_) => true,
            Type::Fn(params, ret) => {
                params.iter().any(|p| p.contains_var()) || ret.contains_var()
            }
            Type::ADT(_, args) | Type::TyConApp(_, args) => {
                args.iter().any(|a| a.contains_var())
            }
            Type::Int | Type::Bool | Type::String | Type::Float => false,
        }
    }

    /// Returns true if this type is **fully concrete** — no `Type::Var` (and no
    /// `Type::TyConApp`, whose head is itself a type variable) anywhere in its
    /// structure.
    ///
    /// **This is the GOT-slot eligibility predicate** (Principle 20, BC §7
    /// "Callability is structural"). The architectural invariant is: a def has a
    /// GOT slot **iff** its type is fully concrete. "Concrete" is *strictly
    /// stronger* than "unconstrained" (no trait bounds): a generic-but-
    /// unconstrained def (`id : ∀a. a→a`, or a HOF whose result is `(Box a)`)
    /// carries **zero** trait constraints yet is **not** concrete. Gating GOT-slot
    /// allocation on constraint-emptiness instead of concreteness was the leak that
    /// let a non-concrete def reach codegen as a value (S84 — the `(Box a)`-through-
    /// HOF SIGSEGV). The slot-allocation gate MUST test `is_concrete()`, not
    /// `constraints.is_empty()`.
    ///
    /// `TyConApp` is treated as non-concrete because its `TypeId` head is an
    /// unresolved higher-kinded type variable; a `TyConApp` reaching the slot gate
    /// is by construction not a monomorphised concrete callable.
    ///
    /// Equivalent today to `!self.contains_var()` for the first-order fragment;
    /// named separately because it expresses the *eligibility* intent at the gate
    /// (the inverse `contains_var` expresses the *debug-tripwire* intent at
    /// codegen), and because the `TyConApp`-head case is part of "concrete" but is
    /// not a bare `Var`.
    pub fn is_concrete(&self) -> bool {
        match self {
            Type::Var(_) => false,
            // A type-constructor application's head is an unresolved HKT variable;
            // a concrete callable never carries one at the slot gate.
            Type::TyConApp(_, _) => false,
            Type::Fn(params, ret) => {
                params.iter().all(|p| p.is_concrete()) && ret.is_concrete()
            }
            Type::ADT(_, args) => args.iter().all(|a| a.is_concrete()),
            Type::Int | Type::Bool | Type::String | Type::Float => true,
        }
    }

}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::String => write!(f, "String"),
            Type::Float => write!(f, "Float"),
            Type::Fn(params, ret) => {
                write!(f, "(Fn [")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{p}")?;
                }
                write!(f, "] {ret})")
            }
            Type::ADT(fqtn, args) => {
                if args.is_empty() {
                    write!(f, "{fqtn}")
                } else {
                    write!(f, "({fqtn}")?;
                    for a in args {
                        write!(f, " {a}")?;
                    }
                    write!(f, ")")
                }
            }
            Type::Var(id) => write!(f, "t{id}"),
            Type::TyConApp(id, args) => {
                write!(f, "(TyCon t{id}")?;
                for a in args {
                    write!(f, " {a}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Polymorphic type scheme: universally quantified type with optional trait constraints.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Scheme {
    /// Quantified type variables
    pub type_vars: Vec<TypeId>,
    /// Trait constraints on type variables: TypeId -> list of required fully-qualified trait names
    pub constraints: HashMap<TypeId, Vec<FQTraitName>>,
    /// The underlying type
    pub ty: Type,
}

/// Map from internal TypeId to user-friendly type variable name (a, b, c, ...).
///
/// Collects all Var ids in order of first occurrence, then assigns sequential
/// names. Used by REPL display and Scheme formatting.
pub fn type_var_names(ty: &Type) -> HashMap<TypeId, String> {
    let mut ids = Vec::new();
    collect_var_ids_ordered(ty, &mut ids);
    ids.into_iter()
        .enumerate()
        .map(|(i, id)| {
            let name = if i < 26 {
                String::from((b'a' + i as u8) as char)
            } else {
                format!("t{id}")
            };
            (id, name)
        })
        .collect()
}

/// Format a type with user-friendly variable names (a, b, c, ...).
///
/// Replaces internal TypeId numbers with sequential letters.
pub fn format_type_display(ty: &Type) -> String {
    let names = type_var_names(ty);
    format_type_with_vars(ty, &names)
}

/// Format a type using the given variable name mapping.
pub fn format_type_with_vars(ty: &Type, var_names: &HashMap<TypeId, String>) -> String {
    match ty {
        Type::Int => "Int".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Float => "Float".to_string(),
        Type::Fn(params, ret) => {
            let parts: Vec<String> = params
                .iter()
                .map(|p| format_type_with_vars(p, var_names))
                .collect();
            let ret_s = format_type_with_vars(ret, var_names);
            format!("(Fn [{}] {ret_s})", parts.join(" "))
        }
        Type::ADT(fqtn, args) => {
            if args.is_empty() {
                format!("{fqtn}")
            } else {
                let arg_strs: Vec<String> = args
                    .iter()
                    .map(|a| format_type_with_vars(a, var_names))
                    .collect();
                format!("({fqtn} {})", arg_strs.join(" "))
            }
        }
        Type::Var(id) => {
            var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{id}"))
        }
        Type::TyConApp(id, args) => {
            let name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{id}"));
            if args.is_empty() {
                name
            } else {
                let arg_strs: Vec<String> = args
                    .iter()
                    .map(|a| format_type_with_vars(a, var_names))
                    .collect();
                format!("({name} {})", arg_strs.join(" "))
            }
        }
    }
}

/// Collect Var ids in order of first occurrence (left-to-right, depth-first).
fn collect_var_ids_ordered(ty: &Type, ids: &mut Vec<TypeId>) {
    match ty {
        Type::Var(id) => {
            if !ids.contains(id) {
                ids.push(*id);
            }
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_var_ids_ordered(p, ids);
            }
            collect_var_ids_ordered(ret, ids);
        }
        Type::ADT(_, args) | Type::TyConApp(_, args) => {
            for a in args {
                collect_var_ids_ordered(a, ids);
            }
        }
        Type::Int | Type::Bool | Type::String | Type::Float => {}
    }
}

/// Type substitution: mapping from type variables to concrete types.
pub type Subst = HashMap<TypeId, Type>;

/// Apply a substitution to a type, replacing Var(id) with the mapped type.
/// Recursively applies until no more substitutions can be made.
pub fn apply(subst: &Subst, ty: &Type) -> Type {
    match ty {
        Type::Var(id) => {
            if let Some(mapped) = subst.get(id) {
                // Defensive cycle guard: a well-formed substitution never maps
                // a variable (transitively) to a type containing itself — that
                // is an occurs-check violation. If one is ever constructed
                // (see FIXME 0279/0295: a cross-module instantiation building
                // an identity self-map `{id -> Var(id)}` when the fresh-var
                // counter collides with an imported scheme's bound vars), the
                // naive chase `apply(subst, mapped)` recurses forever and
                // overflows the stack. Detect a direct self-map and treat the
                // variable as unbound rather than diverging. Instantiation is
                // fixed at construction (typecheck `fresh_instantiation_subst`)
                // so this guard should never fire in practice; the
                // `debug_assert!` surfaces it as a clear failure in debug
                // builds, and the fallthrough keeps release builds bounded.
                if let Type::Var(mapped_id) = mapped
                    && mapped_id == id
                {
                    debug_assert!(
                        false,
                        "apply: cyclic substitution — Var({id}) maps to itself (occurs-check violation)"
                    );
                    return ty.clone();
                }
                apply(subst, mapped)
            } else {
                ty.clone()
            }
        }
        Type::Fn(params, ret) => {
            let params = params.iter().map(|p| apply(subst, p)).collect();
            let ret = Box::new(apply(subst, ret));
            Type::Fn(params, ret)
        }
        Type::ADT(name, args) => {
            let args = args.iter().map(|a| apply(subst, a)).collect();
            Type::ADT(name.clone(), args)
        }
        Type::TyConApp(id, args) => {
            let applied_args: Vec<Type> = args.iter().map(|a| apply(subst, a)).collect();
            // If the constructor variable is in the substitution, remap:
            // - subst[id] = ADT(name, []) → ADT(name, applied_args)
            // - subst[id] = Var(other_id) → TyConApp(other_id, applied_args)
            if let Some(mapped) = subst.get(id) {
                let resolved = apply(subst, mapped);
                match resolved {
                    Type::ADT(name, _) => Type::ADT(name, applied_args),
                    Type::Var(other_id) => Type::TyConApp(other_id, applied_args),
                    _ => Type::TyConApp(*id, applied_args),
                }
            } else {
                Type::TyConApp(*id, applied_args)
            }
        }
        // Primitive types are not affected by substitution.
        Type::Int | Type::Bool | Type::String | Type::Float => ty.clone(),
    }
}

/// Find the maximum TypeId used in a type (including in Var and TyConApp).
///
/// Returns `None` if the type contains no type variables or type constructors.
/// Used to advance the typechecker's `next_id` past type vars from cached modules
/// to prevent ID collisions during instantiation.
pub fn max_type_var_id(ty: &Type) -> Option<TypeId> {
    let mut max_id: Option<TypeId> = None;
    collect_max_type_var_id(ty, &mut max_id);
    max_id
}

fn collect_max_type_var_id(ty: &Type, max_id: &mut Option<TypeId>) {
    match ty {
        Type::Var(id) => {
            *max_id = Some(max_id.map_or(*id, |m| m.max(*id)));
        }
        Type::TyConApp(id, args) => {
            *max_id = Some(max_id.map_or(*id, |m| m.max(*id)));
            for a in args {
                collect_max_type_var_id(a, max_id);
            }
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_max_type_var_id(p, max_id);
            }
            collect_max_type_var_id(ret, max_id);
        }
        Type::ADT(_, args) => {
            for a in args {
                collect_max_type_var_id(a, max_id);
            }
        }
        Type::Int | Type::Bool | Type::String | Type::Float => {}
    }
}

/// Collect free (unbound) type variables in a type.
pub fn free_vars(ty: &Type) -> HashSet<TypeId> {
    let mut result = HashSet::new();
    collect_free_vars(ty, &mut result);
    result
}

fn collect_free_vars(ty: &Type, result: &mut HashSet<TypeId>) {
    match ty {
        Type::Var(id) => {
            result.insert(*id);
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_free_vars(p, result);
            }
            collect_free_vars(ret, result);
        }
        Type::ADT(_, args) => {
            for a in args {
                collect_free_vars(a, result);
            }
        }
        Type::TyConApp(con_id, args) => {
            // The constructor ID itself is a type variable for occurs-check purposes
            result.insert(*con_id);
            for a in args {
                collect_free_vars(a, result);
            }
        }
        Type::Int | Type::Bool | Type::String | Type::Float => {}
    }
}

#[cfg(test)]
mod tests;
