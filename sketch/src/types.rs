use std::collections::HashMap;
use std::fmt;

use serde::{Deserialize, Serialize};

pub type TypeId = usize;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Type {
    Int,
    Bool,
    String,
    Float,
    Fn(Vec<Type>, Box<Type>),
    ADT(String, Vec<Type>),
    Var(TypeId),
    /// Type constructor variable applied to type args, e.g. `(f a)` in HKT traits.
    /// At codegen time, all TyConApp should be resolved to ADT via substitution.
    TyConApp(TypeId, Vec<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::String => write!(f, "String"),
            Type::Float => write!(f, "Float"),
            Type::Fn(params, ret) => {
                write!(f, "(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, ") -> {}", ret)
            }
            Type::ADT(name, args) => {
                if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(f, "({}", name)?;
                    for a in args {
                        write!(f, " {}", a)?;
                    }
                    write!(f, ")")
                }
            }
            Type::Var(id) => write!(f, "t{}", id),
            Type::TyConApp(id, args) => {
                write!(f, "(t{}", id)?;
                for a in args {
                    write!(f, " {}", a)?;
                }
                write!(f, ")")
            }
        }
    }
}

/// A type scheme: forall [vars]. ty
/// Used for let-polymorphism (generalized function types).
/// `constraints` maps quantified type variable IDs to trait names they must satisfy.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Scheme {
    pub vars: Vec<TypeId>,
    pub constraints: HashMap<TypeId, Vec<String>>,
    pub ty: Type,
}

impl Scheme {
    /// Create a monomorphic scheme (no quantified vars, no constraints).
    pub fn mono(ty: Type) -> Self {
        Scheme {
            vars: vec![],
            constraints: HashMap::new(),
            ty,
        }
    }

    /// Check if this scheme has any trait constraints on its type variables.
    pub fn is_constrained(&self) -> bool {
        !self.constraints.is_empty()
    }

    /// Extract the parameter count from the scheme's type (0 if not a function type).
    pub fn param_count(&self) -> usize {
        match &self.ty {
            Type::Fn(params, _) => params.len(),
            _ => 0,
        }
    }
}

impl Type {
    /// Returns true if values of this type are heap-allocated pointers.
    /// Scalars (Int, Bool, Float) and nullary ADT tags are NOT heap-allocated,
    /// but ADT is conservatively marked true (may be nullary at runtime).
    pub fn is_heap_type(&self) -> bool {
        match self {
            Type::String | Type::Fn(_, _) => true,
            Type::ADT(_, _) => true, // conservative: may be nullary at runtime
            Type::TyConApp(_, _) => true, // conservative: will be ADT at runtime
            _ => false,
        }
    }
}

/// Substitution map from type variable IDs to their resolved types.
pub type Subst = HashMap<TypeId, Type>;

/// Apply a substitution to a type, recursively resolving variables.
pub fn apply(subst: &Subst, ty: &Type) -> Type {
    match ty {
        Type::Int | Type::Bool | Type::String | Type::Float => ty.clone(),
        Type::Var(id) => {
            if let Some(resolved) = subst.get(id) {
                apply(subst, resolved)
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
            // If the constructor variable is bound, collapse to ADT
            if let Some(resolved) = subst.get(id) {
                let resolved = apply(subst, resolved);
                if let Type::ADT(name, _base_args) = &resolved {
                    // Constructor var bound to ADT(name, []) — apply args
                    let resolved_args: Vec<Type> = args.iter().map(|a| apply(subst, a)).collect();
                    return Type::ADT(name.clone(), resolved_args);
                }
                // Constructor var bound to another var — keep TyConApp but update id
                if let Type::Var(new_id) = resolved {
                    let resolved_args: Vec<Type> = args.iter().map(|a| apply(subst, a)).collect();
                    return Type::TyConApp(new_id, resolved_args);
                }
            }
            let resolved_args: Vec<Type> = args.iter().map(|a| apply(subst, a)).collect();
            Type::TyConApp(*id, resolved_args)
        }
    }
}

/// Collect all free type variable IDs in a type.
pub fn free_vars(ty: &Type) -> Vec<TypeId> {
    match ty {
        Type::Int | Type::Bool | Type::String | Type::Float => vec![],
        Type::Var(id) => vec![*id],
        Type::Fn(params, ret) => {
            let mut vars: Vec<TypeId> = params.iter().flat_map(free_vars).collect();
            vars.extend(free_vars(ret));
            vars.sort();
            vars.dedup();
            vars
        }
        Type::ADT(_, args) => {
            let mut vars: Vec<TypeId> = args.iter().flat_map(free_vars).collect();
            vars.sort();
            vars.dedup();
            vars
        }
        Type::TyConApp(id, args) => {
            let mut vars = vec![*id];
            vars.extend(args.iter().flat_map(free_vars));
            vars.sort();
            vars.dedup();
            vars
        }
    }
}
