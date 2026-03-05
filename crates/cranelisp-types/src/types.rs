use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use crate::{TraitName, TypeName};

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
    /// Algebraic data type: type name + type arguments
    ADT(TypeName, Vec<Type>),
    /// Unification variable (inference internal; resolved before codegen)
    Var(TypeId),
    /// Type constructor application (higher-kinded types, Ring 2+)
    TyConApp(TypeId, Vec<Type>),
}

impl Type {
    /// Centralized primitive name -> Type mapping.
    pub fn from_name(name: &str) -> Option<Type> {
        match name {
            "Int" => Some(Type::Int),
            "Bool" => Some(Type::Bool),
            "String" => Some(Type::String),
            "Float" => Some(Type::Float),
            _ => None,
        }
    }

    /// Centralized Type -> display name mapping.
    pub fn type_name(&self) -> Option<&'static str> {
        match self {
            Type::Int => Some("Int"),
            Type::Bool => Some("Bool"),
            Type::String => Some("String"),
            Type::Float => Some("Float"),
            _ => None,
        }
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
            Type::ADT(name, args) => {
                if args.is_empty() {
                    write!(f, "{name}")
                } else {
                    write!(f, "({name}")?;
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
    pub vars: Vec<TypeId>,
    /// Trait constraints on type variables: TypeId -> list of required trait names
    pub constraints: HashMap<TypeId, Vec<TraitName>>,
    /// The underlying type
    pub ty: Type,
}

/// Type substitution: mapping from type variables to concrete types.
pub type Subst = HashMap<TypeId, Type>;

/// Apply a substitution to a type, replacing Var(id) with the mapped type.
/// Recursively applies until no more substitutions can be made.
pub fn apply(subst: &Subst, ty: &Type) -> Type {
    match ty {
        Type::Var(id) => {
            if let Some(mapped) = subst.get(id) {
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
            let args = args.iter().map(|a| apply(subst, a)).collect();
            Type::TyConApp(*id, args)
        }
        // Primitive types are not affected by substitution.
        Type::Int | Type::Bool | Type::String | Type::Float => ty.clone(),
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
        Type::ADT(_, args) | Type::TyConApp(_, args) => {
            for a in args {
                collect_free_vars(a, result);
            }
        }
        Type::Int | Type::Bool | Type::String | Type::Float => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_name() {
        assert_eq!(Type::from_name("Int"), Some(Type::Int));
        assert_eq!(Type::from_name("Bool"), Some(Type::Bool));
        assert_eq!(Type::from_name("Float"), Some(Type::Float));
        assert_eq!(Type::from_name("String"), Some(Type::String));
        assert_eq!(Type::from_name("Foo"), None);
    }

    #[test]
    fn test_type_name() {
        assert_eq!(Type::Int.type_name(), Some("Int"));
        assert_eq!(Type::Bool.type_name(), Some("Bool"));
        assert_eq!(Type::Var(0).type_name(), None);
    }

    #[test]
    fn test_apply_identity() {
        let subst = Subst::new();
        assert_eq!(apply(&subst, &Type::Int), Type::Int);
    }

    #[test]
    fn test_apply_var_substitution() {
        let mut subst = Subst::new();
        subst.insert(0, Type::Int);
        assert_eq!(apply(&subst, &Type::Var(0)), Type::Int);
    }

    #[test]
    fn test_apply_fn_substitution() {
        let mut subst = Subst::new();
        subst.insert(0, Type::Int);
        let fn_type = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0)));
        let expected = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        assert_eq!(apply(&subst, &fn_type), expected);
    }

    #[test]
    fn test_free_vars() {
        let ty = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(1)));
        let fv = free_vars(&ty);
        assert!(fv.contains(&0));
        assert!(fv.contains(&1));
        assert_eq!(fv.len(), 2);
    }

    #[test]
    fn test_free_vars_no_vars() {
        let ty = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
        let fv = free_vars(&ty);
        assert!(fv.is_empty());
    }

    #[test]
    fn test_contains_var_primitive() {
        assert!(!Type::Int.contains_var());
        assert!(!Type::Bool.contains_var());
        assert!(!Type::String.contains_var());
        assert!(!Type::Float.contains_var());
    }

    #[test]
    fn test_contains_var_direct() {
        assert!(Type::Var(0).contains_var());
    }

    #[test]
    fn test_contains_var_nested_fn() {
        let ty = Type::Fn(vec![Type::Int], Box::new(Type::Var(0)));
        assert!(ty.contains_var());

        let ty2 = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
        assert!(!ty2.contains_var());
    }

    #[test]
    fn test_contains_var_nested_adt() {
        let ty = Type::ADT(TypeName::from("Option"), vec![Type::Var(0)]);
        assert!(ty.contains_var());

        let ty2 = Type::ADT(TypeName::from("Option"), vec![Type::Int]);
        assert!(!ty2.contains_var());
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", Type::Int), "Int");
        let fn_ty = Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int));
        assert_eq!(format!("{fn_ty}"), "(Fn [Int Int] Int)");
        let adt = Type::ADT(TypeName::from("Color"), vec![]);
        assert_eq!(format!("{adt}"), "Color");
    }
}
