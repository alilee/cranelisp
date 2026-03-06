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
        Type::ADT(name, args) => {
            if args.is_empty() {
                format!("{name}")
            } else {
                let arg_strs: Vec<String> = args
                    .iter()
                    .map(|a| format_type_with_vars(a, var_names))
                    .collect();
                format!("({name} {})", arg_strs.join(" "))
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

    // --- U1.6: type variable display name tests ---

    #[test]
    fn test_format_type_display_single_var() {
        // A single type variable should display as "a", not "t42".
        let ty = Type::Var(42);
        assert_eq!(format_type_display(&ty), "a");
    }

    #[test]
    fn test_format_type_display_identity_fn() {
        // (Fn [Var(5)] Var(5)) should display as "(Fn [a] a)".
        let ty = Type::Fn(vec![Type::Var(5)], Box::new(Type::Var(5)));
        assert_eq!(format_type_display(&ty), "(Fn [a] a)");
    }

    #[test]
    fn test_format_type_display_two_vars() {
        // Two distinct vars should be "a" and "b".
        let ty = Type::Fn(vec![Type::Var(10), Type::Var(20)], Box::new(Type::Var(10)));
        assert_eq!(format_type_display(&ty), "(Fn [a b] a)");
    }

    #[test]
    fn test_format_type_display_concrete_type() {
        // Concrete types should display normally.
        assert_eq!(format_type_display(&Type::Int), "Int");
        assert_eq!(format_type_display(&Type::Bool), "Bool");
    }

    #[test]
    fn test_format_type_display_polymorphic_adt() {
        // (Option Var(3)) should display as "(Option a)".
        let ty = Type::ADT(TypeName::from("Option"), vec![Type::Var(3)]);
        assert_eq!(format_type_display(&ty), "(Option a)");
    }

    #[test]
    fn test_type_var_names_ordering() {
        // Variable names assigned in order of first occurrence.
        let ty = Type::Fn(
            vec![Type::Var(99), Type::Var(50)],
            Box::new(Type::Var(99)),
        );
        let names = type_var_names(&ty);
        assert_eq!(names.get(&99), Some(&"a".to_string()));
        assert_eq!(names.get(&50), Some(&"b".to_string()));
    }
}
