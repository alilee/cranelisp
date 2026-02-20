use std::collections::HashMap;

use crate::ast::TypeExpr;
use crate::error::{CranelispError, Span};
use crate::types::*;

use super::TypeChecker;

impl TypeChecker {
    pub(crate) fn fresh_var(&mut self) -> Type {
        let id = self.next_id;
        self.next_id += 1;
        Type::Var(id)
    }

    /// Convert a TypeExpr to a Type, resolving `self` to `self_type`.
    pub(crate) fn resolve_type_expr(&self, texpr: &TypeExpr, self_type: &Type) -> Type {
        self.resolve_type_expr_with_vars(texpr, self_type, &HashMap::new())
    }

    /// Convert a TypeExpr to a Type, resolving `self` to `self_type` and
    /// looking up type variable names in `var_map`.
    pub(crate) fn resolve_type_expr_with_vars(
        &self,
        texpr: &TypeExpr,
        self_type: &Type,
        var_map: &HashMap<String, TypeId>,
    ) -> Type {
        match texpr {
            TypeExpr::SelfType => self_type.clone(),
            TypeExpr::Named(name) => match name.as_str() {
                "Int" => Type::Int,
                "Bool" => Type::Bool,
                "String" => Type::String,
                "Float" => Type::Float,
                _ => {
                    // Handle self-referential types: during register_type_def,
                    // the module may not contain this type yet, but self_type
                    // carries the ADT name being defined.
                    if let Type::ADT(self_name, self_args) = self_type {
                        if name == self_name {
                            return Type::ADT(name.clone(), self_args.clone());
                        }
                    }
                    // User-defined ADT type name (e.g., Point, Option)
                    if self.resolve_type_def_via_modules(name).is_some() {
                        Type::ADT(name.clone(), vec![])
                    } else {
                        panic!("unknown type: {}", name)
                    }
                }
            },
            TypeExpr::FnType(params, ret) => {
                let param_tys = params
                    .iter()
                    .map(|p| self.resolve_type_expr_with_vars(p, self_type, var_map))
                    .collect();
                let ret_ty = self.resolve_type_expr_with_vars(ret, self_type, var_map);
                Type::Fn(param_tys, Box::new(ret_ty))
            }
            TypeExpr::TypeVar(name) => {
                if let Some(&id) = var_map.get(name) {
                    Type::Var(id)
                } else {
                    panic!("unresolved type variable: {}", name)
                }
            }
            TypeExpr::Applied(name, args) => {
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| self.resolve_type_expr_with_vars(a, self_type, var_map))
                    .collect();
                // Handle self-referential types: during register_type_def,
                // the TypeDef entry doesn't exist yet, but self_type carries
                // the ADT name being defined.
                if let Type::ADT(self_name, _) = self_type {
                    if name == self_name {
                        return Type::ADT(name.clone(), resolved_args);
                    }
                }
                if self.resolve_type_def_via_modules(name).is_some() {
                    Type::ADT(name.clone(), resolved_args)
                } else {
                    panic!("unknown type: {}", name)
                }
            }
        }
    }

    /// Instantiate a type scheme by replacing its quantified variables with fresh variables.
    /// Propagates constraints from the scheme to the fresh type variables.
    pub(crate) fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let mapping: HashMap<TypeId, Type> =
            scheme.vars.iter().map(|&v| (v, self.fresh_var())).collect();
        // Propagate constraints to fresh vars
        for (old_id, traits) in &scheme.constraints {
            if let Some(Type::Var(new_id)) = mapping.get(old_id) {
                self.var_constraints
                    .entry(*new_id)
                    .or_default()
                    .extend(traits.iter().cloned());
            }
        }
        substitute_vars(&scheme.ty, &mapping)
    }

    /// Generalize a type over variables not free in the environment.
    pub(crate) fn generalize(&self, ty: &Type) -> Scheme {
        let ty = apply(&self.subst, ty);
        let reachable = self.reachable_schemes();
        let env_vars: Vec<TypeId> = self
            .local_env
            .values()
            .chain(reachable.iter().copied())
            .flat_map(|s| {
                let resolved = apply(&self.subst, &s.ty);
                free_vars(&resolved)
            })
            .collect();
        let ty_vars = free_vars(&ty);
        let vars: Vec<TypeId> = ty_vars
            .into_iter()
            .filter(|v| !env_vars.contains(v))
            .collect();
        // Collect constraints for quantified vars
        let constraints: HashMap<TypeId, Vec<String>> = vars
            .iter()
            .filter_map(|v| {
                self.var_constraints.get(v).map(|cs| {
                    let mut sorted: Vec<String> = cs.iter().cloned().collect();
                    sorted.sort();
                    (*v, sorted)
                })
            })
            .collect();
        Scheme {
            vars,
            constraints,
            ty,
        }
    }

    /// Resolve a type annotation against a target type.
    /// For concrete types (Int, Bool, ADTs, etc.), unifies with target.
    /// For trait names (Num, Display, etc.), adds a constraint to the target's type variable.
    pub(crate) fn resolve_annotation(
        &mut self,
        texpr: &TypeExpr,
        target_ty: &Type,
        span: Span,
    ) -> Result<(), CranelispError> {
        match texpr {
            TypeExpr::Named(name) => {
                // Try as concrete type first
                let concrete = match name.as_str() {
                    "Int" => Some(Type::Int),
                    "Bool" => Some(Type::Bool),
                    "String" => Some(Type::String),
                    "Float" => Some(Type::Float),
                    _ if self.resolve_type_def_via_modules(name).is_some() => Some(Type::ADT(name.clone(), vec![])),
                    _ => None,
                };

                if let Some(ty) = concrete {
                    self.unify(target_ty, &ty, span)
                } else if self.find_trait_decl(name).is_some() {
                    // Trait constraint
                    let resolved = apply(&self.subst, target_ty);
                    if let Type::Var(id) = resolved {
                        self.var_constraints
                            .entry(id)
                            .or_default()
                            .insert(name.clone());
                        Ok(())
                    } else {
                        // Target is already concrete — trait method calls will catch errors
                        Ok(())
                    }
                } else {
                    Err(CranelispError::TypeError {
                        message: format!("unknown type or trait: {}", name),
                        span,
                    })
                }
            }
            TypeExpr::Applied(name, args) => {
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| self.resolve_annotation_type(a, span))
                    .collect::<Result<_, _>>()?;
                let ty = Type::ADT(name.clone(), resolved_args);
                self.unify(target_ty, &ty, span)
            }
            TypeExpr::FnType(params, ret) => {
                let param_tys: Vec<Type> = params
                    .iter()
                    .map(|p| self.resolve_annotation_type(p, span))
                    .collect::<Result<_, _>>()?;
                let ret_ty = self.resolve_annotation_type(ret, span)?;
                let ty = Type::Fn(param_tys, Box::new(ret_ty));
                self.unify(target_ty, &ty, span)
            }
            TypeExpr::TypeVar(_) | TypeExpr::SelfType => Err(CranelispError::TypeError {
                message: "type variables and 'self' are not allowed in type annotations"
                    .to_string(),
                span,
            }),
        }
    }

    /// Convert a TypeExpr to a Type in annotation context (inner positions only).
    /// Returns an error instead of panicking for unknown types.
    fn resolve_annotation_type(
        &self,
        texpr: &TypeExpr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        match texpr {
            TypeExpr::Named(name) => match name.as_str() {
                "Int" => Ok(Type::Int),
                "Bool" => Ok(Type::Bool),
                "String" => Ok(Type::String),
                "Float" => Ok(Type::Float),
                _ if self.resolve_type_def_via_modules(name).is_some() => Ok(Type::ADT(name.clone(), vec![])),
                _ => Err(CranelispError::TypeError {
                    message: format!("unknown type: {}", name),
                    span,
                }),
            },
            TypeExpr::Applied(name, args) => {
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| self.resolve_annotation_type(a, span))
                    .collect::<Result<_, _>>()?;
                if self.resolve_type_def_via_modules(name).is_some() || name == "Vec" {
                    Ok(Type::ADT(name.clone(), resolved_args))
                } else {
                    Err(CranelispError::TypeError {
                        message: format!("unknown type: {}", name),
                        span,
                    })
                }
            }
            TypeExpr::FnType(params, ret) => {
                let param_tys: Vec<Type> = params
                    .iter()
                    .map(|p| self.resolve_annotation_type(p, span))
                    .collect::<Result<_, _>>()?;
                let ret_ty = self.resolve_annotation_type(ret, span)?;
                Ok(Type::Fn(param_tys, Box::new(ret_ty)))
            }
            TypeExpr::TypeVar(_) | TypeExpr::SelfType => Err(CranelispError::TypeError {
                message: "type variables and 'self' are not allowed in type annotations"
                    .to_string(),
                span,
            }),
        }
    }

    /// Unify two types, updating the substitution map.
    pub(crate) fn unify(&mut self, a: &Type, b: &Type, span: Span) -> Result<(), CranelispError> {
        let a = apply(&self.subst, a);
        let b = apply(&self.subst, b);

        match (&a, &b) {
            (Type::Int, Type::Int)
            | (Type::Bool, Type::Bool)
            | (Type::String, Type::String)
            | (Type::Float, Type::Float) => Ok(()),
            (Type::Var(id), other) | (other, Type::Var(id)) => {
                let id = *id;
                if let Type::Var(other_id) = other {
                    if id == *other_id {
                        return Ok(());
                    }
                }
                // Occurs check
                if occurs(id, other) {
                    return Err(CranelispError::TypeError {
                        message: format!("infinite type: t{} occurs in {}", id, other),
                        span,
                    });
                }
                // Merge constraints when unifying two type vars
                if let Type::Var(other_id) = other {
                    if let Some(cs) = self.var_constraints.remove(&id) {
                        self.var_constraints
                            .entry(*other_id)
                            .or_default()
                            .extend(cs);
                    }
                }
                self.subst.insert(id, other.clone());
                Ok(())
            }
            (Type::ADT(n1, a1), Type::ADT(n2, a2)) => {
                if n1 != n2 {
                    return Err(CranelispError::TypeError {
                        message: format!("type mismatch: {} vs {}", n1, n2),
                        span,
                    });
                }
                if a1.len() != a2.len() {
                    return Err(CranelispError::TypeError {
                        message: format!("type argument count mismatch for {}", n1),
                        span,
                    });
                }
                for (a, b) in a1.iter().zip(a2.iter()) {
                    self.unify(a, b, span)?;
                }
                Ok(())
            }
            // TyConApp(f, args) vs ADT(name, args2): bind f → ADT(name, []), unify args
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
                        span,
                    });
                }
                // Bind f to ADT(name, []) — the constructor itself
                self.subst.insert(f_id, Type::ADT(name.clone(), vec![]));
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    self.unify(a1, a2, span)?;
                }
                Ok(())
            }
            // TyConApp(f1, args1) vs TyConApp(f2, args2): bind f1 → Var(f2), unify args
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
                        span,
                    });
                }
                if f1 != f2 {
                    self.subst.insert(f1, Type::Var(f2));
                }
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    self.unify(a1, a2, span)?;
                }
                Ok(())
            }
            (Type::Fn(p1, r1), Type::Fn(p2, r2)) => {
                if p1.len() != p2.len() {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "function arity mismatch: expected {} args, got {}",
                            p1.len(),
                            p2.len()
                        ),
                        span,
                    });
                }
                for (a, b) in p1.iter().zip(p2.iter()) {
                    self.unify(a, b, span)?;
                }
                self.unify(r1, r2, span)
            }
            _ => Err(CranelispError::TypeError {
                message: format!("type mismatch: cannot unify {} with {}", a, b),
                span,
            }),
        }
    }
}

/// Check if a type variable occurs in a type (for the occurs check).
pub(super) fn occurs(id: TypeId, ty: &Type) -> bool {
    match ty {
        Type::Int | Type::Bool | Type::String | Type::Float => false,
        Type::Var(other) => id == *other,
        Type::Fn(params, ret) => params.iter().any(|p| occurs(id, p)) || occurs(id, ret),
        Type::ADT(_, args) => args.iter().any(|a| occurs(id, a)),
        Type::TyConApp(con_id, args) => id == *con_id || args.iter().any(|a| occurs(id, a)),
    }
}

/// Substitute type variable IDs according to a mapping (for instantiation).
pub(crate) fn substitute_vars(ty: &Type, mapping: &HashMap<TypeId, Type>) -> Type {
    match ty {
        Type::Int | Type::Bool | Type::String | Type::Float => ty.clone(),
        Type::Var(id) => mapping.get(id).cloned().unwrap_or_else(|| ty.clone()),
        Type::Fn(params, ret) => {
            let params = params.iter().map(|p| substitute_vars(p, mapping)).collect();
            let ret = Box::new(substitute_vars(ret, mapping));
            Type::Fn(params, ret)
        }
        Type::ADT(name, args) => {
            let args = args.iter().map(|a| substitute_vars(a, mapping)).collect();
            Type::ADT(name.clone(), args)
        }
        Type::TyConApp(id, args) => {
            let new_id = if let Some(Type::Var(mapped_id)) = mapping.get(id) {
                *mapped_id
            } else {
                *id
            };
            let args = args.iter().map(|a| substitute_vars(a, mapping)).collect();
            Type::TyConApp(new_id, args)
        }
    }
}

/// Check if a type contains any type variables.
pub(crate) fn has_type_var(ty: &Type) -> bool {
    match ty {
        Type::Int | Type::Bool | Type::String | Type::Float => false,
        Type::Var(_) => true,
        Type::Fn(params, ret) => params.iter().any(has_type_var) || has_type_var(ret),
        Type::ADT(_, args) => args.iter().any(has_type_var),
        Type::TyConApp(_, _) => true, // always has a type constructor variable
    }
}
