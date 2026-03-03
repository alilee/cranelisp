use crate::ast::*;
use crate::error::CranelispError;
use crate::types::*;

use super::{MethodResolutions, ResolvedCall, TypeChecker};

impl TypeChecker {
    /// Check if a name is an overloaded function.
    pub fn is_overloaded(&self, name: &str) -> bool {
        self.overloads.contains_key(name)
    }

    /// Build mangled Defn items for all multi-sig functions in a program
    /// (after check_program has resolved overloads).
    pub fn build_multi_defns(&self, program: &Program) -> Vec<Defn> {
        let mut result = Vec::new();
        for (name, variants, _span) in crate::ast::defn_multis(program) {
            if let Some(resolved) = self.resolved_overloads.get(name) {
                for (i, (_param_types, _ret_ty, mangled_name)) in resolved.iter().enumerate() {
                    if i < variants.len() {
                        result.push(Defn {
                            visibility: crate::ast::Visibility::Public,
                            name: mangled_name.clone(),
                            docstring: None,
                            params: variants[i].params.clone(),
                            param_annotations: variants[i].param_annotations.clone(),
                            body: variants[i].body.clone(),
                            span: variants[i].span,
                        });
                    }
                }
            }
        }
        result
    }

    /// Resolve all pending overload dispatches and auto-curry resolutions.
    /// Appends to the provided MethodResolutions table.
    pub fn resolve_overloads(
        &mut self,
        resolutions: &mut MethodResolutions,
    ) -> Result<(), CranelispError> {
        // Resolve overload dispatches
        let pending = std::mem::take(&mut self.pending_overload_resolutions);
        for (span, base_name, arg_types, ret_type_var) in &pending {
            let concrete_args: Vec<Type> =
                arg_types.iter().map(|t| apply(&self.subst, t)).collect();

            let variants = self
                .resolved_overloads
                .get(base_name)
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!("no overloaded function: {}", base_name),
                    span: *span,
                })?
                .clone();

            // Find exact arity matches
            let mut exact_matches: Vec<(Vec<Type>, Type, String)> = Vec::new();
            let mut curry_candidates: Vec<(Vec<Type>, Type, String)> = Vec::new();

            for (param_types, ret_ty, mangled_name) in &variants {
                if param_types.len() == concrete_args.len() {
                    // Check type compatibility
                    let mut compatible = true;
                    for (p, a) in param_types.iter().zip(concrete_args.iter()) {
                        if !types_compatible(p, a) {
                            compatible = false;
                            break;
                        }
                    }
                    if compatible {
                        exact_matches.push((
                            param_types.clone(),
                            ret_ty.clone(),
                            mangled_name.clone(),
                        ));
                    }
                } else if param_types.len() > concrete_args.len() && !concrete_args.is_empty() {
                    // Auto-curry candidate
                    let mut compatible = true;
                    for (p, a) in param_types.iter().zip(concrete_args.iter()) {
                        if !types_compatible(p, a) {
                            compatible = false;
                            break;
                        }
                    }
                    if compatible {
                        curry_candidates.push((
                            param_types.clone(),
                            ret_ty.clone(),
                            mangled_name.clone(),
                        ));
                    }
                }
            }

            if exact_matches.len() == 1 {
                let (param_types, ret_ty, mangled_name) = &exact_matches[0];
                // Unify param types with arg types to bind type variables in the
                // return type (e.g., Seq<a> + arg Seq<Int> → a=Int → ret Seq<Int>)
                for (p, a) in param_types.iter().zip(concrete_args.iter()) {
                    self.unify(p, a, *span)?;
                }
                self.unify(ret_type_var, ret_ty, *span)?;
                resolutions.insert(
                    *span,
                    ResolvedCall::SigDispatch {
                        mangled_name: mangled_name.clone(),
                    },
                );
            } else if exact_matches.len() > 1 {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "ambiguous call to '{}' — {} matching signatures",
                        base_name,
                        exact_matches.len()
                    ),
                    span: *span,
                });
            } else if curry_candidates.len() == 1 {
                let (param_types, ret_ty, mangled_name) = &curry_candidates[0];
                // Unify applied args with first N params
                for (p, a) in param_types.iter().zip(concrete_args.iter()) {
                    self.unify(p, a, *span)?;
                }
                // Return type is a function from remaining params to ret
                let remaining: Vec<Type> = param_types[concrete_args.len()..]
                    .iter()
                    .map(|t| apply(&self.subst, t))
                    .collect();
                let curry_ret = Type::Fn(remaining, Box::new(ret_ty.clone()));
                self.unify(ret_type_var, &curry_ret, *span)?;
                resolutions.insert(
                    *span,
                    ResolvedCall::AutoCurry {
                        target_name: mangled_name.clone(),
                        applied_count: concrete_args.len(),
                        total_count: param_types.len(),
                    },
                );
            } else if curry_candidates.len() > 1 {
                // Try to disambiguate using the resolved return type constraint
                let resolved_ret = apply(&self.subst, ret_type_var);
                let mut narrowed: Vec<(Vec<Type>, Type, String)> = Vec::new();
                if let Type::Fn(expected_params, _) = &resolved_ret {
                    // Return type is constrained to a function type; use arity to disambiguate
                    for (param_types, ret_ty, mangled_name) in &curry_candidates {
                        let remaining = param_types.len() - concrete_args.len();
                        if remaining == expected_params.len() {
                            narrowed.push((
                                param_types.clone(),
                                ret_ty.clone(),
                                mangled_name.clone(),
                            ));
                        }
                    }
                }
                if narrowed.len() == 1 {
                    let (param_types, ret_ty, mangled_name) = &narrowed[0];
                    for (p, a) in param_types.iter().zip(concrete_args.iter()) {
                        self.unify(p, a, *span)?;
                    }
                    let remaining: Vec<Type> = param_types[concrete_args.len()..]
                        .iter()
                        .map(|t| apply(&self.subst, t))
                        .collect();
                    let curry_ret = Type::Fn(remaining, Box::new(ret_ty.clone()));
                    self.unify(ret_type_var, &curry_ret, *span)?;
                    resolutions.insert(
                        *span,
                        ResolvedCall::AutoCurry {
                            target_name: mangled_name.clone(),
                            applied_count: concrete_args.len(),
                            total_count: param_types.len(),
                        },
                    );
                } else {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "ambiguous auto-curry of '{}' — {} matching signatures",
                            base_name,
                            curry_candidates.len()
                        ),
                        span: *span,
                    });
                }
            } else {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "no matching signature for '{}' with arg types ({})",
                        base_name,
                        concrete_args
                            .iter()
                            .map(|t| format!("{}", t))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    span: *span,
                });
            }
        }

        // Resolve auto-curry for single-arity functions
        let pending_curry = std::mem::take(&mut self.pending_auto_curry);
        for (span, name, applied_count, total_count) in &pending_curry {
            resolutions.insert(
                *span,
                ResolvedCall::AutoCurry {
                    target_name: name.clone(),
                    applied_count: *applied_count,
                    total_count: *total_count,
                },
            );
        }

        Ok(())
    }

    /// Type-check a multi-signature function definition (for REPL use).
    /// Returns list of (mangled_name, defn, scheme) for compilation.
    pub fn check_defn_multi(
        &mut self,
        name: &str,
        variants: &[DefnVariant],
    ) -> Result<Vec<(String, Defn, Scheme)>, CranelispError> {
        let mut internal_names = Vec::new();
        let mut internal_defns = Vec::new();

        // Register each variant under an internal name with fresh type vars
        for (i, variant) in variants.iter().enumerate() {
            let internal_name = format!("{}__v{}", name, i);
            let param_tys: Vec<Type> = variant.params.iter().map(|_| self.fresh_var()).collect();
            let ret_ty = self.fresh_var();
            let fn_ty = Type::Fn(param_tys.clone(), Box::new(ret_ty.clone()));
            self.insert_def(internal_name.clone(), Scheme::mono(fn_ty));
            internal_names.push((internal_name.clone(), param_tys, ret_ty));
            internal_defns.push(Defn {
                visibility: crate::ast::Visibility::Public,
                name: internal_name,
                docstring: None,
                params: variant.params.clone(),
                param_annotations: variant.param_annotations.clone(),
                body: variant.body.clone(),
                span: variant.span,
            });
        }

        // Register overloads entry
        let overload_entries: Vec<(String, usize)> = internal_names
            .iter()
            .enumerate()
            .map(|(i, (iname, _, _))| (iname.clone(), variants[i].params.len()))
            .collect();
        self.overloads.insert(name.to_string(), overload_entries);

        // Check each variant's body
        for (defn, (_, param_tys, ret_ty)) in internal_defns.iter().zip(internal_names.iter()) {
            let saved_local = self.local_env.clone();
            for (pname, ty) in defn.params.iter().zip(param_tys.iter()) {
                self.local_env.insert(
                    crate::names::Symbol::from(pname.as_str()),
                    Scheme::mono(ty.clone()),
                );
            }
            let body_ty = self.infer_expr(&defn.body)?;
            self.unify(&body_ty, ret_ty, defn.span)?;
            self.local_env = saved_local;
        }

        // Build mangled names from concrete types
        let mut result = Vec::new();
        let mut sig_set: Vec<Vec<Type>> = Vec::new();

        for (i, (iname, param_tys, ret_ty)) in internal_names.iter().enumerate() {
            let concrete_params: Vec<Type> =
                param_tys.iter().map(|t| apply(&self.subst, t)).collect();
            let concrete_ret = apply(&self.subst, ret_ty);
            let mangled = crate::ast::mangle_sig(name, &concrete_params);

            // Check for duplicate signatures
            if sig_set.iter().any(|s| s == &concrete_params) {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "duplicate signature for '{}': ({})",
                        name,
                        concrete_params
                            .iter()
                            .map(|t| format!("{}", t))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    span: variants[i].span,
                });
            }
            sig_set.push(concrete_params.clone());

            let fn_ty = Type::Fn(concrete_params.clone(), Box::new(concrete_ret.clone()));
            let scheme = self.generalize(&fn_ty);

            // Remove internal name, register mangled name
            self.remove_def(iname);
            self.insert_def(mangled.clone(), scheme.clone());

            let mangled_defn = Defn {
                visibility: crate::ast::Visibility::Public,
                name: mangled.clone(),
                docstring: None,
                params: variants[i].params.clone(),
                param_annotations: variants[i].param_annotations.clone(),
                body: variants[i].body.clone(),
                span: variants[i].span,
            };

            // Store per-variant metadata with param names
            let meta = super::SymbolMeta::UserFn {
                docstring: None,
                param_names: variants[i].params.clone(),
            };
            self.update_current_module_meta(&mangled, meta);

            result.push((mangled.clone(), mangled_defn, scheme.clone()));
        }

        // Store resolved overloads
        let resolved: Vec<(Vec<Type>, Type, String)> = result
            .iter()
            .enumerate()
            .map(|(i, (mangled, _, _))| {
                let concrete_params: Vec<Type> = internal_names[i]
                    .1
                    .iter()
                    .map(|t| apply(&self.subst, t))
                    .collect();
                let concrete_ret = apply(&self.subst, &internal_names[i].2);
                (concrete_params, concrete_ret, mangled.clone())
            })
            .collect();
        self.resolved_overloads.insert(name.to_string(), resolved);

        Ok(result)
    }
}

/// Check if two concrete types are compatible (for overload resolution).
fn types_compatible(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Int, Type::Int)
        | (Type::Bool, Type::Bool)
        | (Type::String, Type::String)
        | (Type::Float, Type::Float) => true,
        (Type::Fn(p1, r1), Type::Fn(p2, r2)) => {
            p1.len() == p2.len()
                && p1
                    .iter()
                    .zip(p2.iter())
                    .all(|(a, b)| types_compatible(a, b))
                && types_compatible(r1, r2)
        }
        (Type::ADT(n1, a1), Type::ADT(n2, a2)) => {
            n1 == n2
                && a1.len() == a2.len()
                && a1
                    .iter()
                    .zip(a2.iter())
                    .all(|(a, b)| types_compatible(a, b))
        }
        (Type::Var(_), _) | (_, Type::Var(_)) => true, // Unresolved — assume compatible
        _ => false,
    }
}
