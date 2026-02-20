use std::collections::HashMap;

use crate::ast::*;
use crate::error::CranelispError;
use crate::types::*;

use super::{CheckResult, TypeChecker};

impl TypeChecker {
    /// Type-check a whole program (list of top-level items).
    /// Two-pass: first register all signatures, then check bodies.
    /// Returns method resolutions for trait dispatch and monomorphisation data.
    pub fn check_program(&mut self, program: &Program) -> Result<CheckResult, CranelispError> {
        // Register builtins (primitives + platform) as qualified names,
        // then install bare aliases for the no-module path.
        self.init_builtins();
        self.install_synthetic_bare_names();

        // Register type definitions (deftype) before anything else
        // register_type_def already dual-writes TypeDef + Constructor entries into CompiledModule
        for item in program {
            if matches!(item, TopLevel::TypeDef { .. }) {
                self.register_type_def(item);
            }
        }

        // Register user-defined traits
        for td in crate::ast::trait_decls(program) {
            self.register_trait(td);
        }

        // Validate and register user-defined trait impls
        for ti in crate::ast::trait_impls(program) {
            self.validate_impl(ti)?;
            self.register_impl(ti);
        }

        // Process DefnMulti items: build internal Defns (registration happens in Pass 1)
        let multis = crate::ast::defn_multis(program);
        let mut multi_internal_defns: Vec<Defn> = Vec::new();

        for (name, variants, _span) in &multis {
            let mut overload_entries = Vec::new();
            for (i, variant) in variants.iter().enumerate() {
                let internal_name = format!("{}__v{}", name, i);
                overload_entries.push((internal_name.clone(), variant.params.len()));
                multi_internal_defns.push(Defn {
                    visibility: crate::ast::Visibility::Public,
                    name: internal_name,
                    docstring: None,
                    params: variant.params.clone(),
                    param_annotations: variant.param_annotations.clone(),
                    body: variant.body.clone(),
                    span: variant.span,
                });
            }
            self.overloads.insert(name.to_string(), overload_entries);
        }

        // Extract impl method defns with mangled names (e.g., doubled$Int, show$Option$Int)
        let impl_method_defns = crate::ast::impl_method_defns(program);

        // Build impl self type map: mangled method name → self type for pre-unification.
        // For concrete impls like `(impl Display (Option Int) ...)`, the self type is
        // `Type::ADT("Option", [Type::Int])`, and the method's first param should be unified with it.
        let mut impl_self_types: HashMap<String, Type> = HashMap::new();
        for ti in crate::ast::trait_impls(program) {
            let self_type = self.resolve_impl_self_type(ti)?;
            let target = ti.impl_target_mangled();
            for method in &ti.methods {
                let mangled = format!("{}${}", method.name, target);
                impl_self_types.insert(mangled, self_type.clone());
            }
        }

        let program_defns = crate::ast::defns(program);

        // Collect all defns: regular + impl methods + multi-sig internal
        let mut all_defns: Vec<&Defn> = program_defns.clone();
        for d in &impl_method_defns {
            all_defns.push(d);
        }
        for d in &multi_internal_defns {
            all_defns.push(d);
        }

        // Pass 1: register all function signatures with fresh type variables
        let mut fn_types: Vec<(String, Vec<Type>, Type)> = Vec::new();
        for defn in &all_defns {
            let param_tys: Vec<Type> = defn.params.iter().map(|_| self.fresh_var()).collect();
            let ret_ty = self.fresh_var();
            let fn_ty = Type::Fn(param_tys.clone(), Box::new(ret_ty.clone()));
            self.insert_def(defn.name.clone(), Scheme::mono(fn_ty));
            fn_types.push((defn.name.clone(), param_tys, ret_ty));
        }

        // Process param annotations (between Pass 1 and Pass 2)
        for (defn, (_, param_tys, _)) in all_defns.iter().zip(fn_types.iter()) {
            if !defn.param_annotations.is_empty() {
                for (ann, param_ty) in defn.param_annotations.iter().zip(param_tys.iter()) {
                    if let Some(texpr) = ann {
                        self.resolve_annotation(texpr, param_ty, defn.span)?;
                    }
                }
            }
        }

        // Pass 2: check each body, then generalize immediately so later
        // functions can use this one polymorphically.
        for (defn, (_, param_tys, ret_ty)) in all_defns.iter().zip(fn_types.iter()) {
            // Pre-unify the dispatch param with impl self type if this is an impl method.
            // For HKT methods, the dispatch param is at hkt_param_index; for regular traits, it's 0.
            if let Some(self_type) = impl_self_types.get(&defn.name) {
                let param_idx = self.hkt_param_idx_for_method(&defn.name);
                if let Some(target_param) = param_tys.get(param_idx) {
                    self.unify(target_param, self_type, defn.span)?;
                }
            }

            // Save local_env, add params
            let saved_local = self.local_env.clone();
            for (name, ty) in defn.params.iter().zip(param_tys.iter()) {
                self.local_env.insert(
                    crate::names::Symbol::from(name.as_str()),
                    Scheme::mono(ty.clone()),
                );
            }

            let body_ty = self.infer_expr(&defn.body)?;
            self.unify(&body_ty, ret_ty, defn.span)?;

            // Restore local_env (remove params)
            self.local_env = saved_local;

            // Generalize immediately. Remove the function's own monomorphic
            // entry first so its free type variables get quantified.
            self.remove_def(&defn.name);
            let resolved_ty = apply(
                &self.subst,
                &Type::Fn(param_tys.clone(), Box::new(ret_ty.clone())),
            );
            let scheme = self.generalize(&resolved_ty);
            self.insert_def(defn.name.clone(), scheme);
        }

        // Detect constrained functions BEFORE resolution so that resolve_one_method
        // can recognize polymorphic impl methods (like show$Option) as constrained fns
        // and produce SigDispatch instead of bare TraitMethod calls.
        let mut all_defns_for_constrained: Vec<&Defn> = program_defns.clone();
        for d in &impl_method_defns {
            all_defns_for_constrained.push(d);
        }
        let constrained_fn_names = self.detect_constrained_fns(&all_defns_for_constrained);

        // Resolve all trait methods — the deferral mechanism in resolve_one_method
        // handles unresolved type vars automatically. This makes type variables from
        // operator calls concrete before multi-sig overload resolution needs them.
        let early_trait_resolutions = self.resolve_methods()?;

        // Resolve multi-sig overloads: build mangled names from concrete types
        // Use fn_types from Pass 1 (which were unified during Pass 2)
        let multis_ref = crate::ast::defn_multis(program);
        for (name, variants, _span) in &multis_ref {
            let mut resolved = Vec::new();
            let mut sig_set: Vec<Vec<Type>> = Vec::new();

            for (i, variant) in variants.iter().enumerate() {
                let internal_name = format!("{}__v{}", name, i);
                // Find the fn_types entry for this internal name
                let (_, param_tys, ret_ty) = fn_types
                    .iter()
                    .find(|(n, _, _)| n == &internal_name)
                    .unwrap();

                let concrete_params: Vec<Type> =
                    param_tys.iter().map(|t| apply(&self.subst, t)).collect();
                let concrete_ret = apply(&self.subst, ret_ty);
                let mangled = crate::ast::mangle_sig(name, &concrete_params);

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
                        span: variant.span,
                    });
                }
                sig_set.push(concrete_params.clone());

                let fn_ty = Type::Fn(concrete_params.clone(), Box::new(concrete_ret.clone()));
                let scheme = self.generalize(&fn_ty);
                self.remove_def(&internal_name);
                self.insert_def(mangled.clone(), scheme);

                resolved.push((concrete_params, concrete_ret, mangled));
            }
            self.resolved_overloads.insert(name.to_string(), resolved);
        }

        // Verify main exists and has type () -> IO _
        if let Some(main_scheme) = self.lookup("main") {
            let main_ty = apply(&self.subst, &main_scheme.ty);
            match &main_ty {
                Type::Fn(params, ret) if params.is_empty() => match ret.as_ref() {
                    Type::ADT(name, _) if name == "IO" => {}
                    _ => {
                        return Err(CranelispError::TypeError {
                            message: format!("main must return IO _, but returns {}", ret),
                            span: (0, 0),
                        })
                    }
                },
                Type::Fn(params, _) => {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "main must take no parameters, but takes {}",
                            params.len()
                        ),
                        span: (0, 0),
                    })
                }
                _ => {
                    return Err(CranelispError::TypeError {
                        message: "main must be a function".to_string(),
                        span: (0, 0),
                    })
                }
            }
        } else {
            return Err(CranelispError::TypeError {
                message: "no main function defined".to_string(),
                span: (0, 0),
            });
        }

        // Start with early trait resolutions
        let mut resolutions = early_trait_resolutions;

        // Generate monomorphised specializations + call-site dispatches
        // (from resolve_methods' pending_mono_calls for constrained fns)
        let (mut mono_defns, mono_dispatches) = self.monomorphise_all()?;
        resolutions.extend(mono_dispatches);

        // Resolve overload dispatches (before remaining trait methods, so that
        // return types from overloaded calls become concrete for e.g. show)
        self.resolve_overloads(&mut resolutions)?;

        // Move deferred resolutions back to pending for re-resolution.
        // The first resolve_methods pass may have deferred calls whose arg types
        // depended on multi-sig overload resolution (now complete).
        let deferred = std::mem::take(&mut self.deferred_resolutions);
        self.pending_resolutions.extend(deferred);

        // Resolve remaining trait methods (e.g., show calls whose arg types were
        // determined during overload resolution)
        let late_trait_resolutions = self.resolve_methods()?;
        resolutions.extend(late_trait_resolutions);

        // Run monomorphisation again — resolve_methods may have added new
        // pending_mono_calls (e.g., polymorphic impl methods like show$Option)
        let (late_mono_defns, late_mono_dispatches) = self.monomorphise_all()?;
        mono_defns.extend(late_mono_defns);
        resolutions.extend(late_mono_dispatches);

        // Note: builtin_resolutions are drained inside resolve_methods() above,
        // so they're already included in early_trait_resolutions / late_trait_resolutions.

        // Resolve expr_types through final substitution
        let resolved_expr_types = self
            .expr_types
            .iter()
            .map(|(span, ty)| (*span, apply(&self.subst, ty)))
            .collect();

        Ok(CheckResult {
            method_resolutions: resolutions,
            constrained_fn_names,
            mono_defns,
            expr_types: resolved_expr_types,
        })
    }
}
