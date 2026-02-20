use crate::ast::*;
use crate::error::CranelispError;
use crate::names::{resolve_bare_name, split_dotted, split_qualified, Symbol};
use crate::types::*;

use super::TypeChecker;

impl TypeChecker {
    /// Record the inferred type of an expression by its span.
    fn record_expr_type(&mut self, expr: &Expr, ty: &Type) {
        self.expr_types.insert(expr.span(), ty.clone());
    }

    /// Infer the type of an expression.
    pub(crate) fn infer_expr(&mut self, expr: &Expr) -> Result<Type, CranelispError> {
        match expr {
            Expr::IntLit { .. } => {
                self.record_expr_type(expr, &Type::Int);
                Ok(Type::Int)
            }
            Expr::FloatLit { .. } => {
                self.record_expr_type(expr, &Type::Float);
                Ok(Type::Float)
            }
            Expr::BoolLit { .. } => {
                self.record_expr_type(expr, &Type::Bool);
                Ok(Type::Bool)
            }
            Expr::StringLit { .. } => {
                self.record_expr_type(expr, &Type::String);
                Ok(Type::String)
            }
            Expr::Var { name, span } => {
                // Module-qualified names: "module/local"
                if let Some((module, local)) = split_qualified(name) {
                    if !self.module_names.contains(module) {
                        return Err(CranelispError::TypeError {
                            message: format!(
                                "unknown module '{}' in qualified name '{}'",
                                module, name
                            ),
                            span: *span,
                        });
                    }
                    // If local part is dotted (e.g. "util/Option.Some"), resolve via type/trait validation
                    if let Some((parent, member)) = split_dotted(local) {
                        return self.resolve_qualified_dotted_var(
                            module, parent, member, name, expr, *span,
                        );
                    }
                    // Look up "module/local" directly in env
                    return self.resolve_qualified_var(name, expr, *span);
                }
                // Resolve dotted name: "Parent.member" → validate & look up bare member
                if let Some((parent, member)) = split_dotted(name) {
                    return self.resolve_dotted_var(parent, member, name, expr, *span);
                }
                // Check if bare name is ambiguous (two origins registered it)
                self.check_ambiguity(name, *span)?;
                // Bare reference to an overloaded name is ambiguous
                if self.overloads.contains_key(name) {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "ambiguous reference to overloaded function '{}' — use in a call",
                            name
                        ),
                        span: *span,
                    });
                }
                // Bare reference to a constrained function is ambiguous
                if let Some(scheme) = self.lookup(name) {
                    if scheme.is_constrained() {
                        return Err(CranelispError::TypeError {
                            message: format!(
                                "cannot use constrained function '{}' as a value — call it with arguments",
                                name
                            ),
                            span: *span,
                        });
                    }
                }
                if let Some(scheme) = self.lookup(name) {
                    let scheme = scheme.clone();
                    let ty = self.instantiate(&scheme);
                    // Track builtin references for closure wrapping in codegen
                    if let Some(fq) = self.resolve_builtin_fq(name) {
                        self.builtin_resolutions.insert(
                            *span,
                            crate::typechecker::ResolvedCall::BuiltinFn(fq),
                        );
                    }
                    self.record_expr_type(expr, &ty);
                    Ok(ty)
                } else {
                    Err(CranelispError::TypeError {
                        message: format!("unbound variable: {}", name),
                        span: *span,
                    })
                }
            }
            Expr::Let { bindings, body, .. } => {
                for (name, val_expr) in bindings {
                    let val_ty = self.infer_expr(val_expr)?;
                    self.local_env
                        .insert(Symbol::from(name.as_str()), Scheme::mono(val_ty));
                }
                let ty = self.infer_expr(body)?;
                self.record_expr_type(expr, &ty);
                Ok(ty)
            }
            Expr::If {
                cond,
                then_branch,
                else_branch,
                span,
            } => {
                let cond_ty = self.infer_expr(cond)?;
                self.unify(&cond_ty, &Type::Bool, cond.span())?;
                let then_ty = self.infer_expr(then_branch)?;
                let else_ty = self.infer_expr(else_branch)?;
                self.unify(&then_ty, &else_ty, *span)?;
                let ty = apply(&self.subst, &then_ty);
                self.record_expr_type(expr, &ty);
                Ok(ty)
            }
            Expr::Lambda {
                params,
                param_annotations,
                body,
                span,
            } => {
                let param_tys: Vec<Type> = params.iter().map(|_| self.fresh_var()).collect();
                // Process param annotations
                if !param_annotations.is_empty() {
                    for (ann, param_ty) in param_annotations.iter().zip(param_tys.iter()) {
                        if let Some(texpr) = ann {
                            self.resolve_annotation(texpr, param_ty, *span)?;
                        }
                    }
                }
                let saved_local = self.local_env.clone();
                for (name, ty) in params.iter().zip(param_tys.iter()) {
                    self.local_env
                        .insert(Symbol::from(name.as_str()), Scheme::mono(ty.clone()));
                }
                let body_ty = self.infer_expr(body)?;
                self.local_env = saved_local;
                let fn_ty = Type::Fn(
                    param_tys.iter().map(|t| apply(&self.subst, t)).collect(),
                    Box::new(apply(&self.subst, &body_ty)),
                );
                self.record_expr_type(expr, &fn_ty);
                Ok(fn_ty)
            }
            Expr::Apply {
                callee, args, span, ..
            } => {
                // Intercept: overloaded callee (multi-signature function)
                if let Expr::Var { name, .. } = callee.as_ref() {
                    let effective = resolve_bare_name(name);
                    if self.overloads.contains_key(effective) {
                        let arg_tys: Vec<Type> = args
                            .iter()
                            .map(|a| self.infer_expr(a))
                            .collect::<Result<_, _>>()?;
                        let ret_ty = self.fresh_var();
                        self.pending_overload_resolutions.push((
                            *span,
                            effective.to_string(),
                            arg_tys,
                            ret_ty.clone(),
                        ));
                        self.record_expr_type(expr, &ret_ty);
                        return Ok(ret_ty);
                    }
                }

                // Intercept: constrained function call — instantiate without
                // triggering the Var branch's "cannot use as value" error
                let callee_ty = if let Expr::Var { name, .. } = callee.as_ref() {
                    let effective = resolve_bare_name(name);
                    let is_constrained = self
                        .lookup(effective)
                        .map(|s| s.is_constrained())
                        .unwrap_or(false);
                    if is_constrained {
                        let scheme = self.lookup(effective).unwrap().clone();
                        self.instantiate(&scheme)
                    } else {
                        self.infer_expr(callee)?
                    }
                } else {
                    self.infer_expr(callee)?
                };

                let arg_tys: Vec<Type> = args
                    .iter()
                    .map(|a| self.infer_expr(a))
                    .collect::<Result<_, _>>()?;

                let ret_ty = self.fresh_var();
                let expected = Type::Fn(arg_tys.clone(), Box::new(ret_ty.clone()));
                let unify_result = self.unify(&callee_ty, &expected, *span);

                if let Err(ref _e) = unify_result {
                    // Try auto-curry: callee has more params than provided args
                    let resolved_callee = apply(&self.subst, &callee_ty);
                    if let Type::Fn(params, ret) = &resolved_callee {
                        if args.len() < params.len() && !args.is_empty() {
                            // Unify applied args with first N params
                            for (arg_ty, param_ty) in arg_tys.iter().zip(params.iter()) {
                                self.unify(arg_ty, param_ty, *span)?;
                            }
                            let remaining: Vec<Type> = params[args.len()..]
                                .iter()
                                .map(|t| apply(&self.subst, t))
                                .collect();
                            let curry_ret = Type::Fn(remaining, ret.clone());

                            // Record pending auto-curry resolution
                            if let Expr::Var { name, .. } = callee.as_ref() {
                                self.pending_auto_curry.push((
                                    *span,
                                    resolve_bare_name(name).to_string(),
                                    args.len(),
                                    params.len(),
                                ));
                            }

                            let ty = apply(&self.subst, &curry_ret);
                            self.record_expr_type(expr, &ty);
                            return Ok(ty);
                        }
                    }
                    // Not auto-curryable — propagate original error
                    unify_result?;
                }

                // Track trait method calls for later resolution.
                if let Expr::Var { name, .. } = callee.as_ref() {
                    let effective = resolve_bare_name(name);
                    if let Some(trait_name) = self.find_trait_for_method(effective) {
                        let trait_name = trait_name.to_string();
                        // Determine which arg to use for dispatch:
                        // HKT methods use the constructor-carrying param, others use first
                        let param_idx = self.hkt_param_idx_for_method(effective);
                        if let Some(dispatch_arg_ty) = arg_tys.get(param_idx) {
                            // Eagerly detect constraints: if the arg type is an
                            // unresolved var and multiple impls exist, record a constraint
                            let resolved_arg = apply(&self.subst, dispatch_arg_ty);
                            if let Type::Var(id) = resolved_arg {
                                let impl_count = self
                                    .all_impls()
                                    .filter(|ui| ui.trait_name == trait_name)
                                    .count();
                                if impl_count > 1 {
                                    self.var_constraints
                                        .entry(id)
                                        .or_default()
                                        .insert(trait_name.clone());
                                }
                            }
                            self.pending_resolutions.push((
                                *span,
                                effective.to_string(),
                                dispatch_arg_ty.clone(),
                            ));
                        }
                    }
                }

                // Track calls to constrained functions for monomorphisation.
                // Skip trait methods — they're dispatched via pending_resolutions instead.
                if let Expr::Var { name, .. } = callee.as_ref() {
                    let effective = resolve_bare_name(name);
                    if self.find_trait_for_method(effective).is_none() {
                        if let Some(scheme) = self.lookup(effective) {
                            if scheme.is_constrained() {
                                self.pending_mono_calls.push((
                                    *span,
                                    effective.to_string(),
                                    arg_tys,
                                ));
                            }
                        }
                    }
                }

                // Track calls to builtin extern/platform primitives for resolution-based dispatch.
                if let Expr::Var { name, .. } = callee.as_ref() {
                    let effective = resolve_bare_name(name);
                    if let Some(fq) = self.resolve_builtin_fq(effective) {
                        self.builtin_resolutions.insert(
                            *span,
                            crate::typechecker::ResolvedCall::BuiltinFn(fq),
                        );
                    }
                }

                let ty = apply(&self.subst, &ret_ty);
                self.record_expr_type(expr, &ty);
                Ok(ty)
            }
            Expr::VecLit { elements, span } => {
                let elem_ty = self.fresh_var();
                for elem in elements {
                    let et = self.infer_expr(elem)?;
                    self.unify(&et, &elem_ty, *span)?;
                }
                let resolved = apply(&self.subst, &elem_ty);
                let ty = Type::ADT("Vec".to_string(), vec![resolved]);
                self.record_expr_type(expr, &ty);
                Ok(ty)
            }
            Expr::Match {
                scrutinee,
                arms,
                span: _,
            } => {
                let scrut_ty = self.infer_expr(scrutinee)?;
                let result_ty = self.fresh_var();

                for arm in arms {
                    let saved_local = self.local_env.clone();

                    match &arm.pattern {
                        Pattern::Constructor {
                            name,
                            bindings,
                            span: pat_span,
                        } => {
                            // Module-qualified patterns: "module/Ctor" → look up "module/Ctor"
                            // Also handle "module/Type.Ctor" → validate then look up "module/Ctor"
                            let lookup_name = if let Some((module, local)) = split_qualified(name) {
                                if !self.module_names.contains(module) {
                                    return Err(CranelispError::TypeError {
                                        message: format!(
                                            "unknown module '{}' in qualified pattern '{}'",
                                            module, name
                                        ),
                                        span: *pat_span,
                                    });
                                }
                                if let Some((parent, member)) = split_dotted(local) {
                                    // "module/Type.Ctor" → validate parent type, use "module/Ctor"
                                    let qualified_parent = format!("{}/{}", module, parent);
                                    let td_key = if self.resolve_type_def_via_modules(&qualified_parent).is_some() {
                                        qualified_parent
                                    } else if self.resolve_type_def_via_modules(parent).is_some() {
                                        parent.to_string()
                                    } else {
                                        return Err(CranelispError::TypeError {
                                            message: format!("'{}' is not a known type", parent),
                                            span: *pat_span,
                                        });
                                    };
                                    if let Some(td) = self.resolve_type_def_via_modules(&td_key) {
                                        if !td.constructors.iter().any(|c| c.name == member) {
                                            return Err(CranelispError::TypeError {
                                                message: format!(
                                                    "'{}' is not a constructor of type '{}'",
                                                    member, parent
                                                ),
                                                span: *pat_span,
                                            });
                                        }
                                    }
                                    format!("{}/{}", module, member)
                                } else {
                                    // "module/Ctor" → use directly
                                    name.clone()
                                }
                            } else if let Some((parent, member)) = split_dotted(name) {
                                // Validate parent is a type with member as constructor
                                if let Some(td) = self.resolve_type_def_via_modules(parent) {
                                    if !td.constructors.iter().any(|c| c.name == member) {
                                        return Err(CranelispError::TypeError {
                                            message: format!(
                                                "'{}' is not a constructor of type '{}'",
                                                member, parent
                                            ),
                                            span: *pat_span,
                                        });
                                    }
                                } else {
                                    return Err(CranelispError::TypeError {
                                        message: format!(
                                            "'{}' is not a known type or trait",
                                            parent
                                        ),
                                        span: *pat_span,
                                    });
                                }
                                member.to_string()
                            } else {
                                name.clone()
                            };
                            // Look up constructor in env
                            let ctor_scheme = self
                                .lookup(&lookup_name)
                                .ok_or_else(|| CranelispError::TypeError {
                                    message: format!("unknown constructor: {}", name),
                                    span: *pat_span,
                                })?
                                .clone();
                            let ctor_ty = self.instantiate(&ctor_scheme);

                            match &ctor_ty {
                                Type::Fn(field_tys, ret_ty) => {
                                    if bindings.len() != field_tys.len() {
                                        return Err(CranelispError::TypeError {
                                            message: format!(
                                                "constructor {} expects {} fields, got {} bindings",
                                                name,
                                                field_tys.len(),
                                                bindings.len()
                                            ),
                                            span: *pat_span,
                                        });
                                    }
                                    self.unify(&scrut_ty, ret_ty, *pat_span)?;
                                    for (binding, field_ty) in bindings.iter().zip(field_tys.iter())
                                    {
                                        let resolved = apply(&self.subst, field_ty);
                                        self.local_env.insert(
                                            Symbol::from(binding.as_str()),
                                            Scheme::mono(resolved),
                                        );
                                    }
                                }
                                // Nullary constructor — no bindings expected
                                Type::ADT(..) => {
                                    if !bindings.is_empty() {
                                        return Err(CranelispError::TypeError {
                                            message: format!(
                                                "nullary constructor {} takes no fields, got {} bindings",
                                                name, bindings.len()
                                            ),
                                            span: *pat_span,
                                        });
                                    }
                                    self.unify(&scrut_ty, &ctor_ty, *pat_span)?;
                                }
                                _ => {
                                    return Err(CranelispError::TypeError {
                                        message: format!("{} is not a constructor", name),
                                        span: *pat_span,
                                    });
                                }
                            }
                        }
                        Pattern::Var { name, .. } => {
                            let resolved = apply(&self.subst, &scrut_ty);
                            self.local_env
                                .insert(Symbol::from(name.as_str()), Scheme::mono(resolved));
                        }
                        Pattern::Wildcard { .. } => {}
                    }

                    let body_ty = self.infer_expr(&arm.body)?;
                    self.unify(&body_ty, &result_ty, arm.span)?;

                    self.local_env = saved_local;
                }

                let ty = apply(&self.subst, &result_ty);
                self.record_expr_type(expr, &ty);
                Ok(ty)
            }
            Expr::Annotate {
                annotation,
                expr: inner,
                span,
            } => {
                let inner_ty = self.infer_expr(inner)?;
                self.resolve_annotation(annotation, &inner_ty, *span)?;
                let ty = apply(&self.subst, &inner_ty);
                self.record_expr_type(expr, &ty);
                Ok(ty)
            }
        }
    }

    /// Resolve a dotted var reference like "Option.Some" or "Display.show".
    /// Validates the parent is a type or trait, and the member is a valid constructor/method.
    fn resolve_dotted_var(
        &mut self,
        parent: &str,
        member: &str,
        full_name: &str,
        expr: &Expr,
        span: crate::error::Span,
    ) -> Result<Type, CranelispError> {
        // Check if parent is a type with member as constructor or field accessor
        if let Some(td) = self.resolve_type_def_via_modules(parent) {
            // Try constructor first, then field accessor
            let scheme: Option<Scheme> = if td.constructors.iter().any(|c| c.name == member) {
                self.lookup_constructor_scheme(parent, member).cloned()
            } else if td
                .constructors
                .iter()
                .any(|c| c.fields.iter().any(|(f, _)| f == member))
            {
                // Field accessor: Type.field — constructs scheme from TypeDefInfo
                self.lookup_field_accessor_scheme(parent, member)
            } else {
                None
            };
            if let Some(scheme) = scheme {
                // Check for overloaded/constrained as the Var branch would
                if self.overloads.contains_key(member) {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "ambiguous reference to overloaded function '{}' — use in a call",
                            full_name
                        ),
                        span,
                    });
                }
                if scheme.is_constrained() {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "cannot use constrained function '{}' as a value — call it with arguments",
                            full_name
                        ),
                        span,
                    });
                }
                let ty = self.instantiate(&scheme);
                self.record_expr_type(expr, &ty);
                return Ok(ty);
            }
            return Err(CranelispError::TypeError {
                message: format!(
                    "'{}' is not a constructor or field of type '{}'",
                    member, parent
                ),
                span,
            });
        }

        // Check if parent is a trait with member as method.
        // Check has_method first with &self borrow, then drop it before &mut self call.
        let trait_has_method = self
            .find_trait_decl(parent)
            .map(|decl| decl.methods.iter().any(|m| m.name == member));
        if let Some(has_method) = trait_has_method {
            if has_method {
                // Valid Trait.method — construct scheme from TraitDecl (bypasses ambiguity)
                if let Some(scheme) = self.lookup_trait_method_scheme(parent, member) {
                    if self.overloads.contains_key(member) {
                        return Err(CranelispError::TypeError {
                            message: format!(
                                "ambiguous reference to overloaded function '{}' — use in a call",
                                full_name
                            ),
                            span,
                        });
                    }
                    if scheme.is_constrained() {
                        return Err(CranelispError::TypeError {
                            message: format!(
                                "cannot use constrained function '{}' as a value — call it with arguments",
                                full_name
                            ),
                            span,
                        });
                    }
                    let ty = self.instantiate(&scheme);
                    self.record_expr_type(expr, &ty);
                    return Ok(ty);
                }
            }
            return Err(CranelispError::TypeError {
                message: format!("'{}' is not a method of trait '{}'", member, parent),
                span,
            });
        }

        Err(CranelispError::TypeError {
            message: format!("'{}' is not a known type or trait", parent),
            span,
        })
    }

    /// Resolve a module-qualified variable like "util/foo".
    /// The name is looked up directly in the env (registered by register_qualified_aliases).
    fn resolve_qualified_var(
        &mut self,
        qualified_name: &str,
        expr: &Expr,
        span: crate::error::Span,
    ) -> Result<Type, CranelispError> {
        if let Some(scheme) = self.lookup(qualified_name) {
            let scheme = scheme.clone();
            if scheme.is_constrained() {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "cannot use constrained function '{}' as a value — call it with arguments",
                        qualified_name
                    ),
                    span,
                });
            }
            let ty = self.instantiate(&scheme);
            self.record_expr_type(expr, &ty);
            Ok(ty)
        } else {
            Err(CranelispError::TypeError {
                message: format!("unbound qualified name: {}", qualified_name),
                span,
            })
        }
    }

    /// Resolve a module-qualified dotted var like "util/Option.Some" or "util/Display.show".
    fn resolve_qualified_dotted_var(
        &mut self,
        module: &str,
        parent: &str,
        member: &str,
        _full_name: &str,
        expr: &Expr,
        span: crate::error::Span,
    ) -> Result<Type, CranelispError> {
        // Try qualified parent first ("util/Option"), then bare parent ("Option")
        let td_key = {
            let qualified_parent = format!("{}/{}", module, parent);
            if self.resolve_type_def_via_modules(&qualified_parent).is_some() {
                Some(qualified_parent)
            } else if self.resolve_type_def_via_modules(parent).is_some() {
                Some(parent.to_string())
            } else {
                None
            }
        };

        if let Some(key) = td_key {
            if let Some(td) = self.resolve_type_def_via_modules(&key) {
                if td.constructors.iter().any(|c| c.name == member) {
                    // Look up "module/member" in env
                    let qualified_member = format!("{}/{}", module, member);
                    let lookup = if self.lookup(&qualified_member).is_some() {
                        qualified_member
                    } else {
                        member.to_string()
                    };
                    if let Some(scheme) = self.lookup(&lookup) {
                        let scheme = scheme.clone();
                        let ty = self.instantiate(&scheme);
                        self.record_expr_type(expr, &ty);
                        return Ok(ty);
                    }
                }
                return Err(CranelispError::TypeError {
                    message: format!("'{}' is not a constructor of type '{}'", member, parent),
                    span,
                });
            }
        }

        // Check if parent is a trait
        if self.find_trait_decl(parent).is_some() {
            if self.find_trait_for_method(member) == Some(parent) {
                let qualified_member = format!("{}/{}", module, member);
                let lookup = if self.lookup(&qualified_member).is_some() {
                    qualified_member
                } else {
                    member.to_string()
                };
                if let Some(scheme) = self.lookup(&lookup) {
                    let scheme = scheme.clone();
                    let ty = self.instantiate(&scheme);
                    self.record_expr_type(expr, &ty);
                    return Ok(ty);
                }
            }
            return Err(CranelispError::TypeError {
                message: format!("'{}' is not a method of trait '{}'", member, parent),
                span,
            });
        }

        Err(CranelispError::TypeError {
            message: format!(
                "'{}' is not a known type or trait in module '{}'",
                parent, module
            ),
            span,
        })
    }

    /// Type-check a single function definition incrementally (for REPL).
    /// Registers the function type in the environment and returns its generalized scheme.
    pub fn check_defn(&mut self, defn: &Defn) -> Result<Scheme, CranelispError> {
        // Create fresh type variables for params and return type
        let param_tys: Vec<Type> = defn.params.iter().map(|_| self.fresh_var()).collect();
        let ret_ty = self.fresh_var();
        let fn_ty = Type::Fn(param_tys.clone(), Box::new(ret_ty.clone()));

        // Process param annotations
        if !defn.param_annotations.is_empty() {
            for (ann, param_ty) in defn.param_annotations.iter().zip(param_tys.iter()) {
                if let Some(texpr) = ann {
                    self.resolve_annotation(texpr, param_ty, defn.span)?;
                }
            }
        }

        // Register the function (allows recursion)
        self.insert_def(defn.name.clone(), Scheme::mono(fn_ty));

        // Check body with params in scope
        let saved_local = self.local_env.clone();
        for (name, ty) in defn.params.iter().zip(param_tys.iter()) {
            self.local_env
                .insert(Symbol::from(name.as_str()), Scheme::mono(ty.clone()));
        }

        let body_ty = self.infer_expr(&defn.body)?;
        self.unify(&body_ty, &ret_ty, defn.span)?;

        // Restore env (remove params)
        self.local_env = saved_local;

        // Remove the function's own monomorphic entry before generalizing,
        // otherwise its free type variables appear "in the env" and won't
        // be quantified (breaking polymorphism).
        self.remove_def(&defn.name);
        let resolved_ty = apply(&self.subst, &Type::Fn(param_tys, Box::new(ret_ty)));
        let scheme = self.generalize(&resolved_ty);
        self.insert_def(defn.name.clone(), scheme.clone());

        // Store function metadata (docstring + param names)
        let meta = super::SymbolMeta::UserFn {
            docstring: defn.docstring.clone(),
            param_names: defn.params.clone(),
        };
        self.update_current_module_meta(&defn.name, meta);

        Ok(scheme)
    }

    /// Type-check an impl method definition, pre-unifying the first param with self_type.
    /// Used in REPL for trait impl methods that need their first param to be a specific type.
    pub fn check_impl_method(
        &mut self,
        defn: &Defn,
        self_type: &Type,
    ) -> Result<Scheme, CranelispError> {
        let param_tys: Vec<Type> = defn.params.iter().map(|_| self.fresh_var()).collect();
        let ret_ty = self.fresh_var();
        let fn_ty = Type::Fn(param_tys.clone(), Box::new(ret_ty.clone()));

        // Process param annotations
        if !defn.param_annotations.is_empty() {
            for (ann, param_ty) in defn.param_annotations.iter().zip(param_tys.iter()) {
                if let Some(texpr) = ann {
                    self.resolve_annotation(texpr, param_ty, defn.span)?;
                }
            }
        }

        self.insert_def(defn.name.clone(), Scheme::mono(fn_ty));

        // Pre-unify dispatch param with self type (HKT-aware)
        let param_idx = self.hkt_param_idx_for_method(&defn.name);
        if let Some(target_param) = param_tys.get(param_idx) {
            self.unify(target_param, self_type, defn.span)?;
        }

        let saved_local = self.local_env.clone();
        for (name, ty) in defn.params.iter().zip(param_tys.iter()) {
            self.local_env
                .insert(Symbol::from(name.as_str()), Scheme::mono(ty.clone()));
        }

        let body_ty = self.infer_expr(&defn.body)?;
        self.unify(&body_ty, &ret_ty, defn.span)?;

        self.local_env = saved_local;

        self.remove_def(&defn.name);
        let resolved_ty = apply(&self.subst, &Type::Fn(param_tys, Box::new(ret_ty)));
        let scheme = self.generalize(&resolved_ty);
        self.insert_def(defn.name.clone(), scheme.clone());

        Ok(scheme)
    }

    /// Type-check a bare expression (for REPL evaluation).
    /// Returns the resolved type.
    pub fn check_expr(&mut self, expr: &Expr) -> Result<Type, CranelispError> {
        let ty = self.infer_expr(expr)?;
        Ok(apply(&self.subst, &ty))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast_builder::parse_program;
    use crate::ast_builder::{parse_expr, parse_repl_input};

    const PRELUDE: &str = include_str!("../unittest_prelude.cl");

    fn tc_with_prelude() -> TypeChecker {
        let mut tc = TypeChecker::new();
        tc.init_builtins();
        tc.install_synthetic_bare_names();
        let prelude_program = parse_program(PRELUDE).unwrap();
        // Register type definitions first
        for item in &prelude_program {
            if matches!(item, TopLevel::TypeDef { .. }) {
                tc.register_type_def(item);
            }
        }
        for item in &prelude_program {
            match item {
                TopLevel::TraitDecl(td) => {
                    tc.register_trait_public(td);
                }
                TopLevel::TraitImpl(ti) => {
                    tc.validate_impl_public(ti).unwrap();
                    tc.register_impl(ti);
                    for method in &ti.methods {
                        let mangled = Defn {
                            visibility: crate::ast::Visibility::Public,
                            name: format!("{}${}", method.name, ti.target_type),
                            docstring: None,
                            params: method.params.clone(),
                            param_annotations: method.param_annotations.clone(),
                            body: method.body.clone(),
                            span: method.span,
                        };
                        tc.check_defn(&mangled).unwrap();
                    }
                }
                _ => {}
            }
        }
        tc
    }

    #[test]
    fn repl_polymorphic_defn_used_at_different_types() {
        let mut tc = tc_with_prelude();

        // Define a polymorphic function
        let input = parse_repl_input("(defn sandwich [x] 3)").unwrap();
        if let ReplInput::Defn(defn) = input {
            tc.check_defn(&defn).unwrap();
        }

        // Call with Int — should succeed
        let expr = parse_expr("(sandwich 4)").unwrap();
        tc.check_expr(&expr).unwrap();

        // Call with Bool — should also succeed (polymorphic)
        let expr = parse_expr("(sandwich true)").unwrap();
        tc.check_expr(&expr).unwrap();
    }

    #[test]
    fn annotation_concrete_type() {
        let mut tc = tc_with_prelude();
        let expr = parse_expr(":Int 42").unwrap();
        let ty = tc.check_expr(&expr).unwrap();
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn annotation_constrains_param() {
        let mut tc = tc_with_prelude();
        let input = parse_repl_input("(defn f [x] :Int x)").unwrap();
        if let ReplInput::Defn(defn) = input {
            let scheme = tc.check_defn(&defn).unwrap();
            // f should be (fn [Int] Int)
            assert_eq!(scheme.ty, Type::Fn(vec![Type::Int], Box::new(Type::Int)));
        }
    }

    #[test]
    fn annotation_type_mismatch_error() {
        let mut tc = tc_with_prelude();
        let expr = parse_expr(":Bool 42").unwrap();
        assert!(tc.check_expr(&expr).is_err());
    }

    #[test]
    fn annotation_applied_type() {
        let mut tc = tc_with_prelude();
        let expr = parse_expr(":(Option Int) None").unwrap();
        let ty = tc.check_expr(&expr).unwrap();
        assert_eq!(ty, Type::ADT("Option".to_string(), vec![Type::Int]));
    }

    #[test]
    fn param_annotation_concrete() {
        let mut tc = tc_with_prelude();
        let input = parse_repl_input("(defn f [:Int x] x)").unwrap();
        if let ReplInput::Defn(defn) = input {
            let scheme = tc.check_defn(&defn).unwrap();
            assert_eq!(scheme.ty, Type::Fn(vec![Type::Int], Box::new(Type::Int)));
        }
    }

    #[test]
    fn qualified_name_unknown_module_error() {
        let mut tc = tc_with_prelude();
        let expr = parse_expr("core.option/Some").unwrap();
        let result = tc.check_expr(&expr);
        assert!(result.is_err());
        let err_msg = format!("{}", result.unwrap_err());
        assert!(
            err_msg.contains("unknown module"),
            "expected unknown module error, got: {}",
            err_msg
        );
    }

    #[test]
    fn param_annotation_trait_constraint() {
        let mut tc = tc_with_prelude();
        let input = parse_repl_input("(defn add [:Num x :Num y] (+ x y))").unwrap();
        if let ReplInput::Defn(defn) = input {
            let scheme = tc.check_defn(&defn).unwrap();
            // Should be constrained polymorphic
            assert!(scheme.is_constrained());
            assert!(!scheme.constraints.is_empty());
        }
    }
}
