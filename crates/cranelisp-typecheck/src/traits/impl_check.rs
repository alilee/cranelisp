use std::collections::{HashMap, HashSet};

use cranelisp_types::{ErrorLocation, CranelispError, DefKind, Defn, DefnVariant, FQTraitName, ModuleEntry, ModuleFullPath, MonoDefnVariant, ResolvedCall,
    Span, Symbol, TraitDeclInfo, TraitImpl, TraitMethodSig, Type, TypeId,
    TypeName, UserFnState, Visibility, apply,
};

use crate::checker::{CheckState, TypeCheckEnv};
use crate::scheme;
use super::*;

// ---------------------------------------------------------------------------
// Impl Registration and Checking
// ---------------------------------------------------------------------------

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Register and validate a trait implementation.
    pub(crate) fn register_trait_impl(
        &self,
        state: &mut CheckState,
        impl_: &TraitImpl,
    ) -> Result<Vec<Defn>, CranelispError> {
        // Look up the trait declaration via SymbolTables
        let decl = self
            .lookup_trait_decl_with_state(state, &impl_.trait_name.name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("unknown trait: {}", impl_.trait_name),
                location: ErrorLocation::from_span(impl_.span),
            })?;

        // HKT arity validation: if the trait has constructor variables,
        // verify the impl target is a type constructor with matching arity.
        if !decl.type_params.is_empty() {
            let is_hkt = decl.methods.iter().any(|m| {
                m.params
                    .iter()
                    .any(|(_, p)| type_expr_uses_con_var(p, &decl.type_params))
                    || type_expr_uses_con_var(&m.ret_type, &decl.type_params)
            });
            if is_hkt {
                for con_name in &decl.type_params {
                    if let Some(expected_arity) = con_var_arity(&decl, con_name) {
                        // Check if impl target is a primitive type
                        if expected_arity > 0 {
                            match impl_target_name_or_panic(&impl_.target).as_ref() {
                                "Int" | "Bool" | "String" | "Float" => {
                                    return Err(CranelispError::TypeError {
                                        message: format!(
                                            "{} is not a type constructor (trait {} expects arity {})",
                                            impl_target_name_or_panic(&impl_.target), impl_.trait_name, expected_arity
                                        ),
                                        location: ErrorLocation::from_span(impl_.span),
                                    });
                                }
                                _ => {}
                            }
                        }
                        // Check arity of known ADT types
                        if let Some(td) = self.lookup_type_def_with_state(state, impl_target_name_or_panic(&impl_.target))
                            && td.type_params.len() != expected_arity
                        {
                            return Err(CranelispError::TypeError {
                                message: format!(
                                    "{} has {} type parameters, but trait {} expects a constructor with arity {}",
                                    impl_target_name_or_panic(&impl_.target),
                                    td.type_params.len(),
                                    impl_.trait_name,
                                    expected_arity
                                ),
                                location: ErrorLocation::from_span(impl_.span),
                            });
                        }
                    }
                }
            }
        }

        // Check all required methods are present (that don't have defaults)
        self.check_impl_methods_present(state, &decl, impl_)?;

        // Generate default method implementations for missing methods
        let default_defns =
            self.generate_default_methods(state, &decl, impl_)?;

        // Register the impl as a ModuleEntry::TraitImpl in the trait's
        // **defining module** (Decision 45 / Pattern B). The write target is
        // resolved by chain-following the trait reference from the writer's
        // current module back to its home — not the writer's lexical module.
        //
        // For builtin trait impls (trait declared in `primitives`, written
        // from `primitives`), the chain is length-zero, and the write target
        // coincides with `state.current_module`. For user-mode impls
        // (trait imported into the writer's module), the chain follows the
        // per-symbol `ModuleEntry::Import` binding back to the trait's home,
        // and the write lands there — not in the writer's table.
        // Trait reachability was just validated by `lookup_trait_decl_with_state`
        // above; the chain-follow must succeed. Treat absence as a typecheck
        // invariant violation (post-FIXME 0192 method 6 deletion: no
        // `defining_module_for` fallback).
        // `impl_.trait_name: TraitRef` carries `name: TraitName` + optional
        // module qualification (Decision 47 — syntactic-stage shape).
        let bare_trait_name = impl_.trait_name.name.clone();
        let trait_home = self
            .resolve_trait(state, bare_trait_name.as_ref(), impl_.span)
            .map_err(cranelisp_types::CranelispError::from)?;
        let fq_trait_name = FQTraitName::new(trait_home.clone(), bare_trait_name.clone());
        let fq_impl_type = self
            .resolve_type(state, impl_target_name_or_panic(&impl_.target), impl_.span)
            .map_err(cranelisp_types::CranelispError::from)?;

        let method_names: Vec<Symbol> = impl_.methods.iter()
            .map(|m| m.name.clone())
            .collect();

        let impl_key = Symbol::from(format!(
            "impl${}${}",
            fq_impl_type, fq_trait_name
        ));
        self.symbol_table_mut_in(&trait_home).insert(
            impl_key,
            ModuleEntry::TraitImpl {
                trait_name: fq_trait_name,
                impl_type: fq_impl_type,
                methods: method_names,
                visibility: Visibility::Public,
            },
        );

        // Type-check each impl method body and generate mangled-name Defns.
        // check_impl_method returns the annotated defn (already written to
        // ModuleEntry::Def.ast under the mangled name).
        let mut all_defns = Vec::with_capacity(default_defns.len() + impl_.methods.len());

        // Default methods: each defn's name is already mangled (e.g.,
        // "Countable.count-plus$Int"). Type-check with the corresponding
        // trait method sig so the body is inferred with concrete Self, and
        // the result is written to ModuleEntry::Def.ast. This prevents
        // Pass 2's check_form_body_single_defn from re-inferring with fresh
        // vars and spuriously marking the method as a constrained_fn
        // (→ null GOT slot → SIGSEGV on dispatch).
        for default_defn in &default_defns {
            // Recover the unmangled method name from the mangled form.
            // Expected format: "{trait_name}.{method_name}${target_type}"
            let mangled = default_defn.name.as_ref();
            let prefix = format!("{}.", decl.name);
            let suffix = format!("${}", impl_target_name_or_panic(&impl_.target));
            let method_name = mangled
                .strip_prefix(&prefix)
                .and_then(|s| s.strip_suffix(&suffix))
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!(
                        "internal: default method defn name {} does not match expected mangled form",
                        mangled
                    ),
                    location: ErrorLocation::from_span(default_defn.span),
                })?;
            let method_sig = decl
                .methods
                .iter()
                .find(|m| m.name.as_ref() == method_name)
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!(
                        "internal: trait {} has no method named {}",
                        decl.name, method_name
                    ),
                    location: ErrorLocation::from_span(default_defn.span),
                })?;
            let annotated = self.check_impl_method_with_sig(
                state,
                &decl,
                impl_,
                default_defn,
                method_sig,
                true,
                // D1 (S86): a synthesized default-method body resolves its free
                // names in the trait's DEFINING module, not the impl writer's.
                Some(&trait_home),
            )?;
            all_defns.push(annotated);
        }

        for method_defn in &impl_.methods {
            let annotated = self.check_impl_method(
                state,
                &decl,
                impl_,
                method_defn,
            )?;
            all_defns.push(annotated);
        }

        Ok(all_defns)
    }

    /// Check that all required methods are provided in the impl.
    fn check_impl_methods_present(
        &self,
        _state: &CheckState,
        decl: &TraitDeclInfo,
        impl_: &TraitImpl,
    ) -> Result<(), CranelispError> {
        let provided: std::collections::HashSet<&str> = impl_
            .methods
            .iter()
            .map(|m| m.name.as_ref())
            .collect();

        for method_sig in &decl.methods {
            // Skip methods with defaults
            if method_sig.default_body.is_some() {
                continue;
            }
            if !provided.contains(method_sig.name.as_ref()) {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "impl {} for {}: missing required method {}",
                        decl.name, impl_target_name_or_panic(&impl_.target), method_sig.name
                    ),
                    location: ErrorLocation::from_span(impl_.span),
                });
            }
        }

        Ok(())
    }

    /// Type-check a single impl method.
    ///
    /// Clones the method defn, type-checks the body, annotates the clone
    /// with resolved calls and inferred types from side maps, applies final
    /// substitution, and writes the annotated defn to `ModuleEntry::Def.ast`
    /// under the mangled name.
    fn check_impl_method(
        &self,
        state: &mut CheckState,
        decl: &TraitDeclInfo,
        impl_: &TraitImpl,
        method_defn: &Defn,
    ) -> Result<Defn, CranelispError> {
        // Look up the method signature from the trait by the defn's (unmangled) name.
        let method_sig = decl
            .methods
            .iter()
            .find(|m| m.name == method_defn.name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!(
                    "method {} not found in trait {}",
                    method_defn.name, decl.name
                ),
                location: ErrorLocation::from_span(method_defn.span),
            })?;
        // `home: None` — an explicit impl-provided method body is correct in the
        // writer's (current) module scope; no defining-module switch (D1, S86).
        self.check_impl_method_with_sig(state, decl, impl_, method_defn, method_sig, false, None)
    }

    /// Type-check an impl method (or default method) given an explicit trait method sig.
    ///
    /// `is_default_mangled` = true indicates the `method_defn.name` is already mangled
    /// (`Trait.method$Type`) as generated by `generate_default_methods`. In that case
    /// the existing name is used as the symbol-table key; otherwise the mangled name is
    /// built from `impl_.trait_name + method_defn.name + impl_target_name_or_panic(&impl_.target)`.
    ///
    /// `home` is `Some(trait_defining_module)` for a SYNTHESIZED default-method body
    /// (D1, S86): the body's free names (a bare primitive like `add-i64`, another
    /// trait method) live in the trait's DEFINING module, not the impl-writer's
    /// (caller's) module. `state.current_module` is saved and switched to `home`
    /// around the body check, then restored — mirroring `recheck_body_for_mono`'s
    /// FIXME-0355 switch. `None` (an explicit impl-provided method) leaves the
    /// current module unchanged: the writer's lexical scope is correct for it.
    #[allow(clippy::too_many_arguments)]
    fn check_impl_method_with_sig(
        &self,
        state: &mut CheckState,
        decl: &TraitDeclInfo,
        impl_: &TraitImpl,
        method_defn: &Defn,
        method_sig: &TraitMethodSig,
        is_default_mangled: bool,
        home: Option<&ModuleFullPath>,
    ) -> Result<Defn, CranelispError> {
        let mut local_next_id = self.next_id_snapshot();

        // Check if this is an HKT trait (constructor variables used in Applied position)
        let is_hkt = !decl.type_params.is_empty()
            && decl.methods.iter().any(|m| {
                m.params
                    .iter()
                    .any(|(_, p)| type_expr_uses_con_var(p, &decl.type_params))
                    || type_expr_uses_con_var(&m.ret_type, &decl.type_params)
            });

        if is_hkt {
            return self.check_hkt_impl_method(state, decl, impl_, method_defn, method_sig);
        }

        // Resolve the concrete type for Self.
        // For parameterized impls like `(impl Showable (MyOpt Int) ...)`,
        // type_args contains the concrete type arguments (e.g., ["Int"]).
        // Phase B Part 1.4(3): when the target resolves to an intrinsic
        // scalar (Int/Bool/Float/String), `concrete_self` becomes the
        // intrinsic's bare `Type::Int` (etc.); ADT-shaped targets become
        // `Type::ADT(target_fqtn, type_args)`. The dispatch is centralised
        // in `concrete_type_for_impl_target`. C-4: `type_args` child
        // structure lives inside `impl_.target` (TypeExpr).
        let target_args: Vec<cranelisp_types::TypeExpr> = match &impl_.target {
            cranelisp_types::TypeExpr::Applied(_, args) => args.clone(),
            _ => Vec::new(),
        };
        let resolved_type_args: Vec<Type> = target_args
            .iter()
            .map(|arg| -> Result<Type, cranelisp_types::CranelispError> {
                let head_name = arg.head_ref().map(|r| r.name.as_ref()).unwrap_or_else(|| {
                    match arg {
                        cranelisp_types::TypeExpr::TypeVar(name) => name.as_ref(),
                        _ => "_",
                    }
                });
                self.concrete_type_for_impl_target(
                    state,
                    &TypeName::from(head_name),
                    Vec::new(),
                    impl_.span,
                )
                .map_err(cranelisp_types::CranelispError::from)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let concrete_self = self
            .concrete_type_for_impl_target(
                state,
                impl_target_name_or_panic(&impl_.target),
                resolved_type_args,
                impl_.span,
            )
            .map_err(cranelisp_types::CranelispError::from)?;

        // Pre-seed var_map: trait type params map to concrete self type.
        let mut var_map: HashMap<Symbol, Type> = HashMap::new();
        for param in &decl.type_params {
            var_map.insert(param.clone(), concrete_self.clone());
        }

        // Build concrete param types
        let param_types: Vec<Type> = method_sig
            .params
            .iter()
            .map(|(_, p)| resolve_trait_type_expr(p, &concrete_self, method_defn.span, &mut var_map, &mut local_next_id))
            .collect::<Result<Vec<_>, _>>()?;

        let ret_ty = resolve_trait_type_expr(
            &method_sig.ret_type,
            &concrete_self,
            method_defn.span,
            &mut var_map,
            &mut local_next_id,
        )?;

        self.commit_next_id(local_next_id);

        // Snapshot side maps for per-defn delta extraction
        let mr_before: HashSet<Span> = state.method_resolutions.resolved_calls.keys().copied().collect();
        let et_before: HashSet<Span> = state.expr_types.keys().copied().collect();

        // Clone the method defn and check the body with the mutable copy.
        //
        // D1 (S86): for a SYNTHESIZED default-method body (`home: Some(trait_home)`),
        // switch `state.current_module` into the trait's defining module around the
        // body check so the body's free names (a bare primitive, another trait
        // method) resolve in the defining module's import context — not the
        // impl-writer's, where they may be out of scope (`undefined variable:
        // add-i64`). Mirrors `recheck_body_for_mono`'s FIXME-0355 switch. The
        // module is restored before the mangled-name writeback so the annotated
        // defn lands in the writer's table as before. `None` leaves the module
        // unchanged (an explicit impl-provided method is correct in the writer's
        // scope).
        let saved_current_module =
            home.map(|h| std::mem::replace(&mut state.current_module, h.clone()));

        let mut method_clone = method_defn.clone();
        let body_result =
            self.check_defn_body_with_types(state, &mut method_clone, &param_types, &ret_ty);

        // Per-defn post-passes (auto-curry only; overloads deferred to finalize).
        // Run under the switched module too (auto-curry resolution mirrors the
        // body's scope), matching `recheck_body_for_mono`.
        if body_result.is_ok() {
            self.resolve_auto_curry(state);
        }

        // Restore the writer's module before the writeback (unconditional, mirrors
        // `recheck_body_for_mono`'s save/restore discipline).
        if let Some(prev) = saved_current_module {
            state.current_module = prev;
        }

        body_result?;

        // Build the mangled name and create annotated defn for symbol table.
        // For default methods, `method_defn.name` is already mangled by
        // generate_default_methods (e.g., "Countable.count-plus$Int"), so we
        // use the name as-is to avoid double-mangling.
        let mangled_sym = if is_default_mangled {
            method_defn.name.clone()
        } else {
            let mangled = format!(
                "{}.{}${}",
                impl_.trait_name, method_defn.name, impl_target_name_or_panic(&impl_.target)
            );
            Symbol::from(mangled.as_str())
        };

        self.finalize_impl_method_writeback(
            state,
            method_defn,
            &method_clone,
            mangled_sym,
            &param_types,
            &ret_ty,
            &mr_before,
            &et_before,
        )
    }

    /// Shared tail of `check_impl_method_with_sig` / `check_hkt_impl_method`.
    ///
    /// Both methods, after checking the method body with concrete param/return
    /// types, extract the per-defn side-map delta, annotate a fresh `Defn`
    /// clone with those types + resolved calls, apply the final substitution,
    /// and write the annotated `DefnVariant` into the symbol table (inserting a
    /// concrete-scheme `Def` entry if one doesn't already exist). `mr_before` /
    /// `et_before` are the side-map key snapshots taken *before* the body check.
    ///
    /// The symbol table entry may not yet exist because `register_trait_impl`
    /// runs during Pass 1's TraitImpl processing, BEFORE the mangled-name Defns
    /// are iterated through `check_form_register` (which calls
    /// `register_defn_signature` to create the Def entry). We insert a fresh Def
    /// entry here so that:
    ///   1. `ast: Some(annotated)` persists through later `register_defn_signature`
    ///      (which now preserves existing ast).
    ///   2. `check_form_body_single_defn` short-circuits on `ast: Some(_)`,
    ///      avoiding spurious re-inference that would acquire trait constraints
    ///      on fresh type vars and mark the method as a constrained_fn — which
    ///      would cause codegen to skip it, leaving a null GOT slot → SIGSEGV.
    #[allow(clippy::too_many_arguments)]
    fn finalize_impl_method_writeback(
        &self,
        state: &mut CheckState,
        method_defn: &Defn,
        method_clone: &Defn,
        mangled_sym: Symbol,
        param_types: &[Type],
        ret_ty: &Type,
        mr_before: &HashSet<Span>,
        et_before: &HashSet<Span>,
    ) -> Result<Defn, CranelispError> {
        // Extract delta: only entries added during this method's body check
        let method_mr: HashMap<Span, ResolvedCall> = state.method_resolutions
            .resolved_calls
            .iter()
            .filter(|(span, _)| !mr_before.contains(span))
            .map(|(span, res)| (*span, res.clone()))
            .collect();
        let method_et: HashMap<Span, Type> = state.expr_types
            .iter()
            .filter(|(span, _)| !et_before.contains(span))
            .map(|(span, ty)| (*span, apply(&state.subst, ty)))
            .collect();

        // Annotate the clone with types and resolved calls from delta,
        // then apply final substitution to resolve Var(N) type variables
        let mut annotated = Defn {
            name: mangled_sym.clone(),
            docstring: method_clone.docstring.clone(),
            variants: vec![DefnVariant {
                params: method_clone.params().to_vec(),
                body: method_clone.body().clone(),
                span: method_clone.span,
            }],
            visibility: Visibility::Public,
            span: method_clone.span,
        };
        crate::program::annotate_defn_from_maps(
            &mut annotated,
            &method_et,
            &method_mr,
        );
        crate::program::apply_subst_to_defn(&state.subst, &mut annotated);

        // Write the fully annotated defn to ModuleEntry::Def.ast.
        let fn_type = Type::Fn(param_types.to_vec(), Box::new(ret_ty.clone()));
        let concrete_scheme = crate::scheme::mono(fn_type);
        let ast_variant: Option<DefnVariant> = annotated.variants.first().cloned();
        // S84 Phase-3 (FIXME 0392): a trait-impl method (mangled `Trait.method$Type`)
        // is a codegen-bound `Concrete` entry — build its concrete-boundary
        // `MonoExpr` view from the same annotated, subst-resolved body the `ast`
        // carries (best-effort per `build_concrete_codegen_view`; a `Self`-typed
        // impl-method body checked against a contrived synthetic-span fixture can
        // legitimately leave a residual var the `ast`-path codegen never reads).
        let codegen_view: Option<MonoDefnVariant> = ast_variant
            .as_ref()
            .and_then(|v| crate::program::build_concrete_codegen_view(&mangled_sym, v));
        let mut st = self.current_symbol_table_mut(state);
        if let Some(ModuleEntry::Def { ast, codegen_view: cv, .. }) =
            st.symbols.get_mut(&mangled_sym)
        {
            *ast = ast_variant;
            *cv = codegen_view;
        } else {
            // Concrete trait-impl method body (mangled name), born with its slot
            // (S83 deferred allocation): slot rides inside `Concrete` fn_state.
            let got_slot = st.allocate_got_slot();
            let mut builder = ModuleEntry::def(
                concrete_scheme,
                DefKind::UserFn { fn_state: UserFnState::Concrete { got_slot } },
            )
            .param_names(method_defn.params().iter().map(|(n, _)| n.clone()).collect());
            if let Some(doc) = method_defn.docstring.clone() {
                builder = builder.docstring(doc);
            }
            if let Some(ast) = ast_variant {
                builder = builder.ast(ast);
            }
            if let Some(view) = codegen_view {
                builder = builder.codegen_view(view);
            }
            st.insert(mangled_sym.clone(), builder.build());
        }

        Ok(annotated)
    }

    /// Type-check an HKT impl method.
    ///
    /// For `(impl Functor Option (defn fmap [func opt] ...))`:
    /// - The constructor variable `f` maps to the impl target `Option`
    /// - `(f a)` in the signature resolves to `(Option a)` via ADT application
    ///
    /// Same clone-annotate-write pattern as `check_impl_method`.
    fn check_hkt_impl_method(
        &self,
        state: &mut CheckState,
        decl: &TraitDeclInfo,
        impl_: &TraitImpl,
        method_defn: &Defn,
        method_sig: &TraitMethodSig,
    ) -> Result<Defn, CranelispError> {
        let mut local_next_id = self.next_id_snapshot();
        // Build con_var_map: constructor variable name -> resolve to ADT name
        // For HKT impls, we substitute constructor vars with the target ADT.
        // Use resolve_type_expr_hkt_impl which produces concrete ADT types.
        let mut type_var_map: HashMap<Symbol, TypeId> = HashMap::new();

        // Determine the arity of the constructor from the trait signature
        let arity = decl.type_params.iter().find_map(|p| {
            con_var_arity(decl, p)
        }).expect("invariant: HKT trait must use constructor param in Applied position");

        // Build the concrete self type: ADT(target, [fresh_vars...])
        let type_arg_vars: Vec<Type> = (0..arity)
            .map(|_| {
                let (ty, _) = crate::unify::fresh_var_id(&mut local_next_id);
                ty
            })
            .collect();
        // Phase B Part 1.4(3): HKT impls may target ADT-shaped types only
        // (intrinsics have no type parameters and don't carry HKT shape).
        // Still use the centralised resolver to get a typed error if the
        // target is unknown.
        let target_fqtn = self
            .resolve_type(state, impl_target_name_or_panic(&impl_.target), impl_.span)
            .map_err(cranelisp_types::CranelispError::from)?;
        let concrete_self = Type::ADT(target_fqtn.clone(), type_arg_vars);

        // Build param types using HKT-aware resolution that substitutes
        // constructor variable applications with concrete ADT applications
        let param_types: Vec<Type> = method_sig
            .params
            .iter()
            .map(|(_, p)| resolve_type_expr_hkt_impl(
                p,
                &decl.type_params,
                &target_fqtn,
                &mut type_var_map,
                &mut local_next_id,
                impl_.span,
            ))
            .collect::<Result<Vec<_>, _>>()?;

        let ret_ty = resolve_type_expr_hkt_impl(
            &method_sig.ret_type,
            &decl.type_params,
            &target_fqtn,
            &mut type_var_map,
            &mut local_next_id,
            impl_.span,
        )?;

        // Pre-unify the dispatch parameter with the concrete self type
        if let Some(param_idx) = method_sig.hkt_param_index
            && let Some(param_ty) = param_types.get(param_idx)
        {
            self.unify(state, param_ty, &concrete_self, method_defn.span)?;
        }

        self.commit_next_id(local_next_id);

        // Snapshot side maps for per-defn delta extraction
        let mr_before: HashSet<Span> = state.method_resolutions.resolved_calls.keys().copied().collect();
        let et_before: HashSet<Span> = state.expr_types.keys().copied().collect();

        // Clone the method defn and check the body with the mutable copy
        let mut method_clone = method_defn.clone();
        self.check_defn_body_with_types(state, &mut method_clone, &param_types, &ret_ty)?;

        // Per-defn post-passes (auto-curry only; overloads deferred to finalize)
        self.resolve_auto_curry(state);

        // Build the mangled name and create annotated defn for symbol table
        let mangled = format!(
            "{}.{}${}",
            impl_.trait_name, method_defn.name, impl_target_name_or_panic(&impl_.target)
        );
        let mangled_sym = Symbol::from(mangled.as_str());

        self.finalize_impl_method_writeback(
            state,
            method_defn,
            &method_clone,
            mangled_sym,
            &param_types,
            &ret_ty,
            &mr_before,
            &et_before,
        )
    }

    /// Check a function body with explicit parameter types.
    /// Shared helper for impl method checking and monomorphisation re-check.
    ///
    /// Takes `&mut Defn` so callers can annotate the AST after inference
    /// (via `annotate_defn_from_maps` + `apply_subst_to_defn`).
    pub(crate) fn check_defn_body_with_types(
        &self,
        state: &mut CheckState,
        defn: &mut Defn,
        param_types: &[Type],
        ret_ty: &Type,
    ) -> Result<(), CranelispError> {
        self.push_scope(state);

        for ((param_name, _), param_ty) in
            defn.params().iter().zip(param_types.iter())
        {
            self.bind_local(
                state,
                param_name.clone(),
                scheme::mono(param_ty.clone()),
            );
        }

        let body_ty = self.infer_expr(state, defn.body())?;
        self.unify(state, &body_ty, ret_ty, defn.span)?;

        // Post-inference deferred trait resolution
        self.resolve_deferred_trait_calls(state, defn.body());

        self.pop_scope(state);
        Ok(())
    }

    /// Generate default method implementations for methods not provided in the impl.
    pub(crate) fn generate_default_methods(
        &self,
        _state: &CheckState,
        decl: &TraitDeclInfo,
        impl_: &TraitImpl,
    ) -> Result<Vec<Defn>, CranelispError> {
        let provided: std::collections::HashSet<&str> = impl_
            .methods
            .iter()
            .map(|m| m.name.as_ref())
            .collect();

        let mut defaults = Vec::new();

        for method_sig in &decl.methods {
            if provided.contains(method_sig.name.as_ref())
                || method_sig.default_body.is_none()
            {
                continue;
            }

            // Create a mangled name for this default method
            let mangled = format!(
                "{}.{}${}",
                decl.name, method_sig.name, impl_target_name_or_panic(&impl_.target)
            );

            let span = impl_.span;
            let body = if let Some(ref expr_body) = method_sig.default_body {
                // User-defined default body: pre-parsed AST (S69 Submission 26).
                expr_body.clone()
            } else {
                // Hard-coded builtin defaults (Eq.!=, Ord.>, etc.)
                build_default_body(
                    decl.name.as_ref(),
                    method_sig.name.as_ref(),
                    &method_sig.params.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>(),
                    span,
                )?
            };

            defaults.push(Defn {
                name: Symbol::from(mangled.as_str()),
                docstring: None,
                variants: vec![DefnVariant {
                    params: method_sig.params.iter().map(|(n, _)| (n.clone(), None)).collect::<Vec<_>>(),
                    body,
                    span,
                }],
                visibility: Visibility::Public,
                span,
            });
        }

        Ok(defaults)
    }
}
