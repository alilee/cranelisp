//! Trait registration, impl checking, method resolution, and monomorphisation.
//!
//! Ring 2A: traits provide constrained polymorphism. Operators like `+` are
//! resolved as trait methods (`Num.+$Int`), not builtin primitives.
//!
//! Trait declarations are stored as `ModuleEntry::TraitDecl` entries on per-module
//! SymbolTables. Trait implementations are stored as `ModuleEntry::TraitImpl` entries.
//! Method-to-trait reverse lookup uses the `trait_origin` field on `ModuleEntry::Def`.
//! The old `TraitRegistry` and `ImplRegistry` global caches have been eliminated.

use std::collections::{HashMap, HashSet};

use cranelisp_types::{ErrorLocation,
    ConstrainedFn, CranelispError, DefKind, Defn, DefnVariant, Expr, FQTraitName, FQTypeName,
    JitSymbol, MethodResolutions, ModuleEntry, ModuleFullPath, MonoDefn, MonoDefnVariant, MonoExpr,
    NotConcrete, ResolvedCall, Scheme,
    Span, Symbol, TraitDecl, TraitDeclInfo, TraitImpl, TraitMethodSig, TraitName, Type, TypeId,
    TypeName, UserFnState, Visibility, apply,
};

use crate::checker::{CheckState, TypeCheckEnv};
use crate::scheme;

/// Extract the head `TypeName` from an impl's `target: TypeExpr`. Used for
/// diagnostics + lookup at sites that previously consumed the retired
/// `TraitImpl.target_type: TypeName` field. Returns `None` for `SelfType`,
/// `FnType`, and bare `TypeVar` targets — these have no single head name.
/// Per spec §5.4 EBNF, an impl `target` always resolves to `Named` or
/// `Applied`, so callers may `.expect()` in production paths.
fn impl_target_name(target: &cranelisp_types::TypeExpr) -> Option<&TypeName> {
    target.head_ref().map(|r| &r.name)
}

/// Extract the head TypeName, panicking if absent — for sites where spec
/// §5.4 guarantees a head name on the impl target.
fn impl_target_name_or_panic(target: &cranelisp_types::TypeExpr) -> &TypeName {
    impl_target_name(target).expect("spec §5.4: impl target lowers to Named or Applied")
}

// ---------------------------------------------------------------------------
// Active Constraints (tracked during body checking)
// ---------------------------------------------------------------------------

/// Tracks trait constraints on type variables during inference.
/// Populated when a constrained scheme is instantiated, consulted during generalize.
#[derive(Debug, Clone, Default)]
pub struct ActiveConstraints {
    /// TypeId -> list of required fully-qualified trait names
    pub(crate) constraints: HashMap<TypeId, Vec<FQTraitName>>,
}

impl ActiveConstraints {
    /// Add a constraint on a type variable (idempotent — duplicates are ignored).
    pub fn add(&mut self, var_id: TypeId, trait_name: FQTraitName) {
        let traits = self.constraints.entry(var_id).or_default();
        if !traits.contains(&trait_name) {
            traits.push(trait_name);
        }
    }

    /// Get constraints for a type variable.
    #[allow(dead_code)]
    pub fn get(&self, var_id: TypeId) -> Option<&Vec<FQTraitName>> {
        self.constraints.get(&var_id)
    }

    /// Clear all active constraints (between top-level forms).
    #[allow(dead_code)]
    pub fn clear(&mut self) {
        self.constraints.clear();
    }

    /// Iterate over all (var_id, traits) pairs.
    pub fn all(&self) -> impl Iterator<Item = (&TypeId, &Vec<FQTraitName>)> {
        self.constraints.iter()
    }

    /// Collect constraints for a set of type variable IDs.
    /// Returns a constraints map suitable for Scheme.constraints.
    /// Note: does NOT follow the substitution — use `TypeChecker::generalize`
    /// for correct constraint propagation through unified vars.
    #[allow(dead_code)]
    pub fn collect_for_vars(
        &self,
        vars: &[TypeId],
    ) -> HashMap<TypeId, Vec<FQTraitName>> {
        let mut result = HashMap::new();
        for &var_id in vars {
            if let Some(traits) = self.constraints.get(&var_id)
                && !traits.is_empty()
            {
                result.insert(var_id, traits.clone());
            }
        }
        result
    }
}

// ---------------------------------------------------------------------------
// Trait Registration
// ---------------------------------------------------------------------------

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Register a trait declaration.
    ///
    /// - Stores the TraitDecl in the trait registry
    /// - Registers each method as a constrained polymorphic symbol
    /// - Registers the trait name in the symbol table as TraitDecl
    pub(crate) fn register_trait_decl(
        &self,
        state: &mut CheckState,
        decl: &TraitDecl,
    ) -> Result<(), CranelispError> {
        // Check for duplicate trait name by looking in SymbolTables
        if self.lookup_trait_decl_with_state(state, &decl.name).is_some() {
            return Err(CranelispError::TypeError {
                message: format!("trait {} already defined", decl.name),
                location: ErrorLocation::from_span(decl.span),
            });
        }

        // If trait has type_params used in Applied position, use HKT registration path
        if !decl.type_params.is_empty()
            && decl.methods.iter().any(|m| {
                m.params
                    .iter()
                    .any(|(_, p)| type_expr_uses_con_var(p, &decl.type_params))
                    || type_expr_uses_con_var(&m.ret_type, &decl.type_params)
            })
        {
            return self.register_hkt_trait(state, decl);
        }

        // Allocate a fresh type variable for the trait's type parameter
        let (_, type_var_id) = self.fresh_var_id();

        // Register each method with a constrained polymorphic scheme. The
        // method binding inherits the trait's visibility (a Private trait's
        // methods are Private Defs) so a private trait does not leak its
        // operators as bare names through the prelude outer-scope fallback
        // (`/review` I-1); within the trait's own subtree they stay reachable
        // (the `cranelisp_types::resolve` visibility check honours `in_subtree`).
        for method in &decl.methods {
            self.register_trait_method(state,
                &decl.name,
                method,
                type_var_id,
                &decl.type_params,
                decl.visibility,
                decl.span,
            )?;
        }

        // Register in symbol table as TraitDecl entry
        self.current_symbol_table_mut(state).insert(
            Symbol::from(decl.name.as_ref()),
            cranelisp_types::ModuleEntry::TraitDecl {
                info: cranelisp_types::TraitDeclInfo {
                    name: decl.name.clone(),
                    type_params: decl.type_params.clone(),
                    methods: decl.methods.clone(),
                },
                visibility: decl.visibility,
                docstring: decl.docstring.clone(),
            },
        );

        Ok(())
    }

    /// Register an HKT trait where type_params are type constructor variables.
    /// E.g., `(deftrait (Functor f) (fmap [(Fn [a] b) (f a)] (f b)))`
    fn register_hkt_trait(
        &self,
        state: &mut CheckState,
        decl: &TraitDecl,
    ) -> Result<(), CranelispError> {
        let mut local_next_id = self.next_id_snapshot();
        // Create fresh type var IDs for each constructor param
        let mut con_var_map: HashMap<Symbol, TypeId> = HashMap::new();
        for param_name in &decl.type_params {
            let (_, id) = self.fresh_var_id();
            con_var_map.insert(param_name.clone(), id);
        }

        // Build a modified decl with hkt_param_index set on each method
        let mut modified_decl = decl.clone();

        for (mi, method) in decl.methods.iter().enumerate() {
            // Determine which param index carries the type constructor
            // find_hkt_param_index now expects &[(Symbol, TypeExpr)] per spec
            // — pass `method.params` directly.
            let param_idx = find_hkt_param_index(&method.params, &decl.type_params);
            modified_decl.methods[mi].hkt_param_index = Some(param_idx);

            // Create fresh regular type vars for any type variables in the signature
            // that are NOT constructor params
            let mut type_var_map: HashMap<Symbol, TypeId> = HashMap::new();

            let param_tys: Vec<Type> = method
                .params
                .iter()
                .map(|(_, p)| resolve_type_expr_hkt(p, &con_var_map, &mut type_var_map, &mut local_next_id, decl.span))
                .collect::<Result<Vec<_>, _>>()?;
            let ret_ty =
                resolve_type_expr_hkt(&method.ret_type, &con_var_map, &mut type_var_map, &mut local_next_id, decl.span)?;

            // Collect all var IDs (constructor + regular)
            let mut all_vars: Vec<TypeId> = con_var_map.values().copied().collect();
            all_vars.extend(type_var_map.values());
            all_vars.sort();
            all_vars.dedup();

            // Add trait constraint to constructor vars
            let fq_trait_name = FQTraitName::new(state.current_module.clone(), decl.name.clone());
            let mut constraints: HashMap<TypeId, Vec<FQTraitName>> = HashMap::new();
            for &con_id in con_var_map.values() {
                constraints.insert(con_id, vec![fq_trait_name.clone()]);
            }

            let method_scheme = Scheme {
                type_vars: all_vars,
                constraints,
                ty: Type::Fn(param_tys, Box::new(ret_ty)),
            };

            // Register the method name as a symbol with trait_origin. The method
            // inherits the trait's visibility (I-1 — see `register_trait_decl`).
            let mut builder = cranelisp_types::ModuleEntry::def(
                method_scheme,
                cranelisp_types::DefKind::UserFn {
                    fn_state: cranelisp_types::UserFnState::NotDetermined,
                },
            )
            .visibility(decl.visibility)
            .param_names(method.params.iter().map(|(n, _)| n.clone()).collect())
            .trait_origin(fq_trait_name.clone());
            if let Some(doc) = method.docstring.clone() {
                builder = builder.docstring(doc);
            }
            self.current_symbol_table_mut(state).insert(method.name.clone(), builder.build());

            // trait_origin is already set on the ModuleEntry::Def above,
            // so no separate reverse lookup registration is needed.
        }

        // Register in symbol table as TraitDecl entry (with hkt_param_index)
        self.current_symbol_table_mut(state).insert(
            Symbol::from(decl.name.as_ref()),
            cranelisp_types::ModuleEntry::TraitDecl {
                info: cranelisp_types::TraitDeclInfo {
                    name: modified_decl.name.clone(),
                    type_params: modified_decl.type_params.clone(),
                    methods: modified_decl.methods.clone(),
                },
                visibility: decl.visibility,
                docstring: decl.docstring.clone(),
            },
        );

        self.commit_next_id(local_next_id);
        Ok(())
    }

    /// Register a single trait method with its constrained polymorphic scheme.
    #[allow(clippy::too_many_arguments)]
    fn register_trait_method(
        &self,
        state: &mut CheckState,
        trait_name: &TraitName,
        method: &TraitMethodSig,
        type_var_id: TypeId,
        trait_type_params: &[Symbol],
        visibility: Visibility,
        span: Span,
    ) -> Result<(), CranelispError> {
        let method_type =
            self.build_method_type(method, type_var_id, trait_type_params, span)?;

        // Build FQTraitName using the current module (where the trait is being defined)
        let fq_trait_name = FQTraitName::new(state.current_module.clone(), trait_name.clone());

        let mut constraints = HashMap::new();
        constraints.insert(type_var_id, vec![fq_trait_name.clone()]);

        let method_scheme = Scheme {
            type_vars: vec![type_var_id],
            constraints,
            ty: method_type,
        };

        // Register the method name as a symbol with trait_origin. The method
        // inherits the trait's visibility (I-1 — see `register_trait_decl`).
        let mut builder = cranelisp_types::ModuleEntry::def(
            method_scheme,
            cranelisp_types::DefKind::UserFn {
                fn_state: cranelisp_types::UserFnState::NotDetermined,
            },
        )
        .visibility(visibility)
        .param_names(method.params.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>())
        .trait_origin(fq_trait_name);
        if let Some(doc) = method.docstring.clone() {
            builder = builder.docstring(doc);
        }
        self.current_symbol_table_mut(state).insert(method.name.clone(), builder.build());

        // trait_origin is already set on the ModuleEntry::Def above,
        // so no separate reverse lookup registration is needed.

        Ok(())
    }

    /// Build the function type for a trait method.
    ///
    /// Resolves `Self` type expressions to the type variable.
    /// TypeVars matching the trait's type parameters map to self_type;
    /// other TypeVars get fresh type variables (I3 fix).
    fn build_method_type(
        &self,
        method: &TraitMethodSig,
        type_var_id: TypeId,
        trait_type_params: &[Symbol],
        span: Span,
    ) -> Result<Type, CranelispError> {
        let mut local_next_id = self.next_id_snapshot();
        let self_type = Type::Var(type_var_id);

        // Pre-seed var_map: trait type params map to self_type.
        let mut var_map: HashMap<Symbol, Type> = HashMap::new();
        for param in trait_type_params {
            var_map.insert(param.clone(), self_type.clone());
        }

        let param_types: Vec<Type> = method
            .params
            .iter()
            .map(|(_, p)| resolve_trait_type_expr(p, &self_type, span, &mut var_map, &mut local_next_id))
            .collect::<Result<Vec<_>, _>>()?;

        let ret_type =
            resolve_trait_type_expr(&method.ret_type, &self_type, span, &mut var_map, &mut local_next_id)?;

        self.commit_next_id(local_next_id);
        Ok(Type::Fn(param_types, Box::new(ret_type)))
    }
}

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
        self.check_impl_method_with_sig(state, decl, impl_, method_defn, method_sig, false)
    }

    /// Type-check an impl method (or default method) given an explicit trait method sig.
    ///
    /// `is_default_mangled` = true indicates the `method_defn.name` is already mangled
    /// (`Trait.method$Type`) as generated by `generate_default_methods`. In that case
    /// the existing name is used as the symbol-table key; otherwise the mangled name is
    /// built from `impl_.trait_name + method_defn.name + impl_target_name_or_panic(&impl_.target)`.
    fn check_impl_method_with_sig(
        &self,
        state: &mut CheckState,
        decl: &TraitDeclInfo,
        impl_: &TraitImpl,
        method_defn: &Defn,
        method_sig: &TraitMethodSig,
        is_default_mangled: bool,
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

        // Clone the method defn and check the body with the mutable copy
        let mut method_clone = method_defn.clone();
        self.check_defn_body_with_types(state, &mut method_clone, &param_types, &ret_ty)?;

        // Per-defn post-passes (auto-curry only; overloads deferred to finalize)
        self.resolve_auto_curry(state);

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


// ---------------------------------------------------------------------------
// Method Resolution
// ---------------------------------------------------------------------------

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Try to resolve a call as a trait method.
    ///
    /// Returns Some(ResolvedCall::TraitMethod) if the callee is a trait method
    /// and the argument types resolve to a concrete impl.
    /// Returns None if the callee is not a trait method.
    pub(crate) fn try_resolve_trait_method(
        &self,
        state: &mut CheckState,
        callee_name: &Symbol,
        arg_types: &[Type],
        span: Span,
    ) -> Result<Option<ResolvedCall>, CranelispError> {
        // Check if this name is a trait method (via trait_origin on ModuleEntry::Def).
        // State-rooted: chain-follow from the current module's view per Principle 17.
        let trait_name = match self.method_to_trait_with_state(state, callee_name) {
            Some(tn) => tn,
            None => return Ok(None),
        };

        // Use hkt_param_index for dispatch argument selection (defaults to 0)
        let param_idx = self.hkt_param_idx_for_method(state, callee_name);
        let dispatch_arg = match arg_types.get(param_idx) {
            Some(a) => a,
            None => return Ok(None),
        };
        let resolved_arg = self.apply_subst(state, dispatch_arg);

        let impl_type_name = match concrete_type_name(&resolved_arg) {
            Some(tn) => tn,
            // Type is still a variable — defer resolution (batch mode will
            // catch this during monomorphisation).
            None => return Ok(None),
        };

        // Check if an impl exists — if the name IS a trait method and the
        // type IS concrete but the impl DOESN'T exist, that's a type error.
        // State-rooted: chain-follow the trait reference from the current
        // module's view to the trait's defining module per Decision 45.
        if !self.has_impl_with_state(state, &trait_name, &impl_type_name) {
            return Err(CranelispError::TypeError {
                message: format!(
                    "no impl of trait {} for type {}",
                    trait_name, impl_type_name
                ),
                location: ErrorLocation::from_span(span),
            });
        }

        // Primitive trait-method short-circuit (FIXME 0185).
        //
        // When the resolved (trait, method, impl_type) names a primitive
        // operator on a primitive type (e.g., (Num, +, Int) → "add-i64"),
        // emit `ResolvedCall::BuiltinFn` directly so backend inlines via
        // `try_emit_inline_primitive` instead of routing through the
        // trait-impl body wrapper. This preserves the pre-D43 inline
        // optimisation while keeping backend trait-free (the dispatch is
        // monomorphisation-keyed in typecheck, not trait-keyed in backend).
        if let Some(prim_name) = primitive_for_trait_method(&trait_name, callee_name, &impl_type_name) {
            return Ok(Some(ResolvedCall::BuiltinFn {
                name: Symbol::from(prim_name),
            }));
        }

        let mangled = format!(
            "{}.{}${}",
            trait_name, callee_name, impl_type_name
        );

        // Build FQTraitName — chain-follow the trait reference to its
        // defining module per Decision 45 Pattern B. `has_impl_with_state`
        // succeeded just above, so the chain-follow is guaranteed.
        let trait_defining_module = self
            .resolve_trait(state, trait_name.as_ref(), span)
            .map_err(cranelisp_types::CranelispError::from)?;
        let fq_trait_name = FQTraitName::new(trait_defining_module, trait_name);

        // Build FQTypeName for the impl type — works for both ADT and
        // intrinsic targets (Phase B Part 5).
        let fq_impl_type = self
            .resolve_type(state, &impl_type_name, span)
            .map_err(cranelisp_types::CranelispError::from)?;

        Ok(Some(ResolvedCall::TraitMethod {
            trait_name: fq_trait_name,
            method_name: callee_name.clone(),
            impl_type: fq_impl_type,
            mangled_name: JitSymbol::from(mangled.as_str()),
        }))
    }
}

// ---------------------------------------------------------------------------
// Primitive trait-method dispatch table (FIXME 0185)
// ---------------------------------------------------------------------------

/// Map `(trait, method, impl_type) → primitive jit name` for the small set
/// of Ring-0 operator impls that the typecheck-side optimisation collapses
/// from `ResolvedCall::TraitMethod` to `ResolvedCall::BuiltinFn`.
///
/// Per FIXME 0185 (filed by /dev (backend) Sprint 67 Wave 3), this restores
/// the inline-substitution optimisation that the backend's
/// `primitive_for_trait_method` deletion removed (Decision 43 close — backend
/// has no trait knowledge). The dispatch lives here because the resolution
/// is monomorphisation-keyed (which `(impl_type, method)` resolves to which
/// primitive name) and that information is available at typecheck time.
///
/// **Monomorphisation-keyed**, not **trait-keyed** — Decision 43 compatible.
/// Backend continues to handle `ResolvedCall::BuiltinFn { name }` via
/// `try_emit_inline_primitive(name)` without any trait knowledge.
///
/// The mapping mirrors the pre-D43 `primitive_for_trait_method` table in
/// `crates/cranelisp-backend/src/primitives_inline.rs` (deleted in Wave 3 row 6).
fn primitive_for_trait_method(
    trait_name: &TraitName,
    method_name: &Symbol,
    impl_type: &TypeName,
) -> Option<&'static str> {
    let t = trait_name.as_ref();
    let m = method_name.as_ref();
    let i = impl_type.as_ref();

    match (t, m, i) {
        // Num trait: arithmetic operators
        ("Num", "+", "Int") => Some("add-i64"),
        ("Num", "-", "Int") => Some("sub-i64"),
        ("Num", "*", "Int") => Some("mul-i64"),
        ("Num", "/", "Int") => Some("div-i64"),
        ("Num", "+", "Float") => Some("add-f64"),
        ("Num", "-", "Float") => Some("sub-f64"),
        ("Num", "*", "Float") => Some("mul-f64"),
        ("Num", "/", "Float") => Some("div-f64"),

        // Eq trait: equality operators
        ("Eq", "=", "Int") => Some("eq-i64"),
        ("Eq", "=", "Float") => Some("eq-f64"),
        ("Eq", "=", "Bool") => Some("eq-bool"),
        ("Eq", "=", "String") => Some("str-eq"),

        // Ord trait: comparison operators
        ("Ord", "<", "Int") => Some("lt-i64"),
        ("Ord", "<", "Float") => Some("lt-f64"),
        ("Ord", ">", "Int") => Some("gt-i64"),
        ("Ord", ">", "Float") => Some("gt-f64"),
        ("Ord", "<=", "Int") => Some("le-i64"),
        ("Ord", "<=", "Float") => Some("le-f64"),
        ("Ord", ">=", "Int") => Some("ge-i64"),
        ("Ord", ">=", "Float") => Some("ge-f64"),

        // Eq trait: inequality (default method)
        ("Eq", "!=", "Int") => Some("neq-i64"),
        ("Eq", "!=", "Float") => Some("neq-f64"),
        ("Eq", "!=", "Bool") => Some("neq-bool"),
        ("Eq", "!=", "String") => Some("neq-string"),

        // Display trait: show (string conversion)
        ("Display", "show", "Int") => Some("int-to-string"),
        ("Display", "show", "Float") => Some("float-to-string"),
        ("Display", "show", "Bool") => Some("bool-to-string"),
        ("Display", "show", "String") => Some("string-identity"),

        _ => None,
    }
}

#[cfg(test)]
mod primitive_dispatch_tests;

// Continuation impl for the original trait-method block — split by the
// primitive_for_trait_method dispatch table inserted above per FIXME 0185.
impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {

    /// Check if a callee name is a trait method (via trait_origin on ModuleEntry::Def).
    /// Default-rooted to `user` — for state-aware callers use
    /// [`Self::is_trait_method_with_state`].
    #[allow(dead_code)]
    pub(crate) fn is_trait_method(&self, name: &Symbol) -> bool {
        self.method_to_trait(name).is_some()
    }

    /// State-rooted variant of [`Self::is_trait_method`]. Chain-follows from
    /// `state.current_module` per Principle 17.
    pub(crate) fn is_trait_method_with_state(&self, state: &CheckState, name: &Symbol) -> bool {
        self.method_to_trait_with_state(state, name).is_some()
    }
}

// ---------------------------------------------------------------------------
// Constrained Instantiation
// ---------------------------------------------------------------------------

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Instantiate a constrained scheme, tracking the constraints on fresh vars.
    ///
    /// Returns the instantiated type. Side effect: adds constraints to
    /// `self.state.active_constraints`.
    pub(crate) fn instantiate_constrained(
        &self,
        state: &mut CheckState,
        scheme: &Scheme,
    ) -> Type {
        if scheme.type_vars.is_empty() {
            return scheme.ty.clone();
        }

        // Build mapping from old vars to fresh vars.
        //
        // Each fresh var must NOT collide with any of the scheme's own
        // quantified vars — re-roll on collision. A collision (e.g. a
        // cross-module scheme whose quantified TypeIds the per-session
        // `next_id` counter has not been advanced past) would otherwise build
        // an identity self-map and make `apply` recurse forever
        // (FIXME 0279/0295). See `instantiate_scheme`'s `fresh_instantiation_subst`.
        let bound: std::collections::HashSet<cranelisp_types::TypeId> =
            scheme.type_vars.iter().copied().collect();
        let mut inst_subst = cranelisp_types::Subst::new();
        let mut var_mapping = HashMap::new();
        for &var_id in &scheme.type_vars {
            let (fresh_ty, fresh_id) = loop {
                let (fresh_ty, fresh_id) = self.fresh_var_id();
                if !bound.contains(&fresh_id) {
                    break (fresh_ty, fresh_id);
                }
            };
            inst_subst.insert(var_id, fresh_ty);
            var_mapping.insert(var_id, fresh_id);
        }

        // Carry constraints to fresh vars
        for (old_var, traits) in &scheme.constraints {
            if let Some(&new_var) = var_mapping.get(old_var) {
                for t in traits {
                    state.active_constraints.add(new_var, t.clone());
                }
            }
        }

        apply(&inst_subst, &scheme.ty)
    }
}

// ---------------------------------------------------------------------------
// Monomorphisation
// ---------------------------------------------------------------------------

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Generate a monomorphised specialization of a constrained function.
    ///
    /// Called when a constrained function is applied with concrete argument types.
    #[allow(dead_code)]
    ///
    /// `home` is `Some(defining_module)` when `fn_name` is an IMPORTED
    /// constrained fn whose body must be re-checked in its DEFINING module's
    /// import context (FIXME 0355) — `show`/`str-concat`/trait-method references
    /// inside the body resolve there, not in the caller's scope. It is `None` for
    /// a locally-defined constrained fn (the as-built same-module path), in which
    /// case the lookup + re-check use `state.current_module` unchanged.
    pub(crate) fn monomorphise_call(
        &self,
        state: &mut CheckState,
        fn_name: &Symbol,
        arg_types: &[Type],
        call_span: Span,
        home: Option<&ModuleFullPath>,
    ) -> Result<Option<MonoDefn>, CranelispError> {
        // Look up the constrained fn (in its defining module when imported).
        let constrained_fn = match self.get_constrained_fn(state, fn_name, home) {
            Some(cf) => cf,
            None => return Ok(None),
        };

        let scheme = constrained_fn.scheme.clone();
        let defn = constrained_fn.variant.clone();

        // Instantiate, unify with arg types, and resolve concrete types. Keep
        // the original→fresh var-id mapping so constraint verification resolves
        // through the instantiated vars (FIXME 0355).
        let (resolved, var_mapping) =
            self.instantiate_and_resolve(state, &scheme, arg_types, call_span)?;

        let concrete_param_types = if let Type::Fn(pts, _) = &resolved {
            pts.clone()
        } else {
            return Ok(None);
        };

        let mangled_name = build_mangled_name(fn_name, &concrete_param_types);

        // Check constraints are satisfied. For an IMPORTED callee (FIXME 0355),
        // the trait + impl referenced by the constraint live in the DEFINING
        // module's scope, so switch `current_module` to `home` for the impl
        // lookup (mirrors `recheck_body_for_mono`'s module switch). Restored
        // unconditionally. Without this, `has_impl_with_state` roots the trait
        // resolution in the caller's scope and a home-local (non-prelude) impl
        // is invisible — a spurious "no impl of trait T for type Int".
        let saved_module = home.map(|h| {
            std::mem::replace(&mut state.current_module, h.clone())
        });
        let verify_result = self.verify_constraints(state, &scheme, &var_mapping, call_span);
        if let Some(prev) = saved_module {
            state.current_module = prev;
        }
        verify_result?;

        // Re-check the body with concrete types and harvest resolutions
        let concrete_ret_ty = if let Type::Fn(_, ret) = &resolved {
            *ret.clone()
        } else {
            return Ok(None);
        };

        // FIXME 0349 — propagate the concrete return type back to the CALL SITE.
        // `instantiate_and_resolve` instantiated a FRESH copy of the callee
        // scheme and unified only its parameters with the concrete arg types;
        // the freshly-instantiated return var (now resolved to `concrete_ret_ty`)
        // is otherwise disconnected from the caller's recorded result type. Under
        // forward-reference ordering a polymorphic callee (`reduce`) is generalized
        // before the helper that ties its accumulator-to-result var, so the
        // caller (`main`) bound its own result var to the callee's *loose*
        // generalized return var during body-check; that left `main`'s result
        // un-pinned (`(IO t)`), marking `main` itself spuriously polymorphic.
        // Unifying the call-site's recorded expr type with the concrete return
        // pins the caller's result (`t -> Int`), so the subsequent caller
        // re-generalization yields the correct monomorphic scheme — the caller
        // then calls the mono variant instead of the polymorphic template (0344).
        if let Some(call_result_ty) = state.expr_types.get(&call_span).cloned() {
            self.unify(state, &call_result_ty, &concrete_ret_ty, call_span)?;
        }

        // `defn: DefnVariant` (S70 ConstrainedFn narrowing). Wrap in a
        // temporary single-variant `Defn` for the recheck helpers which
        // still take `&mut Defn`.
        let mut wrap_defn = Defn {
            name: fn_name.clone(),
            docstring: None,
            variants: vec![defn.clone()],
            visibility: Visibility::Public,
            span: defn.span,
        };
        let (mut resolutions, mono_expr_types) =
            self.recheck_body_for_mono(state, &mut wrap_defn, &concrete_param_types, &concrete_ret_ty, home)?;

        // Add SigDispatch entries for inner constrained fn calls. For an
        // imported callee, inner constrained calls (e.g. self-recursion) are
        // named in the DEFINING module's scope, so scope this in `home` too
        // (FIXME 0355).
        self.resolve_inner_constrained_calls(
            state,
            &wrap_defn,
            &mono_expr_types,
            &mut resolutions,
            home,
        );

        // FIXME 0373 (Tier 1, /arch ruling (A)) — propagate the concrete
        // instantiation through the CHAIN OF HOPS. The repro `(h1 neg)` reaches
        // its invocation through two hops: `h1` calls `h2` calls `f`. The
        // top-level pass4 scan collected `(h1 neg)` and monomorphised `h1` here,
        // re-checking its body `(h2 f)` with `f: (Fn [Int] Int)` concrete — but
        // the inner `(h2 f)` call only became concrete DURING this recheck, so
        // pass4's outer scan (where `f` was still `h1`'s generic param var) never
        // saw it with concrete types. Without monomorphising `h2` HERE, `h2`'s
        // result stays `Type::Var` → the same RC-guard SIGSEGV one hop deeper.
        //
        // So after re-checking this hop's body we recursively monomorphise the
        // inner polymorphic-result hops it reached, using the concrete types now
        // pinned in `mono_expr_types`. `resolve_inner_constrained_calls` above
        // already records the SigDispatch for inner CONSTRAINED self-recursion;
        // this step additionally CREATES the mono entries for distinct inner
        // hops (constrained or pure-parametric) and records their dispatch. The
        // `seen`-style de-dup that guards the outer pass lives in
        // `register_mono_entry` (it preserves an existing entry's slot) and in
        // the `resolved_calls` contains-key guard inside the recursion, so a
        // diamond of hops converging on one specialisation is created once.
        self.monomorphise_inner_parametric_hops(
            state,
            &wrap_defn,
            &mono_expr_types,
            &mut resolutions,
            home,
        )?;

        // FIXME 0374 — monomorphic self-recursion. A polymorphic fn that recurses
        // on itself at its OWN generic vars (`(repeat-fn f (sub-i64 n 1) (f x))`)
        // is monomorphic recursion (rank-1 HM): the self-call instantiates the
        // SAME `(Def, type-args)` as this mono, so it dispatches to THIS mono
        // (`mangled_name`). With the structural slot gate the original
        // `fn_name` def is slot-less `Polymorphic`, so the self-call MUST be
        // redirected to the slotted mono instance or it lowers through a missing
        // slot ("undefined function"). `collect_apply_var_calls` deliberately
        // skips self-calls (they are not a DISTINCT instance to mint), so record
        // their dispatch here. Only the same-arg-type self-recursion is the same
        // mono; a self-call at different concrete types would have been a
        // distinct hop already minted above.
        {
            let mut self_calls = Vec::new();
            collect_self_apply_calls(wrap_defn.body(), fn_name, &mut self_calls);
            for (arg_spans, self_span) in &self_calls {
                if resolutions.resolved_calls.contains_key(self_span) {
                    continue;
                }
                let self_arg_types: Vec<Type> = arg_spans
                    .iter()
                    .filter_map(|span| mono_expr_types.get(span).cloned())
                    .collect();
                if self_arg_types.len() != arg_spans.len() {
                    continue;
                }
                // Same concrete param types ⇒ same mono instance (`mangled_name`).
                if build_mangled_name(fn_name, &self_arg_types) == mangled_name {
                    resolutions.resolved_calls.insert(
                        *self_span,
                        ResolvedCall::SigDispatch {
                            mangled_name: JitSymbol::from(mangled_name.as_str()),
                        },
                    );
                }
            }
        }

        // Build annotated mono defn: annotate from side maps, apply subst.
        // `defn: DefnVariant` (S70 ConstrainedFn narrowing) — name/docstring/
        // visibility no longer ride on the payload; recover them from
        // the parent Def's ModuleEntry which is keyed by `fn_name`. For an
        // imported callee the parent `Def` lives in `home`, not the caller's
        // current module, so probe there (FIXME 0355).
        let parent_metadata: Option<(Option<String>, Visibility)> = {
            let lookup_module = home.unwrap_or(&state.current_module);
            self.resolve_terminal_entry_and_home(lookup_module, fn_name.as_ref())
                .and_then(|(e, _)| match e {
                    ModuleEntry::Def { docstring, visibility, .. } => {
                        Some((docstring.clone(), visibility))
                    }
                    _ => None,
                })
        };
        let (docstring, visibility) = parent_metadata.unwrap_or((None, Visibility::Public));
        let mut mono_defn_ast = Defn {
            name: Symbol::from(mangled_name.as_str()),
            docstring,
            variants: vec![DefnVariant {
                params: defn.params.clone(),
                body: defn.body.clone(),
                span: defn.span,
            }],
            visibility,
            span: defn.span,
        };
        crate::program::annotate_defn_from_maps(
            &mut mono_defn_ast,
            &mono_expr_types,
            &resolutions.resolved_calls,
        );
        crate::program::apply_subst_to_defn(&state.subst, &mut mono_defn_ast);

        // S84 Phase 2b (concrete-boundary-type.md §2.4 "mono-population seam"):
        // build the concrete-boundary AST view (`MonoExpr`) of this instance at
        // the seam, IMMEDIATELY after `apply_subst_to_defn` resolved every node's
        // `inferred_type` through the substitution. `MonoExpr::from_expr` walks the
        // fully-annotated, subst-resolved body and converts each node's
        // `inferred_type` to a `ConcreteType` — failing at the first node whose
        // type is absent or a residual `Type::Var` / unresolved HKT head.
        //
        // The validation payoff: `from_expr` runs on EVERY monomorphised instance.
        // A correctly-monomorphised instance MUST succeed (every node concrete). A
        // failure means this mono instance retains a residual `Var` (a genuine
        // incompleteness) — surfaced HERE as the unified §3.11.1 ambiguity /
        // could-not-monomorphise error (reusing the same diagnostic wording the
        // position-complete scan in `find_ambiguous_top_level_form` produces, so no
        // regression in rejection coverage), NOT silently swallowed.
        //
        // TRANSITIONAL (produces-but-unused for codegen): the backend still reads
        // `Expr.inferred_type` off `MonoDefn.defn` in Phase 2; it does NOT yet
        // consume `MonoExpr` (Phase 3). The `MonoDefnVariant` is accumulated on
        // `state.mono_variants` (drained by `pass4_monomorphise` into the parallel
        // `Vec<MonoDefnVariant>`), dual-carried ALONGSIDE the `Defn` body so the
        // backend's read-path is intact. `from_expr` is non-destructive over the
        // source `Defn`.
        //
        // **Phase-4 part A — the carve-out is DELETED; every minted instance is
        // concrete.** Before Phase 4, the mono pass minted a SPURIOUS partial
        // instance (`reduce-loop$Vec+Int+Int`, the 0344 fold) whose body retained
        // scheme-quantified vars, and an `allowed_vars` carve-out admitted it with
        // no `MonoExpr`. Part A suppresses that mint at the collection gate
        // (`local_parametric_call_triggers` + `monomorphise_inner_parametric_hops`
        // now require ALL ARGS CONCRETE). With no partial instance minted, every
        // instance reaching this seam is fully concrete ⇒ `from_expr` succeeds on
        // EVERY one ⇒ the carve-out is dead code, deleted. The deletion IS the
        // completeness proof: an `Err` here now means a GENUINELY-free residual
        // (the real ambiguity case, §1.3 / §2.6) — for a valid program it must
        // not happen, and if it does the suite goes red at that instance
        // (Principle 20: completeness forced by representation, not chased by
        // hand).
        // S84 Phase-3 (FIXME 0392): the `MonoDefnVariant` built here is the
        // entry's `codegen_view` — set ON the mono instance's `ModuleEntry::Def`
        // at `register_mono_entry` (single source of truth, Principle 7). The
        // P2b transitional `CheckState.mono_variants` parallel `Vec` is retired:
        // the view lives on the entry, not a side `Vec`.
        let codegen_view = match MonoExpr::from_expr(mono_defn_ast.body()) {
            Ok(mono_body) => {
                // Genuinely concrete instance — carry the concrete-boundary view.
                MonoDefnVariant {
                    name: Symbol::from(mangled_name.as_str()),
                    params: mono_defn_ast.params().iter().map(|(n, _)| n.clone()).collect(),
                    body: mono_body,
                    span: defn.span,
                }
            }
            // A genuinely-free residual (an unbound type variable, or an
            // un-annotated node — `Var(0)` sentinel — reaching a codegen
            // position) is the unified ambiguity / could-not-monomorphise error
            // (§1.3 / §2.6), reusing the §3.11.1 diagnostic wording (no
            // rejection-coverage regression). Post-part-A this arm fires ONLY for
            // genuinely-ambiguous code, never for a valid program.
            Err(nc) => {
                let detail = match nc {
                    NotConcrete::Var(_) => "a residual unbound type variable",
                    NotConcrete::HktHead(_) => "an unresolved higher-kinded type head",
                };
                return Err(CranelispError::TypeError {
                    message: format!(
                        "ambiguous type; add an annotation to pin the type of \
                         the polymorphic value monomorphised in `{}` ({detail} \
                         reached a codegen position)",
                        mangled_name
                    ),
                    location: ErrorLocation::from_span(defn.span),
                });
            }
        };

        // FIXME 0033 (S81 W-G): `MonoDefn` no longer carries per-mono side
        // maps. The `mono_defn_ast` was just annotated by
        // `annotate_defn_from_maps` + `apply_subst_to_defn` above — every typed
        // expression carries its `inferred_type` and every `Expr::Apply` /
        // `Expr::Var` carries `resolved_call` directly on the AST, which is the
        // single source of truth for the resolved-stage data. `resolutions` +
        // `mono_expr_types` are still produced here (they drive inner-call
        // resolution + the call-site dispatch recorded by callers) but no
        // longer propagated onto `MonoDefn` — annotations live on the AST.
        let _ = (&resolutions, &mono_expr_types); // produced for inner-call resolution; not propagated onto MonoDefn
        let mono_defn = MonoDefn {
            defn: mono_defn_ast,
        };

        // Wave 0 (§9.4): register the mono specialisation as a symbol-table
        // entry with `ast: Some(annotated)`. The body has been fully annotated
        // by `annotate_defn_from_maps` + `apply_subst_to_defn` above — no further
        // enrichment needed. Backend codegen reads the body via
        // `ModuleEntry::Def.ast`. This is additive to `CheckResult.mono_defns`;
        // /int removes the `finalize_module` inlining loop in Wave 2.
        self.register_mono_entry(
            state,
            &mono_defn,
            &concrete_param_types,
            &concrete_ret_ty,
            codegen_view,
        );

        Ok(Some(mono_defn))
    }

    /// Register a mono specialisation on the current module's symbol table
    /// as a `ModuleEntry::Def` with `ast: Some(annotated)`. Wave 0 §9.4.
    fn register_mono_entry(
        &self,
        state: &mut CheckState,
        mono: &MonoDefn,
        concrete_param_types: &[Type],
        concrete_ret_ty: &Type,
        codegen_view: MonoDefnVariant,
    ) {
        let fn_ty = Type::Fn(
            concrete_param_types.to_vec(),
            Box::new(concrete_ret_ty.clone()),
        );
        let scheme = crate::scheme::mono(fn_ty);

        let mut st = self.current_symbol_table_mut(state);
        // De-duplication note: `pass4_monomorphise` / `monomorphise_expr_calls`
        // short-circuit via `seen` before calling `monomorphise_call` a second
        // time for the same mangled name, so this insertion runs exactly once
        // per specialisation. If an entry already exists (e.g., REPL redefinition),
        // we preserve its `got_slot` to keep call-site GOT indices stable.
        // A mono specialisation is a concrete callable born with its slot
        // (S83 deferred allocation, Principle 20). On REPL redefinition reuse
        // the prior concrete entry's slot (read via `callable_got_slot`) to
        // keep call-site GOT indices stable; the slot rides inside the
        // `Concrete` fn_state, not a flat `Def` field.
        let existing_got_slot = st.get(mono.defn.name.as_ref())
            .and_then(|e| e.callable_got_slot());
        let got_slot = existing_got_slot.unwrap_or_else(|| st.allocate_got_slot());

        let mut builder = ModuleEntry::def(
            scheme,
            DefKind::UserFn { fn_state: UserFnState::Concrete { got_slot } },
        )
        .visibility(mono.defn.visibility)
        .param_names(mono.defn.params().iter().map(|(n, _)| n.clone()).collect());
        if let Some(doc) = mono.defn.docstring.clone() {
            builder = builder.docstring(doc);
        }
        // S69 Submission 35: ast holds the single meaningful DefnVariant
        // (not the parent Defn wrapper).
        if let Some(ast) = mono.defn.variants.first().cloned() {
            builder = builder.ast(ast);
        }
        // S84 Phase-3 (FIXME 0392): a mono instance is a codegen-bound
        // `Concrete` entry — carry its concrete-boundary `MonoExpr` view, built
        // + validated at the `monomorphise_call` seam. Produces-but-unread until
        // the backend read-flip (FIXME 0391); the backend still reads `ast`.
        builder = builder.codegen_view(codegen_view);
        st.insert(mono.defn.name.clone(), builder.build());
    }

    /// Instantiate a scheme with fresh type variables, unify with the given
    /// argument types, and return the fully-resolved function type.
    fn instantiate_and_resolve(
        &self,
        state: &mut CheckState,
        scheme: &Scheme,
        arg_types: &[Type],
        call_span: Span,
    ) -> Result<(Type, HashMap<cranelisp_types::TypeId, cranelisp_types::TypeId>), CranelispError>
    {
        // Instantiate the scheme with fresh vars, KEEPING the original→fresh
        // var-id mapping. The mapping is needed by `verify_constraints`:
        // `scheme.constraints` are keyed by the scheme's ORIGINAL var_ids, but
        // only the FRESH vars are unified into `state.subst` here. Cross-module
        // (FIXME 0355) the scheme comes from another module's check, so its
        // original var_ids are stale in the caller's `state.subst` — and may
        // COLLIDE with a caller var (observed: `cmp`'s constraint var_id
        // resolving to the caller's `IO` from `main`'s `Pure`, producing a
        // spurious "no impl of Eq/Display for IO"). Resolving constraints
        // through the instantiation map fixes this. Re-rolls fresh ids on
        // collision with the scheme's own bound vars (FIXME 0279/0295), like
        // the sibling instantiator above.
        let bound: std::collections::HashSet<cranelisp_types::TypeId> =
            scheme.type_vars.iter().copied().collect();
        let mut inst_subst = cranelisp_types::Subst::new();
        let mut var_mapping: HashMap<cranelisp_types::TypeId, cranelisp_types::TypeId> =
            HashMap::new();
        for &var_id in &scheme.type_vars {
            let (fresh_ty, fresh_id) = loop {
                let (fresh_ty, fresh_id) = self.fresh_var_id();
                if !bound.contains(&fresh_id) {
                    break (fresh_ty, fresh_id);
                }
            };
            inst_subst.insert(var_id, fresh_ty);
            var_mapping.insert(var_id, fresh_id);
        }
        let inst_type = apply(&inst_subst, &scheme.ty);

        if let Type::Fn(param_types, _) = &inst_type {
            for (pt, at) in param_types.iter().zip(arg_types.iter()) {
                self.unify(state, pt, at, call_span)?;
            }
        }

        Ok((self.apply_subst(state, &inst_type), var_mapping))
    }

    /// Verify that all trait constraints in the scheme are satisfied by
    /// the concrete types determined during unification.
    fn verify_constraints(
        &self,
        state: &CheckState,
        scheme: &Scheme,
        var_mapping: &HashMap<cranelisp_types::TypeId, cranelisp_types::TypeId>,
        call_span: Span,
    ) -> Result<(), CranelispError> {
        for (var_id, traits) in &scheme.constraints {
            // `scheme.constraints` are keyed by the scheme's ORIGINAL quantified
            // var_ids. Only the FRESH vars from instantiation were unified into
            // `state.subst`, so resolve each constraint var through the
            // instantiation map first (FIXME 0355 — cross-module the original
            // var_id is stale/colliding in the caller's subst). A var absent
            // from the map (defensive) falls back to its original id.
            let effective_id = var_mapping.get(var_id).copied().unwrap_or(*var_id);
            let resolved_var = apply(&state.subst, &Type::Var(effective_id));
            let impl_type = match concrete_type_name(&resolved_var) {
                Some(tn) => tn,
                None => continue,
            };
            for fq_trait in traits {
                if !self.has_impl_with_state(state, &fq_trait.name, &impl_type) {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "no impl of trait {} for type {}",
                            fq_trait, impl_type
                        ),
                        location: ErrorLocation::from_span(call_span),
                    });
                }
            }
        }
        Ok(())
    }

    /// Re-check a function body with concrete types, saving and restoring
    /// the typechecker's resolution/expr_types state around the check.
    ///
    /// Returns the per-specialization method resolutions and expression types.
    ///
    /// `home` is `Some(defining_module)` for an IMPORTED constrained fn
    /// (FIXME 0355): `state.current_module` is saved and switched to `home`
    /// around the body re-check, so the body's bare references
    /// (`show`/`str-concat`/trait methods) resolve in the DEFINING module's
    /// import context — re-checking them in the caller's scope mis-resolves them
    /// (`no impl of trait Display for type IO`). The home is a COMMITTED import
    /// → the live view suffices (no staging shadow). It is restored unconditionally
    /// alongside the resolution/expr-type/auto-curry side state. `None` leaves the
    /// current module unchanged (the as-built same-module path).
    pub(crate) fn recheck_body_for_mono(
        &self,
        state: &mut CheckState,
        defn: &mut Defn,
        concrete_param_types: &[Type],
        concrete_ret_ty: &Type,
        home: Option<&ModuleFullPath>,
    ) -> Result<(MethodResolutions, HashMap<Span, Type>), CranelispError> {
        let saved_resolutions = std::mem::take(&mut state.method_resolutions);
        let saved_expr_types = std::mem::take(&mut state.expr_types);
        let saved_pending_auto_curry = std::mem::take(&mut state.pending_auto_curry);
        // Switch into the defining module for an imported callee so the body's
        // bare-name references resolve in its import context (FIXME 0355).
        let saved_current_module = home.map(|h| {
            std::mem::replace(&mut state.current_module, h.clone())
        });

        let result = self.check_defn_body_with_types(state, defn, concrete_param_types, concrete_ret_ty);

        // Drain pending auto-curry entries into method_resolutions before
        // capturing. During re-check, auto-curry sites push to
        // pending_auto_curry but aren't yet in method_resolutions.
        if result.is_ok() {
            self.resolve_auto_curry(state);
        }

        let resolutions = std::mem::take(&mut state.method_resolutions);
        let mono_expr_types: HashMap<Span, Type> = state.expr_types
            .iter()
            .map(|(span, ty)| (*span, apply(&state.subst, ty)))
            .collect();

        state.method_resolutions = saved_resolutions;
        state.expr_types = saved_expr_types;
        state.pending_auto_curry = saved_pending_auto_curry;
        // Restore the caller's module unconditionally (mirrors the side-state
        // save/restore discipline above).
        if let Some(prev) = saved_current_module {
            state.current_module = prev;
        }

        result?;
        Ok((resolutions, mono_expr_types))
    }

    /// Scan the monomorphised body for constrained fn calls (e.g. self-recursive
    /// calls) and add SigDispatch entries so the backend can find them.
    fn resolve_inner_constrained_calls(
        &self,
        state: &CheckState,
        defn: &Defn,
        mono_expr_types: &HashMap<Span, Type>,
        resolutions: &mut MethodResolutions,
        home: Option<&ModuleFullPath>,
    ) {
        // For an imported callee, inner constrained-fn names live in the
        // DEFINING module's scope (FIXME 0355). Read constrained fns from there
        // rather than the caller's current module.
        let constrained_fn_names: HashSet<Symbol> = match home {
            Some(h) => {
                let mut names = HashSet::new();
                self.for_each_in_module(h, |name, entry| {
                    if let ModuleEntry::Def { kind, .. } = entry
                        && let DefKind::UserFn { fn_state: UserFnState::Constrained(_) } = kind.as_ref()
                    {
                        names.insert(name.clone());
                    }
                });
                names
            }
            None => {
                let r = self.current_symbol_table(state);
                r.view()
                    .iter()
                    .filter_map(|(name, entry)| {
                        if let ModuleEntry::Def { kind, .. } = entry
                            && let DefKind::UserFn { fn_state: UserFnState::Constrained(_) } = kind.as_ref()
                        {
                            return Some(name.clone());
                        }
                        None
                    })
                    .collect()
            }
        };
        let mut inner_calls = Vec::new();
        Self::collect_constrained_calls(defn.body(), &constrained_fn_names, &mut inner_calls);
        for (inner_fn_name, arg_spans, inner_call_span) in &inner_calls {
            if resolutions.resolved_calls.contains_key(inner_call_span) {
                continue; // already resolved (e.g. as a trait method)
            }
            let inner_arg_types: Vec<Type> = arg_spans
                .iter()
                .filter_map(|span| mono_expr_types.get(span).cloned())
                .collect();
            if inner_arg_types.len() != arg_spans.len() {
                continue;
            }
            let inner_mangled = build_mangled_name(inner_fn_name, &inner_arg_types);
            resolutions.resolved_calls.insert(
                *inner_call_span,
                ResolvedCall::SigDispatch {
                    mangled_name: JitSymbol::from(inner_mangled.as_str()),
                },
            );
        }
    }

    /// Recursively monomorphise the polymorphic-result hops a just-rechecked
    /// mono body reached (FIXME 0373, Tier 1 — multi-hop concrete-type
    /// propagation; /arch ruling (A)).
    ///
    /// `resolve_inner_constrained_calls` (called just before this) records the
    /// SigDispatch for inner CONSTRAINED self-recursion, but does not CREATE a
    /// mono entry for a *distinct* inner hop. A chain `h1 → h2 → f` needs `h2`
    /// monomorphised at the concrete `(Fn [Int] Int)` instantiation that only
    /// became visible during `h1`'s recheck — otherwise `h2`'s result stays
    /// `Type::Var` and the RC-guard SIGSEGV fires one hop deeper.
    ///
    /// For each inner `Apply`-of-bare-`Var` call whose callee chain-resolves to a
    /// monomorphisable polymorphic `Def` (constrained OR pure-parametric), with
    /// all argument types now concrete in `mono_expr_types`, this recursively
    /// invokes [`Self::monomorphise_call`] (which itself recurses into deeper
    /// hops and registers the inner mono entry + slot via `register_mono_entry`),
    /// then records the inner call site's SigDispatch. The recheck module is the
    /// callee's HOME: an inner hop reached from an imported hop lives in `home`;
    /// a local hop lives in `current_module`. A callee that resolves to a
    /// different module than the recheck scope is handed `Some(its_home)` so its
    /// own body re-checks in the right import context (the 0355 module switch).
    fn monomorphise_inner_parametric_hops(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        mono_expr_types: &HashMap<Span, Type>,
        resolutions: &mut MethodResolutions,
        home: Option<&ModuleFullPath>,
    ) -> Result<(), CranelispError> {
        // The scope the body was re-checked in: `home` for an imported hop, else
        // the caller's current module.
        let recheck_module = home.cloned().unwrap_or_else(|| state.current_module.clone());

        // Collect inner Apply-of-bare-Var call sites first (immutable walk), then
        // monomorphise (mutable) — avoids borrowing `self`/`state` across the walk.
        let mut inner_sites: Vec<(Symbol, Vec<Span>, Span)> = Vec::new();
        collect_apply_var_calls(defn.body(), &defn.name, &mut inner_sites);

        for (inner_name, arg_spans, inner_span) in &inner_sites {
            if resolutions.resolved_calls.contains_key(inner_span) {
                continue; // already resolved (trait method / inner constrained self-rec)
            }
            // Resolve the inner callee's terminal entry + its home, rooted in the
            // module the body was re-checked in.
            let resolved = self.resolve_terminal_entry_and_home(&recheck_module, inner_name.as_ref());
            let (entry, callee_home) = match resolved {
                Some(r) => r,
                None => continue,
            };
            if !Self::entry_is_monomorphisable_polymorphic(&entry) {
                continue;
            }
            // All arg types must be concrete (pinned during the parent recheck).
            let inner_arg_types: Vec<Type> = arg_spans
                .iter()
                .filter_map(|span| mono_expr_types.get(span).cloned())
                .collect();
            if inner_arg_types.len() != arg_spans.len() {
                continue;
            }
            // ALL-ARGS-CONCRETE GUARD (Phase-4 part A, concrete-boundary-type.md
            // §4-A). A hop reached from a GENERIC caller's body is collected with
            // the parent's OWN free scheme vars in its arg positions (the
            // `reduce → reduce-loop` 0344 fold: `f`/`acc`/element are still
            // `reduce`'s `Var34`/`Var31`). Minting on that is a SPURIOUS partial
            // instance — a re-spelling of the generic template under a lossy
            // name, not a concrete specialisation. The GENUINE concrete instance
            // is minted by the parent's CONCRETE re-check chain (e.g.
            // `reduce$Int+Vec → reduce-loop$Int+Vec+Int+Int`), which arrives here
            // with every arg pinned. Skip the hop unless every arg is concrete
            // after substitution — suppressing the spurious mint so the
            // `allowed_vars` carve-out at the mono-population seam is dead and
            // `from_expr` succeeds on every minted instance (the completeness
            // proof).
            if !inner_arg_types
                .iter()
                .all(|t| apply(&state.subst, t).is_concrete())
            {
                continue;
            }
            // FIXME 0373 (Tier 1.5 — CROSS-MODULE hops). `monomorphise_call`
            // roots its callee lookup + body re-check at `home`, falling back to
            // `state.current_module` when `home` is `None`. Crucially,
            // `recheck_body_for_mono` has ALREADY RESTORED `state.current_module`
            // to the caller's module by the time this runs — so the gate must be
            // "is the inner callee in a different module than `state.current_module`
            // NOW", not "than `recheck_module`". For a CROSS-MODULE parent hop
            // (`h1` imported from `hop`, re-checked with `recheck_module = hop` but
            // `state.current_module = user`), the inner hop `h2` lives in `hop`,
            // which differs from the current `user`; passing `None` here would make
            // `get_constrained_fn` look `h2` up in `user` (where it does not exist)
            // → `None` → `h2` never re-monomorphised at the concrete
            // `(Fn [Int] Int)` instantiation → its result stays `Type::Var` → the
            // RC-guard SIGSEGV one hop deeper (the 0373 residual). Rooting at
            // `Some(callee_home)` whenever the callee is not in the current module
            // re-checks `h2`'s body in its defining (`hop`) scope (the 0355 module
            // switch), yielding a concrete-`Int`-result `h2$` mono. A genuinely
            // same-(current-)module inner hop still passes `None` (the as-built
            // local path).
            let inner_home = if callee_home == state.current_module {
                None
            } else {
                Some(callee_home.clone())
            };
            // Isolate `state.subst` around the inner-mono recursion (FIXME 0373,
            // preserves 0344). The sole obligation of this recursion is to CREATE
            // the inner hop's concrete mono entry (`register_mono_entry`, with its
            // own GOT slot) so its result type is concrete at codegen. We must NOT
            // let the recursion's call-result unification (the FIXME 0349
            // propagation in `monomorphise_call` ~line 1339) leak back into the
            // PARENT's substitution: when the inner callee is a recursive helper
            // sharing the parent's accumulator var (the 0344 `reduce`/`reduce-loop`
            // fold), that leak pins the accumulator and re-collapses the
            // polymorphic scheme 0344 deliberately keeps. The inner entry is built
            // from `inner_arg_types` (already concrete, captured before this) +
            // the isolated subst, so isolation does not affect what gets created.
            let saved_subst = state.subst.clone();
            let inner_mono = self.monomorphise_call(
                state,
                inner_name,
                &inner_arg_types,
                *inner_span,
                inner_home.as_ref(),
            );
            state.subst = saved_subst;
            if let Some(mono) = inner_mono? {
                resolutions.resolved_calls.insert(
                    *inner_span,
                    ResolvedCall::SigDispatch {
                        mangled_name: JitSymbol::from(mono.defn.name.as_ref()),
                    },
                );
            }
        }
        Ok(())
    }

    /// Look up a constrained function by name.
    #[allow(dead_code)]
    fn get_constrained_fn(
        &self,
        state: &CheckState,
        name: &Symbol,
        home: Option<&ModuleFullPath>,
    ) -> Option<ConstrainedFn> {
        // For an IMPORTED callee (FIXME 0355), the constrained `Def` lives in its
        // DEFINING module — chain-follow to the terminal entry there. The home is
        // a committed import → live view suffices. For a local callee, read the
        // current module directly. Staging-aware (FIXME 0179): the local probe
        // reads through staging so in-cluster constrained-fn registrations are
        // visible.
        let entry = match home {
            Some(h) => self.resolve_terminal_entry_and_home(h, name.as_ref()).map(|(e, _)| e)?,
            None => self.probe_module_entry_owned(&state.current_module, name.as_ref())?,
        };
        match &entry {
            ModuleEntry::Def { kind, scheme, ast, .. } => match kind.as_ref() {
                DefKind::UserFn {
                    fn_state: UserFnState::Constrained(cf),
                } => Some(cf.as_ref().clone()),
                // Pure parametric polymorphism: the scheme is still polymorphic
                // (non-empty `vars`), no trait constraints, but the call site
                // demands a concrete specialisation. Synthesise a
                // `ConstrainedFn` view from the stored AST so the existing
                // `monomorphise_call` machinery applies. The previously-stored
                // defn AST is the source of truth for the body — it was
                // annotated and substitution-applied during the originating
                // Pass 2 / finalize pass for this defn.
                DefKind::UserFn { fn_state }
                    if !matches!(fn_state, UserFnState::Constrained(_))
                        && !scheme.type_vars.is_empty()
                        && ast.is_some() =>
                {
                    Some(ConstrainedFn {
                        variant: ast.as_ref().unwrap().clone(),
                        scheme: scheme.clone(),
                    })
                }
                _ => None,
            },
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build a mangled name from a function name and its concrete parameter types.
///
/// Format: `name$Type1+Type2`
/// Collect every `Apply`-of-bare-`Var` call site in an expression tree, except
/// calls a fn makes to ITSELF (generic self-recursion is not a concrete mono
/// site — its arg types are the defn's own generic vars). Records
/// `(callee_name, arg_spans, call_span)`. Used by
/// `monomorphise_inner_parametric_hops` (FIXME 0373) to find inner hops to
/// recursively monomorphise after a parent hop's body re-check.
fn collect_apply_var_calls(
    expr: &Expr,
    self_name: &Symbol,
    out: &mut Vec<(Symbol, Vec<Span>, Span)>,
) {
    if let Expr::Apply { callee, args, span, .. } = expr
        && let Expr::Var { name, .. } = callee.as_ref()
        && name != self_name
    {
        let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
        out.push((name.clone(), arg_spans, *span));
    }
    crate::program::for_each_child_expr(expr, |child| {
        collect_apply_var_calls(child, self_name, out)
    });
}

/// Collect every `Apply`-of-bare-`Var` call to `self_name` (the OPPOSITE of
/// [`collect_apply_var_calls`], which excludes self-calls). Used by
/// `monomorphise_call` (FIXME 0374) to redirect a polymorphic fn's monomorphic
/// self-recursion to its own mono instance — the original `Polymorphic` def is
/// slot-less, so a by-name self-call would lower through a missing slot.
fn collect_self_apply_calls(
    expr: &Expr,
    self_name: &Symbol,
    out: &mut Vec<(Vec<Span>, Span)>,
) {
    if let Expr::Apply { callee, args, span, .. } = expr
        && let Expr::Var { name, .. } = callee.as_ref()
        && name == self_name
    {
        let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
        out.push((arg_spans, *span));
    }
    crate::program::for_each_child_expr(expr, |child| {
        collect_self_apply_calls(child, self_name, out)
    });
}

pub(crate) fn build_mangled_name(fn_name: &Symbol, param_types: &[Type]) -> String {
    // TRIPWIRE (Phase-4 part A, concrete-boundary-type.md §4-A "secondary
    // hardening", Principle 18). After the all-args-concrete collection gate,
    // every minted instance has all-CONCRETE params (`is_concrete()`). The
    // mangler intentionally NAMES only the head-typed params (`Int`, `Vec`, …)
    // and drops `Fn`-typed params (`concrete_type_name` returns `None` for
    // `Type::Fn` — a concrete-but-unnameable shape: `reduce$Int+Vec` legitimately
    // omits its `(Fn ..)` first param). The hazard the spurious mint exhibited
    // was a `Type::Var` param being dropped — producing a LOSSY name where two
    // distinct partial instantiations collide. Trip on a non-`is_concrete()`
    // param (a residual `Var`/`TyConApp`), NOT on the legitimate `Fn`-param drop,
    // so a future spurious-mint site is caught here.
    debug_assert!(
        param_types.iter().all(|t| t.is_concrete()),
        "build_mangled_name({fn_name}) saw a non-concrete param type \
         (lossy-name hazard — a spurious partial mono instance reached the \
         mangler): {param_types:?}"
    );
    let type_names: Vec<String> = param_types
        .iter()
        .filter_map(|t| concrete_type_name(t).map(|tn| tn.to_string()))
        .collect();
    format!("{}${}", fn_name, type_names.join("+"))
}

/// Extract the bare TypeName from a concrete (non-Var) type.
/// For ADTs, returns the bare name without module qualification.
/// This is used for mangled name construction and impl registry lookup.
fn concrete_type_name(ty: &Type) -> Option<TypeName> {
    match ty {
        Type::Int => Some(TypeName::from("Int")),
        Type::Float => Some(TypeName::from("Float")),
        Type::Bool => Some(TypeName::from("Bool")),
        Type::String => Some(TypeName::from("String")),
        Type::ADT(fqtn, _) => Some(fqtn.name.clone()),
        _ => None,
    }
}

/// Build the AST body for a known default trait method.
///
/// Hard-codes the bodies for the builtin default methods:
///   Eq.!=  → (not (= x y))
///   Ord.>  → (< y x)
///   Ord.<= → (not (< y x))
///   Ord.>= → (not (< x y))
fn build_default_body(
    trait_name: &str,
    method_name: &str,
    param_names: &[Symbol],
    span: Span,
) -> Result<cranelisp_types::Expr, CranelispError> {
    use cranelisp_types::Expr;

    if param_names.len() != 2 {
        return Err(CranelispError::TypeError {
            message: format!(
                "default method {trait_name}.{method_name}: expected 2 params, got {}",
                param_names.len()
            ),
            location: ErrorLocation::from_span(span),
        });
    }

    let x = Expr::var(param_names[0].clone(), span);
    let y = Expr::var(param_names[1].clone(), span);
    let not_var = Expr::var(Symbol::from("not"), span);
    let eq_var = Expr::var(Symbol::from("="), span);
    let lt_var = Expr::var(Symbol::from("<"), span);

    match (trait_name, method_name) {
        // != → (not (= x y))
        ("Eq", "!=") => Ok(Expr::Apply {
            callee: Box::new(not_var),
            args: vec![Expr::Apply {
                callee: Box::new(eq_var),
                args: vec![x, y],
                span,
                resolved_call: None,
                inferred_type: None,
            }],
            span,
            resolved_call: None,
            inferred_type: None,
        }),
        // > → (< y x)
        ("Ord", ">") => Ok(Expr::Apply {
            callee: Box::new(lt_var),
            args: vec![y, x],
            span,
            resolved_call: None,
            inferred_type: None,
        }),
        // <= → (not (< y x))
        ("Ord", "<=") => Ok(Expr::Apply {
            callee: Box::new(not_var),
            args: vec![Expr::Apply {
                callee: Box::new(lt_var),
                args: vec![y, x],
                span,
                resolved_call: None,
                inferred_type: None,
            }],
            span,
            resolved_call: None,
            inferred_type: None,
        }),
        // >= → (not (< x y))
        ("Ord", ">=") => Ok(Expr::Apply {
            callee: Box::new(not_var),
            args: vec![Expr::Apply {
                callee: Box::new(lt_var),
                args: vec![x, y],
                span,
                resolved_call: None,
                inferred_type: None,
            }],
            span,
            resolved_call: None,
            inferred_type: None,
        }),
        _ => Err(CranelispError::TypeError {
            message: format!(
                "no hard-coded default body for {trait_name}.{method_name}"
            ),
            location: ErrorLocation::from_span(span),
        }),
    }
}

// `sexp_to_default_expr` retired in Sprint 72 Wave 1 — per S69 Submission 26,
// `TraitMethodSig.default_body: Option<Expr>` carries pre-parsed AST (vindication
// of the prior facade target). The Sexp→Expr lowering at trait-decl time now
// lives in the frontend `build_method_sig` path; the typecheck consumer simply
// clones the Expr. Decision-grounding: S69 Submission 26 + `design/arch/facades/typecheck.md` §"Typing rule".

/// Map a `TypeRef` to a `Type` for intrinsic scalar names, returning `None`
/// for non-intrinsic names. Caller decides how to handle unknown / user types.
/// Per C-13 (`Type::from_name` retired): intrinsic-bare-names resolve directly;
/// non-intrinsic names flow through ADT placeholders.
fn type_from_intrinsic_ref(name: &cranelisp_types::TypeRef) -> Option<Type> {
    if name.module.is_some() {
        return None;
    }
    match name.name.as_ref() {
        "Int" => Some(Type::Int),
        "Bool" => Some(Type::Bool),
        "Float" => Some(Type::Float),
        "String" => Some(Type::String),
        _ => None,
    }
}

/// Resolve a TypeExpr in a trait context, substituting SelfType with the given type.
fn resolve_trait_type_expr(
    texpr: &cranelisp_types::TypeExpr,
    self_type: &Type,
    span: Span,
    var_map: &mut HashMap<Symbol, Type>,
    next_id: &mut TypeId,
) -> Result<Type, CranelispError> {
    use cranelisp_types::TypeExpr;

    match texpr {
        TypeExpr::SelfType => Ok(self_type.clone()),
        TypeExpr::Named(name) => type_from_intrinsic_ref(name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("unknown type: {name}"),
                location: ErrorLocation::from_span(span),
            }),
        TypeExpr::TypeVar(name) => {
            if let Some(ty) = var_map.get(name) {
                Ok(ty.clone())
            } else {
                let ty = crate::unify::fresh_var(next_id);
                var_map.insert(name.clone(), ty.clone());
                Ok(ty)
            }
        }
        TypeExpr::FnType(params, ret) => {
            let ps: Vec<Type> = params
                .iter()
                .map(|p| resolve_trait_type_expr(p, self_type, span, var_map, next_id))
                .collect::<Result<Vec<_>, _>>()?;
            let r = resolve_trait_type_expr(ret, self_type, span, var_map, next_id)?;
            Ok(Type::Fn(ps, Box::new(r)))
        }
        TypeExpr::Applied(name, args) => {
            // Regular ADT application: (Option Int), (List :a)
            // Use a placeholder FQTypeName — the bare name will be resolved
            // when the type flows through the module system.
            let fqtn = FQTypeName::new(ModuleFullPath::from(""), name.name.clone());
            let resolved_args: Vec<Type> = args
                .iter()
                .map(|a| resolve_trait_type_expr(a, self_type, span, var_map, next_id))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Type::ADT(fqtn, resolved_args))
        }
        // Stacked trait-bound annotations (`:Eq :Display a`) are a *param-binder*
        // construct (constrained-fn parameters), not a trait-method-signature
        // construct: a trait method's parameter types are concrete types or
        // `Self`/type-vars, never a free constrained binder. Reject rather than
        // silently accept (FIXME 0346).
        TypeExpr::Bounds(_) => Err(CranelispError::TypeError {
            message: "trait bounds are not allowed in a trait-method signature \
                      type position".to_string(),
            location: ErrorLocation::from_span(span),
        }),
    }
}

// ---------------------------------------------------------------------------
// HKT Helpers (free functions)
// ---------------------------------------------------------------------------

/// Resolve a TypeExpr in HKT context, producing TyConApp for constructor variable applications.
fn resolve_type_expr_hkt(
    texpr: &cranelisp_types::TypeExpr,
    con_var_map: &HashMap<Symbol, TypeId>,
    type_var_map: &mut HashMap<Symbol, TypeId>,
    next_id: &mut TypeId,
    span: Span,
) -> Result<Type, CranelispError> {
    use cranelisp_types::TypeExpr;

    match texpr {
        TypeExpr::Applied(name, args) => {
            let name_sym = Symbol::from(name.name.as_ref());
            if let Some(&con_id) = con_var_map.get(&name_sym) {
                // Constructor variable application: (f a) -> TyConApp(f_id, [a])
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| resolve_type_expr_hkt(a, con_var_map, type_var_map, next_id, span))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Type::TyConApp(con_id, resolved_args))
            } else {
                // Regular ADT application: (Option Int)
                let fqtn = FQTypeName::new(ModuleFullPath::from(""), name.name.clone());
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| resolve_type_expr_hkt(a, con_var_map, type_var_map, next_id, span))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Type::ADT(fqtn, resolved_args))
            }
        }
        TypeExpr::TypeVar(name) => {
            if let Some(&con_id) = con_var_map.get(name) {
                // Bare constructor variable used as a type
                Ok(Type::Var(con_id))
            } else if let Some(&id) = type_var_map.get(name) {
                Ok(Type::Var(id))
            } else {
                let (ty, id) = crate::unify::fresh_var_id(next_id);
                type_var_map.insert(name.clone(), id);
                Ok(ty)
            }
        }
        TypeExpr::Named(name) => {
            Ok(type_from_intrinsic_ref(name).unwrap_or_else(|| { Type::ADT(FQTypeName::new(ModuleFullPath::from(""), name.name.clone()), vec![]) }))
        }
        TypeExpr::SelfType => {
            Err(CranelispError::TypeError {
                message: "Self is not allowed in HKT trait signatures".to_string(),
                location: ErrorLocation::from_span(span),
            })
        }
        TypeExpr::FnType(params, ret) => {
            let param_tys: Vec<Type> = params
                .iter()
                .map(|p| resolve_type_expr_hkt(p, con_var_map, type_var_map, next_id, span))
                .collect::<Result<Vec<_>, _>>()?;
            let ret_ty = resolve_type_expr_hkt(ret, con_var_map, type_var_map, next_id, span)?;
            Ok(Type::Fn(param_tys, Box::new(ret_ty)))
        }
        // Trait bounds are a param-binder construct, not an HKT trait-method
        // signature construct — reject (FIXME 0346).
        TypeExpr::Bounds(_) => Err(CranelispError::TypeError {
            message: "trait bounds are not allowed in an HKT trait-method \
                      signature type position".to_string(),
            location: ErrorLocation::from_span(span),
        }),
    }
}

/// Resolve a TypeExpr for an HKT impl method.
/// Constructor variable applications are resolved to concrete ADT applications.
/// E.g., for `(impl Functor Option ...)`, `(f a)` becomes `(Option a)`.
fn resolve_type_expr_hkt_impl(
    texpr: &cranelisp_types::TypeExpr,
    con_var_names: &[Symbol],
    target_fqtn: &FQTypeName,
    type_var_map: &mut HashMap<Symbol, TypeId>,
    next_id: &mut TypeId,
    span: Span,
) -> Result<Type, CranelispError> {
    use cranelisp_types::TypeExpr;

    match texpr {
        TypeExpr::Applied(name, args) => {
            let name_sym = Symbol::from(name.name.as_ref());
            let fqtn = if con_var_names.contains(&name_sym) {
                // Constructor variable — resolve to the target ADT's FQTypeName.
                target_fqtn.clone()
            } else {
                // Non-constructor-var Applied type — use target module as fallback.
                FQTypeName::new(target_fqtn.module.clone(), name.name.clone())
            };
            let resolved_args: Vec<Type> = args
                .iter()
                .map(|a| resolve_type_expr_hkt_impl(a, con_var_names, target_fqtn, type_var_map, next_id, span))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Type::ADT(fqtn, resolved_args))
        }
        TypeExpr::TypeVar(name) => {
            if let Some(&id) = type_var_map.get(name) {
                Ok(Type::Var(id))
            } else {
                let (ty, id) = crate::unify::fresh_var_id(next_id);
                type_var_map.insert(name.clone(), id);
                Ok(ty)
            }
        }
        TypeExpr::Named(name) => {
            Ok(type_from_intrinsic_ref(name).unwrap_or_else(|| { // Use target module as fallback for user-defined types.
                Type::ADT(FQTypeName::new(target_fqtn.module.clone(), name.name.clone()), vec![]) }))
        }
        TypeExpr::SelfType => {
            Err(CranelispError::TypeError {
                message: "Self is not allowed in HKT trait signatures".to_string(),
                location: ErrorLocation::from_span(span),
            })
        }
        TypeExpr::FnType(params, ret) => {
            let param_tys: Vec<Type> = params
                .iter()
                .map(|p| resolve_type_expr_hkt_impl(p, con_var_names, target_fqtn, type_var_map, next_id, span))
                .collect::<Result<Vec<_>, _>>()?;
            let ret_ty = resolve_type_expr_hkt_impl(ret, con_var_names, target_fqtn, type_var_map, next_id, span)?;
            Ok(Type::Fn(param_tys, Box::new(ret_ty)))
        }
        // Trait bounds are a param-binder construct, not an HKT impl-method
        // signature construct — reject (FIXME 0346).
        TypeExpr::Bounds(_) => Err(CranelispError::TypeError {
            message: "trait bounds are not allowed in an HKT impl-method \
                      signature type position".to_string(),
            location: ErrorLocation::from_span(span),
        }),
    }
}

/// Check if a TypeExpr uses any of the constructor variable names in Applied position.
fn type_expr_uses_con_var(texpr: &cranelisp_types::TypeExpr, con_names: &[Symbol]) -> bool {
    use cranelisp_types::TypeExpr;

    match texpr {
        TypeExpr::Applied(name, args) => {
            let name_sym = Symbol::from(name.name.as_ref());
            con_names.contains(&name_sym)
                || args.iter().any(|a| type_expr_uses_con_var(a, con_names))
        }
        TypeExpr::FnType(params, ret) => {
            params.iter().any(|p| type_expr_uses_con_var(p, con_names))
                || type_expr_uses_con_var(ret, con_names)
        }
        _ => false,
    }
}

/// Find the first parameter index that uses a constructor variable in Applied position.
fn find_hkt_param_index(params: &[(Symbol, cranelisp_types::TypeExpr)], type_params: &[Symbol]) -> usize {
    for (idx, (_, param)) in params.iter().enumerate() {
        if type_expr_uses_con_var(param, type_params) {
            return idx;
        }
    }
    0 // fallback to first param
}

/// Determine the arity (number of type args) of a constructor variable in a trait declaration.
fn con_var_arity(decl: &TraitDeclInfo, con_name: &Symbol) -> Option<usize> {
    for method in &decl.methods {
        for (_, param) in &method.params {
            if let Some(arity) = find_applied_arity(param, con_name) {
                return Some(arity);
            }
        }
        if let Some(arity) = find_applied_arity(&method.ret_type, con_name) {
            return Some(arity);
        }
    }
    None
}

/// Find the arity of a constructor variable name in a TypeExpr tree.
fn find_applied_arity(texpr: &cranelisp_types::TypeExpr, con_name: &Symbol) -> Option<usize> {
    use cranelisp_types::TypeExpr;

    match texpr {
        TypeExpr::Applied(name, args) => {
            let name_sym = Symbol::from(name.name.as_ref());
            if &name_sym == con_name {
                Some(args.len())
            } else {
                args.iter().find_map(|a| find_applied_arity(a, con_name))
            }
        }
        TypeExpr::FnType(params, ret) => {
            params.iter().find_map(|p| find_applied_arity(p, con_name))
                .or_else(|| find_applied_arity(ret, con_name))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// HKT Method Resolution Helpers (on TypeChecker)
// ---------------------------------------------------------------------------

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Get the HKT param index for a method name, defaulting to 0.
    /// For mangled names like "Functor.fmap$Option", extracts the base method name first.
    ///
    /// Per Principle 17 — current-module-rooted; trait declarations reach
    /// here via the prelude's per-symbol `ModuleEntry::Import` bindings (or
    /// the user's explicit imports), which the underlying chain-follow
    /// follows back to the trait's defining module.
    fn hkt_param_idx_for_method(&self, state: &CheckState, name: &Symbol) -> usize {
        let name_str = name.as_ref();
        // Try direct lookup
        if let Some(idx) = self.find_hkt_param_index_in_registry(state, name_str) {
            return idx;
        }
        // For mangled names like "Functor.fmap$Option", extract the method name
        if let Some(dollar_pos) = name_str.find('$') {
            let prefix = &name_str[..dollar_pos];
            // Handle trait-qualified names: "Trait.method" -> "method"
            let base = if let Some(dot_pos) = prefix.rfind('.') {
                &prefix[dot_pos + 1..]
            } else {
                prefix
            };
            if let Some(idx) = self.find_hkt_param_index_in_registry(state, base) {
                return idx;
            }
        }
        0
    }

    /// Walk trait declarations visible from `state.current_module` to find a
    /// method's `hkt_param_index`.
    ///
    /// Per Principle 17 shape 4 (bulk introspection — current-module-only):
    /// iterates the current module's symbol table; `Import`/`Reexport`
    /// entries are chain-followed to their terminal `TraitDecl` so traits
    /// imported (e.g., via the prelude) are reachable.
    ///
    /// When the current module misses and its prelude-fallback bit is ON, the
    /// prelude's own table is iterated as the implicit-prelude outer scope
    /// (S78 §2.7.5 / FIXME 0315) — so an HKT trait declared in the prelude with
    /// a non-zero `hkt_param_index` dispatches on the correct argument even
    /// when the current module never imports it explicitly.
    fn find_hkt_param_index_in_registry(
        &self,
        state: &CheckState,
        method_name: &str,
    ) -> Option<usize> {
        if let Some(idx) =
            self.find_hkt_param_index_in_module(state, &state.current_module, method_name, false)
        {
            return Some(idx);
        }
        // Inner miss — consult the prelude outer scope iff the bit is ON
        // (`prelude_fallback_target`; absence-is-OFF, never self-fallback). Only
        // PUBLIC prelude `TraitDecl`s are reachable as a bare method through the
        // implicit outer scope (`/review` I-1) — `public_only = true`.
        let prelude = self.prelude_fallback_target(&state.current_module)?;
        self.find_hkt_param_index_in_module(state, &prelude, method_name, true)
    }

    /// Iterate `module_path`'s symbol table for a `TraitDecl` carrying
    /// `method_name`, returning that method's `hkt_param_index`. Shared by the
    /// current-module probe and the prelude outer-scope fallback in
    /// [`Self::find_hkt_param_index_in_registry`].
    ///
    /// `public_only` filters the scanned `module_path` bindings to PUBLIC heads
    /// only — set for the prelude outer-scope fallback hop so a Private prelude
    /// `TraitDecl` does not leak its methods as bare names (`/review` I-1).
    fn find_hkt_param_index_in_module(
        &self,
        state: &CheckState,
        module_path: &ModuleFullPath,
        method_name: &str,
        public_only: bool,
    ) -> Option<usize> {
        // Staging-aware (FIXME 0179): iterate the unioned View when probing the
        // current module so in-cluster TraitDecl registrations are visible. For
        // the prelude fallback the prelude is never the staging module, so a
        // plain owned-name snapshot is sufficient. When `public_only`, drop
        // non-public head bindings before chain-following (I-1).
        let names: Vec<Symbol> = if *module_path == state.current_module {
            let r = self.current_symbol_table(state);
            r.view()
                .iter()
                .filter(|(_, entry)| !public_only || entry.is_public())
                .map(|(name, _)| name.clone())
                .collect()
        } else {
            let mut names = Vec::new();
            self.for_each_in_module(module_path, |name, entry| {
                if !public_only || entry.is_public() {
                    names.push(name.clone());
                }
            });
            names
        };
        for name in &names {
            if let Some(terminal) =
                self.resolve_terminal_entry_and_home(module_path, name.as_ref()).map(|(e, _home)| e)
                && let ModuleEntry::TraitDecl { info, .. } = terminal
            {
                for method in &info.methods {
                    if method.name.as_ref() == method_name {
                        return method.hkt_param_index;
                    }
                }
            }
        }
        None
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
