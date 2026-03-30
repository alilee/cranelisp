//! Trait registration, impl checking, method resolution, and monomorphisation.
//!
//! Ring 2A: traits provide constrained polymorphism. Operators like `+` are
//! resolved as trait methods (`Num.+$Int`), not builtin primitives.

use std::collections::{HashMap, HashSet};

use cranelisp_types::{
    ConstrainedFn, CranelispError, DefKind, Defn, DefnVariant, JitSymbol, MethodResolutions,
    ModuleEntry, MonoDefn, ResolvedCall, Scheme, Span, Symbol, TraitDecl,
    TraitImpl, TraitMethodSig, TraitName, Type, TypeId, TypeName, Visibility,
    apply,
};

use crate::checker::TypeChecker;
use crate::scheme;

// ---------------------------------------------------------------------------
// Trait Registry (stored on TypeChecker)
// ---------------------------------------------------------------------------

/// Registered trait declarations, keyed by trait name.
#[derive(Debug, Clone, Default)]
pub struct TraitRegistry {
    /// Trait declarations: trait name -> TraitDecl
    pub(crate) decls: HashMap<TraitName, TraitDecl>,
    /// Method -> trait name reverse lookup: method name -> trait name
    pub(crate) method_to_trait: HashMap<Symbol, TraitName>,
}

impl TraitRegistry {
    /// Check if a method belongs to a specific trait.
    pub fn method_belongs_to_trait(&self, method: &Symbol, trait_name: &TraitName) -> bool {
        self.method_to_trait
            .get(method) == Some(trait_name)
    }
}

/// A registered trait implementation.
#[derive(Debug, Clone)]
#[allow(dead_code)] // Fields are stored for future use (e.g., method resolution by impl type).
pub struct RegisteredImpl {
    pub trait_name: TraitName,
    pub impl_type: TypeName,
    /// Method name -> primitive name it delegates to (for builtin impls)
    pub method_primitives: HashMap<Symbol, Symbol>,
}

/// Registry of trait implementations, keyed by trait_name then impl_type.
#[derive(Debug, Clone, Default)]
pub struct ImplRegistry {
    /// trait_name -> (impl_type -> RegisteredImpl)
    pub(crate) impls: HashMap<TraitName, HashMap<TypeName, RegisteredImpl>>,
}

impl ImplRegistry {
    /// Look up an impl for a specific trait and concrete type.
    #[allow(dead_code)]
    pub fn get(
        &self,
        trait_name: &TraitName,
        impl_type: &TypeName,
    ) -> Option<&RegisteredImpl> {
        self.impls.get(trait_name)?.get(impl_type)
    }

    /// Check if an impl exists for a trait and type.
    pub fn has_impl(
        &self,
        trait_name: &TraitName,
        impl_type: &TypeName,
    ) -> bool {
        self.impls
            .get(trait_name)
            .is_some_and(|inner| inner.contains_key(impl_type))
    }
}

// ---------------------------------------------------------------------------
// Active Constraints (tracked during body checking)
// ---------------------------------------------------------------------------

/// Tracks trait constraints on type variables during inference.
/// Populated when a constrained scheme is instantiated, consulted during generalize.
#[derive(Debug, Clone, Default)]
pub struct ActiveConstraints {
    /// TypeId -> list of required trait names
    pub(crate) constraints: HashMap<TypeId, Vec<TraitName>>,
}

impl ActiveConstraints {
    /// Add a constraint on a type variable (idempotent — duplicates are ignored).
    pub fn add(&mut self, var_id: TypeId, trait_name: TraitName) {
        let traits = self.constraints.entry(var_id).or_default();
        if !traits.contains(&trait_name) {
            traits.push(trait_name);
        }
    }

    /// Get constraints for a type variable.
    #[allow(dead_code)]
    pub fn get(&self, var_id: TypeId) -> Option<&Vec<TraitName>> {
        self.constraints.get(&var_id)
    }

    /// Clear all active constraints (between top-level forms).
    #[allow(dead_code)]
    pub fn clear(&mut self) {
        self.constraints.clear();
    }

    /// Iterate over all (var_id, traits) pairs.
    pub fn all(&self) -> impl Iterator<Item = (&TypeId, &Vec<TraitName>)> {
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
    ) -> HashMap<TypeId, Vec<TraitName>> {
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

impl TypeChecker {
    /// Register a trait declaration.
    ///
    /// - Stores the TraitDecl in the trait registry
    /// - Registers each method as a constrained polymorphic symbol
    /// - Registers the trait name in the symbol table as TraitDecl
    pub(crate) fn register_trait_decl(
        &mut self,
        decl: &TraitDecl,
    ) -> Result<(), CranelispError> {
        // Check for duplicate trait name
        if self.trait_registry.get_mut().unwrap().decls.contains_key(&decl.name) {
            return Err(CranelispError::TypeError {
                message: format!("trait {} already defined", decl.name),
                span: decl.span,
            });
        }

        // If trait has type_params used in Applied position, use HKT registration path
        if !decl.type_params.is_empty()
            && decl.methods.iter().any(|m| {
                m.params
                    .iter()
                    .any(|p| type_expr_uses_con_var(p, &decl.type_params))
                    || type_expr_uses_con_var(&m.ret_type, &decl.type_params)
            })
        {
            return self.register_hkt_trait(decl);
        }

        // Allocate a fresh type variable for the trait's type parameter
        let (_, type_var_id) = self.fresh_var_id();

        // Register each method with a constrained polymorphic scheme
        for method in &decl.methods {
            self.register_trait_method(
                &decl.name,
                method,
                type_var_id,
                &decl.type_params,
                decl.span,
            )?;
        }

        // Store the declaration
        self.trait_registry.get_mut().unwrap()
            .decls
            .insert(decl.name.clone(), decl.clone());

        // Register in symbol table as TraitDecl entry
        self.current_symbol_table_mut().insert(
            Symbol::from(decl.name.as_ref()),
            cranelisp_types::ModuleEntry::TraitDecl {
                decl: decl.clone(),
                visibility: decl.visibility,
                sexp: None,
            },
        );

        Ok(())
    }

    /// Register an HKT trait where type_params are type constructor variables.
    /// E.g., `(deftrait (Functor f) (fmap [(Fn [a] b) (f a)] (f b)))`
    fn register_hkt_trait(
        &mut self,
        decl: &TraitDecl,
    ) -> Result<(), CranelispError> {
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
            let param_idx = find_hkt_param_index(&method.params, &decl.type_params);
            modified_decl.methods[mi].hkt_param_index = Some(param_idx);

            // Create fresh regular type vars for any type variables in the signature
            // that are NOT constructor params
            let mut type_var_map: HashMap<Symbol, TypeId> = HashMap::new();

            let param_tys: Vec<Type> = method
                .params
                .iter()
                .map(|p| resolve_type_expr_hkt(p, &con_var_map, &mut type_var_map, self.next_id.get_mut(), decl.span))
                .collect::<Result<Vec<_>, _>>()?;
            let ret_ty =
                resolve_type_expr_hkt(&method.ret_type, &con_var_map, &mut type_var_map, self.next_id.get_mut(), decl.span)?;

            // Collect all var IDs (constructor + regular)
            let mut all_vars: Vec<TypeId> = con_var_map.values().copied().collect();
            all_vars.extend(type_var_map.values());
            all_vars.sort();
            all_vars.dedup();

            // Add trait constraint to constructor vars
            let mut constraints: HashMap<TypeId, Vec<TraitName>> = HashMap::new();
            for &con_id in con_var_map.values() {
                constraints.insert(con_id, vec![decl.name.clone()]);
            }

            let method_scheme = Scheme {
                vars: all_vars,
                constraints,
                ty: Type::Fn(param_tys, Box::new(ret_ty)),
            };

            // Register the method name as a symbol
            self.current_symbol_table_mut().insert(
                method.name.clone(),
                cranelisp_types::ModuleEntry::Def {
                    scheme: method_scheme,
                    visibility: Visibility::Public,
                    docstring: method.docstring.clone(),
                    param_names: method.default_param_names.clone(),
                    kind: Box::new(cranelisp_types::DefKind::UserFn {
                        constrained_fn: None,
                    }),
                    callees: Vec::new(),
                },
            );

            // Register reverse lookup
            self.trait_registry.get_mut().unwrap()
                .method_to_trait
                .insert(method.name.clone(), decl.name.clone());
        }

        // Store the modified declaration (with hkt_param_index set)
        self.trait_registry.get_mut().unwrap()
            .decls
            .insert(decl.name.clone(), modified_decl.clone());

        // Register in symbol table as TraitDecl entry (with hkt_param_index)
        self.current_symbol_table_mut().insert(
            Symbol::from(decl.name.as_ref()),
            cranelisp_types::ModuleEntry::TraitDecl {
                decl: modified_decl,
                visibility: decl.visibility,
                sexp: None,
            },
        );

        Ok(())
    }

    /// Register a single trait method with its constrained polymorphic scheme.
    fn register_trait_method(
        &mut self,
        trait_name: &TraitName,
        method: &TraitMethodSig,
        type_var_id: TypeId,
        trait_type_params: &[Symbol],
        span: Span,
    ) -> Result<(), CranelispError> {
        let method_type =
            self.build_method_type(method, type_var_id, trait_type_params, span)?;

        let mut constraints = HashMap::new();
        constraints.insert(type_var_id, vec![trait_name.clone()]);

        let method_scheme = Scheme {
            vars: vec![type_var_id],
            constraints,
            ty: method_type,
        };

        // Register the method name as a symbol
        self.current_symbol_table_mut().insert(
            method.name.clone(),
            cranelisp_types::ModuleEntry::Def {
                scheme: method_scheme,
                visibility: Visibility::Public,
                docstring: method.docstring.clone(),
                param_names: method.default_param_names.clone(),
                kind: Box::new(cranelisp_types::DefKind::UserFn {
                    constrained_fn: None,
                }),
                callees: Vec::new(),
            },
        );

        // Register reverse lookup
        self.trait_registry.get_mut().unwrap()
            .method_to_trait
            .insert(method.name.clone(), trait_name.clone());

        Ok(())
    }

    /// Build the function type for a trait method.
    ///
    /// Resolves `Self` type expressions to the type variable.
    /// TypeVars matching the trait's type parameters map to self_type;
    /// other TypeVars get fresh type variables (I3 fix).
    fn build_method_type(
        &mut self,
        method: &TraitMethodSig,
        type_var_id: TypeId,
        trait_type_params: &[Symbol],
        span: Span,
    ) -> Result<Type, CranelispError> {
        let self_type = Type::Var(type_var_id);

        // Pre-seed var_map: trait type params map to self_type.
        let mut var_map: HashMap<Symbol, Type> = HashMap::new();
        for param in trait_type_params {
            var_map.insert(param.clone(), self_type.clone());
        }

        let param_types: Vec<Type> = method
            .params
            .iter()
            .map(|p| resolve_trait_type_expr(p, &self_type, span, &mut var_map, self.next_id.get_mut()))
            .collect::<Result<Vec<_>, _>>()?;

        let ret_type =
            resolve_trait_type_expr(&method.ret_type, &self_type, span, &mut var_map, self.next_id.get_mut())?;

        Ok(Type::Fn(param_types, Box::new(ret_type)))
    }
}

// ---------------------------------------------------------------------------
// Impl Registration and Checking
// ---------------------------------------------------------------------------

impl TypeChecker {
    /// Register and validate a trait implementation.
    pub(crate) fn register_trait_impl(
        &mut self,
        impl_: &TraitImpl,
    ) -> Result<Vec<Defn>, CranelispError> {
        // Look up the trait declaration
        let decl = self
            .trait_registry.get_mut().unwrap()
            .decls
            .get(&impl_.trait_name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("unknown trait: {}", impl_.trait_name),
                span: impl_.span,
            })?
            .clone();

        // HKT arity validation: if the trait has constructor variables,
        // verify the impl target is a type constructor with matching arity.
        if !decl.type_params.is_empty() {
            let is_hkt = decl.methods.iter().any(|m| {
                m.params
                    .iter()
                    .any(|p| type_expr_uses_con_var(p, &decl.type_params))
                    || type_expr_uses_con_var(&m.ret_type, &decl.type_params)
            });
            if is_hkt {
                for con_name in &decl.type_params {
                    if let Some(expected_arity) = con_var_arity(&decl, con_name) {
                        // Check if impl target is a primitive type
                        if expected_arity > 0 {
                            match impl_.target_type.as_ref() {
                                "Int" | "Bool" | "String" | "Float" => {
                                    return Err(CranelispError::TypeError {
                                        message: format!(
                                            "{} is not a type constructor (trait {} expects arity {})",
                                            impl_.target_type, impl_.trait_name, expected_arity
                                        ),
                                        span: impl_.span,
                                    });
                                }
                                _ => {}
                            }
                        }
                        // Check arity of known ADT types
                        if let Some(td) = self.type_defs.get_mut().unwrap().get(&impl_.target_type)
                            && td.type_params.len() != expected_arity
                        {
                            return Err(CranelispError::TypeError {
                                message: format!(
                                    "{} has {} type parameters, but trait {} expects a constructor with arity {}",
                                    impl_.target_type,
                                    td.type_params.len(),
                                    impl_.trait_name,
                                    expected_arity
                                ),
                                span: impl_.span,
                            });
                        }
                    }
                }
            }
        }

        // Check all required methods are present (that don't have defaults)
        self.check_impl_methods_present(&decl, impl_)?;

        // Generate default method implementations for missing methods
        let default_defns =
            self.generate_default_methods(&decl, impl_)?;

        // Register the impl
        let mut method_primitives = HashMap::new();
        for method_defn in &impl_.methods {
            // No primitive mappings for user impls
            method_primitives
                .insert(method_defn.name.clone(), method_defn.name.clone());
        }

        self.impl_registry.get_mut().unwrap().impls
            .entry(impl_.trait_name.clone())
            .or_default()
            .insert(
                impl_.target_type.clone(),
                RegisteredImpl {
                    trait_name: impl_.trait_name.clone(),
                    impl_type: impl_.target_type.clone(),
                    method_primitives,
                },
            );

        // Type-check each impl method body and generate mangled-name Defns.
        let mut all_defns = default_defns;
        for method_defn in &impl_.methods {
            self.check_impl_method(
                &decl,
                impl_,
                method_defn,
            )?;

            // Gap 3: Emit a Defn with the mangled name for the backend to compile.
            let mangled = format!(
                "{}.{}${}",
                impl_.trait_name, method_defn.name, impl_.target_type
            );
            all_defns.push(Defn {
                name: Symbol::from(mangled.as_str()),
                docstring: method_defn.docstring.clone(),
                variants: vec![DefnVariant {
                    params: method_defn.params().to_vec(),
                    param_annotations: method_defn.param_annotations().to_vec(),
                    body: method_defn.body().clone(),
                    span: method_defn.span,
                }],
                visibility: Visibility::Public,
                span: method_defn.span,
            });
        }

        Ok(all_defns)
    }

    /// Check that all required methods are provided in the impl.
    fn check_impl_methods_present(
        &self,
        decl: &TraitDecl,
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
                        decl.name, impl_.target_type, method_sig.name
                    ),
                    span: impl_.span,
                });
            }
        }

        Ok(())
    }

    /// Type-check a single impl method.
    fn check_impl_method(
        &mut self,
        decl: &TraitDecl,
        impl_: &TraitImpl,
        method_defn: &Defn,
    ) -> Result<(), CranelispError> {
        // Look up the method signature from the trait
        let method_sig = decl
            .methods
            .iter()
            .find(|m| m.name == method_defn.name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!(
                    "method {} not found in trait {}",
                    method_defn.name, decl.name
                ),
                span: method_defn.span,
            })?;

        // Check if this is an HKT trait (constructor variables used in Applied position)
        let is_hkt = !decl.type_params.is_empty()
            && decl.methods.iter().any(|m| {
                m.params
                    .iter()
                    .any(|p| type_expr_uses_con_var(p, &decl.type_params))
                    || type_expr_uses_con_var(&m.ret_type, &decl.type_params)
            });

        if is_hkt {
            return self.check_hkt_impl_method(decl, impl_, method_defn, method_sig);
        }

        // Resolve the concrete type for Self
        let concrete_self = Type::from_name(impl_.target_type.as_ref())
            .unwrap_or_else(|| {
                Type::ADT(impl_.target_type.clone(), vec![])
            });

        // Pre-seed var_map: trait type params map to concrete self type.
        let mut var_map: HashMap<Symbol, Type> = HashMap::new();
        for param in &decl.type_params {
            var_map.insert(param.clone(), concrete_self.clone());
        }

        // Build concrete param types
        let param_types: Vec<Type> = method_sig
            .params
            .iter()
            .map(|p| resolve_trait_type_expr(p, &concrete_self, method_defn.span, &mut var_map, self.next_id.get_mut()))
            .collect::<Result<Vec<_>, _>>()?;

        let ret_ty = resolve_trait_type_expr(
            &method_sig.ret_type,
            &concrete_self,
            method_defn.span,
            &mut var_map,
            self.next_id.get_mut(),
        )?;

        // Check the body
        self.check_defn_body_with_types(method_defn, &param_types, &ret_ty)?;

        Ok(())
    }

    /// Type-check an HKT impl method.
    ///
    /// For `(impl Functor Option (defn fmap [func opt] ...))`:
    /// - The constructor variable `f` maps to the impl target `Option`
    /// - `(f a)` in the signature resolves to `(Option a)` via ADT application
    fn check_hkt_impl_method(
        &mut self,
        decl: &TraitDecl,
        impl_: &TraitImpl,
        method_defn: &Defn,
        method_sig: &TraitMethodSig,
    ) -> Result<(), CranelispError> {
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
                let (ty, _) = crate::unify::fresh_var_id(self.next_id.get_mut());
                ty
            })
            .collect();
        let concrete_self = Type::ADT(impl_.target_type.clone(), type_arg_vars);

        // Build param types using HKT-aware resolution that substitutes
        // constructor variable applications with concrete ADT applications
        let param_types: Vec<Type> = method_sig
            .params
            .iter()
            .map(|p| resolve_type_expr_hkt_impl(
                p,
                &decl.type_params,
                &impl_.target_type,
                &mut type_var_map,
                self.next_id.get_mut(),
                impl_.span,
            ))
            .collect::<Result<Vec<_>, _>>()?;

        let ret_ty = resolve_type_expr_hkt_impl(
            &method_sig.ret_type,
            &decl.type_params,
            &impl_.target_type,
            &mut type_var_map,
            self.next_id.get_mut(),
            impl_.span,
        )?;

        // Pre-unify the dispatch parameter with the concrete self type
        if let Some(param_idx) = method_sig.hkt_param_index
            && let Some(param_ty) = param_types.get(param_idx)
        {
            self.unify(param_ty, &concrete_self, method_defn.span)?;
        }

        // Check the body
        self.check_defn_body_with_types(method_defn, &param_types, &ret_ty)?;

        Ok(())
    }

    /// Check a function body with explicit parameter types.
    /// Shared helper for impl method checking.
    pub(crate) fn check_defn_body_with_types(
        &mut self,
        defn: &Defn,
        param_types: &[Type],
        ret_ty: &Type,
    ) -> Result<(), CranelispError> {
        self.push_scope();

        for (param_name, param_ty) in
            defn.params().iter().zip(param_types.iter())
        {
            self.bind_local(
                param_name.clone(),
                scheme::mono(param_ty.clone()),
            );
        }

        let body_ty = self.infer_expr(defn.body())?;
        self.unify(&body_ty, ret_ty, defn.span)?;

        // Post-inference deferred trait resolution
        self.resolve_deferred_trait_calls(defn.body());

        self.pop_scope();
        Ok(())
    }

    /// Generate default method implementations for methods not provided in the impl.
    fn generate_default_methods(
        &self,
        decl: &TraitDecl,
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
                decl.name, method_sig.name, impl_.target_type
            );

            let span = impl_.span;
            let body = build_default_body(
                decl.name.as_ref(),
                method_sig.name.as_ref(),
                &method_sig.default_param_names,
                span,
            )?;

            defaults.push(Defn {
                name: Symbol::from(mangled.as_str()),
                docstring: None,
                variants: vec![DefnVariant {
                    params: method_sig.default_param_names.clone(),
                    param_annotations: vec![None; method_sig.default_param_names.len()],
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

impl TypeChecker {
    /// Try to resolve a call as a trait method.
    ///
    /// Returns Some(ResolvedCall::TraitMethod) if the callee is a trait method
    /// and the argument types resolve to a concrete impl.
    /// Returns None if the callee is not a trait method.
    pub(crate) fn try_resolve_trait_method(
        &mut self,
        callee_name: &Symbol,
        arg_types: &[Type],
        span: Span,
    ) -> Result<Option<ResolvedCall>, CranelispError> {
        // Check if this name is a trait method
        let trait_name = match self.trait_registry.get_mut().unwrap().method_to_trait.get(callee_name) {
            Some(tn) => tn.clone(),
            None => return Ok(None),
        };

        // Use hkt_param_index for dispatch argument selection (defaults to 0)
        let param_idx = self.hkt_param_idx_for_method(callee_name);
        let dispatch_arg = match arg_types.get(param_idx) {
            Some(a) => a,
            None => return Ok(None),
        };
        let resolved_arg = self.apply_subst(dispatch_arg);

        let impl_type_name = match concrete_type_name(&resolved_arg) {
            Some(tn) => tn,
            // Type is still a variable — defer resolution (batch mode will
            // catch this during monomorphisation).
            None => return Ok(None),
        };

        // Check if an impl exists — if the name IS a trait method and the
        // type IS concrete but the impl DOESN'T exist, that's a type error.
        if !self.impl_registry.get_mut().unwrap().has_impl(&trait_name, &impl_type_name) {
            return Err(CranelispError::TypeError {
                message: format!(
                    "no impl of trait {} for type {}",
                    trait_name, impl_type_name
                ),
                span,
            });
        }

        let mangled = format!(
            "{}.{}${}",
            trait_name, callee_name, impl_type_name
        );

        Ok(Some(ResolvedCall::TraitMethod {
            trait_name,
            method_name: callee_name.clone(),
            impl_type: impl_type_name,
            mangled_name: JitSymbol::from(mangled.as_str()),
        }))
    }

    /// Check if a callee name is a trait method (has constraints in its scheme).
    #[allow(dead_code)]
    pub(crate) fn is_trait_method(&self, name: &Symbol) -> bool {
        self.trait_registry.read().unwrap().method_to_trait.contains_key(name)
    }
}

// ---------------------------------------------------------------------------
// Constrained Instantiation
// ---------------------------------------------------------------------------

impl TypeChecker {
    /// Instantiate a constrained scheme, tracking the constraints on fresh vars.
    ///
    /// Returns the instantiated type. Side effect: adds constraints to
    /// `self.state.active_constraints`.
    pub(crate) fn instantiate_constrained(
        &mut self,
        scheme: &Scheme,
    ) -> Type {
        if scheme.vars.is_empty() {
            return scheme.ty.clone();
        }

        // Build mapping from old vars to fresh vars
        let mut inst_subst = cranelisp_types::Subst::new();
        let mut var_mapping = HashMap::new();
        for &var_id in &scheme.vars {
            let (fresh_ty, fresh_id) = self.fresh_var_id();
            inst_subst.insert(var_id, fresh_ty);
            var_mapping.insert(var_id, fresh_id);
        }

        // Carry constraints to fresh vars
        for (old_var, traits) in &scheme.constraints {
            if let Some(&new_var) = var_mapping.get(old_var) {
                for t in traits {
                    self.state.active_constraints.add(new_var, t.clone());
                }
            }
        }

        apply(&inst_subst, &scheme.ty)
    }
}

// ---------------------------------------------------------------------------
// Monomorphisation
// ---------------------------------------------------------------------------

impl TypeChecker {
    /// Generate a monomorphised specialization of a constrained function.
    ///
    /// Called when a constrained function is applied with concrete argument types.
    #[allow(dead_code)]
    pub(crate) fn monomorphise_call(
        &mut self,
        fn_name: &Symbol,
        arg_types: &[Type],
        call_span: Span,
    ) -> Result<Option<MonoDefn>, CranelispError> {
        // Look up the constrained fn
        let constrained_fn = match self.get_constrained_fn(fn_name) {
            Some(cf) => cf,
            None => return Ok(None),
        };

        let scheme = constrained_fn.scheme.clone();
        let defn = constrained_fn.defn.clone();

        // Instantiate, unify with arg types, and resolve concrete types
        let resolved = self.instantiate_and_resolve(&scheme, arg_types, call_span)?;

        let concrete_param_types = if let Type::Fn(pts, _) = &resolved {
            pts.clone()
        } else {
            return Ok(None);
        };

        let mangled_name = build_mangled_name(fn_name, &concrete_param_types);

        // Check constraints are satisfied
        self.verify_constraints(&scheme, call_span)?;

        // Re-check the body with concrete types and harvest resolutions
        let concrete_ret_ty = if let Type::Fn(_, ret) = &resolved {
            *ret.clone()
        } else {
            return Ok(None);
        };

        let (mut resolutions, mono_expr_types) =
            self.recheck_body_for_mono(&defn, &concrete_param_types, &concrete_ret_ty)?;

        // Add SigDispatch entries for inner constrained fn calls
        self.resolve_inner_constrained_calls(
            &defn,
            &mono_expr_types,
            &mut resolutions,
        );

        let mono_defn = MonoDefn {
            defn: Defn {
                name: Symbol::from(mangled_name.as_str()),
                docstring: defn.docstring.clone(),
                variants: vec![DefnVariant {
                    params: defn.params().to_vec(),
                    param_annotations: defn.param_annotations().to_vec(),
                    body: defn.body().clone(),
                    span: defn.span,
                }],
                visibility: defn.visibility,
                span: defn.span,
            },
            resolutions,
            expr_types: mono_expr_types,
        };

        Ok(Some(mono_defn))
    }

    /// Instantiate a scheme with fresh type variables, unify with the given
    /// argument types, and return the fully-resolved function type.
    fn instantiate_and_resolve(
        &mut self,
        scheme: &Scheme,
        arg_types: &[Type],
        call_span: Span,
    ) -> Result<Type, CranelispError> {
        let inst_type = scheme::instantiate(scheme, self.next_id.get_mut());

        if let Type::Fn(param_types, _) = &inst_type {
            for (pt, at) in param_types.iter().zip(arg_types.iter()) {
                self.unify(pt, at, call_span)?;
            }
        }

        Ok(self.apply_subst(&inst_type))
    }

    /// Verify that all trait constraints in the scheme are satisfied by
    /// the concrete types determined during unification.
    fn verify_constraints(
        &self,
        scheme: &Scheme,
        call_span: Span,
    ) -> Result<(), CranelispError> {
        for (var_id, traits) in &scheme.constraints {
            let resolved_var = apply(&self.state.subst, &Type::Var(*var_id));
            let impl_type = match concrete_type_name(&resolved_var) {
                Some(tn) => tn,
                None => continue,
            };
            for trait_name in traits {
                if !self.impl_registry.read().unwrap().has_impl(trait_name, &impl_type) {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "no impl of trait {} for type {}",
                            trait_name, impl_type
                        ),
                        span: call_span,
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
    fn recheck_body_for_mono(
        &mut self,
        defn: &Defn,
        concrete_param_types: &[Type],
        concrete_ret_ty: &Type,
    ) -> Result<(MethodResolutions, HashMap<Span, Type>), CranelispError> {
        let saved_resolutions = std::mem::take(&mut self.state.method_resolutions);
        let saved_expr_types = std::mem::take(&mut self.state.expr_types);
        let saved_pending_auto_curry = std::mem::take(&mut self.state.pending_auto_curry);

        self.check_defn_body_with_types(defn, concrete_param_types, concrete_ret_ty)?;

        // Drain pending auto-curry entries into method_resolutions before
        // capturing. During re-check, auto-curry sites push to
        // pending_auto_curry but aren't yet in method_resolutions.
        self.resolve_auto_curry();

        let resolutions = std::mem::take(&mut self.state.method_resolutions);
        let mono_expr_types: HashMap<Span, Type> = self.state.expr_types
            .iter()
            .map(|(span, ty)| (*span, apply(&self.state.subst, ty)))
            .collect();

        self.state.method_resolutions = saved_resolutions;
        self.state.expr_types = saved_expr_types;
        self.state.pending_auto_curry = saved_pending_auto_curry;

        Ok((resolutions, mono_expr_types))
    }

    /// Scan the monomorphised body for constrained fn calls (e.g. self-recursive
    /// calls) and add SigDispatch entries so the backend can find them.
    fn resolve_inner_constrained_calls(
        &self,
        defn: &Defn,
        mono_expr_types: &HashMap<Span, Type>,
        resolutions: &mut MethodResolutions,
    ) {
        let constrained_fn_names: HashSet<Symbol> = self.current_symbol_table().symbols
            .iter()
            .filter_map(|(name, entry)| {
                if let ModuleEntry::Def { kind, .. } = entry
                    && let DefKind::UserFn { constrained_fn: Some(_) } = kind.as_ref()
                {
                    return Some(name.clone());
                }
                None
            })
            .collect();
        let mut inner_calls = Vec::new();
        Self::collect_constrained_calls(defn.body(), &constrained_fn_names, &mut inner_calls);
        for (inner_fn_name, arg_spans, inner_call_span) in &inner_calls {
            if resolutions.contains_key(inner_call_span) {
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
            resolutions.insert(
                *inner_call_span,
                ResolvedCall::SigDispatch {
                    mangled_name: JitSymbol::from(inner_mangled.as_str()),
                },
            );
        }
    }

    /// Look up a constrained function by name.
    #[allow(dead_code)]
    fn get_constrained_fn(
        &self,
        name: &Symbol,
    ) -> Option<&ConstrainedFn> {
        use cranelisp_types::{DefKind, ModuleEntry};

        match self.current_symbol_table().get(name.as_ref())? {
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                DefKind::UserFn {
                    constrained_fn: Some(cf),
                } => Some(cf),
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
fn build_mangled_name(fn_name: &Symbol, param_types: &[Type]) -> String {
    let type_names: Vec<String> = param_types
        .iter()
        .filter_map(|t| concrete_type_name(t).map(|tn| tn.to_string()))
        .collect();
    format!("{}${}", fn_name, type_names.join("+"))
}

/// Extract the TypeName from a concrete (non-Var) type.
fn concrete_type_name(ty: &Type) -> Option<TypeName> {
    match ty {
        Type::Int => Some(TypeName::from("Int")),
        Type::Float => Some(TypeName::from("Float")),
        Type::Bool => Some(TypeName::from("Bool")),
        Type::String => Some(TypeName::from("String")),
        Type::ADT(name, _) => Some(name.clone()),
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
            span,
        });
    }

    let x = Expr::Var { name: param_names[0].clone(), span };
    let y = Expr::Var { name: param_names[1].clone(), span };
    let not_var = Expr::Var { name: Symbol::from("not"), span };
    let eq_var = Expr::Var { name: Symbol::from("="), span };
    let lt_var = Expr::Var { name: Symbol::from("<"), span };

    match (trait_name, method_name) {
        // != → (not (= x y))
        ("Eq", "!=") => Ok(Expr::Apply {
            callee: Box::new(not_var),
            args: vec![Expr::Apply {
                callee: Box::new(eq_var),
                args: vec![x, y],
                span,
            }],
            span,
        }),
        // > → (< y x)
        ("Ord", ">") => Ok(Expr::Apply {
            callee: Box::new(lt_var),
            args: vec![y, x],
            span,
        }),
        // <= → (not (< y x))
        ("Ord", "<=") => Ok(Expr::Apply {
            callee: Box::new(not_var),
            args: vec![Expr::Apply {
                callee: Box::new(lt_var),
                args: vec![y, x],
                span,
            }],
            span,
        }),
        // >= → (not (< x y))
        ("Ord", ">=") => Ok(Expr::Apply {
            callee: Box::new(not_var),
            args: vec![Expr::Apply {
                callee: Box::new(lt_var),
                args: vec![x, y],
                span,
            }],
            span,
        }),
        _ => Err(CranelispError::TypeError {
            message: format!(
                "no hard-coded default body for {trait_name}.{method_name}"
            ),
            span,
        }),
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
        TypeExpr::Named(name) => Type::from_name(name.as_ref())
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("unknown type: {name}"),
                span,
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
            let resolved_args: Vec<Type> = args
                .iter()
                .map(|a| resolve_trait_type_expr(a, self_type, span, var_map, next_id))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Type::ADT(name.clone(), resolved_args))
        }
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
            let name_sym = Symbol::from(name.as_ref());
            if let Some(&con_id) = con_var_map.get(&name_sym) {
                // Constructor variable application: (f a) -> TyConApp(f_id, [a])
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| resolve_type_expr_hkt(a, con_var_map, type_var_map, next_id, span))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Type::TyConApp(con_id, resolved_args))
            } else {
                // Regular ADT application: (Option Int)
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| resolve_type_expr_hkt(a, con_var_map, type_var_map, next_id, span))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Type::ADT(name.clone(), resolved_args))
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
            Ok(Type::from_name(name.as_ref()).unwrap_or_else(|| Type::ADT(name.clone(), vec![])))
        }
        TypeExpr::SelfType => {
            Err(CranelispError::TypeError {
                message: "Self is not allowed in HKT trait signatures".to_string(),
                span,
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
    }
}

/// Resolve a TypeExpr for an HKT impl method.
/// Constructor variable applications are resolved to concrete ADT applications.
/// E.g., for `(impl Functor Option ...)`, `(f a)` becomes `(Option a)`.
fn resolve_type_expr_hkt_impl(
    texpr: &cranelisp_types::TypeExpr,
    con_var_names: &[Symbol],
    target_type: &TypeName,
    type_var_map: &mut HashMap<Symbol, TypeId>,
    next_id: &mut TypeId,
    span: Span,
) -> Result<Type, CranelispError> {
    use cranelisp_types::TypeExpr;

    match texpr {
        TypeExpr::Applied(name, args) => {
            let name_sym = Symbol::from(name.as_ref());
            let resolved_name: TypeName = if con_var_names.contains(&name_sym) {
                target_type.clone()
            } else {
                name.clone()
            };
            let resolved_args: Vec<Type> = args
                .iter()
                .map(|a| resolve_type_expr_hkt_impl(a, con_var_names, target_type, type_var_map, next_id, span))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Type::ADT(resolved_name, resolved_args))
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
            Ok(Type::from_name(name.as_ref()).unwrap_or_else(|| Type::ADT(name.clone(), vec![])))
        }
        TypeExpr::SelfType => {
            Err(CranelispError::TypeError {
                message: "Self is not allowed in HKT trait signatures".to_string(),
                span,
            })
        }
        TypeExpr::FnType(params, ret) => {
            let param_tys: Vec<Type> = params
                .iter()
                .map(|p| resolve_type_expr_hkt_impl(p, con_var_names, target_type, type_var_map, next_id, span))
                .collect::<Result<Vec<_>, _>>()?;
            let ret_ty = resolve_type_expr_hkt_impl(ret, con_var_names, target_type, type_var_map, next_id, span)?;
            Ok(Type::Fn(param_tys, Box::new(ret_ty)))
        }
    }
}

/// Check if a TypeExpr uses any of the constructor variable names in Applied position.
fn type_expr_uses_con_var(texpr: &cranelisp_types::TypeExpr, con_names: &[Symbol]) -> bool {
    use cranelisp_types::TypeExpr;

    match texpr {
        TypeExpr::Applied(name, args) => {
            let name_sym = Symbol::from(name.as_ref());
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
fn find_hkt_param_index(params: &[cranelisp_types::TypeExpr], type_params: &[Symbol]) -> usize {
    for (idx, param) in params.iter().enumerate() {
        if type_expr_uses_con_var(param, type_params) {
            return idx;
        }
    }
    0 // fallback to first param
}

/// Determine the arity (number of type args) of a constructor variable in a trait declaration.
fn con_var_arity(decl: &TraitDecl, con_name: &Symbol) -> Option<usize> {
    for method in &decl.methods {
        for param in &method.params {
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
            let name_sym = Symbol::from(name.as_ref());
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

impl TypeChecker {
    /// Get the HKT param index for a method name, defaulting to 0.
    /// For mangled names like "Functor.fmap$Option", extracts the base method name first.
    fn hkt_param_idx_for_method(&self, name: &Symbol) -> usize {
        let name_str = name.as_ref();
        // Try direct lookup
        if let Some(idx) = self.find_hkt_param_index_in_registry(name_str) {
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
            if let Some(idx) = self.find_hkt_param_index_in_registry(base) {
                return idx;
            }
        }
        0
    }

    /// Walk trait declarations in the registry to find a method's hkt_param_index.
    fn find_hkt_param_index_in_registry(&self, method_name: &str) -> Option<usize> {
        for decl in self.trait_registry.read().unwrap().decls.values() {
            for method in &decl.methods {
                if method.name.as_ref() == method_name {
                    return method.hkt_param_index;
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
mod tests {
    use super::*;
    use crate::checker::TypeChecker;
    use cranelisp_types::{
        Defn, DefnVariant, FQSymbol, ModuleEntry, ModuleFullPath, Sexp, Span, TraitDecl,
        TraitImpl, TraitMethodSig, TypeExpr, Visibility,
    };

    /// Create a TypeChecker with all primitives available in the current module.
    fn tc_with_prims() -> TypeChecker {
        let mut tc = TypeChecker::new();
        tc.set_current_module(ModuleFullPath::from("test"));
        tc
    }

    /// Make a test-only trait decl (not conflicting with builtins).
    fn make_test_trait_decl() -> TraitDecl {
        TraitDecl {
            name: TraitName::from("TestTrait"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![
                TraitMethodSig {
                    name: Symbol::from("test-op"),
                    docstring: None,
                    params: vec![
                        TypeExpr::TypeVar(Symbol::from("a")),
                        TypeExpr::TypeVar(Symbol::from("a")),
                    ],
                    ret_type: TypeExpr::TypeVar(Symbol::from("a")),
                    span: Span::SYNTHETIC,
                    hkt_param_index: None,
                    default_param_names: vec![
                        Symbol::from("lhs"),
                        Symbol::from("rhs"),
                    ],
                    default_body: None,
                },
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }
    }

    // spec: 07-traits §7.1 — trait registry is empty before any declarations
    #[test]
    fn test_trait_registry_starts_empty() {
        let reg = TraitRegistry::default();
        assert!(reg.decls.is_empty());
        assert!(reg.method_to_trait.is_empty());
    }

    // spec: 07-traits §7.3 — impl registry is empty before any implementations
    #[test]
    fn test_impl_registry_starts_empty() {
        let reg = ImplRegistry::default();
        assert!(reg.impls.is_empty());
    }

    // spec: 03-types §3.6.1 — constraint detection: add and get trait constraints
    #[test]
    fn test_active_constraints_add_and_get() {
        let mut ac = ActiveConstraints::default();
        ac.add(0, TraitName::from("Num"));
        assert_eq!(ac.get(0).map(|v| v.len()), Some(1));
        assert!(ac.get(1).is_none());
    }

    // spec: 03-types §3.6.2 — constraint propagation: duplicate adds are idempotent
    #[test]
    fn test_active_constraints_add_is_idempotent() {
        let mut ac = ActiveConstraints::default();
        ac.add(0, TraitName::from("Num"));
        ac.add(0, TraitName::from("Num"));
        ac.add(0, TraitName::from("Eq"));
        ac.add(0, TraitName::from("Eq"));
        let traits = ac.get(0).unwrap();
        assert_eq!(traits.len(), 2, "duplicate adds should be ignored");
        assert_eq!(traits[0].as_ref(), "Num");
        assert_eq!(traits[1].as_ref(), "Eq");
    }

    // spec: 03-types §3.6.2 — collect constraints for specific type variable set
    #[test]
    fn test_active_constraints_collect_for_vars() {
        let mut ac = ActiveConstraints::default();
        ac.add(0, TraitName::from("Num"));
        ac.add(1, TraitName::from("Eq"));

        let collected = ac.collect_for_vars(&[0, 2]);
        assert!(collected.contains_key(&0));
        assert!(!collected.contains_key(&1));
        assert!(!collected.contains_key(&2));
    }

    // spec: 03-types §3.6.2 — constraint state can be cleared
    #[test]
    fn test_active_constraints_clear() {
        let mut ac = ActiveConstraints::default();
        ac.add(0, TraitName::from("Num"));
        ac.clear();
        assert!(ac.constraints.is_empty());
    }

    // spec: 07-traits §7.4.1 — concrete_type_name maps Int to TypeName
    #[test]
    fn test_concrete_type_name_int() {
        assert_eq!(concrete_type_name(&Type::Int), Some(TypeName::from("Int")));
    }

    // spec: 07-traits §7.4.1 — concrete_type_name maps Float to TypeName
    #[test]
    fn test_concrete_type_name_float() {
        assert_eq!(
            concrete_type_name(&Type::Float),
            Some(TypeName::from("Float"))
        );
    }

    // spec: 07-traits §7.4.1 — concrete_type_name maps Bool to TypeName
    #[test]
    fn test_concrete_type_name_bool() {
        assert_eq!(
            concrete_type_name(&Type::Bool),
            Some(TypeName::from("Bool"))
        );
    }

    // spec: 07-traits §7.4.1 — concrete_type_name maps String to TypeName
    #[test]
    fn test_concrete_type_name_string() {
        assert_eq!(
            concrete_type_name(&Type::String),
            Some(TypeName::from("String"))
        );
    }

    // spec: 07-traits §7.4.1 — concrete_type_name maps ADT to its TypeName
    #[test]
    fn test_concrete_type_name_adt() {
        assert_eq!(
            concrete_type_name(&Type::ADT(TypeName::from("Color"), vec![])),
            Some(TypeName::from("Color"))
        );
    }

    // spec: 07-traits §7.4.1 — type variable has no concrete type name
    #[test]
    fn test_concrete_type_name_var_is_none() {
        assert_eq!(concrete_type_name(&Type::Var(0)), None);
    }

    // spec: 07-traits §7.1 — deftrait registers trait and methods in symbol table
    #[test]
    fn test_register_trait_decl() {
        let mut tc = TypeChecker::new();
        let decl = make_test_trait_decl();
        tc.register_trait_decl(&decl).unwrap();

        // Trait should be in the registry
        assert!(tc.trait_registry.read().unwrap().decls.contains_key(&TraitName::from("TestTrait")));
        // Method should be reverse-mapped
        assert_eq!(
            tc.trait_registry.read().unwrap().method_to_trait.get(&Symbol::from("test-op")),
            Some(&TraitName::from("TestTrait"))
        );
        // Trait should be in symbol table
        assert!(matches!(
            tc.symbol_table().get("TestTrait"),
            Some(ModuleEntry::TraitDecl { .. })
        ));
    }

    // spec: 07-traits §7.1 — duplicate trait declaration is an error
    #[test]
    fn test_register_duplicate_trait_fails() {
        let mut tc = TypeChecker::new();
        let decl = make_test_trait_decl();
        tc.register_trait_decl(&decl).unwrap();
        let err = tc.register_trait_decl(&decl).unwrap_err();
        assert!(err.message().contains("already defined"));
    }

    // spec: 03-types §3.4.1 — trait method scheme carries trait constraint
    #[test]
    fn test_trait_method_has_constrained_scheme() {
        let mut tc = TypeChecker::new();
        let decl = make_test_trait_decl();
        tc.register_trait_decl(&decl).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("test-op") {
            assert_eq!(scheme.vars.len(), 1, "test-op should have 1 quantified var");
            assert!(
                !scheme.constraints.is_empty(),
                "test-op should have TestTrait constraint"
            );
            let var_id = scheme.vars[0];
            let traits = scheme.constraints.get(&var_id).unwrap();
            assert_eq!(traits.len(), 1);
            assert_eq!(traits[0].as_ref(), "TestTrait");
        } else {
            panic!("test-op should be registered");
        }
    }

    // spec: 07-traits §7.3.1 — register concrete trait implementation
    #[test]
    fn test_register_trait_impl() {
        let mut tc = tc_with_prims();
        let decl = make_test_trait_decl();
        tc.register_trait_decl(&decl).unwrap();

        let impl_ = TraitImpl {
            trait_name: TraitName::from("TestTrait"),
            target_type: TypeName::from("Int"),
            type_args: vec![],
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("test-op"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("lhs"), Symbol::from("rhs")],
                    param_annotations: vec![None, None],
                    body: cranelisp_types::Expr::Apply {
                        callee: Box::new(cranelisp_types::Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: Span::SYNTHETIC,
                        }),
                        args: vec![
                            cranelisp_types::Expr::Var { name: Symbol::from("lhs"), span: Span::SYNTHETIC },
                            cranelisp_types::Expr::Var { name: Symbol::from("rhs"), span: Span::SYNTHETIC },
                        ],
                        span: Span::SYNTHETIC,
                    },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        };
        tc.register_trait_impl(&impl_).unwrap();

        assert!(tc
            .impl_registry
            .read().unwrap()
            .has_impl(&TraitName::from("TestTrait"), &TypeName::from("Int")));
        assert!(!tc
            .impl_registry
            .read().unwrap()
            .has_impl(&TraitName::from("TestTrait"), &TypeName::from("Bool")));
    }

    // spec: 07-traits §7.4.1 — resolve trait method to concrete impl mangled name
    #[test]
    fn test_try_resolve_trait_method_success() {
        let mut tc = tc_with_prims();
        let decl = make_test_trait_decl();
        tc.register_trait_decl(&decl).unwrap();

        let impl_ = TraitImpl {
            trait_name: TraitName::from("TestTrait"),
            target_type: TypeName::from("Int"),
            type_args: vec![],
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("test-op"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("lhs"), Symbol::from("rhs")],
                    param_annotations: vec![None, None],
                    body: cranelisp_types::Expr::Apply {
                        callee: Box::new(cranelisp_types::Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: Span::SYNTHETIC,
                        }),
                        args: vec![
                            cranelisp_types::Expr::Var { name: Symbol::from("lhs"), span: Span::SYNTHETIC },
                            cranelisp_types::Expr::Var { name: Symbol::from("rhs"), span: Span::SYNTHETIC },
                        ],
                        span: Span::SYNTHETIC,
                    },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        };
        tc.register_trait_impl(&impl_).unwrap();

        let result = tc.try_resolve_trait_method(
            &Symbol::from("test-op"),
            &[Type::Int, Type::Int],
            Span::SYNTHETIC,
        );
        let result = result.expect("should not error");
        assert!(result.is_some());
        if let Some(ResolvedCall::TraitMethod {
            trait_name,
            method_name,
            impl_type,
            mangled_name,
        }) = result
        {
            assert_eq!(trait_name.as_ref(), "TestTrait");
            assert_eq!(method_name.as_ref(), "test-op");
            assert_eq!(impl_type.as_ref(), "Int");
            assert_eq!(mangled_name.as_ref(), "TestTrait.test-op$Int");
        }
    }

    // spec: 07-traits §7.4.3 — no matching impl returns TypeError
    #[test]
    fn test_try_resolve_trait_method_no_impl() {
        let mut tc = TypeChecker::new();
        let decl = make_test_trait_decl();
        tc.register_trait_decl(&decl).unwrap();
        // No impl registered for Bool under TestTrait

        let result = tc.try_resolve_trait_method(
            &Symbol::from("test-op"),
            &[Type::Bool, Type::Bool],
            Span::SYNTHETIC,
        );
        assert!(result.is_err());
        let err = result.unwrap_err();
        match err {
            CranelispError::TypeError { message, .. } => {
                assert!(message.contains("no impl of trait TestTrait for type Bool"), "{message}");
            }
            other => panic!("expected TypeError, got {other:?}"),
        }
    }

    // spec: 07-traits §7.4.1 — non-trait-method name returns None
    #[test]
    fn test_try_resolve_non_trait_method() {
        let mut tc = TypeChecker::new();
        let result = tc.try_resolve_trait_method(
            &Symbol::from("add-i64"),
            &[Type::Int, Type::Int],
            Span::SYNTHETIC,
        );
        assert!(matches!(result, Ok(None)));
    }

    // spec: 07-traits §7.4.3 — impl registry tracks trait-type pairs
    #[test]
    fn test_impl_registry_has_impl() {
        let mut reg = ImplRegistry::default();
        reg.impls
            .entry(TraitName::from("Num"))
            .or_default()
            .insert(
                TypeName::from("Int"),
                RegisteredImpl {
                    trait_name: TraitName::from("Num"),
                    impl_type: TypeName::from("Int"),
                    method_primitives: HashMap::new(),
                },
            );
        assert!(reg.has_impl(&TraitName::from("Num"), &TypeName::from("Int")));
        assert!(!reg.has_impl(&TraitName::from("Num"), &TypeName::from("Bool")));
    }

    // spec: 07-traits §7.1 — is_trait_method distinguishes trait methods from plain fns
    #[test]
    fn test_is_trait_method() {
        let mut tc = TypeChecker::new();
        let decl = make_test_trait_decl();
        tc.register_trait_decl(&decl).unwrap();

        assert!(tc.is_trait_method(&Symbol::from("test-op")));
        assert!(!tc.is_trait_method(&Symbol::from("add-i64")));
    }

    // spec: 07-traits §7.1.1 — self type resolves to implementing type
    #[test]
    fn test_resolve_trait_type_expr_self() {
        let mut var_map = HashMap::new();
        let mut next_id: TypeId = 100;
        let result = resolve_trait_type_expr(
            &TypeExpr::SelfType,
            &Type::Int,
            Span::SYNTHETIC,
            &mut var_map,
            &mut next_id,
        )
        .unwrap();
        assert_eq!(result, Type::Int);
    }

    // spec: 07-traits §7.1.4 — named type in trait signature resolves to concrete type
    #[test]
    fn test_resolve_trait_type_expr_named() {
        let mut var_map = HashMap::new();
        let mut next_id: TypeId = 100;
        let result = resolve_trait_type_expr(
            &TypeExpr::Named(TypeName::from("Bool")),
            &Type::Int,
            Span::SYNTHETIC,
            &mut var_map,
            &mut next_id,
        )
        .unwrap();
        assert_eq!(result, Type::Bool);
    }

    // spec: 07-traits §7.1.4 — type variable in trait sig gets fresh var
    #[test]
    fn test_resolve_trait_type_expr_type_var_gets_fresh_var() {
        let mut var_map = HashMap::new();
        let mut next_id: TypeId = 100;
        let result = resolve_trait_type_expr(
            &TypeExpr::TypeVar(Symbol::from("b")),
            &Type::Float,
            Span::SYNTHETIC,
            &mut var_map,
            &mut next_id,
        )
        .unwrap();
        assert!(matches!(result, Type::Var(_)));
        assert_ne!(result, Type::Float);
    }

    // spec: 07-traits §7.1.4 — pre-seeded type var reuses existing mapping
    #[test]
    fn test_resolve_trait_type_expr_type_var_preseeded() {
        let mut var_map = HashMap::new();
        var_map.insert(Symbol::from("a"), Type::Int);
        let mut next_id: TypeId = 100;
        let result = resolve_trait_type_expr(
            &TypeExpr::TypeVar(Symbol::from("a")),
            &Type::Float,
            Span::SYNTHETIC,
            &mut var_map,
            &mut next_id,
        )
        .unwrap();
        assert_eq!(result, Type::Int);
    }

    // spec: 07-traits §7.1.4 — same type variable name reuses same var across calls
    #[test]
    fn test_resolve_trait_type_expr_same_var_reused() {
        let mut var_map = HashMap::new();
        let mut next_id: TypeId = 100;
        let r1 = resolve_trait_type_expr(
            &TypeExpr::TypeVar(Symbol::from("b")),
            &Type::Int,
            Span::SYNTHETIC,
            &mut var_map,
            &mut next_id,
        )
        .unwrap();
        let r2 = resolve_trait_type_expr(
            &TypeExpr::TypeVar(Symbol::from("b")),
            &Type::Int,
            Span::SYNTHETIC,
            &mut var_map,
            &mut next_id,
        )
        .unwrap();
        assert_eq!(r1, r2);
    }

    // spec: pipeline-orchestration §5 — no core traits at startup (Decision 17 eliminated)
    #[test]
    fn test_no_core_traits_at_startup() {
        let tc = TypeChecker::new();
        // Traits come from prelude .cl files, NOT compiler builtins
        assert!(tc.trait_registry.read().unwrap().decls.is_empty(),
            "no traits should be registered at startup");
        assert!(tc.impl_registry.read().unwrap().impls.is_empty(),
            "no impls should be registered at startup");
    }

    // spec: pipeline-orchestration §5 — operator symbols NOT in symbol table at startup
    #[test]
    fn test_no_operators_at_startup() {
        let tc = TypeChecker::new();
        let ops = ["+", "-", "*", "/", "=", "!=", "<", ">", "<=", ">="];
        for op in ops {
            assert!(
                tc.symbol_table().get(op).is_none(),
                "operator {op} should NOT be in symbol table at startup"
            );
        }
    }

    // spec: 07-traits §7.4.2 — trait method resolution works with inline trait definitions
    #[test]
    fn test_try_resolve_with_inline_trait() {
        let mut tc = tc_with_prims();
        // Register Num trait inline (as prelude would)
        let num_decl = TraitDecl {
            name: TraitName::from("Num"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("+"),
                docstring: None,
                params: vec![
                    TypeExpr::TypeVar(Symbol::from("a")),
                    TypeExpr::TypeVar(Symbol::from("a")),
                ],
                ret_type: TypeExpr::TypeVar(Symbol::from("a")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        tc.register_trait_decl(&num_decl).unwrap();

        // Register impl Num for Int
        let impl_ = TraitImpl {
            trait_name: TraitName::from("Num"),
            target_type: TypeName::from("Int"),
            type_args: vec![],
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("+"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("x"), Symbol::from("y")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: Span::SYNTHETIC,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: Span::SYNTHETIC },
                            Expr::Var { name: Symbol::from("y"), span: Span::SYNTHETIC },
                        ],
                        span: Span::SYNTHETIC,
                    },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        };
        tc.register_trait_impl(&impl_).unwrap();
        tc.clear_transient_state();

        let result = tc.try_resolve_trait_method(
            &Symbol::from("+"),
            &[Type::Int, Type::Int],
            Span::SYNTHETIC,
        ).expect("should not error");
        assert!(result.is_some());
        if let Some(ResolvedCall::TraitMethod { mangled_name, .. }) = result {
            assert_eq!(mangled_name.as_ref(), "Num.+$Int");
        }
    }

    // -----------------------------------------------------------------------
    // Default method body generation tests
    // -----------------------------------------------------------------------

    use cranelisp_types::Expr;

    /// Helper: check that an expr is `Apply { callee: Var(name), .. }`
    fn assert_apply_callee(expr: &Expr, expected_name: &str) {
        if let Expr::Apply { callee, .. } = expr {
            if let Expr::Var { name, .. } = callee.as_ref() {
                assert_eq!(name.as_ref(), expected_name);
                return;
            }
        }
        panic!("expected Apply with callee Var({expected_name}), got {expr:?}");
    }

    /// Helper: extract Apply args
    fn apply_args(expr: &Expr) -> &[Expr] {
        if let Expr::Apply { args, .. } = expr {
            args.as_slice()
        } else {
            panic!("expected Apply, got {expr:?}");
        }
    }

    /// Helper: assert Var with given name
    fn assert_var(expr: &Expr, expected: &str) {
        if let Expr::Var { name, .. } = expr {
            assert_eq!(name.as_ref(), expected);
        } else {
            panic!("expected Var({expected}), got {expr:?}");
        }
    }

    // spec: 07-traits §7.1.5 — default method body: != is (not (= x y))
    #[test]
    fn test_build_default_body_neq() {
        // != → (not (= x y))
        let body = build_default_body(
            "Eq", "!=",
            &[Symbol::from("x"), Symbol::from("y")],
            Span::SYNTHETIC,
        ).unwrap();

        assert_apply_callee(&body, "not");
        let not_args = apply_args(&body);
        assert_eq!(not_args.len(), 1);
        assert_apply_callee(&not_args[0], "=");
        let eq_args = apply_args(&not_args[0]);
        assert_eq!(eq_args.len(), 2);
        assert_var(&eq_args[0], "x");
        assert_var(&eq_args[1], "y");
    }

    // spec: 07-traits §7.1.5 — default method body: > is (< y x)
    #[test]
    fn test_build_default_body_gt() {
        // > → (< y x)
        let body = build_default_body(
            "Ord", ">",
            &[Symbol::from("x"), Symbol::from("y")],
            Span::SYNTHETIC,
        ).unwrap();

        assert_apply_callee(&body, "<");
        let args = apply_args(&body);
        assert_eq!(args.len(), 2);
        assert_var(&args[0], "y");
        assert_var(&args[1], "x");
    }

    // spec: 07-traits §7.1.5 — default method body: <= is (not (< y x))
    #[test]
    fn test_build_default_body_le() {
        // <= → (not (< y x))
        let body = build_default_body(
            "Ord", "<=",
            &[Symbol::from("x"), Symbol::from("y")],
            Span::SYNTHETIC,
        ).unwrap();

        assert_apply_callee(&body, "not");
        let not_args = apply_args(&body);
        assert_eq!(not_args.len(), 1);
        assert_apply_callee(&not_args[0], "<");
        let lt_args = apply_args(&not_args[0]);
        assert_eq!(lt_args.len(), 2);
        assert_var(&lt_args[0], "y");
        assert_var(&lt_args[1], "x");
    }

    // spec: 07-traits §7.1.5 — default method body: >= is (not (< x y))
    #[test]
    fn test_build_default_body_ge() {
        // >= → (not (< x y))
        let body = build_default_body(
            "Ord", ">=",
            &[Symbol::from("x"), Symbol::from("y")],
            Span::SYNTHETIC,
        ).unwrap();

        assert_apply_callee(&body, "not");
        let not_args = apply_args(&body);
        assert_eq!(not_args.len(), 1);
        assert_apply_callee(&not_args[0], "<");
        let lt_args = apply_args(&not_args[0]);
        assert_eq!(lt_args.len(), 2);
        assert_var(&lt_args[0], "x");
        assert_var(&lt_args[1], "y");
    }

    // spec: 07-traits §7.1.5 — unknown trait/method has no default body
    #[test]
    fn test_build_default_body_unknown_method_errors() {
        let result = build_default_body(
            "Unknown", "foo",
            &[Symbol::from("x"), Symbol::from("y")],
            Span::SYNTHETIC,
        );
        assert!(result.is_err());
    }

    // spec: 07-traits §7.1.5 — default body with wrong param count errors
    #[test]
    fn test_build_default_body_wrong_param_count_errors() {
        let result = build_default_body(
            "Eq", "!=",
            &[Symbol::from("x")],
            Span::SYNTHETIC,
        );
        assert!(result.is_err());
    }

    // spec: 07-traits §7.1.5 — generate_default_methods synthesizes missing impl methods
    #[test]
    fn test_generate_default_methods_produces_real_bodies() {
        // Register Eq trait inline and create an impl with only "=" provided.
        // The "!=" default should be generated with a real body.
        let mut tc = TypeChecker::new();

        // Register Eq trait inline (as prelude would)
        let eq_decl = TraitDecl {
            name: TraitName::from("Eq"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![
                TraitMethodSig {
                    name: Symbol::from("="),
                    docstring: None,
                    params: vec![
                        TypeExpr::TypeVar(Symbol::from("a")),
                        TypeExpr::TypeVar(Symbol::from("a")),
                    ],
                    ret_type: TypeExpr::Named(TypeName::from("Bool")),
                    span: Span::SYNTHETIC,
                    hkt_param_index: None,
                    default_param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
                    default_body: None,
                },
                TraitMethodSig {
                    name: Symbol::from("!="),
                    docstring: None,
                    params: vec![
                        TypeExpr::TypeVar(Symbol::from("a")),
                        TypeExpr::TypeVar(Symbol::from("a")),
                    ],
                    ret_type: TypeExpr::Named(TypeName::from("Bool")),
                    span: Span::SYNTHETIC,
                    hkt_param_index: None,
                    default_param_names: vec![Symbol::from("x"), Symbol::from("y")],
                    default_body: Some(Sexp::Symbol("default".to_string(), Span::SYNTHETIC)),
                },
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        tc.register_trait_decl(&eq_decl).unwrap();

        let impl_ = TraitImpl {
            trait_name: TraitName::from("Eq"),
            target_type: TypeName::from("Int"),
            type_args: vec![],
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("="),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("lhs"), Symbol::from("rhs")],
                    param_annotations: vec![None, None],
                    body: Expr::BoolLit { value: true, span: Span::SYNTHETIC },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        };

        let decl = tc.trait_registry.read().unwrap().decls
            .get(&TraitName::from("Eq"))
            .unwrap()
            .clone();
        let defaults = tc.generate_default_methods(&decl, &impl_).unwrap();

        assert_eq!(defaults.len(), 1, "should generate 1 default method (!=)");
        let neq = &defaults[0];
        assert_eq!(neq.name.as_ref(), "Eq.!=$Int");
        assert_eq!(neq.params().len(), 2);

        // Body should be (not (= x y)), not IntLit 0
        assert_apply_callee(neq.body(), "not");
    }
}
