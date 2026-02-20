use std::collections::HashMap;

use crate::ast::*;
use crate::error::{CranelispError, Span};
use crate::types::*;

use super::has_type_var;
use super::{MethodResolutions, ResolvedCall, TypeChecker};

impl TypeChecker {
    /// Register a trait declaration (public, for REPL use).
    pub fn register_trait_public(&mut self, decl: &TraitDecl) {
        self.register_trait(decl);
    }

    /// Validate a user-defined trait impl (public, for REPL use).
    pub fn validate_impl_public(&self, ti: &TraitImpl) -> Result<(), CranelispError> {
        self.validate_impl(ti)
    }

    /// Register a validated trait impl (public, for REPL use).
    pub fn register_impl(&mut self, ti: &TraitImpl) {
        let current = self.current_module_path.clone();
        let cm = self
            .modules
            .entry(current.clone())
            .or_insert_with(|| crate::module::CompiledModule::new(current));
        cm.impls.push(ti.clone());
    }

    /// Register a trait declaration and add its methods to the type env as polymorphic functions.
    pub(crate) fn register_trait(&mut self, decl: &TraitDecl) {
        self.register_trait_internal(decl, true);
    }

    /// Register a trait declaration. If `add_to_env` is true, methods are added to the type env.
    /// Operator traits (Num, Eq, Ord) use `add_to_env: false` for word-based names.
    fn register_trait_internal(&mut self, decl: &TraitDecl, add_to_env: bool) {
        // Write TraitDecl entry into current module's CompiledModule
        {
            let current = self.current_module_path.clone();
            let cm = self
                .modules
                .entry(current.clone())
                .or_insert_with(|| crate::module::CompiledModule::new(current));
            cm.symbols.insert(
                crate::names::Symbol::from(decl.name.as_str()),
                crate::module::ModuleEntry::TraitDecl {
                    decl: decl.clone(),
                    visibility: decl.visibility,
                    sexp: None,
                },
            );
        }

        // If trait has type_params (HKT), use the HKT registration path
        if !decl.type_params.is_empty() {
            self.register_hkt_trait(decl, add_to_env);
            return;
        }

        for method in &decl.methods {
            if add_to_env {
                // Register the method as a polymorphic function: forall a. <sig with self=a>
                let a = self.fresh_var();
                let a_id = match &a {
                    Type::Var(id) => *id,
                    _ => unreachable!(),
                };
                let param_tys: Vec<Type> = method
                    .params
                    .iter()
                    .map(|p| self.resolve_type_expr(p, &a))
                    .collect();
                let ret_ty = self.resolve_type_expr(&method.ret_type, &a);
                self.insert_def_checked(
                    method.name.clone(),
                    Scheme {
                        vars: vec![a_id],
                        constraints: HashMap::new(),
                        ty: Type::Fn(param_tys, Box::new(ret_ty)),
                    },
                );
            }
        }
    }

    /// Register an HKT trait where type_params are type constructor variables.
    /// E.g., `(deftrait (Functor f) (fmap [(Fn [a] b) (f a)] (f b)))`
    fn register_hkt_trait(&mut self, decl: &TraitDecl, add_to_env: bool) {
        // Create fresh type var IDs for each constructor param
        let mut con_var_map: HashMap<String, TypeId> = HashMap::new();
        for param_name in &decl.type_params {
            let var = self.fresh_var();
            if let Type::Var(id) = var {
                con_var_map.insert(param_name.clone(), id);
            }
        }

        // Build a modified decl with hkt_param_index set on each method,
        // then overwrite the TraitDecl entry in CompiledModule.
        let mut modified_decl = decl.clone();

        for (mi, method) in decl.methods.iter().enumerate() {
            // Determine which param index carries the type constructor
            let param_idx = self.find_hkt_param_index(&method.params, &decl.type_params);
            modified_decl.methods[mi].hkt_param_index = Some(param_idx);

            if add_to_env {
                // Create fresh regular type vars for any type variables used in the signature
                // that are NOT constructor params
                let mut type_var_map: HashMap<String, TypeId> = HashMap::new();

                let param_tys: Vec<Type> = method
                    .params
                    .iter()
                    .map(|p| self.resolve_type_expr_hkt(p, &con_var_map, &mut type_var_map))
                    .collect();
                let ret_ty =
                    self.resolve_type_expr_hkt(&method.ret_type, &con_var_map, &mut type_var_map);

                // Collect all var IDs (constructor + regular)
                let mut all_vars: Vec<TypeId> = con_var_map.values().copied().collect();
                all_vars.extend(type_var_map.values());
                all_vars.sort();
                all_vars.dedup();

                // Add trait constraint to constructor vars
                let mut constraints: HashMap<TypeId, Vec<String>> = HashMap::new();
                for &con_id in con_var_map.values() {
                    constraints.insert(con_id, vec![decl.name.clone()]);
                }

                self.insert_def_checked(
                    method.name.clone(),
                    Scheme {
                        vars: all_vars,
                        constraints,
                        ty: Type::Fn(param_tys.clone(), Box::new(ret_ty)),
                    },
                );
            }
        }

        // Overwrite the TraitDecl in CompiledModule with hkt_param_index set
        {
            let current = self.current_module_path.clone();
            let cm = self
                .modules
                .entry(current.clone())
                .or_insert_with(|| crate::module::CompiledModule::new(current));
            cm.symbols.insert(
                crate::names::Symbol::from(decl.name.as_str()),
                crate::module::ModuleEntry::TraitDecl {
                    decl: modified_decl,
                    visibility: decl.visibility,
                    sexp: None,
                },
            );
        }
    }

    /// Resolve a TypeExpr in HKT context, producing TyConApp for constructor variable applications.
    fn resolve_type_expr_hkt(
        &mut self,
        texpr: &TypeExpr,
        con_var_map: &HashMap<String, TypeId>,
        type_var_map: &mut HashMap<String, TypeId>,
    ) -> Type {
        match texpr {
            TypeExpr::Applied(name, args) => {
                if let Some(&con_id) = con_var_map.get(name) {
                    // This is a constructor variable application: (f a) → TyConApp(f_id, [a])
                    let resolved_args: Vec<Type> = args
                        .iter()
                        .map(|a| self.resolve_type_expr_hkt(a, con_var_map, type_var_map))
                        .collect();
                    Type::TyConApp(con_id, resolved_args)
                } else {
                    // Regular ADT application: (Option Int)
                    let resolved_args: Vec<Type> = args
                        .iter()
                        .map(|a| self.resolve_type_expr_hkt(a, con_var_map, type_var_map))
                        .collect();
                    Type::ADT(name.clone(), resolved_args)
                }
            }
            TypeExpr::TypeVar(name) => {
                if let Some(&con_id) = con_var_map.get(name) {
                    // Bare constructor variable used as a type — shouldn't happen in well-formed sigs
                    Type::Var(con_id)
                } else if let Some(&id) = type_var_map.get(name) {
                    Type::Var(id)
                } else {
                    let var = self.fresh_var();
                    if let Type::Var(id) = var {
                        type_var_map.insert(name.clone(), id);
                        Type::Var(id)
                    } else {
                        unreachable!()
                    }
                }
            }
            TypeExpr::Named(name) => match name.as_str() {
                "Int" => Type::Int,
                "Bool" => Type::Bool,
                "String" => Type::String,
                "Float" => Type::Float,
                _ => {
                    if self.resolve_type_def_via_modules(name).is_some() {
                        Type::ADT(name.clone(), vec![])
                    } else {
                        panic!("unknown type in HKT trait sig: {}", name)
                    }
                }
            },
            TypeExpr::SelfType => {
                // SelfType doesn't apply in HKT traits (they use explicit constructor vars)
                panic!("SelfType in HKT trait signature")
            }
            TypeExpr::FnType(params, ret) => {
                let param_tys: Vec<Type> = params
                    .iter()
                    .map(|p| self.resolve_type_expr_hkt(p, con_var_map, type_var_map))
                    .collect();
                let ret_ty = self.resolve_type_expr_hkt(ret, con_var_map, type_var_map);
                Type::Fn(param_tys, Box::new(ret_ty))
            }
        }
    }

    /// Find the first parameter index that uses a constructor variable in Applied position.
    fn find_hkt_param_index(&self, params: &[TypeExpr], type_params: &[String]) -> usize {
        for (idx, param) in params.iter().enumerate() {
            if self.type_expr_uses_con_var(param, type_params) {
                return idx;
            }
        }
        0 // fallback to first param
    }

    /// Check if a TypeExpr uses any of the constructor variable names in Applied position.
    fn type_expr_uses_con_var(&self, texpr: &TypeExpr, con_names: &[String]) -> bool {
        match texpr {
            TypeExpr::Applied(name, _) => con_names.contains(name),
            TypeExpr::FnType(params, ret) => {
                params
                    .iter()
                    .any(|p| self.type_expr_uses_con_var(p, con_names))
                    || self.type_expr_uses_con_var(ret, con_names)
            }
            _ => false,
        }
    }

    /// Get the HKT param index for a method name, defaulting to 0.
    /// For mangled names like "fmap$Option", extracts the base method name first.
    /// Walks module TraitDecl entries to find the method's hkt_param_index.
    pub(crate) fn hkt_param_idx_for_method(&self, name: &str) -> usize {
        // Try direct lookup
        if let Some(idx) = self.find_hkt_param_index_in_modules(name) {
            return idx;
        }
        // For mangled names like "fmap$Option", try the base name
        if let Some(dollar_pos) = name.find('$') {
            let base = &name[..dollar_pos];
            if let Some(idx) = self.find_hkt_param_index_in_modules(base) {
                return idx;
            }
        }
        0
    }

    /// Walk all module TraitDecl entries to find a method's hkt_param_index.
    fn find_hkt_param_index_in_modules(&self, method_name: &str) -> Option<usize> {
        for cm in self.modules.values() {
            for entry in cm.symbols.values() {
                if let crate::module::ModuleEntry::TraitDecl { decl, .. } = entry {
                    for method in &decl.methods {
                        if method.name == method_name {
                            return method.hkt_param_index;
                        }
                    }
                }
            }
        }
        None
    }

    /// Build the self type for an impl target.
    /// For concrete: `(impl Display (Option Int) ...)` → `Type::ADT("Option", [Type::Int])`
    /// For polymorphic: `(impl Display (Option :Display a) ...)` → `Type::ADT("Option", [fresh_var])`
    /// For bare: `(impl Display Color ...)` → `Type::ADT("Color", [])` or primitive type
    pub fn resolve_impl_self_type(&mut self, ti: &TraitImpl) -> Result<Type, CranelispError> {
        if ti.type_args.is_empty() {
            // Bare type name: Int, Bool, Color, Option, etc.
            return self.name_to_type(&ti.target_type, ti.span);
        }

        // Has type args: (Option Int) or (Option :Display a)
        let td = self
            .resolve_type_def_via_modules(&ti.target_type)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("unknown type: {}", ti.target_type),
                span: ti.span,
            })?;

        if ti.type_args.len() != td.type_params.len() {
            return Err(CranelispError::TypeError {
                message: format!(
                    "{} expects {} type parameters, got {}",
                    ti.target_type,
                    td.type_params.len(),
                    ti.type_args.len()
                ),
                span: ti.span,
            });
        }

        let mut arg_types = Vec::new();
        for arg_name in &ti.type_args {
            if arg_name.starts_with(|c: char| c.is_uppercase()) {
                // Concrete type name
                arg_types.push(self.name_to_type(arg_name, ti.span)?);
            } else {
                // Type variable — create a fresh var
                let var = self.fresh_var();
                // Apply explicit constraints if any
                if let Type::Var(id) = &var {
                    for (cvar, trait_name) in &ti.type_constraints {
                        if cvar == arg_name {
                            self.var_constraints
                                .entry(*id)
                                .or_default()
                                .insert(trait_name.clone());
                        }
                    }
                }
                arg_types.push(var);
            }
        }

        Ok(Type::ADT(ti.target_type.clone(), arg_types))
    }

    /// Convert a type name string to a Type.
    pub(crate) fn name_to_type(&mut self, name: &str, span: Span) -> Result<Type, CranelispError> {
        match name {
            "Int" => Ok(Type::Int),
            "Bool" => Ok(Type::Bool),
            "String" => Ok(Type::String),
            "Float" => Ok(Type::Float),
            _ => {
                let param_count = self.resolve_type_def_via_modules(name).map(|td| td.type_params.len());
                match param_count {
                    Some(0) => Ok(Type::ADT(name.to_string(), vec![])),
                    Some(n) => {
                        let args: Vec<Type> = (0..n).map(|_| self.fresh_var()).collect();
                        Ok(Type::ADT(name.to_string(), args))
                    }
                    None => Err(CranelispError::TypeError {
                        message: format!("unknown type: {}", name),
                        span,
                    }),
                }
            }
        }
    }

    /// Validate a user-defined trait impl against its trait declaration.
    pub(crate) fn validate_impl(&self, ti: &TraitImpl) -> Result<(), CranelispError> {
        let decl = self
            .find_trait_decl(&ti.trait_name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("unknown trait: {}", ti.trait_name),
                span: ti.span,
            })?;

        // HKT arity validation: if the trait has type constructor params,
        // verify the impl target's arity matches the expected constructor arity.
        if !decl.type_params.is_empty() {
            for con_name in &decl.type_params {
                if let Some(expected_arity) = Self::con_var_arity(decl, con_name) {
                    // The impl target must be a known type constructor with matching arity
                    if let Some(td) = self.resolve_type_def_via_modules(&ti.target_type) {
                        if td.type_params.len() != expected_arity {
                            return Err(CranelispError::TypeError {
                                message: format!(
                                    "{} has {} type parameters, but trait {} expects a constructor with arity {}",
                                    ti.target_type,
                                    td.type_params.len(),
                                    ti.trait_name,
                                    expected_arity
                                ),
                                span: ti.span,
                            });
                        }
                    } else if expected_arity > 0 {
                        // Primitive types (Int, Bool, etc.) have arity 0
                        match ti.target_type.as_str() {
                            "Int" | "Bool" | "String" | "Float" => {
                                return Err(CranelispError::TypeError {
                                    message: format!(
                                        "{} is not a type constructor (trait {} expects arity {})",
                                        ti.target_type, ti.trait_name, expected_arity
                                    ),
                                    span: ti.span,
                                });
                            }
                            _ => {}
                        }
                    }
                }
            }
        }

        // Validate type arg count if target is a known ADT with type params
        if !ti.type_args.is_empty() {
            if let Some(td) = self.resolve_type_def_via_modules(&ti.target_type) {
                if ti.type_args.len() != td.type_params.len() {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "{} expects {} type parameters, got {}",
                            ti.target_type,
                            td.type_params.len(),
                            ti.type_args.len()
                        ),
                        span: ti.span,
                    });
                }
            }
        }

        // Check that all required methods are implemented
        for method_sig in &decl.methods {
            if !ti.methods.iter().any(|m| m.name == method_sig.name) {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "missing method '{}' in impl {} for {}",
                        method_sig.name, ti.trait_name, ti.target_type
                    ),
                    span: ti.span,
                });
            }
        }

        // Check param count matches
        for method_sig in &decl.methods {
            if let Some(impl_method) = ti.methods.iter().find(|m| m.name == method_sig.name) {
                if impl_method.params.len() != method_sig.params.len() {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "method '{}' expects {} params, impl has {}",
                            method_sig.name,
                            method_sig.params.len(),
                            impl_method.params.len()
                        ),
                        span: impl_method.span,
                    });
                }
            }
        }

        Ok(())
    }

    /// Determine the arity (number of type args) of a constructor variable in a trait declaration.
    /// Scans method signatures for Applied uses of the constructor param name.
    fn con_var_arity(decl: &TraitDecl, con_name: &str) -> Option<usize> {
        for method in &decl.methods {
            for param in &method.params {
                if let Some(arity) = Self::find_applied_arity(param, con_name) {
                    return Some(arity);
                }
            }
            if let Some(arity) = Self::find_applied_arity(&method.ret_type, con_name) {
                return Some(arity);
            }
        }
        None
    }

    /// Find the arity of a constructor variable name in a TypeExpr tree.
    fn find_applied_arity(texpr: &TypeExpr, con_name: &str) -> Option<usize> {
        match texpr {
            TypeExpr::Applied(name, args) if name == con_name => Some(args.len()),
            TypeExpr::FnType(params, ret) => {
                for p in params {
                    if let Some(a) = Self::find_applied_arity(p, con_name) {
                        return Some(a);
                    }
                }
                Self::find_applied_arity(ret, con_name)
            }
            TypeExpr::Applied(_, args) => {
                for a in args {
                    if let Some(arity) = Self::find_applied_arity(a, con_name) {
                        return Some(arity);
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Find a matching impl for a concrete type and trait, returning the mangled target name.
    /// Checks concrete ADT impls first (e.g., `(Option Int)`), then bare impls (e.g., `Option` or `Color`),
    /// then polymorphic impls (e.g., `(Option :Display a)`).
    fn find_impl_for_type(
        &self,
        trait_name: &str,
        method_name: &str,
        concrete_type: &Type,
    ) -> Option<String> {
        let (base_name, concrete_args) = match concrete_type {
            Type::Int => ("Int", vec![]),
            Type::Bool => ("Bool", vec![]),
            Type::String => ("String", vec![]),
            Type::Float => ("Float", vec![]),
            Type::ADT(name, args) => (name.as_str(), args.clone()),
            _ => return None,
        };

        // For ADT types with concrete args, look for an exact concrete impl first
        if !concrete_args.is_empty() && concrete_args.iter().all(|a| !has_type_var(a)) {
            for ui in self.all_impls() {
                if ui.trait_name != trait_name || ui.target_type != base_name {
                    continue;
                }
                if !ui.methods.iter().any(|m| m.name == method_name) {
                    continue;
                }
                if ui.type_args.len() == concrete_args.len() {
                    // Check if all type args are concrete and match
                    let all_concrete_match = ui.type_args.iter().zip(concrete_args.iter()).all(
                        |(arg_name, concrete_arg)| {
                            if !arg_name.starts_with(|c: char| c.is_uppercase()) {
                                return false; // type variable, not a concrete match
                            }
                            match (arg_name.as_str(), concrete_arg) {
                                ("Int", Type::Int)
                                | ("Bool", Type::Bool)
                                | ("String", Type::String)
                                | ("Float", Type::Float) => true,
                                (name, Type::ADT(aname, aargs))
                                    if name == aname && aargs.is_empty() =>
                                {
                                    true
                                }
                                _ => false,
                            }
                        },
                    );
                    if all_concrete_match {
                        return Some(ui.impl_target_mangled());
                    }
                }
            }
        }

        // Look for bare impl (type_args is empty) — works for primitives and monomorphic ADTs
        for ui in self.all_impls() {
            if ui.trait_name == trait_name
                && ui.target_type == base_name
                && ui.type_args.is_empty()
                && ui.methods.iter().any(|m| m.name == method_name)
            {
                return Some(ui.impl_target_mangled());
            }
        }

        // Look for polymorphic impl (type_args has type variables)
        if !concrete_args.is_empty() {
            for ui in self.all_impls() {
                if ui.trait_name != trait_name || ui.target_type != base_name {
                    continue;
                }
                if !ui.methods.iter().any(|m| m.name == method_name) {
                    continue;
                }
                if ui.type_args.len() == concrete_args.len() {
                    let has_type_vars = ui
                        .type_args
                        .iter()
                        .any(|a| a.starts_with(|c: char| c.is_lowercase()));
                    if has_type_vars {
                        return Some(ui.impl_target_mangled());
                    }
                }
            }
        }

        // Last resort: if the ADT has unresolved type vars in its args, find any matching impl
        // by base name (will be resolved via unification in the caller)
        if !concrete_args.is_empty() && concrete_args.iter().any(has_type_var) {
            let matching: Vec<&TraitImpl> = self
                .all_impls()
                .filter(|ui: &&TraitImpl| {
                    ui.trait_name == trait_name
                        && ui.target_type == base_name
                        && ui.methods.iter().any(|m| m.name == method_name)
                        && ui.type_args.len() == concrete_args.len()
                })
                .collect();
            if matching.len() == 1 {
                return Some(matching[0].impl_target_mangled());
            }
        }

        None
    }

    /// Resolve a single pending resolution entry into a ResolvedCall, or defer/error.
    /// Returns Ok(Some(resolution)) on success, Ok(None) if deferred, Err on failure.
    fn resolve_one_method(
        &mut self,
        span: Span,
        method_name: &str,
        arg_type: &Type,
    ) -> Result<Option<ResolvedCall>, CranelispError> {
        let concrete = apply(&self.subst, arg_type);

        match &concrete {
            Type::Var(_) => {
                // Type is polymorphic — find unique user_impl for this method.
                let trait_name = self
                    .find_trait_for_method(method_name)
                    .ok_or_else(|| CranelispError::TypeError {
                        message: format!("unknown trait method: {}", method_name),
                        span,
                    })?
                    .to_string();
                let matching: Vec<String> = self
                    .all_impls()
                    .filter(|ui: &&TraitImpl| {
                        ui.trait_name == trait_name
                            && ui.methods.iter().any(|m| m.name == method_name)
                    })
                    .map(|ui| ui.impl_target_mangled())
                    .collect();
                if matching.len() == 1 {
                    let target_mangled = &matching[0];
                    let mangled_name = format!("{}${}", method_name, target_mangled);
                    // Try to unify with the target type
                    let target_type_name = &self
                        .all_impls()
                        .find(|ui: &&TraitImpl| {
                            ui.trait_name == trait_name
                                && ui.methods.iter().any(|m| m.name == method_name)
                        })
                        .unwrap()
                        .target_type
                        .clone();
                    let target_type = match target_type_name.as_str() {
                        "Int" => Type::Int,
                        "Bool" => Type::Bool,
                        "String" => Type::String,
                        "Float" => Type::Float,
                        _ => {
                            if self.resolve_type_def_via_modules(target_type_name.as_str()).is_some() {
                                Type::ADT(target_type_name.clone(), vec![])
                            } else {
                                return Err(CranelispError::TypeError {
                                    message: format!("unknown target type: {}", target_type_name),
                                    span,
                                });
                            }
                        }
                    };
                    self.unify(arg_type, &target_type, span)?;
                    return Ok(Some(ResolvedCall::TraitMethod { mangled_name }));
                }
                if matching.len() > 1 {
                    // Defer for monomorphisation
                    self.deferred_resolutions.push((
                        span,
                        method_name.to_string(),
                        arg_type.clone(),
                    ));
                    return Ok(None);
                }
                Err(CranelispError::TypeError {
                    message: format!(
                        "cannot resolve trait method '{}' — type is ambiguous",
                        method_name
                    ),
                    span,
                })
            }
            Type::Int | Type::Bool | Type::String | Type::Float | Type::ADT(_, _) => {
                let trait_name = self
                    .find_trait_for_method(method_name)
                    .ok_or_else(|| CranelispError::TypeError {
                        message: format!("unknown trait method: {}", method_name),
                        span,
                    })?
                    .to_string();

                if let Some(target_mangled) =
                    self.find_impl_for_type(&trait_name, method_name, &concrete)
                {
                    // If the arg type has unresolved type vars (e.g., (Option a) matching
                    // a concrete impl (Option Int)), unify with the impl's self type
                    if let Type::ADT(base_name, args) = &concrete {
                        if args.iter().any(has_type_var) {
                            // Clone the matching impl to avoid borrow conflict
                            let matching_impl = self
                                .all_impls()
                                .find(|ui: &&TraitImpl| {
                                    ui.trait_name == trait_name
                                        && ui.target_type == *base_name
                                        && ui.methods.iter().any(|m| m.name == method_name)
                                })
                                .cloned();
                            if let Some(ui) = matching_impl {
                                let self_type = self.resolve_impl_self_type(&ui)?;
                                self.unify(arg_type, &self_type, span)?;
                            }
                        }
                    }

                    let mangled = format!("{}${}", method_name, target_mangled);

                    // Re-apply subst after potential unification
                    let concrete = apply(&self.subst, arg_type);

                    // If the target is a polymorphic impl (target_mangled == base type name for an ADT
                    // with type args), check if it's a constrained fn and add mono request
                    if self.resolve_constrained_fn_via_modules(&mangled).is_some() {
                        if let Type::ADT(_, args) = &concrete {
                            if !args.is_empty() && args.iter().all(|a| !has_type_var(a)) {
                                self.pending_mono_calls.push((
                                    span,
                                    mangled.clone(),
                                    vec![concrete.clone()],
                                ));
                                // For impl methods, mangle with type args only (not the full ADT)
                                let mono_mangled = crate::ast::mangle_sig(&mangled, args);
                                return Ok(Some(ResolvedCall::SigDispatch {
                                    mangled_name: mono_mangled,
                                }));
                            }
                        }
                    }

                    return Ok(Some(ResolvedCall::TraitMethod {
                        mangled_name: mangled,
                    }));
                }

                Err(CranelispError::TypeError {
                    message: format!(
                        "no impl of {} for {} (method '{}')",
                        trait_name, concrete, method_name
                    ),
                    span,
                })
            }
            other => Err(CranelispError::TypeError {
                message: format!(
                    "no impl for trait method '{}' on type {}",
                    method_name, other
                ),
                span,
            }),
        }
    }

    /// Resolve all pending trait method calls after type inference.
    /// Returns a MethodResolutions table mapping spans to resolved calls.
    pub fn resolve_methods(&mut self) -> Result<MethodResolutions, CranelispError> {
        let mut resolutions = HashMap::new();

        let pending = std::mem::take(&mut self.pending_resolutions);
        for (span, method_name, arg_type) in pending {
            if let Some(resolved) = self.resolve_one_method(span, &method_name, &arg_type)? {
                resolutions.insert(span, resolved);
            }
        }

        // Merge builtin function resolutions (extern/platform primitives).
        // These are accumulated during infer_expr and drained here so that
        // all callers (batch per-defn, REPL, check_program) get them.
        resolutions.extend(std::mem::take(&mut self.builtin_resolutions));

        Ok(resolutions)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast_builder::parse_program;

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
    fn get_method_trait_returns_display_for_show() {
        let tc = tc_with_prelude();
        assert_eq!(tc.get_method_trait("show"), Some("Display"));
    }

    #[test]
    fn get_trait_returns_display() {
        let tc = tc_with_prelude();
        let decl = tc.get_trait("Display");
        assert!(decl.is_some());
        assert_eq!(decl.unwrap().name, "Display");
        assert_eq!(decl.unwrap().methods.len(), 1);
        assert_eq!(decl.unwrap().methods[0].name, "show");
    }

    #[test]
    fn operator_symbols_in_env() {
        let tc = tc_with_prelude();
        for sym in &["+", "-", "*", "/", "=", "<", ">", "<=", ">="] {
            assert!(tc.lookup(*sym).is_some(), "operator '{}' not in env", sym);
        }
    }

    #[test]
    fn trait_for_operator_symbols() {
        let tc = tc_with_prelude();
        assert_eq!(tc.get_method_trait("+"), Some("Num"));
        assert_eq!(tc.get_method_trait("-"), Some("Num"));
        assert_eq!(tc.get_method_trait("="), Some("Eq"));
        assert_eq!(tc.get_method_trait("<"), Some("Ord"));
        assert_eq!(tc.get_method_trait("<="), Some("Ord"));
    }
}
