use std::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::error::{CranelispError, Span};
use crate::types::*;

use super::{has_type_var, substitute_vars};
use super::{ConstrainedFn, MethodResolutions, MonoDefn, ResolvedCall, TypeChecker};
use crate::names::ModuleFullPath;

impl TypeChecker {
    /// Detect constrained functions after type inference and operator resolution.
    /// A constrained function has a generalized scheme with trait constraints.
    /// Returns the set of constrained function names.
    pub(crate) fn detect_constrained_fns(&mut self, program_defns: &[&Defn]) -> HashSet<String> {
        let deferred = std::mem::take(&mut self.deferred_resolutions);
        let pending = std::mem::take(&mut self.pending_resolutions);
        let mut constrained_names = HashSet::new();

        // Group deferred/pending resolutions by the function they belong to
        // (match span ranges to function bodies)
        // Both deferred_resolutions (from Var-branch deferrals in operator resolution)
        // and pending_resolutions (unresolved non-operator trait methods) are checked.
        let mut consumed_pending = HashSet::new();
        for defn in program_defns {
            if let Some(scheme) = self.lookup(&defn.name) {
                if scheme.is_constrained() {
                    let mut fn_deferred: Vec<(Span, String, Type)> = deferred
                        .iter()
                        .filter(|(span, _, _)| span.0 >= defn.span.0 && span.1 <= defn.span.1)
                        .cloned()
                        .collect();

                    // Also capture pending (unresolved) trait methods in this fn's span
                    for (i, entry) in pending.iter().enumerate() {
                        if entry.0 .0 >= defn.span.0 && entry.0 .1 <= defn.span.1 {
                            fn_deferred.push(entry.clone());
                            consumed_pending.insert(i);
                        }
                    }

                    let cf = ConstrainedFn {
                        defn: (*defn).clone(),
                        scheme: scheme.clone(),
                        deferred_resolutions: fn_deferred,
                        defining_module: self.current_module_path.clone(),
                    };
                    // Write to CompiledModule (sole source of truth)
                    if let Some(cm) =
                        self.modules.get_mut(self.current_module_path.as_ref())
                    {
                        cm.update_constrained_fn(&defn.name, cf);
                    }
                    constrained_names.insert(defn.name.clone());
                }
            }
        }

        // Put back pending resolutions that weren't consumed by constrained fns
        self.pending_resolutions = pending
            .into_iter()
            .enumerate()
            .filter(|(i, _)| !consumed_pending.contains(i))
            .map(|(_, entry)| entry)
            .collect();

        constrained_names
    }

    /// Collect monomorphisation requests from pending_mono_calls.
    fn collect_mono_requests(&mut self) -> Vec<(Span, String, Vec<Type>)> {
        let mut requests = Vec::new();
        let pending = std::mem::take(&mut self.pending_mono_calls);
        for (span, fn_name, arg_tys) in pending {
            let concrete: Vec<Type> = arg_tys.iter().map(|t| apply(&self.subst, t)).collect();
            if concrete.iter().all(|t| !has_type_var(t)) {
                let mangled = mono_mangle(&fn_name, &concrete);
                if !self.generated_specializations.contains(&mangled) {
                    requests.push((span, fn_name, concrete));
                }
            }
        }
        requests
    }

    /// Generate a monomorphised defn for a constrained function called with concrete types.
    /// Returns the MonoDefn and the defining module where the specialization should live.
    fn monomorphise_fn(
        &self,
        fn_name: &str,
        concrete_params: &[Type],
    ) -> Result<(MonoDefn, ModuleFullPath), CranelispError> {
        let cf = self
            .resolve_constrained_fn_via_modules(fn_name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("no constrained function: {}", fn_name),
                span: (0, 0),
            })?
            .clone();
        let defining_module = cf.defining_module.clone();

        let mangled = mono_mangle(fn_name, concrete_params);

        // Build substitution: scheme vars → concrete types from function params
        // The scheme's function type is (fn [param_tys...] ret_ty),
        // and concrete_params tells us the concrete type for each param.
        let mut local_subst = HashMap::new();
        if let Type::Fn(scheme_params, _) = &cf.scheme.ty {
            for (scheme_param, concrete_param) in scheme_params.iter().zip(concrete_params.iter()) {
                collect_var_mapping(scheme_param, concrete_param, &mut local_subst);
            }
        }

        // Re-resolve deferred resolutions with concrete types
        let mut mr = HashMap::new();
        for (span, method_name, arg_type) in &cf.deferred_resolutions {
            let concrete = apply_with(&self.subst, &local_subst, arg_type);
            let type_name = type_to_name(&concrete).ok_or_else(|| CranelispError::TypeError {
                message: format!(
                    "cannot monomorphise '{}' — type {} is not concrete",
                    fn_name, concrete
                ),
                span: *span,
            })?;
            let mangled_method = format!("{}${}", method_name, type_name);
            mr.insert(
                *span,
                ResolvedCall::TraitMethod {
                    mangled_name: mangled_method,
                },
            );
        }

        Ok((MonoDefn {
            defn: Defn {
                visibility: crate::ast::Visibility::Public,
                name: mangled,
                docstring: None,
                params: cf.defn.params.clone(),
                param_annotations: cf.defn.param_annotations.clone(),
                body: cf.defn.body.clone(),
                span: cf.defn.span,
            },
            resolutions: mr,
        }, defining_module))
    }

    /// Iteratively generate all needed monomorphised specializations.
    /// Returns (mono_defns_with_modules, call_site_dispatches) where each mono defn
    /// is paired with the defining module where the specialization should be compiled,
    /// and call_site_dispatches maps call-site spans to SigDispatch resolutions.
    pub fn monomorphise_all(
        &mut self,
    ) -> Result<(Vec<(MonoDefn, ModuleFullPath)>, MethodResolutions), CranelispError> {
        let mut all = Vec::new();
        let mut dispatches = HashMap::new();
        loop {
            let requests = self.collect_mono_requests();
            if requests.is_empty() {
                break;
            }
            for (call_span, fn_name, concrete) in requests {
                let mangled = mono_mangle(&fn_name, &concrete);

                // Record call-site dispatch (even for already-generated specializations)
                dispatches.insert(
                    call_span,
                    ResolvedCall::SigDispatch {
                        mangled_name: mangled.clone(),
                    },
                );

                if self.generated_specializations.contains(&mangled) {
                    continue;
                }
                self.generated_specializations.insert(mangled.clone());
                let (mono, defining_module) = self.monomorphise_fn(&fn_name, &concrete)?;

                // Register the monomorphised function's type in the env
                let cf_scheme = self
                    .resolve_constrained_fn_via_modules(&fn_name)
                    .expect("constrained fn must exist for monomorphisation")
                    .scheme
                    .clone();
                let fn_ty = Type::Fn(
                    concrete.clone(),
                    Box::new(apply_concrete_ret(&cf_scheme, &concrete)),
                );
                self.insert_def(mangled, Scheme::mono(fn_ty));

                all.push((mono, defining_module));
            }
        }
        Ok((all, dispatches))
    }

    /// Register a constrained function for later monomorphisation (for REPL use).
    pub fn register_constrained_fn(&mut self, defn: &Defn, scheme: &Scheme) {
        let deferred = std::mem::take(&mut self.deferred_resolutions);
        let fn_deferred: Vec<(Span, String, Type)> = deferred
            .iter()
            .filter(|(span, _, _)| span.0 >= defn.span.0 && span.1 <= defn.span.1)
            .cloned()
            .collect();
        // Put back any deferred resolutions that don't belong to this function
        let remaining: Vec<(Span, String, Type)> = deferred
            .into_iter()
            .filter(|(span, _, _)| !(span.0 >= defn.span.0 && span.1 <= defn.span.1))
            .collect();
        self.deferred_resolutions = remaining;

        let cf = ConstrainedFn {
            defn: defn.clone(),
            scheme: scheme.clone(),
            deferred_resolutions: fn_deferred,
            defining_module: self.current_module_path.clone(),
        };
        // Write to CompiledModule (sole source of truth)
        if let Some(cm) = self.modules.get_mut(self.current_module_path.as_ref()) {
            cm.update_constrained_fn(&defn.name, cf);
        }
    }

    /// Check if a name is a constrained function.
    pub fn is_constrained_fn(&self, name: &str) -> bool {
        self.resolve_constrained_fn_via_modules(name).is_some()
    }

    /// Re-generalize a function's env entry after method resolution has
    /// narrowed type variables via unification. Returns the updated scheme.
    pub fn finalize_defn_type(&mut self, name: &str) -> Scheme {
        let old_scheme = self.remove_def(name).expect("function not in env");
        let resolved_ty = apply(&self.subst, &old_scheme.ty);
        let new_scheme = self.generalize(&resolved_ty);
        self.insert_def(name.to_string(), new_scheme.clone());
        new_scheme
    }
}

/// Collect variable-to-type mappings by matching a scheme type against concrete types.
pub(super) fn collect_var_mapping(
    scheme_ty: &Type,
    concrete_ty: &Type,
    mapping: &mut HashMap<TypeId, Type>,
) {
    match (scheme_ty, concrete_ty) {
        (Type::Var(id), concrete) => {
            mapping.insert(*id, concrete.clone());
        }
        (Type::Fn(sp, sr), Type::Fn(cp, cr)) => {
            for (s, c) in sp.iter().zip(cp.iter()) {
                collect_var_mapping(s, c, mapping);
            }
            collect_var_mapping(sr, cr, mapping);
        }
        (Type::ADT(sn, sa), Type::ADT(cn, ca)) if sn == cn && sa.len() == ca.len() => {
            for (s, c) in sa.iter().zip(ca.iter()) {
                collect_var_mapping(s, c, mapping);
            }
        }
        (Type::TyConApp(id, sa), Type::ADT(_, ca)) if sa.len() == ca.len() => {
            mapping.insert(*id, concrete_ty.clone());
            for (s, c) in sa.iter().zip(ca.iter()) {
                collect_var_mapping(s, c, mapping);
            }
        }
        _ => {}
    }
}

/// Apply substitution using both global subst and a local mapping (for monomorphisation).
pub(super) fn apply_with(
    global_subst: &Subst,
    local_mapping: &HashMap<TypeId, Type>,
    ty: &Type,
) -> Type {
    match ty {
        Type::Int | Type::Bool | Type::String | Type::Float => ty.clone(),
        Type::Var(id) => {
            // Try local mapping first, then global subst
            if let Some(resolved) = local_mapping.get(id) {
                resolved.clone()
            } else if let Some(resolved) = global_subst.get(id) {
                apply_with(global_subst, local_mapping, resolved)
            } else {
                ty.clone()
            }
        }
        Type::Fn(params, ret) => {
            let params = params
                .iter()
                .map(|p| apply_with(global_subst, local_mapping, p))
                .collect();
            let ret = Box::new(apply_with(global_subst, local_mapping, ret));
            Type::Fn(params, ret)
        }
        Type::ADT(name, args) => {
            let args = args
                .iter()
                .map(|a| apply_with(global_subst, local_mapping, a))
                .collect();
            Type::ADT(name.clone(), args)
        }
        Type::TyConApp(id, args) => {
            // Try to resolve the constructor variable
            if let Some(Type::ADT(name, _)) = local_mapping.get(id) {
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| apply_with(global_subst, local_mapping, a))
                    .collect();
                return Type::ADT(name.clone(), resolved_args);
            }
            let resolved_args: Vec<Type> = args
                .iter()
                .map(|a| apply_with(global_subst, local_mapping, a))
                .collect();
            Type::TyConApp(*id, resolved_args)
        }
    }
}

/// Compute the mangled name for a monomorphised function.
/// For impl method constrained fns (fn_name contains "$"), the concrete_params
/// contains the full ADT type, but we should mangle using only the type args
/// to avoid double-mangling (e.g., show$Option + [Option$Int] → show$Option$Int, not show$Option$Option$Int).
pub(super) fn mono_mangle(fn_name: &str, concrete_params: &[Type]) -> String {
    if fn_name.contains('$') && concrete_params.len() == 1 {
        if let Type::ADT(_, args) = &concrete_params[0] {
            if !args.is_empty() {
                return crate::ast::mangle_sig(fn_name, args);
            }
        }
    }
    crate::ast::mangle_sig(fn_name, concrete_params)
}

pub(super) fn type_to_name(ty: &Type) -> Option<String> {
    match ty {
        Type::Int => Some("Int".to_string()),
        Type::Bool => Some("Bool".to_string()),
        Type::String => Some("String".to_string()),
        Type::Float => Some("Float".to_string()),
        Type::ADT(name, args) if args.is_empty() => Some(name.clone()),
        Type::ADT(name, args) => {
            let parts: Option<Vec<String>> = args.iter().map(type_to_name).collect();
            Some(format!("{}${}", name, parts?.join("+")))
        }
        _ => None,
    }
}

/// Compute the concrete return type of a constrained function given concrete param types.
pub(super) fn apply_concrete_ret(scheme: &Scheme, concrete_params: &[Type]) -> Type {
    let mut mapping = HashMap::new();
    if let Type::Fn(scheme_params, _) = &scheme.ty {
        for (sp, cp) in scheme_params.iter().zip(concrete_params.iter()) {
            collect_var_mapping(sp, cp, &mut mapping);
        }
    }
    if let Type::Fn(_, ret) = &scheme.ty {
        substitute_vars(ret, &mapping)
    } else {
        Type::Int // fallback, shouldn't happen
    }
}
