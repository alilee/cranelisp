//! Multi-pass type checking pipeline.
//!
//! `check()` is the unified entry point: it processes any `&[TopLevel]` slice
//! through a multi-pass pipeline (register → check → constrained → mono → curry).
//! A REPL line is a one-element slice; a batch program is a multi-element slice.
//! The passes work identically regardless of slice length.
//!
//! ## Per-Form API (v4 Pipeline)
//!
//! `check_form()` processes a single `TopLevel` form through one pass at a time.
//! The caller drives two-pass iteration:
//! - Pass 1 (`CheckPass::Register`): register type defs, traits, signatures.
//! - Pass 2 (`CheckPass::CheckBody`): check function bodies, detect constraints.
//!
//! `merge_form_result()` accumulates per-form results into a `ModuleCheckAccumulator`.
//! `finalize_check_result()` runs post-passes and drains the accumulator into `CheckResult`.
//!
//! `check()` internally uses `check_form()` in two passes — existing callers unchanged.
//!
//! `check_program` and `check_repl_input` are deprecated. All production callers
//! now use `check()`. The old methods are retained only for typecheck crate tests.

use std::collections::{HashMap, HashSet};

use cranelisp_types::{ErrorLocation,
    CompileContext, ConstrainedFn, CranelispError, Defn, DefKind, DefnVariant,
    DisplayInfo, Expr, FQSymbol, JitSymbol, ModuleEntry, ModuleFullPath,
    ModuleStrategy, MonoDefn, ResolvedCall, Scheme, Span, Symbol, SymbolTable, TopLevel, Type,
    Visibility, Warning, apply,
};

use crate::result::CheckResult;

use cranelisp_types::types::Subst;

use crate::checker::{CheckState, TypeCheckEnv};
use crate::resolve::resolve_type_expr;
use crate::scheme::mono;

// --- AST annotation helpers (Step 1b) ---

/// Apply substitution to all `inferred_type` fields on an expression tree.
/// Replaces `Var(N)` with concrete types from the substitution.
fn apply_subst_to_expr(subst: &Subst, expr: &mut Expr) {
    // Apply substitution to this node's inferred_type
    if let Some(ty) = expr.inferred_type() {
        let resolved = apply(subst, ty);
        expr.set_inferred_type(Some(Box::new(resolved)));
    }
    // Recurse into children
    match expr {
        Expr::Apply { callee, args, .. } => {
            apply_subst_to_expr(subst, callee);
            for arg in args {
                apply_subst_to_expr(subst, arg);
            }
        }
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            for (_, binding_expr) in bindings {
                apply_subst_to_expr(subst, binding_expr);
            }
            apply_subst_to_expr(subst, body);
        }
        Expr::If { cond, then_branch, else_branch, .. } => {
            apply_subst_to_expr(subst, cond);
            apply_subst_to_expr(subst, then_branch);
            apply_subst_to_expr(subst, else_branch);
        }
        Expr::Lambda { body, .. } => {
            apply_subst_to_expr(subst, body);
        }
        Expr::Match { scrutinee, arms, .. } => {
            apply_subst_to_expr(subst, scrutinee);
            for arm in arms {
                apply_subst_to_expr(subst, &mut arm.body);
            }
        }
        Expr::Annotate { expr: inner, .. } => {
            apply_subst_to_expr(subst, inner);
        }
        Expr::VecLit { elements, .. } => {
            for elem in elements {
                apply_subst_to_expr(subst, elem);
            }
        }
        Expr::Trace { body, .. } => {
            apply_subst_to_expr(subst, body);
        }
        // Leaf nodes: no children to recurse into
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. } => {}
    }
}

/// Apply substitution to all `inferred_type` fields in a `Defn`.
pub(crate) fn apply_subst_to_defn(subst: &Subst, defn: &mut Defn) {
    for variant in &mut defn.variants {
        apply_subst_to_expr(subst, &mut variant.body);
    }
}

/// Annotate an expression tree with types and resolved calls from side maps.
/// Walks the tree recursively; for each node, sets `inferred_type` from
/// `expr_types` (by span) and `resolved_call` from `method_resolutions` (by span).
fn annotate_expr_from_maps(
    expr: &mut Expr,
    expr_types: &HashMap<Span, Type>,
    method_resolutions: &HashMap<Span, ResolvedCall>,
) {
    let span = expr.span();

    // Set inferred_type from expr_types
    if let Some(ty) = expr_types.get(&span) {
        expr.set_inferred_type(Some(Box::new(ty.clone())));
    }

    // Set resolved_call on Apply nodes from method_resolutions
    if let Expr::Apply { resolved_call, span: apply_span, .. } = expr
        && let Some(resolution) = method_resolutions.get(apply_span)
    {
        *resolved_call = Some(Box::new(resolution.clone()));
    }

    // Recurse into children
    match expr {
        Expr::Apply { callee, args, .. } => {
            annotate_expr_from_maps(callee, expr_types, method_resolutions);
            for arg in args {
                annotate_expr_from_maps(arg, expr_types, method_resolutions);
            }
        }
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            for (_, binding_expr) in bindings {
                annotate_expr_from_maps(binding_expr, expr_types, method_resolutions);
            }
            annotate_expr_from_maps(body, expr_types, method_resolutions);
        }
        Expr::If { cond, then_branch, else_branch, .. } => {
            annotate_expr_from_maps(cond, expr_types, method_resolutions);
            annotate_expr_from_maps(then_branch, expr_types, method_resolutions);
            annotate_expr_from_maps(else_branch, expr_types, method_resolutions);
        }
        Expr::Lambda { body, .. } => {
            annotate_expr_from_maps(body, expr_types, method_resolutions);
        }
        Expr::Match { scrutinee, arms, .. } => {
            annotate_expr_from_maps(scrutinee, expr_types, method_resolutions);
            for arm in arms {
                annotate_expr_from_maps(&mut arm.body, expr_types, method_resolutions);
            }
        }
        Expr::Annotate { expr: inner, .. } => {
            annotate_expr_from_maps(inner, expr_types, method_resolutions);
        }
        Expr::VecLit { elements, .. } => {
            for elem in elements {
                annotate_expr_from_maps(elem, expr_types, method_resolutions);
            }
        }
        Expr::Trace { body, .. } => {
            annotate_expr_from_maps(body, expr_types, method_resolutions);
        }
        // Leaf nodes
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. } => {}
    }
}

/// Annotate a `Defn` with types and resolved calls from side maps.
pub(crate) fn annotate_defn_from_maps(
    defn: &mut Defn,
    expr_types: &HashMap<Span, Type>,
    method_resolutions: &HashMap<Span, ResolvedCall>,
) {
    for variant in &mut defn.variants {
        annotate_expr_from_maps(&mut variant.body, expr_types, method_resolutions);
    }
}

// --- Callee write helper (Decision 21) ---

/// Group call graph edges by caller, sort + deduplicate, and write to `ModuleEntry`.
///
/// Used by both `merge_form_result` (eager write so the scheduler can read callees
/// immediately) and `finalize_check_result` (canonical final write that includes
/// any edges from post-passes).
fn write_callees_to_module_entries<C, L>(
    sym_table: &mut SymbolTable<C, L>,
    edges: &[(Symbol, FQSymbol)],
)
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut by_caller: HashMap<Symbol, Vec<FQSymbol>> = HashMap::new();
    for (caller, callee) in edges {
        by_caller
            .entry(caller.clone())
            .or_default()
            .push(callee.clone());
    }
    for (caller, mut callees) in by_caller {
        callees.sort_by(|a, b| {
            a.module
                .as_ref()
                .cmp(b.module.as_ref())
                .then(a.symbol.as_ref().cmp(b.symbol.as_ref()))
        });
        callees.dedup();
        if let Some(
            ModuleEntry::Def { callees: c, .. } | ModuleEntry::Macro { callees: c, .. },
        ) = sym_table.symbols.get_mut(&caller)
        {
            *c = callees;
        }
    }
}

// --- Per-Form Typecheck API types ---

/// Pass indicator for `check_form()`.
///
/// The two-pass structure (register all signatures, then check all bodies) is
/// fundamental to Algorithm W with mutual recursion. The caller drives the
/// iteration; `check_form` does the right thing for each (form, pass) pair.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CheckPass {
    /// Pass 1: register type/trait/signature.
    /// For Defn: registers signature only. For TypeDef/TraitDecl/TraitImpl: full registration.
    Register,
    /// Pass 2: check function body, generalize, detect constraints.
    /// Only meaningful for Defn forms. Other form kinds return an empty result.
    CheckBody,
}

/// Per-form typecheck result.
///
/// Returned by `check_form()` for each (form, pass) invocation. The caller
/// feeds this to `merge_form_result()` to accumulate into module-level state.
/// In v4, the scheduler also uses these fields for per-symbol codegen readiness.
#[derive(Debug)]
pub(crate) struct FormCheckResult {
    /// Method resolutions discovered while checking this form.
    /// In Pass 1: empty (registration produces no resolutions).
    /// In Pass 2: resolutions from the body of this defn.
    pub(crate) method_resolutions: HashMap<Span, ResolvedCall>,

    /// Expression types for this form's AST nodes.
    /// In Pass 1: may contain constructor types for TypeDef forms.
    /// In Pass 2: contains all expr types from the defn body + the defn's Fn type.
    pub(crate) expr_types: HashMap<Span, Type>,

    /// If this form defines a constrained polymorphic function (Pass 2 only),
    /// the function name. Used by the caller to build the constrained_fn_names set.
    pub(crate) constrained_fn: Option<Symbol>,

    /// Monomorphised definitions generated from this form's call sites (Pass 2 only).
    pub(crate) mono_defns: Vec<MonoDefn>,

    /// Default method definitions expanded from trait impls in this form (Pass 1 only).
    /// Produced when a TraitImpl form triggers default method synthesis.
    pub(crate) default_method_defns: Vec<Defn>,

    /// Multi-sig mangled definitions produced during overload resolution.
    /// Populated when a multi-sig DefnMulti's variants are resolved after Pass 2.
    pub(crate) multi_sig_defns: Vec<Defn>,

    /// Warnings emitted during checking this form.
    pub(crate) warnings: Vec<Warning>,

    /// Call graph edges discovered during this form's checking.
    /// Each entry is (caller_symbol, callee_fqsymbol). The caller is local to
    /// the current module; the callee is fully qualified (may be cross-module).
    /// Accumulated for the module's call graph, used by the scheduler for
    /// macro dependency walks.
    pub(crate) call_graph_edges: Vec<(Symbol, FQSymbol)>,
}

impl FormCheckResult {
    /// Create an empty FormCheckResult (used for no-op passes).
    fn empty() -> Self {
        FormCheckResult {
            method_resolutions: HashMap::new(),
            expr_types: HashMap::new(),
            constrained_fn: None,
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings: Vec::new(),
            call_graph_edges: Vec::new(),
        }
    }
}

/// Per-module accumulator for form-by-form typecheck results.
///
/// One accumulator per module. Created before Pass 1, consumed by
/// `finalize_check_result()`. No concurrent access — a single worker
/// processes one module's forms sequentially (Invariant 5).
/// The accumulator is the **authoritative source** for method_resolutions, expr_types,
/// and warnings in the final `CheckResult`. During per-form checking, `merge_form_result()`
/// collects these from each `FormCheckResult`. After post-passes run in
/// `finalize_check_result()`, any additional resolutions/warnings produced by those passes
/// are swept from `self.state` into the accumulator, and the `CheckResult` is built
/// exclusively from the accumulator.
pub(crate) struct ModuleCheckAccumulator {
    pub(crate) method_resolutions: HashMap<Span, ResolvedCall>,
    pub(crate) expr_types: HashMap<Span, Type>,
    pub(crate) constrained_fn_names: HashSet<Symbol>,
    pub(crate) mono_defns: Vec<MonoDefn>,
    pub(crate) default_method_defns: Vec<Defn>,
    pub(crate) multi_sig_defns: Vec<Defn>,
    pub(crate) warnings: Vec<Warning>,
    pub(crate) call_graph_edges: Vec<(Symbol, FQSymbol)>,
    /// Type vars from pass 1 registration, keyed by defn name.
    /// Needed by pass 2 to check bodies against registered signatures.
    pub(crate) defn_type_vars: HashMap<Symbol, (Vec<Type>, Type)>,
}

impl Default for ModuleCheckAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl ModuleCheckAccumulator {
    /// Create a new empty accumulator for a module.
    pub(crate) fn new() -> Self {
        ModuleCheckAccumulator {
            method_resolutions: HashMap::new(),
            expr_types: HashMap::new(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings: Vec::new(),
            call_graph_edges: Vec::new(),
            defn_type_vars: HashMap::new(),
        }
    }
}

// --- Multi-sig type aliases ---
//
// Reachable only through `check_program` / `check_repl_input` /
// `finalize_check_result` chains, which are `pub(crate)` and consumed only
// by `#[cfg(test)]` test-fixture proxies (see `TestFixture` in `checker.rs`).
// The new free-function surface (`check_form_signatures` /
// `check_form_body`) does not yet wire through multi-sig overload
// resolution; that integration arrives in Wave 3a-α completion.

/// Resolved variant info: (concrete_params, concrete_ret, internal_name, variant_index).
#[allow(dead_code)]
type ResolvedVariant = (Vec<Type>, Type, Symbol, usize);

/// Mangled variant info: (concrete_params, concrete_ret, mangled_name).
#[allow(dead_code)]
type MangledVariantInfo = (Vec<Type>, Type, Symbol);

// --- Name mangling for multi-sig overload dispatch ---

/// Mangle a function name with its parameter type signature.
/// e.g., `mangle_sig("foo", &[Type::Int, Type::Bool])` → `"foo$Int+Bool"`.
/// Returns true if `name` matches the trait-impl mangled form `Trait.method$Type`
/// (e.g., `Double.double$Int`, `Num.+$Int`, `Countable.count-plus$Int`).
///
/// This is used to distinguish annotated defns produced by `check_impl_method`
/// from user-written or REPL-synthetic defns (`__expr`), so that the
/// "skip re-inference" fast path only applies to trait impl methods.
fn is_trait_impl_mangled_name(name: &str) -> bool {
    // Trait-impl mangled names contain exactly one '.' followed by a '$'
    // separating the method name from the impl type suffix.
    if let Some(dot_pos) = name.find('.')
        && let Some(dollar_pos) = name[dot_pos + 1..].find('$')
    {
        let after_dot = &name[dot_pos + 1..];
        let method_part = &after_dot[..dollar_pos];
        let type_part = &after_dot[dollar_pos + 1..];
        return !method_part.is_empty() && !type_part.is_empty();
    }
    false
}

#[allow(dead_code)]
fn mangle_sig(name: &str, param_types: &[Type]) -> Symbol {
    if param_types.is_empty() {
        Symbol::from(format!("{}$", name))
    } else {
        let parts: Vec<String> = param_types.iter().map(mangle_type).collect();
        Symbol::from(format!("{}${}", name, parts.join("+")))
    }
}

/// Mangle a single type for name mangling.
#[allow(dead_code)]
fn mangle_type(ty: &Type) -> String {
    match ty {
        Type::Int => "Int".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Float => "Float".to_string(),
        Type::Fn(_, _) => "Fn".to_string(),
        Type::ADT(name, args) => {
            if args.is_empty() {
                name.to_string()
            } else {
                let arg_parts: Vec<String> = args.iter().map(mangle_type).collect();
                format!("{}${}", name, arg_parts.join("+"))
            }
        }
        Type::Var(_) => "Var".to_string(),
        Type::TyConApp(id, _) => format!("TyCon{id}"),
    }
}

/// Check if two concrete types are compatible (for overload resolution).
#[allow(dead_code)]
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
        (Type::TyConApp(id1, a1), Type::TyConApp(id2, a2)) => {
            id1 == id2
                && a1.len() == a2.len()
                && a1.iter().zip(a2.iter()).all(|(a, b)| types_compatible(a, b))
        }
        (Type::Var(_), _) | (_, Type::Var(_)) => true, // Unresolved — assume compatible
        _ => false,
    }
}

// The whole-program / REPL-input legacy check methods (`check`,
// `check_program`, `check_repl_input`) plus their helper chain are
// reachable only through `#[cfg(test)]` test-fixture proxies (per the
// Wave 3a-β public-surface demotion — see FIXME 0173). Their dead-code
// lints are suppressed at the impl-block level until the chain is fully
// retired in a follow-up wave; the new free-function surface
// (`check_form_signatures` / `check_form_body`) is the production path.
#[allow(dead_code)]
impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    // =================================================================
    // Per-Form Typecheck API (v4 pipeline)
    // =================================================================

    /// Extract call graph edges from method resolutions for a given caller.
    ///
    /// For each `ResolvedCall` in the provided map, derives the callee as an
    /// `FQSymbol`. `BuiltinFn` resolutions are skipped (always available).
    /// The caller symbol is the defn whose body produced these resolutions.
    fn extract_call_graph_edges(
        &self,
        state: &CheckState,
        caller: &Symbol,
        method_resolutions: &HashMap<Span, ResolvedCall>,
    ) -> Vec<(Symbol, FQSymbol)> {
        let current_module = state.current_module.clone();
        let mut edges = Vec::new();

        for resolved in method_resolutions.values() {
            if let Some(callee) = self.resolved_call_to_fqsymbol(resolved, &current_module) {
                edges.push((caller.clone(), callee));
            }
        }

        edges
    }

    /// Derive the callee `FQSymbol` from a `ResolvedCall`, if it represents
    /// a user-defined dependency (not a builtin).
    fn resolved_call_to_fqsymbol(
        &self,
        resolved: &ResolvedCall,
        current_module: &ModuleFullPath,
    ) -> Option<FQSymbol> {
        match resolved {
            ResolvedCall::TraitMethod { mangled_name, .. } => {
                // The impl method lives in the current module for now (Step 4).
                // Step 5 will look up the impl's defining module from the trait registry.
                Some(FQSymbol {
                    module: current_module.clone(),
                    symbol: Symbol::from(mangled_name.as_ref()),
                })
            }
            ResolvedCall::SigDispatch { mangled_name } => {
                // Multi-sig variants are always local to the current module.
                Some(FQSymbol {
                    module: current_module.clone(),
                    symbol: Symbol::from(mangled_name.as_ref()),
                })
            }
            ResolvedCall::AutoCurry { target_name, trait_resolution, .. } => {
                // If there's an inner trait resolution, derive the edge from it.
                if let Some(inner) = trait_resolution {
                    self.resolved_call_to_fqsymbol(inner, current_module)
                } else {
                    // Plain function curry — target is in current module.
                    Some(FQSymbol {
                        module: current_module.clone(),
                        symbol: target_name.clone(),
                    })
                }
            }
            ResolvedCall::BuiltinFn { .. } => {
                // Builtins are always available — no codegen dependency.
                None
            }
        }
    }

    /// Check a single `TopLevel` form through one pass.
    ///
    /// The caller drives the two-pass iteration:
    /// - Pass 1 (`CheckPass::Register`): call for every form in source order.
    /// - Pass 2 (`CheckPass::CheckBody`): call for every form in source order.
    ///
    /// Returns a `FormCheckResult` that the caller feeds to `merge_form_result()`.
    ///
    /// ## Invariants
    /// - All signatures must be registered (Pass 1) before any body is checked (Pass 2).
    /// - Source order within Pass 1 must respect: TypeDef < TraitDecl < TraitImpl < Defn.
    /// - One `ModuleCheckAccumulator` per module, no concurrent access.
    ///
    /// The caller owns the `CheckState` and passes it in. Multiple workers
    /// can hold `&TypeCheckEnv` concurrently, each with their own state.
    pub(crate) fn check_form(
        &self,
        _module: &ModuleFullPath,
        form: &TopLevel,
        pass: CheckPass,
        state: &mut CheckState,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        match pass {
            CheckPass::Register => self.check_form_register(state, form, accumulator),
            CheckPass::CheckBody => self.check_form_body(state, form, accumulator),
        }
    }

    /// Pass 1 (Register) dispatch: register type defs, trait decls/impls, signatures.
    fn check_form_register(
        &self,
        state: &mut CheckState,
        form: &TopLevel,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        match form {
            TopLevel::TypeDef {
                name,
                docstring,
                type_params,
                constructors,
                visibility,
                span,
            } => {
                self.register_type_def(
                    state, name, docstring, type_params, constructors, *visibility, *span,
                )?;
                Ok(FormCheckResult::empty())
            }
            TopLevel::TraitDecl(decl) => {
                self.register_trait_decl(state, decl)?;
                Ok(FormCheckResult::empty())
            }
            TopLevel::TraitImpl(impl_) => {
                let defaults = self.register_trait_impl(state, impl_)?;
                let mut result = FormCheckResult::empty();
                result.default_method_defns = defaults;
                Ok(result)
            }
            TopLevel::Defn(defn) => {
                if defn.is_multi_sig() {
                    self.check_form_register_multi_sig(state, defn, accumulator)
                } else {
                    self.check_form_register_single_defn(state, defn, accumulator)
                }
            }
            TopLevel::Expr(_) => {
                // Expr forms should be wrapped as synthetic Defn before reaching here.
                // If they somehow arrive unwrapped, treat as no-op.
                Ok(FormCheckResult::empty())
            }
        }
    }

    /// Register a single-sig defn's signature (Pass 1).
    fn check_form_register_single_defn(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        let (param_types, ret_ty) = self.register_defn_signature(state, defn)?;
        accumulator.defn_type_vars.insert(defn.name.clone(), (param_types, ret_ty));
        Ok(FormCheckResult::empty())
    }

    /// Register a multi-sig defn: expand variants, register each, register base as Overloaded.
    fn check_form_register_multi_sig(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        let mut overload_entries = Vec::new();
        for (i, variant) in defn.variants.iter().enumerate() {
            let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
            overload_entries.push((internal_name.clone(), variant.params.len()));

            let internal_defn = Defn {
                name: internal_name.clone(),
                docstring: defn.docstring.clone(),
                variants: vec![DefnVariant {
                    params: variant.params.clone(),
                    param_annotations: variant.param_annotations.clone(),
                    body: variant.body.clone(),
                    span: variant.span,
                }],
                visibility: defn.visibility,
                span: variant.span,
            };
            // Register each variant's signature
            let (param_types, ret_ty) = self.register_defn_signature(state, &internal_defn)?;
            accumulator.defn_type_vars.insert(internal_name, (param_types, ret_ty));
        }
        state.overloads.insert(defn.name.clone(), overload_entries);

        // Register a placeholder for the base name
        let placeholder_ty = self.fresh_var();
        let placeholder_scheme = mono(placeholder_ty);
        self.current_symbol_table_mut(state).insert(
            defn.name.clone(),
            ModuleEntry::Def {
                scheme: placeholder_scheme,
                visibility: defn.visibility,
                docstring: defn.docstring.clone(),
                param_names: vec![],
                kind: Box::new(DefKind::Overloaded { variants: vec![] }),
                callees: Vec::new(),
                got_slot: None,
                trait_origin: None,
                ast: None,
                code: None,
            },
        );

        Ok(FormCheckResult::empty())
    }

    /// Pass 2 (CheckBody) dispatch: check function bodies, generalize, detect constraints.
    fn check_form_body(
        &self,
        state: &mut CheckState,
        form: &TopLevel,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        match form {
            TopLevel::Defn(defn) => {
                if defn.is_multi_sig() {
                    self.check_form_body_multi_sig(state, defn, accumulator)
                } else {
                    self.check_form_body_single_defn(state, defn, accumulator)
                }
            }
            // Non-Defn forms are no-ops in CheckBody pass.
            _ => Ok(FormCheckResult::empty()),
        }
    }

    /// Check a single-sig defn body (Pass 2).
    ///
    /// Checks the body, does eager constrained-fn detection, and scans
    /// for monomorphisation call sites.
    fn check_form_body_single_defn(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        accumulator: &ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        // Skip body re-check for trait impl (mangled) defns already type-checked
        // by `check_impl_method` during Pass 1. Re-checking with fresh type vars
        // causes spurious constrained-fn detection → null GOT → SIGSEGV.
        //
        // Gated on the `Trait.method$Type` name pattern to avoid false positives
        // on REPL-transient `__expr` or regular user defns whose ast was
        // annotated by a prior evaluation.
        if is_trait_impl_mangled_name(defn.name.as_ref()) {
            let sym_table = self.current_symbol_table(state);
            if let Some(ModuleEntry::Def { ast: Some(_), .. }) =
                sym_table.symbols.get(&defn.name)
            {
                return Ok(FormCheckResult::empty());
            }
        }

        let (param_types, ret_ty) = accumulator
            .defn_type_vars
            .get(&defn.name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("internal: missing type vars for {}", defn.name),
                location: ErrorLocation::from_span(defn.span),
            })?;

        // Snapshot method_resolutions and expr_types sizes so we can extract
        // just the new entries added during this form's checking.
        let mr_before: HashSet<Span> = state.method_resolutions.keys().copied().collect();
        let et_before: HashSet<Span> = state.expr_types.keys().copied().collect();

        self.check_defn_body(state, defn, param_types, ret_ty)?;
        self.resolve_deferred_trait_calls(state, defn.body());

        // Per-defn post-passes: resolve auto-curry accumulated during this
        // defn's body check. Overload resolution is deferred to finalize
        // because resolved_overloads is populated by resolve_multi_sig_overloads.
        self.resolve_auto_curry(state);

        // Eager constrained-fn detection
        let fn_type = Type::Fn(
            param_types.iter().map(|t| self.apply_subst(state, t)).collect(),
            Box::new(self.apply_subst(state, ret_ty)),
        );
        let trial_scheme = self.generalize(state, &fn_type);
        let constrained_fn = if !trial_scheme.constraints.is_empty() {
            if let Some(ModuleEntry::Def { kind, .. }) =
                self.current_symbol_table_mut(state).symbols.get_mut(&defn.name)
            {
                let cf = ConstrainedFn {
                    defn: defn.clone(),
                    scheme: trial_scheme,
                };
                **kind = DefKind::UserFn {
                    constrained_fn: Some(Box::new(cf)),
                };
            }
            Some(defn.name.clone())
        } else {
            None
        };

        // Extract new method resolutions and expr types added during this form
        let mut form_mr = HashMap::new();
        for (span, res) in &state.method_resolutions {
            if !mr_before.contains(span) {
                form_mr.insert(*span, res.clone());
            }
        }
        let mut form_et = HashMap::new();
        for (span, ty) in &state.expr_types {
            if !et_before.contains(span) {
                form_et.insert(*span, ty.clone());
            }
        }

        // Per-defn AST annotation: clone the defn, annotate from side maps,
        // apply final substitution, and write to ModuleEntry::Def.ast.
        {
            let resolved_et: HashMap<Span, Type> = form_et
                .iter()
                .map(|(span, ty)| (*span, apply(&state.subst, ty)))
                .collect();
            let mut annotated = defn.clone();
            annotate_defn_from_maps(&mut annotated, &resolved_et, &form_mr);
            apply_subst_to_defn(&state.subst, &mut annotated);
            if let Some(ModuleEntry::Def { ast, .. }) =
                self.current_symbol_table_mut(state).symbols.get_mut(&defn.name)
            {
                *ast = Some(annotated);
            }
        }

        // Extract call graph edges from method resolutions (Decision 21).
        let call_graph_edges = self.extract_call_graph_edges(state, &defn.name, &form_mr);

        let warnings = std::mem::take(&mut state.warnings);

        Ok(FormCheckResult {
            method_resolutions: form_mr,
            expr_types: form_et,
            constrained_fn,
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings,
            call_graph_edges,
        })
    }

    /// Check a multi-sig defn's variant bodies (Pass 2).
    fn check_form_body_multi_sig(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        accumulator: &ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        let mr_before: HashSet<Span> = state.method_resolutions.keys().copied().collect();
        let et_before: HashSet<Span> = state.expr_types.keys().copied().collect();

        // Check each variant body
        for (i, variant) in defn.variants.iter().enumerate() {
            let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
            let (param_types, ret_ty) = accumulator
                .defn_type_vars
                .get(&internal_name)
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!(
                        "internal: missing type vars for multi-sig variant {}",
                        internal_name
                    ),
                    location: ErrorLocation::from_span(variant.span),
                })?;

            // Snapshot for per-variant delta extraction
            let variant_mr_before: HashSet<Span> = state.method_resolutions.keys().copied().collect();
            let variant_et_before: HashSet<Span> = state.expr_types.keys().copied().collect();

            // Build a temporary single-variant defn for body checking
            let internal_defn = Defn {
                name: internal_name.clone(),
                docstring: defn.docstring.clone(),
                variants: vec![DefnVariant {
                    params: variant.params.clone(),
                    param_annotations: variant.param_annotations.clone(),
                    body: variant.body.clone(),
                    span: variant.span,
                }],
                visibility: defn.visibility,
                span: variant.span,
            };

            self.check_defn_body(state, &internal_defn, param_types, ret_ty)?;
            self.resolve_deferred_trait_calls(state, internal_defn.body());

            // Per-variant post-passes (auto-curry only; overloads deferred to finalize)
            self.resolve_auto_curry(state);

            // Per-variant AST annotation
            {
                let variant_mr: HashMap<Span, ResolvedCall> = state.method_resolutions
                    .iter()
                    .filter(|(span, _)| !variant_mr_before.contains(span))
                    .map(|(span, res)| (*span, res.clone()))
                    .collect();
                let variant_et: HashMap<Span, Type> = state.expr_types
                    .iter()
                    .filter(|(span, _)| !variant_et_before.contains(span))
                    .map(|(span, ty)| (*span, apply(&state.subst, ty)))
                    .collect();
                let mut annotated = internal_defn.clone();
                annotate_defn_from_maps(&mut annotated, &variant_et, &variant_mr);
                apply_subst_to_defn(&state.subst, &mut annotated);
                if let Some(ModuleEntry::Def { ast, .. }) =
                    self.current_symbol_table_mut(state).symbols.get_mut(&internal_name)
                {
                    *ast = Some(annotated);
                }
            }

            // Eager constrained-fn detection for variant
            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(state, t)).collect(),
                Box::new(self.apply_subst(state, ret_ty)),
            );
            let trial_scheme = self.generalize(state, &fn_type);
            if !trial_scheme.constraints.is_empty()
                && let Some(ModuleEntry::Def { kind, .. }) =
                    self.current_symbol_table_mut(state).symbols.get_mut(&internal_name)
            {
                let cf = ConstrainedFn {
                    defn: internal_defn,
                    scheme: trial_scheme,
                };
                **kind = DefKind::UserFn {
                    constrained_fn: Some(Box::new(cf)),
                };
            }
        }

        // Extract new method resolutions and expr types
        let mut form_mr = HashMap::new();
        for (span, res) in &state.method_resolutions {
            if !mr_before.contains(span) {
                form_mr.insert(*span, res.clone());
            }
        }
        let mut form_et = HashMap::new();
        for (span, ty) in &state.expr_types {
            if !et_before.contains(span) {
                form_et.insert(*span, ty.clone());
            }
        }

        // Extract call graph edges for each variant (Decision 21).
        // Multi-sig variant edges are attributed to the base defn name since
        // the mangled names aren't known until overload resolution in finalize.
        let call_graph_edges = self.extract_call_graph_edges(state, &defn.name, &form_mr);

        let warnings = std::mem::take(&mut state.warnings);

        Ok(FormCheckResult {
            method_resolutions: form_mr,
            expr_types: form_et,
            constrained_fn: None,
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings,
            call_graph_edges,
        })
    }

    /// Merge a `FormCheckResult` into the module's accumulator.
    ///
    /// Called after each `check_form()` to accumulate per-form results
    /// into the module-level state. Also eagerly writes callees to
    /// `ModuleEntry` in the symbol table (Decision 21) so that the
    /// scheduler can read them immediately without waiting for
    /// `finalize_check_result`.
    /// Merge a per-form check result into the module accumulator.
    pub(crate) fn merge_form_result(
        &self,
        _module: &ModuleFullPath,
        state: &mut CheckState,
        accumulator: &mut ModuleCheckAccumulator,
        result: FormCheckResult,
    ) {
        self.merge_form_result_inner(state, accumulator, result);
    }

    fn merge_form_result_inner(
        &self,
        state: &mut CheckState,
        accumulator: &mut ModuleCheckAccumulator,
        result: FormCheckResult,
    ) {
        // Write callees to ModuleEntry eagerly (Decision 21).
        if !result.call_graph_edges.is_empty() {
            let mut guard = self.current_symbol_table_mut(state);
            write_callees_to_module_entries(&mut *guard, &result.call_graph_edges);
        }

        accumulator.method_resolutions.extend(result.method_resolutions);
        accumulator.expr_types.extend(result.expr_types);
        if let Some(name) = result.constrained_fn {
            accumulator.constrained_fn_names.insert(name);
        }
        accumulator.mono_defns.extend(result.mono_defns);
        accumulator.default_method_defns.extend(result.default_method_defns);
        accumulator.multi_sig_defns.extend(result.multi_sig_defns);
        accumulator.warnings.extend(result.warnings);
        accumulator.call_graph_edges.extend(result.call_graph_edges);
    }

    /// Finalize typecheck for a module: run post-passes and drain accumulator into `CheckResult`.
    ///
    /// Runs:
    /// 1. Phase 2 generalization (apply final substitution, clear false-positive constrained markers)
    /// 2. Phase 3 re-resolve deferred trait calls
    /// 3. Multi-sig overload resolution (pass 2.5)
    /// 4. Constrained-fn detection and monomorphisation (passes 3-4)
    /// 5. Pending overload + auto-curry resolution (pass 5)
    /// 6. Build `CheckResult` from accumulated state
    ///
    /// Note: `type_defs` and `constructor_to_type` are read from the TypeChecker's
    /// module tables, not from the accumulator — TypeDef registration writes
    /// directly into the module's type_defs registry during Pass 1.
    /// Finalize: run post-passes and drain the accumulator into `CheckResult`.
    pub(crate) fn finalize_check_result(
        &self,
        _module: &ModuleFullPath,
        state: &mut CheckState,
        accumulator: &mut ModuleCheckAccumulator,
        working_program: &[TopLevel],
        strategy: ModuleStrategy,
    ) -> Result<CheckResult, CranelispError> {
        self.finalize_check_result_inner(state, accumulator, working_program, strategy)
    }

    fn finalize_check_result_inner(
        &self,
        state: &mut CheckState,
        accumulator: &mut ModuleCheckAccumulator,
        working_program: &[TopLevel],
        strategy: ModuleStrategy,
    ) -> Result<CheckResult, CranelispError> {
        // Phase 2: generalize all functions (matching pass2_check_bodies Phase 2).
        // Clear false-positive constrained markers.
        for (name, (param_types, ret_ty)) in &accumulator.defn_type_vars {
            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(state, t)).collect(),
                Box::new(self.apply_subst(state, ret_ty)),
            );
            let scheme = self.generalize(state, &fn_type);
            if let Some(ModuleEntry::Def { scheme: s, kind, .. }) =
                self.current_symbol_table_mut(state).symbols.get_mut(name)
            {
                *s = scheme.clone();
                if scheme.constraints.is_empty()
                    && let DefKind::UserFn { constrained_fn: Some(_) } = kind.as_ref()
                {
                    **kind = DefKind::UserFn { constrained_fn: None };
                }
            }
        }

        // Phase 3: re-resolve deferred trait calls with final substitution.
        // Per-defn resolution already ran in check_form_body, but cross-defn
        // substitution refinement (e.g., constrained fns pinned by call sites)
        // may enable additional resolutions. This updates the side maps for
        // backward compatibility; AST annotation is already done per-defn.
        for top in working_program {
            if let TopLevel::Defn(defn) = top {
                if defn.is_multi_sig() {
                    for (i, variant) in defn.variants.iter().enumerate() {
                        let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
                        let internal_defn = Defn {
                            name: internal_name,
                            docstring: defn.docstring.clone(),
                            variants: vec![DefnVariant {
                                params: variant.params.clone(),
                                param_annotations: variant.param_annotations.clone(),
                                body: variant.body.clone(),
                                span: variant.span,
                            }],
                            visibility: defn.visibility,
                            span: variant.span,
                        };
                        self.resolve_deferred_trait_calls(state, internal_defn.body());
                    }
                } else {
                    self.resolve_deferred_trait_calls(state, defn.body());
                }
            }
        }

        // Pass 2.5: resolve multi-sig overloads.
        // Side effect: registers mangled variants on the symbol table.
        // The returned Vec<Defn> was carried on CheckResult.default_method_defns
        // pre-slim; no longer needed — mangled entries live on SymbolTable.
        let _multi_sig_defns = self.resolve_multi_sig_overloads(
            state,
            working_program,
            &accumulator.defn_type_vars,
        )?;

        // Pass 3: detect constrained polymorphic functions
        let single_sig_defns = Self::collect_single_sig_defns(working_program);
        let mut constrained_fn_names = self.detect_constrained_fns(state, &single_sig_defns);

        // Add previously-accumulated constrained fns and those from prior REPL evals
        constrained_fn_names.extend(accumulator.constrained_fn_names.drain());

        if strategy == ModuleStrategy::Additive {
            for (name, entry) in self.current_symbol_table(state).all_symbols() {
                if let ModuleEntry::Def { kind, scheme, ast, .. } = entry {
                    match kind.as_ref() {
                        // Trait-constrained polymorphism: classic constrained
                        // fn marker.
                        DefKind::UserFn { constrained_fn: Some(_) } => {
                            constrained_fn_names.insert(name.clone());
                        }
                        // Pure parametric polymorphism registered by a previous
                        // `check_forms` call (Additive cross-call shape): the
                        // scheme is still polymorphic (`scheme.vars` non-empty)
                        // and we have the annotated `ast`. The current
                        // cluster's call sites against this name need
                        // monomorphisation just as if it were constrained —
                        // backend codegen requires concrete CLIF types.
                        // `get_constrained_fn` synthesises a `ConstrainedFn`
                        // view from `ast + scheme` for this case.
                        DefKind::UserFn { constrained_fn: None }
                            if !scheme.vars.is_empty() && ast.is_some() =>
                        {
                            constrained_fn_names.insert(name.clone());
                        }
                        _ => {}
                    }
                }
            }
        }

        // Pass 4: monomorphise constrained function call sites.
        // Side effect: registers mono specialisations on the symbol table via
        // `register_mono_entry` inside `monomorphise_call`. The returned
        // Vec<MonoDefn> was carried on CheckResult.mono_defns pre-slim; no
        // longer needed — mono entries live on SymbolTable.
        let _mono_defns = self.pass4_monomorphise(state, &single_sig_defns, &constrained_fn_names)?;

        // Pass 5: overloads and auto-curry already resolved per-defn.
        // Drain any remaining entries (e.g., from mono defn generation).
        self.resolve_pending_overloads(state)?;
        self.resolve_auto_curry(state);

        // Sweep post-pass outputs from self.state into the accumulator.
        // Post-passes (resolve_deferred_trait_calls, pass4_monomorphise,
        // resolve_pending_overloads, resolve_auto_curry) write new method
        // resolutions into state.method_resolutions. Merge these into
        // the accumulator so it becomes the single authoritative source.
        accumulator.method_resolutions.extend(
            std::mem::take(&mut state.method_resolutions),
        );
        accumulator.expr_types.extend(
            std::mem::take(&mut state.expr_types),
        );
        accumulator.warnings.extend(
            std::mem::take(&mut state.warnings),
        );

        // Final callee write (Decision 21): overwrite the eager writes from
        // merge_form_result with the final canonical version that includes any
        // edges from post-passes.
        if !accumulator.call_graph_edges.is_empty() {
            let mut guard = self.current_symbol_table_mut(state);
            write_callees_to_module_entries(&mut *guard, &accumulator.call_graph_edges);
        }

        // Resolve all accumulated expr_types through the final substitution.
        let resolved_expr_types: HashMap<Span, Type> = accumulator
            .expr_types
            .iter()
            .map(|(span, ty)| (*span, apply(&state.subst, ty)))
            .collect();

        // Step 1b: AST annotation is primarily per-defn (check_form_body_single_defn,
        // check_form_body_multi_sig, check_impl_method, check_hkt_impl_method,
        // monomorphise_call). However, cross-defn substitution refinement (e.g.,
        // constrained fns pinned by call sites) and batch post-passes (Phase 3
        // re-resolve, Pass 5 overloads/auto-curry) may add new resolutions after
        // per-defn annotation. Re-annotate ASTs that have new information.
        {
            let sym_table = &mut self.current_symbol_table_mut(state);
            for top in working_program {
                match top {
                    TopLevel::Defn(defn) if defn.is_multi_sig() => {
                        for (i, _variant) in defn.variants.iter().enumerate() {
                            let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
                            if let Some(ModuleEntry::Def { ast: Some(existing), .. }) =
                                sym_table.symbols.get_mut(&internal_name)
                            {
                                annotate_defn_from_maps(
                                    existing,
                                    &resolved_expr_types,
                                    &accumulator.method_resolutions,
                                );
                                apply_subst_to_defn(&state.subst, existing);
                            }
                        }
                    }
                    TopLevel::Defn(defn) => {
                        if let Some(ModuleEntry::Def { ast: Some(existing), .. }) =
                            sym_table.symbols.get_mut(&defn.name)
                        {
                            annotate_defn_from_maps(
                                existing,
                                &resolved_expr_types,
                                &accumulator.method_resolutions,
                            );
                            apply_subst_to_defn(&state.subst, existing);
                        }
                    }
                    TopLevel::TraitImpl(ti) => {
                        for method in &ti.methods {
                            let mangled = format!("{}.{}${}", ti.trait_name, method.name, ti.target_type);
                            let mangled_sym = Symbol::from(mangled.as_str());
                            if let Some(ModuleEntry::Def { ast: Some(existing), .. }) =
                                sym_table.symbols.get_mut(&mangled_sym)
                            {
                                annotate_defn_from_maps(
                                    existing,
                                    &resolved_expr_types,
                                    &accumulator.method_resolutions,
                                );
                                apply_subst_to_defn(&state.subst, existing);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        // Build CheckResult from the accumulator (authoritative source).
        // Sprint 57 Wave 2 step 4: CheckResult slimmed to `{ warnings, display }`.
        // The legacy `method_resolutions` / `expr_types` / `mono_defns` /
        // `constrained_fn_names` / `default_method_defns` fields were retired —
        // their data lives on annotated AST nodes and `ModuleEntry::Def` entries
        // (symbol-table registrations above are the durable carriers).
        let result = CheckResult {
            warnings: std::mem::take(&mut accumulator.warnings),
            display: None,
        };

        Ok(result)
    }

    // =================================================================
    // Unified check() entry point — uses check_form internally
    // =================================================================

    /// Unified type-checking entry point.
    ///
    /// Processes a slice of `TopLevel` forms through the multi-pass pipeline
    /// using `check_form()` internally. Existing callers see identical results.
    ///
    /// `Expr` variants are wrapped in a synthetic zero-arg `Defn` named `__expr`
    /// so they flow through the same passes as regular definitions.
    #[must_use = "check result contains expr_types and method_resolutions needed by codegen"]
    pub(crate) fn check(
        &self,
        state: &mut CheckState,
        program: &[TopLevel],
        ctx: &CompileContext,
        strategy: ModuleStrategy,
    ) -> Result<CheckResult, CranelispError> {
        // Ensure the module's symbol table exists (DashMap interior mutation).
        self.ensure_module_exists(&ctx.module);

        // Set the module on the caller-owned state.
        state.current_module = ctx.module.clone();
        self.check_inner(state, program, strategy)
    }

    fn check_inner(
        &self,
        state: &mut CheckState,
        program: &[TopLevel],
        strategy: ModuleStrategy,
    ) -> Result<CheckResult, CranelispError> {
        // If Replace strategy, clear existing module state so that removed
        // definitions don't persist as stale entries.
        if strategy == ModuleStrategy::Replace {
            self.clear_module_for_replace(state);
        }

        // Build a working copy of the program with Expr variants wrapped
        // as synthetic zero-arg Defns.
        let working_program = Self::wrap_exprs_as_defns(program);

        // Create per-module accumulator
        let mut accumulator = ModuleCheckAccumulator::new();

        // Pass 1: Register all forms in source order
        for form in &working_program {
            let result = self.check_form_register(state, form, &mut accumulator)?;
            self.merge_form_result_inner(state, &mut accumulator, result);
        }

        // Register default method defns generated during Pass 1 TraitImpl processing.
        // These need Pass 1 signature registration too.
        let defaults: Vec<Defn> = std::mem::take(&mut accumulator.default_method_defns);
        for defn in &defaults {
            let form = TopLevel::Defn(defn.clone());
            let result = self.check_form_register(state, &form, &mut accumulator)?;
            self.merge_form_result_inner(state, &mut accumulator, result);
        }
        // Put defaults back so finalize knows about them
        accumulator.default_method_defns = defaults;

        // Pass 2: Check bodies for all forms
        for form in &working_program {
            let result = self.check_form_body(state, form, &mut accumulator)?;
            self.merge_form_result_inner(state, &mut accumulator, result);
        }

        // Check bodies of default method defns too.
        let defaults_for_body: Vec<Defn> = accumulator.default_method_defns.clone();
        for defn in &defaults_for_body {
            let form = TopLevel::Defn(defn.clone());
            let result = self.check_form_body(state, &form, &mut accumulator)?;
            self.merge_form_result_inner(state, &mut accumulator, result);
        }

        // Finalize: run post-passes (generalization, overload resolution, monomorphisation,
        // auto-curry) and build CheckResult.
        let mut result = self.finalize_check_result_inner(
            state, &mut accumulator, &working_program, strategy,
        )?;

        // Populate display info
        result.display = self.compute_display_info(state, program, &accumulator.defn_type_vars);

        Ok(result)
    }

    /// Wrap `Expr` variants as synthetic zero-arg `Defn` named `__expr`.
    fn wrap_exprs_as_defns(program: &[TopLevel]) -> Vec<TopLevel> {
        let mut working_program = Vec::with_capacity(program.len());
        for top in program {
            match top {
                TopLevel::Expr(expr) => {
                    let span = expr.span();
                    let wrapper_span = Span::new(
                        span.start.saturating_sub(1),
                        span.end.saturating_add(1),
                    );
                    let synthetic_defn = Defn {
                        name: Symbol::from("__expr"),
                        docstring: None,
                        variants: vec![DefnVariant {
                            params: vec![],
                            param_annotations: vec![],
                            body: expr.clone(),
                            span,
                        }],
                        visibility: Visibility::Public,
                        span: wrapper_span,
                    };
                    working_program.push(TopLevel::Defn(synthetic_defn));
                }
                other => {
                    working_program.push(other.clone());
                }
            }
        }
        working_program
    }

    /// Compute DisplayInfo from the last form in the program.
    ///
    /// Populated when the input has 1-2 elements (REPL-like input).
    /// For batch programs (many forms), returns None.
    fn compute_display_info(
        &self,
        state: &CheckState,
        original_program: &[TopLevel],
        defn_type_vars: &HashMap<Symbol, (Vec<Type>, Type)>,
    ) -> Option<DisplayInfo> {
        if original_program.len() > 2 {
            return None;
        }

        let last = original_program.last()?;
        match last {
            TopLevel::Expr(_expr) => {
                // The synthetic __expr defn was registered — look up its type.
                if let Some((_param_tys, ret_ty)) = defn_type_vars.get(&Symbol::from("__expr")) {
                    let resolved = self.apply_subst(state, ret_ty);
                    Some(DisplayInfo {
                        ty: resolved,
                        scheme: None,
                    })
                } else {
                    None
                }
            }
            TopLevel::Defn(defn) => {
                // Look up the defn's generalized scheme from the symbol table.
                if let Some(ModuleEntry::Def { scheme, .. }) =
                    self.current_symbol_table(state).get(defn.name.as_ref())
                {
                    Some(DisplayInfo {
                        ty: scheme.ty.clone(),
                        scheme: Some(scheme.clone()),
                    })
                } else {
                    None
                }
            }
            TopLevel::TypeDef { name, .. } => {
                let fqtn = cranelisp_types::FQTypeName::new(
                    state.current_module.clone(), name.clone(),
                );
                let ty = Type::ADT(fqtn, vec![]);
                Some(DisplayInfo { ty, scheme: None })
            }
            TopLevel::TraitDecl(_) => {
                Some(DisplayInfo { ty: Type::Bool, scheme: None })
            }
            TopLevel::TraitImpl(_) => {
                Some(DisplayInfo { ty: Type::Bool, scheme: None })
            }
        }
    }

    /// Public wrapper for `clear_module_for_replace` (used by v4 worker).
    pub fn clear_module_for_replace_public(&self, state: &mut CheckState) {
        self.clear_module_for_replace(state);
    }

    /// Public wrapper for `compute_display_info` (used by v4 worker).
    pub fn compute_display_info_public(
        &self,
        state: &CheckState,
        original_program: &[TopLevel],
        defn_type_vars: &HashMap<Symbol, (Vec<Type>, Type)>,
    ) -> Option<DisplayInfo> {
        self.compute_display_info(state, original_program, defn_type_vars)
    }

    /// Prepare module for Replace strategy.
    ///
    /// The symbol table is preserved — existing entries guide GOT slot
    /// reuse and enable type-change detection during re-registration.
    /// GOT zeroing and codegen artifact cleanup happen at the worker
    /// level (worker.rs) which has access to SharedCodegenState.
    ///
    /// After re-processing, symbols present in the old table but absent
    /// from the new source are stale and should be invalidated.
    fn clear_module_for_replace(&self, _state: &mut CheckState) {
        // Symbol table intentionally NOT cleared.
        // Slot assignments and type info are needed for correct re-registration.
        // See worker.rs clear_module_codegen() for the GOT/codegen side.
    }

    /// Collect only single-sig Defn entries (skip multi-sig).
    fn collect_single_sig_defns(program: &[TopLevel]) -> Vec<&Defn> {
        program
            .iter()
            .filter_map(|top| {
                if let TopLevel::Defn(defn) = top {
                    if defn.is_multi_sig() {
                        None
                    } else {
                        Some(defn)
                    }
                } else {
                    None
                }
            })
            .collect()
    }

    /// Expand multi-sig defns into synthetic single-variant defns with
    /// internal names (`name__v0`, `name__v1`, ...).
    ///
    /// Also populates `self.overloads` with the base name → internal name
    /// mapping for later overload resolution.
    ///
    /// Returns owned `Vec<Defn>` — the caller holds references into this vec
    /// alongside the single-sig defn references from the program.
    ///
    /// Note: Superseded by `check_form_register_multi_sig` for the `check()` path.
    /// Retained for the deprecated `check_program` path used in tests.
    #[allow(dead_code)]
    fn expand_multi_sig_defns(&self,
        state: &mut CheckState, program: &[TopLevel]) -> Vec<Defn> {
        let mut internal_defns = Vec::new();

        for top in program {
            if let TopLevel::Defn(defn) = top {
                if !defn.is_multi_sig() {
                    continue;
                }

                let mut overload_entries = Vec::new();
                for (i, variant) in defn.variants.iter().enumerate() {
                    let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
                    overload_entries.push((internal_name.clone(), variant.params.len()));

                    internal_defns.push(Defn {
                        name: internal_name,
                        docstring: defn.docstring.clone(),
                        variants: vec![DefnVariant {
                            params: variant.params.clone(),
                            param_annotations: variant.param_annotations.clone(),
                            body: variant.body.clone(),
                            span: variant.span,
                        }],
                        visibility: defn.visibility,
                        span: variant.span,
                    });
                }
                state.overloads.insert(defn.name.clone(), overload_entries);

                // Register a placeholder for the base name so `infer_var`
                // can find it during pass 2. The placeholder uses a fresh
                // type variable — the actual type is determined during
                // overload resolution after pass 2.
                let placeholder_ty = self.fresh_var();
                let placeholder_scheme = mono(placeholder_ty);
                self.current_symbol_table_mut(state).insert(
                    defn.name.clone(),
                    ModuleEntry::Def {
                        scheme: placeholder_scheme,
                        visibility: defn.visibility,
                        docstring: defn.docstring.clone(),
                        param_names: vec![],
                        kind: Box::new(DefKind::Overloaded { variants: vec![] }),
                        callees: Vec::new(),
                        got_slot: None,
                        trait_origin: None,
                        ast: None,
                        code: None,
                    },
                );
            }
        }

        internal_defns
    }

    /// Resolve multi-sig overloads after pass 2: build mangled names from
    /// concrete types, check for duplicates, register mangled names in symbol
    /// table, and populate `resolved_overloads`.
    ///
    /// Returns a list of mangled Defn objects that the backend should compile.
    fn resolve_multi_sig_overloads(
        &self,
        state: &mut CheckState,
        program: &[TopLevel],
        type_vars: &HashMap<Symbol, (Vec<Type>, Type)>,
    ) -> Result<Vec<Defn>, CranelispError> {
        let mut result_defns = Vec::new();

        for top in program {
            if let TopLevel::Defn(defn) = top {
                if !defn.is_multi_sig() {
                    continue;
                }

                let resolved = self.resolve_variant_types(state, defn, type_vars)?;
                let (mangled_defns, resolved_info) =
                    self.register_mangled_variants(state, defn, &resolved);
                result_defns.extend(mangled_defns);
                self.register_overloaded_base(state, defn, resolved_info);
            }
        }

        Ok(result_defns)
    }

    /// For a single multi-sig defn, resolve each variant's concrete param/return
    /// types by applying substitution, and check for duplicate signatures.
    ///
    /// Returns a vec of `(concrete_params, concrete_ret, internal_name, variant_index)`
    /// for each variant.
    fn resolve_variant_types(
        &self,
        state: &CheckState,
        defn: &Defn,
        type_vars: &HashMap<Symbol, (Vec<Type>, Type)>,
    ) -> Result<Vec<ResolvedVariant>, CranelispError> {
        let mut resolved = Vec::new();
        let mut sig_set: Vec<Vec<Type>> = Vec::new();

        for (i, variant) in defn.variants.iter().enumerate() {
            let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));

            let (param_tys, ret_ty) = type_vars
                .get(&internal_name)
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!(
                        "internal: missing type vars for multi-sig variant {}",
                        internal_name
                    ),
                    location: ErrorLocation::from_span(variant.span),
                })?;

            let concrete_params: Vec<Type> = param_tys
                .iter()
                .map(|t| self.apply_subst(state, t))
                .collect();
            let concrete_ret = self.apply_subst(state, ret_ty);

            // Check for duplicate signatures
            if sig_set.iter().any(|s| s == &concrete_params) {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "duplicate signature for '{}': ({})",
                        defn.name,
                        concrete_params
                            .iter()
                            .map(|t| format!("{t}"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    location: ErrorLocation::from_span(variant.span),
                });
            }
            sig_set.push(concrete_params.clone());

            resolved.push((concrete_params, concrete_ret, internal_name, i));
        }

        Ok(resolved)
    }

    /// For each resolved variant, compute the mangled name, update the symbol
    /// table (remove internal name, register mangled name), and build the
    /// mangled `Defn` for the backend.
    ///
    /// Returns `(mangled_defns, resolved_info)` where `resolved_info` is
    /// `(concrete_params, concrete_ret, mangled_name)` per variant.
    fn register_mangled_variants(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        resolved: &[ResolvedVariant],
    ) -> (Vec<Defn>, Vec<MangledVariantInfo>) {
        let mut mangled_defns = Vec::new();
        let mut resolved_info = Vec::new();

        for (concrete_params, concrete_ret, internal_name, idx) in resolved {
            let variant = &defn.variants[*idx];
            let mangled = mangle_sig(defn.name.as_ref(), concrete_params);

            let fn_ty = Type::Fn(
                concrete_params.clone(),
                Box::new(concrete_ret.clone()),
            );
            let scheme = self.generalize(state, &fn_ty);

            // Remove internal name, register mangled name.
            // Wave 0 (§9.3): capture the already-annotated `ast` from the
            // internal-name entry (`foo__v0`) and transfer it onto the mangled
            // entry, renaming `defn.name` to the mangled form. The internal
            // variant was fully annotated by `check_form_body_multi_sig` —
            // no re-annotation needed here.
            let mut st = self.current_symbol_table_mut(state);
            let internal_entry = st.symbols.remove(internal_name.as_ref());
            let annotated_ast: Option<Defn> = match internal_entry {
                Some(ModuleEntry::Def { ast, .. }) => {
                    ast.map(|mut d| {
                        d.name = mangled.clone();
                        d
                    })
                }
                _ => None,
            };
            let slot = st.allocate_got_slot();
            st.insert(
                mangled.clone(),
                ModuleEntry::Def {
                    scheme: scheme.clone(),
                    visibility: defn.visibility,
                    docstring: defn.docstring.clone(),
                    param_names: variant.params.clone(),
                    kind: Box::new(DefKind::UserFn {
                        constrained_fn: None,
                    }),
                    callees: Vec::new(),
                    got_slot: Some(slot),
                    trait_origin: None,
                    ast: annotated_ast,
                    code: None,
                },
            );

            // Build the mangled defn for the backend
            mangled_defns.push(Defn {
                name: mangled.clone(),
                docstring: defn.docstring.clone(),
                variants: vec![DefnVariant {
                    params: variant.params.clone(),
                    param_annotations: variant.param_annotations.clone(),
                    body: variant.body.clone(),
                    span: variant.span,
                }],
                visibility: defn.visibility,
                span: variant.span,
            });

            resolved_info.push((concrete_params.clone(), concrete_ret.clone(), mangled));
        }

        (mangled_defns, resolved_info)
    }

    /// Build `OverloadVariant` entries, register the base name as `Overloaded`
    /// in the symbol table, and record resolved overloads in state.
    fn register_overloaded_base(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        resolved: Vec<(Vec<Type>, Type, Symbol)>,
    ) {
        let overload_variants = resolved
            .iter()
            .map(|(params, ret, mangled)| {
                cranelisp_types::OverloadVariant {
                    param_types: params.clone(),
                    ret_type: ret.clone(),
                    mangled_name: mangled.clone(),
                }
            })
            .collect();

        // Build a union scheme for the base name — use first variant's
        // scheme for now. The base name is registered as Overloaded so
        // `infer_apply` detects it and records a pending overload.
        let first_fn_ty = Type::Fn(
            resolved[0].0.clone(),
            Box::new(resolved[0].1.clone()),
        );
        let base_scheme = self.generalize(state, &first_fn_ty);

        self.current_symbol_table_mut(state).insert(
            defn.name.clone(),
            ModuleEntry::Def {
                scheme: base_scheme,
                visibility: defn.visibility,
                docstring: defn.docstring.clone(),
                param_names: vec![],
                kind: Box::new(DefKind::Overloaded {
                    variants: overload_variants,
                }),
                callees: Vec::new(),
                got_slot: None,
                trait_origin: None,
                ast: None,
                code: None,
            },
        );

        state.resolved_overloads.insert(
            defn.name.clone(),
            resolved,
        );
    }

    /// Resolve pending overload dispatch resolutions.
    ///
    /// For each pending `(span, base_name, arg_types, ret_type_var)`, find
    /// the matching variant and record `SigDispatch` in method_resolutions.
    fn resolve_pending_overloads(&self, state: &mut CheckState) -> Result<(), CranelispError> {
        let pending = std::mem::take(&mut state.pending_overload_resolutions);

        for (span, base_name, arg_types, ret_type_var) in &pending {
            let concrete_args: Vec<Type> = arg_types
                .iter()
                .map(|t| apply(&state.subst, t))
                .collect();

            let variants = state
                .resolved_overloads
                .get(base_name)
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!("no overloaded function: {}", base_name),
                    location: ErrorLocation::from_span(*span),
                })?
                .clone();

            // Find exact arity + type matches
            let mut exact_matches: Vec<&(Vec<Type>, Type, Symbol)> = Vec::new();

            for variant in &variants {
                let (param_types, _ret_ty, _mangled) = variant;
                if param_types.len() == concrete_args.len() {
                    let compatible = param_types
                        .iter()
                        .zip(concrete_args.iter())
                        .all(|(p, a)| types_compatible(p, a));
                    if compatible {
                        exact_matches.push(variant);
                    }
                }
            }

            if exact_matches.len() == 1 {
                let (param_types, ret_ty, mangled_name) = exact_matches[0];
                // Unify to bind type variables
                for (p, a) in param_types.iter().zip(concrete_args.iter()) {
                    self.unify(state, p, a, *span)?;
                }
                self.unify(state, ret_type_var, ret_ty, *span)?;
                state.method_resolutions.insert(
                    *span,
                    ResolvedCall::SigDispatch {
                        mangled_name: JitSymbol::from(mangled_name.as_ref()),
                    },
                );
            } else if exact_matches.len() > 1 {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "ambiguous call to '{}' — {} matching signatures",
                        base_name,
                        exact_matches.len()
                    ),
                    location: ErrorLocation::from_span(*span),
                });
            } else {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "no matching signature for '{}' with arg types ({})",
                        base_name,
                        concrete_args
                            .iter()
                            .map(|t| format!("{t}"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    location: ErrorLocation::from_span(*span),
                });
            }
        }

        Ok(())
    }

    /// Check a complete program (batch mode).
    ///
    /// Two-pass pipeline:
    /// 1. Register type definitions and function signatures.
    /// 2. Check function bodies, generalize types.
    #[deprecated(note = "use check() instead — unified pipeline entry point")]
    #[must_use = "check result contains expr_types and method_resolutions needed by codegen"]
    pub(crate) fn check_program(
        &self,
        state: &mut CheckState,
        program: &[TopLevel],
    ) -> Result<CheckResult, CranelispError> {
        self.check_program_inner(state, program)
    }

    fn check_program_inner(
        &self,
        state: &mut CheckState,
        program: &[TopLevel],
    ) -> Result<CheckResult, CranelispError> {
        // Pass 1: register type definitions
        self.register_type_defs_from_program(state, program)?;

        // Pass 1: register trait declarations
        self.register_trait_decls_from_program(state, program)?;

        // Pass 1: register trait implementations.
        // Side effect: registers default-method defns on the symbol table.
        // The returned Vec<Defn> was carried on CheckResult.default_method_defns
        // pre-slim (Sprint 57 Wave 2 step 4); no longer needed.
        let _default_defns =
            self.register_trait_impls_from_program(state, program)?;

        // Pass 1: register function signatures with fresh type variables
        let defns = Self::collect_defns(program);
        let defn_type_vars = self.pass1_register_signatures(state, &defns)?;

        // Pass 2: check function bodies and generalize
        self.pass2_check_bodies(state, &defns, &defn_type_vars)?;

        // Pass 3: detect constrained polymorphic functions
        let constrained_fn_names =
            self.detect_constrained_fns(state, &defns);

        // Pass 4: monomorphise constrained function call sites.
        // Side effect: registers mono specialisations on the symbol table via
        // `register_mono_entry` inside `monomorphise_call`. The returned
        // Vec<MonoDefn> was carried on CheckResult.mono_defns pre-slim; no
        // longer needed — annotated mono ASTs already live on SymbolTable.
        let _mono_defns = self.pass4_monomorphise(state, &defns, &constrained_fn_names)?;

        // Pass 5: resolve auto-curry sites into method_resolutions
        self.resolve_auto_curry(state);

        let resolved_expr_types = self.resolve_expr_types(state);

        // Step 1b: Annotate AST nodes and write to ModuleEntry::Def.ast
        {
            let sym_table = &mut self.current_symbol_table_mut(state);
            for top in program {
                match top {
                    TopLevel::Defn(defn) if defn.is_multi_sig() => {
                        for (i, variant) in defn.variants.iter().enumerate() {
                            let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
                            let mut variant_defn = Defn {
                                name: internal_name.clone(),
                                docstring: defn.docstring.clone(),
                                variants: vec![DefnVariant {
                                    params: variant.params.clone(),
                                    param_annotations: variant.param_annotations.clone(),
                                    body: variant.body.clone(),
                                    span: variant.span,
                                }],
                                visibility: defn.visibility,
                                span: variant.span,
                            };
                            annotate_defn_from_maps(
                                &mut variant_defn,
                                &resolved_expr_types,
                                &state.method_resolutions,
                            );
                            apply_subst_to_defn(&state.subst, &mut variant_defn);
                            if let Some(ModuleEntry::Def { ast, .. }) =
                                sym_table.symbols.get_mut(&internal_name)
                            {
                                *ast = Some(variant_defn);
                            }
                        }
                    }
                    TopLevel::Defn(defn) => {
                        let mut annotated = defn.clone();
                        annotate_defn_from_maps(
                            &mut annotated,
                            &resolved_expr_types,
                            &state.method_resolutions,
                        );
                        apply_subst_to_defn(&state.subst, &mut annotated);
                        if let Some(ModuleEntry::Def { ast, .. }) =
                            sym_table.symbols.get_mut(&defn.name)
                        {
                            *ast = Some(annotated);
                        }
                    }
                    TopLevel::TraitImpl(ti) => {
                        for method in &ti.methods {
                            let mangled = format!("{}.{}${}", ti.trait_name, method.name, ti.target_type);
                            let mangled_sym = Symbol::from(mangled.as_str());
                            let mut annotated = method.clone();
                            annotated.name = mangled_sym.clone();
                            annotate_defn_from_maps(
                                &mut annotated,
                                &resolved_expr_types,
                                &state.method_resolutions,
                            );
                            apply_subst_to_defn(&state.subst, &mut annotated);
                            if let Some(ModuleEntry::Def { ast, .. }) =
                                sym_table.symbols.get_mut(&mangled_sym)
                            {
                                *ast = Some(annotated);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        // Sprint 57 Wave 2 step 4: mono defn ASTs are already annotated by
        // `monomorphise_call` and written onto the symbol table by
        // `register_mono_entry` before reaching this point. The previous
        // re-annotation loop over `mono_defns` only existed to feed
        // `CheckResult.mono_defns`; the slimmed CheckResult no longer carries
        // that field. `constrained_fn_names` / `resolved_expr_types` locals
        // above similarly have no boundary consumer post-slim.
        let _ = constrained_fn_names;
        let _ = resolved_expr_types;

        Ok(CheckResult {
            warnings: std::mem::take(&mut state.warnings),
            display: None,
        })
    }

    /// Check a single REPL input incrementally.
    #[deprecated(note = "use check() instead — unified pipeline entry point")]
    #[must_use = "check result contains type and expr_types needed by codegen"]
    pub(crate) fn check_repl_input(
        &self,
        state: &mut CheckState,
        input: &TopLevel,
    ) -> Result<CheckResult, CranelispError> {
        self.check_repl_input_inner(state, input)
    }

    fn check_repl_input_inner(
        &self,
        state: &mut CheckState,
        input: &TopLevel,
    ) -> Result<CheckResult, CranelispError> {
        match input {
            TopLevel::Expr(expr) => {
                let ty = self.infer_expr(state, expr)?;
                let resolved = self.apply_subst(state, &ty);

                // Resolve auto-curry sites before building result.
                self.resolve_auto_curry(state);

                // Gap 4: scan for constrained-fn calls, monomorphise on demand.
                // Side effect: registers mono specialisations on the symbol
                // table via `register_mono_entry`. Returned Vec<MonoDefn> was
                // carried on CheckResult.mono_defns pre-slim (Wave 2 step 4).
                let _mono_defns = self.monomorphise_expr_calls(state, expr)?;

                Ok(self.build_repl_result(state, resolved, None))
            }

            TopLevel::Defn(defn) if defn.is_multi_sig() => {
                self.check_repl_multi_sig(state, defn)
            }

            TopLevel::Defn(defn) => {
                let (ty, scheme) = self.check_single_defn(state, defn)?;

                // Resolve auto-curry sites before building result.
                self.resolve_auto_curry(state);

                // Scan defn body for constrained-fn calls, monomorphise on demand.
                // Side effect: registers mono specialisations on the symbol
                // table via `register_mono_entry`. Returned Vec<MonoDefn> was
                // carried on CheckResult.mono_defns pre-slim (Wave 2 step 4).
                let _mono_defns = self.monomorphise_expr_calls(state, defn.body())?;

                // Step 1b: Annotate AST and write to ModuleEntry::Def.ast (REPL path)
                {
                    let resolved_expr_types = self.resolve_expr_types(state);
                    let mut annotated = defn.clone();
                    annotate_defn_from_maps(
                        &mut annotated,
                        &resolved_expr_types,
                        &state.method_resolutions,
                    );
                    apply_subst_to_defn(&state.subst, &mut annotated);
                    if let Some(ModuleEntry::Def { ast, .. }) =
                        self.current_symbol_table_mut(state).symbols.get_mut(&defn.name)
                    {
                        *ast = Some(annotated);
                    }
                }

                Ok(self.build_repl_result(state, ty, Some(scheme)))
            }

            TopLevel::TypeDef {
                name,
                docstring,
                type_params,
                constructors,
                visibility,
                span,
            } => {
                self.register_type_def(state, name, docstring, type_params, constructors, *visibility, *span)?;
                let fqtn = cranelisp_types::FQTypeName::new(
                    state.current_module.clone(), name.clone(),
                );
                let ty = Type::ADT(fqtn, vec![]);
                Ok(self.build_repl_result(state, ty, None))
            }

            TopLevel::TraitDecl(decl) => {
                self.register_trait_decl(state, decl)?;
                let ty = Type::Bool; // Placeholder return type for trait decl
                Ok(self.build_repl_result(state, ty, None))
            }

            TopLevel::TraitImpl(impl_) => {
                // Side effect: default method defns registered on symbol table
                // via `register_trait_impl`. Returned Vec<Defn> was carried on
                // CheckResult.default_method_defns pre-slim (Wave 2 step 4).
                let _default_defns = self.register_trait_impl(state, impl_)?;
                let ty = Type::Bool; // Placeholder return type for trait impl
                Ok(self.build_repl_result(state, ty, None))
            }
        }
    }

    // --- Pass 1: Registration ---

    /// Register all TypeDef entries from the program.
    fn register_type_defs_from_program(
        &self,
        state: &mut CheckState,
        program: &[TopLevel],
    ) -> Result<(), CranelispError> {
        for top in program {
            if let TopLevel::TypeDef {
                name,
                docstring,
                type_params,
                constructors,
                visibility,
                span,
            } = top
            {
                self.register_type_def(
                    state,
                    name,
                    docstring,
                    type_params,
                    constructors,
                    *visibility,
                    *span,
                )?;
            }
        }
        Ok(())
    }

    /// Register all TraitDecl entries from the program.
    fn register_trait_decls_from_program(
        &self,
        state: &mut CheckState,
        program: &[TopLevel],
    ) -> Result<(), CranelispError> {
        for top in program {
            if let TopLevel::TraitDecl(decl) = top {
                self.register_trait_decl(state, decl)?;
            }
        }
        Ok(())
    }

    /// Register all TraitImpl entries from the program.
    /// Returns default method definitions generated.
    fn register_trait_impls_from_program(
        &self,
        state: &mut CheckState,
        program: &[TopLevel],
    ) -> Result<Vec<Defn>, CranelispError> {
        let mut default_defns = Vec::new();
        for top in program {
            if let TopLevel::TraitImpl(impl_) = top {
                let defaults = self.register_trait_impl(state, impl_)?;
                default_defns.extend(defaults);
            }
        }
        Ok(default_defns)
    }

    /// Detect constrained polymorphic functions after generalization.
    ///
    /// A function is constrained if its generalized scheme has non-empty constraints.
    /// These functions are stored with `ConstrainedFn` in their DefKind.
    fn detect_constrained_fns(
        &self,
        state: &mut CheckState,
        defns: &[&Defn],
    ) -> HashSet<Symbol> {
        // Constrained functions are eagerly marked in pass2_check_bodies
        // by checking DefKind::UserFn { constrained_fn: Some(..) }.
        let mut names = HashSet::new();

        for defn in defns {
            if let Some(ModuleEntry::Def { kind, .. }) =
                self.current_symbol_table(state).get(defn.name.as_ref())
                && let DefKind::UserFn { constrained_fn: Some(_) } = kind.as_ref()
            {
                names.insert(defn.name.clone());
            }
        }

        names
    }

    /// Collect all Defn entries from the program.
    fn collect_defns(program: &[TopLevel]) -> Vec<&Defn> {
        program
            .iter()
            .filter_map(|top| {
                if let TopLevel::Defn(defn) = top {
                    // Skip multi-sig defns — not supported in Ring 0 batch path
                    if defn.is_multi_sig() {
                        None
                    } else {
                        Some(defn)
                    }
                } else {
                    None
                }
            })
            .collect()
    }

    /// Create fresh type variables for a function's parameters and return type,
    /// respecting any annotations, and register the signature in the symbol table.
    ///
    /// Returns `(param_types, return_type)` for use in body checking.
    /// Shared by `pass1_register_signatures` (batch) and `check_single_defn` (REPL)
    /// to prevent the two paths from diverging as rings add complexity.
    fn register_defn_signature(
        &self,
        state: &mut CheckState,
        defn: &Defn,
    ) -> Result<(Vec<Type>, Type), CranelispError> {
        // Fast path for trait impl (mangled) methods: if this symbol already
        // has a Def entry with `ast: Some(_)` and a concrete scheme (no free
        // vars / constraints), AND its name matches the trait-impl mangled
        // form `Trait.method$Type`, it was already type-checked by
        // `check_impl_method`. Reuse its param/ret types rather than
        // allocating fresh type vars — the fresh vars would never be unified
        // (CheckBody short-circuits on `ast: Some`) and would leave the symbol
        // with a spuriously polymorphic scheme after
        // `finalize_check_result_inner`'s generalization pass, breaking trait
        // dispatch (e.g., `(double true)` silently accepting any type).
        //
        // The name-pattern gate avoids false positives on `__expr` (REPL
        // synthetic) or regular user defns whose ast was annotated by a prior
        // REPL evaluation.
        if is_trait_impl_mangled_name(defn.name.as_ref()) {
            let st_ro = self.current_symbol_table(state);
            if let Some(ModuleEntry::Def { scheme, ast: Some(_), .. }) =
                st_ro.symbols.get(defn.name.as_ref())
                && scheme.vars.is_empty()
                && scheme.constraints.is_empty()
                && let Type::Fn(param_types, ret_ty) = &scheme.ty
            {
                return Ok((param_types.clone(), (**ret_ty).clone()));
            }
        }

        let mut param_types = Vec::new();
        for (i, _param) in defn.params().iter().enumerate() {
            let param_ty = if let Some(Some(ann)) = defn.param_annotations().get(i) {
                let known = self.known_type_names_with_state(state);
                let var_map = HashMap::new();
                resolve_type_expr(ann, &var_map, &known, defn.span)?
            } else {
                self.fresh_var()
            };
            param_types.push(param_ty);
        }
        let ret_ty = self.fresh_var();

        let fn_type = Type::Fn(param_types.clone(), Box::new(ret_ty.clone()));
        let scheme = mono(fn_type);

        // Upsert: preserve existing got_slot, ast, AND code if the symbol is being
        // redefined (REPL Additive mode, module reload, or trait impl method
        // re-registration). New symbols get a fresh slot. Preserving ast prevents
        // double-checking of trait impl methods that were already type-checked by
        // check_impl_method.
        //
        // Sprint 58 Wave 3b (Decision 35 / 31): preserving `code` is load-bearing
        // for failed-redefinition recovery. Pre-Wave-3b, `Arc<Jit>` lived in
        // `SharedState.kept_jits` (session-level); replacing the entry was a
        // pointer-swap and the JIT pages stayed alive at session level. Wave 3b
        // moves `Arc<Jit>` retention onto `Code::Jit` per-entry — replacing the
        // entry with `code: None` drops the Arc, and if no other entry referenced
        // it, the Jit's `Drop` calls `free_memory()` and the GOT slot's old
        // pointer (still in place during typecheck) becomes invalid. If the
        // redefinition then fails (type error), snapshot/restore reverts the
        // entry's keys but the GOT slot is already pointing at freed pages —
        // a subsequent call to the original defn segfaults.
        //
        // Carrying the existing `code` forward through registration preserves
        // the Arc; on success, codegen overwrites it with the new `Code::Jit`;
        // on failure, restore keeps the carried-forward (original) `code`,
        // and the GOT slot remains valid because the Arc never dropped.
        let mut st = self.current_symbol_table_mut(state);
        let (existing_slot, existing_ast, existing_code) = st.get(defn.name.as_ref())
            .map(|e| match e {
                ModuleEntry::Def { got_slot, ast, code, .. } => (*got_slot, ast.clone(), code.clone()),
                _ => (None, None, None),
            })
            .unwrap_or((None, None, None));
        let got_slot = Some(existing_slot.unwrap_or_else(|| st.allocate_got_slot()));

        st.insert(
            defn.name.clone(),
            ModuleEntry::Def {
                scheme,
                visibility: defn.visibility,
                docstring: defn.docstring.clone(),
                param_names: defn.params().to_vec(),
                kind: Box::new(DefKind::UserFn {
                    constrained_fn: None,
                }),
                callees: Vec::new(),
                got_slot,
                trait_origin: None,
                ast: existing_ast,
                code: existing_code,
            },
        );

        Ok((param_types, ret_ty))
    }

    /// Pass 1: Register function signatures with fresh type variables.
    ///
    /// Returns a map from function name to (param type vars, return type var)
    /// for use in Pass 2.
    fn pass1_register_signatures(
        &self,
        state: &mut CheckState,
        defns: &[&Defn],
    ) -> Result<HashMap<Symbol, (Vec<Type>, Type)>, CranelispError> {
        let mut type_vars = HashMap::new();

        for defn in defns {
            let (param_types, ret_ty) = self.register_defn_signature(state, defn)?;
            type_vars.insert(defn.name.clone(), (param_types, ret_ty));
        }

        Ok(type_vars)
    }

    /// Pass 2: Check function bodies and generalize types.
    ///
    /// All bodies are checked first (with deferred trait resolution), then
    /// all functions are generalized.
    ///
    /// After each body check, we eagerly detect constrained polymorphism
    /// by checking if the function's type vars have active constraints.
    /// This must happen before later functions' call sites can pin the vars
    /// to concrete types through the shared substitution.
    fn pass2_check_bodies(
        &self,
        state: &mut CheckState,
        defns: &[&Defn],
        type_vars: &HashMap<Symbol, (Vec<Type>, Type)>,
    ) -> Result<(), CranelispError> {
        // Phase 1: Check all bodies, resolve deferred trait calls,
        // and eagerly mark constrained functions.
        for defn in defns {
            let (param_types, ret_ty) = type_vars
                .get(&defn.name)
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!("internal: missing type vars for {}", defn.name),
                    location: ErrorLocation::from_span(defn.span),
                })?;

            self.check_defn_body(state, defn, param_types, ret_ty)?;
            self.resolve_deferred_trait_calls(state, defn.body());

            // Eagerly detect if this function is constrained.
            // Must happen now, before later call sites resolve its type vars.
            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(state, t)).collect(),
                Box::new(self.apply_subst(state, ret_ty)),
            );
            let trial_scheme = self.generalize(state, &fn_type);
            if !trial_scheme.constraints.is_empty() {
                // Mark as constrained immediately
                if let Some(ModuleEntry::Def { kind, .. }) =
                    self.current_symbol_table_mut(state).symbols.get_mut(&defn.name)
                {
                    let cf = ConstrainedFn {
                        defn: (*defn).clone(),
                        scheme: trial_scheme,
                    };
                    **kind = DefKind::UserFn {
                        constrained_fn: Some(Box::new(cf)),
                    };
                }
            }
        }

        // Phase 2: Generalize all functions.
        // If the final scheme has no constraints, clear any eager constrained_fn marker
        // (later call sites may have pinned the type vars to concrete types).
        for defn in defns {
            let (param_types, ret_ty) = type_vars.get(&defn.name).unwrap();
            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(state, t)).collect(),
                Box::new(self.apply_subst(state, ret_ty)),
            );
            let scheme = self.generalize(state, &fn_type);
            if let Some(ModuleEntry::Def { scheme: s, kind, .. }) =
                self.current_symbol_table_mut(state).symbols.get_mut(&defn.name)
            {
                *s = scheme.clone();
                // Clear eager constrained marker if final scheme is unconstrained
                if scheme.constraints.is_empty()
                    && let DefKind::UserFn { constrained_fn: Some(_) } = kind.as_ref()
                {
                    **kind = DefKind::UserFn { constrained_fn: None };
                }
            }
        }

        // Phase 3: Re-resolve deferred trait calls now that all types are pinned.
        // During Phase 1, some trait method calls (e.g., `+` in `add`) couldn't be
        // resolved because arg types were still unresolved vars. After Phase 2,
        // later call sites may have pinned those vars to concrete types.
        for defn in defns {
            self.resolve_deferred_trait_calls(state, defn.body());
        }

        Ok(())
    }

    /// Check a single function definition body.
    fn check_defn_body(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        param_types: &[Type],
        ret_ty: &Type,
    ) -> Result<(), CranelispError> {
        self.push_scope(state);

        // Bind parameters
        for (param_name, param_ty) in defn.params().iter().zip(param_types.iter()) {
            self.bind_local(state, param_name.clone(), mono(param_ty.clone()));
        }

        // Bind the function name for recursion
        let fn_type = Type::Fn(param_types.to_vec(), Box::new(ret_ty.clone()));
        self.bind_local(state, defn.name.clone(), mono(fn_type));

        // Infer body type
        let body_ty = self.infer_expr(state, defn.body())?;

        // Unify body type with return type variable
        self.unify(state, &body_ty, ret_ty, defn.span)?;

        self.pop_scope(state);

        // Record the defn's Fn type in expr_types so the backend can look up
        // authoritative parameter types. Without this, unused params (e.g.,
        // `_s` in `(defn f [:String _s] 42)`) have no type recorded and
        // scope cleanup skips their RC dec, causing leaks.
        let resolved_fn_type = Type::Fn(
            param_types.iter().map(|t| self.apply_subst(state, t)).collect(),
            Box::new(self.apply_subst(state, ret_ty)),
        );
        self.record_expr_type(state, defn.span, resolved_fn_type);

        Ok(())
    }

    /// Check a single defn for REPL (register, check, generalize in one step).
    fn check_single_defn(
        &self,
        state: &mut CheckState,
        defn: &Defn,
    ) -> Result<(Type, Scheme), CranelispError> {
        let (param_types, ret_ty) = self.register_defn_signature(state, defn)?;

        // Check body
        self.check_defn_body(state, defn, &param_types, &ret_ty)?;

        // Post-inference deferred trait resolution
        self.resolve_deferred_trait_calls(state, defn.body());

        // Generalize (propagates active constraints)
        let resolved_fn_type = Type::Fn(
            param_types.iter().map(|t| self.apply_subst(state, t)).collect(),
            Box::new(self.apply_subst(state, &ret_ty)),
        );
        let scheme = self.generalize(state, &resolved_fn_type);

        // Update symbol table with generalized scheme
        // If constrained, also store as ConstrainedFn
        if let Some(ModuleEntry::Def { scheme: s, kind, .. }) =
            self.current_symbol_table_mut(state).symbols.get_mut(&defn.name)
        {
            *s = scheme.clone();

            if !scheme.constraints.is_empty() {
                let cf = ConstrainedFn {
                    defn: defn.clone(),
                    scheme: scheme.clone(),
                };
                **kind = DefKind::UserFn {
                    constrained_fn: Some(Box::new(cf)),
                };
            }
        }

        Ok((scheme.ty.clone(), scheme))
    }

    /// Check a multi-sig defn for REPL: register variants, check bodies,
    /// resolve overloads, and build the result — all in one step.
    fn check_repl_multi_sig(
        &self,
        state: &mut CheckState,
        defn: &Defn,
    ) -> Result<CheckResult, CranelispError> {
        // Phase 1: Register each variant's signature
        let mut defn_type_vars = HashMap::new();
        let mut overload_entries = Vec::new();
        for (i, variant) in defn.variants.iter().enumerate() {
            let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
            overload_entries.push((internal_name.clone(), variant.params.len()));

            let internal_defn = Defn {
                name: internal_name.clone(),
                docstring: defn.docstring.clone(),
                variants: vec![DefnVariant {
                    params: variant.params.clone(),
                    param_annotations: variant.param_annotations.clone(),
                    body: variant.body.clone(),
                    span: variant.span,
                }],
                visibility: defn.visibility,
                span: variant.span,
            };
            let (param_types, ret_ty) = self.register_defn_signature(state, &internal_defn)?;
            defn_type_vars.insert(internal_name, (param_types, ret_ty));
        }
        state.overloads.insert(defn.name.clone(), overload_entries);

        // Register a placeholder for the base name
        let placeholder_ty = self.fresh_var();
        let placeholder_scheme = mono(placeholder_ty);
        self.current_symbol_table_mut(state).insert(
            defn.name.clone(),
            ModuleEntry::Def {
                scheme: placeholder_scheme,
                visibility: defn.visibility,
                docstring: defn.docstring.clone(),
                param_names: vec![],
                kind: Box::new(DefKind::Overloaded { variants: vec![] }),
                callees: Vec::new(),
                got_slot: None,
                trait_origin: None,
                ast: None,
                code: None,
            },
        );

        // Phase 2: Check each variant body
        for (i, variant) in defn.variants.iter().enumerate() {
            let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
            let (param_types, ret_ty) = defn_type_vars
                .get(&internal_name)
                .expect("internal: missing type vars for multi-sig variant");

            let internal_defn = Defn {
                name: internal_name.clone(),
                docstring: defn.docstring.clone(),
                variants: vec![DefnVariant {
                    params: variant.params.clone(),
                    param_annotations: variant.param_annotations.clone(),
                    body: variant.body.clone(),
                    span: variant.span,
                }],
                visibility: defn.visibility,
                span: variant.span,
            };

            self.check_defn_body(state, &internal_defn, param_types, ret_ty)?;
            self.resolve_deferred_trait_calls(state, internal_defn.body());
        }

        // Phase 2.5: Resolve multi-sig overloads (mangle names, register).
        // Side effect: `register_mangled_variants` writes mangled entries onto
        // the symbol table. Returned Vec<Defn> was carried on
        // CheckResult.default_method_defns pre-slim (Wave 2 step 4).
        let resolved = self.resolve_variant_types(state, defn, &defn_type_vars)?;
        let (_mangled_defns, resolved_info) =
            self.register_mangled_variants(state, defn, &resolved);
        self.register_overloaded_base(state, defn, resolved_info);

        // Resolve pending overloads and auto-curry
        self.resolve_pending_overloads(state)?;
        self.resolve_auto_curry(state);

        // Build the result using the first variant's type for display
        let first_variant_ty = if let Some((concrete_params, concrete_ret, _, _)) = resolved.first() {
            Type::Fn(concrete_params.clone(), Box::new(concrete_ret.clone()))
        } else {
            Type::Int // fallback — shouldn't happen
        };
        let scheme = self.generalize(state, &first_variant_ty);
        Ok(self.build_repl_result(state, first_variant_ty, Some(scheme)))
    }

    // --- Monomorphisation passes ---

    /// Pass 4 (batch): scan all defn bodies for calls to constrained functions
    /// and generate monomorphised specializations.
    fn pass4_monomorphise(
        &self,
        state: &mut CheckState,
        defns: &[&Defn],
        constrained_fn_names: &HashSet<Symbol>,
    ) -> Result<Vec<MonoDefn>, CranelispError> {
        if constrained_fn_names.is_empty() {
            return Ok(Vec::new());
        }

        // Collect call sites: (fn_name, arg_spans, call_span)
        let mut call_sites = Vec::new();
        for defn in defns {
            // Don't scan constrained fns for calls to themselves — those
            // are the generic definitions, not concrete call sites.
            if constrained_fn_names.contains(&defn.name) {
                continue;
            }
            Self::collect_constrained_calls(
                defn.body(),
                constrained_fn_names,
                &mut call_sites,
            );
        }

        // Resolve expr_types so we can look up concrete arg types
        let resolved_expr_types = self.resolve_expr_types(state);

        // Monomorphise each call site and record dispatch mappings
        let mut mono_defns = Vec::new();
        let mut seen: HashMap<String, JitSymbol> = HashMap::new();

        for (fn_name, arg_spans, call_span) in &call_sites {
            // Look up concrete arg types from resolved expr_types
            let arg_types: Vec<Type> = arg_spans
                .iter()
                .filter_map(|span| resolved_expr_types.get(span).cloned())
                .collect();

            if arg_types.len() != arg_spans.len() {
                // Missing type info for some args — skip this call site
                continue;
            }

            // Deduplicate: same fn + same arg types = same specialization
            let key = format!("{}${}", fn_name, arg_types.iter()
                .map(|t| format!("{}", t))
                .collect::<Vec<_>>()
                .join("+"));

            if let Some(mangled) = seen.get(&key) {
                // Already generated this specialization — just record dispatch
                state.method_resolutions.insert(
                    *call_span,
                    ResolvedCall::SigDispatch { mangled_name: mangled.clone() },
                );
                continue;
            }

            if let Some(mono) = self.monomorphise_call(state, fn_name, &arg_types, *call_span)? {
                let mangled = JitSymbol::from(mono.defn.name.as_ref());
                // Record dispatch for this call site
                state.method_resolutions.insert(
                    *call_span,
                    ResolvedCall::SigDispatch { mangled_name: mangled.clone() },
                );
                seen.insert(key, mangled);
                mono_defns.push(mono);
            }
        }

        Ok(mono_defns)
    }

    /// Scan an expression for calls to constrained functions (REPL path).
    ///
    /// Collects call sites, resolves arg types, and calls `monomorphise_call`
    /// for each. Used by both `check_repl_input(Expr)` and `check_repl_input(Defn)`.
    fn monomorphise_expr_calls(
        &self,
        state: &mut CheckState,
        expr: &Expr,
    ) -> Result<Vec<MonoDefn>, CranelispError> {
        // Build the set of constrained fn names from the symbol table
        let constrained_fn_names: HashSet<Symbol> = self.current_symbol_table(state).symbols
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

        if constrained_fn_names.is_empty() {
            return Ok(Vec::new());
        }

        let mut call_sites = Vec::new();
        Self::collect_constrained_calls(expr, &constrained_fn_names, &mut call_sites);

        if call_sites.is_empty() {
            return Ok(Vec::new());
        }

        let resolved_expr_types = self.resolve_expr_types(state);

        let mut mono_defns = Vec::new();
        let mut seen: HashMap<String, JitSymbol> = HashMap::new();

        for (fn_name, arg_spans, call_span) in &call_sites {
            let arg_types: Vec<Type> = arg_spans
                .iter()
                .filter_map(|span| resolved_expr_types.get(span).cloned())
                .collect();

            if arg_types.len() != arg_spans.len() {
                continue;
            }

            let key = format!("{}${}", fn_name, arg_types.iter()
                .map(|t| format!("{}", t))
                .collect::<Vec<_>>()
                .join("+"));

            if let Some(mangled) = seen.get(&key) {
                state.method_resolutions.insert(
                    *call_span,
                    ResolvedCall::SigDispatch { mangled_name: mangled.clone() },
                );
                continue;
            }

            if let Some(mono) = self.monomorphise_call(state, fn_name, &arg_types, *call_span)? {
                let mangled = JitSymbol::from(mono.defn.name.as_ref());
                state.method_resolutions.insert(
                    *call_span,
                    ResolvedCall::SigDispatch { mangled_name: mangled.clone() },
                );
                seen.insert(key, mangled);
                mono_defns.push(mono);
            }
        }

        Ok(mono_defns)
    }

    /// Recursively walk an expression tree collecting calls to constrained fns.
    ///
    /// Each call site is recorded as (fn_name, arg_spans, call_span).
    /// The arg_spans are the spans of each argument expression, used to look up
    /// their types from `expr_types`.
    pub(crate) fn collect_constrained_calls(
        expr: &Expr,
        constrained_fn_names: &HashSet<Symbol>,
        out: &mut Vec<(Symbol, Vec<Span>, Span)>,
    ) {
        match expr {
            Expr::Apply { callee, args, span, .. } => {
                // Check if callee is a constrained fn
                if let Expr::Var { name, .. } = callee.as_ref()
                    && constrained_fn_names.contains(name)
                {
                    let arg_spans: Vec<Span> = args.iter()
                        .map(|a| a.span())
                        .collect();
                    out.push((name.clone(), arg_spans, *span));
                }
                // Recurse into callee and args
                Self::collect_constrained_calls(callee, constrained_fn_names, out);
                for arg in args {
                    Self::collect_constrained_calls(arg, constrained_fn_names, out);
                }
            }
            Expr::Let { bindings, body, .. } => {
                for (_, binding_expr) in bindings {
                    Self::collect_constrained_calls(binding_expr, constrained_fn_names, out);
                }
                Self::collect_constrained_calls(body, constrained_fn_names, out);
            }
            Expr::If { cond, then_branch, else_branch, .. } => {
                Self::collect_constrained_calls(cond, constrained_fn_names, out);
                Self::collect_constrained_calls(then_branch, constrained_fn_names, out);
                Self::collect_constrained_calls(else_branch, constrained_fn_names, out);
            }
            Expr::Lambda { body, .. } => {
                Self::collect_constrained_calls(body, constrained_fn_names, out);
            }
            Expr::Match { scrutinee, arms, .. } => {
                Self::collect_constrained_calls(scrutinee, constrained_fn_names, out);
                for arm in arms {
                    Self::collect_constrained_calls(&arm.body, constrained_fn_names, out);
                }
            }
            Expr::Annotate { expr: inner, .. } => {
                Self::collect_constrained_calls(inner, constrained_fn_names, out);
            }
            Expr::VecLit { elements, .. } => {
                for elem in elements {
                    Self::collect_constrained_calls(elem, constrained_fn_names, out);
                }
            }
            Expr::Trace { body, .. } => {
                Self::collect_constrained_calls(body, constrained_fn_names, out);
            }
            Expr::ParBind { bindings, body, .. } => {
                for (_, binding_expr) in bindings {
                    Self::collect_constrained_calls(binding_expr, constrained_fn_names, out);
                }
                Self::collect_constrained_calls(body, constrained_fn_names, out);
            }
            // Leaf nodes: no children to recurse into
            Expr::IntLit { .. }
            | Expr::FloatLit { .. }
            | Expr::BoolLit { .. }
            | Expr::StringLit { .. }
            | Expr::Var { .. } => {}
        }
    }

    // --- Result building ---

    /// Drain pending auto-curry resolutions into method_resolutions.
    ///
    /// Each entry in `pending_auto_curry` records a call site where the
    /// typechecker detected partial application (fewer args than params).
    /// This converts them to `ResolvedCall::AutoCurry` entries that the
    /// backend can use for codegen.
    pub(crate) fn resolve_auto_curry(&self, state: &mut CheckState) {
        let pending = std::mem::take(&mut state.pending_auto_curry);
        for (span, name, applied_count, total_count, callee_ty, mut trait_resolution) in pending {
            // If the trait resolution wasn't determined earlier (types were
            // still unresolved vars during try_auto_curry), attempt it now.
            // Later unifications (e.g., from a call site like `(make-adder 10)`)
            // may have pinned the type vars to concrete types.
            if trait_resolution.is_none() {
                let resolved_callee = self.apply_subst(state, &callee_ty);
                if let Type::Fn(full_params, _) = &resolved_callee {
                    let resolved_params: Vec<Type> = full_params
                        .iter()
                        .map(|t| self.apply_subst(state, t))
                        .collect();
                    if let Ok(Some(r)) = self.try_resolve_trait_method(state, &name, &resolved_params, span) {
                        trait_resolution = Some(r);
                    } else if let Some(jit_name) = self.resolve_primitive_jit_name(state, &name) {
                        trait_resolution = Some(ResolvedCall::BuiltinFn { name: jit_name });
                    }
                }
            }

            state.method_resolutions.insert(
                span,
                ResolvedCall::AutoCurry {
                    target_name: name,
                    applied_count,
                    total_count,
                    trait_resolution: trait_resolution.map(Box::new),
                },
            );
        }
    }

    /// Resolve all recorded expr_types through the current substitution.
    fn resolve_expr_types(&self, state: &CheckState) -> HashMap<Span, Type> {
        state.expr_types
            .iter()
            .map(|(span, ty)| (*span, apply(&state.subst, ty)))
            .collect()
    }

    /// Build a CheckResult with display info from the current state (REPL path).
    ///
    /// Sprint 57 Wave 2 step 4: `CheckResult` slimmed to `{ warnings, display }`;
    /// typecheck-internal side maps (`method_resolutions`, `expr_types`, etc.)
    /// live on `CheckState` and are consumed in-place by downstream passes —
    /// they are no longer drained here.
    fn build_repl_result(
        &self,
        state: &mut CheckState,
        ty: Type,
        scheme: Option<Scheme>,
    ) -> CheckResult {
        CheckResult {
            warnings: std::mem::take(&mut state.warnings),
            display: Some(DisplayInfo { ty, scheme }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::checker::TestFixture;
    use cranelisp_types::{CompileContext, DefnVariant, Expr, FQTypeName, ImportNames, ImportSpec,
        ModuleFullPath, Symbol,
        TraitDecl, TraitImpl, TraitMethodSig, TraitName, TypeExpr, TypeName, Visibility,
    };

    /// Test helper: create an FQTypeName in the "test" module (used by tc_with_prims()).
    fn test_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("test"), TypeName::from(name))
    }

    fn span(start: u32, end: u32) -> Span {
        Span::new(start, end)
    }

    /// Create a single-sig Defn (convenience for tests).
    fn make_defn(
        name: &str,
        params: Vec<Symbol>,
        param_annotations: Vec<Option<TypeExpr>>,
        body: Expr,
        visibility: Visibility,
        span: Span,
    ) -> Defn {
        Defn {
            name: Symbol::from(name),
            docstring: None,
            variants: vec![DefnVariant {
                params,
                param_annotations,
                body,
                span,
            }],
            visibility,
            span,
        }
    }

    /// Create a TypeChecker with primitives imported into a "test" module.
    fn tc_with_prims() -> TestFixture {
        let mut tc = TestFixture::new();
        tc.set_current_module(ModuleFullPath::from("test"));
        let import_spec = ImportSpec {
            module_path: ModuleFullPath::from("primitives"),
            alias: None,
            names: ImportNames::Glob,
            span: Span::new(0, 0),
        };
        tc.register_imports_self(&[import_spec]).unwrap();
        tc
    }

    /// Test helper: walk an Expr tree, recording whether any node carries an
    /// `inferred_type` annotation and whether all annotations are resolved
    /// (no `Type::Var`). Used by tests that previously inspected
    /// `CheckResult.expr_types` — the post-slim equivalent is reading
    /// `inferred_type` from annotated AST nodes.
    fn walk_inferred_types(expr: &Expr, any_typed: &mut bool, all_resolved: &mut bool) {
        if let Some(ty) = expr.inferred_type() {
            *any_typed = true;
            if let Type::Var(_) = ty {
                *all_resolved = false;
            }
        }
        match expr {
            Expr::Apply { callee, args, .. } => {
                walk_inferred_types(callee, any_typed, all_resolved);
                for a in args {
                    walk_inferred_types(a, any_typed, all_resolved);
                }
            }
            Expr::If { cond, then_branch, else_branch, .. } => {
                walk_inferred_types(cond, any_typed, all_resolved);
                walk_inferred_types(then_branch, any_typed, all_resolved);
                walk_inferred_types(else_branch, any_typed, all_resolved);
            }
            Expr::Let { bindings, body, .. } => {
                for (_, bexpr) in bindings {
                    walk_inferred_types(bexpr, any_typed, all_resolved);
                }
                walk_inferred_types(body, any_typed, all_resolved);
            }
            Expr::Lambda { body, .. } => {
                walk_inferred_types(body, any_typed, all_resolved);
            }
            Expr::Match { scrutinee, arms, .. } => {
                walk_inferred_types(scrutinee, any_typed, all_resolved);
                for arm in arms {
                    walk_inferred_types(&arm.body, any_typed, all_resolved);
                }
            }
            Expr::VecLit { elements, .. } => {
                for e in elements {
                    walk_inferred_types(e, any_typed, all_resolved);
                }
            }
            Expr::Annotate { expr, .. } => {
                walk_inferred_types(expr, any_typed, all_resolved);
            }
            Expr::Trace { body, .. } => {
                walk_inferred_types(body, any_typed, all_resolved);
            }
            Expr::ParBind { bindings, body, .. } => {
                for (_, bexpr) in bindings {
                    walk_inferred_types(bexpr, any_typed, all_resolved);
                }
                walk_inferred_types(body, any_typed, all_resolved);
            }
            _ => {}
        }
    }

    /// Register a minimal Num trait with `+` method, plus an impl for Int,
    /// so tests using `(+ x y)` work after Decision 17 elimination.
    fn register_num_trait_inline(tc: &mut TestFixture) {
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
        tc.register_trait_decl_self(&num_decl).unwrap();

        // impl Num for Int: + → add-i64
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
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: Span::SYNTHETIC, inferred_type: None, },
                            Expr::Var { name: Symbol::from("y"), span: Span::SYNTHETIC, inferred_type: None, },
                        ],
                        span: Span::SYNTHETIC,
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        };
        tc.register_trait_impl_self(&impl_).unwrap();
        tc.clear_transient_state();
    }

    // spec: 05-definitions §5.1 — defn registers function with inferred type
    #[test]
    fn test_check_program_simple_defn() {
        let mut tc = tc_with_prims();
        // (defn add-one [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("add-one"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-i64"),
                        span: span(20, 27),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("x"),
                            span: span(28, 29),
                            inferred_type: None,
                        },
                        Expr::IntLit {
                            value: 1,
                            span: span(30, 31),
                            inferred_type: None,
                        },
                    ],
                    span: span(19, 32),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 33),
            }],
            visibility: Visibility::Public,
            span: span(0, 33),
        })];

        let _result = tc.check_program_self(&program).unwrap();

        // Check the function was registered with correct type: Fn([Int], Int)
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-one") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("add-one not found in symbol table");
        }
    }

    // spec: 03-types §3.4 — identity function generalized to polymorphic scheme
    #[test]
    fn test_check_program_identity_is_polymorphic() {
        let mut tc = tc_with_prims();
        // (defn id [x] x)
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("id"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(14, 15),
                    inferred_type: None,
                },
                span: span(0, 16),
            }],
            visibility: Visibility::Public,
            span: span(0, 16),
        })];

        tc.check_program_self(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("id") {
            // Should be forall [a]. Fn([a], a)
            assert_eq!(scheme.vars.len(), 1, "id should have 1 quantified var");
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 1);
                    assert_eq!(params[0], **ret);
                }
                _ => panic!("expected Fn type"),
            }
        } else {
            panic!("id not found in symbol table");
        }
    }

    // spec: 03-types §3.5.1 — recursive function inferred as monomorphic via self-reference
    #[test]
    fn test_check_program_recursive_function() {
        let mut tc = tc_with_prims();
        // (defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1)))))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("fact"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("n")],
                param_annotations: vec![None],
                body: Expr::If {
                    cond: Box::new(Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("eq-i64"),
                            span: span(20, 26),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var {
                                name: Symbol::from("n"),
                                span: span(27, 28),
                                inferred_type: None,
                            },
                            Expr::IntLit {
                                value: 0,
                                span: span(29, 30),
                                inferred_type: None,
                            },
                        ],
                        span: span(19, 31),
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    then_branch: Box::new(Expr::IntLit {
                        value: 1,
                        span: span(33, 34),
                        inferred_type: None,
                    }),
                    else_branch: Box::new(Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("mul-i64"),
                            span: span(36, 43),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var {
                                name: Symbol::from("n"),
                                span: span(44, 45),
                                inferred_type: None,
                            },
                            Expr::Apply {
                                callee: Box::new(Expr::Var {
                                    name: Symbol::from("fact"),
                                    span: span(47, 51),
                                    inferred_type: None,
                                }),
                                args: vec![Expr::Apply {
                                    callee: Box::new(Expr::Var {
                                        name: Symbol::from("sub-i64"),
                                        span: span(53, 60),
                                        inferred_type: None,
                                    }),
                                    args: vec![
                                        Expr::Var {
                                            name: Symbol::from("n"),
                                            span: span(61, 62),
                                            inferred_type: None,
                                        },
                                        Expr::IntLit {
                                            value: 1,
                                            span: span(63, 64),
                                            inferred_type: None,
                                        },
                                    ],
                                    span: span(52, 65),
                                    resolved_call: None,
                                    inferred_type: None,
                                }],
                                span: span(46, 66),
                                resolved_call: None,
                                inferred_type: None,
                            },
                        ],
                        span: span(35, 67),
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    span: span(15, 68),
                    inferred_type: None,
                },
                span: span(0, 69),
            }],
            visibility: Visibility::Public,
            span: span(0, 69),
        })];

        tc.check_program_self(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("fact") {
            assert!(
                scheme.vars.is_empty(),
                "fact should be monomorphic (Int -> Int)"
            );
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("fact not found in symbol table");
        }
    }

    // spec: 05-definitions §5.2 — deftype registers constructors and enables match
    #[test]
    fn test_check_program_with_typedef() {
        let mut tc = tc_with_prims();
        let program = vec![
            TopLevel::TypeDef {
                name: TypeName::from("Color"),
                docstring: None,
                type_params: vec![],
                constructors: vec![
                    cranelisp_types::ConstructorDef {
                        name: Symbol::from("Red"),
                        docstring: None,
                        fields: vec![],
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::ConstructorDef {
                        name: Symbol::from("Green"),
                        docstring: None,
                        fields: vec![],
                        span: Span::SYNTHETIC,
                    },
                ],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            },
            TopLevel::Defn(Defn {
                name: Symbol::from("is-red"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("c")],
                    param_annotations: vec![None],
                    body: Expr::Match {
                        scrutinee: Box::new(Expr::Var {
                            name: Symbol::from("c"),
                            span: span(30, 31),
                            inferred_type: None,
                        }),
                        arms: vec![
                            cranelisp_types::MatchArm {
                                pattern: cranelisp_types::Pattern::Constructor {
                                    name: Symbol::from("Red"),
                                    bindings: vec![],
                                    span: span(33, 36),
                                },
                                body: Expr::BoolLit {
                                    value: true,
                                    span: span(37, 41),
                                    inferred_type: None,
                                },
                                span: span(33, 41),
                            },
                            cranelisp_types::MatchArm {
                                pattern: cranelisp_types::Pattern::Wildcard {
                                    span: span(42, 43),
                                },
                                body: Expr::BoolLit {
                                    value: false,
                                    span: span(44, 49),
                                    inferred_type: None,
                                },
                                span: span(42, 49),
                            },
                        ],
                        span: span(24, 50),
                        compiler_generated: false,
                        inferred_type: None,
                    },
                    span: span(0, 51),
                }],
                visibility: Visibility::Public,
                span: span(0, 51),
            }),
        ];

        let _result = tc.check_program_self(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("is-red") {
            assert_eq!(
                scheme.ty,
                Type::Fn(
                    vec![Type::ADT(test_fqtn("Color"), vec![])],
                    Box::new(Type::Bool)
                )
            );
        } else {
            panic!("is-red not found in symbol table");
        }

        // Type defs should be in the result
        assert!(tc.lookup_type_def(&TypeName::from("Color")).is_some());
        assert!(tc.lookup_constructor_type("Red").is_some());
    }

    // spec: 03-types §3.8 — unification failure produces type error
    #[test]
    fn test_check_program_type_error() {
        let mut tc = tc_with_prims();
        // (defn bad [x] (add-i64 x true)) -- type error: Bool arg to monomorphic Int primitive
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("bad"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-i64"),
                        span: span(16, 23),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("x"),
                            span: span(24, 25),
                            inferred_type: None,
                        },
                        Expr::BoolLit {
                            value: true,
                            span: span(26, 30),
                            inferred_type: None,
                        },
                    ],
                    span: span(15, 31),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 32),
            }],
            visibility: Visibility::Public,
            span: span(0, 32),
        })];

        // add-i64 has monomorphic type (Fn [Int Int] Int) so (add-i64 x true) is a
        // type error: Bool cannot unify with Int.
        let result = tc.check_program_self(&program);
        assert!(result.is_err());
    }

    // spec: 03-types §3.5.1 — all expression types fully resolved after inference
    #[test]
    fn test_check_program_expr_types_resolved() {
        let mut tc = tc_with_prims();
        // (defn inc [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("inc"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-i64"),
                        span: span(16, 23),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("x"),
                            span: span(24, 25),
                            inferred_type: None,
                        },
                        Expr::IntLit {
                            value: 1,
                            span: span(26, 27),
                            inferred_type: None,
                        },
                    ],
                    span: span(15, 28),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 29),
            }],
            visibility: Visibility::Public,
            span: span(0, 29),
        })];

        let _result = tc.check_program_self(&program).unwrap();

        // All expr_types should be resolved (no Var types)
        for (span, ty) in &tc.state_expr_types_resolved() {
            if let Type::Var(_) = ty {
                panic!("unresolved Var in expr_types at {span}");
            }
        }
    }

    // spec: 03-types §3.1 — REPL expression inferred as literal type
    #[test]
    fn test_check_repl_expression() {
        let mut tc = tc_with_prims();
        let input = TopLevel::Expr(Expr::IntLit {
            value: 42,
            span: span(0, 2),
            inferred_type: None,
        });
        let result = tc.check_repl_input_self(&input).unwrap();
        assert_eq!(result.display.as_ref().unwrap().ty, Type::Int);
        assert!(result.display.as_ref().unwrap().scheme.is_none());
    }

    // spec: 03-types §3.4 — REPL defn produces polymorphic scheme
    #[test]
    fn test_check_repl_defn() {
        let mut tc = tc_with_prims();
        let input = TopLevel::Defn(Defn {
            name: Symbol::from("id"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(14, 15),
                    inferred_type: None,
                },
                span: span(0, 16),
            }],
            visibility: Visibility::Public,
            span: span(0, 16),
        });
        let result = tc.check_repl_input_self(&input).unwrap();

        // The scheme should be polymorphic
        let scheme = result.display.as_ref().unwrap().scheme.clone().unwrap();
        assert_eq!(scheme.vars.len(), 1);
    }

    // spec: 05-definitions §5.2 — REPL typedef registers type and constructors
    #[test]
    fn test_check_repl_typedef() {
        let mut tc = tc_with_prims();
        let input = TopLevel::TypeDef {
            name: TypeName::from("Dir"),
            docstring: None,
            type_params: vec![],
            constructors: vec![
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("North"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("South"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let result = tc.check_repl_input_self(&input).unwrap();
        assert_eq!(result.display.as_ref().unwrap().ty, Type::ADT(test_fqtn("Dir"), vec![]));
        assert!(tc.lookup_type_def(&TypeName::from("Dir")).is_some());
    }

    // spec: 03-types §3.5.1 — forward references resolved via two-pass inference
    #[test]
    fn test_check_program_forward_reference() {
        let mut tc = tc_with_prims();
        // Two functions where the first calls the second
        // (defn double [x] (add-self x))
        // (defn add-self [y] (add-i64 y y))
        //
        // add-i64 is monomorphic (Fn [Int Int] Int), so add-self is pinned to Int.
        // double's type unifies with add-self's type through the call.
        let program = vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("double"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-self"),
                            span: span(18, 26),
                            inferred_type: None,
                        }),
                        args: vec![Expr::Var {
                            name: Symbol::from("x"),
                            span: span(27, 28),
                            inferred_type: None,
                        }],
                        span: span(17, 29),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(0, 30),
                }],
                visibility: Visibility::Public,
                span: span(0, 30),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("add-self"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("y")],
                    param_annotations: vec![None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(48, 55),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var {
                                name: Symbol::from("y"),
                                span: span(56, 57),
                                inferred_type: None,
                            },
                            Expr::Var {
                                name: Symbol::from("y"),
                                span: span(58, 59),
                                inferred_type: None,
                            },
                        ],
                        span: span(47, 60),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(31, 61),
                }],
                visibility: Visibility::Public,
                span: span(31, 61),
            }),
        ];

        tc.check_program_self(&program).unwrap();

        // add-self is monomorphic: Fn([Int], Int) — add-i64 pins y to Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-self") {
            assert!(
                scheme.vars.is_empty(),
                "add-self should have no quantified vars (monomorphic via add-i64)"
            );
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                "add-self: (Fn [Int] Int)"
            );
        } else {
            panic!("add-self not found in symbol table");
        }

        // double should also be monomorphic (calls add-self with Int)
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("double") {
            assert!(
                scheme.vars.is_empty(),
                "double should have no quantified vars (monomorphic via add-self)"
            );
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                "double: (Fn [Int] Int)"
            );
        } else {
            panic!("double not found in symbol table");
        }
    }

    // spec: 03-types §3.9 — type annotation pins parameter type in forward reference
    #[test]
    fn test_check_program_forward_reference_pinned() {
        let mut tc = tc_with_prims();
        // (defn double [:Int x] (add-self x))
        // (defn add-self [y] (add-i64 y y))
        // Both are monomorphic: add-i64 pins y to Int, and annotation pins x to Int.
        let program = vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("double"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![Some(cranelisp_types::TypeExpr::Named(TypeName::from("Int")))],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-self"),
                            span: span(118, 126),
                            inferred_type: None,
                        }),
                        args: vec![Expr::Var {
                            name: Symbol::from("x"),
                            span: span(127, 128),
                            inferred_type: None,
                        }],
                        span: span(117, 129),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(100, 130),
                }],
                visibility: Visibility::Public,
                span: span(100, 130),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("add-self"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("y")],
                    param_annotations: vec![None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(148, 155),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var {
                                name: Symbol::from("y"),
                                span: span(156, 157),
                                inferred_type: None,
                            },
                            Expr::Var {
                                name: Symbol::from("y"),
                                span: span(158, 159),
                                inferred_type: None,
                            },
                        ],
                        span: span(147, 160),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(131, 161),
                }],
                visibility: Visibility::Public,
                span: span(131, 161),
            }),
        ];

        tc.check_program_self(&program).unwrap();

        // double is pinned: Fn([Int], Int) — annotation + add-i64 both constrain to Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("double") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("double not found");
        }

        // add-self is also pinned: Fn([Int], Int) — add-i64 constrains y to Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-self") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("add-self not found");
        }
    }

    // spec: 07-traits §7.5 — builtin function call resolved as BuiltinFn in method resolutions
    #[test]
    fn test_check_program_check_result_has_builtin_resolutions() {
        let mut tc = tc_with_prims();
        // (defn inc [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("inc"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-i64"),
                        span: span(16, 23),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("x"),
                            span: span(24, 25),
                            inferred_type: None,
                        },
                        Expr::IntLit {
                            value: 1,
                            span: span(26, 27),
                            inferred_type: None,
                        },
                    ],
                    span: span(15, 28),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 29),
            }],
            visibility: Visibility::Public,
            span: span(0, 29),
        })];

        let _result = tc.check_program_self(&program).unwrap();

        // The add-i64 call site should have a BuiltinFn resolution
        let method_resolutions = tc.state_method_resolutions();
        assert!(!method_resolutions.is_empty());
        let resolution = method_resolutions.get(&span(15, 28)).unwrap();
        match resolution {
            cranelisp_types::ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-i64");
            }
            _ => panic!("expected BuiltinFn"),
        }
    }

    // --- Ring 1: Polymorphic ADT program tests ---

    // spec: 05-definitions §5.2.2 — polymorphic typedef registers constructors with type params
    #[test]
    fn test_check_program_polymorphic_typedef() {
        let mut tc = tc_with_prims();
        // (deftype (Option a) None (Some [:a val]))
        // (defn unwrap-or [opt default] (match opt [(Some x) x (None default)]))
        let program = vec![
            TopLevel::TypeDef {
                name: TypeName::from("Option"),
                docstring: None,
                type_params: vec![Symbol::from("a")],
                constructors: vec![
                    cranelisp_types::ConstructorDef {
                        name: Symbol::from("None"),
                        docstring: None,
                        fields: vec![],
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::ConstructorDef {
                        name: Symbol::from("Some"),
                        docstring: None,
                        fields: vec![cranelisp_types::FieldDef {
                            name: Symbol::from("val"),
                            type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                        }],
                        span: Span::SYNTHETIC,
                    },
                ],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            },
        ];

        let _result = tc.check_program_self(&program).unwrap();
        assert!(tc.lookup_type_def(&TypeName::from("Option")).is_some());
        assert!(tc.lookup_constructor_type("Some").is_some());
        assert!(tc.lookup_constructor_type("None").is_some());
    }

    // spec: 05-definitions §5.2.2 — REPL polymorphic typedef registers type defs
    #[test]
    fn test_check_repl_polymorphic_typedef() {
        let mut tc = tc_with_prims();
        let input = TopLevel::TypeDef {
            name: TypeName::from("Option"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            constructors: vec![
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("None"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("Some"),
                    docstring: None,
                    fields: vec![cranelisp_types::FieldDef {
                        name: Symbol::from("val"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                    }],
                    span: Span::SYNTHETIC,
                },
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let _result = tc.check_repl_input_self(&input).unwrap();
        assert!(tc.lookup_type_def(&TypeName::from("Option")).is_some());
    }

    // spec: 03-types §3.1 — string literal inferred as String type
    #[test]
    fn test_check_repl_string_expression() {
        let mut tc = tc_with_prims();
        let input = TopLevel::Expr(Expr::StringLit {
            value: "hello".to_string(),
            span: span(0, 7),
            inferred_type: None,
        });
        let result = tc.check_repl_input_self(&input).unwrap();
        assert_eq!(result.display.as_ref().unwrap().ty, Type::String);
    }

    // spec: 03-types §3.1 — function returning string literal has String return type
    #[test]
    fn test_check_program_string_in_function() {
        let mut tc = tc_with_prims();
        // (defn greet [] "hello")
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("greet"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::StringLit {
                    value: "hello".to_string(),
                    span: span(16, 23),
                    inferred_type: None,
                },
                span: span(0, 24),
            }],
            visibility: Visibility::Public,
            span: span(0, 24),
        })];

        tc.check_program_self(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("greet") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![], Box::new(Type::String))
            );
        } else {
            panic!("greet not found in symbol table");
        }
    }

    // --- Ring 2: Constrained polymorphism tests ---

    // spec: 03-types §3.6 — collect_constrained_calls finds direct call to constrained fn
    #[test]
    fn test_collect_constrained_calls_finds_direct_call() {
        let constrained = HashSet::from([Symbol::from("add")]);
        // (add x y) where add is constrained
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add"),
                span: span(1, 4),
                inferred_type: None,
            }),
            args: vec![
                Expr::Var { name: Symbol::from("x"), span: span(5, 6), inferred_type: None, },
                Expr::Var { name: Symbol::from("y"), span: span(7, 8), inferred_type: None, },
            ],
            span: span(0, 9),
            resolved_call: None,
            inferred_type: None,
        };

        let mut calls = Vec::new();
        TypeCheckEnv::<()>::collect_constrained_calls(&expr, &constrained, &mut calls);

        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].0.as_ref(), "add");
        assert_eq!(calls[0].1.len(), 2); // two arg spans
        assert_eq!(calls[0].2, span(0, 9)); // call span
    }

    // spec: 03-types §3.6 — collect_constrained_calls ignores non-constrained functions
    #[test]
    fn test_collect_constrained_calls_ignores_non_constrained() {
        let constrained = HashSet::from([Symbol::from("add")]);
        // (sub-i64 x y) where sub-i64 is NOT constrained
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("sub-i64"),
                span: span(1, 8),
                inferred_type: None,
            }),
            args: vec![
                Expr::Var { name: Symbol::from("x"), span: span(9, 10), inferred_type: None, },
                Expr::Var { name: Symbol::from("y"), span: span(11, 12), inferred_type: None, },
            ],
            span: span(0, 13),
            resolved_call: None,
            inferred_type: None,
        };

        let mut calls = Vec::new();
        TypeCheckEnv::<()>::collect_constrained_calls(&expr, &constrained, &mut calls);

        assert!(calls.is_empty());
    }

    // spec: 03-types §3.6 — collect_constrained_calls recurses into let bindings
    #[test]
    fn test_collect_constrained_calls_recurses_into_let() {
        let constrained = HashSet::from([Symbol::from("add")]);
        // (let [z (add x y)] z)
        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("z"),
                Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add"),
                        span: span(10, 13),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var { name: Symbol::from("x"), span: span(14, 15), inferred_type: None, },
                        Expr::Var { name: Symbol::from("y"), span: span(16, 17), inferred_type: None, },
                    ],
                    span: span(9, 18),
                    resolved_call: None,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Var {
                name: Symbol::from("z"),
                span: span(20, 21),
                inferred_type: None,
            }),
            span: span(0, 22),
            inferred_type: None,
        };

        let mut calls = Vec::new();
        TypeCheckEnv::<()>::collect_constrained_calls(&expr, &constrained, &mut calls);

        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].0.as_ref(), "add");
    }

    // spec: 03-types §3.6 — collect_constrained_calls recurses into if branches
    #[test]
    fn test_collect_constrained_calls_recurses_into_if() {
        let constrained = HashSet::from([Symbol::from("add")]);
        // (if true (add 1 2) (add 3 4))
        let expr = Expr::If {
            cond: Box::new(Expr::BoolLit { value: true, span: span(4, 8), inferred_type: None, }),
            then_branch: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add"),
                    span: span(10, 13),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::IntLit { value: 1, span: span(14, 15), inferred_type: None, },
                    Expr::IntLit { value: 2, span: span(16, 17), inferred_type: None, },
                ],
                span: span(9, 18),
                resolved_call: None,
                inferred_type: None,
            }),
            else_branch: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add"),
                    span: span(20, 23),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::IntLit { value: 3, span: span(24, 25), inferred_type: None, },
                    Expr::IntLit { value: 4, span: span(26, 27), inferred_type: None, },
                ],
                span: span(19, 28),
                resolved_call: None,
                inferred_type: None,
            }),
            span: span(0, 29),
            inferred_type: None,
        };

        let mut calls = Vec::new();
        TypeCheckEnv::<()>::collect_constrained_calls(&expr, &constrained, &mut calls);

        assert_eq!(calls.len(), 2, "should find calls in both branches");
    }

    // spec: 03-types §3.6 — batch mode monomorphises constrained fn at concrete call site
    #[test]
    fn test_batch_monomorphise_generates_mono_defn() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        // Program: (defn add [x y] (+ x y))  -- constrained via +
        //          (defn main [] (add 3 4))   -- concrete Int call site
        let program = vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("add"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("x"), Symbol::from("y")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("+"),
                            span: span(18, 19),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(20, 21), inferred_type: None, },
                            Expr::Var { name: Symbol::from("y"), span: span(22, 23), inferred_type: None, },
                        ],
                        span: span(17, 24),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(0, 25),
                }],
                visibility: Visibility::Public,
                span: span(0, 25),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("main"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![],
                    param_annotations: vec![],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add"),
                            span: span(40, 43),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::IntLit { value: 3, span: span(44, 45), inferred_type: None, },
                            Expr::IntLit { value: 4, span: span(46, 47), inferred_type: None, },
                        ],
                        span: span(39, 48),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(26, 49),
                }],
                visibility: Visibility::Public,
                span: span(26, 49),
            }),
        ];

        let _result = tc.check_program_self(&program).unwrap();

        // In batch mode, add and main share a substitution during Pass 2.
        // main's (add 3 4) pins add's type vars to Int before generalization.
        // So add becomes monomorphic Fn([Int, Int], Int), not constrained.
        // This is correct HM behavior for same-program references.
        // Constrained polymorphism applies across module boundaries.
        assert!(
            tc.constrained_fn_names_set().is_empty(),
            "within same program, add should be monomorphic due to shared subst"
        );
        assert!(
            tc.mono_defn_names().is_empty(),
            "no constrained fns means no mono_defns needed"
        );

        // Verify add was correctly inferred as Fn([Int, Int], Int)
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("add not found");
        }

        // The + call site within add didn't get resolved during Pass 2
        // because x/y were still Vars during add's body check.
        // In the same-program case, add is used monomorphically and
        // doesn't need separate mono_defn generation.
    }

    // spec: 03-types §3.6 — constrained fn without callers detected and registered
    #[test]
    fn test_batch_constrained_fn_alone_detected() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        // (defn add [x y] (+ x y))  -- alone, no callers; should be constrained
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x"), Symbol::from("y")],
                param_annotations: vec![None, None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("+"),
                        span: span(18, 19),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var { name: Symbol::from("x"), span: span(20, 21), inferred_type: None, },
                        Expr::Var { name: Symbol::from("y"), span: span(22, 23), inferred_type: None, },
                    ],
                    span: span(17, 24),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 25),
            }],
            visibility: Visibility::Public,
            span: span(0, 25),
        })];

        let _result = tc.check_program_self(&program).unwrap();

        assert!(
            tc.constrained_fn_names_set().contains(&Symbol::from("add")),
            "add should be in constrained_fn_names"
        );

        // No callers, so no mono_defns
        let mono_names = tc.mono_defn_names();
        assert!(
            mono_names.is_empty(),
            "no call sites means no mono_defns, got: {mono_names:?}"
        );

        // Check the scheme has Num constraint
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add") {
            assert!(
                !scheme.constraints.is_empty(),
                "add should have Num constraint"
            );
        } else {
            panic!("add not found in symbol table");
        }
    }

    // spec: 03-types §3.6 — REPL expression monomorphises constrained fn on demand
    #[test]
    fn test_repl_expr_monomorphise() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);

        // First, define a constrained fn: (defn add [x y] (+ x y))
        let defn_input = TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x"), Symbol::from("y")],
                param_annotations: vec![None, None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("+"),
                        span: span(18, 19),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var { name: Symbol::from("x"), span: span(20, 21), inferred_type: None, },
                        Expr::Var { name: Symbol::from("y"), span: span(22, 23), inferred_type: None, },
                    ],
                    span: span(17, 24),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 25),
            }],
            visibility: Visibility::Public,
            span: span(0, 25),
        });
        let _ = tc.check_repl_input_self(&defn_input).unwrap();

        // Now evaluate an expression that calls the constrained fn: (add 3 4)
        let expr_input = TopLevel::Expr(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add"),
                span: span(100, 103),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 3, span: span(104, 105), inferred_type: None, },
                Expr::IntLit { value: 4, span: span(106, 107), inferred_type: None, },
            ],
            span: span(99, 108),
            resolved_call: None,
            inferred_type: None,
        });
        let _result = tc.check_repl_input_self(&expr_input).unwrap();

        // Should have mono_defns populated (entry on SymbolTable post-slim)
        let mono_names = tc.mono_defn_names();
        assert!(
            !mono_names.is_empty(),
            "REPL expr should generate mono_defns for constrained fn calls"
        );
        assert!(
            mono_names.iter().any(|n| n.as_ref() == "add$Int+Int"),
            "expected add$Int+Int in mono entries, got {mono_names:?}"
        );
    }

    // spec: 03-types §3.6 — REPL defn body triggers monomorphisation of constrained calls
    #[test]
    fn test_repl_defn_body_monomorphise() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);

        // Define a constrained fn: (defn add [x y] (+ x y))
        let defn_input = TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x"), Symbol::from("y")],
                param_annotations: vec![None, None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("+"),
                        span: span(18, 19),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var { name: Symbol::from("x"), span: span(20, 21), inferred_type: None, },
                        Expr::Var { name: Symbol::from("y"), span: span(22, 23), inferred_type: None, },
                    ],
                    span: span(17, 24),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 25),
            }],
            visibility: Visibility::Public,
            span: span(0, 25),
        });
        let _ = tc.check_repl_input_self(&defn_input).unwrap();

        // Define a function that calls the constrained fn: (defn main [] (add 1 2))
        let main_input = TopLevel::Defn(Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add"),
                        span: span(200, 203),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::IntLit { value: 1, span: span(204, 205), inferred_type: None, },
                        Expr::IntLit { value: 2, span: span(206, 207), inferred_type: None, },
                    ],
                    span: span(199, 208),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(180, 209),
            }],
            visibility: Visibility::Public,
            span: span(180, 209),
        });
        let _result = tc.check_repl_input_self(&main_input).unwrap();

        // Should have mono_defns from the defn body scan (entry on SymbolTable post-slim)
        let mono_names = tc.mono_defn_names();
        assert!(
            !mono_names.is_empty(),
            "REPL defn should generate mono_defns for constrained fn calls in body"
        );
        assert!(
            mono_names.iter().any(|n| n.as_ref() == "add$Int+Int"),
            "expected add$Int+Int in mono entries, got {mono_names:?}"
        );
    }

    // spec: 03-types §3.6 — program without constrained fns produces empty mono results
    #[test]
    fn test_batch_mono_no_constrained_fns_produces_empty() {
        let mut tc = tc_with_prims();
        // (defn inc [x] (add-i64 x 1)) — no constrained fns, all monomorphic
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("inc"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-i64"),
                        span: span(16, 23),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var { name: Symbol::from("x"), span: span(24, 25), inferred_type: None, },
                        Expr::IntLit { value: 1, span: span(26, 27), inferred_type: None, },
                    ],
                    span: span(15, 28),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 29),
            }],
            visibility: Visibility::Public,
            span: span(0, 29),
        })];

        let _result = tc.check_program_self(&program).unwrap();

        assert!(tc.constrained_fn_names_set().is_empty());
        assert!(tc.mono_defn_names().is_empty());
    }

    // --- Multi-sig defn tests ---

    /// Helper to build a CompileContext for test module.
    fn test_ctx() -> CompileContext {
        CompileContext {
            module: ModuleFullPath::from("test"),
            codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
        }
    }

    /// Helper to build a multi-sig Defn.
    fn make_multi_defn(
        name: &str,
        variants: Vec<DefnVariant>,
        span: Span,
    ) -> Defn {
        Defn {
            name: Symbol::from(name),
            docstring: None,
            variants,
            visibility: Visibility::Public,
            span,
        }
    }

    // spec: 05-definitions §5.1.2 — multi-sig defn with different arities
    #[test]
    fn test_multi_sig_different_arities() {
        let mut tc = tc_with_prims();

        // (defn add
        //   ([x y] (add-i64 x y))
        //   ([x y z] (add-i64 x (add-i64 y z))))
        let program = vec![TopLevel::Defn(make_multi_defn(
            "add",
            vec![
                DefnVariant {
                    params: vec![Symbol::from("x"), Symbol::from("y")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(10, 17),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(18, 19), inferred_type: None, },
                            Expr::Var { name: Symbol::from("y"), span: span(20, 21), inferred_type: None, },
                        ],
                        span: span(9, 22),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(5, 23),
                },
                DefnVariant {
                    params: vec![
                        Symbol::from("x"),
                        Symbol::from("y"),
                        Symbol::from("z"),
                    ],
                    param_annotations: vec![None, None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(30, 37),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(38, 39), inferred_type: None, },
                            Expr::Apply {
                                callee: Box::new(Expr::Var {
                                    name: Symbol::from("add-i64"),
                                    span: span(41, 48),
                                    inferred_type: None,
                                }),
                                args: vec![
                                    Expr::Var { name: Symbol::from("y"), span: span(49, 50), inferred_type: None, },
                                    Expr::Var { name: Symbol::from("z"), span: span(51, 52), inferred_type: None, },
                                ],
                                span: span(40, 53),
                                resolved_call: None,
                                inferred_type: None,
                            },
                        ],
                        span: span(29, 54),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(25, 55),
                },
            ],
            span(0, 56),
        ))];

        let _result = tc.check(&program, &test_ctx(), cranelisp_types::ModuleStrategy::Additive).unwrap();

        // The base name "add" should be registered as Overloaded
        let table_guard = tc.symbol_table();
        let entry = table_guard.get("add");
        assert!(entry.is_some(), "base name 'add' should be registered");
        if let Some(ModuleEntry::Def { kind, .. }) = entry {
            assert!(
                matches!(kind.as_ref(), DefKind::Overloaded { variants } if variants.len() == 2),
                "add should be Overloaded with 2 variants"
            );
        } else {
            panic!("add should be a Def entry");
        }

        // Mangled names should be registered: add$Int+Int and add$Int+Int+Int
        assert!(
            tc.symbol_table().get("add$Int+Int").is_some(),
            "add$Int+Int should be registered"
        );
        assert!(
            tc.symbol_table().get("add$Int+Int+Int").is_some(),
            "add$Int+Int+Int should be registered"
        );

        // The multi-sig defns live on SymbolTable post-slim (Wave 2 step 4).
        // The `default_method_defns` CheckResult field was retired; the mangled
        // entries are directly observable on the symbol table instead.
        let mangled_count = tc
            .symbol_table()
            .all_symbols()
            .filter(|(name, _)| name.as_ref().starts_with("add$"))
            .count();
        assert_eq!(
            mangled_count, 2,
            "should produce 2 mangled defns for the backend"
        );
    }

    // spec: 05-definitions §5.1.2 — multi-sig with same arity but different types
    #[test]
    fn test_multi_sig_same_arity_different_types() {
        let mut tc = tc_with_prims();

        // (defn process
        //   ([:Int x] (add-i64 x 1))
        //   ([:Bool x] (if x 1 0)))
        let program = vec![TopLevel::Defn(make_multi_defn(
            "process",
            vec![
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![Some(TypeExpr::Named(TypeName::from("Int")))],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(110, 117),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(118, 119), inferred_type: None, },
                            Expr::IntLit { value: 1, span: span(120, 121), inferred_type: None, },
                        ],
                        span: span(109, 122),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(105, 123),
                },
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![Some(TypeExpr::Named(TypeName::from("Bool")))],
                    body: Expr::If {
                        cond: Box::new(Expr::Var {
                            name: Symbol::from("x"),
                            span: span(130, 131),
                            inferred_type: None,
                        }),
                        then_branch: Box::new(Expr::IntLit { value: 1, span: span(132, 133), inferred_type: None, }),
                        else_branch: Box::new(Expr::IntLit { value: 0, span: span(134, 135), inferred_type: None, }),
                        span: span(127, 136),
                        inferred_type: None,
                    },
                    span: span(125, 137),
                },
            ],
            span(100, 138),
        ))];

        let _result = tc.check(&program, &test_ctx(), cranelisp_types::ModuleStrategy::Additive).unwrap();

        // Mangled names should be different: process$Int vs process$Bool
        assert!(
            tc.symbol_table().get("process$Int").is_some(),
            "process$Int should be registered"
        );
        assert!(
            tc.symbol_table().get("process$Bool").is_some(),
            "process$Bool should be registered"
        );

        // 2 mangled defns produced (observable on SymbolTable post-slim).
        let mangled_count = tc
            .symbol_table()
            .all_symbols()
            .filter(|(name, _)| name.as_ref().starts_with("process$"))
            .count();
        assert_eq!(mangled_count, 2);
    }

    // spec: 05-definitions §5.1.2 — duplicate signatures produce an error
    #[test]
    fn test_multi_sig_duplicate_signatures_error() {
        let mut tc = tc_with_prims();

        // (defn dup
        //   ([:Int x] (add-i64 x 1))
        //   ([:Int y] (add-i64 y 2)))
        // Both variants have the same signature (Int) -> Int — should error.
        let program = vec![TopLevel::Defn(make_multi_defn(
            "dup",
            vec![
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![Some(TypeExpr::Named(TypeName::from("Int")))],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(210, 217),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(218, 219), inferred_type: None, },
                            Expr::IntLit { value: 1, span: span(220, 221), inferred_type: None, },
                        ],
                        span: span(209, 222),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(205, 223),
                },
                DefnVariant {
                    params: vec![Symbol::from("y")],
                    param_annotations: vec![Some(TypeExpr::Named(TypeName::from("Int")))],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(230, 237),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("y"), span: span(238, 239), inferred_type: None, },
                            Expr::IntLit { value: 2, span: span(240, 241), inferred_type: None, },
                        ],
                        span: span(229, 242),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(225, 243),
                },
            ],
            span(200, 244),
        ))];

        let err = tc.check(&program, &test_ctx(), cranelisp_types::ModuleStrategy::Additive);
        assert!(err.is_err(), "duplicate signatures should produce an error");
        let msg = format!("{}", err.unwrap_err());
        assert!(
            msg.contains("duplicate signature"),
            "error should mention 'duplicate signature', got: {msg}"
        );
    }

    // spec: 05-definitions §5.1.2 — call site resolves to correct variant
    #[test]
    fn test_multi_sig_call_site_resolution() {
        let mut tc = tc_with_prims();

        // Define multi-sig:
        // (defn add
        //   ([:Int x :Int y] (add-i64 x y))
        //   ([:Int x :Int y :Int z] (add-i64 x (add-i64 y z))))
        //
        // Then call it:
        // (add 1 2)  -- should resolve to add$Int+Int

        let multi_defn = TopLevel::Defn(make_multi_defn(
            "add",
            vec![
                DefnVariant {
                    params: vec![Symbol::from("x"), Symbol::from("y")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(310, 317),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(318, 319), inferred_type: None, },
                            Expr::Var { name: Symbol::from("y"), span: span(320, 321), inferred_type: None, },
                        ],
                        span: span(309, 322),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(305, 323),
                },
                DefnVariant {
                    params: vec![
                        Symbol::from("x"),
                        Symbol::from("y"),
                        Symbol::from("z"),
                    ],
                    param_annotations: vec![None, None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(330, 337),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(338, 339), inferred_type: None, },
                            Expr::Apply {
                                callee: Box::new(Expr::Var {
                                    name: Symbol::from("add-i64"),
                                    span: span(341, 348),
                                    inferred_type: None,
                                }),
                                args: vec![
                                    Expr::Var { name: Symbol::from("y"), span: span(349, 350), inferred_type: None, },
                                    Expr::Var { name: Symbol::from("z"), span: span(351, 352), inferred_type: None, },
                                ],
                                span: span(340, 353),
                                resolved_call: None,
                                inferred_type: None,
                            },
                        ],
                        span: span(329, 354),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(325, 355),
                },
            ],
            span(300, 356),
        ));

        // Expression that calls add with 2 args: (add 1 2)
        let call_span = span(400, 410);
        let call_expr = TopLevel::Expr(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add"),
                span: span(401, 404),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 1, span: span(405, 406), inferred_type: None, },
                Expr::IntLit { value: 2, span: span(407, 408), inferred_type: None, },
            ],
            span: call_span,
            resolved_call: None,
            inferred_type: None,
        });

        let program = vec![multi_defn, call_expr];
        let _result = tc.check(&program, &test_ctx(), cranelisp_types::ModuleStrategy::Additive).unwrap();

        // The call site should have a SigDispatch resolution to "add$Int+Int".
        // Post-slim (Wave 2 step 4): resolutions live on annotated AST nodes.
        let resolutions = tc.annotated_resolutions();
        let resolution = resolutions.get(&call_span);
        assert!(
            resolution.is_some(),
            "call site should have a resolution"
        );
        match resolution.unwrap() {
            ResolvedCall::SigDispatch { mangled_name } => {
                assert_eq!(
                    mangled_name.as_ref(), "add$Int+Int",
                    "should dispatch to add$Int+Int"
                );
            }
            other => {
                panic!("expected SigDispatch, got {:?}", other);
            }
        }
    }

    // =========================================================================
    // Per-Form Typecheck API tests (Sprint 40 Wave 2)
    // =========================================================================
    //
    // These tests exercise the new check_form / merge_form_result / finalize_check_result
    // API introduced for the v4 pipeline. They validate:
    // 1. Behavioral identity: check() via check_form produces same results
    // 2. Per-form basics: individual forms through check_form
    // 3. Two-pass correctness: register-then-check ordering
    // 4. Multi-form programs with interactions
    // 5. Edge cases from the design doc
    // 6. Negative tests (error cases)

    /// Helper: create a CompileContext for the "test" module (check_form tests).
    fn cf_test_ctx() -> CompileContext {
        CompileContext {
            module: ModuleFullPath::from("test"),
            codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
        }
    }

    /// Helper: build an "inc" defn: (defn inc [x] (add-i64 x 1))
    fn make_inc_defn() -> Defn {
        make_defn(
            "inc",
            vec![Symbol::from("x")],
            vec![None],
            Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add-i64"),
                    span: span(16, 23),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("x"),
                        span: span(24, 25),
                        inferred_type: None,
                    },
                    Expr::IntLit {
                        value: 1,
                        span: span(26, 27),
                        inferred_type: None,
                    },
                ],
                span: span(15, 28),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(0, 29),
        )
    }

    /// Helper: build a Color typedef with Red and Green constructors.
    fn make_color_typedef() -> TopLevel {
        TopLevel::TypeDef {
            name: TypeName::from("Color"),
            docstring: None,
            type_params: vec![],
            constructors: vec![
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("Red"),
                    docstring: None,
                    fields: vec![],
                    span: span(200, 203),
                },
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("Green"),
                    docstring: None,
                    fields: vec![],
                    span: span(204, 209),
                },
            ],
            visibility: Visibility::Public,
            span: span(190, 210),
        }
    }

    /// Helper: build an is-red defn that matches on Color.
    fn make_is_red_defn() -> Defn {
        Defn {
            name: Symbol::from("is-red"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("c")],
                param_annotations: vec![None],
                body: Expr::Match {
                    scrutinee: Box::new(Expr::Var {
                        name: Symbol::from("c"),
                        span: span(230, 231),
                        inferred_type: None,
                    }),
                    arms: vec![
                        cranelisp_types::MatchArm {
                            pattern: cranelisp_types::Pattern::Constructor {
                                name: Symbol::from("Red"),
                                bindings: vec![],
                                span: span(233, 236),
                            },
                            body: Expr::BoolLit {
                                value: true,
                                span: span(237, 241),
                                inferred_type: None,
                            },
                            span: span(233, 241),
                        },
                        cranelisp_types::MatchArm {
                            pattern: cranelisp_types::Pattern::Wildcard {
                                span: span(242, 243),
                            },
                            body: Expr::BoolLit {
                                value: false,
                                span: span(244, 249),
                                inferred_type: None,
                            },
                            span: span(242, 249),
                        },
                    ],
                    span: span(224, 250),
                    compiler_generated: false,
                    inferred_type: None,
                },
                span: span(211, 251),
            }],
            visibility: Visibility::Public,
            span: span(211, 251),
        }
    }

    /// Helper: build the forward-reference program (double calls add-self).
    fn make_forward_ref_program() -> Vec<TopLevel> {
        vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("double"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-self"),
                            span: span(318, 326),
                            inferred_type: None,
                        }),
                        args: vec![Expr::Var {
                            name: Symbol::from("x"),
                            span: span(327, 328),
                            inferred_type: None,
                        }],
                        span: span(317, 329),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(300, 330),
                }],
                visibility: Visibility::Public,
                span: span(300, 330),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("add-self"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("y")],
                    param_annotations: vec![None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(348, 355),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var {
                                name: Symbol::from("y"),
                                span: span(356, 357),
                                inferred_type: None,
                            },
                            Expr::Var {
                                name: Symbol::from("y"),
                                span: span(358, 359),
                                inferred_type: None,
                            },
                        ],
                        span: span(347, 360),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(331, 361),
                }],
                visibility: Visibility::Public,
                span: span(331, 361),
            }),
        ]
    }

    // ---- Category 1: Behavioral Identity ----

    // spec: design/typecheck/check-form-api.md — check() via check_form produces identical CheckResult
    #[test]
    fn test_check_form_identity_simple_defn() {
        // Run a simple defn program through check() and verify the result matches expectations.
        // Since check() now internally uses check_form(), this tests behavioral identity.
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        let program = vec![TopLevel::Defn(make_inc_defn())];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Verify the function was registered with correct type
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("inc") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                "inc should be (Fn [Int] Int)"
            );
        } else {
            panic!("inc not found in symbol table after check()");
        }

        // Verify annotated ASTs carry inferred types on body expressions.
        // Post-slim (Wave 2 step 4): `expr_types` is no longer on CheckResult.
        let mut any_typed = false;
        let mut all_resolved = true;
        if let Some(ModuleEntry::Def { ast: Some(defn), .. }) = tc.symbol_table().get("inc") {
            for variant in &defn.variants {
                walk_inferred_types(&variant.body, &mut any_typed, &mut all_resolved);
            }
        }
        assert!(any_typed, "expr_types should be populated on annotated AST");
        assert!(all_resolved, "all expr_types should be resolved (no Var types)");

        // Verify method_resolutions populated (add-i64 call site resolved)
        assert!(
            !tc.annotated_resolutions().is_empty(),
            "method_resolutions should have add-i64 call site"
        );
    }

    // spec: design/typecheck/check-form-api.md — typedef + defn identity
    #[test]
    fn test_check_form_identity_typedef_plus_defn() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        let program = vec![
            make_color_typedef(),
            TopLevel::Defn(make_is_red_defn()),
        ];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // type_defs and constructor_to_type should be populated
        assert!(tc.lookup_type_def(&TypeName::from("Color")).is_some());
        assert!(tc.lookup_constructor_type("Red").is_some());
        assert!(tc.lookup_constructor_type("Green").is_some());

        // is-red should have correct type
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("is-red") {
            assert_eq!(
                scheme.ty,
                Type::Fn(
                    vec![Type::ADT(test_fqtn("Color"), vec![])],
                    Box::new(Type::Bool)
                )
            );
        } else {
            panic!("is-red not found in symbol table");
        }

        // expr_types should be populated on annotated AST (post-slim).
        let mut any_typed = false;
        let mut _all_resolved = true;
        if let Some(ModuleEntry::Def { ast: Some(defn), .. }) = tc.symbol_table().get("is-red") {
            for variant in &defn.variants {
                walk_inferred_types(&variant.body, &mut any_typed, &mut _all_resolved);
            }
        }
        assert!(any_typed);
    }

    // spec: design/typecheck/check-form-api.md — forward reference identity
    #[test]
    fn test_check_form_identity_forward_reference() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        let program = make_forward_ref_program();

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Both should be monomorphic Int -> Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("double") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
            );
        } else {
            panic!("double not found");
        }

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-self") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
            );
        } else {
            panic!("add-self not found");
        }

        // expr_types should be populated on annotated AST (post-slim).
        let mut any_typed = false;
        let mut _all_resolved = true;
        if let Some(ModuleEntry::Def { ast: Some(defn), .. }) = tc.symbol_table().get("add-self") {
            for variant in &defn.variants {
                walk_inferred_types(&variant.body, &mut any_typed, &mut _all_resolved);
            }
        }
        assert!(any_typed);
    }

    // spec: design/typecheck/check-form-api.md — constrained fn identity
    #[test]
    fn test_check_form_identity_constrained_fn() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        let ctx = cf_test_ctx();

        // (defn add [x y] (+ x y)) — constrained by Num trait
        let program = vec![TopLevel::Defn(make_defn(
            "add",
            vec![Symbol::from("x"), Symbol::from("y")],
            vec![None, None],
            Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("+"),
                    span: span(400, 401),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::Var { name: Symbol::from("x"), span: span(402, 403), inferred_type: None, },
                    Expr::Var { name: Symbol::from("y"), span: span(404, 405), inferred_type: None, },
                ],
                span: span(399, 406),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(390, 407),
        ))];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Should be detected as constrained polymorphic (entry on SymbolTable
        // post-slim; derived from `DefKind::UserFn { constrained_fn: Some(_) }`).
        assert!(
            tc.constrained_fn_names_set().contains(&Symbol::from("add")),
            "add should be detected as constrained polymorphic"
        );
    }

    // spec: design/typecheck/check-form-api.md — expression-only identity
    #[test]
    fn test_check_form_identity_expr() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        let program = vec![TopLevel::Expr(Expr::IntLit {
            value: 42,
            span: span(500, 502),
            inferred_type: None,
        })];

        let result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Display info should show Int type
        assert!(result.display.is_some());
        assert_eq!(result.display.as_ref().unwrap().ty, Type::Int);

        // expr_types should contain the literal's type. Post-slim (Wave 2
        // step 4), `__expr` carries its annotated AST on the symbol table.
        let mut any_typed = false;
        let mut _all_resolved = true;
        if let Some(ModuleEntry::Def { ast: Some(defn), .. }) = tc.symbol_table().get("__expr") {
            for variant in &defn.variants {
                walk_inferred_types(&variant.body, &mut any_typed, &mut _all_resolved);
            }
        }
        assert!(any_typed, "expr_types should contain the literal's type");
    }

    // spec: design/typecheck/check-form-api.md — multi-sig defn identity
    #[test]
    fn test_check_form_identity_multi_sig() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();

        // Multi-sig: (defn add ([x] (add-i64 x 1)) ([x y] (add-i64 x y)))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(610, 617),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(618, 619), inferred_type: None, },
                            Expr::IntLit { value: 1, span: span(620, 621), inferred_type: None, },
                        ],
                        span: span(609, 622),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(600, 623),
                },
                DefnVariant {
                    params: vec![Symbol::from("x"), Symbol::from("y")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(640, 647),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(648, 649), inferred_type: None, },
                            Expr::Var { name: Symbol::from("y"), span: span(650, 651), inferred_type: None, },
                        ],
                        span: span(639, 652),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(630, 653),
                },
            ],
            visibility: Visibility::Public,
            span: span(590, 654),
        })];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // The base name should be Overloaded in symbol table
        if let Some(ModuleEntry::Def { kind, .. }) = tc.symbol_table().get("add") {
            match kind.as_ref() {
                DefKind::Overloaded { variants } => {
                    assert_eq!(variants.len(), 2, "should have 2 overload variants");
                }
                other => panic!("expected Overloaded, got {:?}", other),
            }
        } else {
            panic!("add not found in symbol table");
        }

        // expr_types should be populated from both variant bodies (post-slim).
        let mut any_typed = false;
        let mut _all_resolved = true;
        if let Some(ModuleEntry::Def { ast: Some(defn), .. }) =
            tc.symbol_table().get("add$Int+Int")
        {
            for variant in &defn.variants {
                walk_inferred_types(&variant.body, &mut any_typed, &mut _all_resolved);
            }
        }
        assert!(any_typed);
    }

    // ---- Category 2: Per-Form Basics ----

    // spec: design/typecheck/check-form-api.md §check_form — single defn Register pass
    #[test]
    fn test_check_form_single_defn_register() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let defn = make_inc_defn();
        let form = TopLevel::Defn(defn);
        let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // Register pass should produce empty method_resolutions and expr_types
        assert!(result.method_resolutions.is_empty(), "Register pass produces no method resolutions");
        assert!(result.expr_types.is_empty(), "Register pass produces no expr types");
        assert!(result.constrained_fn.is_none(), "Register pass has no constrained fn");
        assert!(result.mono_defns.is_empty(), "Register pass has no mono defns");

        // Signature should be registered in the accumulator's defn_type_vars
        assert!(
            accumulator.defn_type_vars.contains_key(&Symbol::from("inc")),
            "defn_type_vars should contain 'inc' after Register pass"
        );

        // Signature should be registered in symbol table
        assert!(
            tc.symbol_table().get("inc").is_some(),
            "inc should be in symbol table after Register pass"
        );
    }

    // spec: design/typecheck/check-form-api.md §check_form — single defn CheckBody pass
    #[test]
    fn test_check_form_single_defn_check_body() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let defn = make_inc_defn();
        let form = TopLevel::Defn(defn);

        // Must register first
        let reg_result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, reg_result);

        // Now check body
        let body_result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator).unwrap();

        // CheckBody pass should produce expr_types (body expressions typed)
        assert!(
            !body_result.expr_types.is_empty(),
            "CheckBody should produce expr_types for body expressions"
        );

        // CheckBody pass should produce method_resolutions for add-i64 call
        assert!(
            !body_result.method_resolutions.is_empty(),
            "CheckBody should have method resolution for add-i64 call"
        );

        // No constrained fn (inc is monomorphic)
        assert!(body_result.constrained_fn.is_none());
    }

    // spec: design/typecheck/check-form-api.md §check_form — TypeDef Register pass
    #[test]
    fn test_check_form_typedef_register() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let form = make_color_typedef();
        let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // Registration should be mostly empty result (type is registered internally)
        assert!(result.default_method_defns.is_empty());

        // Constructors should be registered in symbol table
        assert!(
            tc.symbol_table().get("Red").is_some(),
            "Red constructor should be in symbol table"
        );
        assert!(
            tc.symbol_table().get("Green").is_some(),
            "Green constructor should be in symbol table"
        );
    }

    // spec: design/typecheck/check-form-api.md §check_form — TypeDef CheckBody is no-op
    #[test]
    fn test_check_form_typedef_check_body_noop() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let form = make_color_typedef();
        // Register first
        let _ = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // CheckBody on TypeDef should be a no-op
        let result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator).unwrap();
        assert!(result.method_resolutions.is_empty());
        assert!(result.expr_types.is_empty());
        assert!(result.constrained_fn.is_none());
        assert!(result.mono_defns.is_empty());
    }

    // spec: design/typecheck/check-form-api.md §check_form — TraitDecl Register pass
    #[test]
    fn test_check_form_trait_decl_register() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let decl = TraitDecl {
            name: TraitName::from("Eq"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("eq"),
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
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let form = TopLevel::TraitDecl(decl);
        let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // Should produce an empty result (registration is internal)
        assert!(result.method_resolutions.is_empty());
        assert!(result.expr_types.is_empty());
        assert!(result.default_method_defns.is_empty());
    }

    // spec: design/typecheck/check-form-api.md §check_form — TraitDecl CheckBody is no-op
    #[test]
    fn test_check_form_trait_decl_check_body_noop() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let decl = TraitDecl {
            name: TraitName::from("Show"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("show"),
                docstring: None,
                params: vec![TypeExpr::TypeVar(Symbol::from("a"))],
                ret_type: TypeExpr::Named(TypeName::from("String")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_param_names: vec![Symbol::from("x")],
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let form = TopLevel::TraitDecl(decl);

        // Register first
        let _ = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // CheckBody should be no-op
        let result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator).unwrap();
        assert!(result.method_resolutions.is_empty());
        assert!(result.expr_types.is_empty());
    }

    // spec: design/typecheck/check-form-api.md §check_form — TraitImpl Register pass
    #[test]
    fn test_check_form_trait_impl_register() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Register a new trait (Eq) then impl it for Int
        let decl = TraitDecl {
            name: TraitName::from("Eq"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("eq"),
                docstring: None,
                params: vec![
                    TypeExpr::TypeVar(Symbol::from("a")),
                    TypeExpr::TypeVar(Symbol::from("a")),
                ],
                ret_type: TypeExpr::Named(TypeName::from("Bool")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_param_names: vec![Symbol::from("a"), Symbol::from("b")],
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let decl_form = TopLevel::TraitDecl(decl);
        let _ = tc.check_form(&module, &decl_form, CheckPass::Register, &mut accumulator).unwrap();

        // Now impl Eq for Int
        let impl_ = TraitImpl {
            trait_name: TraitName::from("Eq"),
            target_type: TypeName::from("Int"),
            type_args: vec![],
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("eq"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("a"), Symbol::from("b")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("eq-i64"),
                            span: Span::SYNTHETIC,
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("a"), span: Span::SYNTHETIC, inferred_type: None, },
                            Expr::Var { name: Symbol::from("b"), span: Span::SYNTHETIC, inferred_type: None, },
                        ],
                        span: Span::SYNTHETIC,
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        };
        let impl_form = TopLevel::TraitImpl(impl_);
        let result = tc.check_form(&module, &impl_form, CheckPass::Register, &mut accumulator).unwrap();

        // Impl registration should succeed (no error).
        // default_method_defns contains mangled-name defns for each impl method
        // (e.g., "Eq.eq$Int") that need signature registration and body checking.
        assert!(
            !result.default_method_defns.is_empty(),
            "impl should produce mangled method defns for backend compilation"
        );
        // The mangled defn name should follow the pattern Trait.method$Type
        assert!(
            result.default_method_defns.iter().any(|d| d.name.as_ref().contains("Eq.eq$Int")),
            "should contain Eq.eq$Int mangled defn"
        );
    }

    // spec: design/typecheck/check-form-api.md §check_form — Expr wrapped as __expr
    #[test]
    fn test_check_form_expr_register_and_check() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Wrap expr as synthetic defn (matching what check() does internally)
        let expr = Expr::IntLit { value: 42, span: span(700, 702), inferred_type: None, };
        let synthetic_defn = Defn {
            name: Symbol::from("__expr"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: expr,
                span: span(700, 702),
            }],
            visibility: Visibility::Public,
            span: span(699, 703),
        };
        let form = TopLevel::Defn(synthetic_defn);

        // Register pass
        let reg_result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, reg_result);

        assert!(accumulator.defn_type_vars.contains_key(&Symbol::from("__expr")));

        // CheckBody pass
        let body_result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator).unwrap();

        // expr_types should contain the literal's type
        assert!(
            !body_result.expr_types.is_empty(),
            "CheckBody should produce expr_types for the expression"
        );
    }

    // ---- Category 3: Two-Pass Correctness ----

    // spec: design/typecheck/check-form-api.md §Invariant 1 — forward reference resolves via two-pass
    #[test]
    fn test_check_form_two_pass_mutual_reference() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let program = make_forward_ref_program();

        // Pass 1: Register both defns
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::Register, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Both signatures should be registered
        assert!(accumulator.defn_type_vars.contains_key(&Symbol::from("double")));
        assert!(accumulator.defn_type_vars.contains_key(&Symbol::from("add-self")));

        // Pass 2: Check bodies of both
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::CheckBody, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Both should have produced expr_types
        assert!(!accumulator.expr_types.is_empty(), "accumulated expr_types should be non-empty");

        // Finalize to get final types
        let _result = tc.finalize_check_result(
            &module, &mut accumulator, &program, ModuleStrategy::Replace,
        ).unwrap();

        // After finalization, all expr_types should be resolved on annotated ASTs.
        for name in ["double", "add-self"] {
            if let Some(ModuleEntry::Def { ast: Some(defn), .. }) =
                tc.symbol_table().get(name)
            {
                let mut _any = false;
                let mut all_resolved = true;
                for variant in &defn.variants {
                    walk_inferred_types(&variant.body, &mut _any, &mut all_resolved);
                }
                assert!(
                    all_resolved,
                    "unresolved Var in expr_types after finalize for {name}"
                );
            } else {
                panic!("{name} should be registered after finalize");
            }
        }
    }

    // spec: design/typecheck/check-form-api.md §Invariant 1 — CheckBody before Register errors
    #[test]
    fn test_check_form_check_body_before_register_errors() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let defn = make_inc_defn();
        let form = TopLevel::Defn(defn);

        // Try CheckBody without registering first — should error
        let result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator);
        assert!(
            result.is_err(),
            "CheckBody before Register should produce an error"
        );
    }

    // spec: design/typecheck/check-form-api.md §Invariant 1 — Register populates defn_type_vars
    #[test]
    fn test_check_form_register_populates_defn_type_vars() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let defn = make_inc_defn();
        let form = TopLevel::Defn(defn);

        let _ = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // defn_type_vars should contain the defn's name with type vars
        let (param_types, _ret_ty) = accumulator.defn_type_vars.get(&Symbol::from("inc"))
            .expect("inc should be in defn_type_vars");

        // inc has 1 parameter
        assert_eq!(param_types.len(), 1, "inc has 1 parameter");
    }

    // spec: design/typecheck/check-form-api.md §Invariant 2 — TypeDef before defn using constructors
    #[test]
    fn test_check_form_typedef_before_defn() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Register TypeDef(Color) first
        let typedef_form = make_color_typedef();
        let result = tc.check_form(&module, &typedef_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // Then register Defn(is-red) which uses Color constructors
        let defn_form = TopLevel::Defn(make_is_red_defn());
        let result = tc.check_form(&module, &defn_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // Pass 2: check body — should resolve constructor types correctly
        // TypeDef is no-op in CheckBody
        let _ = tc.check_form(&module, &typedef_form, CheckPass::CheckBody, &mut accumulator).unwrap();

        let body_result = tc.check_form(&module, &defn_form, CheckPass::CheckBody, &mut accumulator).unwrap();

        // Should succeed and produce expr_types
        assert!(!body_result.expr_types.is_empty(), "is-red body should have expr_types");
    }

    // spec: design/typecheck/check-form-api.md §Invariant 2 — TraitDecl before TraitImpl
    #[test]
    fn test_check_form_trait_decl_before_impl() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Register TraitDecl(Eq) first
        let decl = TraitDecl {
            name: TraitName::from("Eq"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("eq"),
                docstring: None,
                params: vec![
                    TypeExpr::TypeVar(Symbol::from("a")),
                    TypeExpr::TypeVar(Symbol::from("a")),
                ],
                ret_type: TypeExpr::Named(TypeName::from("Bool")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_param_names: vec![Symbol::from("a"), Symbol::from("b")],
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let decl_form = TopLevel::TraitDecl(decl);
        let result = tc.check_form(&module, &decl_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // Then register TraitImpl(Eq for Int) — should succeed because decl was registered first
        let impl_ = TraitImpl {
            trait_name: TraitName::from("Eq"),
            target_type: TypeName::from("Int"),
            type_args: vec![],
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("eq"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("a"), Symbol::from("b")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("eq-i64"),
                            span: Span::SYNTHETIC,
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("a"), span: Span::SYNTHETIC, inferred_type: None, },
                            Expr::Var { name: Symbol::from("b"), span: Span::SYNTHETIC, inferred_type: None, },
                        ],
                        span: Span::SYNTHETIC,
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        };
        let impl_form = TopLevel::TraitImpl(impl_);
        let result = tc.check_form(&module, &impl_form, CheckPass::Register, &mut accumulator);

        // Should succeed — no error
        assert!(result.is_ok(), "TraitImpl after TraitDecl should succeed");
    }

    // ---- Category 4: Multi-Form Programs ----

    // spec: design/typecheck/check-form-api.md §Invariant 3 — shared substitution
    #[test]
    fn test_check_form_multi_defn_shared_substitution() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Three defns: h uses add-i64 (pins to Int), g calls h, f calls g
        let h = TopLevel::Defn(make_defn(
            "h",
            vec![Symbol::from("x"), Symbol::from("y")],
            vec![None, None],
            Expr::Apply {
                callee: Box::new(Expr::Var { name: Symbol::from("add-i64"), span: span(800, 807), inferred_type: None, }),
                args: vec![
                    Expr::Var { name: Symbol::from("x"), span: span(808, 809), inferred_type: None, },
                    Expr::Var { name: Symbol::from("y"), span: span(810, 811), inferred_type: None, },
                ],
                span: span(799, 812),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(790, 813),
        ));
        let g = TopLevel::Defn(make_defn(
            "g",
            vec![Symbol::from("a")],
            vec![None],
            Expr::Apply {
                callee: Box::new(Expr::Var { name: Symbol::from("h"), span: span(830, 831), inferred_type: None, }),
                args: vec![
                    Expr::Var { name: Symbol::from("a"), span: span(832, 833), inferred_type: None, },
                    Expr::Var { name: Symbol::from("a"), span: span(834, 835), inferred_type: None, },
                ],
                span: span(829, 836),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(820, 837),
        ));
        let f = TopLevel::Defn(make_defn(
            "f",
            vec![Symbol::from("z")],
            vec![None],
            Expr::Apply {
                callee: Box::new(Expr::Var { name: Symbol::from("g"), span: span(860, 861), inferred_type: None, }),
                args: vec![
                    Expr::Var { name: Symbol::from("z"), span: span(862, 863), inferred_type: None, },
                ],
                span: span(859, 864),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(850, 865),
        ));

        let program = vec![f, g, h];

        // Pass 1: Register all
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::Register, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Pass 2: Check all bodies
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::CheckBody, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Finalize
        let _result = tc.finalize_check_result(
            &module, &mut accumulator, &program, ModuleStrategy::Replace,
        ).unwrap();

        // All three should be monomorphic Int via shared substitution
        for name in &["f", "g", "h"] {
            if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get(*name) {
                assert!(
                    scheme.vars.is_empty(),
                    "{} should be monomorphic (pinned to Int via shared substitution)", name
                );
            } else {
                panic!("{} not found in symbol table", name);
            }
        }
    }

    // spec: design/typecheck/check-form-api.md — accumulator merge grows with each form
    #[test]
    fn test_check_form_accumulator_merge() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let program = make_forward_ref_program();

        // Pass 1: Register all
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::Register, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Pass 2: Check bodies and verify accumulator grows
        let et_before_first = accumulator.expr_types.len();
        let form0_result = tc.check_form(&module, &program[0], CheckPass::CheckBody, &mut accumulator).unwrap();
        let form0_et = form0_result.expr_types.len();
        tc.merge_form_result(&module, &mut accumulator, form0_result);
        let et_after_first = accumulator.expr_types.len();

        assert!(
            et_after_first > et_before_first,
            "accumulator should grow after first form's CheckBody"
        );

        let form1_result = tc.check_form(&module, &program[1], CheckPass::CheckBody, &mut accumulator).unwrap();
        let form1_et = form1_result.expr_types.len();
        tc.merge_form_result(&module, &mut accumulator, form1_result);
        let et_after_second = accumulator.expr_types.len();

        assert!(
            et_after_second > et_after_first,
            "accumulator should grow after second form's CheckBody"
        );
        assert_eq!(
            et_after_second,
            et_before_first + form0_et + form1_et,
            "total expr_types should be sum of per-form contributions"
        );
    }

    // spec: design/typecheck/check-form-api.md — finalize resolves pending and produces complete result
    #[test]
    fn test_check_form_finalize_produces_complete_result() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let program = vec![TopLevel::Defn(make_inc_defn())];

        // Full two-pass processing
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::Register, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::CheckBody, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        let _result = tc.finalize_check_result(
            &module, &mut accumulator, &program, ModuleStrategy::Replace,
        ).unwrap();

        // finalize should produce complete annotated ASTs + method resolutions.
        // Post-slim (Wave 2 step 4): resolutions live on annotated AST nodes;
        // expr_types live on `Expr::inferred_type`.
        let mut any_typed = false;
        let mut all_resolved = true;
        if let Some(ModuleEntry::Def { ast: Some(defn), .. }) = tc.symbol_table().get("inc") {
            for variant in &defn.variants {
                walk_inferred_types(&variant.body, &mut any_typed, &mut all_resolved);
            }
        }
        assert!(any_typed, "finalized result should have expr_types");
        assert!(all_resolved, "all expr_types should be fully resolved");
        assert!(
            !tc.annotated_resolutions().is_empty(),
            "finalized result should have method_resolutions"
        );
    }

    // ---- Category 5: Edge Cases ----

    // spec: design/typecheck/check-form-api.md §DefnMulti — multi-sig Register
    #[test]
    fn test_check_form_defn_multi_register() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Multi-sig defn: two variants
        let multi = TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var { name: Symbol::from("add-i64"), span: span(1010, 1017), inferred_type: None, }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(1018, 1019), inferred_type: None, },
                            Expr::IntLit { value: 1, span: span(1020, 1021), inferred_type: None, },
                        ],
                        span: span(1009, 1022),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(1000, 1023),
                },
                DefnVariant {
                    params: vec![Symbol::from("x"), Symbol::from("y")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var { name: Symbol::from("add-i64"), span: span(1040, 1047), inferred_type: None, }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(1048, 1049), inferred_type: None, },
                            Expr::Var { name: Symbol::from("y"), span: span(1050, 1051), inferred_type: None, },
                        ],
                        span: span(1039, 1052),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(1030, 1053),
                },
            ],
            visibility: Visibility::Public,
            span: span(990, 1054),
        });

        let result = tc.check_form(&module, &multi, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // Internal variant defns should be in defn_type_vars
        assert!(
            accumulator.defn_type_vars.contains_key(&Symbol::from("add__v0")),
            "add__v0 should be in defn_type_vars"
        );
        assert!(
            accumulator.defn_type_vars.contains_key(&Symbol::from("add__v1")),
            "add__v1 should be in defn_type_vars"
        );

        // Base name should be in symbol table as Overloaded placeholder
        if let Some(ModuleEntry::Def { kind, .. }) = tc.symbol_table().get("add") {
            match kind.as_ref() {
                DefKind::Overloaded { .. } => {} // expected
                other => panic!("expected Overloaded placeholder, got {:?}", other),
            }
        } else {
            panic!("add base name not found in symbol table");
        }
    }

    // spec: design/typecheck/check-form-api.md §Constrained polymorphism — detection
    #[test]
    fn test_check_form_constrained_fn_detection() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // (defn add [x y] (+ x y)) — constrained by Num
        let defn_form = TopLevel::Defn(make_defn(
            "add",
            vec![Symbol::from("x"), Symbol::from("y")],
            vec![None, None],
            Expr::Apply {
                callee: Box::new(Expr::Var { name: Symbol::from("+"), span: span(1100, 1101), inferred_type: None, }),
                args: vec![
                    Expr::Var { name: Symbol::from("x"), span: span(1102, 1103), inferred_type: None, },
                    Expr::Var { name: Symbol::from("y"), span: span(1104, 1105), inferred_type: None, },
                ],
                span: span(1099, 1106),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(1090, 1107),
        ));

        // Register
        let reg = tc.check_form(&module, &defn_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, reg);

        // Check body
        let body = tc.check_form(&module, &defn_form, CheckPass::CheckBody, &mut accumulator).unwrap();

        // Should detect constrained fn
        assert!(
            body.constrained_fn.is_some(),
            "add should be detected as constrained"
        );
        assert_eq!(
            body.constrained_fn.as_ref().unwrap().as_ref(),
            "add",
        );
    }

    // spec: design/typecheck/check-form-api.md — expr_types fully resolved after finalize
    #[test]
    fn test_check_form_expr_types_no_unresolved_vars() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();

        // Use a polymorphic identity function called with Int to test resolution
        let program = vec![
            TopLevel::Defn(make_defn(
                "id",
                vec![Symbol::from("x")],
                vec![None],
                Expr::Var { name: Symbol::from("x"), span: span(1214, 1215), inferred_type: None, },
                Visibility::Public,
                span(1200, 1216),
            )),
            TopLevel::Defn(make_defn(
                "use-id",
                vec![Symbol::from("y")],
                vec![None],
                Expr::Apply {
                    callee: Box::new(Expr::Var { name: Symbol::from("id"), span: span(1230, 1232), inferred_type: None, }),
                    args: vec![Expr::Apply {
                        callee: Box::new(Expr::Var { name: Symbol::from("add-i64"), span: span(1234, 1241), inferred_type: None, }),
                        args: vec![
                            Expr::Var { name: Symbol::from("y"), span: span(1242, 1243), inferred_type: None, },
                            Expr::IntLit { value: 1, span: span(1244, 1245), inferred_type: None, },
                        ],
                        span: span(1233, 1246),
                        resolved_call: None,
                        inferred_type: None,
                    }],
                    span: span(1229, 1247),
                    resolved_call: None,
                    inferred_type: None,
                },
                Visibility::Public,
                span(1220, 1248),
            )),
        ];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // All expr_types should be fully resolved on annotated ASTs (post-slim).
        for (_name, entry) in tc.symbol_table().all_symbols() {
            if let ModuleEntry::Def { ast: Some(defn), .. } = entry {
                let mut _any = false;
                let mut all_resolved = true;
                for variant in &defn.variants {
                    walk_inferred_types(&variant.body, &mut _any, &mut all_resolved);
                }
                assert!(all_resolved, "unresolved Var in expr_types after check()");
            }
        }
    }

    // spec: design/typecheck/check-form-api.md — warnings accumulated across forms
    #[test]
    fn test_check_form_warnings_accumulated() {
        // This tests that the merge mechanism for warnings works.
        // We verify structurally that warnings from FormCheckResult are collected.
        let mut accumulator = ModuleCheckAccumulator::new();
        assert!(accumulator.warnings.is_empty());

        // Simulate a FormCheckResult with a warning
        let result_with_warning = FormCheckResult {
            method_resolutions: HashMap::new(),
            expr_types: HashMap::new(),
            constrained_fn: None,
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings: vec![Warning {
                kind: cranelisp_types::WarningKind::Other,
                message: "test warning".to_string(),
                span: Span::SYNTHETIC,
            }],
            call_graph_edges: Vec::new(),
        };

        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        tc.merge_form_result(&module, &mut accumulator, result_with_warning);

        assert_eq!(accumulator.warnings.len(), 1);
        assert_eq!(accumulator.warnings[0].message, "test warning");
    }

    // ---- Negative Tests ----

    // spec: design/typecheck/check-form-api.md — type error propagates from CheckBody
    #[test]
    fn test_check_form_type_error_propagates() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // (defn bad [x] (add-i64 x true)) — type error
        let bad_defn = TopLevel::Defn(make_defn(
            "bad",
            vec![Symbol::from("x")],
            vec![None],
            Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add-i64"),
                    span: span(1316, 1323),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::Var { name: Symbol::from("x"), span: span(1324, 1325), inferred_type: None, },
                    Expr::BoolLit { value: true, span: span(1326, 1330), inferred_type: None, },
                ],
                span: span(1315, 1331),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(1300, 1332),
        ));

        // Register should succeed
        let reg = tc.check_form(&module, &bad_defn, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, reg);

        // CheckBody should produce an error
        let result = tc.check_form(&module, &bad_defn, CheckPass::CheckBody, &mut accumulator);
        assert!(result.is_err(), "type error in body should propagate as Err");
    }

    // spec: design/typecheck/check-form-api.md — unknown trait in TraitImpl errors
    #[test]
    fn test_check_form_trait_impl_unknown_trait_error() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // TraitImpl referencing undeclared trait
        let impl_ = TraitImpl {
            trait_name: TraitName::from("NonexistentTrait"),
            target_type: TypeName::from("Int"),
            type_args: vec![],
            type_constraints: vec![],
            methods: vec![],
            span: Span::SYNTHETIC,
        };
        let form = TopLevel::TraitImpl(impl_);
        let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator);

        assert!(result.is_err(), "TraitImpl for undeclared trait should error");
    }

    // ---- AST Annotation Tests (Step 1b) ----

    /// Walk an Expr tree and collect all (span, inferred_type) pairs.
    fn collect_inferred_types(expr: &Expr, out: &mut Vec<(Span, Option<Type>)>) {
        out.push((expr.span(), expr.inferred_type().cloned()));
        match expr {
            Expr::Apply { callee, args, .. } => {
                collect_inferred_types(callee, out);
                for arg in args {
                    collect_inferred_types(arg, out);
                }
            }
            Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                for (_, binding_expr) in bindings {
                    collect_inferred_types(binding_expr, out);
                }
                collect_inferred_types(body, out);
            }
            Expr::If { cond, then_branch, else_branch, .. } => {
                collect_inferred_types(cond, out);
                collect_inferred_types(then_branch, out);
                collect_inferred_types(else_branch, out);
            }
            Expr::Lambda { body, .. } => {
                collect_inferred_types(body, out);
            }
            Expr::Match { scrutinee, arms, .. } => {
                collect_inferred_types(scrutinee, out);
                for arm in arms {
                    collect_inferred_types(&arm.body, out);
                }
            }
            Expr::Annotate { expr: inner, .. } => {
                collect_inferred_types(inner, out);
            }
            Expr::VecLit { elements, .. } => {
                for elem in elements {
                    collect_inferred_types(elem, out);
                }
            }
            Expr::Trace { body, .. } => {
                collect_inferred_types(body, out);
            }
            _ => {}
        }
    }

    /// Find the resolved_call on an Apply node with a given span.
    fn find_resolved_call(expr: &Expr, target_span: Span) -> Option<ResolvedCall> {
        if let Expr::Apply { resolved_call, span, callee, args, .. } = expr {
            if *span == target_span {
                return resolved_call.as_ref().map(|rc| *rc.clone());
            }
            if let Some(rc) = find_resolved_call(callee, target_span) {
                return Some(rc);
            }
            for arg in args {
                if let Some(rc) = find_resolved_call(arg, target_span) {
                    return Some(rc);
                }
            }
        }
        match expr {
            Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                for (_, binding_expr) in bindings {
                    if let Some(rc) = find_resolved_call(binding_expr, target_span) {
                        return Some(rc);
                    }
                }
                find_resolved_call(body, target_span)
            }
            Expr::If { cond, then_branch, else_branch, .. } => {
                find_resolved_call(cond, target_span)
                    .or_else(|| find_resolved_call(then_branch, target_span))
                    .or_else(|| find_resolved_call(else_branch, target_span))
            }
            Expr::Lambda { body, .. } => find_resolved_call(body, target_span),
            Expr::Match { scrutinee, arms, .. } => {
                find_resolved_call(scrutinee, target_span)
                    .or_else(|| arms.iter().find_map(|arm| find_resolved_call(&arm.body, target_span)))
            }
            Expr::Annotate { expr: inner, .. } | Expr::Trace { body: inner, .. } => {
                find_resolved_call(inner, target_span)
            }
            _ => None,
        }
    }

    // spec: design/arch/ast-annotation-examples.md §3.1 — simple fn resolved_call
    #[test]
    fn test_ast_annotation_simple_fn_resolved_call() {
        // (defn double [x] (add-i64 x x))
        // After typecheck, the add-i64 Apply should have:
        // - inferred_type: Some(Int) (concrete, no Var)
        // - resolved_call: Some(BuiltinFn) (since add-i64 is a primitive)
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();

        let add_span = span(100, 115);
        let program = vec![TopLevel::Defn(make_defn(
            "double",
            vec![Symbol::from("x")],
            vec![None],
            Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add-i64"),
                    span: span(101, 108),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::Var { name: Symbol::from("x"), span: span(109, 110), inferred_type: None },
                    Expr::Var { name: Symbol::from("x"), span: span(111, 112), inferred_type: None },
                ],
                span: add_span,
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(90, 120),
        ))];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Retrieve the annotated AST from the symbol table
        let st = tc.symbol_table();
        let entry = st.get("double").expect("double should be in symbol table");
        if let ModuleEntry::Def { ast: Some(defn), .. } = entry {
            let body = defn.body();

            // All inferred_types should be concrete (no Var)
            let mut types = Vec::new();
            collect_inferred_types(body, &mut types);
            for (s, ty) in &types {
                let ty = ty.as_ref().unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
                assert!(
                    !ty.contains_var(),
                    "inferred_type at span {:?} contains Var: {:?}", s, ty
                );
            }

            // The Apply node should have inferred_type = Int
            assert_eq!(
                body.inferred_type().unwrap(),
                &Type::Int,
                "Apply (add-i64 x x) should have type Int"
            );

            // Check that resolved_call is present on the Apply (BuiltinFn for add-i64)
            let rc = find_resolved_call(body, add_span);
            assert!(rc.is_some(), "Apply (add-i64 x x) should have resolved_call");
            match rc.unwrap() {
                ResolvedCall::BuiltinFn { name } => {
                    assert_eq!(name.as_ref(), "add-i64");
                }
                other => panic!("expected BuiltinFn, got {:?}", other),
            }
        } else {
            panic!("double should have ast: Some(..), got {:?}", entry);
        }
    }

    // spec: design/arch/ast-annotation-examples.md §3.1 — trait method resolved_call
    #[test]
    fn test_ast_annotation_trait_method_resolved_call() {
        // (defn double [x] (+ x x))  with Num trait
        // (double 5)
        // After typecheck, the + Apply should have resolved_call = TraitMethod
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        let ctx = cf_test_ctx();

        let plus_span = span(200, 210);
        let call_span = span(220, 230);
        let program = vec![
            TopLevel::Defn(make_defn(
                "double",
                vec![Symbol::from("x")],
                vec![None],
                Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("+"),
                        span: span(201, 202),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var { name: Symbol::from("x"), span: span(203, 204), inferred_type: None },
                        Expr::Var { name: Symbol::from("x"), span: span(205, 206), inferred_type: None },
                    ],
                    span: plus_span,
                    resolved_call: None,
                    inferred_type: None,
                },
                Visibility::Public,
                span(190, 215),
            )),
            // Call site: (double 5)
            TopLevel::Defn(make_defn(
                "__expr",
                vec![],
                vec![],
                Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("double"),
                        span: span(221, 227),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::IntLit { value: 5, span: span(228, 229), inferred_type: None },
                    ],
                    span: call_span,
                    resolved_call: None,
                    inferred_type: None,
                },
                Visibility::Public,
                span(219, 231),
            )),
        ];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Verify the annotated ASTs carry the trait method resolution.
        // Post-slim (Wave 2 step 4): resolutions live on AST nodes, not on
        // a side map inside CheckResult.
        assert!(
            tc.annotated_resolutions().contains_key(&plus_span),
            "annotated ASTs should carry a resolution for + call"
        );

        // Verify the AST has the same resolution
        let st = tc.symbol_table();
        let entry = st.get("double").expect("double should be in symbol table");
        if let ModuleEntry::Def { ast: Some(defn), .. } = entry {
            let body = defn.body();
            let rc = find_resolved_call(body, plus_span);
            assert!(rc.is_some(), "Apply (+ x x) should have resolved_call on AST node");
            match rc.unwrap() {
                ResolvedCall::TraitMethod { .. } => {} // expected
                other => panic!("expected TraitMethod, got {:?}", other),
            }

            // All types should be concrete
            let mut types = Vec::new();
            collect_inferred_types(body, &mut types);
            for (s, ty) in &types {
                let ty = ty.as_ref().unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
                assert!(
                    !ty.contains_var(),
                    "inferred_type at span {:?} contains Var: {:?}", s, ty
                );
            }
        } else {
            panic!("double should have ast: Some(..)");
        }
    }

    // spec: design/arch/ast-annotation-examples.md §3.7 — let binding concrete types
    #[test]
    fn test_ast_annotation_let_binding_concrete_type() {
        // (defn f [] (let [x (add-i64 1 2)] x))
        // All inferred_type fields should be concrete (Int, no Var).
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();

        let add_span = span(310, 325);
        let program = vec![TopLevel::Defn(make_defn(
            "f",
            vec![],
            vec![],
            Expr::Let {
                bindings: vec![(
                    Symbol::from("x"),
                    Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(311, 318),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::IntLit { value: 1, span: span(319, 320), inferred_type: None },
                            Expr::IntLit { value: 2, span: span(321, 322), inferred_type: None },
                        ],
                        span: add_span,
                        resolved_call: None,
                        inferred_type: None,
                    },
                )],
                body: Box::new(Expr::Var {
                    name: Symbol::from("x"),
                    span: span(330, 331),
                    inferred_type: None,
                }),
                span: span(300, 340),
                inferred_type: None,
            },
            Visibility::Public,
            span(295, 345),
        ))];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        let st = tc.symbol_table();
        let entry = st.get("f").expect("f should be in symbol table");
        if let ModuleEntry::Def { ast: Some(defn), .. } = entry {
            let body = defn.body();

            // All inferred_types should be concrete
            let mut types = Vec::new();
            collect_inferred_types(body, &mut types);
            for (s, ty) in &types {
                let ty = ty.as_ref().unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
                assert!(
                    !ty.contains_var(),
                    "inferred_type at span {:?} contains Var: {:?}", s, ty
                );
            }

            // The Let expression should have type Int
            assert_eq!(body.inferred_type().unwrap(), &Type::Int);

            // The binding expression (add-i64 1 2) should have resolved_call
            let rc = find_resolved_call(body, add_span);
            assert!(rc.is_some(), "Apply (add-i64 1 2) should have resolved_call");
        } else {
            panic!("f should have ast: Some(..)");
        }
    }

    // spec: design/arch/ast-annotation-examples.md §3.6 — self-recursive all resolved
    #[test]
    fn test_ast_annotation_self_recursive_all_resolved() {
        // (defn fact [n acc]
        //   (if (eq-i64 n 0)
        //     acc
        //     (fact (sub-i64 n 1) (mul-i64 n acc))))
        // All inferred_types should be concrete Int.
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();

        let eq_span = span(410, 425);
        let sub_span = span(440, 455);
        let mul_span = span(460, 475);
        let fact_span = span(430, 480);
        let program = vec![TopLevel::Defn(make_defn(
            "fact",
            vec![Symbol::from("n"), Symbol::from("acc")],
            vec![None, None],
            Expr::If {
                cond: Box::new(Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("eq-i64"),
                        span: span(411, 417),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var { name: Symbol::from("n"), span: span(418, 419), inferred_type: None },
                        Expr::IntLit { value: 0, span: span(420, 421), inferred_type: None },
                    ],
                    span: eq_span,
                    resolved_call: None,
                    inferred_type: None,
                }),
                then_branch: Box::new(Expr::Var {
                    name: Symbol::from("acc"),
                    span: span(426, 429),
                    inferred_type: None,
                }),
                else_branch: Box::new(Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("fact"),
                        span: span(431, 435),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Apply {
                            callee: Box::new(Expr::Var {
                                name: Symbol::from("sub-i64"),
                                span: span(441, 448),
                                inferred_type: None,
                            }),
                            args: vec![
                                Expr::Var { name: Symbol::from("n"), span: span(449, 450), inferred_type: None },
                                Expr::IntLit { value: 1, span: span(451, 452), inferred_type: None },
                            ],
                            span: sub_span,
                            resolved_call: None,
                            inferred_type: None,
                        },
                        Expr::Apply {
                            callee: Box::new(Expr::Var {
                                name: Symbol::from("mul-i64"),
                                span: span(461, 468),
                                inferred_type: None,
                            }),
                            args: vec![
                                Expr::Var { name: Symbol::from("n"), span: span(469, 470), inferred_type: None },
                                Expr::Var { name: Symbol::from("acc"), span: span(471, 474), inferred_type: None },
                            ],
                            span: mul_span,
                            resolved_call: None,
                            inferred_type: None,
                        },
                    ],
                    span: fact_span,
                    resolved_call: None,
                    inferred_type: None,
                }),
                span: span(400, 490),
                inferred_type: None,
            },
            Visibility::Public,
            span(395, 495),
        ))];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        let st = tc.symbol_table();
        let entry = st.get("fact").expect("fact should be in symbol table");
        if let ModuleEntry::Def { ast: Some(defn), .. } = entry {
            let body = defn.body();

            // All inferred_types should be concrete
            let mut types = Vec::new();
            collect_inferred_types(body, &mut types);
            for (s, ty) in &types {
                let ty = ty.as_ref().unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
                assert!(
                    !ty.contains_var(),
                    "inferred_type at span {:?} contains Var: {:?}", s, ty
                );
            }

            // Builtin calls should have resolved_call
            let eq_rc = find_resolved_call(body, eq_span);
            assert!(eq_rc.is_some(), "eq-i64 Apply should have resolved_call");
            let sub_rc = find_resolved_call(body, sub_span);
            assert!(sub_rc.is_some(), "sub-i64 Apply should have resolved_call");
            let mul_rc = find_resolved_call(body, mul_span);
            assert!(mul_rc.is_some(), "mul-i64 Apply should have resolved_call");

            // The recursive call to fact should NOT have resolved_call (it's a plain user fn)
            let fact_rc = find_resolved_call(body, fact_span);
            assert!(fact_rc.is_none(), "recursive fact call should have resolved_call = None (plain user fn)");
        } else {
            panic!("fact should have ast: Some(..)");
        }
    }

    // spec: design/arch/ast-annotation-examples.md §3.2 — constrained fn with shared subst
    #[test]
    fn test_ast_annotation_constrained_fn_pinned_by_call_site() {
        // (defn add [x y] (+ x y))
        // (defn main [] (add 1 2))
        // Within the same program, the shared substitution pins add's type vars
        // to Int. The AST on ModuleEntry::Def.ast for `add` should have fully
        // concrete types (Int), and the + Apply should have a TraitMethod resolution.
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);

        let plus_span = span(500, 510);
        let program = vec![
            TopLevel::Defn(make_defn(
                "add",
                vec![Symbol::from("x"), Symbol::from("y")],
                vec![None, None],
                Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("+"),
                        span: span(501, 502),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var { name: Symbol::from("x"), span: span(503, 504), inferred_type: None },
                        Expr::Var { name: Symbol::from("y"), span: span(505, 506), inferred_type: None },
                    ],
                    span: plus_span,
                    resolved_call: None,
                    inferred_type: None,
                },
                Visibility::Public,
                span(490, 515),
            )),
            TopLevel::Defn(make_defn(
                "main",
                vec![],
                vec![],
                Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add"),
                        span: span(521, 524),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::IntLit { value: 1, span: span(525, 526), inferred_type: None },
                        Expr::IntLit { value: 2, span: span(527, 528), inferred_type: None },
                    ],
                    span: span(520, 530),
                    resolved_call: None,
                    inferred_type: None,
                },
                Visibility::Public,
                span(518, 531),
            )),
        ];

        let _result = tc.check_program_self(&program).unwrap();

        // The `add` function should have a fully annotated AST on ModuleEntry::Def.ast.
        // The shared substitution pins add's type vars to Int.
        let st = tc.symbol_table();
        let entry = st.get("add").expect("add should be in symbol table");
        if let ModuleEntry::Def { ast: Some(defn), .. } = entry {
            let body = defn.body();

            // All inferred_types should be concrete (Int, no Var)
            let mut types = Vec::new();
            collect_inferred_types(body, &mut types);
            for (s, ty) in &types {
                let ty = ty.as_ref().unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
                assert!(
                    !ty.contains_var(),
                    "inferred_type at span {:?} contains Var: {:?}", s, ty
                );
            }

            // The + call should have resolved_call = TraitMethod (resolved via
            // deferred trait call resolution after the call site pins types)
            let rc = find_resolved_call(body, plus_span);
            assert!(rc.is_some(), "Apply (+ x x) should have resolved_call on AST node");
            match rc.unwrap() {
                ResolvedCall::TraitMethod { .. } => {} // expected
                other => panic!("expected TraitMethod, got {:?}", other),
            }
        } else {
            panic!("add should have ast: Some(..)");
        }
    }

    // spec: design/arch/ast-annotation-examples.md — qualified cross-module extern
    // A defn body that calls macros/sconcat via qualified name must have
    // resolved_call set on the Apply node. This is the pattern quasiquote
    // ~@ generates inside macro clause bodies.
    //
    // FIXME(/dev frontend): test references `cranelisp_frontend::build_program`
    // which was renamed to `build_form` returning `Vec<ParsedEntry>` per
    // the Wave 3a-β FIXME 0156 pivot. The test wiring needs to land
    // after frontend's parallel /dev work completes.
    #[cfg(any())]
    #[test]
    fn test_ast_annotation_qualified_extern_resolved_call() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();

        let sexps = cranelisp_frontend::parse(
            "(defn concat-nils [] (macros/sconcat macros/SNil macros/SNil))"
        ).unwrap();
        let program = cranelisp_frontend::build_program(&sexps).unwrap();

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        let st = tc.symbol_table();
        let entry = st.get("concat-nils").expect("concat-nils should be in symbol table");
        if let ModuleEntry::Def { ast: Some(defn), .. } = entry {
            let body = defn.body();

            // Find the Apply node (there's only one)
            fn find_any_apply(expr: &Expr) -> Option<&Expr> {
                if matches!(expr, Expr::Apply { .. }) {
                    return Some(expr);
                }
                match expr {
                    Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                        for (_, e) in bindings { if let Some(a) = find_any_apply(e) { return Some(a); } }
                        find_any_apply(body)
                    }
                    Expr::If { cond, then_branch, else_branch, .. } => {
                        find_any_apply(cond).or_else(|| find_any_apply(then_branch)).or_else(|| find_any_apply(else_branch))
                    }
                    Expr::Lambda { body, .. } | Expr::Annotate { expr: body, .. } | Expr::Trace { body, .. } => find_any_apply(body),
                    _ => None,
                }
            }
            let apply = find_any_apply(body).expect("should have an Apply node");
            if let Expr::Apply { resolved_call, .. } = apply {
                assert!(
                    resolved_call.is_some(),
                    "Apply (macros/sconcat ...) should have resolved_call on AST node"
                );
                match resolved_call.as_deref().unwrap() {
                    ResolvedCall::BuiltinFn { name } => {
                        assert_eq!(name.as_ref(), "sconcat");
                    }
                    other => panic!("expected BuiltinFn for macros/sconcat, got {:?}", other),
                }
            }

            let ty = body.inferred_type().expect("Apply should have inferred_type");
            assert!(!ty.contains_var(), "inferred_type should be concrete, got {:?}", ty);
        } else {
            panic!("concat-nils should have ast: Some(..)");
        }
    }

    // =========================================================================
    // AST annotation tests — trait impl methods
    // =========================================================================

    // SIGSEGV isolation: trait impl method using trait dispatch in body
    // must NOT be marked as constrained fn after body check pass.
    //
    // Reproduces the Sprint 55 regression where check_form_body_single_defn
    // re-infers the impl method body with fresh type vars, finds trait
    // constraints (from + operator), and marks the method as constrained_fn.
    // Codegen then skips it (constrained fns are deferred for monomorphisation),
    // leaving a null GOT slot -> SIGSEGV on dispatch.
    #[test]
    fn test_impl_method_not_marked_constrained_after_body_check() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        register_num_trait_inline(&mut tc);

        let mut accumulator = ModuleCheckAccumulator::new();

        // Register Double trait: (deftrait Double (double [self] self))
        let double_decl = TraitDecl {
            name: TraitName::from("Double"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("double"),
                docstring: None,
                params: vec![TypeExpr::TypeVar(Symbol::from("a"))],
                ret_type: TypeExpr::TypeVar(Symbol::from("a")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_param_names: vec![Symbol::from("x")],
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let decl_form = TopLevel::TraitDecl(double_decl);
        let result = tc.check_form(&module, &decl_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // Impl Double for Int: (defn double [x] (+ x x))
        let impl_ = TraitImpl {
            trait_name: TraitName::from("Double"),
            target_type: TypeName::from("Int"),
            type_args: vec![],
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("double"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("+"),
                            span: span(100, 101),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(102, 103), inferred_type: None },
                            Expr::Var { name: Symbol::from("x"), span: span(104, 105), inferred_type: None },
                        ],
                        span: span(99, 106),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(90, 110),
                }],
                visibility: Visibility::Public,
                span: span(90, 110),
            }],
            span: span(80, 120),
        };
        let impl_form = TopLevel::TraitImpl(impl_);
        let result = tc.check_form(&module, &impl_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // The register pass should produce the mangled defn
        let mangled_name = Symbol::from("Double.double$Int");
        assert!(
            !accumulator.default_method_defns.is_empty(),
            "register should produce default_method_defns"
        );
        assert!(
            accumulator.default_method_defns.iter().any(|d| d.name == mangled_name),
            "should contain Double.double$Int"
        );

        // Step: Run register for the mangled defn (like register_default_methods does)
        let defaults = std::mem::take(&mut accumulator.default_method_defns);
        for defn in &defaults {
            let form = TopLevel::Defn(defn.clone());
            let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }
        accumulator.default_method_defns = defaults;

        // Step: Run CheckBody for the mangled defn (like finalize_module does)
        let defaults_for_body = accumulator.default_method_defns.clone();
        for defn in &defaults_for_body {
            let form = TopLevel::Defn(defn.clone());
            let result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // KEY ASSERTION: The mangled method must NOT be constrained.
        // If it is, codegen will skip it -> null GOT slot -> SIGSEGV.
        let table = tc.symbol_table();
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = table.get(mangled_name.as_ref()) {
            match kind.as_ref() {
                DefKind::UserFn { constrained_fn } => {
                    assert!(
                        constrained_fn.is_none(),
                        "BUG: trait impl method '{}' was marked as constrained fn \
                        (scheme: {}). This causes codegen to skip it, leaving a null \
                        GOT slot -> SIGSEGV on dispatch.",
                        mangled_name, scheme.ty
                    );
                }
                other => panic!("expected UserFn, got {:?}", other),
            }

            // Also verify the scheme is concrete
            assert!(
                scheme.vars.is_empty() && scheme.constraints.is_empty(),
                "impl method scheme should be concrete (no vars/constraints), got: {:?}",
                scheme,
            );
        } else {
            panic!("mangled method '{}' not found in symbol table", mangled_name);
        }

        // Verify AST annotations are concrete (no Var(N))
        if let Some(ModuleEntry::Def { ast: Some(annotated), .. }) = table.get(mangled_name.as_ref()) {
            let body = annotated.body();
            if let Some(ty) = body.inferred_type() {
                assert!(
                    !ty.contains_var(),
                    "impl method body inferred_type should be concrete, got: {:?}",
                    ty
                );
            }
        }
    }

    // ---- Sprint 56 Wave 0 §9.3 — mangled multi-sig variant ast pre-materialisation ----

    /// Build a two-variant multi-sig `add` defn:
    ///   (defn add
    ///     ([:Int a :Int b]   (add-i64 a b))
    ///     ([:Float a :Float b] (add-f64 a b)))
    fn make_add_multi_sig_int_float() -> Defn {
        make_multi_defn(
            "add",
            vec![
                DefnVariant {
                    params: vec![Symbol::from("a"), Symbol::from("b")],
                    param_annotations: vec![
                        Some(TypeExpr::Named(TypeName::from("Int"))),
                        Some(TypeExpr::Named(TypeName::from("Int"))),
                    ],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(510, 517),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("a"), span: span(518, 519), inferred_type: None },
                            Expr::Var { name: Symbol::from("b"), span: span(520, 521), inferred_type: None },
                        ],
                        span: span(509, 522),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(505, 523),
                },
                DefnVariant {
                    params: vec![Symbol::from("a"), Symbol::from("b")],
                    param_annotations: vec![
                        Some(TypeExpr::Named(TypeName::from("Float"))),
                        Some(TypeExpr::Named(TypeName::from("Float"))),
                    ],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-f64"),
                            span: span(530, 537),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("a"), span: span(538, 539), inferred_type: None },
                            Expr::Var { name: Symbol::from("b"), span: span(540, 541), inferred_type: None },
                        ],
                        span: span(529, 542),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(525, 543),
                },
            ],
            span(500, 544),
        )
    }

    // spec: design/typecheck/ast-annotation.md §9.3 — mangled multi-sig variant ast pre-materialisation
    #[test]
    fn wave0_mangled_variant_carries_ast() {
        let mut tc = tc_with_prims();
        let program = vec![TopLevel::Defn(make_add_multi_sig_int_float())];
        tc.check(&program, &test_ctx(), ModuleStrategy::Additive).unwrap();

        let st = tc.symbol_table();

        // add$Int+Int: Def entry with ast: Some(..) and ast.name == "add$Int+Int",
        // single variant (mangled defns are per-variant).
        match st.get("add$Int+Int") {
            Some(ModuleEntry::Def { ast: Some(defn), kind, .. }) => {
                assert_eq!(defn.name.as_ref(), "add$Int+Int");
                assert_eq!(
                    defn.variants.len(),
                    1,
                    "mangled variant must be a single-variant defn"
                );
                assert!(
                    matches!(kind.as_ref(), DefKind::UserFn { constrained_fn: None }),
                    "mangled variant kind should be UserFn(None), got {:?}",
                    kind
                );
            }
            other => panic!("add$Int+Int should be Def {{ ast: Some(..), .. }}, got {:?}", other),
        }

        // add$Float+Float: same shape, name rewritten.
        match st.get("add$Float+Float") {
            Some(ModuleEntry::Def { ast: Some(defn), kind, .. }) => {
                assert_eq!(defn.name.as_ref(), "add$Float+Float");
                assert_eq!(defn.variants.len(), 1);
                assert!(matches!(kind.as_ref(), DefKind::UserFn { constrained_fn: None }));
            }
            other => panic!("add$Float+Float should be Def {{ ast: Some(..), .. }}, got {:?}", other),
        }
    }

    // spec: design/typecheck/ast-annotation.md §9.3 — annotations fully substituted on mangled variant
    #[test]
    fn wave0_mangled_variant_ast_is_annotated() {
        let mut tc = tc_with_prims();
        let program = vec![TopLevel::Defn(make_add_multi_sig_int_float())];
        tc.check(&program, &test_ctx(), ModuleStrategy::Additive).unwrap();

        let st = tc.symbol_table();
        let entry = st.get("add$Int+Int").expect("add$Int+Int must be registered");
        let defn = match entry {
            ModuleEntry::Def { ast: Some(d), .. } => d,
            other => panic!("expected ast: Some(..), got {:?}", other),
        };

        // Walk every Expr node in the body; every inferred_type must be concrete
        // (no Type::Var leaks after final substitution).
        let body = defn.body();
        let mut types = Vec::new();
        collect_inferred_types(body, &mut types);
        assert!(!types.is_empty(), "body should have at least one Expr node");
        for (s, ty) in &types {
            let ty = ty
                .as_ref()
                .unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
            assert!(
                !ty.contains_var(),
                "inferred_type at span {:?} contains Type::Var: {:?}",
                s,
                ty
            );
        }

        // The body root (the add-i64 Apply) should be concretely typed as Int.
        assert_eq!(
            body.inferred_type(),
            Some(&Type::Int),
            "add$Int+Int body should be Int"
        );
    }

    // spec: design/typecheck/ast-annotation.md §9.3 — overloaded base has no ast
    #[test]
    fn wave0_overloaded_base_has_no_ast() {
        let mut tc = tc_with_prims();
        let program = vec![TopLevel::Defn(make_add_multi_sig_int_float())];
        tc.check(&program, &test_ctx(), ModuleStrategy::Additive).unwrap();

        let st = tc.symbol_table();
        match st.get("add") {
            Some(ModuleEntry::Def { ast, kind, .. }) => {
                assert!(
                    ast.is_none(),
                    "overloaded base 'add' must have ast: None (bodies live on mangled variants)"
                );
                assert!(
                    matches!(kind.as_ref(), DefKind::Overloaded { variants } if variants.len() == 2),
                    "overloaded base kind should be Overloaded with 2 variants, got {:?}",
                    kind
                );
            }
            other => panic!("'add' base should be Def {{ Overloaded, ast: None }}, got {:?}", other),
        }
    }
}
