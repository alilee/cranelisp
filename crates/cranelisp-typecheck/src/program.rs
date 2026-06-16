//! Multi-pass type checking pipeline.
//!
//! The production entry surface is the `check_forms` free function in
//! `form.rs` (Decision 44): it drives a single cluster-typecheck pass over a
//! `Vec<ParsedEntry>` through the per-form API below.
//!
//! ## Per-Form API (v4 Pipeline)
//!
//! `check_form()` processes a single `TopLevel` form through one pass at a time.
//! The caller (`check_forms`) drives two-pass iteration:
//! - Pass 1 (`CheckPass::Register`): register type defs, traits, signatures.
//! - Pass 2 (`CheckPass::CheckBody`): check function bodies, detect constraints.
//!
//! `merge_form_result()` accumulates per-form results into a `ModuleCheckAccumulator`.
//! `finalize_check_result()` runs post-passes and drains the accumulator into `CheckResult`.
//!
//! `check_via_forms()` is a `#[cfg(test)]` driver that runs the same Pass 1 /
//! Pass 2 / finalize pipeline over a `&[TopLevel]` slice and retains the
//! display-bearing `CheckResult` for in-crate test assertions. Production code
//! never calls it — it routes through `check_forms`.

use std::collections::{HashMap, HashSet};

use cranelisp_types::{ErrorLocation,
    ConstrainedFn, CranelispError, Defn, DefKind, DefnVariant,
    Expr, FQSymbol, JitSymbol, ModuleEntry, ModuleFullPath,
    ModuleStrategy, MonoDefn, ResolvedCall, Span, Subst, Symbol, SymbolTable, TopLevel, Type,
    UserFnState, Warning, apply,
};

// Test-only imports: used exclusively by the `#[cfg(test)]` `check_via_forms`
// driver, `compute_display_info` / `wrap_exprs_as_defns` helpers, and the
// in-crate test module.
#[cfg(test)]
use cranelisp_types::{CompileContext, DisplayInfo, Visibility};

use crate::result::CheckResult;

use crate::checker::{CheckState, TypeCheckEnv};
use crate::scheme::mono;

// --- Shared Expr child traversal (the single child-enumeration helper) ---

/// Invoke `f` on each immediate child sub-expression of `expr` (immutable).
///
/// This is the single source of truth for "what are an `Expr`'s child
/// expressions" — every structural walker in the crate routes its recursion
/// through this (or its `_mut` sibling) so the variant coverage lives in one
/// place. Walkers supply their own per-node action separately; only the child
/// enumeration is shared. Leaf variants (`IntLit` / `FloatLit` / `BoolLit` /
/// `StringLit` / `Var`) have no children and invoke `f` zero times.
pub(crate) fn for_each_child_expr(expr: &Expr, mut f: impl FnMut(&Expr)) {
    match expr {
        Expr::Apply { callee, args, .. } => {
            f(callee);
            for arg in args {
                f(arg);
            }
        }
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            for (_, binding_expr) in bindings {
                f(binding_expr);
            }
            f(body);
        }
        Expr::If { cond, then_branch, else_branch, .. } => {
            f(cond);
            f(then_branch);
            f(else_branch);
        }
        Expr::Lambda { body, .. } => f(body),
        Expr::Match { scrutinee, arms, .. } => {
            f(scrutinee);
            for arm in arms {
                f(&arm.body);
            }
        }
        Expr::Annotate { expr: inner, .. } => f(inner),
        Expr::VecLit { elements, .. } => {
            for elem in elements {
                f(elem);
            }
        }
        Expr::Trace { body, .. } => f(body),
        Expr::ConstrADT { fields, .. } => {
            for field in fields {
                f(field);
            }
        }
        // Leaf nodes: no children to recurse into
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. } => {}
    }
}

/// Mutable sibling of [`for_each_child_expr`]: invoke `f` on each immediate
/// child sub-expression of `expr` by `&mut` reference. Same variant coverage.
pub(crate) fn for_each_child_expr_mut(expr: &mut Expr, mut f: impl FnMut(&mut Expr)) {
    match expr {
        Expr::Apply { callee, args, .. } => {
            f(callee);
            for arg in args {
                f(arg);
            }
        }
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            for (_, binding_expr) in bindings {
                f(binding_expr);
            }
            f(body);
        }
        Expr::If { cond, then_branch, else_branch, .. } => {
            f(cond);
            f(then_branch);
            f(else_branch);
        }
        Expr::Lambda { body, .. } => f(body),
        Expr::Match { scrutinee, arms, .. } => {
            f(scrutinee);
            for arm in arms {
                f(&mut arm.body);
            }
        }
        Expr::Annotate { expr: inner, .. } => f(inner),
        Expr::VecLit { elements, .. } => {
            for elem in elements {
                f(elem);
            }
        }
        Expr::Trace { body, .. } => f(body),
        Expr::ConstrADT { fields, .. } => {
            for field in fields {
                f(field);
            }
        }
        // Leaf nodes: no children to recurse into
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. } => {}
    }
}

// --- AST annotation helpers (Step 1b) ---

/// Apply substitution to all `inferred_type` fields on an expression tree.
/// Replaces `Var(N)` with concrete types from the substitution.
fn apply_subst_to_expr(subst: &Subst, expr: &mut Expr) {
    // Apply substitution to this node's inferred_type
    if let Some(ty) = expr.inferred_type() {
        let resolved = apply(subst, ty);
        expr.set_inferred_type(Some(Box::new(resolved)));
    }
    // Recurse into children via the shared enumeration helper.
    for_each_child_expr_mut(expr, |child| apply_subst_to_expr(subst, child));
}

/// Apply substitution to all `inferred_type` fields in a `Defn`.
pub(crate) fn apply_subst_to_defn(subst: &Subst, defn: &mut Defn) {
    for variant in &mut defn.variants {
        apply_subst_to_expr(subst, &mut variant.body);
    }
}

/// Apply substitution to all `inferred_type` fields in a `DefnVariant`.
/// S69 Submission 35 narrowing — `ModuleEntry::Def.ast` now carries the
/// single meaningful `DefnVariant` payload; the outer `Defn` wrapper is the
/// frontend AST shape, not the per-entry runtime payload.
pub(crate) fn apply_subst_to_variant(subst: &Subst, variant: &mut DefnVariant) {
    apply_subst_to_expr(subst, &mut variant.body);
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

    // Set resolved_call on Apply nodes (call position) AND Var nodes (value
    // position — spec §7.6 trait-method-as-value, resolved by
    // `resolve_value_position_trait_methods`) from method_resolutions.
    match expr {
        Expr::Apply { resolved_call, span: apply_span, .. } => {
            if let Some(resolution) = method_resolutions.get(apply_span) {
                *resolved_call = Some(Box::new(resolution.clone()));
            }
        }
        Expr::Var { resolved_call, span: var_span, .. } => {
            if let Some(resolution) = method_resolutions.get(var_span) {
                *resolved_call = Some(Box::new(resolution.clone()));
            }
        }
        _ => {}
    }

    // Recurse into children via the shared enumeration helper.
    for_each_child_expr_mut(expr, |child| {
        annotate_expr_from_maps(child, expr_types, method_resolutions)
    });
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

/// Annotate a `DefnVariant` with types and resolved calls from side maps.
/// Sibling of `annotate_defn_from_maps` for the post-S35 narrowing.
pub(crate) fn annotate_variant_from_maps(
    variant: &mut DefnVariant,
    expr_types: &HashMap<Span, Type>,
    method_resolutions: &HashMap<Span, ResolvedCall>,
) {
    annotate_expr_from_maps(&mut variant.body, expr_types, method_resolutions);
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
        // Per Submission 22: `ModuleEntry::Macro` retired. Macros are now
        // `ModuleEntry::Def` entries with `kind: DefKind::Macro { clauses_meta }`,
        // so the prior OR-pattern collapses to the single Def arm.
        if let Some(ModuleEntry::Def { callees: c, .. }) =
            sym_table.symbols.get_mut(&caller)
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
    /// **Redefinition slot carry-forward (S83, FIXME 0356/0357, Principle 20).**
    /// With deferred GOT-slot allocation, Pass-1 `register_defn_signature`
    /// overwrites a redefined symbol's prior `Concrete` entry with a slot-less
    /// `UserFnState::NotDetermined` — which would drop the prior callable slot
    /// before the Pass-2 determination point can reuse it (orphaning the live
    /// GOT pointer the prior `Code::Jit` installed = a use-after-free). So Pass-1
    /// captures the prior entry's concrete slot HERE (read via
    /// `callable_got_slot()`, before the overwrite), keyed by defn name; the
    /// Pass-2 unconstrained determination arm reuses it instead of allocating
    /// fresh. A prior `NotDetermined` / `Constrained` / absent entry leaves no
    /// key here, so the arm allocates a fresh slot (constrained→concrete redef,
    /// or first definition). Per-`check`-call (each REPL eval threads its own
    /// accumulator through Pass-1 → Pass-2), which is exactly the redefinition
    /// granularity. See `UserFnState` rustdoc "Timing-wall resolution".
    pub(crate) redef_slots: HashMap<Symbol, usize>,
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
            redef_slots: HashMap::new(),
        }
    }
}

// --- Multi-sig type aliases ---
//
// Used by the multi-sig overload-resolution helpers
// (`resolve_variant_types` / `register_mangled_variants`) reached from
// `finalize_check_result`'s `resolve_multi_sig_overloads` post-pass — part
// of the production `check_forms` path.

/// Resolved variant info: (concrete_params, concrete_ret, internal_name, variant_index).
type ResolvedVariant = (Vec<Type>, Type, Symbol, usize);

/// Mangled variant info: (concrete_params, concrete_ret, mangled_name).
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

/// Read the GOT slot of a prior **concrete callable** entry named `name` in
/// the symbol table `st`, if one exists.
///
/// **The redefinition slot-reuse seam (S83, FIXME 0356/0357, Principle 20).**
/// With deferred GOT-slot allocation, Pass-1 no longer carries a slot forward;
/// the carry-forward moved here, to the Pass-2 determination point. When an
/// unconstrained (concrete) defn is being redefined over a prior **concrete**
/// entry, the determination arm must **REUSE** the prior slot rather than
/// allocate a fresh one — orphaning the live GOT pointer the prior `Code::Jit`
/// installed would be a use-after-free (the same guard the S82 `existing_slot`
/// carry-forward provided in Pass-1). The read goes through
/// `callable_got_slot()` (the single read-through point), so it returns `Some`
/// only for the slot-bearing callable kinds (`Concrete` `UserFn`, `Primitive`,
/// `Constructor`) and `None` for a prior `NotDetermined` / `Constrained` /
/// non-`Def` entry — exactly the cases where there is no live pointer to
/// preserve and a fresh slot is correct.
fn existing_callable_slot<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore>(
    st: &SymbolTable<C, L>,
    name: &str,
) -> Option<usize> {
    st.get(name).and_then(|e| e.callable_got_slot())
}

/// Returns true if `name` is a synthesised macro-clause defn — the
/// `__macro_{macro}_clause_{idx}` shape produced by
/// `cranelisp_frontend::synthesize_macro_clause_defn`. Typecheck checks each
/// clause body as an ordinary `defn`; this predicate recovers the "I am inside
/// a macro clause body" context from the defn name alone, so no clause-body
/// flag has to be threaded through the inference signatures.
fn is_macro_clause_defn_name(name: &str) -> bool {
    // Shape: __macro_{macro}_clause_{idx}. The `_clause_` infix plus the
    // `__macro_` prefix together are specific enough to never collide with a
    // user-authored or REPL-synthetic defn name (which never carry the
    // double-underscore `__macro_` prefix from the frontend synthesiser).
    name.starts_with("__macro_") && name.contains("_clause_")
}

/// Enrich a bare "undefined variable" body-resolution error into the §0.8
/// macro-availability diagnostic when the failing resolution happened inside a
/// `defmacro` clause body.
///
/// Per `design/arch/macro-availability-model.md` §0.8 (DECISION LOCKED
/// 2026-06-03): a macro's expansion may reference only dependency-module
/// definitions and macros — NOT same-module non-macro definitions. When a
/// clause body references such a name, the pass-ordered three-pass model leaves
/// the name structurally invisible at expansion, so typecheck reports a generic
/// "undefined variable: helper". This rewrites that into the actionable
/// diagnostic, preserving the offending symbol name (callers substring-match on
/// it) and naming the dependency-module rule.
///
/// Any non-undefined-variable error (or an error against a non-macro-clause
/// defn) passes through unchanged.
fn enrich_macro_clause_resolution_error(
    defn_name: &str,
    err: CranelispError,
) -> CranelispError {
    const PREFIX: &str = "undefined variable: ";
    if !is_macro_clause_defn_name(defn_name) {
        return err;
    }
    if let CranelispError::TypeError { message, location } = &err
        && let Some(sym) = message.strip_prefix(PREFIX)
    {
        return CranelispError::TypeError {
            message: format!(
                "undefined variable: {sym} — macro expansion may not reference \
                 same-module non-macro definitions; define `{sym}` in a \
                 dependency module (or import it)"
            ),
            location: location.clone(),
        };
    }
    err
}

fn mangle_sig(name: &str, param_types: &[Type]) -> Symbol {
    if param_types.is_empty() {
        Symbol::from(format!("{}$", name))
    } else {
        let parts: Vec<String> = param_types.iter().map(mangle_type).collect();
        Symbol::from(format!("{}${}", name, parts.join("+")))
    }
}

/// Mangle a single type for name mangling.
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
            // `ResolvedCall` is `#[non_exhaustive]` per Decision 47 / S69
            // Submission 32. Future variants land here; they default to "no
            // call graph edge" until the call-graph maintainers wire them.
            _ => None,
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
        // Capture the prior concrete slot BEFORE register_defn_signature
        // overwrites the entry with a slot-less NotDetermined (S83 deferred
        // allocation, Principle 20). The Pass-2 determination point reuses it.
        // Read through the same `current_symbol_table_mut().get()` path the
        // overwrite uses, so staging-vs-live matches the write target.
        if let Some(slot) = self
            .current_symbol_table_mut(state)
            .get(defn.name.as_ref())
            .and_then(|e| e.callable_got_slot())
        {
            accumulator.redef_slots.insert(defn.name.clone(), slot);
        }
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
                    body: variant.body.clone(),
                    span: variant.span,
                }],
                visibility: defn.visibility,
                span: variant.span,
            };
            // Capture the prior concrete slot for this `__vN` variant before
            // register_defn_signature overwrites it (S83 deferred allocation):
            // the Pass-2 determination point reuses it on REPL redefinition of
            // the same multi-sig defn.
            if let Some(slot) = self
                .current_symbol_table_mut(state)
                .get(internal_name.as_ref())
                .and_then(|e| e.callable_got_slot())
            {
                accumulator.redef_slots.insert(internal_name.clone(), slot);
            }
            // Register each variant's signature
            let (param_types, ret_ty) = self.register_defn_signature(state, &internal_defn)?;
            accumulator.defn_type_vars.insert(internal_name, (param_types, ret_ty));
        }
        state.overloads.insert(defn.name.clone(), overload_entries);

        // Register a placeholder for the base name
        let placeholder_ty = self.fresh_var();
        let placeholder_scheme = mono(placeholder_ty);
        let mut builder = ModuleEntry::def(
            placeholder_scheme,
            DefKind::Overloaded { variants: vec![] },
        )
        .visibility(defn.visibility);
        if let Some(doc) = defn.docstring.clone() {
            builder = builder.docstring(doc);
        }
        self.current_symbol_table_mut(state).insert(defn.name.clone(), builder.build());

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
            let r = self.current_symbol_table(state);
            let v = r.view();
            if let Some(ModuleEntry::Def { ast: Some(_), .. }) = v.lookup(&defn.name) {
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
        let mr_before: HashSet<Span> = state.method_resolutions.resolved_calls.keys().copied().collect();
        let et_before: HashSet<Span> = state.expr_types.keys().copied().collect();

        self.check_defn_body(state, defn, param_types, ret_ty)
            .map_err(|e| enrich_macro_clause_resolution_error(defn.name.as_ref(), e))?;
        self.resolve_deferred_trait_calls(state, defn.body());
        self.resolve_value_position_trait_methods(state, defn.body(), false);

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

        // FIXME 0344 — generalize-before-cross-defn-use (PURE-parametric only).
        // Write the generalized scheme back to this defn's symbol-table entry
        // NOW, immediately after its body is checked, so a later-source sibling
        // in the same cluster that calls it instantiates a FRESH (polymorphic)
        // copy rather than monomorphising the defn's own still-`mono` Pass-1
        // vars. Without this, a fold helper threading a polymorphic accumulator
        // distinct from the element type (`vec-reduce`) collapses `b`, `a`, and
        // `Vec` onto one var when a sibling Vec-accumulator use is checked.
        //
        // Gated on `trial_scheme.constraints.is_empty()`: this writeback is for
        // PURE parametric polymorphism (the 0344 fold shape). A *constrained*
        // fn (one whose scheme carries trait constraints) MUST keep its `mono`
        // Pass-1 entry so a same-program caller monomorphises it through the
        // shared substitution (the established constrained-fn-vs-same-program
        // behaviour the monomorphisation pipeline depends on); generalizing a
        // constrained fn here would suppress that call-site pinning. The
        // recursion-name binding itself stays `mono(fn_type)` (set in
        // `check_defn_body`) in both cases — we do NOT make the self-reference
        // polymorphic (polymorphic recursion is undecidable in HM). This
        // writeback is idempotent with `finalize`'s Phase-2 writeback
        // (`finalize_check_result_inner` ~line 1109): both recompute from the
        // same `accumulator.defn_type_vars` source vars + the same global
        // `subst`, so the later pass writes the identical scheme.
        if trial_scheme.constraints.is_empty()
            && let Some(ModuleEntry::Def { scheme, .. }) =
                self.current_symbol_table_mut(state).symbols.get_mut(&defn.name)
        {
            *scheme = trial_scheme.clone();
        }

        // Eager constrained-fn detection reads from the trial scheme (regression
        // guard (a): constraint detection still keys off `trial_scheme`, not the
        // entry's scheme field).
        //
        // **The determination point (S83, FIXME 0356/0357, Principle 20;
        // deferred GOT-slot allocation).** Pass-1 registered this fn as
        // `UserFnState::NotDetermined` (slot-less). Now that body-check has run
        // and constraints are known, we finalise the `fn_state`:
        //
        // - **Unconstrained → `Concrete { got_slot }`.** Allocate the slot HERE,
        //   reusing a prior concrete entry's slot on REPL redefinition (the
        //   `existing_callable_slot` carry-forward — orphaning the live GOT
        //   pointer would be a use-after-free; see the helper rustdoc). A
        //   constrained→concrete redef reads `None` (the prior constrained
        //   template carried no slot) and allocates fresh.
        // - **Constrained → `Constrained(cf)`.** Construct the slot-less template
        //   directly (replaces the retired `mark_constrained_template` flip +
        //   `assert_well_formed` phantom-slot guard — there is no sibling slot
        //   field to clear or assert about now). A concrete→constrained redef
        //   drops the old slot; the constrained template is never call-resolved
        //   so there is no live GOT pointer to orphan (no UAF).
        let constrained_fn = if !trial_scheme.constraints.is_empty() {
            if let Some(entry) =
                self.current_symbol_table_mut(state).symbols.get_mut(&defn.name)
                && let ModuleEntry::Def { kind, .. } = entry
            {
                let cf = ConstrainedFn {
                    variant: defn.variants[0].clone(),
                    scheme: trial_scheme,
                };
                *kind = Box::new(DefKind::UserFn {
                    fn_state: UserFnState::Constrained(Box::new(cf)),
                });
            }
            Some(defn.name.clone())
        } else {
            // Unconstrained: allocate (or reuse) the slot and pin `Concrete`.
            // Prefer the Pass-1-captured redefinition slot (the prior concrete
            // entry's slot, stashed before Pass-1 overwrote it with
            // NotDetermined). Fall back to a same-call concrete slot if one
            // somehow already exists, else allocate fresh.
            let mut st = self.current_symbol_table_mut(state);
            let reuse = accumulator
                .redef_slots
                .get(&defn.name)
                .copied()
                .or_else(|| existing_callable_slot(&st, defn.name.as_ref()));
            let got_slot = reuse.unwrap_or_else(|| st.allocate_got_slot());
            // Slot-reuse invariant (replaces the retired `assert_well_formed`):
            // a reused slot is below the high-water mark; a freshly allocated one
            // equals it minus one. Either way it is a valid allocated index.
            debug_assert!(
                got_slot < st.next_got_slot,
                "determination-point got_slot {got_slot} must be within the \
                 allocated range (next_got_slot = {})",
                st.next_got_slot,
            );
            if let Some(ModuleEntry::Def { kind, .. }) =
                st.symbols.get_mut(&defn.name)
            {
                *kind = Box::new(DefKind::UserFn {
                    fn_state: UserFnState::Concrete { got_slot },
                });
            }
            None
        };

        // Extract new method resolutions and expr types added during this form
        let mut form_mr = HashMap::new();
        for (span, res) in &state.method_resolutions.resolved_calls {
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
                // S69 Submission 35: `ast: Option<DefnVariant>` (the single
                // meaningful payload; multi-sig decomposition already split
                // into per-mangled-name Defs upstream of this point).
                *ast = annotated.variants.into_iter().next();
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
        let mr_before: HashSet<Span> = state.method_resolutions.resolved_calls.keys().copied().collect();
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
            let variant_mr_before: HashSet<Span> = state.method_resolutions.resolved_calls.keys().copied().collect();
            let variant_et_before: HashSet<Span> = state.expr_types.keys().copied().collect();

            // Build a temporary single-variant defn for body checking
            let internal_defn = Defn {
                name: internal_name.clone(),
                docstring: defn.docstring.clone(),
                variants: vec![DefnVariant {
                    params: variant.params.clone(),
                    body: variant.body.clone(),
                    span: variant.span,
                }],
                visibility: defn.visibility,
                span: variant.span,
            };

            self.check_defn_body(state, &internal_defn, param_types, ret_ty)?;
            self.resolve_deferred_trait_calls(state, internal_defn.body());
            self.resolve_value_position_trait_methods(state, internal_defn.body(), false);

            // Per-variant post-passes (auto-curry only; overloads deferred to finalize)
            self.resolve_auto_curry(state);

            // Per-variant AST annotation
            {
                let variant_mr: HashMap<Span, ResolvedCall> = state.method_resolutions
                    .resolved_calls
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
                    // S69 Submission 35 narrowing.
                    *ast = annotated.variants.into_iter().next();
                }
            }

            // Eager constrained-fn detection for variant
            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(state, t)).collect(),
                Box::new(self.apply_subst(state, ret_ty)),
            );
            let trial_scheme = self.generalize(state, &fn_type);

            // FIXME 0344 — generalize-before-cross-defn-use, mirrored at the
            // multi-sig variant site (PURE-parametric only): write the
            // generalized scheme back to the variant's `__vN` entry now so a
            // sibling that references it sees a polymorphic, instantiable view.
            // A constrained variant keeps its `mono` entry for same-program
            // call-site monomorphisation. Idempotent with `finalize` Phase 2.
            if trial_scheme.constraints.is_empty()
                && let Some(ModuleEntry::Def { scheme, .. }) =
                    self.current_symbol_table_mut(state).symbols.get_mut(&internal_name)
            {
                *scheme = trial_scheme.clone();
            }

            // Determination point for this multi-sig variant's `__vN` entry
            // (S83, FIXME 0356/0357, Principle 20; deferred GOT-slot
            // allocation). Mirrors the single-sig site: constrained → slot-less
            // `Constrained(cf)`; unconstrained → allocate (or reuse) the slot
            // and pin `Concrete`. The `__vN` internal names are synthesised
            // fresh per multi-sig form, so `existing_callable_slot` reuse only
            // fires on REPL redefinition of the same multi-sig defn.
            if !trial_scheme.constraints.is_empty() {
                if let Some(entry) =
                    self.current_symbol_table_mut(state).symbols.get_mut(&internal_name)
                    && let ModuleEntry::Def { kind, .. } = entry
                {
                    let cf = ConstrainedFn {
                        variant: internal_defn.variants.into_iter().next().expect(
                            "internal_defn constructed with exactly one variant above",
                        ),
                        scheme: trial_scheme,
                    };
                    *kind = Box::new(DefKind::UserFn {
                        fn_state: UserFnState::Constrained(Box::new(cf)),
                    });
                }
            } else {
                let mut st = self.current_symbol_table_mut(state);
                let reuse = accumulator
                    .redef_slots
                    .get(&internal_name)
                    .copied()
                    .or_else(|| existing_callable_slot(&st, internal_name.as_ref()));
                let got_slot = reuse.unwrap_or_else(|| st.allocate_got_slot());
                debug_assert!(
                    got_slot < st.next_got_slot,
                    "multi-sig determination-point got_slot {got_slot} must be \
                     within the allocated range (next_got_slot = {})",
                    st.next_got_slot,
                );
                if let Some(ModuleEntry::Def { kind, .. }) =
                    st.symbols.get_mut(&internal_name)
                {
                    *kind = Box::new(DefKind::UserFn {
                        fn_state: UserFnState::Concrete { got_slot },
                    });
                }
            }
        }

        // Extract new method resolutions and expr types
        let mut form_mr = HashMap::new();
        for (span, res) in &state.method_resolutions.resolved_calls {
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

    /// Re-generalize every defn's scheme from its `defn_type_vars` source vars
    /// resolved through the current global substitution, and clear any
    /// false-positive constrained-fn markers whose schemes ended up
    /// constraint-free.
    ///
    /// Run once after body-checking (the original Phase-2 generalization) and
    /// AGAIN after monomorphisation (FIXME 0349): pass4's call-site result
    /// propagation can pin a caller's previously-loose result var (a
    /// forward-referenced callee left it polymorphic), and re-running this makes
    /// the caller's stored scheme reflect that pinning — turning a spuriously
    /// polymorphic caller (`main : (Fn [] (IO t))`) into its true monomorphic
    /// form (`main : (Fn [] (IO Int))`). Idempotent for defns whose source vars
    /// did not move between calls.
    fn regeneralize_defn_schemes(
        &self,
        state: &mut CheckState,
        accumulator: &ModuleCheckAccumulator,
    ) {
        for (name, (param_types, ret_ty)) in &accumulator.defn_type_vars {
            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(state, t)).collect(),
                Box::new(self.apply_subst(state, ret_ty)),
            );
            let scheme = self.generalize(state, &fn_type);
            let mut st = self.current_symbol_table_mut(state);
            // Demoting a false-positive constrained template to a concrete
            // callable needs a slot (S83 deferred allocation, Principle 20):
            // reuse the entry's own concrete slot if it somehow already has one,
            // otherwise allocate fresh. Computed before the `get_mut` borrow so
            // the `&mut st` allocate doesn't alias the entry borrow.
            let is_false_positive_constrained = scheme.constraints.is_empty()
                && matches!(
                    st.get(name.as_ref()),
                    Some(ModuleEntry::Def { kind, .. })
                        if matches!(
                            kind.as_ref(),
                            DefKind::UserFn { fn_state: UserFnState::Constrained(_) }
                        )
                );
            let demoted_slot = if is_false_positive_constrained {
                Some(existing_callable_slot(&st, name.as_ref())
                    .unwrap_or_else(|| st.allocate_got_slot()))
            } else {
                None
            };
            if let Some(ModuleEntry::Def { scheme: s, kind, .. }) =
                st.symbols.get_mut(name)
            {
                *s = scheme.clone();
                if let Some(got_slot) = demoted_slot {
                    **kind = DefKind::UserFn {
                        fn_state: UserFnState::Concrete { got_slot },
                    };
                }
            }
        }
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
        self.regeneralize_defn_schemes(state, accumulator);

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
                                body: variant.body.clone(),
                                span: variant.span,
                            }],
                            visibility: defn.visibility,
                            span: variant.span,
                        };
                        self.resolve_deferred_trait_calls(state, internal_defn.body());
                        self.resolve_value_position_trait_methods(state, internal_defn.body(), false);
                    }
                } else {
                    self.resolve_deferred_trait_calls(state, defn.body());
                    self.resolve_value_position_trait_methods(state, defn.body(), false);
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
            let r = self.current_symbol_table(state);
            for (name, entry) in r.view().iter() {
                if let ModuleEntry::Def { kind, scheme, ast, .. } = entry {
                    match kind.as_ref() {
                        // Trait-constrained polymorphism: classic constrained
                        // fn marker.
                        DefKind::UserFn { fn_state: UserFnState::Constrained(_) } => {
                            constrained_fn_names.insert(name.clone());
                        }
                        // Pure parametric polymorphism registered by a previous
                        // `check_forms` call (Additive cross-call shape): the
                        // scheme is still polymorphic (`scheme.type_vars` non-empty)
                        // and we have the annotated `ast`. The current
                        // cluster's call sites against this name need
                        // monomorphisation just as if it were constrained —
                        // backend codegen requires concrete CLIF types.
                        // `get_constrained_fn` synthesises a `ConstrainedFn`
                        // view from `ast + scheme` for this case. Matches the
                        // non-constrained `UserFn` states (`Concrete` /
                        // `NotDetermined`) — the slot, if any, is irrelevant here.
                        DefKind::UserFn { fn_state }
                            if !matches!(fn_state, UserFnState::Constrained(_))
                                && !scheme.type_vars.is_empty()
                                && ast.is_some() =>
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

        // FIXME 0349 — re-generalize after monomorphisation. pass4's call-site
        // result propagation (`monomorphise_call`) can pin a caller's
        // previously-loose result var (a forward-referenced callee left it
        // polymorphic). Re-running generalization makes the caller's STORED
        // scheme reflect that pinning, so a spuriously-polymorphic caller
        // collapses to its true monomorphic scheme and the backend emits a
        // direct call to the mono variant rather than the polymorphic template.
        self.regeneralize_defn_schemes(state, accumulator);

        // Pass 5: overloads and auto-curry already resolved per-defn.
        // Drain any remaining entries (e.g., from mono defn generation).
        self.resolve_pending_overloads(state)?;
        self.resolve_auto_curry(state);

        // Surface any field-accessor synthesis collisions with a NON-accessor
        // binding (FIXME 0351(a), spec §5.2.6 safe disposition): the accessor
        // was suppressed (the existing binding wins) and the clash is reported
        // as a non-fatal warning so it is never silent. Drained so a redefining
        // REPL re-check does not double-report.
        for (accessor_name, type_name) in std::mem::take(&mut state.deferred_accessor_collisions) {
            state.warnings.push(cranelisp_types::Warning {
                kind: cranelisp_types::WarningKind::ShadowedName,
                message: format!(
                    "field accessor `{accessor_name}` for type `{type_name}` \
                     conflicts with a name already bound to `{accessor_name}`; \
                     the accessor is suppressed and the existing binding is kept"
                ),
                span: Span::SYNTHETIC,
            });
        }

        // Sweep post-pass outputs from self.state into the accumulator.
        // Post-passes (resolve_deferred_trait_calls, pass4_monomorphise,
        // resolve_pending_overloads, resolve_auto_curry) write new method
        // resolutions into state.method_resolutions. Merge these into
        // the accumulator so it becomes the single authoritative source.
        accumulator.method_resolutions.extend(
            std::mem::take(&mut state.method_resolutions).resolved_calls,
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
                                annotate_variant_from_maps(
                                    existing,
                                    &resolved_expr_types,
                                    &accumulator.method_resolutions,
                                );
                                apply_subst_to_variant(&state.subst, existing);
                            }
                        }
                    }
                    TopLevel::Defn(defn) => {
                        if let Some(ModuleEntry::Def { ast: Some(existing), .. }) =
                            sym_table.symbols.get_mut(&defn.name)
                        {
                            annotate_variant_from_maps(
                                existing,
                                &resolved_expr_types,
                                &accumulator.method_resolutions,
                            );
                            apply_subst_to_variant(&state.subst, existing);
                        }
                    }
                    TopLevel::TraitImpl(ti) => {
                        for method in &ti.methods {
                            let target_name = ti.target.head_ref().map(|r| r.name.as_ref()).unwrap_or("");
                            let mangled = format!("{}.{}${}", ti.trait_name, method.name, target_name);
                            let mangled_sym = Symbol::from(mangled.as_str());
                            if let Some(ModuleEntry::Def { ast: Some(existing), .. }) =
                                sym_table.symbols.get_mut(&mangled_sym)
                            {
                                annotate_variant_from_maps(
                                    existing,
                                    &resolved_expr_types,
                                    &accumulator.method_resolutions,
                                );
                                apply_subst_to_variant(&state.subst, existing);
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
    // Unified multi-form check driver — drives `check_forms`'s internal
    // pipeline (Pass 1 register, Pass 2 check bodies, finalize) over a
    // `&[TopLevel]` slice and returns the `CheckResult` (including display
    // info). The production entry surface is `check_forms` in `form.rs`,
    // which discards the display-bearing `CheckResult`; this driver retains
    // it so in-crate tests can assert on inferred types / schemes.
    // =================================================================

    /// Drive the cluster pipeline over a `TopLevel` slice and return the
    /// display-bearing `CheckResult`.
    ///
    /// Mirrors `check_forms`'s internal Pass 1 / Pass 2 / finalize ordering.
    /// `Expr` variants are wrapped in a synthetic zero-arg `Defn` named
    /// `__expr` so they flow through the same passes as regular definitions.
    /// Used by in-crate test fixtures only — the production path is the
    /// `check_forms` free function in `form.rs`.
    #[cfg(test)]
    #[must_use = "check result contains display info needed by REPL-display tests"]
    pub(crate) fn check_via_forms(
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

        // Pass 2: Check bodies for all forms.
        // FIXME 0354 Bug A: mirror `check_forms`' production path — restore the
        // post-Pass-1 bound-param constraints before each form's body check so a
        // prior form's body-instantiation residue (e.g. a `Display`-only var
        // from `show`) does not bleed into this form's generalize.
        let pass1_constraints = state.active_constraints.clone();
        for form in &working_program {
            state.active_constraints = pass1_constraints.clone();
            let result = self.check_form_body(state, form, &mut accumulator)?;
            self.merge_form_result_inner(state, &mut accumulator, result);
        }

        // Check bodies of default method defns too.
        let defaults_for_body: Vec<Defn> = accumulator.default_method_defns.clone();
        for defn in &defaults_for_body {
            state.active_constraints = pass1_constraints.clone();
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
    /// Used only by the `check_via_forms` test driver.
    #[cfg(test)]
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
    /// Used only by the `check_via_forms` test driver.
    #[cfg(test)]
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
                let r = self.current_symbol_table(state);
                if let Some(ModuleEntry::Def { scheme, .. }) = r.view().lookup(&defn.name) {
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
            // Post S69 Submission 35: `ast: Option<DefnVariant>`. No `name`
            // field on DefnVariant — the symbol-table key carries the name;
            // mangling lives at the entry insertion below.
            let annotated_ast: Option<DefnVariant> = match internal_entry {
                Some(ModuleEntry::Def { ast, .. }) => ast,
                _ => None,
            };
            // A resolved multi-sig mangled variant is a concrete callable born
            // with its slot (S83 deferred allocation, Principle 20): the slot
            // rides inside the `Concrete` `fn_state`, not a flat `Def` field.
            let slot = st.allocate_got_slot();
            let mut builder = ModuleEntry::def(
                scheme.clone(),
                DefKind::UserFn { fn_state: UserFnState::Concrete { got_slot: slot } },
            )
            .visibility(defn.visibility)
            .param_names(variant.params.iter().map(|(n, _)| n.clone()).collect());
            if let Some(doc) = defn.docstring.clone() {
                builder = builder.docstring(doc);
            }
            if let Some(ast) = annotated_ast {
                builder = builder.ast(ast);
            }
            st.insert(mangled.clone(), builder.build());

            // Build the mangled defn for the backend
            mangled_defns.push(Defn {
                name: mangled.clone(),
                docstring: defn.docstring.clone(),
                variants: vec![DefnVariant {
                    params: variant.params.clone(),
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

        let mut builder = ModuleEntry::def(
            base_scheme,
            DefKind::Overloaded { variants: overload_variants },
        )
        .visibility(defn.visibility);
        if let Some(doc) = defn.docstring.clone() {
            builder = builder.docstring(doc);
        }
        self.current_symbol_table_mut(state).insert(defn.name.clone(), builder.build());

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
                state.method_resolutions.resolved_calls.insert(
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
        // by checking DefKind::UserFn { fn_state: UserFnState::Constrained(..) }.
        let mut names = HashSet::new();

        for defn in defns {
            let r = self.current_symbol_table(state);
            if let Some(ModuleEntry::Def { kind, .. }) = r.view().lookup(&defn.name)
                && let DefKind::UserFn { fn_state: UserFnState::Constrained(_) } = kind.as_ref()
            {
                names.insert(defn.name.clone());
            }
        }

        names
    }

    /// Resolve a stacked trait-bound parameter annotation (`:Eq :Display a`,
    /// spec §3.9.2) to a fresh constrained type variable (spec §3.9.3
    /// try-type-then-trait; FIXME 0346 / 0341 typecheck half).
    ///
    /// Allocates a fresh `Type::Var`, resolves each `TraitRef` to its
    /// `FQTraitName` (a qualified ref names its module directly; a bare ref is
    /// resolved via the current-module-or-prelude chain), and records the
    /// (var, trait) pairs on `state.active_constraints`. `generalize` then lifts
    /// these onto the defn's `Scheme.constraints` when the var is quantified.
    ///
    /// The binder is deliberately NOT unified with any concrete type here — it
    /// is a fresh constrained var, and any concrete shape is contributed by the
    /// body's use of the parameter (the bounds restrict which instantiations are
    /// legal, exactly as a body-driven constrained-fn does).
    fn resolve_bound_param(
        &self,
        state: &mut CheckState,
        bounds: &[cranelisp_types::TraitRef],
        span: Span,
    ) -> Result<Type, CranelispError> {
        let (var_ty, var_id) = self.fresh_var_id();
        for tref in bounds {
            let home = match &tref.module {
                // Qualified ref (`:fmt/Display`) names its module directly.
                Some(m) => m.clone(),
                // Bare ref (`:Display`) resolves via current-module-or-prelude.
                None => self
                    .resolve_trait(state, tref.name.as_ref(), span)
                    .map_err(CranelispError::from)?,
            };
            let fqtn = cranelisp_types::FQTraitName::new(home, tref.name.clone());
            state.active_constraints.add(var_id, fqtn);
        }
        Ok(var_ty)
    }

    /// Create fresh type variables for a function's parameters and return type,
    /// respecting any annotations, and register the signature in the symbol table.
    ///
    /// Returns `(param_types, return_type)` for use in body checking.
    /// Shared by the per-form registration path (`check_form_register_single_defn`)
    /// and the multi-sig variant registration to prevent the two paths from
    /// diverging as rings add complexity.
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
            let r = self.current_symbol_table(state);
            if let Some(ModuleEntry::Def { scheme, ast: Some(_), .. }) =
                r.view().lookup(&defn.name)
                && scheme.type_vars.is_empty()
                && scheme.constraints.is_empty()
                && let Type::Fn(param_types, ret_ty) = &scheme.ty
            {
                return Ok((param_types.clone(), (**ret_ty).clone()));
            }
        }

        let mut param_types = Vec::new();
        for (_name, ann) in defn.params().iter() {
            let param_ty = match ann {
                // Stacked trait-bound annotation (`:Eq :Display a`, spec §3.9.2):
                // the binder is "an unspecified type satisfying these traits"
                // (spec §3.9.3 try-type-then-trait). It resolves to a FRESH
                // constrained type variable, NOT a concrete type — so it is
                // intercepted here, before delegating to the pure
                // `TypeExpr -> Type` resolver (which has no fresh-var allocator
                // or constraint sink). The traits accumulate onto the var via
                // `active_constraints`, which `generalize` later lifts onto the
                // defn's `Scheme.constraints` (FIXME 0346 / 0341 typecheck half).
                Some(cranelisp_types::TypeExpr::Bounds(bounds)) => {
                    self.resolve_bound_param(state, bounds, defn.span)?
                }
                Some(ann) => {
                    let var_map = HashMap::new();
                    self.resolve_type_expr_in_module(
                        ann, &var_map, &state.current_module, defn.span,
                    )?
                }
                None => self.fresh_var(),
            };
            param_types.push(param_ty);
        }
        let ret_ty = self.fresh_var();

        let fn_type = Type::Fn(param_types.clone(), Box::new(ret_ty.clone()));
        let scheme = mono(fn_type);

        // Upsert: preserve existing ast AND code if the symbol is being
        // redefined (REPL Additive mode, module reload, or trait impl method
        // re-registration). Preserving ast prevents double-checking of trait
        // impl methods that were already type-checked by check_impl_method.
        //
        // **Deferred GOT-slot allocation (S83, FIXME 0356/0357, Principle 20;
        // amends Decision 0035).** Pass-1 NO LONGER allocates a slot here. With
        // callability now a `DefKind::UserFn` property (`UserFnState`), Pass-1
        // cannot yet know whether this fn is `Concrete` (slotted) or
        // `Constrained` (slot-less) — Pass-2 constraint detection runs later.
        // So Pass-1 registers `UserFnState::NotDetermined` (slot-less by
        // construction; nothing may call an as-yet-undetermined fn). The slot is
        // allocated at the determination point in the unconstrained Pass-2 arm
        // (`check_form_body` / `check_form_body_multi_sig`), where the
        // redefinition slot-reuse carry-forward (below) now lives. See the
        // `UserFnState` rustdoc "Timing-wall resolution".
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
        let (existing_ast, existing_code) = st.get(defn.name.as_ref())
            .map(|e| match e {
                ModuleEntry::Def { ast, code, .. } => (ast.clone(), code.clone()),
                _ => (None, None),
            })
            .unwrap_or((None, None));

        // NOT converted to `ModuleEntry::def(...)` (FIXME 0241): this site
        // carries `code: existing_code` forward to preserve the existing
        // `Code::Jit` Arc across REPL redefinition (use-after-free guard, see
        // the block comment above). `DefBuilder` deliberately has no `code`
        // setter (`code` is runtime state, written downstream), so the builder
        // cannot express this entry — the struct literal is retained here.
        st.insert(
            defn.name.clone(),
            ModuleEntry::Def {
                scheme,
                visibility: defn.visibility,
                docstring: defn.docstring.clone(),
                param_names: defn.params().iter().map(|(n, _)| n.clone()).collect(),
                kind: Box::new(DefKind::UserFn {
                    fn_state: UserFnState::NotDetermined,
                }),
                callees: Vec::new(),
                trait_origin: None,
                seq: 0,
                ast: existing_ast,
                code: existing_code,
            },
        );

        Ok((param_types, ret_ty))
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
        for ((param_name, _), param_ty) in defn.params().iter().zip(param_types.iter()) {
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

    // --- Monomorphisation passes ---

    /// Pass 4 (batch): scan all defn bodies for calls to constrained functions
    /// and generate monomorphised specializations.
    fn pass4_monomorphise(
        &self,
        state: &mut CheckState,
        defns: &[&Defn],
        constrained_fn_names: &HashSet<Symbol>,
    ) -> Result<Vec<MonoDefn>, CranelispError> {
        // Collect call sites: (fn_name, arg_spans, call_span, home_module).
        //
        // `home_module` is `None` for a call to a LOCALLY-defined constrained fn
        // (`monomorphise_call` re-checks its body in the current module's scope,
        // the as-built path). It is `Some(home)` for a call to an IMPORTED
        // constrained fn that chain-resolves to a constrained `Def` in another
        // module — the mono body must be re-checked in that DEFINING module's
        // import context, where its trait-method + helper references resolve
        // (FIXME 0355; the feature half of the resolved 0354 SIGSEGV).
        //
        // FIXME 0349 — scan EVERY defn body, including those that are themselves
        // in `constrained_fn_names`. A constrained/polymorphic defn can still
        // host a *concrete* call to another constrained fn that needs a mono
        // variant. Under forward-reference ordering a caller (`main`) can stay
        // spuriously polymorphic (its result var never pinned because the callee
        // it forward-references was generalized before the helper that ties its
        // accumulator) and thus land in `constrained_fn_names`; skipping its body
        // wholesale meant the `(reduce add-i64 0 [1 2 3])` call site was never
        // collected and `reduce$Int+Vec` was never created — so `main` called the
        // polymorphic template and returned the initial accumulator (0344/0349).
        // We must NOT skip such bodies; we only skip a call from a fn to ITSELF
        // (the generic self-recursion of a constrained defn is not a concrete
        // call site — its arg types are the defn's own generic vars).
        let mut local_calls = Vec::new();
        for defn in defns {
            Self::collect_constrained_calls_excluding_self(
                defn.body(),
                &defn.name,
                constrained_fn_names,
                &mut local_calls,
            );
        }
        let mut call_sites: Vec<(Symbol, Vec<Span>, Span, Option<ModuleFullPath>)> = local_calls
            .into_iter()
            .map(|(name, spans, span)| (name, spans, span, None))
            .collect();

        // FIXME 0355 — collect call sites for IMPORTED callees that
        // chain-resolve to a constrained (or pure-parametric) `Def` in another
        // module. These are NOT in `constrained_fn_names` (their local name is a
        // `ModuleEntry::Import`), so the local collection above never sees them.
        for defn in defns {
            self.collect_imported_constrained_calls(
                state,
                defn.body(),
                constrained_fn_names,
                &mut call_sites,
            );
        }

        // Nothing to monomorphise (neither local constrained fns nor imported
        // constrained call sites) — bail before resolving expr_types.
        if call_sites.is_empty() {
            return Ok(Vec::new());
        }

        // Resolve expr_types so we can look up concrete arg types
        let resolved_expr_types = self.resolve_expr_types(state);

        // Monomorphise each call site and record dispatch mappings
        let mut mono_defns = Vec::new();
        let mut seen: HashMap<String, JitSymbol> = HashMap::new();

        for (fn_name, arg_spans, call_span, home_module) in &call_sites {
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
                state.method_resolutions.resolved_calls.insert(
                    *call_span,
                    ResolvedCall::SigDispatch { mangled_name: mangled.clone() },
                );
                continue;
            }

            if let Some(mono) = self.monomorphise_call(
                state, fn_name, &arg_types, *call_span, home_module.as_ref(),
            )? {
                let mangled = JitSymbol::from(mono.defn.name.as_ref());
                // Record dispatch for this call site
                state.method_resolutions.resolved_calls.insert(
                    *call_span,
                    ResolvedCall::SigDispatch { mangled_name: mangled.clone() },
                );
                seen.insert(key, mangled);
                mono_defns.push(mono);
            }
        }

        Ok(mono_defns)
    }

    /// Walk a defn body collecting calls to IMPORTED callees that chain-resolve
    /// to a constrained (trait-bound) or pure-parametric polymorphic `Def` in
    /// another module (FIXME 0355).
    ///
    /// A locally-defined constrained fn is named in `constrained_fn_names` and is
    /// already collected by [`Self::collect_constrained_calls_excluding_self`];
    /// here we skip those and look only at bare `Var` callees whose local name
    /// chain-resolves (via [`Self::resolve_terminal_entry_and_home`]) to a
    /// terminal in a DIFFERENT module. When that terminal is a constrained or
    /// still-polymorphic `UserFn` `Def`, the call needs a cross-module mono
    /// variant re-checked in the terminal's HOME scope, so we record the call
    /// site with `Some(home)`.
    fn collect_imported_constrained_calls(
        &self,
        state: &CheckState,
        expr: &Expr,
        constrained_fn_names: &HashSet<Symbol>,
        out: &mut Vec<(Symbol, Vec<Span>, Span, Option<ModuleFullPath>)>,
    ) {
        if let Expr::Apply { callee, args, span, .. } = expr
            && let Expr::Var { name, .. } = callee.as_ref()
            && !constrained_fn_names.contains(name)
            && let Some((entry, home)) =
                self.resolve_terminal_entry_and_home(&state.current_module, name.as_ref())
            && home != state.current_module
            && Self::entry_is_monomorphisable_polymorphic(&entry)
        {
            let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
            out.push((name.clone(), arg_spans, *span, Some(home)));
        }
        for_each_child_expr(expr, |child| {
            self.collect_imported_constrained_calls(state, child, constrained_fn_names, out)
        });
    }

    /// Does this terminal entry need a monomorphised specialisation when called
    /// with concrete arg types? (FIXME 0355 — mirrors `get_constrained_fn`'s two
    /// accepted shapes: a trait-constrained `UserFn`, or a pure-parametric
    /// polymorphic `UserFn` carrying a stored annotated `ast`.)
    fn entry_is_monomorphisable_polymorphic(entry: &ModuleEntry<C>) -> bool {
        if let ModuleEntry::Def { kind, scheme, ast, .. } = entry {
            match kind.as_ref() {
                DefKind::UserFn { fn_state: UserFnState::Constrained(_) } => true,
                DefKind::UserFn { fn_state }
                    if !matches!(fn_state, UserFnState::Constrained(_))
                        && !scheme.type_vars.is_empty()
                        && ast.is_some() =>
                {
                    true
                }
                _ => false,
            }
        } else {
            false
        }
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
        // Per-node action: record a call site when this node is an Apply whose
        // callee is a bare reference to a constrained fn.
        if let Expr::Apply { callee, args, span, .. } = expr
            && let Expr::Var { name, .. } = callee.as_ref()
            && constrained_fn_names.contains(name)
        {
            let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
            out.push((name.clone(), arg_spans, *span));
        }
        // Recurse into children via the shared enumeration helper.
        for_each_child_expr(expr, |child| {
            Self::collect_constrained_calls(child, constrained_fn_names, out)
        });
    }

    /// Like [`collect_constrained_calls`] but excludes calls a constrained fn
    /// makes to ITSELF (FIXME 0349).
    ///
    /// A constrained/polymorphic defn's self-recursion is the generic definition,
    /// not a concrete monomorphisation site — its argument types are the defn's
    /// own generic vars, so there is no concrete instantiation to specialise.
    /// Every OTHER constrained call inside the body (including calls to *other*
    /// constrained fns from within a constrained fn) IS a real call site and must
    /// be collected, so a forward-referenced helper gets its mono variant created
    /// regardless of source definition order.
    fn collect_constrained_calls_excluding_self(
        expr: &Expr,
        self_name: &Symbol,
        constrained_fn_names: &HashSet<Symbol>,
        out: &mut Vec<(Symbol, Vec<Span>, Span)>,
    ) {
        if let Expr::Apply { callee, args, span, .. } = expr
            && let Expr::Var { name, .. } = callee.as_ref()
            && constrained_fn_names.contains(name)
            && name != self_name
        {
            let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
            out.push((name.clone(), arg_spans, *span));
        }
        for_each_child_expr(expr, |child| {
            Self::collect_constrained_calls_excluding_self(
                child, self_name, constrained_fn_names, out,
            )
        });
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

            state.method_resolutions.resolved_calls.insert(
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

}

#[cfg(test)]
mod tests;
