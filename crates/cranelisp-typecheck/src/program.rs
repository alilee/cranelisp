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
    Expr, FQSymbol, JitSymbol, ModuleEntry, ModuleFullPath, ParametricFn,
    ModuleStrategy, MonoDefn, ResolvedCall, Span, Subst, Symbol, SymbolTable, TopLevel, Type,
    TypeId, UserFnState, Visibility, Warning, apply,
};

// Test-only imports: used exclusively by the `#[cfg(test)]` `check_via_forms`
// driver, `compute_display_info` / `wrap_exprs_as_defns` helpers, and the
// in-crate test module.
#[cfg(test)]
use cranelisp_types::{CompileContext, DisplayInfo};

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
        Expr::LaunchContinue { launched, continuation, .. } => {
            f(launched);
            f(continuation);
        }
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
        Expr::LaunchContinue { launched, continuation, .. } => {
            f(launched);
            f(continuation);
        }
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

/// Rename the bare `Expr::Var` at exactly `target_span` to `new_name`
/// (FIXME 0374 — fn-value-argument monomorphisation). Used to redirect a
/// polymorphic fn-value reference (`mk`) to its minted concrete mono instance
/// (`mk$Int`) in a stored AST so the backend's `compile_fn_as_value` takes the
/// concrete (slotted) instance's GOT slot. Matches on span identity so only the
/// exact fn-value occurrence is renamed, never another use of the same name.
pub(crate) fn rename_var_at_span(expr: &mut Expr, target_span: Span, new_name: &Symbol) {
    if let Expr::Var { name, span, .. } = expr
        && *span == target_span
    {
        *name = new_name.clone();
        return;
    }
    for_each_child_expr_mut(expr, |child| rename_var_at_span(child, target_span, new_name));
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

/// Build the concrete-boundary `MonoExpr` codegen view (`MonoDefnVariant`) for a
/// codegen-bound `Concrete` entry from its fully-annotated, subst-resolved
/// `DefnVariant` body (S84 Phase-3, FIXME 0392 / `concrete-boundary-type.md`
/// §3.0). Shared by the single-sig, multi-sig-mangled, and trait-impl-method
/// concrete-defn population sites.
///
/// Returns `Some(view)` when `MonoExpr::from_expr` succeeds (every body node
/// fully concrete) — the expected case for a body-checked concrete defn.
///
/// **Returns `None` when `from_expr` fails** (a residual `Var` / un-annotated
/// node reached a value position). Unlike the *mono-instance* seam — which hard-
/// errors with the §3.11.1 ambiguity message because a minted mono instance MUST
/// be concrete (Phase-4 part A) — an ordinary concrete defn's `ast` body can
/// legitimately carry a residual `Var` at a node the **current `ast`-path
/// codegen never reads its `inferred_type` for** (e.g. a multi-sig variant with
/// an unconstrained param mangled `f$Var`, or the result var of a forward-
/// reference Apply that the backend resolves via the symbol table, not the
/// node). Hard-erroring here would reject programs the `ast` path compiles
/// today. So the view is best-effort: `Some` populates the codegen-bound entry
/// (the produces-but-unread Phase-3 input); `None` is the populate-gap signal
/// the backend read-flip (FIXME 0391) handles via its single relocated backstop.
/// **This `None`-vs-hard-error asymmetry between concrete defns and mono
/// instances is a recorded finding — see FIXME 0393.**
pub(crate) fn build_concrete_codegen_view(
    name: &Symbol,
    variant: &DefnVariant,
    pattern_ctors: &HashMap<Span, cranelisp_types::FQSymbol>,
) -> Option<cranelisp_types::MonoDefnVariant> {
    match cranelisp_types::MonoExpr::from_expr(&variant.body, pattern_ctors) {
        Ok(mono_body) => Some(cranelisp_types::MonoDefnVariant {
            name: name.clone(),
            params: variant.params.iter().map(|(n, _)| n.clone()).collect(),
            body: mono_body,
            span: variant.span,
            mode_summary: None,
        }),
        Err(_) => None,
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

/// Extract the user-fn reference edges added to `state.user_fn_refs` during
/// one form's checking (FIXME 0470, S101), attributed to `caller`.
///
/// Sibling of the `form_mr` span-set delta for `method_resolutions`: `before`
/// is the key snapshot taken at the top of `check_form_body_*`; everything
/// newer belongs to the form under check (including references inside nested
/// lambdas, which are inferred within the enclosing defn's body — the L-R2
/// carrier attribution).
fn extract_user_fn_ref_edges(
    state: &CheckState,
    caller: &Symbol,
    before: &HashSet<Span>,
) -> Vec<(Symbol, FQSymbol)> {
    state
        .user_fn_refs
        .iter()
        .filter(|(span, _)| !before.contains(span))
        .map(|(_, fq)| (caller.clone(), fq.clone()))
        .collect()
}

/// Group call graph edges by caller, sort + deduplicate, and write to `ModuleEntry`.
///
/// Used by both `merge_form_result` (eager write so the scheduler can read callees
/// immediately) and `finalize_check_result` (canonical final write that includes
/// any edges from post-passes).
///
/// **Completeness contract (FIXME 0470 + 0472, S101).** The edge feed is the
/// union of `ResolvedCall`-derived edges (trait methods, sig-dispatch,
/// auto-curry) and the `CheckState.user_fn_refs` recording (every
/// statically-resolved call- OR value-position reference to a
/// `DefKind::UserFn` `Def`), harvested by the ONE shared
/// `harvest_callee_edges` helper at every body-check seam: the two Pass-2
/// per-form seams (through this sink) AND the Pass-1
/// `finalize_impl_method_writeback` seam (impl-provided, default, and HKT
/// trait-method bodies — written directly to the mangled entry). A checked
/// entry's `callees` therefore names EVERY statically-resolved user-fn
/// reference in its body, with one deliberate residue: mono-instance bodies
/// (`recheck_body_for_mono`) carry no own edges — their constrained
/// TEMPLATE's entry carries the complete set and the call-site recorder gives
/// the caller→template edge, so the reverse closure is preserved through the
/// template chain. The S101 dependent-recompilation transaction derives its
/// reverse index from this set (`design/int/session-transaction.md`
/// §3.2/§3.3); silently dropping edges starves the affected-set closure.
/// Guarded by the `program::tests::callees_*` completeness-contract tests
/// (`tests/plan/s101-coverage-postmortem.md` §2.1).
pub(crate) fn write_callees_to_module_entries<C, L>(
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
/// A located §3.11.1 codegen-reaching ambiguity, enriched with the offending
/// arity clause + param for the diagnostic (0576).
struct AmbiguousForm {
    /// The enclosing `defn` name.
    name: Symbol,
    /// The reference-site span of the unpinned value position.
    span: Span,
    /// The offending clause's arity — `Some` only for a MULTI-arity `defn` (a
    /// single-sig defn has one obvious clause, so it keeps the plain message).
    clause_arity: Option<usize>,
    /// The unpinned param/binder name, when the position is a bare non-synthetic
    /// `Var` (0568: never a `__`-prefixed internal binder).
    param: Option<Symbol>,
}

impl AmbiguousForm {
    /// The user-facing ambiguity message. Names the offending arity CLAUSE and
    /// unpinned PARAM when known (0576) — "each arity clause is type-checked
    /// independently" (§5.1.2), so the fix is a per-clause annotation — and falls
    /// back to the plain fn-level message otherwise.
    fn message(&self) -> String {
        let where_ = match self.clause_arity {
            Some(arity) => format!("the {arity}-arg arity clause of `{}`", self.name),
            None => format!("`{}`", self.name),
        };
        match &self.param {
            Some(p) => format!(
                "ambiguous type: the parameter `{p}` in {where_} is not pinned — \
                 each arity clause is type-checked independently (spec §5.1.2), so \
                 add a `:Type` annotation to `{p}` in that clause"
            ),
            None => format!(
                "ambiguous type; add an annotation to pin the type of the \
                 polymorphic value bound in {where_}"
            ),
        }
    }
}

pub(crate) struct FormCheckResult {
    /// Method resolutions discovered while checking this form.
    /// In Pass 1: empty (registration produces no resolutions).
    /// In Pass 2: resolutions from the body of this defn.
    pub(crate) method_resolutions: HashMap<Span, ResolvedCall>,

    /// The pattern-constructor STORAGE identities discovered while checking this
    /// form's bodies (`MethodResolutions.pattern_ctors`, keyed by
    /// `Pattern::Constructor.span`; S109 W1.2 §10.2). Accumulated cross-form so
    /// the finalize codegen-view rebuild can populate `MonoMatchArm.resolved_ctor`
    /// AFTER the per-form `state.method_resolutions` has been drained.
    pub(crate) pattern_ctors: HashMap<Span, cranelisp_types::FQSymbol>,

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
            pattern_ctors: HashMap::new(),
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
    pub(crate) pattern_ctors: HashMap<Span, cranelisp_types::FQSymbol>,
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
    /// **Written-var lexical scope from Pass-1 signature registration** (spec
    /// §3.3 [S109]), keyed by the same defn name (multi-arity clauses under
    /// their `{name}__v{i}` internal name). Each maps the written type-var names
    /// in the parameter annotations (`:a`, `:(Box a)`) to the ONE rigid `TypeId`
    /// they minted. Pass-2 `check_defn_body` installs it as the definition's
    /// `written_var_scope` + seeds `rigid_vars`, so a body/nested-`fn`
    /// occurrence of the same name co-refers to the same rigid var (the 0588
    /// cross-pass threading; empty for a signature with no written type vars).
    pub(crate) defn_var_scopes: HashMap<Symbol, HashMap<Symbol, TypeId>>,
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
            pattern_ctors: HashMap::new(),
            expr_types: HashMap::new(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings: Vec::new(),
            call_graph_edges: Vec::new(),
            defn_type_vars: HashMap::new(),
            defn_var_scopes: HashMap::new(),
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

/// Map from a multi-sig defn's base name to the MANGLED variant names that
/// `register_mangled_variants` inserted for it (S91 Wave-7, FIXME 0432 Face A).
/// Drives the finalize re-annotation + return-type refresh, both of which must
/// key variant entries by their live mangled names, not the removed internal
/// `{name}__v{i}` keys.
type MangledNamesByBase = HashMap<Symbol, Vec<Symbol>>;

/// A polymorphic fn-value passed as an argument into a HOF, recorded per
/// enclosing defn for post-mint `Var` rewrite (FIXME 0374 / 0488 sig b):
/// (enclosing_defn, bare_fn_value_symbol, arg_span, concrete_param_types,
/// home_of_imported_callee).
type FnValueArgSite = (Symbol, Symbol, Span, Vec<Type>, Option<ModuleFullPath>);

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

/// Convert a single param annotation `TypeExpr` into the `TraitRef` it would
/// denote as a trait bound, for the try-type-then-trait fallback (spec §3.9.3,
/// S86 D4). A trait bound is a bare or qualified trait NAME with no type
/// arguments (spec §3.9.2), so only `TypeExpr::Named` qualifies — `Applied`
/// (e.g. `(Option Int)`) carries type arguments and is a concrete type, never a
/// single trait bound; `TypeVar`/`SelfType`/`FnType`/`Bounds` are not bare
/// names. The as-written module qualification is preserved (`:fmt/Display`).
pub(crate) fn single_trait_bound_from_annotation(
    ann: &cranelisp_types::TypeExpr,
) -> Option<cranelisp_types::TraitRef> {
    match ann {
        cranelisp_types::TypeExpr::Named(tref) => Some(cranelisp_types::TraitRef::new(
            tref.module.clone(),
            cranelisp_types::TraitName::from(tref.name.as_ref()),
        )),
        _ => None,
    }
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

/// Mangle a single concrete type into distinguishing text — THE ONE canonical,
/// total type-mangler (FIXME 0519, Principle 7). Every concrete `Type` variant
/// is recursed so that the produced string is a lossless, collision-free
/// encoding of the type structure (Principle 20):
///
/// - `ADT(name, args)` recurses its args — `Vec$Int` ≠ `Vec$String` (cures the
///   0483 ADT-arg-erasure axis).
/// - `Fn(params, ret)` recurses params + ret in a balanced-bracket form
///   `Fn(<p1>,<p2>;<ret>)` — NEVER dropped (curing the latent Fn-param-drop
///   collision axis). Balanced parens keep nested `Fn` extents unambiguous.
/// - `TyConApp` / scalars — present as distinguishing text.
///
/// Both mono-instance naming (`traits::build_mangled_name`, home-qualified) and
/// multi-sig overload-variant naming (`mangle_sig`, same-module) route their
/// type components through this single function, so the name grain and any
/// dedup-key grain agree by construction.
pub(crate) fn mangle_type(ty: &Type) -> String {
    match ty {
        Type::Int => "Int".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Float => "Float".to_string(),
        Type::Fn(params, ret) => {
            let param_parts: Vec<String> = params.iter().map(mangle_type).collect();
            format!("Fn({};{})", param_parts.join(","), mangle_type(ret))
        }
        Type::ADT(name, args) => {
            if args.is_empty() {
                name.to_string()
            } else {
                let arg_parts: Vec<String> = args.iter().map(mangle_type).collect();
                format!("{}${}", name, arg_parts.join("+"))
            }
        }
        Type::Var(_) => "Var".to_string(),
        Type::TyConApp(id, args) => {
            if args.is_empty() {
                format!("TyCon{id}")
            } else {
                let arg_parts: Vec<String> = args.iter().map(mangle_type).collect();
                format!("TyCon{id}${}", arg_parts.join("+"))
            }
        }
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

    /// The ONE shared callee-edge harvest, applied at EVERY body-check seam
    /// (FIXME 0472 — the `codegen_view` precedent: one helper, all seams).
    ///
    /// Combines the two edge channels for the body just checked, attributed
    /// to `caller`:
    /// - `ResolvedCall`-derived edges from the caller-supplied
    ///   method-resolutions delta (trait methods, sig-dispatch, auto-curry);
    /// - the `CheckState.user_fn_refs` delta since `ufr_before` (every
    ///   statically-resolved call-/value-position user-fn reference,
    ///   FIXME 0470).
    ///
    /// Seams wired: `check_form_body_single_defn` / `check_form_body_multi_sig`
    /// (edges ride `FormCheckResult.call_graph_edges` into the merge/finalize
    /// sinks) and `finalize_impl_method_writeback` (impl-provided, default,
    /// and HKT trait-method bodies — Pass-1 bodies outside the per-form
    /// channel; edges written directly to the mangled entry, mirroring its
    /// `ast`/`codegen_view` direct writes). Deliberately NOT wired:
    /// `recheck_body_for_mono` — a mono instance's body duplicates its
    /// constrained TEMPLATE's body, whose edges are already complete via the
    /// template's own defn-form check, and the call-site recorder gives the
    /// caller→template edge; the reverse closure reaches the minting caller
    /// through the template chain, and mono instances are re-minted whenever
    /// that caller re-typechecks.
    pub(crate) fn harvest_callee_edges(
        &self,
        state: &CheckState,
        caller: &Symbol,
        method_resolutions_delta: &HashMap<Span, ResolvedCall>,
        ufr_before: &HashSet<Span>,
    ) -> Vec<(Symbol, FQSymbol)> {
        let mut edges =
            self.extract_call_graph_edges(state, caller, method_resolutions_delta);
        edges.extend(extract_user_fn_ref_edges(state, caller, ufr_before));
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
                // §8.6.4 (FIXME 0514): reject a type def whose name is already in
                // scope via an explicit import/export or the implicit prelude —
                // the same mode-uniform seam as the value-def case below.
                self.reject_def_over_binding(state, &Symbol::from(name.as_ref()), *span)?;
                self.register_type_def(
                    state, name, docstring, type_params, constructors, *visibility, *span,
                )?;
                Ok(FormCheckResult::empty())
            }
            TopLevel::TraitDecl(decl) => {
                // §8.6.4 (S108 Wave-G convergence): route the trait NAME and
                // each METHOD name through the ONE definition seam BEFORE
                // registration — a `deftrait`/`deftrait-` whose trait name or
                // any method name is already in scope via an explicit
                // import/export or the implicit prelude is a compile-time
                // conflict, never a shadow (§8.8.1: the prelude is just an
                // implicit `(import [prelude [*]])`). Placed at the arm (not
                // inside `register_trait_decl`) so it covers the plain AND HKT
                // registration branches with one call site, keeping
                // `check_form_register` the ONE visible place all typecheck-side
                // definition forms hit the seam. A trait method is a fresh
                // module-scope binding with a fresh terminal — it can never
                // dedup — so each method name is checked identically to the
                // trait name.
                self.reject_def_over_binding(
                    state, &Symbol::from(decl.name.as_ref()), decl.span,
                )?;
                for method in &decl.methods {
                    self.reject_def_over_binding(state, &method.name, decl.span)?;
                }
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
                // §8.6.4 (FIXME 0514): reject a definition whose bare name is
                // already bound in scope by an explicit import/export or the
                // implicit prelude (the no-exception ruling). Fires identically
                // in every mode — the single shared seam both REPL/Additive and
                // batch/Replace traverse. Own-redefinition (home == current) is
                // NOT a collision and is left to the redefinition machinery.
                self.reject_def_over_binding(state, &defn.name, defn.span)?;
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
        let (param_types, ret_ty, var_scope) = self.register_defn_signature(state, defn)?;
        accumulator.defn_type_vars.insert(defn.name.clone(), (param_types, ret_ty));
        accumulator.defn_var_scopes.insert(defn.name.clone(), var_scope);
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
            let (param_types, ret_ty, var_scope) =
                self.register_defn_signature(state, &internal_defn)?;
            accumulator.defn_var_scopes.insert(internal_name.clone(), var_scope);
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
        // FIXME 0488 sig c: settle forward-reference chains in already-determined
        // polymorphic templates so this form's body is checked against tied
        // schemes, not the stale under-tied ones a 0344 writeback froze before a
        // forward-referenced helper's own body ran.
        self.resettle_polymorphic_schemes(state, accumulator);
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
        // The Pass-1 written-var scope threaded through to the body check
        // (spec §3.3 [S109]; empty when no written type vars — 0588).
        let var_scope = accumulator
            .defn_var_scopes
            .get(&defn.name)
            .cloned()
            .unwrap_or_default();

        // Snapshot method_resolutions and expr_types sizes so we can extract
        // just the new entries added during this form's checking.
        let mr_before: HashSet<Span> = state.method_resolutions.resolved_calls.keys().copied().collect();
        let et_before: HashSet<Span> = state.expr_types.keys().copied().collect();
        let ufr_before: HashSet<Span> = state.user_fn_refs.keys().copied().collect();

        self.check_defn_body(state, defn, param_types, ret_ty, var_scope)
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
        } else if !trial_scheme.ty.is_concrete()
            && defn.name.as_ref() != "__expr"
        {
            // S84 Wave 1b (FIXME 0374/0378, Principle 20): the slot gate is now
            // TOTAL — `slot ⟺ is_concrete()`, with NO `monomorphisable-from-
            // params` carve-out. ANY unconstrained non-concrete def (including a
            // RESULT-ONLY-var def: `(defn test-x [] None)` → `(Fn [] (Option a))`,
            // `(defn empty [] [])` → `(Fn [] (Vec a))`) is slot-less `Polymorphic`.
            // The former carve-out kept result-only-var defs `Concrete`-with-a-slot
            // so `discover_test_names` could find them; test fns are now explicit
            // monomorphisation ROOTS (`register_test_fn_mono_roots` in
            // `pass4_monomorphise`), which mint a concrete `(Fn [] (Option String))`
            // instance under the bare name — so a degenerate test fn is found via
            // that concrete instance's slot, not the polymorphic original.
            //
            // **`__expr` is still excluded.** A synthetic top-level-expression
            // defn is a VALUE to evaluate, never a reusable polymorphic template,
            // and the REPL/`--run` driver requires its GOT slot to invoke it. A
            // residual `Type::Var` in an `__expr` result is either a transient
            // unresolved-multi-sig-dispatch shape (concrete at runtime) or a bare
            // polymorphic value (displayed via introspection per §3.11.2, never
            // compiled to a runtime value). Either way it stays `Concrete` here.
            //
            // A def carrying a residual `Type::Var` is NOT directly callable as a
            // value (only its concrete mono instances are), so it is slot-less by
            // construction — the `Polymorphic` arm, a sibling to `Constrained`.
            // This forecloses the leak where a generic-unconstrained def took a
            // `Concrete` slot while carrying a `Type::Var`, reaching
            // `classify(Type::Var)` → the unsound `<1024` RC guard → the
            // `(Box a)`-through-HOF SIGSEGV. Only `pass4_monomorphise` instances
            // (concrete) are slotted. Drops any prior concrete slot (the redef
            // carry-forward is moot — a `Polymorphic` template is never
            // call-resolved, so no live GOT pointer is orphaned).
            if let Some(entry) =
                self.current_symbol_table_mut(state).symbols.get_mut(&defn.name)
                && let ModuleEntry::Def { kind, .. } = entry
            {
                let pf = ParametricFn {
                    variant: defn.variants[0].clone(),
                    scheme: trial_scheme,
                };
                *kind = Box::new(DefKind::UserFn {
                    fn_state: UserFnState::Polymorphic(Box::new(pf)),
                });
            }
            None
        } else {
            // Unconstrained AND concrete: allocate (or reuse) the slot and pin
            // `Concrete`.
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
                    fn_state: UserFnState::Concrete { got_slot, mode_summary: None },
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

            // S84 Phase-3 (FIXME 0392): populate the concrete-boundary
            // `codegen_view` for an ordinary CONCRETE single-sig defn (e.g.
            // `main`, `(defn f [x] (+ x 1))` at a concrete instantiation). Only
            // a `Concrete` entry is a `compile_to_module` codegen target —
            // `Polymorphic`/`Constrained` templates (and any non-`Def`) get no
            // view (they are mono SOURCES, excluded by `defined_symbols()`). The
            // view is built from the SAME fully-annotated, subst-resolved body
            // the `ast` carries, via `MonoExpr::from_expr`.
            //
            // **The validation payoff (FIXME 0392 §VALIDATION):** a
            // `Concrete{slot}` defn that passed body-check (§3.11.1) has a fully
            // concrete body ⇒ `from_expr` MUST succeed. A failure on a
            // legitimate concrete defn is a real §3.11.1-position gap — surfaced
            // HERE as the unified ambiguity / could-not-monomorphise error
            // (NOT silently set to `None`, which would later trip the Phase-3
            // backend backstop).
            let is_concrete_codegen_target = matches!(
                self.current_symbol_table(state).view().lookup(&defn.name),
                Some(ModuleEntry::Def {
                    kind,
                    ..
                }) if matches!(
                    kind.as_ref(),
                    DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                )
            );
            let codegen_view = if is_concrete_codegen_target {
                annotated.variants.first().and_then(|variant| {
                    build_concrete_codegen_view(&defn.name, variant, &state.method_resolutions.pattern_ctors)
                })
            } else {
                None
            };

            if let Some(ModuleEntry::Def { ast, codegen_view: cv, .. }) =
                self.current_symbol_table_mut(state).symbols.get_mut(&defn.name)
            {
                // S69 Submission 35: `ast: Option<DefnVariant>` (the single
                // meaningful payload; multi-sig decomposition already split
                // into per-mangled-name Defs upstream of this point).
                *ast = annotated.variants.into_iter().next();
                *cv = codegen_view;
            }
        }

        // Harvest call graph edges (Decision 21 + FIXME 0470/0472): the
        // ResolvedCall channel + the user-fn references recorded during this
        // form's body inference — call- and value-position alike, uniform
        // carrier. ONE shared helper across all body-check seams.
        let call_graph_edges =
            self.harvest_callee_edges(state, &defn.name, &form_mr, &ufr_before);

        let warnings = std::mem::take(&mut state.warnings);

        Ok(FormCheckResult {
            method_resolutions: form_mr,
            pattern_ctors: state.method_resolutions.pattern_ctors.clone(),
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
        let ufr_before: HashSet<Span> = state.user_fn_refs.keys().copied().collect();

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
            // Each arity clause is a DISJOINT written-var scope (§5.1.2 clause
            // independence; spec §3.3 [S109], u3) — clause i's rigid `:a` is a
            // distinct skolem from clause j's.
            let var_scope = accumulator
                .defn_var_scopes
                .get(&internal_name)
                .cloned()
                .unwrap_or_default();

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

            self.check_defn_body(state, &internal_defn, param_types, ret_ty, var_scope)?;
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
            } else if !trial_scheme.ty.is_concrete() {
                // S84 Wave 1b (FIXME 0374/0378, Principle 20): a multi-sig
                // *variant* whose finalised type still carries ANY `Type::Var`
                // (parameter OR result position) is non-concrete and
                // trait-unconstrained → slot-less `Polymorphic`, NOT
                // `Concrete{slot}`. The slot gate is TOTAL — slot ⟺ concrete,
                // with no `monomorphisable-from-params` carve-out.
                if let Some(entry) =
                    self.current_symbol_table_mut(state).symbols.get_mut(&internal_name)
                    && let ModuleEntry::Def { kind, .. } = entry
                {
                    let pf = ParametricFn {
                        variant: internal_defn.variants.into_iter().next().expect(
                            "internal_defn constructed with exactly one variant above",
                        ),
                        scheme: trial_scheme,
                    };
                    *kind = Box::new(DefKind::UserFn {
                        fn_state: UserFnState::Polymorphic(Box::new(pf)),
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
                        fn_state: UserFnState::Concrete { got_slot, mode_summary: None },
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

        // Harvest call graph edges for the variants (Decision 21 + FIXME
        // 0470/0472) — ONE shared helper across all body-check seams.
        // Multi-sig variant edges are attributed to the base defn name since
        // the mangled names aren't known until overload resolution in finalize.
        let call_graph_edges =
            self.harvest_callee_edges(state, &defn.name, &form_mr, &ufr_before);

        let warnings = std::mem::take(&mut state.warnings);

        Ok(FormCheckResult {
            method_resolutions: form_mr,
            pattern_ctors: state.method_resolutions.pattern_ctors.clone(),
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
        accumulator.pattern_ctors.extend(result.pattern_ctors);
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
            // Demoting a false-positive constrained template (its constraints
            // vanished after final substitution) — the re-slotting decision is
            // the SAME structural gate as the determination point (FIXME 0374,
            // Principle 20): slot ⟺ concrete.
            //   - constraints vanished AND scheme concrete → `Concrete{slot}`
            //     (reuse the entry's own concrete slot if any, else allocate).
            //   - constraints vanished BUT scheme still generic (`Type::Var`)
            //     → `Polymorphic` (slot-less); only its mono instances slot.
            // A constrained template that generalised to a still-generic
            // unconstrained type must NOT be re-slotted `Concrete` — that would
            // re-introduce the non-concrete-def-with-slot leak.
            // A `Constrained` OR `Polymorphic` template whose regeneralized
            // scheme is now constraint-free is a re-slotting candidate (both are
            // slot-less templates that may have become concrete). The
            // re-slotting follows the SAME structural gate as the determination
            // point (FIXME 0374, Principle 20): slot ⟺ concrete.
            let is_reslot_candidate = scheme.constraints.is_empty()
                && matches!(
                    st.get(name.as_ref()),
                    Some(ModuleEntry::Def { kind, .. })
                        if matches!(
                            kind.as_ref(),
                            DefKind::UserFn {
                                fn_state: UserFnState::Constrained(_)
                                    | UserFnState::Polymorphic(_)
                            }
                        )
                );
            // Compute the demoted slot before the `get_mut` borrow so the
            // `&mut st` allocate doesn't alias the entry borrow. Only the
            // concrete branch needs a slot. A `Polymorphic` def whose scheme
            // collapsed to a concrete type (e.g. `g : ∀a.a→a` pinned to
            // `(Fn [Int] Int)` by a direct concrete call `(g 1)` + the post-mono
            // regeneralisation) MUST become `Concrete{slot}` — otherwise it is a
            // slot-less `Polymorphic` arm carrying a concrete scheme, an
            // inconsistent state where a same-program caller cannot resolve it
            // through a slot (the REPL mutual-forward-ref `undefined function`
            // symptom).
            // Keep `Polymorphic` (slot-less) whenever the def is still
            // non-concrete (S84 Wave 1b TOTAL gate — slot ⟺ concrete, no
            // monomorphisable-from-params carve-out). Otherwise allocate a slot:
            // a concrete scheme is a plain `Concrete{slot}`. A result-only-var
            // scheme (`(Fn [] (Option a))`) stays `Polymorphic` here; if it is a
            // test-fn entry it is given a concrete slotted instance by the
            // test-fn mono-root pass (`register_test_fn_mono_roots`).
            let stay_polymorphic = is_reslot_candidate && !scheme.ty.is_concrete();
            let demoted_slot = if is_reslot_candidate && !stay_polymorphic {
                Some(existing_callable_slot(&st, name.as_ref())
                    .unwrap_or_else(|| st.allocate_got_slot()))
            } else {
                None
            };
            if let Some(ModuleEntry::Def { scheme: s, kind, ast, .. }) =
                st.symbols.get_mut(name)
            {
                *s = scheme.clone();
                if is_reslot_candidate {
                    if let Some(got_slot) = demoted_slot {
                        **kind = DefKind::UserFn {
                            fn_state: UserFnState::Concrete { got_slot, mode_summary: None },
                        };
                    } else if let Some(variant) = ast.clone() {
                        // Still non-concrete: slot-less `Polymorphic`, carrying
                        // the stored annotated body + new scheme for later
                        // monomorphisation. (For a `Constrained` false-positive
                        // that stays generic-unconstrained this is the correct
                        // demotion; for a `Polymorphic` that stayed generic this
                        // is idempotent.)
                        **kind = DefKind::UserFn {
                            fn_state: UserFnState::Polymorphic(Box::new(ParametricFn {
                                variant,
                                scheme: scheme.clone(),
                            })),
                        };
                    }
                }
            }
        }
    }

    /// Re-settle the stored schemes of already-determined **`Polymorphic`**
    /// cluster members from their `defn_type_vars` source vars through the
    /// current global substitution — scheme-only, no re-slotting (FIXME 0488
    /// sig c).
    ///
    /// **The ordering bug this fixes.** A fn that FORWARD-references a
    /// same-cluster helper (`vreduce` calling the later-defined `vreduce-loop`)
    /// has its 0344 generalize-writeback run at the END of its OWN body check —
    /// BEFORE the helper's body ties the accumulator↔result vars. The writeback
    /// therefore freezes an UNDER-tied scheme (`vreduce : (Fn [f a (Vec b)] c)`,
    /// result untied). A LATER sibling (`vconcat = (vreduce vec-push va vb)`)
    /// then instantiates that stale scheme and inherits the under-tie into its
    /// OWN scheme (`(Fn [a (Vec b)] c)`), which fails pass-4's all-args-concrete
    /// guard at every composed consumer turn (`undefined function: <outer>`).
    /// `finalize`'s [`Self::regeneralize_defn_schemes`] re-ties the
    /// forward-referencing fn correctly — but only AFTER the sibling's body was
    /// already checked against the stale scheme.
    ///
    /// Running this once BEFORE each subsequent form's body check settles the
    /// forward-reference chain (`vreduce-loop`'s body has run → its ties are in
    /// `state.subst` → `vreduce` re-ties) so the sibling sees the tied scheme.
    /// It re-runs the SAME idempotent generalization `finalize` already
    /// performs, only earlier; it does not change HOW generalization computes.
    ///
    /// **Scoped by construction (does not touch the 0344 balance).** A sibling
    /// that USES a member instantiates a FRESH copy of the member's (now
    /// generalized) scheme, so re-generalizing the member later never disturbs
    /// the sibling's already-done inference — it only picks up ties from the
    /// member's OWN forward-referenced helpers. Restricted to already-determined
    /// `Polymorphic` templates (`NotDetermined` = not-yet-body-checked members
    /// are skipped so a forward reference still binds their shared Pass-1 vars,
    /// which 0349's mono-time result pinning relies on) and gated constraint-free
    /// (mirroring the 0344 body-check writeback) so a `Constrained` fn's mono
    /// Pass-1 entry is never disturbed. Concrete members carry no re-tieable vars
    /// and are skipped after a cheap lookup.
    fn resettle_polymorphic_schemes(
        &self,
        state: &mut CheckState,
        accumulator: &ModuleCheckAccumulator,
    ) {
        for (name, (param_types, ret_ty)) in &accumulator.defn_type_vars {
            // Only already-determined `Polymorphic` templates are re-tie
            // candidates. The read guard is a temporary in this `matches!`.
            let is_poly_determined = matches!(
                self.current_symbol_table(state).view().lookup(name),
                Some(ModuleEntry::Def { kind, .. })
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }
                    )
            );
            if !is_poly_determined {
                continue;
            }
            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(state, t)).collect(),
                Box::new(self.apply_subst(state, ret_ty)),
            );
            let scheme = self.generalize(state, &fn_type);
            // Pure-parametric only (mirror the 0344 writeback gate). A scheme
            // that acquired constraints is left to the constrained-fn path.
            if !scheme.constraints.is_empty() {
                continue;
            }
            if let Some(ModuleEntry::Def { scheme: s, .. }) =
                self.current_symbol_table_mut(state).symbols.get_mut(name)
            {
                *s = scheme;
            }
        }
    }

    /// Find a CODEGEN-REACHING value position whose finalised type retains an
    /// unconstrained `Type::Var` that no reachable use site pins (spec §3.11.1 —
    /// the ambiguity rule). Returns the offending `(name, span)` so the caller
    /// raises the located `TypeError` ("ambiguous type; add an annotation").
    ///
    /// **Scope (the delicate part — disposition triple, spec §3.11):**
    ///
    /// - **§3.11.1 (REJECT):** a `let`-bound value that must become a runtime
    ///   value while a type var is free, with nothing pinning it — the canonical
    ///   `(let [x (identity None)] (match x [None 0 (Some _) 1]))` shape: `x` has
    ///   type `(Option a)`, `a` is unpinned (the `match` scrutinises only the
    ///   tag), `x` is consumed at runtime. THIS is the codegen-reaching position
    ///   the check fires on. A `let`-binding is the canonical §3.11.1 worked
    ///   example; the value is forced to a concrete runtime representation that
    ///   does not exist while `a` is free.
    ///
    /// - **§3.11.2 (DISPLAY, not error):** a BARE top-level polymorphic value at
    ///   the REPL (`None`, `[]`) is `__expr`'s own body, NOT a `let`-binding —
    ///   it is displayed via introspection, never compiled to a runtime value,
    ///   so it is OUT of scope here (the check only inspects `let`-binding values,
    ///   not the `__expr` result itself).
    ///
    /// - **§3.11.3 (ADMIT):** a named polymorphic defn (`(defn empty [] [])`,
    ///   `(defn ambig [] None)`) is sound and dead-for-codegen until instantiated.
    ///   Its body is the defn result, not a `let`-binding, so it is never flagged.
    ///   The structural slot gate makes such a def slot-less `Polymorphic`; the
    ///   ambiguity check never inspects a defn's own result type.
    ///
    /// The check resolves each `let`-binding value's type through the final
    /// substitution (`state.subst`) and flags a residual free var that sits
    /// INSIDE a structure (`(Option a)`, `(Vec a)`) — a bare-`Var` value type is
    /// a transient unresolved-dispatch shape pinned by its use, skipped.
    /// A located §3.11.1 ambiguity, enriched (0576) with the offending arity
    /// CLAUSE (`clause_arity`, `Some` only for a multi-arity `defn`) and the
    /// unpinned PARAM name (`param`, absent when the position is not a bare
    /// binder or is synthetic).
    fn find_ambiguous_top_level_form(
        &self,
        state: &CheckState,
        accumulator: &ModuleCheckAccumulator,
        working_program: &[TopLevel],
    ) -> Option<AmbiguousForm> {
        for top in working_program {
            let TopLevel::Defn(defn) = top else { continue };
            // The vars LEGITIMATELY polymorphic for this defn are the free vars
            // of its finalised function type — these are exactly what generalise
            // into the defn's scheme and are pinned per-instantiation by
            // monomorphisation (§4.4: "a var quantified into the scheme is
            // fine"). A value-position type whose free vars are ALL in this set
            // is sound; a value position carrying a var OUTSIDE it is genuinely
            // un-pinnable (free-at-root) → ambiguous. This is the discriminator
            // that admits the polymorphic-accumulator fold (`reduce`'s body
            // positions carry `reduce`'s own scheme vars) while rejecting an
            // unpinned `(Option a)` in a concrete-scheme defn like `main`.
            let sig = accumulator.defn_type_vars.get(&defn.name);
            let allowed_vars: std::collections::HashSet<u32> = sig
                .map(|(param_types, ret_ty)| {
                    let mut vars = std::collections::HashSet::new();
                    for t in param_types {
                        vars.extend(cranelisp_types::free_vars(&self.apply_subst(state, t)));
                    }
                    vars.extend(cranelisp_types::free_vars(&self.apply_subst(state, ret_ty)));
                    vars
                })
                .unwrap_or_default();
            // §3.11.3 disposition 1 — a POLYMORPHIC definition (its own signature
            // retains a free type var after substitution) is a sound scheme:
            // EVERY free var in its body is a scheme var, pinned per-instantiation
            // by monomorphisation at concrete use sites, NOT free-at-root. The
            // codegen-reaching ambiguity error (§3.11.1 / disposition 2) is a
            // property of a use at a CONCRETE-scheme definition (`main`-like) that
            // leaves a var unpinned — never of a polymorphic definition. Skip the
            // body scan for a polymorphic defn entirely. This also keeps the
            // full-concreteness verdict robust against the 0344 cross-defn
            // generalize/instantiate var-id reconciliation gap: a polymorphic
            // defn's body may carry a body-local instantiation var that the
            // pre-body `defn_type_vars` signature did not record by the same id
            // (the fold `collect`'s `vec-push : (Fn [(Vec a) a] (Vec a))` arg) —
            // that var is quantifiable, not ambiguous (§3.11.3). The narrowing is
            // disposition-faithful: a non-concrete signature ⇒ disposition 1.
            let defn_is_polymorphic = !allowed_vars.is_empty();
            if defn_is_polymorphic {
                continue;
            }
            let multi_arity = defn.variants.len() > 1;
            for variant in &defn.variants {
                if let Some((span, param)) =
                    self.find_ambiguous_value_position(state, &variant.body, &allowed_vars)
                {
                    return Some(AmbiguousForm {
                        name: defn.name.clone(),
                        span,
                        // The offending CLAUSE (0576) — named by its arity only
                        // for a multi-arity `defn`, so a single-sig defn keeps the
                        // plain message.
                        clause_arity: multi_arity.then_some(variant.params.len()),
                        param,
                    });
                }
            }
        }
        None
    }

    /// POSITION-COMPLETE §3.11.1 ambiguity scan (S84 Wave 2, FIXME 0379/0380 —
    /// belt-and-braces ruling). Recursively scan an expression and fire the
    /// per-node verdict on the resolved type of EVERY codegen-reaching value
    /// position `for_each_child_expr` visits — not only `let` bindings. Returns
    /// the offending value's span.
    ///
    /// **Why position-complete (the 0379 hole).** The old scanner only applied
    /// the verdict on `Expr::Let` binding values, but a free `Type::Var` reaches
    /// codegen through many NON-`let` value positions — a `match` scrutinee
    /// (`(Pure (match (id Non) …))`), a fn-call arg, a vec element, a ctor field,
    /// an `if` branch, a `ParBind` binding. Those were recursed-into but not
    /// CHECKED, so an unpinned `(Option a)` in such a position slipped past both
    /// this check AND the backend codegen. The recursion was already complete (via
    /// `for_each_child_expr`); only the verdict was `let`-gated. This lifts the
    /// verdict to every value-producing child.
    ///
    /// **The verdict is FULL CONCRETENESS (spec/03-types.md §3.11.1, tightened
    /// commit `2290aa9`).** A codegen-reaching value whose resolved type is NOT
    /// fully concrete — i.e. retains ANY residual free `Type::Var` — is the
    /// §3.11.1 ambiguity error. There is **no representation-based exemption**:
    /// `(Vec a)`, `(Fn [a] a)`, `(Option a)`, a bare `Type::Var`, a `TyConApp`
    /// head — all reject when unpinned at a codegen-reaching value position, even
    /// when their machine shape is determinate. The strictness is full
    /// concreteness, NOT machine-shape determinacy.
    ///
    /// The verdict is therefore `!ty.is_concrete()` (equivalently
    /// `ConcreteType::from_type(ty).is_err()`) — the SAME full-concreteness
    /// predicate that gates the GOT-slot at the typecheck slot gate, and the same
    /// verdict the backend `ConcreteType` boundary encodes (no `Var` admissible).
    /// The two sides agree by construction (Principle 7; FIXME 0386,
    /// `design/arch/concrete-boundary-type.md` §1.4 / §3.1). Under full
    /// monomorphisation-from-roots a genuinely free var in a codegen-reaching
    /// position means NO root pins it → ambiguous (§3.11.1); the §4.4
    /// `allowed_vars` filter in [`Self::find_ambiguous_value_position`] excludes
    /// the scheme-quantified vars that are pinned per-instantiation (the
    /// polymorphic-accumulator fold's body positions), so this verdict fires only
    /// on a genuinely free-at-root var.
    fn is_codegen_ambiguous_type(&self, ty: &Type) -> bool {
        !ty.is_concrete()
    }


    /// Returns the span of the first codegen-reaching value position carrying a
    /// free-at-root `Type::Var`, plus the offending binder NAME when that
    /// position is a bare `Expr::Var` (a param/`let` use) — so the diagnostic can
    /// name the unpinned param (0576). A synthetic `__`-prefixed binder is NOT
    /// surfaced (0568 — never leak an internal binder into user text).
    fn find_ambiguous_value_position(
        &self,
        state: &CheckState,
        expr: &Expr,
        allowed_vars: &std::collections::HashSet<u32>,
    ) -> Option<(Span, Option<Symbol>)> {
        // The CALLEE of an `Apply` is a DISPATCH position, not a runtime value
        // position — an overloaded / multi-sig / trait-method callee carries a
        // transient bare `Type::Var` pinned-away by sig/dictionary resolution
        // (the §4.2 table lists `Apply { args }`, NOT the callee). Recurse INTO
        // the callee (a nested ambiguous arg there is still caught) but never
        // apply the per-node verdict ON it.
        let callee_span = match expr {
            Expr::Apply { callee, .. } => Some(callee.span()),
            _ => None,
        };

        // Apply the per-node verdict to every value-producing child, then recurse
        // into it. `for_each_child_expr` is the single child-enumeration source
        // of truth — visiting its children covers `Apply.args`, `Match`
        // scrutinee + arm bodies, `If` branches, `VecLit` elements, `ConstrADT`
        // fields, `Let`/`ParBind` bindings + body, `Lambda`/`Trace`/`Annotate`
        // inner — i.e. EVERY codegen-reaching value position.
        let mut found: Option<(Span, Option<Symbol>)> = None;
        for_each_child_expr(expr, |child| {
            if found.is_some() {
                return;
            }
            // The `working_program` ASTs are the INPUT shapes (their
            // `inferred_type` fields are unset — annotation lands on the stored
            // `ModuleEntry::Def.ast`). Read each child's type from
            // `state.expr_types` by span (still populated at the finalisation
            // boundary, before the accumulator drain), resolved through the final
            // substitution. Same mechanism the old `let`-leg used.
            let resolved = child
                .inferred_type()
                .map(|ty| apply(&state.subst, ty))
                .or_else(|| {
                    state
                        .expr_types
                        .get(&child.span())
                        .map(|ty| apply(&state.subst, ty))
                });
            if Some(child.span()) != callee_span
                && let Some(resolved) = resolved
                // The verdict: NOT fully concrete at a codegen-reaching value
                // position — ANY residual free `Type::Var` is the §3.11.1
                // ambiguity error (full concreteness, no representation
                // exemption; spec/03-types.md §3.11.1, tightened). A direct
                // constructor value (`None`, `(Some x)`) at an unpinned type is
                // rejected too — its tag-vs-pointer determinacy does NOT rescue
                // the unpinned var (the FIXME-0382 direct-constructor skip is
                // removed; `(is-some None)` is now the clean ambiguity error,
                // the spec's own worked example).
                && self.is_codegen_ambiguous_type(&resolved)
                // §4.4 nuance: a value position whose free vars are ALL
                // quantified into the enclosing defn's scheme is SOUND — the var
                // is pinned per-instantiation by monomorphisation (this admits
                // the polymorphic-accumulator fold's body positions). Only a var
                // OUTSIDE the defn's quantified set is free-at-root and genuinely
                // un-pinnable → ambiguous.
                // §4.4 nuance: a value position whose free vars are ALL
                // quantified into the enclosing defn's scheme is SOUND — pinned
                // per-instantiation by monomorphisation. For a CONCRETE-scheme
                // defn (the only kind scanned here — polymorphic defns are skipped
                // at the caller per §3.11.3 disposition 1) `allowed_vars` is empty,
                // so any free var is free-at-root → ambiguous.
                && cranelisp_types::free_vars(&resolved)
                    .iter()
                    .any(|v| !allowed_vars.contains(v))
            {
                // Name the unpinned binder when the position is a bare `Var`
                // (a param / `let` use), skipping synthetic `__`-prefixed
                // binders so the internal name never leaks (0568/0576).
                let binder = match child {
                    Expr::Var { name, .. } if !name.as_ref().starts_with("__") => {
                        Some(name.clone())
                    }
                    _ => None,
                };
                found = Some((child.span(), binder));
                return;
            }
            // Not flagged at this position — descend.
            found = self.find_ambiguous_value_position(state, child, allowed_vars);
        });
        found
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
        // `multi_sig_mangled_names` (base → [mangled]) IS needed below: the
        // re-annotation block re-keys multi-sig variant entries by their mangled
        // names (the internal `{name}__v{i}` keys are gone post-registration).
        let mut multi_sig_mangled_names = MangledNamesByBase::new();
        let _multi_sig_defns = self.resolve_multi_sig_overloads(
            state,
            working_program,
            &accumulator.defn_type_vars,
            &mut multi_sig_mangled_names,
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
        // S84 Phase-3 (FIXME 0392): each instance's concrete-boundary `MonoExpr`
        // view is set ON its `ModuleEntry::Def.codegen_view` at
        // `register_mono_entry` (produces-but-unread until the backend read-flip,
        // FIXME 0391). The validation payoff (every instance's body run through
        // `MonoExpr::from_expr` at the seam) is unchanged; the transitional
        // parallel `Vec<MonoDefnVariant>` return is retired.
        let _mono_defns =
            self.pass4_monomorphise(state, &single_sig_defns, &constrained_fn_names)?;

        // FIXME 0349 — re-generalize after monomorphisation. pass4's call-site
        // result propagation (`monomorphise_call`) can pin a caller's
        // previously-loose result var (a forward-referenced callee left it
        // polymorphic). Re-running generalization makes the caller's STORED
        // scheme reflect that pinning, so a spuriously-polymorphic caller
        // collapses to its true monomorphic scheme and the backend emits a
        // direct call to the mono variant rather than the polymorphic template.
        self.regeneralize_defn_schemes(state, accumulator);

        // S84 Wave 1b (FIXME 0374/0378 issue 3): register discovered `test-*`
        // entry points as monomorphisation ROOTS — mint a concrete
        // `(Fn [] (Option String))` instance under the bare name for any
        // slot-less `Polymorphic` degenerate test fn (`(defn test-x [] None)`).
        // Run AFTER both `regeneralize_defn_schemes` passes so the regeneralize's
        // unconditional scheme-writeback cannot demote the minted concrete
        // scheme back to `(Option a)`. The discovery readers
        // (`discover_test_names` / `discover_eligible_tests`) read the concrete
        // instance's slot under the same name.
        self.register_test_fn_mono_roots(state)?;

        // FIXME 0373(ii) / 0374 / 0378 — §3.11.1 ambiguity check (SECONDARY
        // backstop; the structural slot gate above is the PRIMARY SIGSEGV-
        // prevention mechanism). Per the user ruling 2026-06-16 (spec §3.11
        // disposition triple), this check fires ONLY for a CODEGEN-REACHING
        // unpinned polymorphic value (§3.11.1 — a `let`-bound value consumed at
        // runtime while a type var is free), NOT for a bare REPL polymorphic
        // value (§3.11.2 — displayed via introspection) nor a named polymorphic
        // defn (§3.11.3 — sound, dead-for-codegen). `find_ambiguous_top_level_form`
        // is scoped to `let`-binding value positions, so the two REPL display
        // guards stay green and named poly defns are admitted.
        if let Some(amb) = self.find_ambiguous_top_level_form(state, accumulator, working_program) {
            return Err(CranelispError::TypeError {
                message: amb.message(),
                location: ErrorLocation::from_span(amb.span),
            });
        }

        // Pass 5: overloads and auto-curry already resolved per-defn.
        // Drain any remaining entries (e.g., from mono defn generation).
        self.resolve_pending_overloads(state)?;
        self.resolve_auto_curry(state);

        // S91 Wave-7 (FIXME 0432 Face A): a multi-sig variant whose body
        // contains an in-body self-call has a return type that is only pinned
        // once `resolve_pending_overloads` resolves that self-call. But the
        // variant return types were captured into `resolved_overloads`, the
        // persisted `DefKind::Overloaded` base entry, and the mangled entries'
        // schemes back in `resolve_multi_sig_overloads` (Pass 2.5) — BEFORE
        // that resolution. Without this refresh the variant return stays a free
        // var: a later REPL cluster rehydrates `resolved_overloads` from the
        // stale persisted `OverloadVariant.ret_type` and a call to the variant
        // displays an unresolved type (`:a` instead of `:primitives/Int`).
        self.refresh_multi_sig_variant_ret_types(state, &multi_sig_mangled_names);

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
        //
        // S84 ConcreteType arc (FIXME 0394/0395): rebuild each `Concrete{slot}`
        // entry's `codegen_view` HERE, from the now-post-mono-annotated `ast`.
        // The single-sig population at `check_form_body_single_defn` ran at body-
        // check time — BEFORE `pass4_monomorphise` rewrote this caller's call-node
        // `resolved_call` to its `SigDispatch{mangled}` target (`(id 7)`'s `id`
        // call → `SigDispatch{id$Int}`). That early view carried a stale
        // `resolved_call: None` on the polymorphic call, so the backend could not
        // consume it (it rebuilt from `ast` instead — the dual-source FIXME 0395
        // forecloses). This re-annotation block has just refreshed `existing`
        // (the `ast`) from `accumulator.method_resolutions` (now carrying the
        // post-mono `SigDispatch`s) — so rebuilding the view from `existing` HERE
        // makes `codegen_view` POST-mono-correct. The backend reads it on the live
        // path; the dual-source collapses to one (Principle 7).
        //
        // Scope: only a `UserFn { Concrete{slot} }` entry is a body-AST-node-typed
        // codegen target (§3.1.1) — its view is the one the backend backstop
        // guards. Mono-instance entries already populated their post-mono view at
        // the `register_mono_entry` seam (their bodies are built post-subst with
        // the dispatch already resolved); they are not re-walked here.
        {
            // Snapshot the pattern-ctor sidecar BEFORE the mutable symbol-table
            // borrow — `current_symbol_table_mut(state)` borrows `state` mutably,
            // so the codegen-view rebuild inside the closure cannot also read
            // `state.method_resolutions` (§10.2 requires the sidecar to reach
            // `from_expr`). The map is per-cluster (spans → FQSymbols), cheap.
            let pattern_ctors_for_views = accumulator.pattern_ctors.clone();
            let sym_table = &mut self.current_symbol_table_mut(state);
            // Reannotate `existing` from the final side maps + subst, then, for a
            // `Concrete{slot}` codegen target, rebuild `codegen_view` from the
            // refreshed (post-mono) variant.
            let reannotate_and_refresh_view =
                |name: &Symbol,
                 entry: &mut ModuleEntry<C>,
                 resolved_expr_types: &HashMap<Span, Type>,
                 method_resolutions: &HashMap<Span, ResolvedCall>,
                 subst: &Subst| {
                    if let ModuleEntry::Def { ast: Some(existing), kind, codegen_view: cv, .. } =
                        entry
                    {
                        annotate_variant_from_maps(existing, resolved_expr_types, method_resolutions);
                        apply_subst_to_variant(subst, existing);
                        if matches!(
                            kind.as_ref(),
                            DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                        ) {
                            *cv = build_concrete_codegen_view(name, existing, &pattern_ctors_for_views);
                        }
                    }
                };
            for top in working_program {
                match top {
                    TopLevel::Defn(defn) if defn.is_multi_sig() => {
                        // S91 Wave-7 (FIXME 0432 Face A): re-annotate each
                        // variant body under its MANGLED key. The internal
                        // `{name}__v{i}` entries were removed-and-reinserted as
                        // mangled names by `register_mangled_variants` (Pass
                        // 2.5), so a stale internal-key lookup misses and an
                        // in-body self-call's `SigDispatch` resolution (written
                        // by `resolve_pending_overloads`) never lands on the
                        // body — the backend then falls back to the undefined
                        // bare name. Look up the live mangled keys instead.
                        if let Some(mangled_names) = multi_sig_mangled_names.get(&defn.name) {
                            for mangled_name in mangled_names {
                                if let Some(entry) = sym_table.symbols.get_mut(mangled_name) {
                                    reannotate_and_refresh_view(
                                        mangled_name,
                                        entry,
                                        &resolved_expr_types,
                                        &accumulator.method_resolutions,
                                        &state.subst,
                                    );
                                }
                            }
                        }
                    }
                    TopLevel::Defn(defn) => {
                        if let Some(entry) = sym_table.symbols.get_mut(&defn.name) {
                            reannotate_and_refresh_view(
                                &defn.name,
                                entry,
                                &resolved_expr_types,
                                &accumulator.method_resolutions,
                                &state.subst,
                            );
                        }
                    }
                    TopLevel::TraitImpl(ti) => {
                        for method in &ti.methods {
                            let target_name = ti.target.head_ref().map(|r| r.name.as_ref()).unwrap_or("");
                            let mangled = format!("{}.{}${}", ti.trait_name, method.name, target_name);
                            let mangled_sym = Symbol::from(mangled.as_str());
                            if let Some(entry) = sym_table.symbols.get_mut(&mangled_sym) {
                                reannotate_and_refresh_view(
                                    &mangled_sym,
                                    entry,
                                    &resolved_expr_types,
                                    &accumulator.method_resolutions,
                                    &state.subst,
                                );
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        // Pass 5: interprocedural ownership inference (S102 CS-1..4;
        // `design/typecheck/ownership-inference.md`). A post-pass over the
        // now-settled cluster — mono done, callees written, `codegen_view`
        // rebuilt post-mono. Read-path increment: summaries are emitted but
        // UNconsumed by codegen (backend mechanisms are Wave 11), so the pass
        // is behaviour-neutral. Toggle-gated at its entry (`CRANELISP_NO_OWNERSHIP`
        // set ⇒ emits nothing, §13.5).
        crate::ownership::run_pass5(self, state);

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
    /// `mangled_by_base` is an OUT-parameter: for each multi-sig base name it
    /// receives the MANGLED variant names that `register_mangled_variants`
    /// inserted (S91 Wave-7, FIXME 0432 Face A). The finalize re-annotation block
    /// and the return-type refresh need these keys: the internal `{name}__v{i}`
    /// entries no longer exist (they were removed-and-reinserted under the
    /// mangled names here), so a stale internal-key lookup misses and an in-body
    /// self-call's `SigDispatch` resolution never reaches the variant body —
    /// leaving the backend to fall back to the undefined bare name. (Out-param,
    /// not a return-tuple, to keep this fn's `Result` Ok-type unchanged.)
    fn resolve_multi_sig_overloads(
        &self,
        state: &mut CheckState,
        program: &[TopLevel],
        type_vars: &HashMap<Symbol, (Vec<Type>, Type)>,
        mangled_by_base: &mut MangledNamesByBase,
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
                mangled_by_base
                    .entry(defn.name.clone())
                    .or_default()
                    .extend(resolved_info.iter().map(|(_, _, mangled)| mangled.clone()));
                result_defns.extend(mangled_defns);
                self.register_overloaded_base(state, defn, resolved_info);
            }
        }

        Ok(result_defns)
    }

    /// S91 Wave-7 (FIXME 0432 Face A): re-apply the final substitution to each
    /// multi-sig variant's stored return type, after `resolve_pending_overloads`
    /// has resolved any in-body self-calls.
    ///
    /// `resolve_multi_sig_overloads` (Pass 2.5) captures variant return types
    /// into `state.resolved_overloads`, the persisted `DefKind::Overloaded` base
    /// entry's `OverloadVariant.ret_type`, and each mangled entry's scheme — but
    /// it runs BEFORE `resolve_pending_overloads`. A variant whose body
    /// self-calls another variant has a return type that is only pinned by that
    /// later resolution, so the captured value is a free var. This refresh walks
    /// the final subst over those stored return types so a later REPL cluster
    /// (which rehydrates `resolved_overloads` from the persisted base entry) sees
    /// the concrete return type rather than an unresolved var.
    fn refresh_multi_sig_variant_ret_types(
        &self,
        state: &mut CheckState,
        multi_sig_mangled_names: &MangledNamesByBase,
    ) {
        if multi_sig_mangled_names.is_empty() {
            return;
        }

        let subst = state.subst.clone();

        // 1. Refresh the in-memory `resolved_overloads` (read by
        //    `resolve_pending_overloads` for any still-pending calls and the
        //    source of truth for the persisted base entry below).
        for variants in state.resolved_overloads.values_mut() {
            for (_params, ret, _mangled) in variants.iter_mut() {
                *ret = apply(&subst, ret);
            }
        }

        // 2. Refresh the persisted symbol-table entries: the `Overloaded` base
        //    (its `OverloadVariant.ret_type` is what a later REPL cluster
        //    rehydrates from) and each mangled variant entry's scheme return
        //    type (read for direct mangled-call typing and display).
        let mut st = self.current_symbol_table_mut(state);
        for (base, mangled_names) in multi_sig_mangled_names {
            if let Some(ModuleEntry::Def { kind, .. }) = st.symbols.get_mut(base.as_ref())
                && let DefKind::Overloaded { variants } = kind.as_mut()
            {
                for v in variants.iter_mut() {
                    v.ret_type = apply(&subst, &v.ret_type);
                }
            }
            for mangled in mangled_names {
                if let Some(ModuleEntry::Def { scheme, .. }) = st.symbols.get_mut(mangled) {
                    scheme.ty = apply(&subst, &scheme.ty);
                }
            }
        }
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
                DefKind::UserFn { fn_state: UserFnState::Concrete { got_slot: slot, mode_summary: None } },
            )
            .visibility(defn.visibility)
            .param_names(variant.params.iter().map(|(n, _)| n.clone()).collect());
            if let Some(doc) = defn.docstring.clone() {
                builder = builder.docstring(doc);
            }
            if let Some(ast) = annotated_ast {
                // S84 Phase-3 (FIXME 0392): a resolved multi-sig mangled variant
                // is a codegen-bound `Concrete` entry — build its
                // concrete-boundary `MonoExpr` view from the same annotated,
                // subst-resolved variant body the `ast` carries (best-effort; a
                // `$Var`-param variant body legitimately stays non-concrete — see
                // `build_concrete_codegen_view`).
                if let Some(view) = build_concrete_codegen_view(&mangled, &ast, &state.method_resolutions.pattern_ctors) {
                    builder = builder.codegen_view(view);
                }
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
    ) -> Result<(Vec<Type>, Type, HashMap<Symbol, TypeId>), CranelispError> {
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
                return Ok((param_types.clone(), (**ret_ty).clone(), HashMap::new()));
            }
        }

        // ONE var scope for the whole signature (spec §3.3 [S109]): a free
        // lowercase type var the author writes in a param annotation mints a
        // fresh RIGID var, and a repeated name (`[:a x :a y]`) resolves to the
        // SAME var so x and y unify. This map is built fresh PER CALL —
        // multi-arity clauses each go through a separate `register_defn_signature`
        // (via their own `{name}__vN` internal defn, see
        // `check_form_register_multi_sig`), so `:a` in one clause is independent
        // of `:a` in another (fresh scope per clause). It is RETURNED to the
        // caller and threaded (via `accumulator.defn_var_scopes`) into Pass-2
        // body checking so a body/nested-`fn` `:a` co-refers to the param's
        // rigid var (SCOPE-5 lexical co-reference; 0588). Every entry here is a
        // written PARAMETER var and therefore RIGID — `check_defn_body` seeds
        // `rigid_vars` from `var_map.values()`.
        let mut var_map: HashMap<Symbol, TypeId> = HashMap::new();
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
                    match self.resolve_annotation_type_expr_in_module(
                        ann, &mut var_map, &state.current_module, defn.span,
                    ) {
                        // Fresh param-annotation vars are RIGID; the shared scope
                        // (`var_map`) is threaded to Pass-2 where `check_defn_body`
                        // seeds `rigid_vars` from it. `_minted` is redundant with
                        // `var_map.values()` for the param case.
                        Ok((ty, _minted)) => ty,
                        // Try-type-then-trait (spec §3.9.3, S86 D4). A SINGLE
                        // annotation `:Eq a` is ambiguous between a concrete-type
                        // annotation and a single trait bound. The frontend leaves
                        // a run-of-length-1 as the resolved `TypeExpr::Named`
                        // (`annotation_run_carrier`), delegating disambiguation to
                        // here: when no TYPE with that name exists, resolve it as a
                        // trait constraint. We funnel it through `resolve_bound_param`
                        // (the same single-trait → fresh constrained var path as a
                        // `Bounds([..])` of length 1) iff the annotation's head
                        // resolves as a trait; otherwise the original type error
                        // (the genuine "neither type nor trait" case) propagates.
                        Err(type_err) => {
                            match single_trait_bound_from_annotation(ann) {
                                Some(tref)
                                    if self
                                        .resolve_trait(state, tref.name.as_ref(), defn.span)
                                        .is_ok() =>
                                {
                                    self.resolve_bound_param(
                                        state,
                                        std::slice::from_ref(&tref),
                                        defn.span,
                                    )?
                                }
                                _ => return Err(type_err.into()),
                            }
                        }
                    }
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
                // Pass-1 `NotDetermined` entry (pre-body-check) — never a codegen
                // target, so no concrete-boundary view yet. The mono/body-check
                // seam populates `codegen_view` once the body is concrete (S84
                // concrete-boundary arc, Phase 2b/3 — /dev(typecheck)).
                codegen_view: None,
                code: existing_code,
                value_use: false,
            },
        );

        Ok((param_types, ret_ty, var_map))
    }

    /// Check a single function definition body.
    ///
    /// `written_var_scope` is the definition's Pass-1 written-type-var scope
    /// (name → rigid `TypeId`, spec §3.3 [S109]); it is installed as the active
    /// `state.written_var_scope` and seeds `state.rigid_vars` for the duration
    /// of this body so that (a) a body/nested-`fn` `:a` co-refers to the param's
    /// rigid var (SCOPE-5), and (b) a body that would force a rigid var concrete
    /// — by ascription (`:a "hello"`) or by use (`(add-i64 x 1)`) — is a
    /// skolem-escape type error (MUST-3/MUST-4). Both are torn down on return so
    /// a forward-referencing sibling instantiates the (now quantified) var
    /// flexibly (MUST-1).
    fn check_defn_body(
        &self,
        state: &mut CheckState,
        defn: &Defn,
        param_types: &[Type],
        ret_ty: &Type,
        written_var_scope: HashMap<Symbol, TypeId>,
    ) -> Result<(), CranelispError> {
        self.push_scope(state);

        // Activate the definition's written-var scope + the constraint-abstract
        // rigid set (spec §3.3.1–§3.3.2 [S109]). Two independent pieces:
        //
        // - `written_var_scope` (name → `TypeId`) threads LEXICAL CO-REFERENCE:
        //   every occurrence of one bare written name within the definition —
        //   including inside nested `fn` closures (`infer_lambda` shares it) —
        //   resolves to the SAME var (`[:a x :a y]` ties x/y; a body `:a`
        //   co-refers to a param `:a`). This is ALL a bare written var does; it
        //   is an ordinary FLEXIBLE inference var otherwise, and the body MAY pin
        //   it to a concrete type (never an error — §3.3.1 MUST (a), rows 2/4/11).
        //
        // - `rigid_vars` holds ONLY the ASSERTED-constraint param vars (`:C x`):
        //   a constraint at a parameter position is held abstract over `C` for
        //   the body-check, so the body narrowing it to a concrete type — by
        //   ascription or by use — is a skolem escape (§3.3.2 MUST (b), row 6).
        //   These are exactly the param `Type::Var`s that ALREADY carry a
        //   constraint at Pass-2 entry: `resolve_bound_param` recorded the
        //   assertion during Pass-1 signature registration. A BARE `:a` param
        //   that merely ACCRUES a constraint from body use (row 7) is NOT here —
        //   its var carries no constraint until body inference runs, after this
        //   seeding, so it stays flexible (inferred-not-asserted).
        let prev_rigid = std::mem::take(&mut state.rigid_vars);
        let prev_scope = state.written_var_scope.take();
        let mut rigid: HashSet<TypeId> = HashSet::new();
        for pt in param_types {
            if let Type::Var(id) = self.apply_subst(state, pt)
                && state.active_constraints.get(id).is_some()
            {
                rigid.insert(id);
            }
        }
        state.rigid_vars = rigid;
        state.written_var_scope = Some(written_var_scope);
        // Fresh per-body accumulator for nested-`fn` written-param vars (§3.10
        // poly-as-value check below).
        let prev_lambda = std::mem::take(&mut state.lambda_written_vars);

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

        // **Poly-as-value rejection (spec §3.3.4 / §3.10 rank-1, MUST (f), row
        // 10).** A written parameter var freshly introduced by a nested `fn`
        // (`(fn [:b y] …)`) that remains FREE after body inference means the
        // polymorphic function was RETURNED/STORED rather than applied in place
        // (`(defn mk [] (fn [:b y] y))` → `∀b. (Fn [] (Fn [b] b))`). Cranelisp is
        // rank-1: a `∀` held uninstantiated in a value position is unsupported.
        // When the lambda is applied in place (row 9: `((fn [:b y] y) 3)`) the
        // var unifies to the argument type and is not free, so it is not flagged.
        // A co-referring inner `:a` (row 8: `(fn [:a y] y)` under `[:a x]`) is
        // NOT freshly minted here, so it never enters `lambda_written_vars`.
        let escaped_poly_fn = state
            .lambda_written_vars
            .iter()
            .any(|&id| matches!(self.apply_subst(state, &Type::Var(id)), Type::Var(_)));
        state.lambda_written_vars = prev_lambda;
        if escaped_poly_fn {
            return Err(CranelispError::TypeError {
                message: "a polymorphic function cannot be returned or stored as a \
                          value: a written type variable would leave the returned \
                          `fn` polymorphic (rank-2). Apply it in place, or make the \
                          returned function concrete (spec §3.3.4/§3.10)"
                    .to_string(),
                location: ErrorLocation::from_span(defn.span),
            });
        }

        // Deactivate the rigid written-var scope before the post-passes /
        // generalization run (MUST-1: outside its own body the written var is an
        // ordinary quantified var).
        state.rigid_vars = prev_rigid;
        state.written_var_scope = prev_scope;

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
    /// S84 Wave 1b (FIXME 0374/0378 issue 3, Principle 20): register discovered
    /// `test-*` entry points as monomorphisation ROOTS, like `main`.
    ///
    /// The TOTAL slot gate (`slot ⟺ is_concrete()`) makes a result-only-var test
    /// fn (`(defn test-x [] None)` → `(Fn [] (Option a))`) slot-less `Polymorphic`.
    /// But a test fn is an ENTRY POINT — the discovery readers
    /// (`discover_test_names` / `discover_eligible_tests`) need a concrete
    /// `(Fn [] (Option String))` instance to invoke. So we register each such test
    /// fn as a root: recheck its body at the expected entry type
    /// `(Fn [] (Option String))` and re-register a `Concrete{slot}` entry UNDER THE
    /// BARE NAME (no `name$T` mangling — one fixed entry type per test fn). This
    /// mirrors `main`'s `(IO t)→(IO Int)` finalisation, and keeps int's names-only
    /// discovery reader byte-identical (the slot now rides the concrete instance
    /// under the same name).
    ///
    /// Only the **degenerate** shape needs this: a well-formed test fn
    /// (`(defn test-x [] (if c None (Some "msg")))`) already pins `(Option String)`
    /// and is already `Concrete{slot}` — its scheme is concrete, so it is not
    /// `Polymorphic` and is skipped here. A param-polymorphic def is excluded
    /// by the nullary requirement.
    ///
    /// The root set is enumerated by the SAME syntactic+shape filter the discovery
    /// readers use (no int→typecheck call): bare name `test-*`, nullary, current
    /// scheme `(Fn [] (Option a))` with the result var free (the only carve-out
    /// customer). A test fn whose body forces a NON-`String` `(Option …)` (or any
    /// other concrete result) is already `Concrete` and not seen here.
    fn register_test_fn_mono_roots(
        &self,
        state: &mut CheckState,
    ) -> Result<(), CranelispError> {
        // Enumerate eligible Polymorphic test-fn names + their stored variant +
        // the Option FQTypeName from their result type. Read-only scan first (no
        // &mut overlap), then recheck + re-register.
        let candidates: Vec<(Symbol, DefnVariant, cranelisp_types::FQTypeName)> = {
            let st = self.current_symbol_table(state);
            st.view()
                .iter()
                .filter_map(|(name, entry)| {
                    if !name.as_ref().starts_with("test-") {
                        return None;
                    }
                    let ModuleEntry::Def { kind, ast, .. } = entry else {
                        return None;
                    };
                    let DefKind::UserFn {
                        fn_state: UserFnState::Polymorphic(pf),
                    } = kind.as_ref()
                    else {
                        return None;
                    };
                    // Must be nullary with a result-only free var — shape
                    // `(Fn [] (Option a))` (a is unbound). A concrete-result test
                    // fn is already `Concrete{slot}` (not `Polymorphic`), so it
                    // never reaches here; a param-polymorphic def has params.
                    let Type::Fn(params, ret) = &pf.scheme.ty else {
                        return None;
                    };
                    if !params.is_empty() {
                        return None;
                    }
                    // The result must be `(Option <var>)` — the degenerate
                    // `(defn test-x [] None)` shape. Anything else (a bare result
                    // var, a non-Option ADT) is not a test-discovery entry. Keep
                    // the actual FQTypeName so the concrete instance uses Option's
                    // real home module (not a hardcoded one).
                    let Type::ADT(fqtn, args) = ret.as_ref() else {
                        return None;
                    };
                    if fqtn.name.as_ref() != "Option" || args.len() != 1 {
                        return None;
                    }
                    if !matches!(args[0], Type::Var(_)) {
                        return None;
                    }
                    ast.clone().map(|variant| (name.clone(), variant, fqtn.clone()))
                })
                .collect()
        };

        for (name, variant, option_fqtn) in candidates {
            // Recheck the body at the expected entry type `(Fn [] (Option String))`
            // — the discovery contract's fixed entry type (`test_scheme_is_eligible`).
            // The degenerate body `None` unifies trivially (`a -> String`).
            let option_string = Type::ADT(option_fqtn, vec![Type::String]);
            let mut wrap_defn = Defn {
                name: name.clone(),
                docstring: None,
                variants: vec![variant.clone()],
                visibility: Visibility::Public,
                span: variant.span,
            };
            let recheck =
                self.recheck_body_for_mono(state, &mut wrap_defn, &[], &option_string, None);
            // If the body cannot be concretised at `(Option String)` (e.g. it
            // forces a different concrete `Option` instance), leave the
            // `Polymorphic` entry untouched — discovery's eligibility filter will
            // correctly skip a non-`(Option String)` test fn.
            let Ok((resolutions, mono_expr_types)) = recheck else {
                continue;
            };

            // Annotate the body and apply the final substitution so the backend
            // codegens the concrete instance (mirrors `register_mono_entry`).
            let mut concrete_defn = Defn {
                name: name.clone(),
                docstring: None,
                variants: vec![DefnVariant {
                    params: variant.params.clone(),
                    body: variant.body.clone(),
                    span: variant.span,
                }],
                visibility: Visibility::Public,
                span: variant.span,
            };
            annotate_defn_from_maps(
                &mut concrete_defn,
                &mono_expr_types,
                &resolutions.resolved_calls,
            );
            apply_subst_to_defn(&state.subst, &mut concrete_defn);

            // S84 Phase-3 (FIXME 0392): this minted test-fn root is a
            // codegen-bound `Concrete` entry — build its concrete-boundary
            // `MonoExpr` view from the fully-annotated, subst-resolved body. The
            // discovery contract pins it to `(Fn [] (Option String))`, so the
            // body (`None`) is concrete and `from_expr` succeeds (best-effort
            // per `build_concrete_codegen_view`).
            let codegen_view = concrete_defn
                .variants
                .first()
                .and_then(|v| build_concrete_codegen_view(&name, v, &state.method_resolutions.pattern_ctors));

            // Re-register the entry under the BARE name as `Concrete{slot}`,
            // carrying the concrete scheme + annotated body. Allocate a fresh
            // slot (the `Polymorphic` original had none).
            let concrete_scheme = mono(Type::Fn(vec![], Box::new(option_string.clone())));
            let mut st = self.current_symbol_table_mut(state);
            let got_slot = st.allocate_got_slot();
            if let Some(ModuleEntry::Def { scheme, kind, ast, codegen_view: cv, .. }) =
                st.symbols.get_mut(&name)
            {
                *scheme = concrete_scheme;
                **kind = DefKind::UserFn {
                    fn_state: UserFnState::Concrete { got_slot, mode_summary: None },
                };
                *ast = concrete_defn.variants.into_iter().next();
                *cv = codegen_view;
            }
        }
        Ok(())
    }

    /// Monomorphise every reachable polymorphic / constrained call site into
    /// concrete instances.
    ///
    /// Returns the `Vec<MonoDefn>` (each carrying a `Defn` body the backend
    /// still reads pre-Phase-3). S84 Phase-3 (FIXME 0392): the concrete-boundary
    /// `MonoExpr` view of every instance is now set ON the instance's
    /// `ModuleEntry::Def.codegen_view` at `register_mono_entry` (the single
    /// source of truth, Principle 7) — the transitional parallel
    /// `CheckState.mono_variants` `Vec` that carried it is retired. The
    /// `MonoExpr::from_expr` validation (a residual `Var` in any instance
    /// surfaces as a §3.11.1 could-not-monomorphise error) runs at the
    /// `monomorphise_call` seam, unchanged.
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

        // FIXME 0373 (Tier 1, /arch ruling (A) — monomorphise polymorphic-result
        // hops) — collect call sites for LOCAL (same-module) pure-parametric
        // polymorphic callees. These are NOT in `constrained_fn_names` (that set
        // holds only trait-constrained fns — `detect_constrained_fns` keys on
        // `UserFnState::Constrained`), and they live in the current module so the
        // imported-call pass above (which requires `home != current_module`)
        // skips them too. Yet a hop like `(defn h1 [f] (h2 f))` whose RESULT type
        // generalizes to an unbound `Type::Var` is compiled ONCE generically
        // (program.rs §919 "generalize-and-keep-a-single-generic Concrete slot"),
        // leaving its result `Type::Var` at codegen. The backend's RC classifier
        // (`HeapCategory::classify(Type::Var) -> Mixed`) then emits a guarded
        // RC-inc whose `< 1024` immediate-vs-pointer heuristic mis-reads a
        // negative / large Int result as a heap pointer and dereferences it →
        // SIGSEGV (FIXME 0373 root-cause). Monomorphising the hop at the concrete
        // instantiation reached from its call site gives the mono instance a
        // CONCRETE result type (`Int`) → `classify` sees `NeverHeap` → no guard →
        // no crash. This reuses the same 0355 collection + `monomorphise_call` +
        // caller-GOT-slot mechanism, widening the trigger from "constrained /
        // imported callee" to "polymorphic-result hop reached at a concrete type".
        for defn in defns {
            self.collect_local_parametric_calls(
                state,
                defn.body(),
                &defn.name,
                constrained_fn_names,
                &mut call_sites,
            );
        }

        // FIXME 0374 (Tier 2 — the `(Box a)`-field-through-HOF gap). Collect
        // bare-`Var` ARGUMENTS that pass a monomorphisable polymorphic fn as a
        // VALUE into a higher-order call. These are not callees (so the
        // call-site collectors above miss them) but they still need a concrete
        // mono instance — see `collect_parametric_fn_value_args`. Recorded
        // per enclosing defn so the fn-value `Var` can be rewritten to the
        // mangled name in that defn's stored AST after minting.
        let mut fn_value_arg_sites: Vec<FnValueArgSite> = Vec::new();
        for defn in defns {
            let mut sites = Vec::new();
            self.collect_parametric_fn_value_args(state, defn.body(), &mut sites);
            for (arg_name, arg_span, param_types, home) in sites {
                fn_value_arg_sites.push((defn.name.clone(), arg_name, arg_span, param_types, home));
            }
        }

        // Nothing to monomorphise (neither local constrained fns nor imported
        // constrained call sites nor polymorphic fn-value arguments) — bail
        // before resolving expr_types.
        if call_sites.is_empty() && fn_value_arg_sites.is_empty() {
            return Ok(Vec::new());
        }

        // Resolve expr_types so we can look up concrete arg types
        let resolved_expr_types = self.resolve_expr_types(state);

        // Monomorphise each call site and record dispatch mappings
        let mut mono_defns = Vec::new();
        let mut seen: HashMap<String, JitSymbol> = HashMap::new();
        // The caller's module — the fallback home for a LOCAL generic's mono
        // name. `monomorphise_call` restores `state.current_module` per call, so
        // capturing once here is stable across the loop (FIXME 0519).
        let current_module = state.current_module.clone();

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

            // ALL-ARGS-CONCRETE GUARD (Phase-4 part A, concrete-boundary-type.md
            // §4-A). The collection-time trigger (`local_parametric_call_triggers`)
            // gates on `state.subst`-resolved `expr_types`, but the actual arg
            // types are re-derived HERE from the FINAL `resolved_expr_types` — and
            // a call collected from a GENERIC caller's body (the
            // `(reduce-loop f init v (vec-len v) 0)` call inside `reduce`'s body,
            // while `reduce` is still generic) resolves here to the parent's OWN
            // free scheme vars (`[Fn[Var,Var]→Var, Var, (Vec Var), Int, Int]`).
            // Monomorphising that mints the SPURIOUS partial `reduce-loop$Vec+Int+Int`
            // (lossy name, residual body vars). The genuine concrete instance is
            // minted via the parent's CONCRETE re-check chain
            // (`reduce$Int+Vec → reduce-loop$Int+Vec+Int+Int`) — its args ARE all
            // concrete. Skip any site whose final arg types are not all concrete:
            // every minted instance is then fully concrete (the carve-out is dead,
            // `from_expr` succeeds on each — the completeness proof).
            if !arg_types.iter().all(|t| t.is_concrete()) {
                continue;
            }

            // Deduplicate: same defining home + fn + arg types = same
            // specialization. Route the dedup key through the ONE canonical
            // mangler so the dedup grain == the minted-name grain (FIXME 0519):
            // a home-blind key collapsed two same-named imported generics at the
            // dedup step (the 0508 collapse point) even after the name grew a
            // home. `arg_types` are the concrete param types (gated concrete
            // above), so this key string is byte-identical to the `mono.defn.name`
            // that `monomorphise_call` mints below.
            let key_home = home_module
                .clone()
                .unwrap_or_else(|| current_module.clone());
            let key = crate::traits::build_mangled_name(&key_home, fn_name, &arg_types);

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

        // FIXME 0374 (Tier 2 — fn-value-argument monomorphisation). For each
        // polymorphic fn passed as a value into a HOF, mint its concrete mono
        // instance (`mk$Int`) and rewrite the fn-value `Var` in the enclosing
        // defn's stored AST to the mangled name, so the backend's
        // `compile_fn_as_value` takes the concrete (slotted) instance's GOT slot
        // rather than the slot-less `Polymorphic` template. The mono instance's
        // body re-checks at the concrete param types, so its `(Box a)` field
        // becomes `(Box Int)` — concrete, classifying cleanly, no RC guard.
        let mut fn_value_rewrites: Vec<(Symbol, Span, Symbol)> = Vec::new();
        for (enclosing, arg_name, arg_span, param_types, home) in &fn_value_arg_sites {
            // Home-qualified dedup key == the minted name (FIXME 0519): `home`
            // for an IMPORTED generic fn-value (FIXME 0488 sig b), else current.
            let key_home = home
                .clone()
                .unwrap_or_else(|| current_module.clone());
            let key = crate::traits::build_mangled_name(&key_home, arg_name, param_types);
            let mangled_sym = if let Some(existing) = seen.get(&key) {
                Symbol::from(existing.as_ref())
            } else if let Some(mono) =
                // Pass `Span::SYNTHETIC` as the call-span: a fn-VALUE argument is
                // not a call site, so the FIXME-0349 call-result propagation
                // inside `monomorphise_call` (which unifies the call-span's
                // expr-type with the mono's RETURN type) must NOT fire — the
                // arg-span's type is the fn's FULL `(Fn ..)` type, not its
                // return. A synthetic span misses the `expr_types` lookup and
                // skips that unify cleanly. `home` is `Some(defining_module)` for
                // an IMPORTED generic fn-value (FIXME 0488 sig b), `None` local.
                self.monomorphise_call(
                    state, arg_name, param_types, Span::SYNTHETIC, home.as_ref(),
                )?
            {
                let mangled = JitSymbol::from(mono.defn.name.as_ref());
                seen.insert(key, mangled.clone());
                let sym = Symbol::from(mangled.as_ref());
                mono_defns.push(mono);
                sym
            } else {
                continue;
            };
            fn_value_rewrites.push((enclosing.clone(), *arg_span, mangled_sym));
        }

        // Apply the fn-value `Var` renames to the stored ASTs. A later
        // re-annotation pass (in `finalize_check_result_inner`) only writes
        // `inferred_type` / `resolved_call` by span — it does not touch the
        // `Var` name — so this rename survives.
        if !fn_value_rewrites.is_empty() {
            let mut st = self.current_symbol_table_mut(state);
            for (enclosing, arg_span, mangled_sym) in &fn_value_rewrites {
                if let Some(ModuleEntry::Def { ast: Some(variant), .. }) =
                    st.symbols.get_mut(enclosing)
                {
                    rename_var_at_span(&mut variant.body, *arg_span, mangled_sym);
                }
            }
        }

        // S84 Phase-3 (FIXME 0392): the concrete-boundary `MonoExpr` view of
        // each minted instance is now set ON its `ModuleEntry::Def.codegen_view`
        // at `register_mono_entry` — no parallel `Vec` to drain.
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
        // DEF-1 (S86): resolve the bare callee through the **prelude-fallback**
        // scope resolve (`resolve_terminal_fq_scoped`), NOT the
        // current-module-only `resolve_terminal_entry_and_home`. A polymorphic fn
        // provided ONLY via the implicit-prelude outer scope (no explicit import)
        // is invisible to a current-module-rooted lookup, so its concrete mono
        // was never minted in the consuming module → codegen `undefined function`.
        // The fallback-aware resolver applies the same I-1 public-only filter the
        // value/type/ctor/trait chokepoints use, and reports the terminal `home`
        // (the prelude — `!= current_module`), so the cross-module mono path fires
        // exactly as it does for the explicit-import control (S78 outer-scope
        // discipline; the mono-collection chokepoint had been missed).
        if let Expr::Apply { callee, args, span, .. } = expr
            && let Expr::Var { name, .. } = callee.as_ref()
            && !constrained_fn_names.contains(name)
            && let Some(resolved) = self.resolve_terminal_fq_scoped(state, name.as_ref())
            && resolved.home != state.current_module
            && Self::entry_is_monomorphisable_polymorphic(&resolved.entry)
        {
            // FIXME 0488 sig a (cross-module FQ): record the BARE terminal symbol
            // (`resolved.fq.symbol`), not the raw reference `name` — a qualified
            // callee (`gen/iden2`) would otherwise reach `get_constrained_fn`'s
            // home-probe as a `/`-bearing key in the home module → no mint. The
            // resolver already split `mod/sym` and resolved the module alias.
            let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
            out.push((resolved.fq.symbol.clone(), arg_spans, *span, Some(resolved.home)));
        }
        for_each_child_expr(expr, |child| {
            self.collect_imported_constrained_calls(state, child, constrained_fn_names, out)
        });
    }

    /// Whether a call site to a LOCAL polymorphic callee should be collected for
    /// monomorphisation. ONE predicate: **every argument is fully concrete**
    /// (Phase-4 part A, Option 1, concrete-boundary-type.md §4-A — collapsing the
    /// former two triggers).
    ///
    /// A mono instance is minted **iff every argument type is concrete**; its
    /// result is then concrete by the per-instance re-check (the body re-check +
    /// `unify(body_ty, ret_ty)` pins the result). This subsumes BOTH the old
    /// 0373 result-hop trigger (`result_is_bare_var`) and the 0374
    /// direct-concrete-call trigger:
    ///
    /// - **Genuine result hops (0373) are still minted** — a result-bare-var hop
    ///   whose ARGS are concrete (`(g 1)`, `(h2 x)` with `x: Int`) passes this
    ///   predicate; the body re-check pins the result. The genuine concrete
    ///   result-hop arrives here through the parent's concrete re-check chain
    ///   with every arg already pinned.
    /// - **Direct concrete calls (0374)** — `(g 1)` with `g : ∀a. a→a` passes:
    ///   all args concrete, so the `g$Int` instance is minted (`g` is slot-less
    ///   under the structural slot gate; an un-monomorphised call would lower
    ///   through a missing slot).
    /// - **The SPURIOUS partial result-hop is EXCLUDED** — a result-bare-var hop
    ///   whose args are still the parent's free scheme vars (the `reduce →
    ///   reduce-loop` 0344 fold inner call, where `f`/`acc`/element are
    ///   `reduce`'s OWN `Var34`/`Var31`) fails the all-args-concrete predicate,
    ///   so no partial `reduce-loop$Vec+Int+Int` is minted. The genuine concrete
    ///   `reduce-loop$Int+Vec+Int+Int` is minted via the concrete `reduce$Int+Vec`
    ///   chain (where the args ARE pinned), unaffected.
    ///
    /// **The 0344 fold is preserved by the all-args-concrete guard.** The fold
    /// call `(reduce vec-push [] vv)` has args `vec-push` (a polymorphic
    /// fn-VALUE), `[]` (`(Vec a)`), `vv` — NOT all concrete — so it is excluded.
    /// Monomorphising it would pin `reduce`'s accumulator var through the
    /// post-mono regeneralisation, re-collapsing the polymorphic scheme 0344
    /// deliberately keeps; the all-concrete guard keeps it out.
    ///
    /// An empty-arg call does NOT trigger (a nullary polymorphic call cannot be
    /// pinned by its args — if its result is concrete it needs no mono; if its
    /// result is a free var it is the ambiguity case, §2.6, not a mono site).
    fn local_parametric_call_triggers(
        state: &CheckState,
        _call_span: &Span,
        args: &[Expr],
    ) -> bool {
        !args.is_empty()
            && args.iter().all(|a| {
                state
                    .expr_types
                    .get(&a.span())
                    .map(|ty| apply(&state.subst, ty).is_concrete())
                    .unwrap_or(false)
            })
    }

    /// Walk a defn body collecting calls to LOCAL (same-module) pure-parametric
    /// polymorphic callees that need a concrete monomorphisation (FIXME 0373,
    /// Tier 1 — the polymorphic-result-hop fix; /arch ruling (A)).
    ///
    /// Mirrors [`Self::collect_imported_constrained_calls`] for the *local* case:
    /// a trait-constrained local fn is already in `constrained_fn_names` and is
    /// collected by [`Self::collect_constrained_calls_excluding_self`]; here we
    /// pick up bare `Var` callees whose local name resolves (chain-follow) to a
    /// terminal in the SAME module that is a pure-parametric polymorphic `UserFn`
    /// `Def` (the `entry_is_monomorphisable_polymorphic` shape, excluding the
    /// already-collected constrained set). The call site is recorded with
    /// `home: None` (the same-module `monomorphise_call` path — recheck the body
    /// in the current module's scope). A call from a fn to ITSELF is skipped:
    /// generic self-recursion is the defn's own generic vars, not a concrete site.
    fn collect_local_parametric_calls(
        &self,
        state: &CheckState,
        expr: &Expr,
        self_name: &Symbol,
        constrained_fn_names: &HashSet<Symbol>,
        out: &mut Vec<(Symbol, Vec<Span>, Span, Option<ModuleFullPath>)>,
    ) {
        if let Expr::Apply { callee, args, span, .. } = expr
            && let Expr::Var { name, .. } = callee.as_ref()
            && name != self_name
            && !constrained_fn_names.contains(name)
            && Self::local_parametric_call_triggers(state, span, args)
            && let Some(resolved) = self.resolve_terminal_fq_scoped(state, name.as_ref())
            && resolved.home == state.current_module
            && Self::entry_is_monomorphisable_polymorphic(&resolved.entry)
        {
            // FIXME 0488 sig a (same-module FQ): resolve via the `/`-splitting
            // fallback resolver (the raw `resolve_terminal_entry_and_home` probe
            // keyed the qualified `test/iden` string and missed) and record the
            // BARE terminal symbol so `(test/iden 5)` mints/dispatches under the
            // same `iden$Int` name as the bare call. A cross-module qualifier
            // resolves with `home != current` and is left to the imported
            // collector; a prelude fn likewise (home == prelude != current).
            let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
            out.push((resolved.fq.symbol.clone(), arg_spans, *span, None));
        }
        for_each_child_expr(expr, |child| {
            self.collect_local_parametric_calls(
                state, child, self_name, constrained_fn_names, out,
            )
        });
    }

    /// Walk a defn body collecting bare-`Var` ARGUMENTS that pass a
    /// monomorphisable polymorphic fn as a *value* into a higher-order call
    /// (FIXME 0374 — the `(Box a)`-field-carrying-`Type::Var`-through-HOF gap).
    ///
    /// The result-hop collectors ([`Self::collect_local_parametric_calls`] +
    /// [`Self::monomorphise_inner_parametric_hops`]) trigger on a bare-`Var`
    /// *call result* or an `Apply`-of-bare-`Var`. They do NOT cover a polymorphic
    /// fn passed as an argument value (`(thru mk x)` — `mk` is a fn-value
    /// argument, never a callee here, and the HOF call's result `(Box Int)` is
    /// concrete so the result-var gate skips it). That fn-value still needs a
    /// concrete mono instance: `mk`'s body constructs `(Box a)` with a `Type::Var`
    /// field that reaches the RC boundary as a non-concrete `Box` field →
    /// `classify(Type::Var)` → the unsound `<1024` guard → SIGSEGV.
    ///
    /// For each `Apply` whose bare-`Var` argument resolves (chain-follow) to a
    /// LOCAL monomorphisable polymorphic def AND whose resolved expr-type at the
    /// argument span is a FULLY CONCRETE `(Fn [..] ..)`, record
    /// `(arg_var_name, arg_span, concrete_param_types)`. The caller mints
    /// `arg_var$T..` and rewrites the fn-value `Var` in the enclosing defn's
    /// stored AST to the mangled name so the backend takes the concrete mono
    /// instance's GOT slot.
    fn collect_parametric_fn_value_args(
        &self,
        state: &CheckState,
        expr: &Expr,
        out: &mut Vec<(Symbol, Span, Vec<Type>, Option<ModuleFullPath>)>,
    ) {
        // A generic fn referenced in VALUE position at a concrete `Fn` type
        // (FIXME 0374 fn-value monomorphisation; 0571 D1 extension; 0585 —
        // position-completeness cure). A value-position generic fn-value ref
        // reaches the backend slot-less unless monomorphised here ⇒ the
        // `undefined variable` codegen leak (0571 D1).
        //
        // **POSITION-COMPLETE (0585, mirroring `find_ambiguous_value_position`).**
        // The verdict must fire on EVERY codegen-reaching value position, not a
        // hand-picked whitelist. The old shape only visited `Apply { args }` and
        // `Let`/`ParBind` binding values, so a generic fn-value in an `if`
        // branch, a `match` arm body, a `VecLit` element, a ctor field, or a
        // `let` tail body slipped past collection and reached codegen slot-less.
        // `for_each_child_expr` is the single child-enumeration source of truth;
        // its children ARE the value positions. Only the `Apply` CALLEE is a
        // DISPATCH position (not a runtime value) — it mints through the ordinary
        // call-site path, so we recurse INTO it but never collect it as a
        // fn-value. `try_collect_parametric_fn_value` self-guards on
        // `Expr::Var`, so applying it to a non-`Var` child is a no-op.
        let callee_span = match expr {
            Expr::Apply { callee, .. } => Some(callee.span()),
            _ => None,
        };
        for_each_child_expr(expr, |child| {
            if Some(child.span()) != callee_span {
                self.try_collect_parametric_fn_value(state, child, out);
            }
            self.collect_parametric_fn_value_args(state, child, out);
        });
    }

    /// The per-`Var` fn-value monomorphisation collect (FIXME 0374 / 0488 sig b /
    /// 0571 D1) — records `(bare_symbol, ref_span, param_types, home)` for a
    /// value-position `Var` that resolves to a monomorphisable polymorphic fn
    /// whose full `Fn` signature is concrete at this reference. Shared by the HOF
    /// argument and let-binding value sites.
    fn try_collect_parametric_fn_value(
        &self,
        state: &CheckState,
        var_expr: &Expr,
        out: &mut Vec<(Symbol, Span, Vec<Type>, Option<ModuleFullPath>)>,
    ) {
        if let Expr::Var { name, span, .. } = var_expr
            && let Some(ty) = state.expr_types.get(span)
            && let Type::Fn(param_types, ret_ty) = apply(&state.subst, ty)
            // The fn-value's full signature must be concrete — the instantiation
            // the use demands, and the shape that pins any residual ADT-field
            // `Type::Var`.
            && param_types.iter().all(|p| p.is_concrete())
            && ret_ty.is_concrete()
            && let Some(resolved) = self.resolve_terminal_fq_scoped(state, name.as_ref())
            && Self::entry_is_monomorphisable_polymorphic(&resolved.entry)
        {
            // Same-module ⇒ `home: None` (byte-identical to the 0374 path); an
            // IMPORTED generic fn-value carries its defining module so the mint
            // re-checks the body in the DEFINING scope (FIXME 0488 sig b). The
            // BARE terminal symbol keys the mangle + `rename_var_at_span` target.
            let home = if resolved.home == state.current_module {
                None
            } else {
                Some(resolved.home.clone())
            };
            out.push((resolved.fq.symbol.clone(), *span, param_types, home));
        }
    }

    /// Does this terminal entry need a monomorphised specialisation when called
    /// with concrete arg types? (FIXME 0355 — mirrors `get_constrained_fn`'s two
    /// accepted shapes: a trait-constrained `UserFn`, or a pure-parametric
    /// polymorphic `UserFn` carrying a stored annotated `ast`.)
    pub(crate) fn entry_is_monomorphisable_polymorphic(entry: &ModuleEntry<C>) -> bool {
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
