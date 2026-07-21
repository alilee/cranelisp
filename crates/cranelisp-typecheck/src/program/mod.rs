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

use crate::result::CheckResult;
use crate::result::{DispatchGap, UnresolvedDispatchSite};

use crate::checker::{CheckState, TypeCheckEnv};
use crate::scheme::mono;

mod support;
mod callees;
mod register;
mod body;
mod finalize;
mod mono_collect;
#[cfg(test)]
mod test_driver;

// Re-export the free-function toolbox + callee helpers at the `program`
// level so sibling submodules reach them via `use super::*` and the
// existing `crate::program::<fn>` call sites in checker/adt/traits/infer
// keep resolving unchanged (a pure decomposition moves no path).
pub(crate) use mono_collect::AutoCurryDrain;
pub(crate) use support::*;
pub(crate) use callees::*;

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

    /// The per-`Var`-span typed resolution verdicts discovered while checking
    /// this form's bodies (`MethodResolutions.var_refs`; S114 carrier flip).
    /// Mirror of `pattern_ctors` — accumulated cross-form so the finalize
    /// codegen-view rebuild can populate `MonoExpr::Var.resolution` AFTER the
    /// per-form `state.method_resolutions` has been drained.
    pub(crate) var_refs: HashMap<Span, cranelisp_types::VarRef>,

    /// The per-`Apply`-span typed dispatch verdicts discovered while checking
    /// this form's bodies (`MethodResolutions.apply_refs`; S114 carrier flip) —
    /// the Apply-side sibling of `var_refs`, populating
    /// `MonoExpr::Apply.dispatch`.
    pub(crate) apply_refs: HashMap<Span, cranelisp_types::ApplyRef>,

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
    pub(super) fn empty() -> Self {
        FormCheckResult {
            method_resolutions: HashMap::new(),
            pattern_ctors: HashMap::new(),
            var_refs: HashMap::new(),
            apply_refs: HashMap::new(),
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
    pub(crate) var_refs: HashMap<Span, cranelisp_types::VarRef>,
    pub(crate) apply_refs: HashMap<Span, cranelisp_types::ApplyRef>,
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
    /// §3.3.1 [S109 W6.3]), keyed by the same defn name (multi-arity clauses
    /// under their `{name}__v{i}` internal name). Each maps the written type-var
    /// names in the parameter annotations (`:a`, `:(Box a)`) to the ONE flexible
    /// `TypeId` they minted. Pass-2 `check_defn_body` installs it as the
    /// definition's `written_var_scope`, so a body/nested-`fn` occurrence of the
    /// same name CO-REFERS to the same var (the 0588 cross-pass threading; empty
    /// for a signature with no written type vars). A bare written var carries
    /// only a name — rigidity lives on the CONSTRAINT path (`check_defn_body`
    /// seeds `rigid_vars` from asserted-constraint param vars, NOT from this
    /// map).
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
            var_refs: HashMap::new(),
            apply_refs: HashMap::new(),
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


/// Map from a multi-sig defn's base name to the MANGLED variant names that
/// `register_mangled_variants` inserted for it (S91 Wave-7, FIXME 0432 Face A).
/// Drives the finalize re-annotation + return-type refresh, both of which must
/// key variant entries by their live mangled names, not the removed internal
/// `{name}__v{i}` keys.
type MangledNamesByBase = HashMap<Symbol, Vec<Symbol>>;



impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
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

}

#[cfg(test)]
mod test_support;
