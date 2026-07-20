use super::*;

/// FIXME 0653 — the ruled name-scan discipline (the Fix-1 template generalised).
/// A name-scan mono collector's AST callee NAME is only a TRIGGER; the identity
/// is the per-span recorded carrier. A callee `Var` whose recorded verdict is a
/// §4.6 LOCAL (`VarRef::Local`) resolved to a `let`/`fn`/param binding shadowing
/// a top-level constrained/parametric fn — because `record_reference_target`'s
/// frame-guarded shadow gate declined the table reference. Such a call MUST NOT
/// be minted/dispatched by name-match (it would silently wrong-value the shadow
/// to the top-level fn). Returns TRUE when the collector should PROCEED (a real
/// keyed TABLE reference), FALSE to SKIP.
///
/// **S114 carrier flip.** The old test was `resolved_targets.contains_key(span)`:
/// pre-flip the map carried an entry ONLY for a table reference, so
/// contains-key ⇔ "resolved Global". Post-flip `var_refs` is TOTAL — every local
/// carries a `VarRef::Local` entry too — so the test discriminates the variant:
/// `VarRef::Global` is the table reference (incl. the self-recursion carve-out),
/// `VarRef::Local` is the §4.6 shadow. This preserves the exact pre-flip
/// behaviour (a local resolved to no entry ⇒ false; a Global carrier ⇒ true).
/// The consumers guard `Expr::Var` callees, so the span is always a `Var` span
/// (`var_refs`), never an `Apply` span.
///
/// The ONE shared guard (P7): consumed by `collect_local_parametric_calls`,
/// `collect_imported_constrained_calls`, `collect_constrained_calls_excluding_self`
/// (pass-4 top-level collectors, reading `state.method_resolutions.var_refs`),
/// and `resolve_inner_constrained_calls` / `monomorphise_inner_parametric_hops`
/// (mono-recheck epilogue, reading the harvested `resolutions.var_refs`).
pub(crate) fn callee_has_keyed_carrier(
    var_refs: &HashMap<Span, cranelisp_types::VarRef>,
    callee_span: Span,
) -> bool {
    matches!(
        var_refs.get(&callee_span),
        Some(cranelisp_types::VarRef::Global(_))
    )
}

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
pub(super) fn apply_subst_to_expr(subst: &Subst, expr: &mut Expr) {
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
pub(super) fn annotate_expr_from_maps(
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
/// Always returns `Some(view)` (S110 W0.b totalization,
/// `design/arch/backend-keyed-consumer.md` §4 W0.b / §5): typecheck is the SOLE
/// mono-view producer for every codegen-reached body, so this helper never
/// yields `None` for a codegen-bound `Concrete` entry.
///
/// **Strict-first, lenient-fallback.** When `MonoExpr::from_expr` succeeds
/// (every body node fully concrete — the universal real-program case) the strict
/// view is returned. When it fails (a residual `Var` / un-annotated node reached
/// a value position — a multi-sig variant with an unconstrained param mangled
/// `f$Var`, or a body whose forward-reference `Apply` result var the backend
/// resolves via the symbol table, not the node) it falls back to
/// [`MonoExpr::lenient_from_expr`] — the SAME lenient walk the backend used to
/// run on these bodies (`lib.rs:909`'s deleted arm), so codegen is byte-identical
/// (the W0.b golden-CLIF gate `tests/golden_clif_w0b.rs`). The mono-instance seam
/// stays hard-error (a minted instance MUST be concrete, §3.11.1); this
/// best-effort/hard-error asymmetry is deliberate.
///
/// The backend no longer carries a lenient rebuild path: `compile_to_module`
/// hard-errors on a `codegen_view: None` for a codegen-reached body (Principle
/// 18). Synthetic ctor/accessor bodies (`Span::SYNTHETIC`, outside span-keyed
/// transport) are populated DIRECTLY at their synthesis seams (`adt.rs`), not
/// here.
///
/// **S114 carrier flip — the `ViewBuildError` fork (design §4.3).** The strict
/// `from_expr` now returns `Result<_, ViewBuildError>`, and the two failure arms
/// route DIFFERENTLY:
/// - `NotConcrete` — legitimate TYPE incompleteness (multi-sig `f$Var` variants,
///   forward-reference result vars) — falls back to `lenient_from_expr` exactly
///   as pre-flip.
/// - `Unresolved` — a real-span `Var`/`Apply` with no typed verdict: the
///   phase-boundary gate the carrier exists for. It MUST NOT be swallowed into
///   the lenient fallback (the lenient walk would seam-assert on the same miss);
///   it propagates as a LOCATED typecheck-phase error. This is why the helper's
///   return widens to `Result<Option<..>, CranelispError>`; callers thread `?`.
pub(crate) fn build_concrete_codegen_view(
    name: &Symbol,
    variant: &DefnVariant,
    pattern_ctors: &HashMap<Span, cranelisp_types::FQSymbol>,
    var_refs: &HashMap<Span, cranelisp_types::VarRef>,
    apply_refs: &HashMap<Span, cranelisp_types::ApplyRef>,
) -> Result<Option<cranelisp_types::MonoDefnVariant>, CranelispError> {
    let body = match cranelisp_types::MonoExpr::from_expr(
        &variant.body,
        pattern_ctors,
        var_refs,
        apply_refs,
    ) {
        Ok(mono_body) => mono_body,
        Err(cranelisp_types::ViewBuildError::NotConcrete(_)) => {
            cranelisp_types::MonoExpr::lenient_from_expr(
                &variant.body,
                pattern_ctors,
                var_refs,
                apply_refs,
            )
        }
        Err(cranelisp_types::ViewBuildError::Unresolved { span, name: ref_name }) => {
            // The located typecheck-phase gate error (design §4.2/§4.3): a
            // reference typecheck could not classify surfaces HERE, never a
            // codegen-time keyed miss (wrong phase).
            return Err(CranelispError::TypeError {
                message: format!(
                    "unresolved reference `{ref_name}` in the codegen view of \
                     `{name}` — typecheck recorded no local/global verdict for \
                     this reference (in-process producer bug; \
                     design/arch/typed-resolution-carrier.md §4.2)"
                ),
                location: cranelisp_types::ErrorLocation::from_span(span),
            });
        }
    };
    Ok(Some(cranelisp_types::MonoDefnVariant {
        name: name.clone(),
        params: variant.params.iter().map(|(n, _)| n.clone()).collect(),
        body,
        span: variant.span,
        mode_summary: None,
    }))
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


/// Mangle a function name with its parameter type signature.
/// e.g., `mangle_sig("foo", &[Type::Int, Type::Bool])` → `"foo$Int+Bool"`.
/// Returns true if `name` matches the trait-impl mangled form `Trait.method$Type`
/// (e.g., `Double.double$Int`, `Num.+$Int`, `Countable.count-plus$Int`).
///
/// This is used to distinguish annotated defns produced by `check_impl_method`
/// from user-written or REPL-synthetic defns (`__expr`), so that the
/// "skip re-inference" fast path only applies to trait impl methods.
pub(super) fn is_trait_impl_mangled_name(name: &str) -> bool {
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
pub(super) fn existing_callable_slot<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore>(
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
pub(super) fn is_macro_clause_defn_name(name: &str) -> bool {
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
pub(super) fn enrich_macro_clause_resolution_error(
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


pub(super) fn mangle_sig(name: &str, param_types: &[Type]) -> Symbol {
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
pub(super) fn types_compatible(a: &Type, b: &Type) -> bool {
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


/// The outcome of matching an overloaded call's concrete args against the
/// registered variants of its base name.
pub(crate) enum OverloadSelection<'v> {
    /// Exactly one variant's params are compatible with the args.
    Unique(&'v (Vec<Type>, Type, Symbol)),
    /// No variant matches the arity + arg types.
    NoMatch,
    /// More than one variant matches (the count is carried for the diagnostic).
    Ambiguous(usize),
}

/// Select the overload variant whose parameter types are ALL `types_compatible`
/// with `concrete_args` (arity filter + per-arg compatibility zip + unique
/// match). This is the ONE overload-selection predicate (Principle 7),
/// consumed by BOTH `resolve_pending_overloads` (the drain — unifies the
/// `Unique` winner, errors on `NoMatch`/`Ambiguous`) and
/// `collect_pending_overload_result_vars` (the pre-drain read-only benign-var
/// scan — only the `Unique` case contributes). Before CS-4.1 each consumer
/// hand-copied the predicate — the P7 mirror `/review` flagged (I-B).
pub(crate) fn select_unique_overload_variant<'v>(
    variants: &'v [(Vec<Type>, Type, Symbol)],
    concrete_args: &[Type],
) -> OverloadSelection<'v> {
    let matches: Vec<&(Vec<Type>, Type, Symbol)> = variants
        .iter()
        .filter(|(param_types, _ret, _mangled)| {
            param_types.len() == concrete_args.len()
                && param_types
                    .iter()
                    .zip(concrete_args.iter())
                    .all(|(p, a)| types_compatible(p, a))
        })
        .collect();
    match matches.as_slice() {
        [only] => OverloadSelection::Unique(only),
        [] => OverloadSelection::NoMatch,
        many => OverloadSelection::Ambiguous(many.len()),
    }
}



