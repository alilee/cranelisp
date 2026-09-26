use std::collections::{HashMap, HashSet};

use cranelisp_types::{
    CallableOrigin, ConstrainedMeta, CranelispError, Decl, Defn, DefnVariant, ErrorLocation,
    FQSymbol, FQTraitName, FQTypeName, ModuleFullPath, MonoDefnVariant, ResolvedCall, Span, Symbol,
    TemplateKind, TraitDeclInfo, TraitImpl, TraitMethodSig, TraitName, TraitRecord, Type, TypeId,
    Visibility, WrittenTraitImpl, apply, trait_impl_key,
};

use super::*;
use crate::checker::{BodyFrame, CheckState, TypeCheckEnv};
use crate::scheme;

/// Canonical identity and declaration produced by the one impl-head resolve.
///
/// Keeping these fields together prevents impl registration from pairing a
/// declaration found through one spelling with a home re-resolved through
/// another spelling (Principle 24 — resolve once).
#[derive(Clone)]
struct ResolvedImplTrait {
    fq: FQTraitName,
    decl: TraitDeclInfo,
}

/// Arity-aware fix suggestion for a Case-1 kind diagnostic (`hkt.md` §5.4 M2):
/// one fresh type-var per declared parameter, drawn from the constructor's
/// arity. `(Option a)` for arity 1, `(Pair a b)` for arity 2, `(Tri a b c)`
/// for arity 3 — NOT a hard-coded single-var template (which under-applies a
/// multi-param constructor). The vars are the single lowercase letters
/// `a, b, c, …` in order.
fn arity_var_suggestion(head: &str, arity: usize) -> String {
    let vars: Vec<String> = (0..arity)
        .map(|i| ((b'a' + i as u8) as char).to_string())
        .collect();
    format!("({head} {})", vars.join(" "))
}

/// Add the declaration context that a raw body-check error cannot carry.
///
/// The body checker is also used by monomorphisation, so impl-specific names
/// belong at this caller boundary rather than in the shared inference helper.
fn impl_conformance_error(
    error: CranelispError,
    trait_name: &TraitName,
    method_name: &Symbol,
    impl_type: &FQTypeName,
) -> CranelispError {
    match error {
        CranelispError::TypeError { message, location } => CranelispError::TypeError {
            message: format!(
                "impl of trait `{trait_name}` for `{impl_type}`: method `{method_name}` does not conform: {message}"
            ),
            location,
        },
        other => other,
    }
}

// ---------------------------------------------------------------------------
// Impl Registration and Checking
// ---------------------------------------------------------------------------

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    fn resolve_impl_trait_ref(
        &self,
        state: &CheckState,
        written: &cranelisp_types::TraitRef,
        span: Span,
    ) -> Result<ResolvedImplTrait, CranelispError> {
        let written_name = written.to_string();
        let resolved =
            self.scope_resolve(state, &written_name, span)
                .map_err(|error| match error {
                    cranelisp_types::ResolveError::PrivateInaccessible { .. } => {
                        CranelispError::from(error)
                    }
                    _ => CranelispError::TypeError {
                        message: format!("unknown trait: {written_name}"),
                        location: ErrorLocation::from_span(span),
                    },
                })?;
        let Decl::Trait(TraitRecord { info: decl, .. }) = resolved.entry.declaration else {
            return Err(CranelispError::TypeError {
                message: format!("unknown trait: {written_name}"),
                location: ErrorLocation::from_span(span),
            });
        };
        Ok(ResolvedImplTrait {
            fq: FQTraitName::new(resolved.canonical.module, decl.name.clone()),
            decl,
        })
    }

    /// Register and validate a trait implementation.
    pub(crate) fn register_trait_impl(
        &self,
        state: &mut CheckState,
        impl_: &TraitImpl,
    ) -> Result<Vec<Defn>, CranelispError> {
        // Look up the trait declaration via SymbolTables. The `impl` form's
        // `trait_name` is a REFERENCE to resolve, so it routes through the ONE
        // scope resolve (`resolve_trait_decl` → `resolve_terminal_entry_scoped`),
        // with the prelude fallback intrinsic (S108 Wave-G). A PRELUDE-GLOBBED
        // trait (reachable at `user` only via the implicit prelude glob, no
        // `Import` edge) therefore resolves here, exactly as a bare `Display`
        // resolves in a lookup position.
        let resolved_trait = self.resolve_impl_trait_ref(state, &impl_.trait_name, impl_.span)?;
        let decl = resolved_trait.decl.clone();
        let fq_trait_name = resolved_trait.fq.clone();
        let trait_home = fq_trait_name.module.clone();

        // §7.3.5 Case-3 kind-check seam — ONE deterministic path
        // (`design/typecheck/hkt.md` §5.4). The trait's DECLARATION is
        // authoritative on its kind: `type_params` non-empty ⟺ higher-kinded
        // (§5.1; Principle 24 — the sole kind source, no method-body usage
        // re-scan). Slot 1 MUST echo that declared head shape (and, for HK, the
        // con_var spelling); slot 2 is then interpreted STRICTLY per the known
        // kind — no second "is slot-2 a trait or a type-constructor?" classifier.
        // For an HK impl the pairing's constructor arg is extracted and becomes
        // the effective impl target, so every downstream method-check (which
        // assumes the target head is the impl type) is unchanged.
        let is_hk = !decl.type_params.is_empty();

        // Step 3: slot-1 echo validation — shape AND con_var spelling, BOTH
        // checked here against the declaration (a parenthesized head with the
        // WRONG con_var spelling still carries `Some(_)`, so the shape bit alone
        // is a fidelity gap).
        match (is_hk, &impl_.head_con_var) {
            (true, None) => {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "trait {} is higher-kinded; its impl head must echo the \
                         declared form `({} {})`",
                        impl_.trait_name, decl.name, decl.type_params[0]
                    ),
                    location: ErrorLocation::from_span(impl_.span),
                });
            }
            (false, Some(_)) => {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "trait {} is a conventional (kind-`*`) trait; its impl \
                         head is the bare name `{}`",
                        impl_.trait_name, decl.name
                    ),
                    location: ErrorLocation::from_span(impl_.span),
                });
            }
            (true, Some(written)) => {
                // §9.2: a single con_var. Shape OK — the spelling MUST match.
                let declared = &decl.type_params[0];
                if written != declared {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "impl head `({} {written})` does not echo trait {}'s \
                             declared head `({} {declared})`: the constructor \
                             variable is spelled `{written}` but was declared \
                             `{declared}`; reproduce the declared head verbatim \
                             as `({} {declared})`.",
                            decl.name, impl_.trait_name, decl.name, decl.name,
                        ),
                        location: ErrorLocation::from_span(impl_.span),
                    });
                }
            }
            (false, None) => { /* conventional shape OK — no spelling bit */ }
        }

        // Step 4: slot-2 interpretation per the known kind, plus effective-target
        // normalization for HK.
        let rewritten_impl;
        let impl_: &TraitImpl = if is_hk {
            // Higher-kinded (§7.3.5 Case 2): slot 2 is the pairing
            // `(Trait Constructor)`, parsed as `Applied(Trait, [Constructor])`
            // (`hkt.md` §5.4). The kind-check lands on `Constructor`, which MUST
            // be a bare constructor whose arity matches the con_var's
            // usage-derived kind (§7.2.1). §9.2: exactly one con_var.
            let con_name = &decl.type_params[0];
            let expected_arity = con_var_arity(&decl, con_name).expect(
                "invariant: a registered HK trait has an applied con_var \
                 (declaration-time reject guarantees it)",
            );
            let con_ref: cranelisp_types::TypeRef = match &impl_.target {
                cranelisp_types::TypeExpr::Applied(pairing_head, args) if args.len() == 1 => {
                    // B1 (§7.3.5 Case-2, the 4th rejection) — validate the
                    // pairing head FIRST, before the constructor kind-check. The
                    // pairing head MUST name the same trait slot 1 resolves to
                    // (spec §7.3 EBNF `hkt_target = '(' trait_name con_target ')'`).
                    // Resolve it as a `trait_name` reference the SAME way slot 1
                    // was (`resolve_trait` / `scope_resolve`, prelude-fallback
                    // aware) and compare RESOLVED FQ-identity — never written
                    // spelling — against slot-1's hoisted `fq_trait_name`. The
                    // WRITTEN QUALIFIER PARTICIPATES: the head is a §8.5
                    // `trait_name` reference, so its `pairing_head.module`
                    // (`Some` for `fmt/Functor`, `None` for a bare `Functor`) is
                    // threaded into the resolve, NOT dropped (S112 R-1). The
                    // canonical written spelling is rendered by `TypeRef`'s own
                    // Display (`module/name` when qualified) and handed to the ONE
                    // resolution mechanism (`scope_resolve` splits on `/`) — no
                    // second qualified-resolution path (Principle 7). Thus a
                    // qualified spelling resolving to slot-1's trait (`fmt/Functor`
                    // ≡ imported bare `Functor`) ACCEPTS by resolved identity
                    // (§7.3.5 *Pairing-head identity*, TB-25); a head resolving to
                    // a DIFFERENT trait (`other/Functor`), or to NO trait — a bad
                    // qualifier (`nosuchmod/Functor`) or a nonexistent bare name —
                    // both collapse to "FQ ≠ slot-1's FQ / no FQ" and reject.
                    // Closes the `:98` head-discard the /review B1 probe exercised
                    // (`(impl (Functor f) (NotFunctor Option) …)` silently
                    // accepted + dispatched).
                    let pairing_written = pairing_head.to_string();
                    let pairing_ref = cranelisp_types::TraitRef::new(
                        pairing_head.module.clone(),
                        TraitName::from(pairing_head.name.as_ref()),
                    );
                    let pairing_fq = self
                        .resolve_impl_trait_ref(state, &pairing_ref, impl_.span)
                        .ok()
                        .map(|resolved| resolved.fq);
                    if pairing_fq.as_ref() != Some(&fq_trait_name) {
                        let con_disp = args[0]
                            .head_ref()
                            .map(|r| r.name.to_string())
                            .unwrap_or_else(|| "_".to_string());
                        return Err(CranelispError::TypeError {
                            message: format!(
                                "impl of trait `{}` (slot 1) pairs slot 2 with head \
                                 `{}`: a trait-constructor pairing's head must name \
                                 the trait being implemented — write `({} {})`, not \
                                 `({} {})`.",
                                decl.name,
                                pairing_written,
                                decl.name,
                                con_disp,
                                pairing_written,
                                con_disp
                            ),
                            location: ErrorLocation::from_span(impl_.span),
                        });
                    }
                    match &args[0] {
                        cranelisp_types::TypeExpr::Named(cref) => cref.clone(),
                        cranelisp_types::TypeExpr::Applied(cref, _) => {
                            // fully-applied type, e.g. `(Functor (Option Int))`
                            return Err(CranelispError::TypeError {
                                message: format!(
                                    "kind-mismatch: slot 2 names the bare \
                                     constructor `{}`, not an applied type",
                                    cref.name
                                ),
                                location: ErrorLocation::from_span(impl_.span),
                            });
                        }
                        _ => {
                            return Err(CranelispError::TypeError {
                                message: format!(
                                    "trait {} is higher-kinded; slot 2 must be a \
                                     trait-constructor pairing `({} <Constructor>)`",
                                    impl_.trait_name, decl.name
                                ),
                                location: ErrorLocation::from_span(impl_.span),
                            });
                        }
                    }
                }
                _ => {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "trait {} is higher-kinded; slot 2 must be a \
                             trait-constructor pairing `({} <Constructor>)`",
                            impl_.trait_name, decl.name
                        ),
                        location: ErrorLocation::from_span(impl_.span),
                    });
                }
            };

            // Primitive → "not a type constructor" (§7.2.3), a DISTINCT reason
            // from the §7.1.1 no-occurrence rule.
            if matches!(con_ref.name.as_ref(), "Int" | "Bool" | "String" | "Float") {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "{} is not a type constructor (trait {} expects arity {})",
                        con_ref.name, impl_.trait_name, expected_arity
                    ),
                    location: ErrorLocation::from_span(impl_.span),
                });
            }

            // Arity match against the known ADT constructor. Resolve THROUGH THE
            // SCOPE (S108 Wave-G, R1) so a prelude-globbed constructor's arity is
            // read (resolve once, Principle 7).
            if let Some(td) = self
                .scope_resolve(state, con_ref.name.as_ref(), impl_.span)
                .ok()
                .as_ref()
                .and_then(|r| crate::checker::type_def_view_of(&r.entry))
                && td.type_params.len() != expected_arity
            {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "{} has {} type parameters; trait {} expects a \
                         constructor of arity {}",
                        con_ref.name,
                        td.type_params.len(),
                        impl_.trait_name,
                        expected_arity
                    ),
                    location: ErrorLocation::from_span(impl_.span),
                });
            }

            // Normalize: the effective impl target is the bare constructor, so
            // every downstream method-check/mangle site sees the impl type in
            // slot 2 exactly as it did for the pre-S112 `(impl Functor Option)`
            // form. MIRROR (M1): `src/session_v4/types.rs::impl_echo_type_name` performs the
            // reciprocal derivation on the DISPLAY side — it echoes the pairing's
            // constructor ARGUMENT (`Option`), not the pairing head (`Functor`),
            // so the introspection echo names the same type this normalization
            // registers the impl under (Principle 26 — render from settled state).
            // Keep the two in lock-step: both read the constructor out of
            // `Applied(pairing_head, [Constructor])`.
            rewritten_impl = TraitImpl {
                target: cranelisp_types::TypeExpr::Named(con_ref),
                ..impl_.clone()
            };
            &rewritten_impl
        } else {
            // Conventional (§7.3.5 Case 1): slot 2 MUST be kind `*` (a type).
            // When the target head is a known type constructor it MUST be applied
            // to EXACTLY its declared arity — the well-kinded set is
            // `provided == arity`. The former `>` (under-application only) guard
            // GENERALISES to `!=` (I1): an over-applied target `(Option Int Int)`
            // is now rejected too. Both flanking rejections carry a distinct
            // §7.3.5 diagnostic with an ARITY-AWARE fix suggestion (M2 — one fresh
            // type-var per declared parameter, never a hard-coded single var).
            let head = impl_target_name_or_panic(&impl_.target);
            let provided = match &impl_.target {
                cranelisp_types::TypeExpr::Applied(_, args) => args.len(),
                _ => 0,
            };
            let head_spelling = impl_target_head_spelling(&impl_.target, &state.current_module);
            if let Some(td) = self
                .scope_resolve(state, head_spelling.as_ref(), impl_.span)
                .ok()
                .as_ref()
                .and_then(|r| crate::checker::type_def_view_of(&r.entry))
            {
                let arity = td.type_params.len();
                if arity != provided {
                    let suggestion = arity_var_suggestion(head.as_ref(), arity);
                    let message = if provided < arity {
                        // Under-applied / bare (pre-existing) — `Option` is a
                        // constructor, not a type.
                        format!("{head} is a constructor, not a type; apply it: `{suggestion}`")
                    } else {
                        // Over-applied (I1, NEW) — an arity surplus.
                        format!(
                            "{head} takes {arity} type parameter{plural} but is \
                             applied to {provided} here; apply it to exactly its \
                             arity: `{suggestion}`",
                            plural = if arity == 1 { "" } else { "s" }
                        )
                    };
                    return Err(CranelispError::TypeError {
                        message,
                        location: ErrorLocation::from_span(impl_.span),
                    });
                }
            }
            impl_
        };

        // Impl-time field-accessor collision gate — superseded by spec §7.3.1
        // and retained as built pending ACT-0983 (see the function's rustdoc).
        self.check_impl_method_accessor_collisions(state, impl_)?;

        // Check all required methods are present (that don't have defaults)
        self.check_impl_methods_present(state, &decl, impl_)?;

        // Resolve the impl target's FQ type identity ONCE (Principle 7).
        // `fq_impl_type` is the home-qualified type head (`module/Type`) that
        // every impl-method symbol minted below — default, explicit, and HKT —
        // carries in its `$Type` suffix, kept in lock-step with the dispatch
        // site (S102 4th lossy-head cure). It reads the EFFECTIVE (post-rewrite)
        // `impl_.target`, so for an HK impl it resolves the bare constructor
        // (`Option`), not the pairing. `fq_trait_name`/`trait_home` are resolved
        // ONCE at the top of this function (Principle 24 — the sole minting site,
        // reused by the B1 pairing-head compare and the registry key below).
        let head_spelling = impl_target_head_spelling(&impl_.target, &state.current_module);
        let fq_impl_type = self
            .resolve_type(state, &head_spelling, impl_.span)
            .map_err(|failure| failure.into_form_error(state))?;

        // Generate default method implementations for missing methods
        let default_defns =
            self.generate_default_methods(state, &decl, impl_, &fq_trait_name, &fq_impl_type)?;

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
        // Trait reachability was just validated by `resolve_trait_decl`
        // above (prelude-fallback aware; `resolve_trait` below hops the
        // same way to find `trait_home`); the chain-follow must succeed. Treat
        // absence as a typecheck
        // invariant violation (post-FIXME 0192 method 6 deletion: no
        // `defining_module_for` fallback).
        // (`trait_home` / `fq_trait_name` / `fq_impl_type` resolved above — the
        // single-source-of-truth for both the impl registry key and every
        // impl-method mangle in this impl.)
        // The settled implementation surface includes generated defaults as
        // well as explicitly written bodies. This one list feeds both the
        // staged shell and its writer-side cache record.
        let method_names: Vec<Symbol> = decl.methods.iter().map(|m| m.name.clone()).collect();

        let writer_module = state.current_module.clone();
        let written_impl = WrittenTraitImpl::new(
            fq_trait_name.clone(),
            fq_impl_type.clone(),
            writer_module.clone(),
            method_names,
            Visibility::Public,
        );

        // Default bodies are checked as concrete impl methods below. A default
        // may call a required sibling (`bump` calling `size`), and that dispatch
        // must resolve against the candidate impl while its methods are being
        // validated. Stage the impl shell now, but retain the prior shell so the
        // method-check transaction can restore it on any failure. This makes the
        // candidate visible to conformance checking without publishing a failed
        // first impl or partially replacing a settled re-impl (§7.1.5, §5.4.5).
        // Method checking writes each settled mangled `Def` at its normal
        // seam. Snapshot the complete method grain so a later sibling failure
        // can restore the prior enrollment (or remove first-impl writes).
        // This covers first impl and re-impl with the same transaction path.
        let method_symbols: Vec<Symbol> = decl
            .methods
            .iter()
            .map(|method| {
                Symbol::from(
                    mangle_trait_method(
                        fq_trait_name.name.as_ref(),
                        method.name.as_ref(),
                        &fq_impl_type,
                    )
                    .as_str(),
                )
            })
            .collect();
        let retained_methods = self
            .current_symbol_table_mut(state)
            .retain_callables(&method_symbols)
            .map_err(crate::result::lifecycle_error)?;
        let staged_shell = {
            let mut table = self.symbol_table_mut_in(&trait_home);
            table.stage_trait_impl_shell(&written_impl)?
        };

        // Type-check each impl method body and generate mangled-name Defns.
        // check_impl_method returns the annotated defn (already written to
        // ModuleEntry::Def.ast under the mangled name).
        let checked = (|| -> Result<Vec<Defn>, CranelispError> {
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
                // Expected format: "{trait_name}.{method_name}${home}/{target_type}"
                // (the `$Type` suffix is FQ per `mangle_trait_method`, so the strip
                // suffix is `${fq_impl_type}`, not the bare target head).
                let mangled = default_defn.name.as_ref();
                let prefix = format!("{}.", decl.name);
                let suffix = format!("${}", fq_impl_type);
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
                    &fq_trait_name,
                    &fq_impl_type,
                )?;
                all_defns.push(annotated);
            }

            for method_defn in &impl_.methods {
                let annotated = self.check_impl_method(
                    state,
                    &decl,
                    impl_,
                    method_defn,
                    &fq_trait_name,
                    &fq_impl_type,
                )?;
                all_defns.push(annotated);
            }

            Ok(all_defns)
        })();

        let all_defns = match checked {
            Ok(defns) => defns,
            Err(err) => {
                debug_assert_eq!(state.current_module, writer_module);
                self.current_symbol_table_mut(state)
                    .rollback_callables(retained_methods)
                    .map_err(crate::result::lifecycle_error)?;
                self.symbol_table_mut_in(&trait_home)
                    .rollback_trait_impl_shell(staged_shell)?;
                return Err(err);
            }
        };

        self.current_symbol_table_mut(state)
            .upsert_written_trait_impl(written_impl)?;
        retained_methods.commit();
        staged_shell.commit();

        Ok(all_defns)
    }

    /// Check that all required methods are provided in the impl.
    fn check_impl_methods_present(
        &self,
        _state: &CheckState,
        decl: &TraitDeclInfo,
        impl_: &TraitImpl,
    ) -> Result<(), CranelispError> {
        let provided: std::collections::HashSet<&str> =
            impl_.methods.iter().map(|m| m.name.as_ref()).collect();

        for method_sig in &decl.methods {
            // Skip methods with defaults
            if method_default_body(method_sig).is_some() {
                continue;
            }
            if !provided.contains(method_sig.name.as_ref()) {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "impl {} for {}: missing required method {}",
                        decl.name,
                        impl_target_name_or_panic(&impl_.target),
                        method_sig.name
                    ),
                    location: ErrorLocation::from_span(impl_.span),
                });
            }
        }

        Ok(())
    }

    /// Reject a trait `impl` whose method name equals a field-accessor name of
    /// the impl target type.
    ///
    /// **Superseded behaviour, retained as built.** Spec §7.3.1 permits this
    /// overlap: the accessor `Box.v` and the method `HasV.v` stay distinct and
    /// both project the bare spelling `v`
    /// (`design/typecheck/fixme-0365-field-accessor-dotted.md` §2). Removing
    /// this gate and `field_accessor_names_of` awaits defect intake under
    /// `sprints/actions/ACT-0983-accessor-impl-collision-intake.md` (design
    /// §2.1); until then its behaviour and tests are unchanged.
    ///
    /// As built, it runs as a name-level pre-flight before the impl registers
    /// or any body is checked, so a colliding impl produces no `TraitImpl`
    /// entry. The accessor names come from `field_accessor_names_of`, which
    /// reads the union view (staging + live), so an accessor from an earlier
    /// REPL cluster also counts. A primitive / non-ADT target has no field
    /// accessors, so the check trivially passes.
    fn check_impl_method_accessor_collisions(
        &self,
        state: &CheckState,
        impl_: &TraitImpl,
    ) -> Result<(), CranelispError> {
        // Resolve the impl target to its `FQTypeName`. A primitive / non-ADT
        // target resolves to `IntrinsicType` (not an ADT), so there are no field
        // accessors to collide with — pass. An unresolvable target is left for
        // the downstream method-body checks to diagnose.
        let target_ty = match self.concrete_type_for_impl_target(
            state,
            &impl_target_head_spelling(&impl_.target, &state.current_module),
            Vec::new(),
            impl_.span,
        ) {
            Ok(t) => t,
            Err(_) => return Ok(()),
        };
        let Type::ADT(fqtn, _) = target_ty else {
            return Ok(());
        };

        let accessor_names = self.field_accessor_names_of(state, &fqtn);
        if accessor_names.is_empty() {
            return Ok(());
        }

        for method in &impl_.methods {
            if accessor_names.contains(&method.name) {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "impl {} for {}: method `{}` collides with the field \
                         accessor `{}` generated by the field `{}` of type `{}` \
                         (see deftype). A trait method must not shadow an \
                         existing field accessor — rename the method or the field.",
                        impl_.trait_name,
                        fqtn.name,
                        method.name,
                        method.name,
                        method.name,
                        fqtn.name,
                    ),
                    location: ErrorLocation::from_span(method.span),
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
        fq_trait_name: &FQTraitName,
        fq_impl_type: &FQTypeName,
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
        self.check_impl_method_with_sig(
            state,
            decl,
            impl_,
            method_defn,
            method_sig,
            false,
            None,
            fq_trait_name,
            fq_impl_type,
        )
    }

    /// Type-check an impl method (or default method) given an explicit trait method sig.
    ///
    /// `is_default_mangled` = true indicates the `method_defn.name` is already mangled
    /// (`Trait.method$Type`) as generated by `generate_default_methods`. In that case
    /// the existing name is used as the symbol-table key; otherwise the mangled name is
    /// built from canonical `fq_trait_name.name + method_defn.name + fq_impl_type`;
    /// the as-written `impl_.trait_name` is never a mangle input.
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
        fq_trait_name: &FQTraitName,
        fq_impl_type: &FQTypeName,
    ) -> Result<Defn, CranelispError> {
        for variant in &method_defn.variants {
            if variant.params.len() != method_sig.params.len() {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "impl method `{}` has {} parameter{}, but trait `{}` declares {}",
                        method_defn.name,
                        variant.params.len(),
                        if variant.params.len() == 1 { "" } else { "s" },
                        decl.name,
                        method_sig.params.len(),
                    ),
                    location: ErrorLocation::from_span(variant.span),
                });
            }
        }

        // TB24b (§7.3.3 + §8.5) — the impl-target constraint slot's trait
        // references (`(Box :Disp a)` → `type_constraints = [(a, Disp)]`) MUST
        // resolve, exactly as a param-position bound (`:C x`) does — an unknown
        // trait there is an error, NOT a silent accept (`(Box :NoSuchTrait a)`).
        // The constraint rides `impl_.type_constraints`, typecheck-reachable but
        // previously never routed through trait resolution. Resolve each ref
        // honouring qualification, mirroring `resolve_bound_param`; a bare unknown
        // trait fails `resolve_trait` (TraitNotFound). Run before the HK branch so
        // it covers every impl kind.
        for (_var, tref) in &impl_.type_constraints {
            // Compose the as-written reference (qualified `fmt/Disp` or bare
            // `Disp`) and resolve it through the ONE trait resolver — `resolve_trait`
            // routes qualified names through `scope_resolve`'s `/`-split and errors
            // (`TraitNotFound`) on an unknown trait or a non-`TraitDecl` terminal.
            let name: String = match &tref.module {
                Some(m) => format!("{m}/{}", tref.name),
                None => tref.name.to_string(),
            };
            self.resolve_trait(state, &name, impl_.span)
                .map_err(CranelispError::from)?;
        }

        // Kind is read from the DECLARATION alone: `type_params` non-empty ⟺
        // higher-kinded (§5.1; Principle 24 — the same single declaration fact
        // the §7.3.5 Case-3 seam reads, no method-body usage re-scan). A
        // successfully-registered non-empty-`type_params` trait is genuinely HK
        // (the declaration-time never-applied reject guarantees it).
        let is_hkt = !decl.type_params.is_empty();

        if is_hkt {
            return self.check_hkt_impl_method(
                state,
                decl,
                impl_,
                method_defn,
                method_sig,
                fq_trait_name,
                fq_impl_type,
            );
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
        // TB-24 (§3.2): resolve the conventional impl target's ARGS through the
        // ONE shared type-expr resolver (P7), mirroring the HKT pairing path
        // (`resolve_hkt_impl_type_expr`). A poly-applied target `(Option a)` then
        // binds its lowercase con-var `a` as a fresh `Type::Var` (mint-on-miss)
        // for co-reference — instead of the hand-rolled bare-head NAMED lookup
        // (`concrete_type_for_impl_target(TypeName("a"), …)`), which reduced each
        // arg to its head string and rejected `a` as `unknown type a` before the
        // §7.3.5 arity gate (the 0590-tightening blast-radius on a position that
        // legitimately holds a var). A concrete arg (`Int` in `(Option Int)`)
        // resolves byte-identically — both route the head through the symbol table.
        // The `var_map` is the SAME map the method sigs mint into below, so a
        // target var co-refers with a like-named sig var (spec §3.3.1).
        let module = state.current_module.clone();
        let mut var_map: HashMap<Symbol, TypeId> = HashMap::new();
        let target_args: Vec<cranelisp_types::TypeExpr> = match &impl_.target {
            cranelisp_types::TypeExpr::Applied(_, args) => args.clone(),
            _ => Vec::new(),
        };
        let resolved_type_args: Vec<Type> = target_args
            .iter()
            .map(|arg| {
                self.resolve_annotation_type_expr_in_module(arg, &mut var_map, &module, impl_.span)
                    .map_err(|failure| failure.into_form_error(state))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let concrete_self = self
            .concrete_type_for_impl_target(
                state,
                &impl_target_head_spelling(&impl_.target, &module),
                resolved_type_args,
                impl_.span,
            )
            .map_err(|failure| failure.into_form_error(state))?;

        // FIXME 0590: route method sigs through the ONE resolver via the trait-sig
        // wrapper. `Self` and every trait type-parameter name (`decl.type_params`)
        // substitute `concrete_self` (here a concrete ADT, possibly poly-applied).
        // Free lowercase names mint into the same `var_map` for co-reference; a
        // qualified type ref resolves canonically (FIXME 0436 / spec §8.5).

        // Build concrete param types
        let param_types: Vec<Type> = method_sig
            .params
            .iter()
            .map(|(_, p)| {
                self.resolve_trait_sig_type_expr(
                    p,
                    &mut var_map,
                    &module,
                    &concrete_self,
                    &decl.type_params,
                    method_defn.span,
                )
                .map_err(|failure| failure.into_form_error(state))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let ret_ty = if let Some(ret) = method_result_constraint(method_sig) {
            self.resolve_trait_sig_type_expr(
                ret,
                &mut var_map,
                &module,
                &concrete_self,
                &decl.type_params,
                method_defn.span,
            )
            .map_err(|failure| failure.into_form_error(state))?
        } else {
            self.fresh_var()
        };

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
        let body_module = state.current_module.clone();
        // An impl/default body settles at this seam rather than joining the
        // top-level body ledger. Isolate its pending overload calls so this
        // local drain cannot consume work owned by the later module drain.
        let saved_pending_overloads = std::mem::take(&mut state.pending_overload_resolutions);

        let mut method_clone = method_defn.clone();
        let body_result =
            self.check_defn_body_with_types(state, &mut method_clone, &param_types, &ret_ty);
        state.pending_overload_resolutions = saved_pending_overloads;

        // Restore the writer's module before the writeback (unconditional, mirrors
        // `recheck_body_for_mono`'s save/restore discipline).
        if let Some(prev) = saved_current_module {
            state.current_module = prev;
        }

        let user_fn_refs = body_result.map_err(|error| {
            impl_conformance_error(error, &decl.name, &method_sig.name, fq_impl_type)
        })?;

        // Build the mangled name and create annotated defn for symbol table.
        // For default methods, `method_defn.name` is already mangled by
        // generate_default_methods (e.g., "Countable.count-plus$Int"), so we
        // use the name as-is to avoid double-mangling.
        let mangled_sym = if is_default_mangled {
            method_defn.name.clone()
        } else {
            // FQ `$Type` suffix, lock-step with the dispatch site
            // (`mangle_trait_method`) — S102 4th lossy-head cure.
            let mangled = mangle_trait_method(
                fq_trait_name.name.as_ref(),
                method_defn.name.as_ref(),
                fq_impl_type,
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
            &user_fn_refs,
            &body_module,
            fq_trait_name,
            fq_impl_type,
        )
    }

    /// Shared tail of `check_impl_method_with_sig` / `check_hkt_impl_method`.
    ///
    /// Both methods, after checking the method body with concrete param/return
    /// types, select facts for that exact body's spans, annotate a fresh `Defn`
    /// clone with those types + resolved calls, apply the final substitution,
    /// and write the annotated `DefnVariant` into the symbol table (inserting a
    /// concrete-scheme `Def` entry if one doesn't already exist). Exact body
    /// spans, rather than a before-key snapshot, remain correct when separately
    /// parsed forms reuse source offsets; user references come directly from its
    /// completed `BodyFrame`.
    ///
    /// **Callee edges (FIXME 0472).** These Pass-1 bodies settle at this local
    /// seam rather than entering the module body ledger. Their exact canonical
    /// callees are harvested here and passed through the same checked-settlement
    /// call as the AST/view; there is no post-publication callee write.
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
        user_fn_refs: &HashMap<Span, FQSymbol>,
        body_module: &ModuleFullPath,
        fq_trait_name: &FQTraitName,
        fq_impl_type: &FQTypeName,
    ) -> Result<Defn, CranelispError> {
        let mut body_spans = HashSet::new();
        crate::program::collect_expr_spans(method_clone.body(), &mut body_spans);
        // The just-completed body overwrote every fact at its own source spans.
        // Selecting by exact membership avoids both cross-body leakage and the
        // repeated-offset hole of before-key delta extraction.
        let method_mr: HashMap<Span, ResolvedCall> = state
            .method_resolutions
            .resolved_calls
            .iter()
            .filter(|(span, _)| body_spans.contains(span))
            .map(|(span, res)| (*span, res.clone()))
            .collect();
        let method_et: HashMap<Span, Type> = state
            .expr_types
            .iter()
            .filter(|(span, _)| body_spans.contains(span))
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
        crate::program::annotate_defn_from_maps(&mut annotated, &method_et, &method_mr);
        crate::program::apply_subst_to_defn(&state.subst, &mut annotated);

        // Write the fully annotated defn to ModuleEntry::Def.ast.
        let fn_type = apply(
            &state.subst,
            &Type::Fn(param_types.to_vec(), Box::new(ret_ty.clone())),
        );
        // A trait impl method can retain variables supplied by the impl's
        // generic receiver (F2).  Tell the lifecycle the truth: quantify those
        // variables instead of claiming a monomorphic scheme over a residual
        // type.  The ordinary template/mono path can then specialise the
        // checked source body at a concrete dispatch site.
        let method_scheme = self.generalize(state, &fn_type);
        let ast_variant: Option<DefnVariant> = annotated.variants.first().cloned();
        // S84 Phase-3 (FIXME 0392): a trait-impl method (mangled `Trait.method$Type`)
        // is a codegen-bound `Concrete` entry — build its concrete-boundary
        // `MonoExpr` view from the same annotated, subst-resolved body the `ast`
        // carries (best-effort per `build_concrete_codegen_view`; a `Self`-typed
        // impl-method body checked against a contrived synthetic-span fixture can
        // legitimately leave a residual var the `ast`-path codegen never reads).
        let codegen_view: Option<MonoDefnVariant> = match ast_variant
            .as_ref()
            .filter(|_| method_scheme.ty.is_concrete())
        {
            Some(v) => crate::program::build_concrete_codegen_view(
                &mangled_sym,
                v,
                &method_scheme,
                &state.method_resolutions.pattern_ctors,
                &state.method_resolutions.var_refs,
                &state.method_resolutions.apply_refs,
            )?,
            None => None,
        };
        // Harvest before taking the table guard. `body_module` is the module in
        // which inference ran, so a default body's local SigDispatch keeps the
        // trait-home identity even after `state.current_module` is restored to
        // the impl writer.
        let callees = self.harvest_callees_in_module(&method_mr, user_fn_refs, body_module);
        let Some(ast) = ast_variant else {
            return Ok(annotated);
        };
        let shell = FQSymbol {
            module: fq_trait_name.module.clone(),
            symbol: trait_impl_key(fq_impl_type, fq_trait_name),
        };
        let mut st = self.current_symbol_table_mut(state);
        st.declare(
            mangled_sym.clone(),
            method_scheme.clone(),
            method_defn
                .params()
                .iter()
                .map(|(n, _)| n.clone())
                .collect(),
            method_defn.docstring.clone(),
            0,
            CallableOrigin::TraitMethod {
                shell,
                trait_name: fq_trait_name.clone(),
                impl_type: fq_impl_type.clone(),
            },
            Visibility::Public,
        )
        .map_err(crate::result::lifecycle_error)?;
        if method_scheme.ty.is_concrete() {
            let Some(view) = codegen_view else {
                return Ok(annotated);
            };
            st.settle_checked_concrete(&mangled_sym, method_scheme, ast, view, callees)
                .map_err(crate::result::lifecycle_error)?;
        } else {
            let kind = if method_scheme.constraints.is_empty() {
                TemplateKind::Parametric
            } else {
                TemplateKind::Constrained(Box::new(ConstrainedMeta::new(
                    method_scheme.constraints.clone(),
                )))
            };
            st.settle_checked_template(&mangled_sym, method_scheme, ast, kind, callees)
                .map_err(crate::result::lifecycle_error)?;
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
        fq_trait_name: &FQTraitName,
        fq_impl_type: &FQTypeName,
    ) -> Result<Defn, CranelispError> {
        // Build con_var_map: constructor variable name -> resolve to ADT name
        // For HKT impls, we substitute constructor vars with the target ADT via
        // the HKT-impl sig wrapper, which produces concrete ADT types.
        let mut type_var_map: HashMap<Symbol, TypeId> = HashMap::new();

        // Determine the arity of the constructor from the trait signature
        let arity = decl
            .type_params
            .iter()
            .find_map(|p| con_var_arity(decl, p))
            .expect("invariant: HKT trait must use constructor param in Applied position");

        // Build the concrete self type: ADT(target, [fresh_vars...])
        let type_arg_vars: Vec<Type> = (0..arity).map(|_| self.fresh_var_id().0).collect();
        // Phase B Part 1.4(3): HKT impls may target ADT-shaped types only
        // (intrinsics have no type parameters and don't carry HKT shape).
        // Still use the centralised resolver to get a typed error if the
        // target is unknown.
        let target_fqtn = self
            .resolve_type(
                state,
                &impl_target_head_spelling(&impl_.target, &state.current_module),
                impl_.span,
            )
            .map_err(|failure| failure.into_form_error(state))?;
        let concrete_self = Type::ADT(target_fqtn.clone(), type_arg_vars);
        let module = state.current_module.clone();

        // Build param types using HKT-aware resolution that substitutes
        // constructor variable applications with concrete ADT applications
        // (FIXME 0590 — the ONE resolver via the HKT-impl sig wrapper).
        let param_types: Vec<Type> = method_sig
            .params
            .iter()
            .map(|(_, p)| {
                self.resolve_hkt_impl_type_expr(
                    p,
                    &mut type_var_map,
                    &module,
                    &decl.type_params,
                    &target_fqtn,
                    impl_.span,
                )
                .map_err(|failure| failure.into_form_error(state))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let ret_ty = self
            .resolve_hkt_impl_type_expr(
                method_result_constraint(method_sig).expect("HKT methods are required"),
                &mut type_var_map,
                &module,
                &decl.type_params,
                &target_fqtn,
                impl_.span,
            )
            .map_err(|failure| failure.into_form_error(state))?;

        // Pre-unify the dispatch parameter with the concrete self type
        if let Some(param_idx) = method_sig.hkt_param_index
            && let Some(param_ty) = param_types.get(param_idx)
        {
            self.unify(state, param_ty, &concrete_self, method_defn.span)?;
        }

        // Clone the method defn and check the body with the mutable copy. Keep
        // this local settlement's overload work separate from the module drain.
        let saved_pending_overloads = std::mem::take(&mut state.pending_overload_resolutions);
        let mut method_clone = method_defn.clone();
        let body_result =
            self.check_defn_body_with_types(state, &mut method_clone, &param_types, &ret_ty);
        state.pending_overload_resolutions = saved_pending_overloads;
        let user_fn_refs = body_result.map_err(|error| {
            impl_conformance_error(error, &decl.name, &method_sig.name, fq_impl_type)
        })?;

        // Build the mangled name and create annotated defn for symbol table.
        // FQ `$Type` suffix, lock-step with the dispatch site
        // (`mangle_trait_method`) — S102 4th lossy-head cure.
        let mangled = mangle_trait_method(
            fq_trait_name.name.as_ref(),
            method_defn.name.as_ref(),
            fq_impl_type,
        );
        let mangled_sym = Symbol::from(mangled.as_str());
        let body_module = state.current_module.clone();

        self.finalize_impl_method_writeback(
            state,
            method_defn,
            &method_clone,
            mangled_sym,
            &param_types,
            &ret_ty,
            &user_fn_refs,
            &body_module,
            fq_trait_name,
            fq_impl_type,
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
    ) -> Result<HashMap<Span, FQSymbol>, CranelispError> {
        // Binder provenance: the defn form span every param shares (S114
        // `VarRef::Local` — the impl-method / mono-recheck body frame).
        self.push_scope(state, defn.span);

        // This body is re-checked against ALREADY-CONCRETE param/ret types (a
        // monomorphisation instance or a trait-impl method): the caller has
        // chosen the types. Under W6.3 (spec §3.3.1–§3.3.2) rigidity lives only
        // on the constraint path and is seeded from constraint-carrying param
        // VARS — here the params are already concrete, so no rigid var arises.
        // Save/clear/restore the per-body inference sets so nothing leaks past
        // this body.
        let previous_frame = std::mem::replace(&mut state.body_frame, BodyFrame::explicit_types());

        for ((param_name, _), param_ty) in defn.params().iter().zip(param_types.iter()) {
            self.bind_local(state, param_name.clone(), scheme::mono(param_ty.clone()));
        }

        let result = (|| {
            let body_ty = self.infer_expr(state, defn.body())?;
            // The signature is the expectation; the inferred body is the
            // supplied value. Keep that direction in the diagnostic too.
            self.unify(state, ret_ty, &body_ty, defn.span)?;
            self.settle_body_work(
                state,
                defn.body(),
                crate::candidate_selection::BodySettlementScope::Isolated,
            )?;
            Ok(())
        })();

        let completed_frame = std::mem::replace(&mut state.body_frame, previous_frame);
        self.pop_scope(state);
        result.map(|()| completed_frame.user_fn_refs)
    }

    /// Generate default method implementations for methods not provided in the impl.
    pub(crate) fn generate_default_methods(
        &self,
        _state: &CheckState,
        decl: &TraitDeclInfo,
        impl_: &TraitImpl,
        fq_trait_name: &FQTraitName,
        fq_impl_type: &FQTypeName,
    ) -> Result<Vec<Defn>, CranelispError> {
        let provided: std::collections::HashSet<&str> =
            impl_.methods.iter().map(|m| m.name.as_ref()).collect();

        let mut defaults = Vec::new();

        for method_sig in &decl.methods {
            if provided.contains(method_sig.name.as_ref())
                || method_default_body(method_sig).is_none()
            {
                continue;
            }

            // Create a mangled name for this default method. FQ `$Type` suffix
            // (via `mangle_trait_method`) — the trait part is `decl.name`
            // (bare), matching the `{decl.name}.` / `${fq_impl_type}` demangle
            // in `register_trait_impl`. S102 4th lossy-head cure.
            let mangled = mangle_trait_method(
                fq_trait_name.name.as_ref(),
                method_sig.name.as_ref(),
                fq_impl_type,
            );

            let span = impl_.span;
            let body = if let Some(expr_body) = method_default_body(method_sig) {
                // User-defined default body: pre-parsed AST (S69 Submission 26).
                expr_body.clone()
            } else {
                // Hard-coded builtin defaults (Eq.!=, Ord.>, etc.)
                build_default_body(
                    decl.name.as_ref(),
                    method_sig.name.as_ref(),
                    &method_sig
                        .params
                        .iter()
                        .map(|(n, _)| n.clone())
                        .collect::<Vec<_>>(),
                    span,
                )?
            };

            defaults.push(Defn {
                name: Symbol::from(mangled.as_str()),
                docstring: None,
                variants: vec![DefnVariant {
                    params: method_sig
                        .params
                        .iter()
                        .map(|(n, _)| (n.clone(), None))
                        .collect::<Vec<_>>(),
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

#[cfg(test)]
mod tests;
