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

use cranelisp_types::{
    Binding, CallableArmDraft, CallableArmId, CallableOrigin, CallableTarget, ConstrainedMeta,
    CranelispError, Decl, Defn, DefnVariant, ErrorLocation, Expr, FQSymbol, JitSymbol, Life,
    MethodResolutions, ModuleFullPath, ModuleStrategy, MonoDefn, ResolvedCall, Span, Subst, Symbol,
    SymbolTable, TemplateBody, TemplateKind, TopLevel, Type, TypeId, Visibility, Warning, apply,
};

use crate::result::CheckResult;
use crate::result::{DispatchGap, UnresolvedDispatchSite};

use crate::checker::{CheckState, TypeCheckEnv};
use crate::scheme::mono;

mod body;
mod callees;
mod finalize;
pub(crate) use finalize::collect_expr_spans;
mod mono_collect;
mod register;
mod support;
#[cfg(test)]
mod test_driver;

// Re-export the free-function toolbox + callee helpers at the `program`
// level so sibling submodules reach them via `use super::*` and the
// existing `crate::program::<fn>` call sites in checker/adt/traits/infer
// keep resolving unchanged (a pure decomposition moves no path).
pub(crate) use callees::*;
pub(crate) use mono_collect::AutoCurryDrain;
pub(crate) use support::*;

pub(crate) struct FormCheckResult {
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
}

impl FormCheckResult {
    /// Create an empty FormCheckResult (used for no-op passes).
    pub(super) fn empty() -> Self {
        FormCheckResult {
            constrained_fn: None,
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings: Vec::new(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum BodyTarget {
    Direct(Symbol),
    MultiSignatureClause { group: Symbol, clause: usize },
}

#[derive(Clone, Debug)]
pub(crate) struct RegisteredBody {
    pub(crate) target: BodyTarget,
    pub(crate) publication_name: Symbol,
    pub(crate) param_types: Vec<Type>,
    pub(crate) ret_ty: Type,
    pub(crate) written_var_scope: HashMap<Symbol, TypeId>,
    pub(crate) span: Span,
}

#[derive(Clone, Debug)]
pub(crate) struct CheckedBody {
    pub(crate) registration: RegisteredBody,
    pub(crate) ast: DefnVariant,
    pub(crate) callees: Vec<FQSymbol>,
}

mod body_ledger {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
    struct BodySlot(usize);

    enum BodyState {
        Registered,
        Checked {
            ast: DefnVariant,
            callees: Vec<FQSymbol>,
        },
    }

    struct BodyRecord {
        registration: RegisteredBody,
        state: BodyState,
    }

    /// Ledger-borrowed capability for the only valid `Registered -> Checked` move.
    ///
    /// It borrows the exact record that created it and finishes through that
    /// borrow. There is no ledger argument to `finish`, so a capability from
    /// one ledger cannot be applied to another. Dropping it leaves the record
    /// in `Registered`; construction never removes data from the ledger.
    pub(crate) struct RegisteredBodyHandle<'ledger> {
        registration: &'ledger RegisteredBody,
        state: &'ledger mut BodyState,
    }

    impl RegisteredBodyHandle<'_> {
        pub(crate) fn registration(&self) -> &RegisteredBody {
            self.registration
        }

        pub(crate) fn finish(self, ast: DefnVariant, mut callees: Vec<FQSymbol>) {
            callees.sort_by(|a, b| {
                a.module
                    .as_ref()
                    .cmp(b.module.as_ref())
                    .then(a.symbol.as_ref().cmp(b.symbol.as_ref()))
            });
            callees.dedup();
            *self.state = BodyState::Checked { ast, callees };
        }
    }

    #[derive(Default)]
    pub(crate) struct BodyLedger {
        records: Vec<BodyRecord>,
        by_target: HashMap<BodyTarget, BodySlot>,
        by_publication: HashMap<Symbol, BodySlot>,
    }

    impl BodyLedger {
        pub(crate) fn reject_duplicate(
            &self,
            target: &BodyTarget,
            publication_name: &Symbol,
            span: Span,
        ) -> Result<(), CranelispError> {
            if self.by_target.contains_key(target)
                || self.by_publication.contains_key(publication_name)
            {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "illegal redefinition of `{publication_name}` in one compilation cluster; use one multi-signature definition for multiple bodies"
                    ),
                    location: ErrorLocation::from_span(span),
                });
            }
            Ok(())
        }

        pub(crate) fn register(&mut self, body: RegisteredBody) -> Result<(), CranelispError> {
            self.reject_duplicate(&body.target, &body.publication_name, body.span)?;
            let slot = BodySlot(self.records.len());
            self.by_target.insert(body.target.clone(), slot);
            self.by_publication
                .insert(body.publication_name.clone(), slot);
            self.records.push(BodyRecord {
                registration: body,
                state: BodyState::Registered,
            });
            Ok(())
        }

        fn registration(&self, slot: BodySlot) -> Option<&RegisteredBody> {
            self.records.get(slot.0).map(|record| &record.registration)
        }

        pub(crate) fn registration_for_publication(
            &self,
            name: &Symbol,
        ) -> Option<&RegisteredBody> {
            self.registration(*self.by_publication.get(name)?)
        }

        pub(crate) fn registration_for_target(
            &self,
            target: &BodyTarget,
        ) -> Option<&RegisteredBody> {
            self.registration(*self.by_target.get(target)?)
        }

        pub(crate) fn registered_for_check(
            &mut self,
            name: &Symbol,
        ) -> Option<RegisteredBodyHandle<'_>> {
            let slot = *self.by_publication.get(name)?;
            let record = self.records.get_mut(slot.0)?;
            if !matches!(record.state, BodyState::Registered) {
                return None;
            }
            Some(RegisteredBodyHandle {
                registration: &record.registration,
                state: &mut record.state,
            })
        }

        pub(crate) fn checked_for_publication(&self, name: &Symbol) -> Option<CheckedBodyRef<'_>> {
            let slot = *self.by_publication.get(name)?;
            let record = self.records.get(slot.0)?;
            let BodyState::Checked { ast, callees } = &record.state else {
                return None;
            };
            Some(CheckedBodyRef {
                registration: &record.registration,
                ast,
                callees,
            })
        }

        pub(crate) fn checked_mut_for_publication(
            &mut self,
            name: &Symbol,
        ) -> Option<CheckedBodyMut<'_>> {
            let slot = *self.by_publication.get(name)?;
            let record = self.records.get_mut(slot.0)?;
            let BodyState::Checked { ast, callees } = &mut record.state else {
                return None;
            };
            Some(CheckedBodyMut { ast, callees })
        }

        pub(crate) fn rekey_publication(
            &mut self,
            old_name: &Symbol,
            name: Symbol,
        ) -> Result<(), CranelispError> {
            let Some(&slot) = self.by_publication.get(old_name) else {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "internal: no checked-body publication owner for `{old_name}`"
                    ),
                    location: ErrorLocation::unknown(),
                });
            };
            if self
                .by_publication
                .get(&name)
                .is_some_and(|existing| *existing != slot)
            {
                let span = self
                    .registration(slot)
                    .map_or(Span::SYNTHETIC, |registration| registration.span);
                return Err(CranelispError::TypeError {
                    message: format!(
                        "checked-body publication target `{name}` already has an owner"
                    ),
                    location: ErrorLocation::from_span(span),
                });
            }

            // Both collision checks completed before any index or record move.
            let Some(record) = self.records.get_mut(slot.0) else {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "internal: checked-body publication index for `{old_name}` has no record"
                    ),
                    location: ErrorLocation::unknown(),
                });
            };
            record.registration.publication_name = name.clone();
            self.by_publication.remove(old_name);
            self.by_publication.insert(name, slot);
            Ok(())
        }

        pub(crate) fn checked_bodies(&self) -> impl Iterator<Item = CheckedBodyRef<'_>> + '_ {
            self.records.iter().filter_map(|record| {
                let BodyState::Checked { ast, callees } = &record.state else {
                    return None;
                };
                Some(CheckedBodyRef {
                    registration: &record.registration,
                    ast,
                    callees,
                })
            })
        }

        /// Consume the ledger at the sole publication window. Because this
        /// method takes `self`, no checked-body identity survives to publish a
        /// record a second time. An incomplete registered record is reported as
        /// an internal pipeline failure rather than being silently omitted.
        pub(crate) fn into_checked(self) -> Result<Vec<CheckedBody>, CranelispError> {
            self.records
                .into_iter()
                .map(|record| match record.state {
                    BodyState::Checked { ast, callees } => Ok(CheckedBody {
                        registration: record.registration,
                        ast,
                        callees,
                    }),
                    BodyState::Registered => Err(CranelispError::CodegenError {
                        message: format!(
                            "internal: registered body `{}` reached final publication unchecked",
                            record.registration.publication_name
                        ),
                        location: ErrorLocation::from_span(record.registration.span),
                    }),
                })
                .collect()
        }

        #[cfg(test)]
        pub(crate) fn snapshot(
            &self,
        ) -> (
            Vec<Option<(BodyTarget, Symbol)>>,
            Vec<Option<(BodyTarget, Symbol)>>,
            Vec<(BodyTarget, usize)>,
            Vec<(Symbol, usize)>,
        ) {
            let registered = self
                .records
                .iter()
                .map(|record| {
                    matches!(record.state, BodyState::Registered).then(|| {
                        (
                            record.registration.target.clone(),
                            record.registration.publication_name.clone(),
                        )
                    })
                })
                .collect();
            let checked = self
                .records
                .iter()
                .map(|record| {
                    matches!(record.state, BodyState::Checked { .. }).then(|| {
                        (
                            record.registration.target.clone(),
                            record.registration.publication_name.clone(),
                        )
                    })
                })
                .collect();
            let mut targets: Vec<_> = self
                .by_target
                .iter()
                .map(|(target, slot)| (target.clone(), slot.0))
                .collect();
            targets.sort_by_key(|(_, slot)| *slot);
            let mut publications: Vec<_> = self
                .by_publication
                .iter()
                .map(|(name, slot)| (name.clone(), slot.0))
                .collect();
            publications.sort_by_key(|(_, slot)| *slot);
            (registered, checked, targets, publications)
        }
    }

    pub(crate) struct CheckedBodyRef<'ledger> {
        pub(crate) registration: &'ledger RegisteredBody,
        pub(crate) ast: &'ledger DefnVariant,
        #[cfg_attr(not(test), allow(dead_code))]
        pub(crate) callees: &'ledger Vec<FQSymbol>,
    }

    pub(crate) struct CheckedBodyMut<'ledger> {
        pub(crate) ast: &'ledger mut DefnVariant,
        pub(crate) callees: &'ledger mut Vec<FQSymbol>,
    }
}

pub(crate) use body_ledger::BodyLedger;

/// Per-module accumulator for form-by-form typecheck results.
///
/// One accumulator per module. Created before Pass 1, consumed by
/// `finalize_check_result()`. No concurrent access — a single worker
/// processes one module's forms sequentially (`design/typecheck/typecheck.md` §5.2 item 5).
/// The ledger is the authoritative cross-pass owner of source bodies. Active
/// resolution and expression facts remain on `CheckState` through settlement,
/// then the final sweep moves them here once for annotation and publication.
pub(crate) struct ModuleCheckAccumulator {
    pub(crate) resolutions: MethodResolutions,
    pub(crate) expr_types: HashMap<Span, Type>,
    pub(crate) bodies: BodyLedger,
    pub(crate) constrained_fn_names: HashSet<Symbol>,
    pub(crate) mono_defns: Vec<MonoDefn>,
    pub(crate) default_method_defns: Vec<Defn>,
    pub(crate) multi_sig_defns: Vec<Defn>,
    pub(crate) warnings: Vec<Warning>,
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
            resolutions: MethodResolutions::new(),
            expr_types: HashMap::new(),
            bodies: BodyLedger::default(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings: Vec::new(),
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

fn callable_target_owner(target: &CallableTarget) -> Option<&FQSymbol> {
    match target {
        CallableTarget::Binding(owner)
        | CallableTarget::OverloadArm { owner, .. }
        | CallableTarget::MacroClause { owner, .. } => Some(owner),
        _ => None,
    }
}

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
    /// - Pass 1 is one sweep in form order (`design/typecheck/typecheck.md` §5.2 item 2).
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
pub(crate) mod test_support;

#[cfg(test)]
mod ledger_tests {
    use super::*;

    fn registered(target: BodyTarget, publication_name: &str, span: Span) -> RegisteredBody {
        RegisteredBody {
            target,
            publication_name: Symbol::from(publication_name),
            param_types: vec![Type::Int],
            ret_ty: Type::Int,
            written_var_scope: HashMap::new(),
            span,
        }
    }

    fn checked_ast(span: Span) -> DefnVariant {
        DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body: Expr::IntLit {
                value: 1,
                span,
                inferred_type: Some(Box::new(Type::Int)),
            },
            span,
        }
    }

    // spec: design/typecheck/checked-body-publication.md §4;
    //   tests/plan/s121-test-plan.md §3.8 LC-1.
    #[test]
    fn ledger_enforces_registered_checked_consumed_lifecycle() {
        let mut ledger = BodyLedger::default();
        let span = Span::new(10, 20);
        let name = Symbol::from("f");
        ledger
            .register(registered(BodyTarget::Direct(name.clone()), "f", span))
            .unwrap();
        let registered_snapshot = ledger.snapshot();
        drop(
            ledger
                .registered_for_check(&name)
                .expect("registration lends its exact record"),
        );
        assert_eq!(
            ledger.snapshot(),
            registered_snapshot,
            "dropping the borrowed capability leaves registration and indexes intact",
        );
        let handle = ledger
            .registered_for_check(&name)
            .expect("a dropped borrow leaves the registration available");

        let duplicate = FQSymbol {
            module: ModuleFullPath::from("z"),
            symbol: Symbol::from("callee"),
        };
        let first = FQSymbol {
            module: ModuleFullPath::from("a"),
            symbol: Symbol::from("callee"),
        };
        handle.finish(
            checked_ast(span),
            vec![duplicate.clone(), first.clone(), duplicate],
        );
        assert_eq!(
            *ledger.checked_for_publication(&name).unwrap().callees,
            vec![
                first,
                FQSymbol {
                    module: ModuleFullPath::from("z"),
                    symbol: Symbol::from("callee"),
                }
            ]
        );
        let mut published = ledger.into_checked().unwrap();
        let consumed = published.pop().expect("whole-ledger drain owns the body");
        assert_eq!(consumed.registration.publication_name, name);
        assert!(published.is_empty());

        let mut incomplete = BodyLedger::default();
        incomplete
            .register(registered(
                BodyTarget::Direct(Symbol::from("unchecked")),
                "unchecked",
                span,
            ))
            .unwrap();
        let error = incomplete.into_checked().unwrap_err();
        assert!(
            matches!(&error, CranelispError::CodegenError { .. }),
            "the final drain reports, rather than omits, an indexed registered record",
        );
        assert!(error.to_string().contains("registered body `unchecked`"));
    }

    // spec: design/typecheck/checked-body-publication.md §3–§4;
    //   tests/plan/s121-test-plan.md §3.8 LC-1.
    #[test]
    fn ledger_rejects_duplicate_direct_targets_but_accepts_distinct_clauses() {
        let mut ledger = BodyLedger::default();
        let name = Symbol::from("f");
        ledger
            .register(registered(
                BodyTarget::Direct(name.clone()),
                "f",
                Span::new(0, 5),
            ))
            .unwrap();
        let error = ledger
            .register(registered(
                BodyTarget::Direct(name.clone()),
                "f",
                Span::new(6, 11),
            ))
            .unwrap_err();
        assert!(error.to_string().contains("illegal redefinition of `f`"));
        assert!(ledger.registration_for_publication(&name).is_some());

        let mut clauses = BodyLedger::default();
        for clause in 0..2 {
            clauses
                .register(registered(
                    BodyTarget::MultiSignatureClause {
                        group: name.clone(),
                        clause,
                    },
                    &format!("f__v{clause}"),
                    Span::new((clause * 10) as u32, (clause * 10 + 5) as u32),
                ))
                .unwrap();
        }
        let before = clauses.snapshot();
        let collision = clauses
            .rekey_publication(&Symbol::from("f__v0"), Symbol::from("f__v1"))
            .unwrap_err();
        assert!(collision.to_string().contains("already has an owner"));
        assert_eq!(clauses.snapshot(), before);

        let before = clauses.snapshot();
        let same_publication = clauses
            .register(registered(
                BodyTarget::MultiSignatureClause {
                    group: Symbol::from("g"),
                    clause: 0,
                },
                "f__v0",
                Span::new(30, 35),
            ))
            .unwrap_err();
        assert!(
            same_publication
                .to_string()
                .contains("illegal redefinition of `f__v0`")
        );
        assert_eq!(clauses.snapshot(), before);
    }
}
