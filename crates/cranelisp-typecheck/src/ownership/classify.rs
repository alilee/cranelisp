//! CS-1 — the static-call classifier, the `Copy` predicate, and leaf-fact
//! reads (`design/typecheck/ownership-inference.md` §2.1/§2.2, §13.2 CS-1).
//!
//! Pure, table-free, write-free. Everything here is a function over an
//! [`Apply`](cranelisp_types::MonoExpr::Apply) shape (its `resolved_call` + its
//! callee node) plus a caller-supplied name→kind resolver — no fixpoint, no
//! symbol-table mutation. The real pass supplies a resolver that chain-follows
//! through [`TypeCheckEnv`](crate::checker::TypeCheckEnv); unit tests supply a
//! `HashMap`-backed closure.
//!
//! # The §2.1 classification (Principle 19 — no module privileged by name)
//!
//! A call site is classified from its `resolved_call` first, falling back to a
//! chain-follow of the callee `Var`'s terminal [`DefKind`](cranelisp_types::DefKind)
//! for the `resolved_call == None` case. The classifier reads
//! [`PrimitiveBody`](cranelisp_types::PrimitiveBody) representationally
//! (inline vs extern) — it never matches a primitive by name (0476).

use std::cell::RefCell;
use std::collections::HashMap;

use cranelisp_types::{ConcreteType, MonoExpr, ResolvedCall, Symbol};

/// The terminal callable kind a callee `Var` chain-resolves to — the
/// discriminator the `resolved_call == None` row of the §2.1 table needs.
///
/// Produced by the caller-supplied resolver (real pass: a chain-follow +
/// `DefKind` read; tests: a lookup table). A name that resolves to a local
/// `let`/param binding (a closure value) or does not resolve at all is
/// **not** one of these — the resolver returns `None`, which the classifier
/// maps to [`CallClass::Decision24`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TerminalKind {
    /// A concrete user function (incl. a monomorphised instance) — a
    /// statically-resolved moded call target (§2.1 row 1/4).
    UserFnConcrete,
    /// A declared-leaf primitive — inline-lowered or extern-shimmed. Its facts
    /// come from the §9 hand-declared table (its entry's `mode_summary`), never
    /// from a summary walk (§2.1 row 3; §9.3).
    DeclaredLeaf,
    /// A constructor or platform effect — a **pinned Decision-24 boundary**
    /// (§2.1 row 4 tail; spine §3.1 boundary pins). Mode vectors never attach.
    PinnedBoundary,
}

/// The classification verdict for one `Apply` site (§2.1).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CallClass {
    /// A statically-resolved moded call **or** a declared-leaf primitive:
    /// consult the callee summary looked up under `name` (the mangled
    /// `JitSymbol` for `SigDispatch`/`TraitMethod`, the bare name for
    /// `BuiltinFn` and the chain-resolved `Var`). An absent summary reads as
    /// ⊤ (Decision-24) through the [`ModeSummary`](cranelisp_types::ModeSummary)
    /// accessors — never indexed directly.
    Summarised(Symbol),
    /// A **Decision-24 site**: closure-valued callee, auto-curry partial,
    /// non-`Var` (computed) callee, or a pinned boundary (constructor /
    /// platform effect). Every heap argument joins `Owned`+`Retained`+escape
    /// (spine §2.2 rule 5).
    Decision24,
}

/// Classify an `Apply` per the §2.1 table.
///
/// `resolve_callee` maps a callee `Var`'s bare name to its terminal
/// [`TerminalKind`] — consulted **only** for the `resolved_call == None` row.
/// Returning `None` (a local closure binding, an unresolved name) yields
/// [`CallClass::Decision24`].
pub(crate) fn classify_call(
    resolved_call: Option<&ResolvedCall>,
    callee: &MonoExpr,
    resolve_callee: impl Fn(&Symbol) -> Option<TerminalKind>,
) -> CallClass {
    match resolved_call {
        // Row 1/2: mangled mono / multi-sig / post-mono trait-impl target —
        // a named, statically-resolved moded body.
        Some(ResolvedCall::SigDispatch { mangled_name }) => {
            CallClass::Summarised(Symbol::from(mangled_name.as_ref()))
        }
        Some(ResolvedCall::TraitMethod { mangled_name, .. }) => {
            CallClass::Summarised(Symbol::from(mangled_name.as_ref()))
        }
        // Row 3: inline-lowered builtin — declared leaf, facts from §9.
        Some(ResolvedCall::BuiltinFn { name }) => CallClass::Summarised(name.clone()),
        // Auto-curry partial application is a closure value by construction.
        Some(ResolvedCall::AutoCurry { .. }) => CallClass::Decision24,
        // `ResolvedCall` is `#[non_exhaustive]`: a future variant is treated
        // conservatively as a Decision-24 site (monotone-sound).
        Some(_) => CallClass::Decision24,
        // Row 4/5/6: unresolved-at-node — decide by the callee shape.
        None => match callee {
            MonoExpr::Var { name, .. } => match resolve_callee(name) {
                Some(TerminalKind::UserFnConcrete) | Some(TerminalKind::DeclaredLeaf) => {
                    CallClass::Summarised(name.clone())
                }
                // Constructor / platform effect stay Decision-24 at the ABI;
                // a closure-valued binding or an unresolved name likewise.
                Some(TerminalKind::PinnedBoundary) | None => CallClass::Decision24,
            },
            // A computed (non-`Var`) callee is a closure value.
            _ => CallClass::Decision24,
        },
    }
}

/// The `Copy`/value predicate (§2.2, §14.5), memoized over [`ConcreteType`].
///
/// **The R5 delegation (CS-II-3).** A type sits at `Copy` iff the single-sourced
/// [`value_layout`](cranelisp_types::value_layout) predicate returns `Some` —
/// the soundness-coupled carrier both this classifier and the backend's
/// `HeapCategory::Value` arm consume (spine §6.3; §14.5). The classifier
/// **delegates**, never re-implements: a `Copy`-moded param the backend did not
/// flatten is a missing-`rc_inc` use-after-free, so two independent copies of the
/// predicate is the Principle-7 mirror-defect class. This is a **value change**
/// (which `ConcreteType`s classify `Copy`), not a shape change — deterministic
/// (post-mono ⇒ total), hence cache-key-safe.
///
/// Behaviour is controlled by the *inputs* to `value_layout`, not by a separate
/// code path: passing **no** type-defs (`None`) admits only `{Int, Bool, Float}`
/// (an ADT with no reachable def is ineligible) — the scalars-only classifier;
/// passing the session's type tables (`Some(env.modules())`) additionally admits
/// the value-flattenable single-scalar products `value_layout` proves eligible
/// (`(Cell Int)`-style). The classifier holds an erased predicate closure so it
/// carries no `C`/`L` generics into the transfer/fixpoint seams.
///
/// **Landing discipline (§14.5 — `Copy` is scalars-only until R5/B3).**
/// Production currently supplies the **`None` (scalars-only)** predicate. The
/// backend already consumes `Mode::Copy` (it drops RC and treats the value
/// by-value) but does NOT yet flatten value-eligible ADTs (that is R5/Block B3,
/// backend `HeapCategory::Value`; the reuse/R5 witnesses are still RED).
/// Admitting a heap ADT to `Copy` before the backend flattens it is a
/// missing-`rc_inc` use-after-free — so the input stays `None` until B3, which
/// flips it to `Some(env.modules())` in the SAME change-set that lands the
/// flattening. The delegation *mechanism* is the increment-II step; the tables
/// *input* is the coupled B3 step (both surfaces grow precision together).
pub(crate) struct CopyClassifier<'a> {
    memo: RefCell<HashMap<ConcreteType, bool>>,
    /// The value-layout predicate: `true` iff `ty` is value-representable
    /// (`value_layout(ty, type_defs).is_some()`). Erased so the classifier is
    /// generic-free; the closure captures the concrete `C`/`L` at the call site.
    is_value: Box<dyn Fn(&ConcreteType) -> bool + 'a>,
}

impl<'a> CopyClassifier<'a> {
    /// Construct from an explicit value-layout predicate. Production supplies
    /// `|ty| value_layout::<C, L>(ty, None).is_some()` (the delegation, tables
    /// withheld until B3 per §14.5); tests supply a stub to exercise the seam
    /// without rebuilding the tables.
    pub(crate) fn new(is_value: impl Fn(&ConcreteType) -> bool + 'a) -> Self {
        Self {
            memo: RefCell::new(HashMap::new()),
            is_value: Box::new(is_value),
        }
    }

    /// The scalars-only classifier — `value_layout` with **no** type tables,
    /// which admits exactly `{Int, Bool, Float}` (an ADT with no reachable def is
    /// ineligible). A test convenience equivalent to what production supplies
    /// today (`new` with a `None`-tables predicate, §14.5).
    #[cfg(test)]
    pub(crate) fn scalars_only() -> Self {
        Self::new(|ty| cranelisp_types::value_layout::<(), ()>(ty, None).is_some())
    }

    /// `true` iff `ty` is `Copy` — delegates to the value-layout predicate,
    /// memoized (deterministic ⇒ cache-key-safe).
    pub(crate) fn is_copy(&self, ty: &ConcreteType) -> bool {
        if let Some(v) = self.memo.borrow().get(ty) {
            return *v;
        }
        let v = (self.is_value)(ty);
        self.memo.borrow_mut().insert(ty.clone(), v);
        v
    }
}

#[cfg(test)]
mod tests;
