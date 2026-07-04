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

/// The scalars-only `Copy` predicate (§2.2), memoized over [`ConcreteType`].
///
/// **Increment I is exactly `{Int, Bool, Float}`** — the representation clause
/// of the full predicate (all-fields-`Copy` ∧ value-representation) fails for
/// every heap type until R5 value-flattening lands (spine §6.3). The memo
/// carrier is here now so that when R5 adds the ADT/Vec recursion the
/// classifier stays a single memoized function (deterministic ⇒ cache-key-safe).
#[derive(Default)]
pub(crate) struct CopyClassifier {
    memo: RefCell<HashMap<ConcreteType, bool>>,
}

impl CopyClassifier {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// `true` iff `ty` is `Copy` (increment I: a scalar).
    pub(crate) fn is_copy(&self, ty: &ConcreteType) -> bool {
        if let Some(v) = self.memo.borrow().get(ty) {
            return *v;
        }
        let v = matches!(ty, ConcreteType::Int | ConcreteType::Bool | ConcreteType::Float);
        self.memo.borrow_mut().insert(ty.clone(), v);
        v
    }
}

#[cfg(test)]
mod tests;
