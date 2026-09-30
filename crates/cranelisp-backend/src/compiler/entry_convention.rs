//! The entry convention: what a callable's entry does with the heap references
//! it is handed and the reference it returns.
//!
//! It is derived once, from the keyed callable arm's lifecycle state, and it is
//! the only input every RC-action seam reads to decide a call's argument and
//! result handling: the static argument lists, the value-wrapper and auto-curry
//! adaptation, and return protection
//! (`design/backend/non-concrete-release-contract.md` §7.6). A declared `Mode`
//! or `ParamFlow` on anything but a compiled body is analysis input, never an
//! entry's convention (BC §4a invariant 8). A borrow is representable only for
//! a compiled body, so an adaptation against a declared extern mode cannot be
//! written at either seam.

use cranelisp_types::{CodeStore, Life, Mode, ModeSummary, Realization};

/// What an entry does with the heap argument at one position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ParamKind {
    /// The entry takes ownership (Decision 24).
    Consume,
    /// The entry reads the argument and leaves ownership with the caller.
    Borrow,
    /// The position carries no reference.
    NoReference,
}

/// What the caller receives from an entry's heap result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ResultKind {
    /// An owned reference whose ownership is checked where the entry is built:
    /// a body this crate compiles, or an extern shim through the primitives
    /// owned result kind. Licenses return-protect elision.
    Transferred,
    /// Owned under Decision 24 but not checked by anything this crate can see,
    /// so return protection stays.
    OwnedUnverified,
}

/// The derived convention of one callable entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EntryConvention {
    params: Params,
    result: ResultKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Params {
    ConsumeAll,
    /// A compiled body's own non-ABI-conservative summary.
    Body(ModeSummary),
}

impl EntryConvention {
    /// Derive the convention of the callable arm `life` a call site already
    /// keyed for dispatch; `None` is an entry with no table callable (a named
    /// intrinsic, an absent carrier).
    pub(crate) fn of<C: CodeStore>(life: Option<&Life<C>>) -> Self {
        use ResultKind::{OwnedUnverified, Transferred};
        let Some(life) = life else {
            return Self::consuming(OwnedUnverified);
        };
        match life {
            Life::Concrete {
                realization,
                mode_summary,
                ..
            } => match realization {
                Realization::Body { .. } => Self {
                    params: mode_summary
                        .as_ref()
                        .filter(|summary| !summary.is_abi_conservative())
                        .map_or(Params::ConsumeAll, |summary| Params::Body(summary.clone())),
                    result: Transferred,
                },
                Realization::ExternShim { .. } => Self::consuming(Transferred),
                Realization::Dll | Realization::FacadeOf { .. } => Self::consuming(OwnedUnverified),
            },
            // Static sites lower an inline arm in place and value position uses
            // the unit-local wrapper, so no entry call reaches one; consuming is
            // the conservative answer if one ever does.
            Life::Inline { .. } => Self::consuming(OwnedUnverified),
            Life::HostPromised | Life::Broken { .. } => Self::consuming(OwnedUnverified),
            // Refused before any entry call is emitted.
            Life::Template { .. } | Life::Declared { .. } => Self::consuming(OwnedUnverified),
        }
    }

    fn consuming(result: ResultKind) -> Self {
        Self {
            params: Params::ConsumeAll,
            result,
        }
    }

    /// The entry's handling of the argument at `index`.
    pub(crate) fn param(&self, index: usize) -> ParamKind {
        match &self.params {
            Params::ConsumeAll => ParamKind::Consume,
            Params::Body(summary) => match summary.param_mode(index) {
                Mode::Owned => ParamKind::Consume,
                Mode::Borrowed => ParamKind::Borrow,
                Mode::Copy => ParamKind::NoReference,
            },
        }
    }

    /// Whether every position consumes, so the plain Decision-24 argument list
    /// is exactly this convention's.
    pub(crate) fn consumes_every_param(&self) -> bool {
        matches!(self.params, Params::ConsumeAll)
    }

    /// The entry's result handling.
    pub(crate) fn result(&self) -> ResultKind {
        self.result
    }
}

#[cfg(test)]
mod tests;
