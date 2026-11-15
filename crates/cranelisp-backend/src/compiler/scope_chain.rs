// The lexical binding environment: one slot per BINDER, never per name.
//
// `design/backend/binding-scope.md` §2/§3.1: a binder is identified by its slot;
// a name is a *query* answered against the current lexical structure, not a key
// under which binder facts are stored. Two consequences fall out rather than
// being performed — leaving a scope removes that scope's slots and never touches
// an outer binder's facts, and two binders of one name in one frame are two
// slots. Ownership is not stored here: the ownership plan keys it by binder.

use std::collections::HashMap;

use cranelift::prelude::Variable;
use cranelisp_types::{Symbol, Type};

/// The storage facts of ONE binder.
#[derive(Debug, Clone)]
pub(crate) struct BinderSlot {
    /// The binder's name — for RESOLUTION only; it is not this slot's identity.
    name: Symbol,
    /// The binder's Cranelift variable.
    var: Variable,
    /// The binder's type, when one was recorded.
    ///
    /// `None` is load-bearing: a non-heap constructor-pattern field binding,
    /// and a parameter whose type neither the signature nor use-site inference
    /// yields, are never recorded, which keeps them out of every counting site.
    ty: Option<Type>,
}

impl BinderSlot {
    pub(crate) fn var(&self) -> Variable {
        self.var
    }

    pub(crate) fn ty(&self) -> Option<&Type> {
        self.ty.as_ref()
    }
}

/// A stack of frames; a frame is an ORDERED list of slots.
///
/// Frame `0` is the function's parameter frame; frames `1..` are `let` /
/// match / lambda-body frames.
#[derive(Debug, Default)]
pub(crate) struct ScopeChain {
    frames: Vec<Vec<BinderSlot>>,
}

impl ScopeChain {
    /// A chain with the parameter frame open.
    pub(crate) fn new() -> Self {
        ScopeChain {
            frames: vec![Vec::new()],
        }
    }

    pub(crate) fn push_frame(&mut self) {
        self.frames.push(Vec::new());
    }

    /// Drop the innermost frame and every slot it owns. An outer binder's facts
    /// were never touched, so there is nothing to restore (§2).
    pub(crate) fn pop_frame(&mut self) {
        self.frames.pop();
    }

    /// Append a slot to the innermost frame. A repeated name appends a SECOND
    /// slot; it never overwrites the first.
    pub(crate) fn bind(&mut self, name: Symbol, var: Variable, ty: Option<Type>) {
        let frame = self
            .frames
            .last_mut()
            .unwrap_or_else(|| unreachable!("invariant: the scope chain is never empty"));
        frame.push(BinderSlot { name, var, ty });
    }

    /// The binder `name` denotes here: the innermost frame's LATEST slot bearing
    /// it. `None` when no live slot binds the name.
    pub(crate) fn resolve(&self, name: &Symbol) -> Option<&BinderSlot> {
        self.frames
            .iter()
            .rev()
            .find_map(|frame| frame.iter().rev().find(|slot| &slot.name == name))
    }
}

/// The inner function's outermost environment: the names it closed over.
///
/// Captures are NOT scope frames (`binding-scope.md` §3.2). One is seeded once
/// when an inner compiler is constructed (lambda, `ParBind` continuation,
/// `Launch` continuation, dependent spark thunk); it is never released by a body
/// frame — the closure environment's drop glue owns that — and it must survive a
/// body-local binder that shadows its name. So a name resolves against the
/// [`ScopeChain`] FIRST and falls through to here only when no live slot binds
/// it; recording captures into the same map as local binder facts is what made a
/// body-local shadow of a captured name ambiguous.
#[derive(Debug, Default)]
pub(crate) struct CaptureEnv {
    entries: HashMap<Symbol, CaptureSlot>,
}

#[derive(Debug, Clone)]
pub(crate) struct CaptureSlot {
    var: Variable,
    ty: Option<Type>,
}

impl CaptureSlot {
    pub(crate) fn var(&self) -> Variable {
        self.var
    }

    pub(crate) fn ty(&self) -> Option<&Type> {
        self.ty.as_ref()
    }
}

impl CaptureEnv {
    pub(crate) fn new() -> Self {
        CaptureEnv {
            entries: HashMap::new(),
        }
    }

    pub(crate) fn insert(&mut self, name: Symbol, var: Variable, ty: Option<Type>) {
        self.entries.insert(name, CaptureSlot { var, ty });
    }

    pub(crate) fn get(&self, name: &Symbol) -> Option<&CaptureSlot> {
        self.entries.get(name)
    }
}

/// What a name denotes at a codegen site: a live binder slot, or — only when no
/// live slot binds it — a capture.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Binding<'s> {
    Slot(&'s BinderSlot),
    Capture(&'s CaptureSlot),
}

impl<'s> Binding<'s> {
    pub(crate) fn var(self) -> Variable {
        match self {
            Binding::Slot(slot) => slot.var(),
            Binding::Capture(slot) => slot.var(),
        }
    }

    pub(crate) fn ty(self) -> Option<&'s Type> {
        match self {
            Binding::Slot(slot) => slot.ty(),
            Binding::Capture(slot) => slot.ty(),
        }
    }
}

/// THE resolution rule (`binding-scope.md` §3.2): the chain answers first; the
/// capture environment answers only for a name no live slot binds. Every
/// codegen consumer of "what does name N denote here" goes through this one
/// function, so a body-local shadow of a captured name can never be ambiguous.
pub(crate) fn resolve_binding<'s>(
    chain: &'s ScopeChain,
    captures: &'s CaptureEnv,
    name: &Symbol,
) -> Option<Binding<'s>> {
    chain
        .resolve(name)
        .map(Binding::Slot)
        .or_else(|| captures.get(name).map(Binding::Capture))
}

#[cfg(test)]
mod tests;
