// The lexical binding environment: one slot per BINDER, never per name.
//
// `design/backend/binding-scope.md` §2/§3.1: a binder is identified by its slot;
// a name is a *query* answered against the current lexical structure, not a key
// under which binder facts are stored. Two consequences fall out rather than
// being performed — leaving a scope removes that scope's slots and never touches
// an outer binder's facts, and two binders of one name in one frame are two
// slots with two release obligations.

use std::collections::HashMap;

use cranelift::prelude::Variable;
use cranelisp_types::{Symbol, Type};

use super::fn_compiler::BorrowRoot;

/// The complete fact set of ONE binder.
///
/// The five `FnCompiler` maps this replaces (`variables`, `variable_types`,
/// `borrowed_stack`, `field_borrow_root`, `scope_stack`) were each keyed by
/// `Symbol`, so two binders of one name collided in all of them
/// (`binding-scope.md` §1, the `binder-name-underkey` class).
#[derive(Debug, Clone)]
pub(crate) struct BinderSlot {
    /// The binder's name — for RESOLUTION only; it is not this slot's identity.
    name: Symbol,
    /// The binder's Cranelift variable.
    var: Variable,
    /// The binder's type, when one was recorded.
    ///
    /// `None` is load-bearing and mirrors the pre-repair absence of a
    /// `variable_types` entry: a non-heap constructor-pattern field binding, and
    /// a parameter whose type neither the signature nor use-site inference
    /// yields, were never recorded. `apply.rs`'s owned-binding gate keys on that
    /// exact presence, so collapsing it to a real type would change emission.
    ty: Option<Type>,
    /// Does this binder BORROW (the owner releases it, not this frame)?
    borrowed: bool,
    /// Whose reference a borrowed view rides on, when it is a tracked one.
    borrow_root: Option<BorrowRoot>,
}

impl BinderSlot {
    pub(crate) fn name(&self) -> &Symbol {
        &self.name
    }

    pub(crate) fn var(&self) -> Variable {
        self.var
    }

    pub(crate) fn ty(&self) -> Option<&Type> {
        self.ty.as_ref()
    }

    pub(crate) fn is_borrowed(&self) -> bool {
        self.borrowed
    }

    pub(crate) fn borrow_root(&self) -> Option<&BorrowRoot> {
        self.borrow_root.as_ref()
    }
}

/// A reference to ONE slot in the chain: the frame it lives in and its position
/// within that frame's ordered slot list.
///
/// This is what makes the return-value skip a *binder* reference rather than a
/// name (`binding-scope.md` §4). `(let [s (str-concat "h" "e") s (str-len s)] s)`
/// has two slots named `s`; a name-keyed skip suppresses BOTH releases and the
/// displaced String leaks.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct SlotRef {
    frame: usize,
    index: usize,
}

/// A stack of frames; a frame is an ORDERED list of slots.
///
/// Frame `0` is the function's parameter frame (the TCO loop header reuses its
/// slots); frames `1..` are `let` / match / lambda-body frames.
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

    pub(crate) fn frame_count(&self) -> usize {
        self.frames.len()
    }

    /// Append a slot to the innermost frame. A repeated name appends a SECOND
    /// slot; it never overwrites the first.
    pub(crate) fn bind(&mut self, name: Symbol, var: Variable, ty: Option<Type>) {
        let frame = self
            .frames
            .last_mut()
            .unwrap_or_else(|| unreachable!("invariant: the scope chain is never empty"));
        frame.push(BinderSlot {
            name,
            var,
            ty,
            borrowed: false,
            borrow_root: None,
        });
    }

    /// The binder `name` denotes here: the innermost frame's LATEST slot bearing
    /// it. `None` when no live slot binds the name.
    pub(crate) fn resolve(&self, name: &Symbol) -> Option<&BinderSlot> {
        self.resolve_indexed(name).map(|(_, slot)| slot)
    }

    /// [`Self::resolve`] plus the index of the frame the slot lives in.
    pub(crate) fn resolve_indexed(&self, name: &Symbol) -> Option<(usize, &BinderSlot)> {
        self.frames.iter().enumerate().rev().find_map(|(i, frame)| {
            frame
                .iter()
                .rev()
                .find(|slot| &slot.name == name)
                .map(|slot| (i, slot))
        })
    }

    /// A reference to the binder `name` denotes **in the innermost frame only**,
    /// or `None` when that frame does not bind it.
    pub(crate) fn resolve_ref_in_innermost_frame(&self, name: &Symbol) -> Option<SlotRef> {
        let frame = self.frames.len().checked_sub(1)?;
        self.frames[frame]
            .iter()
            .rposition(|slot| &slot.name == name)
            .map(|index| SlotRef { frame, index })
    }

    /// The exact live slot `name` denotes, across every scope frame. Captures
    /// intentionally have no slot, so this cannot manufacture a local owner
    /// for a captured or unresolved name.
    pub(crate) fn resolve_slot_ref(&self, name: &Symbol) -> Option<SlotRef> {
        self.frames
            .iter()
            .enumerate()
            .rev()
            .find_map(|(frame, slots)| {
                slots
                    .iter()
                    .rposition(|slot| &slot.name == name)
                    .map(|index| SlotRef { frame, index })
            })
    }

    pub(crate) fn slot(&self, at: SlotRef) -> Option<&BinderSlot> {
        self.frames.get(at.frame)?.get(at.index)
    }

    /// A reference to the slot at `index` in frame `frame`, if it exists.
    pub(crate) fn slot_ref(&self, frame: usize, index: usize) -> Option<SlotRef> {
        self.frames.get(frame)?.get(index)?;
        Some(SlotRef { frame, index })
    }

    /// The innermost frame's binder NAMES, for the two pure predicates that
    /// still answer a name question over one frame
    /// (`return_cow_source_in_scope`).
    pub(crate) fn innermost_frame_names(&self) -> Vec<Symbol> {
        self.innermost_frame()
            .iter()
            .map(|slot| slot.name.clone())
            .collect()
    }

    fn resolve_mut(&mut self, name: &Symbol) -> Option<&mut BinderSlot> {
        self.frames
            .iter_mut()
            .rev()
            .find_map(|frame| frame.iter_mut().rev().find(|slot| &slot.name == name))
    }

    /// Mark the binder `name` currently denotes as borrowed. Every caller marks
    /// a binder it has just bound, so this reaches that slot and no other.
    pub(crate) fn mark_borrowed(&mut self, name: &Symbol) {
        if let Some(slot) = self.resolve_mut(name) {
            slot.borrowed = true;
        }
    }

    pub(crate) fn set_borrow_root(&mut self, name: &Symbol, root: BorrowRoot) {
        if let Some(slot) = self.resolve_mut(name) {
            slot.borrow_root = Some(root);
        }
    }

    pub(crate) fn is_borrowed(&self, name: &Symbol) -> bool {
        self.resolve(name).is_some_and(BinderSlot::is_borrowed)
    }

    pub(crate) fn frame(&self, index: usize) -> &[BinderSlot] {
        self.frames.get(index).map_or(&[], Vec::as_slice)
    }

    /// The innermost frame's slots.
    pub(crate) fn innermost_frame(&self) -> &[BinderSlot] {
        self.frames.last().map_or(&[], Vec::as_slice)
    }

    /// Does any `let`/match/lambda frame (`1..`) bind `name`?
    pub(crate) fn let_frames_bind(&self, name: &Symbol) -> bool {
        self.frames
            .iter()
            .skip(1)
            .any(|frame| frame.iter().any(|slot| &slot.name == name))
    }

    /// Does the parameter frame (`0`) bind `name`?
    pub(crate) fn param_frame_binds(&self, name: &Symbol) -> bool {
        self.frame(0).iter().any(|slot| &slot.name == name)
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
