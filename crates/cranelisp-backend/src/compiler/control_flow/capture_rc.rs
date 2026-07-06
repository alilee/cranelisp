// Capture-RC-inc: the single source for the "closure env gains its own
// reference" rule applied when a heap-typed value is stored into a closure
// environment (lambda captures, par-bind continuation captures, auto-curry
// captures).
//
// This dedups the heap-category match that, given a `HeapCategory` and a
// `Value`, emits `emit_rc_inc` / `emit_rc_inc_guarded` / nothing. It was
// previously open-coded at five sites across this module (P7 — single source
// of truth; the "duplicate heap classification" pattern the sketch audits
// flag).

use cranelift::prelude::*;
use cranelift_module::Module;

use crate::heap::{self, HeapCategory};

use super::FnCompiler;

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Emit the capture-inc for a heap category onto `self.builder`.
    ///
    /// Single source for the "closure env gains its own reference" rule:
    /// `AlwaysHeap` → `emit_rc_inc`, `Mixed` → `emit_rc_inc_guarded`,
    /// `NeverHeap` → nothing.
    pub(crate) fn emit_capture_inc(&mut self, category: HeapCategory, val: Value) {
        match category {
            HeapCategory::AlwaysHeap => heap::emit_rc_inc(&mut self.builder, self.module, val),
            HeapCategory::Mixed => heap::emit_rc_inc_guarded(&mut self.builder, self.module, val),
            HeapCategory::NeverHeap | HeapCategory::Value => {}
        }
    }
}

/// Borrowed-builder form for wrapper-context emission (the auto-curry wrapper
/// body builds in a separate Cranelift context, not `self.builder`).
///
/// `module` is threaded for the S99 RC-op instrumentation gate (see
/// `heap::emit_rc_inc`); it is inert with the gate off.
pub(crate) fn emit_capture_inc_into<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    category: HeapCategory,
    val: Value,
) {
    match category {
        HeapCategory::AlwaysHeap => heap::emit_rc_inc(builder, module, val),
        HeapCategory::Mixed => heap::emit_rc_inc_guarded(builder, module, val),
        HeapCategory::NeverHeap | HeapCategory::Value => {}
    }
}
