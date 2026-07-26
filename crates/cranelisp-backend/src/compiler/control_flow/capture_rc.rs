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

/// How ONE capture slot is released when the enclosing closure env's drop glue
/// runs — the DEC mirror of [`emit_capture_inc_into`]'s category match.
///
/// The pure DECISION, separated from the resolved carrier below so the whole
/// rule stays unit-testable without a live `FnCompiler`.
///
/// The heap CATEGORY alone is not enough (FIXME 0749): it says whether a slot
/// holds a heap pointer, not how that pointee's own owned references are
/// released. A capture that is itself a CLOSURE box owns its captures, and only
/// the pointer the allocating site embedded in the box knows how to release
/// them — a bare `emit_rc_dec(.., None)` frees the box and strands everything
/// under it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum CaptureReleaseKind {
    /// An ordinary owning slot: release through the slot TYPE's canonical drop
    /// glue, which reaches whatever that type owns at any nesting depth.
    Glue,
    /// A closure box: release through its embedded `DROP_GLUE_PTR`. The capture
    /// tuple is closure-INSTANCE shape rather than a language type, so it has
    /// no type-keyed glue and keeps its runtime dispatch (§1.1 M5).
    ClosureBox,
}

impl CaptureReleaseKind {
    /// The ONE classification rule for a capture slot, and simultaneously the
    /// "is this slot in the dec set at all" filter — `None` for a slot that can
    /// never hold a heap pointer (both capture drop-glue builders used to
    /// open-code that `filter_map` themselves).
    ///
    /// `is_fn_type` is the caller's answer to "is this capture's type a function
    /// type": the two mirrors hold different type representations (`Type` in the
    /// lambda mirror, `ConcreteType` in the auto-curry mirror), so they answer
    /// that one question and this fn owns the rule. The auto-curry target slot
    /// passes `true` unconditionally — it is a closure by construction.
    pub(crate) fn classify(category: HeapCategory, is_fn_type: bool) -> Option<Self> {
        match category {
            HeapCategory::NeverHeap | HeapCategory::Value => None,
            // A `Fn`-typed value is ALWAYS a heap closure box, so the embedded
            // glue is always the right release and no nullary guard applies.
            _ if is_fn_type => Some(CaptureReleaseKind::ClosureBox),
            HeapCategory::AlwaysHeap | HeapCategory::Mixed => Some(CaptureReleaseKind::Glue),
        }
    }
}

/// A capture slot's RESOLVED release (S118 slice S4, design §7.4).
///
/// The `Glue` arm carries the canonical `FuncId` because the glue BODY is built
/// in a separate Cranelift context and cannot reach the enclosing
/// `FnCompiler`'s registry: the enclosing compiler requests the slot type's
/// glue BEFORE the body's builder is created, and the body just emits the call.
///
/// This is what replaces the former `Plain(HeapCategory)` arm's bare
/// `emit_rc_dec(.., None)` — a dec + dealloc that freed the slot's own box and
/// stranded everything under it, which is FIXME 0760's whole shape (a captured
/// Vec-of-Strings, a captured ADT with a String field). It also folds 0796 by
/// construction: user-written and compiler-synthesised closures reach this same
/// seam and differ only in who supplies the capture list.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum CaptureRelease {
    /// Call the slot type's canonical drop glue.
    Glue(cranelift_module::FuncId),
    /// Release through the closure box's embedded `DROP_GLUE_PTR`.
    ClosureBox,
}

/// Emit the capture-DEC for one slot into a borrowed builder (the capture
/// drop-glue bodies build in a separate Cranelift context).
pub(crate) fn emit_capture_dec_into<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    release: CaptureRelease,
    val: Value,
    dealloc_id: cranelift_module::FuncId,
) {
    match release {
        CaptureRelease::ClosureBox => {
            crate::compiler::rc_emission::emit_closure_dec_into(builder, module, val, dealloc_id);
        }
        CaptureRelease::Glue(glue_id) => {
            let glue_ref = module.declare_func_in_func(glue_id, builder.func);
            builder.ins().call(glue_ref, &[val]);
        }
    }
}

#[cfg(test)]
mod tests {
    //! FIXME 0749 mechanism (b) — the capture-release classification.
    //!
    //! The bug lived exactly here: the two capture drop-glue builders described
    //! a slot by its `HeapCategory` alone, and `AlwaysHeap` lowered to a bare
    //! `emit_rc_dec(.., None)` — a dec + dealloc that never runs the pointee's
    //! own drop glue. For a capture that is itself a CLOSURE box that strands
    //! everything the target closure captured, the moment the enclosing env is
    //! the last owner. Measured on `(defn mk [] (let [s "hello"] (let [g (fn
    //! [a b] … (str-len s))] (g 1))))` + `((mk) 2)`, 100 iterations: allocs=301
    //! deallocs=201 with the bare dec, allocs=301 deallocs=301 through the
    //! embedded glue.

    use super::CaptureReleaseKind;
    use crate::heap::HeapCategory;

    // spec: design/backend/s115-carrier-and-rc-sweep.md §3 / FIXME 0749 — a
    // `Fn`-typed capture is a closure box and is released through its EMBEDDED
    // drop glue, whatever its heap category says.
    #[test]
    fn a_fn_typed_capture_releases_through_its_embedded_glue() {
        assert_eq!(
            CaptureReleaseKind::classify(HeapCategory::AlwaysHeap, true),
            Some(CaptureReleaseKind::ClosureBox)
        );
        // ...including via a `Mixed` classification: a closure is never a bare
        // nullary tag, so the guarded form would be wrong as well as stranding.
        assert_eq!(
            CaptureReleaseKind::classify(HeapCategory::Mixed, true),
            Some(CaptureReleaseKind::ClosureBox)
        );
    }

    // spec: §3 (NEGATIVE / byte-identical fence) — every non-`Fn` capture keeps
    // the exact release it had before, so the corpus is emission-identical
    // except at closure-typed slots.
    #[test]
    fn non_fn_captures_keep_their_plain_release_neg() {
        assert_eq!(
            CaptureReleaseKind::classify(HeapCategory::AlwaysHeap, false),
            Some(CaptureReleaseKind::Glue)
        );
        assert_eq!(
            CaptureReleaseKind::classify(HeapCategory::Mixed, false),
            Some(CaptureReleaseKind::Glue)
        );
    }

    // spec: appendix-c-nfr §C.1.4 / FIXME 0760 (S118 slice S4) — **every owning
    // capture descriptor gets a GLUE call**. This is the assertion 0760 recorded
    // that no instrument ever made: the classification is a closed sum with two
    // arms, and both are glue (the slot type's canonical body, or the closure
    // box's embedded pointer). There is no bare-dec disposition left for a
    // classifier to reach, which is what makes the stranding shape
    // unrepresentable rather than merely fixed.
    #[test]
    fn every_owning_capture_kind_resolves_to_a_glue_call() {
        for category in [HeapCategory::AlwaysHeap, HeapCategory::Mixed] {
            for is_fn in [false, true] {
                let kind = CaptureReleaseKind::classify(category, is_fn)
                    .expect("an owning slot is in the dec set");
                // Exhaustive over the sum: adding a non-glue arm is a compile
                // error here, never a silent bare dec.
                match kind {
                    CaptureReleaseKind::Glue | CaptureReleaseKind::ClosureBox => {}
                }
            }
        }
    }

    // spec: appendix-c-nfr §C.1.4 (NEGATIVE, structural) / FIXME 0760 — the
    // capture-dec emitter must not reach a bare `rc_dec`. That call is exactly
    // what stranded a captured Vec's elements and a captured ADT's String
    // field: it freed the slot's own box and nothing under it.
    #[test]
    fn the_capture_dec_emitter_has_no_bare_dec_path_neg() {
        let source = include_str!("capture_rc.rs");
        let start = source
            .find("pub(crate) fn emit_capture_dec_into")
            .expect("the capture-dec emitter must exist");
        let end = source[start..]
            .find("\n#[cfg(test)]")
            .map(|o| start + o)
            .unwrap_or(source.len());
        let body = &source[start..end];
        assert!(
            !body.contains(concat!("emit_rc_", "dec")),
            "the capture-dec emitter regained a bare dec path:\n{body}"
        );
    }

    // spec: §3 — `classify` is also the dec-set MEMBERSHIP filter (the one both
    // builders used to open-code). A slot that can never hold a heap pointer is
    // not in the glue at all — and `is_fn_type` cannot smuggle one in.
    #[test]
    fn non_heap_slots_are_not_in_the_dec_set_neg() {
        assert_eq!(
            CaptureReleaseKind::classify(HeapCategory::NeverHeap, false),
            None
        );
        assert_eq!(
            CaptureReleaseKind::classify(HeapCategory::Value, false),
            None
        );
        assert_eq!(
            CaptureReleaseKind::classify(HeapCategory::NeverHeap, true),
            None
        );
        assert_eq!(
            CaptureReleaseKind::classify(HeapCategory::Value, true),
            None
        );
    }
}
