//! RC / drop-glue emission: [`FnCompiler::emit_typed_rc_dec`], the ONE
//! canonical glue-call emitter every release goes through, and the closure
//! release through a box's embedded glue pointer.

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use cranelisp_types::{ConcreteType, CranelispError};

use crate::heap;

use super::FnCompiler;

/// Release a CLOSURE box through its **embedded** `DROP_GLUE_PTR` — the
/// borrowed-builder body of [`FnCompiler::emit_closure_dec_inline`].
///
/// A closure box OWNS its captures, and the only thing that knows how to
/// release them is the glue pointer the allocating site stored in the box: a
/// bare `heap::emit_rc_dec(.., None)` frees the box and STRANDS everything
/// under it. Emission: `atomic dec` → on rc→0 `fence`, load
/// `DROP_GLUE_PTR`, `call_indirect` it when non-zero, then `dealloc`.
///
/// Free-fn form because the two capture drop-glue mirrors build their bodies in
/// a SEPARATE Cranelift context, not `self.builder` (the `emit_capture_inc_into`
/// precedent). One body, two callers (Principle 7).
pub(crate) fn emit_closure_dec_into<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    closure_val: Value,
    dealloc_id: FuncId,
) {
    use crate::heap::HeapClosure;
    use cranelift_codegen::ir::AtomicRmwOp;
    use cranelisp_types::HeapHeader;

    let cont_block = builder.create_block();

    // Decrement RC.
    let rc_addr = builder
        .ins()
        .iadd_imm(closure_val, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    let old_rc = builder.ins().atomic_rmw(
        types::I64,
        MemFlags::trusted(),
        AtomicRmwOp::Sub,
        rc_addr,
        one,
    );

    // Branch: if old_rc == 1, free the closure.
    let cmp = builder.ins().icmp(IntCC::Equal, old_rc, one);
    let free_block = builder.create_block();
    builder.ins().brif(cmp, free_block, &[], cont_block, &[]);

    // Free path.
    builder.switch_to_block(free_block);
    builder.seal_block(free_block);
    builder.ins().fence();

    // Load drop_glue_ptr from the closure.
    let drop_glue_ptr = heap::heap_load(builder, closure_val, HeapClosure::DROP_GLUE_PTR_OFFSET);

    // If drop_glue_ptr != 0, call it.
    let zero = builder.ins().iconst(types::I64, 0);
    let has_glue = builder.ins().icmp(IntCC::NotEqual, drop_glue_ptr, zero);
    let glue_block = builder.create_block();
    let dealloc_block = builder.create_block();
    builder
        .ins()
        .brif(has_glue, glue_block, &[], dealloc_block, &[]);

    // Call drop glue: (closure_ptr: i64) -> ()
    builder.switch_to_block(glue_block);
    builder.seal_block(glue_block);

    let mut glue_sig = module.make_signature();
    glue_sig.params.push(AbiParam::new(types::I64));
    let glue_sig_ref = builder.import_signature(glue_sig);
    builder
        .ins()
        .call_indirect(glue_sig_ref, drop_glue_ptr, &[closure_val]);
    builder.ins().jump(dealloc_block, &[]);

    // Dealloc the closure.
    builder.switch_to_block(dealloc_block);
    builder.seal_block(dealloc_block);
    let dealloc_ref = module.declare_func_in_func(dealloc_id, builder.func);
    builder.ins().call(dealloc_ref, &[closure_val]);
    builder.ins().jump(cont_block, &[]);

    // Continue.
    builder.switch_to_block(cont_block);
    builder.seal_block(cont_block);
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// **The ONE release emitter** (S118 slice S1,
    /// `design/backend/transitive-drop-glue.md` §4): classify `ty`, and for an
    /// owned heap value emit exactly ONE `call` to the canonical
    /// per-concrete-type drop glue.
    ///
    /// What is deliberately NOT here:
    ///
    /// - **No recursive field inspection.** The body the registry emits walks
    ///   the type's own owned graph, so this seam has no depth and no cutoff.
    /// - **No `needs_guard` parameter.** The nullary-tag guard is a property of
    ///   the concrete TYPE (`GlueShape::guard_nullary`, derived from the type's
    ///   own constructor set) and lives once inside the glue body. A site
    ///   parameter is the last place a *site* could disagree with a *type* about
    ///   how a value is released, which is why removing it is part of the
    ///   migration rather than a tidy.
    /// - **No fallback arm.** The type is a [`ConcreteType`], so a release site
    ///   cannot reach this emitter without one
    ///   (`non-concrete-release-contract.md` §7.4 step 2).
    ///
    /// A non-owning representation (`NeverHeap`) is a no-op — the
    /// registry's `request_if_owning` is the single membership filter.
    pub(crate) fn emit_typed_rc_dec(
        &mut self,
        val: Value,
        ty: &ConcreteType,
    ) -> Result<(), CranelispError> {
        let Some(glue_id) =
            self.glue
                .request_if_owning(self.module, self.ctx.symbol_tables, ty.clone())?
        else {
            return Ok(());
        };
        let glue_ref = self.module.declare_func_in_func(glue_id, self.builder.func);
        self.builder.ins().call(glue_ref, &[val]);
        Ok(())
    }

    /// Emit RC dec for a closure value using its embedded drop glue pointer.
    ///
    /// Unlike `emit_rc_dec` which takes a compile-time `drop_glue_id`,
    /// this loads the drop glue pointer from the closure's embedded
    /// `DROP_GLUE_PTR_OFFSET` field at runtime and calls it if non-zero.
    ///
    /// Used for:
    /// - Closure parameters received from callers (type unknown at compile time)
    /// - Temporary closure expressions used as callees
    /// - Any closure variable where the static drop glue is not available
    pub(crate) fn emit_closure_dec_inline(&mut self, closure_val: Value, dealloc_id: FuncId) {
        emit_closure_dec_into(&mut self.builder, self.module, closure_val, dealloc_id);
    }
}

// `TypedRelease` / `typed_release_kind` (FIXME 0753's per-site teardown
// classification) are DELETED at S118 slice S1: the registry's own
// `GlueShape` classification subsumes them, and the teardown now lives inside
// the generated body rather than at the site. The load-bearing half of that
// rule — Vec is classified BEFORE ADT, because a Vec IS spelled
// `Type::ADT(Vec, [t])` but its elements live behind `DATA_PTR` — is rehomed
// onto `drop_glue::GlueShape` and pinned by
// `drop_glue::tests::a_vec_shape_is_not_classified_as_a_plain_adt`.

/// S118 slice S1 — the canonical glue-call emitter (§10 row 3).
#[cfg(test)]
mod glue_call_emitter_tests;
