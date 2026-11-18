// Vec codegen: VecLit compilation and inline vec-get/vec-set/vec-push/vec-len.
//
// compile_vec_lit: allocate a Vec via runtime/vec_new, store each element
// compile_vec_get: bounds-checked element access with RC inc for heap elements
// compile_vec_set: the guarded COW core for every uniqueness case
// compile_vec_push: COW inline + extern fallback
// compile_vec_len: inline load of len field
//
// Element inc/dec function generation for Vec copy-path externs.

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{ConcreteType, CranelispError, ErrorLocation, HeapHeader, MonoExpr, Span};

use crate::heap::{self, HeapCategory, HeapVec};

use super::FnCompiler;
use super::control_flow::emit_extern_call_in_wrapper;

/// Bundled operands for [`emit_vec_set_cow_core`], shared by the static site
/// and the §12.7 wrapper emission. The new element is an owned value the
/// vector takes.
pub(crate) struct VecSetCow {
    pub vec_val: Value,
    pub idx_val: Value,
    pub new_val: Value,
    /// Per-element-type RC inc fn pointer for the runtime copy helper's
    /// retained-element incs (iconst 0 for NeverHeap).
    pub inc_fn_ptr: Value,
    /// `runtime/panic`, called by the index guard.
    pub panic_id: cranelift_module::FuncId,
    pub source: OwnedSource,
}

/// The teardown materials for a copy-on-write operation's source, which the
/// operation always owns (`uniform-counting.md` §2, rule U2). The `rc == 1`
/// probe chooses the arm: in place, the consumed reference becomes the
/// result's; otherwise the copy is the result and the source is released.
pub(crate) struct OwnedSource {
    pub vec_drop_func_id: cranelift_module::FuncId,
    /// The element type's canonical release adapter, `None` for an element
    /// type that owns no heap. It is the one element-release source: the
    /// teardown callback below and the in-place `vec-set` arm's release of
    /// the overwritten element both come from it (`uniform-counting.md` §3.4
    /// item 5).
    pub elem_release: Option<cranelift_module::FuncId>,
    /// `elem_release` as the `runtime/vec_drop` callback (`iconst 0` for none).
    pub elem_dec_fn_ptr: Value,
}

/// `release` as a `runtime/vec_drop` element callback: its address, or the
/// ABI's null callback for an element type that owns no heap.
fn elem_release_fn_ptr<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    release: Option<cranelift_module::FuncId>,
) -> Value {
    match release {
        Some(id) => {
            let func_ref = module.declare_func_in_func(id, builder.func);
            builder.ins().func_addr(types::I64, func_ref)
        }
        None => builder.ins().iconst(types::I64, 0),
    }
}

/// Release a copy-on-write source on the copy arm, AFTER the copy extern has
/// retained the elements it shares, so a last-reference teardown cannot free
/// an element the copy still holds.
fn release_copied_source<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    vec_val: Value,
    source: &OwnedSource,
) {
    emit_vec_rc_dec_with_drop(
        builder,
        module,
        vec_val,
        source.vec_drop_func_id,
        source.elem_dec_fn_ptr,
    );
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Compile a Vec literal `node`: its elements, evaluated as its operands,
    /// stored into a fresh Vec.
    pub(crate) fn compile_vec_lit(
        &mut self,
        node: &MonoExpr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let elem_vals = self.compile_operands(node)?.values;
        self.emit_vec_lit(&elem_vals, span)
    }

    /// Allocate a Vec holding the owned `elem_vals`, which it takes.
    pub(crate) fn emit_vec_lit(
        &mut self,
        elem_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let vec_new_id = self
            .ctx
            .vec_new_func_id
            .ok_or_else(|| CranelispError::CodegenError {
                message: "runtime/vec_new not declared (need declare_intrinsics)".into(),
                location: ErrorLocation::from_span(span),
            })?;

        let len = elem_vals.len() as i64;

        // Call runtime/vec_new(len) — allocates Vec struct + data buffer with len capacity.
        let len_val = self.builder.ins().iconst(types::I64, len);
        let vec_new_ref = self
            .module
            .declare_func_in_func(vec_new_id, self.builder.func);
        let call = self.builder.ins().call(vec_new_ref, &[len_val]);
        let vec_ptr = self.builder.inst_results(call)[0];

        // Load data_ptr from the Vec struct.
        let data_ptr = heap::heap_load(&mut self.builder, vec_ptr, HeapVec::DATA_PTR_OFFSET); // data_ptr: i64 (ptr-width)

        // Store each owned element into the data buffer at data_ptr + i * 8;
        // the vector takes each element's reference.
        for (i, &val) in elem_vals.iter().enumerate() {
            heap::heap_store(&mut self.builder, val, data_ptr, (i * 8) as i32);
        }

        // Set len = number of elements.
        let len_i64 = self.builder.ins().iconst(types::I64, len);
        heap::heap_store(&mut self.builder, len_i64, vec_ptr, HeapVec::LEN_OFFSET);

        Ok(vec_ptr)
    }

    /// Compile a Vec operation inline over owned operands. Returns `Some(val)`
    /// if handled. Every operation consumes its vector: a read releases it
    /// after reading, and a copy-on-write update owns it (rule U2).
    pub(crate) fn compile_vec_op(
        &mut self,
        name: &str,
        args: &[MonoExpr],
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Option<Value>, CranelispError> {
        let arity_matches = matches!(
            (name, args.len()),
            ("vec-get", 2) | ("vec-set", 3) | ("vec-push", 2) | ("vec-len", 1)
        );
        if !arity_matches {
            return Ok(None);
        }
        let elem_type = self.vec_elem_type(&args[0]);
        let vec_val = arg_vals[0];
        let result = match name {
            "vec-len" => {
                let len = heap::heap_load(&mut self.builder, vec_val, HeapVec::LEN_OFFSET);
                self.release_vec(vec_val, &elem_type, span)?;
                len
            }
            "vec-get" => {
                let panic_id = crate::raise::declared(self.ctx.panic_func_id, span)?;
                let elem_category = self.elem_category(&elem_type, span)?;
                // The core duplicates the element before the vector is
                // released, so the element survives a last-reference teardown.
                let elem = emit_vec_get_core(
                    &mut self.builder,
                    self.module,
                    panic_id,
                    elem_category,
                    vec_val,
                    arg_vals[1],
                    span,
                )?;
                self.release_vec(vec_val, &elem_type, span)?;
                elem
            }
            "vec-set" => {
                let panic_id = crate::raise::declared(self.ctx.panic_func_id, span)?;
                let inc_fn_ptr = self.resolve_elem_inc_fn_ptr(&elem_type, span)?;
                let source = self.owned_source(&elem_type, span)?;
                emit_vec_set_cow_core(
                    &mut self.builder,
                    self.module,
                    VecSetCow {
                        vec_val,
                        idx_val: arg_vals[1],
                        new_val: arg_vals[2],
                        inc_fn_ptr,
                        panic_id,
                        source,
                    },
                    span,
                )?
            }
            _ => {
                let inc_fn_ptr = self.resolve_elem_inc_fn_ptr(&elem_type, span)?;
                let source = self.owned_source(&elem_type, span)?;
                emit_vec_push_cow_core(
                    &mut self.builder,
                    self.module,
                    vec_val,
                    arg_vals[1],
                    inc_fn_ptr,
                    source,
                    span,
                )?
            }
        };
        Ok(Some(result))
    }

    /// Release an owned vector through its rc-checked teardown.
    fn release_vec(
        &mut self,
        vec_val: Value,
        elem_type: &Option<ConcreteType>,
        span: Span,
    ) -> Result<(), CranelispError> {
        let source = self.owned_source(elem_type, span)?;
        release_copied_source(&mut self.builder, self.module, vec_val, &source);
        Ok(())
    }

    /// The teardown materials for an owned vector source.
    fn owned_source(
        &mut self,
        elem_type: &Option<ConcreteType>,
        span: Span,
    ) -> Result<OwnedSource, CranelispError> {
        let vec_drop_func_id = self.vec_drop_id(span)?;
        let elem_release = self.request_elem_dec_adapter(elem_type, span)?;
        let elem_dec_fn_ptr = elem_release_fn_ptr(&mut self.builder, self.module, elem_release);
        Ok(OwnedSource {
            vec_drop_func_id,
            elem_release,
            elem_dec_fn_ptr,
        })
    }

    fn vec_drop_id(&self, span: Span) -> Result<cranelift_module::FuncId, CranelispError> {
        self.ctx
            .vec_drop_func_id
            .ok_or_else(|| CranelispError::CodegenError {
                message: "runtime/vec_drop not declared (need declare_intrinsics)".into(),
                location: ErrorLocation::from_span(span),
            })
    }

    // --- Helpers ---

    /// Extract the element type from a Vec expression's concrete type.
    ///
    /// `pub(crate)`: also read by `control_flow::fn_as_value::compile_auto_curry`
    /// to recover the element type from the applied Vec argument on the
    /// curried-vec-query path (§12.7).
    pub(crate) fn vec_elem_type(&self, vec_expr: &MonoExpr) -> Option<ConcreteType> {
        if let ConcreteType::ADT(fqtn, args) = vec_expr.ty()
            && fqtn.name.as_ref() == "Vec"
            && args.len() == 1
        {
            return Some(args[0].clone());
        }
        None
    }

    /// Resolve or generate a per-element-type inc function pointer.
    ///
    /// Returns iconst(0) for NeverHeap types (runtime skips the call).
    /// Returns a Cranelift func_addr for AlwaysHeap and Mixed types.
    fn resolve_elem_inc_fn_ptr(
        &mut self,
        elem_type: &Option<ConcreteType>,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let category = self.elem_category(elem_type, span)?;
        match category {
            HeapCategory::NeverHeap | HeapCategory::Value => {
                Ok(self.builder.ins().iconst(types::I64, 0))
            }
            HeapCategory::AlwaysHeap => {
                let func_id = self.build_elem_inc_fn(false, span)?;
                let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
                Ok(self.builder.ins().func_addr(types::I64, func_ref))
            }
            HeapCategory::Mixed => {
                let func_id = self.build_elem_inc_fn(true, span)?;
                let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
                Ok(self.builder.ins().func_addr(types::I64, func_ref))
            }
        }
    }

    /// The element type's canonical release adapter for `runtime/vec_drop`'s
    /// `(i64) -> i64` callback ABI, keyed on the types-owned
    /// `drop_glue_symbol_name` identity; `None` for a non-owning element type.
    /// The only part that needs `&mut self` before a borrowed builder exists.
    fn request_elem_dec_adapter(
        &mut self,
        elem_type: &Option<ConcreteType>,
        span: Span,
    ) -> Result<Option<cranelift_module::FuncId>, CranelispError> {
        let Some(ty) = elem_type else {
            return Err(missing_element_type("release", span));
        };
        self.glue
            .request_vec_elem_adapter(self.module, self.ctx.symbol_tables, ty)
    }

    /// The heap category of the element type, which an element increment
    /// needs; a missing element type is a located refusal.
    fn elem_category(
        &self,
        elem_type: &Option<ConcreteType>,
        span: Span,
    ) -> Result<HeapCategory, CranelispError> {
        let Some(ty) = elem_type else {
            return Err(missing_element_type("increment", span));
        };
        Ok(self.heap_category(ty))
    }

    /// Build a standalone inc function: `(val: i64) -> i64`.
    ///
    /// If `guarded` is true, guards against bare nullary tags.
    /// Returns a cached FuncId if this function was already built.
    fn build_elem_inc_fn(
        &mut self,
        guarded: bool,
        span: Span,
    ) -> Result<cranelift_module::FuncId, CranelispError> {
        let suffix = if guarded { "mixed" } else { "heap" };
        let name = format!("runtime/vec_elem_inc_{suffix}");

        // Check if this function was already built (e.g., by a previous module).
        // declare_function is idempotent — it returns the existing FuncId if the
        // signature matches. We only need to skip define_function to avoid the
        // DuplicateDefinition error from Cranelift.
        if let Some(cranelift_module::FuncOrDataId::Func(existing_id)) = self.module.get_name(&name)
        {
            return Ok(existing_id);
        }

        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self
            .module
            .declare_function(&name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare elem inc fn: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        let mut ctx = self.module.make_context();
        let mut func_ctx = FunctionBuilderContext::new();
        ctx.func.signature = sig;

        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);

        let val = builder.block_params(entry)[0];

        emit_elem_inc_body(&mut builder, self.module, val, guarded);
        builder.finalize();

        self.module
            .define_function(func_id, &mut ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define elem inc fn: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        Ok(func_id)
    }

    /// The [`OwnedSource`] for a COW core emitted into a wrapper/curry body,
    /// whose params arrive owned (consuming-closure protocol).
    fn owned_source_into(
        &mut self,
        elem_type: &Option<ConcreteType>,
        builder: &mut FunctionBuilder,
        span: Span,
    ) -> Result<OwnedSource, CranelispError> {
        let vec_drop_func_id = self.vec_drop_id(span)?;
        let elem_release = self.request_elem_dec_adapter(elem_type, span)?;
        let elem_dec_fn_ptr = elem_release_fn_ptr(builder, self.module, elem_release);
        Ok(OwnedSource {
            vec_drop_func_id,
            elem_release,
            elem_dec_fn_ptr,
        })
    }

    fn resolve_elem_dec_fn_ptr_into(
        &mut self,
        elem_type: &Option<ConcreteType>,
        builder: &mut FunctionBuilder,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let release = self.request_elem_dec_adapter(elem_type, span)?;
        Ok(elem_release_fn_ptr(builder, self.module, release))
    }

    /// Resolve or generate a per-element-type inc function pointer into a
    /// specific builder (for wrapper-body emission — the mirror of
    /// `resolve_elem_dec_fn_ptr_into`, and the `_into` sibling of
    /// `resolve_elem_inc_fn_ptr`, which emits into `self.builder`).
    fn resolve_elem_inc_fn_ptr_into(
        &mut self,
        elem_type: &Option<ConcreteType>,
        builder: &mut FunctionBuilder,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let category = self.elem_category(elem_type, span)?;
        match category {
            HeapCategory::NeverHeap | HeapCategory::Value => {
                Ok(builder.ins().iconst(types::I64, 0))
            }
            HeapCategory::AlwaysHeap => {
                let func_id = self.build_elem_inc_fn(false, span)?;
                let func_ref = self.module.declare_func_in_func(func_id, builder.func);
                Ok(builder.ins().func_addr(types::I64, func_ref))
            }
            HeapCategory::Mixed => {
                let func_id = self.build_elem_inc_fn(true, span)?;
                let func_ref = self.module.declare_func_in_func(func_id, builder.func);
                Ok(builder.ins().func_addr(types::I64, func_ref))
            }
        }
    }

    /// Inline-emit a vec-query op (`vec-get` / `vec-set` / `vec-push`) into a
    /// GENERATED WRAPPER body (fn-as-value / auto-curry / trait-method-value —
    /// `control_flow::fn_as_value`). These primitives-table entries are
    /// `PrimitiveBody::Inline` — inline-dispatched with **no GOT slot** by
    /// construction (S102 FIXME 0476: no extern body can exist because a single
    /// monomorphic body cannot know the element's heap category), so the wrapper
    /// MUST synthesize this inline emission rather than dispatch through a slot
    /// (`design/backend/ownership-codegen.md` §12.7 — the S100 SIGSEGV defect).
    ///
    /// Every wrapper param arrives OWNED (consuming closure protocol), the same
    /// as at a static site, so the emission is the static lowering's:
    ///
    /// - `vec-get` — bounds check, element load and duplicate, then the
    ///   rc-checked release of the consumed Vec.
    /// - `vec-len` — length load, then the same release.
    /// - `vec-set` / `vec-push` — the element transfers into the Vec and the
    ///   source is owned, so the shared cores' `rc == 1` probe decides.
    ///
    /// `elem_type` is the per-site element type plumbed from the value-use
    /// site's concrete `Fn` type (or from the applied Vec argument on the
    /// auto-curry path). Element release refuses an absent type rather than
    /// treating it as a known scalar that needs no element disposer.
    pub(crate) fn emit_vec_query_into(
        &mut self,
        builder: &mut FunctionBuilder,
        name: &str,
        params: &[Value],
        elem_type: &Option<ConcreteType>,
        span: Span,
    ) -> Result<Value, CranelispError> {
        match (name, params.len()) {
            ("vec-len", 1) => {
                let vec_drop_id =
                    self.ctx
                        .vec_drop_func_id
                        .ok_or_else(|| CranelispError::CodegenError {
                            message: "runtime/vec_drop not declared".into(),
                            location: ErrorLocation::from_span(span),
                        })?;
                let dec_fn_ptr = self.resolve_elem_dec_fn_ptr_into(elem_type, builder, span)?;
                let len = heap::heap_load(builder, params[0], HeapVec::LEN_OFFSET);
                emit_vec_rc_dec_with_drop(builder, self.module, params[0], vec_drop_id, dec_fn_ptr);
                Ok(len)
            }
            ("vec-get", 2) => {
                let panic_id = crate::raise::declared(self.ctx.panic_func_id, span)?;
                let vec_drop_id =
                    self.ctx
                        .vec_drop_func_id
                        .ok_or_else(|| CranelispError::CodegenError {
                            message: "runtime/vec_drop not declared".into(),
                            location: ErrorLocation::from_span(span),
                        })?;
                let dec_fn_ptr = self.resolve_elem_dec_fn_ptr_into(elem_type, builder, span)?;
                let elem_category = self.elem_category(elem_type, span)?;
                let elem = emit_vec_get_core(
                    builder,
                    self.module,
                    panic_id,
                    elem_category,
                    params[0],
                    params[1],
                    span,
                )?;
                // Release the consumed (owned) Vec — rc-checked, and AFTER the
                // element inc inside the core, so the element survives a
                // last-reference Vec teardown.
                emit_vec_rc_dec_with_drop(builder, self.module, params[0], vec_drop_id, dec_fn_ptr);
                Ok(elem)
            }
            ("vec-set", 3) => {
                let panic_id = crate::raise::declared(self.ctx.panic_func_id, span)?;
                let inc_fn_ptr = self.resolve_elem_inc_fn_ptr_into(elem_type, builder, span)?;
                // Wrapper / curry body: params arrive OWNED (consuming-closure
                // protocol), so the copy branch must release the source Vec's
                // owned reference (§13.3 Ruling 2 — the FIXME-0474 cure). The
                // vec-get arm's release above is the precedent.
                let source = self.owned_source_into(elem_type, builder, span)?;
                emit_vec_set_cow_core(
                    builder,
                    self.module,
                    VecSetCow {
                        vec_val: params[0],
                        idx_val: params[1],
                        new_val: params[2],
                        inc_fn_ptr,
                        panic_id,
                        source,
                    },
                    span,
                )
            }
            ("vec-push", 2) => {
                let inc_fn_ptr = self.resolve_elem_inc_fn_ptr_into(elem_type, builder, span)?;
                // Wrapper / curry body: params arrive owned — release the source
                // on the copy branch (§13.3 Ruling 2).
                let source = self.owned_source_into(elem_type, builder, span)?;
                emit_vec_push_cow_core(
                    builder,
                    self.module,
                    params[0],
                    params[1],
                    inc_fn_ptr,
                    source,
                    span,
                )
            }
            _ => Err(CranelispError::CodegenError {
                message: format!(
                    "vec-query wrapper: unexpected op/arity {name}/{}",
                    params.len()
                ),
                location: ErrorLocation::from_span(span),
            }),
        }
    }
}

// ---------------------------------------------------------------------------
// Free functions
// ---------------------------------------------------------------------------

/// A Vec element operation reached with no element type: the Vec's type
/// carries no argument, which no concrete Vec type does.
fn missing_element_type(operation: &str, span: Span) -> CranelispError {
    CranelispError::CodegenError {
        message: format!(
            "Vec element {operation} reached a missing element type; canonical drop glue \
             requires a concrete type"
        ),
        location: ErrorLocation::from_span(span),
    }
}

/// The one Vec index guard (`design/backend/backend.md` §7). Loads the length;
/// an index below zero or not below the length raises the spec §12.7.2.1 panic.
/// Leaves the builder in the in-range block, so everything the caller emits
/// next is dominated by the comparison.
fn emit_vec_index_guard<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    panic_id: cranelift_module::FuncId,
    vec_val: Value,
    idx_val: Value,
    span: Span,
) -> Result<(), CranelispError> {
    let len = heap::heap_load(builder, vec_val, HeapVec::LEN_OFFSET);
    let zero = builder.ins().iconst(types::I64, 0);
    let neg_check = builder.ins().icmp(IntCC::SignedLessThan, idx_val, zero);
    let bounds_check = builder
        .ins()
        .icmp(IntCC::SignedGreaterThanOrEqual, idx_val, len);
    let out_of_bounds = builder.ins().bor(neg_check, bounds_check);

    let ok_block = builder.create_block();
    let panic_block = builder.create_block();
    builder
        .ins()
        .brif(out_of_bounds, panic_block, &[], ok_block, &[]);

    builder.switch_to_block(panic_block);
    builder.seal_block(panic_block);
    crate::raise::emit_raise(
        builder,
        module,
        panic_id,
        crate::raise::PanicSource::VecIndexOutOfBounds,
        span,
    )?;

    builder.switch_to_block(ok_block);
    builder.seal_block(ok_block);
    Ok(())
}

/// Shared emission core for `vec-get`: the index guard, element load and
/// element RC inc per `elem_category`.
///
/// Builder-parameterized (the `emit_adt_construct_into` precedent) so ONE body
/// serves both the statically-resolved inline site (`compile_vec_get`, over
/// `self.builder`) and the §12.7 fn-as-value / auto-curry wrapper bodies
/// (`emit_vec_query_into`), which build in a separate Cranelift context.
/// Consuming the Vec (the temporary/owned release) is the CALLER's decision —
/// not emitted here.
pub(crate) fn emit_vec_get_core<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    panic_id: cranelift_module::FuncId,
    elem_category: HeapCategory,
    vec_val: Value,
    idx_val: Value,
    span: Span,
) -> Result<Value, CranelispError> {
    emit_vec_index_guard(builder, module, panic_id, vec_val, idx_val, span)?;

    // Load data_ptr.
    let data_ptr = heap::heap_load(builder, vec_val, HeapVec::DATA_PTR_OFFSET);

    // Compute element address: data_ptr + idx * 8.
    let eight = builder.ins().iconst(types::I64, 8);
    let byte_offset = builder.ins().imul(idx_val, eight);
    let elem_addr = builder.ins().iadd(data_ptr, byte_offset);

    // Load element value.
    let elem = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), elem_addr, 0);

    // The projected element is duplicated: the result owns it independently of
    // the vector, which its reader then releases.
    match elem_category {
        HeapCategory::AlwaysHeap => {
            heap::emit_rc_inc(builder, module, elem);
        }
        HeapCategory::Mixed => {
            heap::emit_rc_inc_guarded(builder, module, elem);
        }
        HeapCategory::NeverHeap | HeapCategory::Value => {}
    }

    Ok(elem)
}

/// The only lowering of `vec-set`: the index guard, then the `rc == 1` probe.
/// The in-place arm releases the old element, stores the new one and returns
/// the same Vec; the copy arm calls `vec-set-copy`, which increments only the
/// retained elements, then releases the source. `vec-set-copy` has no
/// out-of-range behaviour to rely on, so the guard must dominate its call.
///
/// Builder-parameterized for the static site and the §12.7 wrapper emission.
/// The new element is owned, so both arms store it without an increment.
pub(crate) fn emit_vec_set_cow_core<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    op: VecSetCow,
    span: Span,
) -> Result<Value, CranelispError> {
    let VecSetCow {
        vec_val,
        idx_val,
        new_val,
        inc_fn_ptr,
        panic_id,
        source,
    } = op;

    emit_vec_index_guard(builder, module, panic_id, vec_val, idx_val, span)?;

    let in_place = |builder: &mut FunctionBuilder, module: &mut M| {
        emit_vec_set_in_place(
            builder,
            module,
            vec_val,
            idx_val,
            new_val,
            source.elem_release,
        )
    };
    let copy = |builder: &mut FunctionBuilder, module: &mut M| {
        emit_extern_call_in_wrapper(
            builder,
            module,
            "vec-set-copy",
            &[vec_val, idx_val, new_val, inc_fn_ptr],
            span,
        )
    };

    let rc = heap::heap_load(builder, vec_val, HeapHeader::RC_OFFSET);
    let one = builder.ins().iconst(types::I64, 1);
    let is_unique = builder.ins().icmp(IntCC::Equal, rc, one);

    let mutate_block = builder.create_block();
    let copy_block = builder.create_block();
    let merge_block = builder.create_block();
    builder.append_block_param(merge_block, types::I64);

    builder
        .ins()
        .brif(is_unique, mutate_block, &[], copy_block, &[]);

    builder.switch_to_block(mutate_block);
    builder.seal_block(mutate_block);
    in_place(builder, module);
    builder.ins().jump(merge_block, &[vec_val]);

    builder.switch_to_block(copy_block);
    builder.seal_block(copy_block);
    // Increment-II reuse tally (§6.5): the copy arm cannot reuse (rc>1) — a
    // reuse MISS. Gated on `CRANELISP_RC_STATS` (off ⇒ no emitted IR).
    heap::emit_rc_stat_call_gated(builder, module, "runtime/reuse_miss");
    let copy_result = copy(builder, module)?;
    release_copied_source(builder, module, vec_val, &source);
    builder.ins().jump(merge_block, &[copy_result]);

    builder.switch_to_block(merge_block);
    builder.seal_block(merge_block);
    Ok(builder.block_params(merge_block)[0])
}

/// The `vec-set` in-place arm: release the old element through its type's
/// canonical release and store the new one in the uniquely held buffer.
fn emit_vec_set_in_place<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    vec_val: Value,
    idx_val: Value,
    new_val: Value,
    elem_release: Option<cranelift_module::FuncId>,
) {
    // Increment-II reuse tally (§6.5): the in-place arm reuses the owned buffer
    // (a reuse HIT, taken only when the caller's runtime `rc == 1` probe
    // selected this arm).
    // Runtime tally gated on the codegen-time `CRANELISP_RC_STATS` switch (off ⇒
    // no emitted IR).
    heap::emit_rc_stat_call_gated(builder, module, "runtime/reuse_hit");

    let data_ptr = heap::heap_load(builder, vec_val, HeapVec::DATA_PTR_OFFSET);
    let eight = builder.ins().iconst(types::I64, 8);
    let byte_off = builder.ins().imul(idx_val, eight);
    let elem_addr = builder.ins().iadd(data_ptr, byte_off);
    let old_elem = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), elem_addr, 0);

    if let Some(release) = elem_release {
        let release_ref = module.declare_func_in_func(release, builder.func);
        builder.ins().call(release_ref, &[old_elem]);
    }

    builder
        .ins()
        .store(MemFlags::trusted(), new_val, elem_addr, 0);
}

/// Shared emission core for the `vec-push` COW path: rc==1 → len<cap fast
/// store / `vec-push-grow` extern; rc>1 → `vec-push-copy` extern.
///
/// Builder-parameterized single source (Principle 7) for the static site and
/// the §12.7 wrapper emission. The source and the new element are owned.
pub(crate) fn emit_vec_push_cow_core<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    vec_val: Value,
    new_val: Value,
    inc_fn_ptr: Value,
    source: OwnedSource,
    span: Span,
) -> Result<Value, CranelispError> {
    // The runtime `rc == 1` probe is the uniqueness check (rule U2).
    let rc = heap::heap_load(builder, vec_val, HeapHeader::RC_OFFSET);
    let one = builder.ins().iconst(types::I64, 1);
    let is_unique = builder.ins().icmp(IntCC::Equal, rc, one);

    let unique_block = builder.create_block();
    let copy_block = builder.create_block();
    let merge_block = builder.create_block();
    builder.append_block_param(merge_block, types::I64);

    builder
        .ins()
        .brif(is_unique, unique_block, &[], copy_block, &[]);

    // Unique path: check if len < cap.
    builder.switch_to_block(unique_block);
    builder.seal_block(unique_block);

    // Increment-II reuse tally (§6.5): the unique (rc==1) arm reuses the owned
    // Vec struct — whether the fast in-place store or the grow realloc — a reuse
    // HIT. Gated on `CRANELISP_RC_STATS` (off ⇒ no emitted IR).
    heap::emit_rc_stat_call_gated(builder, module, "runtime/reuse_hit");

    let len = heap::heap_load(builder, vec_val, HeapVec::LEN_OFFSET);
    let cap = heap::heap_load(builder, vec_val, HeapVec::CAP_OFFSET);
    let has_capacity = builder.ins().icmp(IntCC::SignedLessThan, len, cap);

    let fast_block = builder.create_block();
    let grow_block = builder.create_block();

    builder
        .ins()
        .brif(has_capacity, fast_block, &[], grow_block, &[]);

    // Fast path: store at data[len], increment len.
    builder.switch_to_block(fast_block);
    builder.seal_block(fast_block);

    let data_ptr = heap::heap_load(builder, vec_val, HeapVec::DATA_PTR_OFFSET);
    let eight = builder.ins().iconst(types::I64, 8);
    let byte_off = builder.ins().imul(len, eight);
    let elem_addr = builder.ins().iadd(data_ptr, byte_off);
    builder
        .ins()
        .store(MemFlags::trusted(), new_val, elem_addr, 0);

    // Increment len.
    let new_len = builder.ins().iadd_imm(len, 1);
    heap::heap_store(builder, new_len, vec_val, HeapVec::LEN_OFFSET);

    builder.ins().jump(merge_block, &[vec_val]);

    // Grow path: call vec-push-grow extern.
    builder.switch_to_block(grow_block);
    builder.seal_block(grow_block);
    let grow_result =
        emit_extern_call_in_wrapper(builder, module, "vec-push-grow", &[vec_val, new_val], span)?;
    builder.ins().jump(merge_block, &[grow_result]);

    // Copy path: call vec-push-copy extern.
    builder.switch_to_block(copy_block);
    builder.seal_block(copy_block);
    // Increment-II reuse tally (§6.5): the copy arm cannot reuse (rc>1) — a
    // reuse MISS. Gated on `CRANELISP_RC_STATS` (off ⇒ no emitted IR).
    heap::emit_rc_stat_call_gated(builder, module, "runtime/reuse_miss");
    let copy_result = emit_extern_call_in_wrapper(
        builder,
        module,
        "vec-push-copy",
        &[vec_val, new_val, inc_fn_ptr],
        span,
    )?;
    release_copied_source(builder, module, vec_val, &source);
    builder.ins().jump(merge_block, &[copy_result]);

    // Merge.
    builder.switch_to_block(merge_block);
    builder.seal_block(merge_block);
    Ok(builder.block_params(merge_block)[0])
}

/// Emit an RC dec on a Vec value that properly tears down the Vec on rc=0.
///
/// Unlike `heap::emit_rc_dec` (which calls `runtime/dealloc` on the Vec struct,
/// leaking the data buffer and element refs), this emits:
///
///     old_rc = atomic_rmw(Sub, vec + RC_OFFSET, 1, Release)
///     if old_rc == 1:
///         fence(Acquire)
///         vec_drop(vec, elem_dec_fn_ptr)   // dec each element + free data buffer + dealloc
///
/// `elem_dec_fn_ptr` is an i64 Value — either `func_addr` of a per-element
/// dec function (for AlwaysHeap/Mixed elements) or iconst(0) (for NeverHeap).
pub(crate) fn emit_vec_rc_dec_with_drop<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    vec_val: Value,
    vec_drop_func_id: cranelift_module::FuncId,
    elem_dec_fn_ptr: Value,
) {
    use cranelift_codegen::ir::AtomicRmwOp;

    let cont_block = builder.create_block();

    // §15 row 6 (tier-3 category-B): route the Vec-aware dec through the shared
    // `CRANELISP_RC_DEC_CHECK` seam so the DEC_CHECK lane sees the COW copy-branch
    // source release + every vec teardown/scope-exit dec — not only the header-dec
    // inline. Off by default ⇒ no emitted call ⇒ byte-identical codegen.
    crate::heap::emit_rc_dec_check_gated(builder, module, vec_val);

    // Dec RC — atomic_rmw, or the plain load/isub/store arm under the
    // `CRANELISP_NONATOMIC_RC` probe, whose pre-decrement value stands in for
    // the atomic_rmw's returned old value.
    let rc_addr = builder
        .ins()
        .iadd_imm(vec_val, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    let old_rc = if crate::heap::use_nonatomic_arm() {
        let cur = builder
            .ins()
            .load(types::I64, MemFlags::trusted(), rc_addr, 0);
        let new = builder.ins().isub(cur, one);
        builder.ins().store(MemFlags::trusted(), new, rc_addr, 0);
        cur
    } else {
        builder.ins().atomic_rmw(
            types::I64,
            MemFlags::trusted(),
            AtomicRmwOp::Sub,
            rc_addr,
            one,
        )
    };

    // Branch: if old_rc == 1 (last reference), call vec_drop.
    let cmp = builder.ins().icmp(IntCC::Equal, old_rc, one);
    let drop_block = builder.create_block();
    builder.ins().brif(cmp, drop_block, &[], cont_block, &[]);

    // Drop path: Acquire fence, then vec_drop(vec, elem_dec_fn_ptr).
    builder.switch_to_block(drop_block);
    builder.seal_block(drop_block);
    builder.ins().fence();

    let vec_drop_ref = module.declare_func_in_func(vec_drop_func_id, builder.func);
    builder
        .ins()
        .call(vec_drop_ref, &[vec_val, elem_dec_fn_ptr]);

    builder.ins().jump(cont_block, &[]);

    builder.switch_to_block(cont_block);
    builder.seal_block(cont_block);
}

/// Emit the complete `(val: i64) -> i64` Vec element-retain adapter body.
/// `build_elem_inc_fn` owns declaration and definition; this body shares the
/// canonical guarded increment with ordinary inline Vec sites.
fn emit_elem_inc_body<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    val: Value,
    guarded: bool,
) {
    if guarded {
        heap::emit_rc_inc_guarded(builder, module, val);
    } else {
        heap::emit_rc_inc(builder, module, val);
    }
    builder.ins().return_(&[val]);
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod element_release_tests;

#[cfg(test)]
mod guard_convergence_tests;

#[cfg(test)]
mod index_guard_tests;
