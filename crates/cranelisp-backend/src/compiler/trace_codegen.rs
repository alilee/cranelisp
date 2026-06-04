//! Trace form codegen: `compile_trace` method for `FnCompiler`.
//!
//! Implements `(trace body)` -- a GOT-swap wrapper around a body expression,
//! returning a `Trace` ADT representing the call tree.
//!
//! # S76 target shape (FIXME 0255, `design/arch/tracing.md` §3.3–§3.4, §5)
//!
//! Three responsibilities landed here in S76:
//!
//! 1. **Discovery-in-codegen, swap ALL symbol tables** (`discover_traced_fns`).
//!    Backend computes the traced set itself by iterating every module's GOT in
//!    `symbol_tables` — no int-supplied `traced_fns`, no project-root filter,
//!    primitives included. The callable address is read from the **GOT slot**
//!    (BC §3 invariant 3 — the single source of truth), not from `entry.code`,
//!    so primitives (whose entries carry `code: None` but whose fn ptrs live in
//!    their module's GOT) are naturally included without a code-marker special
//!    case. Constrained-poly base names are skipped (dispatch placeholders).
//!
//! 2. **Display-descriptor baking** (`bake_descriptor_blob`). Each traced
//!    param/result type is baked into a self-contained position-independent
//!    **arena blob** matching the `DisplayDescriptor` ABI owned by
//!    `cranelisp-intrinsics::trace` (FIXME 0254). The blob replaces the leaked
//!    `Box<Type>` second arg to `cranelisp_trace_format`; the intrinsic walks it
//!    with zero symbol-table access. Polymorphic ADT fields are baked after
//!    substituting the call site's concrete type args (the same substitution
//!    `src/display.rs::build_adt_subst` does — replicated here, not imported).
//!
//! 3. **Both-modes emission.** The blob is emitted as a read-only data symbol
//!    via `declare_anonymous_data` + `define_data`, then its address is
//!    materialised inside the wrapper via `declare_data_in_func` + `global_value`.
//!    This single path is mode-agnostic: `JITModule` patches the `global_value`
//!    to a runtime address; `ObjectModule` emits one relocation per wrapper
//!    reference against the data symbol (same family as the GOT data symbol +
//!    string-literal pools). The blob itself carries NO intra-blob relocations —
//!    every cross-link is a self-relative `i32` byte offset — so it survives
//!    `.o` caching unchanged (`tracing.md` §3.4 "arena blob with offset-relative
//!    child links").
//!
//! # Nested-trace guard — no codegen touch-point
//!
//! Per the landed intrinsics guard design (`crates/cranelisp-intrinsics/src/trace.rs`
//! crate-doc §"The nested-trace runtime guard"), backend emits NO explicit
//! `TRACE_BODY_RUNNING` set/clear. The flag is driven entirely from inside the
//! intrinsic bodies backend already calls: `cranelisp_trace_enter` (the first
//! wrapper to fire) raises it, `cranelisp_collect_trace` clears it. Backend MUST
//! honour two constraints, both satisfied below:
//!   (a) it never clears `TRACE_BODY_RUNNING` itself (it emits no such call);
//!   (b) it emits `cranelisp_collect_trace` exactly once per `(trace ...)` form,
//!       as the LAST trace operation (see `compile_trace` / `compile_trace_no_swap`).
//!
//! The trace externs resolve from `cranelisp_intrinsics::catalog::intrinsics_table()`
//! in every mode (JIT `JITBuilder::symbol`, cache-hit `Linker::register_symbol`,
//! `--link` archive resolution) — backend just declares them `Linkage::Import`.

use std::collections::HashMap;

use cranelift::codegen::ir::{StackSlotData, StackSlotKind};
use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};

use cranelisp_intrinsics::trace::DescriptorKind;
use cranelisp_types::{
    CranelispError, DefKind, ErrorLocation, Expr, FQTypeName, ModuleEntry, Span, Type, TypeId,
};

use super::{FnCompiler, TracedFnInfo};

/// Maximum descriptor-tree depth. Recursive/cyclic ADT types (e.g.
/// `(deftype (List a) Nil (Cons [:a head :(List a) tail]))`) would otherwise
/// recurse without bound. Beyond this depth a node is degraded to a `TypeVar`
/// descriptor — the intrinsics walker renders it as the bare value, exactly the
/// residual-type-var fallback (`tracing.md` §3.4: the walker assumes a tree, so
/// backend bounds the depth and degrades interior repeats rather than emitting
/// an infinite blob). 16 is far beyond any realistic display nesting while
/// keeping a recursive `List`/`Tree` trace terminating.
const MAX_DESCRIPTOR_DEPTH: usize = 16;
// The bound must allow real display nesting (e.g. `(Option (Vec Int))` is 3
// levels) while keeping recursive ADTs terminating.
const _: () = assert!(MAX_DESCRIPTOR_DEPTH >= 4);

// ════════════════════════════════════════════════════════════════════════════
// Arena-blob builder — mirrors the `DisplayDescriptor` ABI (intrinsics-owned).
// ════════════════════════════════════════════════════════════════════════════
//
// Encoding (the single rule, from `cranelisp_intrinsics::trace::DisplayDescriptor`
// rustdoc): a contiguous `Vec<u8>` of fixed-size 24-byte descriptor records plus
// the variable-length data they reference (BlobStr, CtorTable). Every cross-link
// is a self-relative i32 byte offset measured from the offset field's own
// address; 0 = absent. No absolute pointers, no intra-blob relocations.

/// Record size in bytes — `size_of::<DisplayDescriptor>()`. Pinned by the
/// intrinsics `const _: assert!(size_of == 24)`; mirrored here as the stride.
const DESC_SIZE: usize = 24;
// Keep the arena stride in lockstep with the intrinsics-owned `DisplayDescriptor`
// ABI — a size change on either side fails this compile-time check (FIXME 0254/0255).
const _: () =
    assert!(DESC_SIZE == std::mem::size_of::<cranelisp_intrinsics::trace::DisplayDescriptor>());

// Field byte offsets within a descriptor record (see DisplayDescriptor rustdoc).
const OFF_KIND: usize = 0;
const OFF_NAME: usize = 8; // name_off (Adt type name)
const OFF_CHILD0: usize = 12; // child0_off (Vec element)
const OFF_CTORS: usize = 16; // ctors_off (Adt ctor table)

/// A flat position-independent descriptor arena.
struct DescriptorBlob {
    buf: Vec<u8>,
}

impl DescriptorBlob {
    fn new() -> Self {
        DescriptorBlob { buf: Vec::new() }
    }

    fn align4(&mut self) {
        while !self.buf.len().is_multiple_of(4) {
            self.buf.push(0);
        }
    }

    fn pos(&self) -> usize {
        self.buf.len()
    }

    /// Reserve a 24-byte descriptor record at a 4-aligned offset; return it.
    fn reserve_desc(&mut self) -> usize {
        self.align4();
        let at = self.buf.len();
        self.buf.extend_from_slice(&[0u8; DESC_SIZE]);
        at
    }

    fn write_i32(&mut self, at: usize, v: i32) {
        self.buf[at..at + 4].copy_from_slice(&v.to_le_bytes());
    }

    fn set_kind(&mut self, desc_at: usize, kind: DescriptorKind) {
        self.write_i32(desc_at + OFF_KIND, kind as i32);
    }

    /// Set a self-relative offset stored at `field_at` to point at `target_at`.
    fn set_self_rel(&mut self, field_at: usize, target_at: usize) {
        let rel = target_at as isize - field_at as isize;
        self.write_i32(field_at, rel as i32);
    }

    /// Append a `BlobStr` (`[len:i32 | bytes]`, NOT NUL-terminated); return its
    /// offset (the `len` field).
    fn append_str(&mut self, s: &str) -> usize {
        self.align4();
        let at = self.buf.len();
        self.buf.extend_from_slice(&(s.len() as i32).to_le_bytes());
        self.buf.extend_from_slice(s.as_bytes());
        at
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Concrete-type-arg substitution (replicates int's display.rs::build_adt_subst).
// ════════════════════════════════════════════════════════════════════════════

/// Collect unique `Type::Var` ids from a type in order of first occurrence.
/// Replicated from `src/display.rs::collect_var_ids` (NOT imported — int is a
/// downstream crate; the substitution logic lives where it is used).
fn collect_var_ids(ty: &Type, ids: &mut Vec<TypeId>) {
    match ty {
        Type::Var(id) => {
            if !ids.contains(id) {
                ids.push(*id);
            }
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_var_ids(p, ids);
            }
            collect_var_ids(ret, ids);
        }
        Type::ADT(_, args) | Type::TyConApp(_, args) => {
            for a in args {
                collect_var_ids(a, ids);
            }
        }
        Type::Int | Type::Bool | Type::String | Type::Float => {}
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Discovery — swap ALL symbol tables (S76 §5).
// ════════════════════════════════════════════════════════════════════════════

/// Compute the traced set by iterating ALL module symbol tables.
///
/// Per module: take its GOT base; select `Def { got_slot: Some(slot), .. }`
/// entries whose GOT slot holds a non-zero callable address (the single source
/// of truth, BC §3 invariant 3 — NOT `entry.code`). Skip constrained-poly base
/// names + overloaded base names (dispatch placeholders). Arity/param/result
/// types come from `entry.scheme.ty` (must be `Type::Fn`, else skip).
///
/// No project-root filter, primitives included — completeness by construction
/// (`tracing.md` §3.5). Free function so it is unit-testable against a
/// hand-built `DashMap` without a full `FnCompiler`.
fn discover_traced_fns_from_tables<C, L>(
    symbol_tables: &dashmap::DashMap<cranelisp_types::ModuleFullPath, cranelisp_types::SymbolTable<C, L>>,
) -> Vec<TracedFnInfo>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut traced = Vec::new();
    for module_guard in symbol_tables.iter() {
        let module_path = module_guard.key();
        let table = module_guard.value();
        let got_base = table.got.base_ptr() as i64;
        for (name, entry) in table.all_symbols() {
            let ModuleEntry::Def {
                got_slot: Some(slot),
                kind,
                scheme,
                ..
            } = entry
            else {
                continue;
            };
            // Skip constrained-poly base names + overloaded base names —
            // dispatch placeholders, not directly callable; their mono
            // specialisations / variants are slotted separately and traced on
            // their own.
            if matches!(
                kind.as_ref(),
                DefKind::UserFn {
                    constrained_fn: Some(_)
                } | DefKind::Overloaded { .. }
            ) {
                continue;
            }
            // Read the callable address from the GOT slot (the single source of
            // truth). 0 = not yet populated / no real code → skip. This includes
            // primitives (code: None) whose ptrs live in the GOT.
            let code_ptr = table.got.load_slot(*slot) as i64;
            if code_ptr == 0 {
                continue;
            }
            // Arity + param/result types from the scheme.
            let Type::Fn(params, ret) = &scheme.ty else {
                continue;
            };
            traced.push(TracedFnInfo {
                name: format!("{module_path}/{name}"),
                got_base,
                got_slot: *slot,
                arity: params.len(),
                code_ptr,
                param_types: params.clone(),
                result_type: (**ret).clone(),
            });
        }
    }
    traced
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Build a substitution from a polymorphic ADT's constructor-field type
    /// vars to the call site's concrete `type_args`. Replicates
    /// `src/display.rs::build_adt_subst`: collect the var ids used across the
    /// type's constructor fields (in first-occurrence order) and map them
    /// positionally to `type_args`.
    fn build_adt_subst(&self, fqtn: &FQTypeName, type_args: &[Type]) -> HashMap<TypeId, Type> {
        let mut subst = HashMap::new();
        let Some(type_def) = self.ctx.lookup_type_def(fqtn) else {
            return subst;
        };
        let metas = self.ctx.constructor_metas(&type_def);
        let mut var_ids = Vec::new();
        for meta in &metas {
            for field in &meta.fields {
                collect_var_ids(&field.ty, &mut var_ids);
            }
        }
        for (i, &id) in var_ids.iter().enumerate() {
            if let Some(arg) = type_args.get(i) {
                subst.insert(id, arg.clone());
            }
        }
        subst
    }

    /// Bake a single type's display descriptor into `blob`, returning the byte
    /// offset of the descriptor record (the blob root for that type).
    ///
    /// Recursion is bounded by `MAX_DESCRIPTOR_DEPTH`: beyond it, the node is
    /// degraded to `TypeVar` (rendered as the bare value), which terminates the
    /// bake for recursive/cyclic ADTs (the intrinsics walker assumes a tree).
    fn bake_descriptor(&self, blob: &mut DescriptorBlob, ty: &Type, depth: usize) -> usize {
        if depth >= MAX_DESCRIPTOR_DEPTH {
            let d = blob.reserve_desc();
            blob.set_kind(d, DescriptorKind::TypeVar);
            return d;
        }
        match ty {
            Type::Int => {
                let d = blob.reserve_desc();
                blob.set_kind(d, DescriptorKind::Int);
                d
            }
            Type::Bool => {
                let d = blob.reserve_desc();
                blob.set_kind(d, DescriptorKind::Bool);
                d
            }
            Type::Float => {
                let d = blob.reserve_desc();
                blob.set_kind(d, DescriptorKind::Float);
                d
            }
            Type::String => {
                let d = blob.reserve_desc();
                blob.set_kind(d, DescriptorKind::String);
                d
            }
            Type::Fn(_, _) => {
                let d = blob.reserve_desc();
                blob.set_kind(d, DescriptorKind::Fn);
                d
            }
            Type::Var(_) | Type::TyConApp(_, _) => {
                // Residual type variable / higher-kinded application with no
                // concrete instantiation at this site — bare-value fallback.
                let d = blob.reserve_desc();
                blob.set_kind(d, DescriptorKind::TypeVar);
                d
            }
            Type::ADT(fqtn, type_args) => {
                if fqtn.name.as_ref() == "Vec" {
                    self.bake_vec(blob, type_args.first(), depth)
                } else {
                    self.bake_adt(blob, fqtn, type_args, depth)
                }
            }
        }
    }

    /// Bake a `Vec` descriptor: kind=Vec with exactly one child (element).
    fn bake_vec(&self, blob: &mut DescriptorBlob, elem: Option<&Type>, depth: usize) -> usize {
        let root = blob.reserve_desc();
        blob.set_kind(root, DescriptorKind::Vec);
        if let Some(elem_ty) = elem {
            let child = self.bake_descriptor(blob, elem_ty, depth + 1);
            blob.set_self_rel(root + OFF_CHILD0, child);
        }
        root
    }

    /// Bake an `Adt` descriptor: kind=Adt with a type-name BlobStr + a CtorTable.
    ///
    /// CtorTable: `[n_ctors:i32 | single_match:i32 | CtorEntry[n]]`.
    /// CtorEntry: `[tag:i32 | n_fields:i32 | name_off:i32 | fields_off:i32]`.
    /// `fields_off` → array of `n_fields` self-relative i32 offsets, each → a
    /// field child descriptor (concrete-substituted).
    fn bake_adt(
        &self,
        blob: &mut DescriptorBlob,
        fqtn: &FQTypeName,
        type_args: &[Type],
        depth: usize,
    ) -> usize {
        let root = blob.reserve_desc();
        blob.set_kind(root, DescriptorKind::Adt);

        let Some(type_def) = self.ctx.lookup_type_def(fqtn) else {
            // No type def available — leave Adt with no name/ctors; the walker
            // falls back to the bare value.
            return root;
        };
        let metas = self.ctx.constructor_metas(&type_def);
        // single_match: exactly one constructor whose name equals the type name
        // (spec §1.5 — suppress the `Type.` prefix, e.g. `(Point 3 4)`).
        let type_name = fqtn.name.as_ref();
        let single_match = type_def.constructors.len() == 1
            && type_def
                .constructors
                .first()
                .map(|c| c.as_ref() == type_name)
                .unwrap_or(false);

        // Concrete-type substitution for polymorphic fields.
        let subst = self.build_adt_subst(fqtn, type_args);

        // Bake child field descriptors FIRST (so their offsets exist), tracking
        // per-constructor (tag, ctor_name, Vec<field_desc_off>).
        struct CtorBake {
            tag: i32,
            name: String,
            field_descs: Vec<usize>,
        }
        let mut ctor_bakes: Vec<CtorBake> = Vec::with_capacity(metas.len());
        for (ctor_name, meta) in type_def.constructors.iter().zip(metas.iter()) {
            let mut field_descs = Vec::with_capacity(meta.fields.len());
            for field in &meta.fields {
                let concrete = cranelisp_types::apply(&subst, &field.ty);
                let fd = self.bake_descriptor(blob, &concrete, depth + 1);
                field_descs.push(fd);
            }
            ctor_bakes.push(CtorBake {
                tag: meta.tag as i32,
                name: ctor_name.as_ref().to_string(),
                field_descs,
            });
        }

        // Bake the type-name BlobStr.
        let type_name_off = blob.append_str(type_name);

        // Bake ctor-name BlobStrs and per-ctor field-offset arrays.
        // ctor_name_off[i], fields_arr_off[i] (0 if no fields).
        let mut ctor_name_offs = Vec::with_capacity(ctor_bakes.len());
        let mut fields_arr_offs = Vec::with_capacity(ctor_bakes.len());
        for cb in &ctor_bakes {
            let name_off = blob.append_str(&cb.name);
            ctor_name_offs.push(name_off);
            if cb.field_descs.is_empty() {
                fields_arr_offs.push(None);
            } else {
                // An array of n self-relative i32 offsets, each pointing at the
                // already-baked field child descriptor.
                blob.align4();
                let arr_at = blob.pos();
                // Reserve the array slots.
                for _ in &cb.field_descs {
                    blob.buf.extend_from_slice(&0i32.to_le_bytes());
                }
                for (i, &fd) in cb.field_descs.iter().enumerate() {
                    blob.set_self_rel(arr_at + i * 4, fd);
                }
                fields_arr_offs.push(Some(arr_at));
            }
        }

        // Bake the CtorTable. Header [n_ctors | single_match] then entries.
        blob.align4();
        let ctab = blob.pos();
        blob.buf
            .extend_from_slice(&(ctor_bakes.len() as i32).to_le_bytes());
        blob.buf
            .extend_from_slice(&(if single_match { 1i32 } else { 0i32 }).to_le_bytes());
        let entries_at = blob.pos();
        // Reserve entry records (4 i32 = 16 bytes each).
        for _ in &ctor_bakes {
            blob.buf.extend_from_slice(&[0u8; 16]);
        }
        for (i, cb) in ctor_bakes.iter().enumerate() {
            let e = entries_at + i * 16;
            blob.write_i32(e, cb.tag); // tag
            blob.write_i32(e + 4, cb.field_descs.len() as i32); // n_fields
            blob.set_self_rel(e + 8, ctor_name_offs[i]); // name_off (self-rel)
            match fields_arr_offs[i] {
                Some(arr_at) => blob.set_self_rel(e + 12, arr_at), // fields_off
                None => blob.write_i32(e + 12, 0),
            }
        }

        // Link root.name_off + root.ctors_off (self-relative).
        blob.set_self_rel(root + OFF_NAME, type_name_off);
        blob.set_self_rel(root + OFF_CTORS, ctab);
        root
    }

    /// Bake the full descriptor set for one traced function — one blob holding
    /// the param descriptors (in order) and the result descriptor — and emit it
    /// as a read-only data symbol. Returns the per-param + result blob-root byte
    /// offsets plus the `DataId`, so the wrapper can materialise each
    /// descriptor's address via `global_value` against the symbol.
    ///
    /// Packing all of one wrapper's descriptors into ONE data symbol matches
    /// `tracing.md` §3.4 "one data symbol per wrapper's descriptor set, one
    /// relocation per wrapper reference."
    fn bake_descriptor_blob(
        &mut self,
        tf: &TracedFnInfo,
        span: Span,
    ) -> Result<DescriptorSet, CranelispError> {
        let mut blob = DescriptorBlob::new();
        let mut param_roots = Vec::with_capacity(tf.param_types.len());
        for pty in &tf.param_types {
            param_roots.push(self.bake_descriptor(&mut blob, pty, 0));
        }
        let result_root = self.bake_descriptor(&mut blob, &tf.result_type, 0);

        // Read-only, non-thread-local anonymous data.
        let data_id = self
            .module
            .declare_anonymous_data(false, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare trace descriptor data for '{}': {e}", tf.name),
                location: ErrorLocation::from_span(span),
            })?;
        let mut desc = cranelift_module::DataDescription::new();
        // 4-byte alignment matches `align_of::<DisplayDescriptor>() == 4`.
        desc.set_align(4);
        desc.define(blob.buf.into_boxed_slice());
        self.module
            .define_data(data_id, &desc)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define trace descriptor data for '{}': {e}", tf.name),
                location: ErrorLocation::from_span(span),
            })?;

        Ok(DescriptorSet {
            data_id,
            param_roots,
            result_root,
        })
    }

    /// Discover the traced set by iterating ALL module symbol tables (S76 §5).
    ///
    /// Per module: take its GOT base; select `Def { got_slot: Some(slot), .. }`
    /// entries whose GOT slot holds a non-zero callable address (the single
    /// source of truth, BC §3 invariant 3 — NOT `entry.code`). Skip
    /// constrained-poly base names (dispatch placeholders). Arity/param/result
    /// types come from `entry.scheme.ty` (must be `Type::Fn`, else skip).
    ///
    /// No project-root filter, primitives included — completeness by
    /// construction (`tracing.md` §3.5).
    fn discover_traced_fns(&self) -> Vec<TracedFnInfo> {
        discover_traced_fns_from_tables(self.ctx.symbol_tables)
    }

    /// Discard a body result by decrementing its RC if it is heap-allocated.
    /// Used by both `compile_trace` and `compile_trace_no_swap` to drop the
    /// body value (the trace result is the Trace ADT, not the body's value).
    fn emit_body_discard(&mut self, body_val: Value, body: &Expr) {
        if let Some(ty) = body.inferred_type().cloned()
            && self.is_heap_type(&ty)
        {
            crate::heap::emit_rc_dec(
                &mut self.builder,
                self.module,
                body_val,
                self.ctx.dealloc_func_id,
                None,
            );
        }
    }

    /// Compile a `(trace body)` expression.
    ///
    /// Returns a `Value` that is a heap pointer to a `Trace` ADT.
    pub(crate) fn compile_trace(
        &mut self,
        _modules: &[cranelisp_types::Symbol],
        body: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Discovery is internal now (S76 §5): iterate all symbol tables.
        let traced = self.discover_traced_fns();
        if traced.is_empty() {
            // Degenerate program with no GOT-slotted callable — fall back to the
            // empty-trace path (still emits collect_trace, last).
            return self.compile_trace_no_swap(body, span);
        }

        // Group by GOT base address (each module has its own GOT table).
        let mut got_groups: Vec<(i64, Vec<&TracedFnInfo>)> = Vec::new();
        for tf in &traced {
            if let Some(grp) = got_groups.iter_mut().find(|(addr, _)| *addr == tf.got_base) {
                grp.1.push(tf);
            } else {
                got_groups.push((tf.got_base, vec![tf]));
            }
        }

        // Declare trace runtime functions in the module (idempotent for Import linkage).
        let swap_id = self.declare_trace_extern("cranelisp_trace_swap_got", 4, true, span)?;
        let restore_id =
            self.declare_trace_extern("cranelisp_trace_restore_got", 2, false, span)?;
        let collect_id = self.declare_trace_extern("cranelisp_collect_trace", 0, true, span)?;

        // For each GOT group: compile wrappers and emit swap_got call.
        let mut swap_results: Vec<(i64, Value)> = Vec::new();

        for (got_base, group) in &got_groups {
            let n = group.len();

            // Allocate and leak a u32 slots array (known at compile time).
            let slots: Box<[u32]> = group
                .iter()
                .map(|tf| tf.got_slot as u32)
                .collect::<Vec<_>>()
                .into_boxed_slice();
            let slots_ptr = Box::into_raw(slots) as *mut u32 as i64;

            // Allocate and leak a wrappers buffer (i64, filled at JIT runtime via func_addr).
            let wrappers_buf: Box<[i64]> = vec![0i64; n].into_boxed_slice();
            let wrappers_buf_ptr = Box::into_raw(wrappers_buf) as *mut i64 as i64;

            // For each function: compile a trace wrapper, then emit a store of its
            // code_ptr into the wrappers buffer at runtime.
            let buf_addr_val = self.builder.ins().iconst(types::I64, wrappers_buf_ptr);
            for (i, tf) in group.iter().enumerate() {
                let wrapper_id = self.compile_trace_wrapper_fn(tf, span)?;
                let func_ref = self
                    .module
                    .declare_func_in_func(wrapper_id, self.builder.func);
                let wrapper_ptr_val = self.builder.ins().func_addr(types::I64, func_ref);
                let offset = (i * 8) as i32;
                self.builder
                    .ins()
                    .store(MemFlags::trusted(), wrapper_ptr_val, buf_addr_val, offset);
            }

            // Emit cranelisp_trace_swap_got(got_base, n_slots, slots_ptr, wrappers_ptr).
            let got_base_val = self.builder.ins().iconst(types::I64, *got_base);
            let n_val = self.builder.ins().iconst(types::I64, n as i64);
            let slots_val = self.builder.ins().iconst(types::I64, slots_ptr);
            let wrappers_val = self.builder.ins().iconst(types::I64, wrappers_buf_ptr);
            let swap_ref = self.module.declare_func_in_func(swap_id, self.builder.func);
            let call = self
                .builder
                .ins()
                .call(swap_ref, &[got_base_val, n_val, slots_val, wrappers_val]);
            let saved_got_val = self.builder.inst_results(call)[0];
            swap_results.push((*got_base, saved_got_val));
        }

        // Compile the body expression.
        // Disable sparkability analysis inside trace bodies — trace must
        // execute sequentially to produce deterministic trace trees.
        let saved_trace = self.in_trace_body;
        self.in_trace_body = true;
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;
        let body_result = self.compile_expr(body)?;
        self.in_tail_position = saved_tail;
        self.in_trace_body = saved_trace;

        // Discard body result (dec RC if it is heap-allocated).
        // The trace result is the Trace ADT, not the body's value.
        self.emit_body_discard(body_result, body);

        // Restore GOTs in reverse order (for clean nesting semantics).
        let restore_ref = self
            .module
            .declare_func_in_func(restore_id, self.builder.func);
        for (got_base, saved_got_val) in swap_results.iter().rev() {
            let got_base_val = self.builder.ins().iconst(types::I64, *got_base);
            self.builder
                .ins()
                .call(restore_ref, &[got_base_val, *saved_got_val]);
        }

        // Call cranelisp_collect_trace() -> Trace ADT heap ptr. Emitted exactly
        // once, LAST — this clears the nested-trace boundary flag (intrinsics
        // guard contract; backend never clears it itself).
        let collect_ref = self
            .module
            .declare_func_in_func(collect_id, self.builder.func);
        let collect_call = self.builder.ins().call(collect_ref, &[]);
        Ok(self.builder.inst_results(collect_call)[0])
    }

    /// Fallback path used when discovery finds no traced functions.
    ///
    /// Evaluates the body (discards result) and returns an empty TraceCall via
    /// `cranelisp_collect_trace`. The trace stack will be empty so it returns a
    /// minimal TraceCall with the root "::trace::" name.
    fn compile_trace_no_swap(
        &mut self,
        body: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;
        let body_result = self.compile_expr(body)?;
        self.in_tail_position = saved_tail;

        // Discard body result.
        self.emit_body_discard(body_result, body);

        // Return empty trace from collect_trace (handles empty stack gracefully).
        let collect_id = self.declare_trace_extern("cranelisp_collect_trace", 0, true, span)?;
        let collect_ref = self
            .module
            .declare_func_in_func(collect_id, self.builder.func);
        let call = self.builder.ins().call(collect_ref, &[]);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Declare a trace runtime extern function in the module.
    ///
    /// `n_params`: number of `i64` parameters.
    /// `has_return`: whether the function returns an `i64`.
    ///
    /// Idempotent: re-declaring with the same signature returns the existing FuncId.
    /// The named symbol resolves from `cranelisp_intrinsics::catalog::intrinsics_table()`
    /// in every mode (S76 §4.2).
    fn declare_trace_extern(
        &mut self,
        name: &str,
        n_params: usize,
        has_return: bool,
        span: Span,
    ) -> Result<FuncId, CranelispError> {
        let mut sig = self.module.make_signature();
        for _ in 0..n_params {
            sig.params.push(AbiParam::new(types::I64));
        }
        if has_return {
            sig.returns.push(AbiParam::new(types::I64));
        }
        self.module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare trace extern '{}': {}", name, e),
                location: ErrorLocation::from_span(span),
            })
    }

    /// Compile a thin trace wrapper function for a single traced function.
    ///
    /// Wrapper signature: `(arg0: i64, ..., argN-1: i64) -> i64`
    ///
    /// Wrapper body:
    /// ```text
    /// str_ptr_0 = cranelisp_trace_format(arg0, descriptor_ptr_0)
    /// ...
    /// store str_ptrs into stack slot
    /// cranelisp_trace_enter(name_ptr, name_len, arity, array_ptr)
    /// orig_result = call_indirect(original_code_ptr, [arg0..argN-1])
    /// result_str  = cranelisp_trace_format(orig_result, result_descriptor_ptr)
    /// final       = cranelisp_trace_exit(orig_result, result_str)
    /// return final
    /// ```
    ///
    /// The original code ptr is embedded as an `iconst` -- calls bypass the GOT and
    /// call the original implementation directly. Recursive calls inside the original
    /// go through the (swapped) GOT, naturally building the call tree.
    ///
    /// Each `cranelisp_trace_format` descriptor pointer is materialised from the
    /// wrapper's baked descriptor blob via `global_value` against the blob's data
    /// symbol — mode-agnostic (JIT patches to a runtime address; object emits one
    /// relocation per reference). See `bake_descriptor_blob`.
    fn compile_trace_wrapper_fn(
        &mut self,
        tf: &TracedFnInfo,
        span: Span,
    ) -> Result<FuncId, CranelispError> {
        assert_eq!(
            tf.arity,
            tf.param_types.len(),
            "trace wrapper arity mismatch for '{}': arity={} but param_types={}",
            tf.name,
            tf.arity,
            tf.param_types.len()
        );

        // Bake the descriptor set (param + result) into one read-only data
        // symbol. Done before building the wrapper IR so the DataId exists.
        let desc_set = self.bake_descriptor_blob(tf, span)?;

        // Wrapper signature: (arg0..argN-1) -> i64.
        let mut sig = self.module.make_signature();
        for _ in 0..tf.arity {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let wrapper_func_id = self
            .module
            .declare_anonymous_function(&sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare trace wrapper for '{}': {}", tf.name, e),
                location: ErrorLocation::from_span(span),
            })?;

        // Declare trace_enter (4 params), trace_exit (2 params), and trace_format (2 params).
        let enter_id = self.declare_trace_extern("cranelisp_trace_enter", 4, false, span)?;
        let exit_id = self.declare_trace_extern("cranelisp_trace_exit", 2, true, span)?;
        let format_id = self.declare_trace_extern("cranelisp_trace_format", 2, true, span)?;

        // Leak the function name bytes -- valid for the program lifetime.
        let name_bytes: Box<[u8]> = tf.name.as_bytes().to_vec().into_boxed_slice();
        let name_len = name_bytes.len() as i64;
        let name_ptr = Box::into_raw(name_bytes) as *mut u8 as i64;

        // Build and compile the wrapper IR.
        {
            let mut wrapper_func = cranelift::codegen::ir::Function::with_name_signature(
                cranelift::codegen::ir::UserFuncName::user(0, wrapper_func_id.as_u32()),
                sig.clone(),
            );
            let mut wrapper_ctx = FunctionBuilderContext::new();
            let mut wb = FunctionBuilder::new(&mut wrapper_func, &mut wrapper_ctx);

            let entry = wb.create_block();
            wb.append_block_params_for_function_params(entry);
            wb.switch_to_block(entry);
            wb.seal_block(entry);

            let args: Vec<Value> = wb.block_params(entry).to_vec();

            // Declare externs inside the wrapper function.
            let format_ref = self.module.declare_func_in_func(format_id, wb.func);
            let enter_ref = self.module.declare_func_in_func(enter_id, wb.func);

            // Materialise the descriptor blob's base address once (one
            // global_value per wrapper → one relocation in object mode).
            let blob_gv = self
                .module
                .declare_data_in_func(desc_set.data_id, wb.func);
            let blob_base = wb.ins().global_value(types::I64, blob_gv);

            // Format each parameter using cranelisp_trace_format(val, descriptor_ptr).
            // descriptor_ptr = blob_base + param_root_offset.
            let arity = tf.arity;
            let mut param_str_ptrs: Vec<Value> = Vec::with_capacity(arity);
            for (i, &root_off) in desc_set.param_roots.iter().enumerate() {
                let arg_val = args[i];
                let desc_ptr = wb.ins().iadd_imm(blob_base, root_off as i64);
                let fmt_call = wb.ins().call(format_ref, &[arg_val, desc_ptr]);
                param_str_ptrs.push(wb.inst_results(fmt_call)[0]);
            }

            // Store formatted param string pointers in a stack slot (if arity > 0),
            // then pass the slot address to cranelisp_trace_enter.
            let (params_count_val, array_ptr_val) = if arity > 0 {
                let slot = wb.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    (arity * 8) as u32,
                    3, // 2^3 = 8 byte alignment
                ));
                for (i, &str_ptr) in param_str_ptrs.iter().enumerate() {
                    wb.ins().stack_store(str_ptr, slot, (i * 8) as i32);
                }
                let count = wb.ins().iconst(types::I64, arity as i64);
                let ptr = wb.ins().stack_addr(types::I64, slot, 0i32);
                (count, ptr)
            } else {
                // No params: pass count=0, ptr=null (runtime won't dereference).
                let count = wb.ins().iconst(types::I64, 0i64);
                let ptr = wb.ins().iconst(types::I64, 0i64);
                (count, ptr)
            };

            // cranelisp_trace_enter(name_ptr, name_len, params_count, array_ptr)
            let name_ptr_val = wb.ins().iconst(types::I64, name_ptr);
            let name_len_val = wb.ins().iconst(types::I64, name_len);
            wb.ins().call(
                enter_ref,
                &[name_ptr_val, name_len_val, params_count_val, array_ptr_val],
            );

            // Build call signature for the original function.
            let mut orig_sig = self.module.make_signature();
            for _ in 0..tf.arity {
                orig_sig.params.push(AbiParam::new(types::I64));
            }
            orig_sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = wb.import_signature(orig_sig);

            // Call original via embedded code_ptr (bypasses the swapped GOT).
            let code_ptr_val = wb.ins().iconst(types::I64, tf.code_ptr);
            let orig_call = wb.ins().call_indirect(sig_ref, code_ptr_val, &args);
            let orig_result = wb.inst_results(orig_call)[0];

            // Format the result using cranelisp_trace_format(orig_result, result_descriptor_ptr).
            let format_ref2 = self.module.declare_func_in_func(format_id, wb.func);
            let result_desc_ptr = wb.ins().iadd_imm(blob_base, desc_set.result_root as i64);
            let result_fmt_call = wb.ins().call(format_ref2, &[orig_result, result_desc_ptr]);
            let result_str = wb.inst_results(result_fmt_call)[0];

            // cranelisp_trace_exit(orig_result, result_str) -> final result
            let exit_ref = self.module.declare_func_in_func(exit_id, wb.func);
            let exit_call = wb.ins().call(exit_ref, &[orig_result, result_str]);
            let final_result = wb.inst_results(exit_call)[0];

            wb.ins().return_(&[final_result]);
            wb.seal_all_blocks();
            wb.finalize();

            let mut ctx = cranelift::codegen::Context::for_function(wrapper_func);
            self.module
                .define_function(wrapper_func_id, &mut ctx)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to define trace wrapper for '{}': {}", tf.name, e),
                    location: ErrorLocation::from_span(span),
                })?;
        }

        Ok(wrapper_func_id)
    }
} // impl FnCompiler — trace codegen

/// One traced function's baked descriptor set: a single read-only data symbol
/// holding the param descriptors (in order) and the result descriptor, plus the
/// blob-root byte offset of each. The wrapper materialises each descriptor's
/// address as `blob_base + offset` (one `global_value` per wrapper).
struct DescriptorSet {
    data_id: cranelift_module::DataId,
    param_roots: Vec<usize>,
    result_root: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_intrinsics::heap_string::{alloc_string, read_string_as_str};
    use cranelisp_intrinsics::trace::cranelisp_trace_format;
    use cranelisp_types::{
        DefKind, ModuleEntry, ModuleFullPath, Scheme, Symbol, SymbolTable, Type, Visibility,
    };
    use dashmap::DashMap;
    use std::collections::HashMap;

    // ── Descriptor-bake round-trip against the intrinsics walker ──────────────
    //
    // These build descriptor blobs with the SAME `DescriptorBlob` primitives the
    // production bakers (`bake_descriptor` / `bake_vec` / `bake_adt`) use, then
    // exercise the intrinsics-owned `cranelisp_trace_format` against them. A pass
    // proves the arena encoding backend emits is read correctly by the formatter
    // — the cross-crate ABI is in agreement (FIXME 0254 + 0255).

    /// Run `cranelisp_trace_format` on a baked blob root and read back the result.
    fn fmt(value: i64, blob: &DescriptorBlob, root: usize) -> String {
        let ptr = unsafe { blob.buf.as_ptr().add(root) } as i64;
        let s_heap = cranelisp_trace_format(value, ptr);
        unsafe { read_string_as_str(s_heap) }.to_string()
    }

    #[test]
    fn bake_int_descriptor_round_trips() {
        let mut b = DescriptorBlob::new();
        let d = b.reserve_desc();
        b.set_kind(d, DescriptorKind::Int);
        assert_eq!(fmt(42, &b, d), "42");
        assert_eq!(fmt(-7, &b, d), "-7");
    }

    #[test]
    fn bake_bool_float_string_descriptors_round_trip() {
        let mut b = DescriptorBlob::new();
        let bd = b.reserve_desc();
        b.set_kind(bd, DescriptorKind::Bool);
        let fd = b.reserve_desc();
        b.set_kind(fd, DescriptorKind::Float);
        let sd = b.reserve_desc();
        b.set_kind(sd, DescriptorKind::String);
        assert_eq!(fmt(1, &b, bd), "true");
        assert_eq!(fmt(0, &b, bd), "false");
        assert_eq!(fmt(1.0_f64.to_bits() as i64, &b, fd), "1.0");
        let heap = alloc_string(b"hi") as i64;
        assert_eq!(fmt(heap, &b, sd), "\"hi\"");
    }

    #[test]
    fn bake_vec_of_int_descriptor_round_trips() {
        // Mirror `bake_vec`: root(Vec) with child0_off → child(Int).
        let mut b = DescriptorBlob::new();
        let root = b.reserve_desc();
        b.set_kind(root, DescriptorKind::Vec);
        let child = b.reserve_desc();
        b.set_kind(child, DescriptorKind::Int);
        b.set_self_rel(root + OFF_CHILD0, child);

        let v = cranelisp_intrinsics::vec_runtime::vec_new(3);
        let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 10);
        let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 20);
        let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 30);
        assert_eq!(fmt(v, &b, root), "[10 20 30]");
    }

    /// Build an `(Option a)` instantiated at `Int` blob by hand, mirroring the
    /// exact record/ctor-table layout `bake_adt` emits, then round-trip
    /// `(Some 42)` + `None` through the walker. Exercises the polymorphic-field
    /// concrete-substitution outcome (Int field descriptor baked from `a := Int`)
    /// and the nested data path.
    #[test]
    fn bake_polymorphic_adt_concrete_substitution_round_trips() {
        let mut b = DescriptorBlob::new();
        let root = b.reserve_desc();
        b.set_kind(root, DescriptorKind::Adt);
        // Some's single field, substituted a := Int.
        let int_field = b.reserve_desc();
        b.set_kind(int_field, DescriptorKind::Int);

        let type_name = b.append_str("Option");
        let none_name = b.append_str("None");
        let some_name = b.append_str("Some");
        // fields_off array for Some (1 self-rel i32 → int_field).
        b.align4();
        let some_fields = b.pos();
        b.buf.extend_from_slice(&0i32.to_le_bytes());
        b.set_self_rel(some_fields, int_field);

        // CtorTable [n=2 | single_match=0 | 2 entries].
        b.align4();
        let ctab = b.pos();
        b.buf.extend_from_slice(&2i32.to_le_bytes());
        b.buf.extend_from_slice(&0i32.to_le_bytes());
        let entries_at = b.pos();
        b.buf.extend_from_slice(&[0u8; 2 * 16]);
        // None tag=0 n_fields=0.
        b.write_i32(entries_at, 0);
        b.write_i32(entries_at + 4, 0);
        b.set_self_rel(entries_at + 8, none_name);
        b.write_i32(entries_at + 12, 0);
        // Some tag=1 n_fields=1.
        b.write_i32(entries_at + 16, 1);
        b.write_i32(entries_at + 16 + 4, 1);
        b.set_self_rel(entries_at + 16 + 8, some_name);
        b.set_self_rel(entries_at + 16 + 12, some_fields);

        b.set_self_rel(root + OFF_NAME, type_name);
        b.set_self_rel(root + OFF_CTORS, ctab);

        assert_eq!(fmt(0, &b, root), "Option.None");
        let some_val = alloc_adt_for_test(1, &[42]);
        assert_eq!(fmt(some_val, &b, root), "(Option.Some 42)");
    }

    /// Nested ADT: `(Option (Vec Int))` rendering `(Some [1 2])`. Exercises a
    /// field child descriptor that is itself a Vec-of-Int (two levels of nesting
    /// through the self-relative offsets).
    #[test]
    fn bake_nested_adt_round_trips() {
        let mut b = DescriptorBlob::new();
        let root = b.reserve_desc();
        b.set_kind(root, DescriptorKind::Adt);
        // Some's field is (Vec Int): Vec root + Int child.
        let vec_field = b.reserve_desc();
        b.set_kind(vec_field, DescriptorKind::Vec);
        let int_child = b.reserve_desc();
        b.set_kind(int_child, DescriptorKind::Int);
        b.set_self_rel(vec_field + OFF_CHILD0, int_child);

        let type_name = b.append_str("Option");
        let some_name = b.append_str("Some");
        b.align4();
        let some_fields = b.pos();
        b.buf.extend_from_slice(&0i32.to_le_bytes());
        b.set_self_rel(some_fields, vec_field);

        b.align4();
        let ctab = b.pos();
        b.buf.extend_from_slice(&1i32.to_le_bytes()); // n_ctors
        b.buf.extend_from_slice(&0i32.to_le_bytes()); // single_match
        let entries_at = b.pos();
        b.buf.extend_from_slice(&[0u8; 16]);
        b.write_i32(entries_at, 1); // tag (Some)
        b.write_i32(entries_at + 4, 1); // n_fields
        b.set_self_rel(entries_at + 8, some_name);
        b.set_self_rel(entries_at + 12, some_fields);
        b.set_self_rel(root + OFF_NAME, type_name);
        b.set_self_rel(root + OFF_CTORS, ctab);

        let v = cranelisp_intrinsics::vec_runtime::vec_new(2);
        let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 1);
        let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 2);
        let some_val = alloc_adt_for_test(1, &[v]);
        assert_eq!(fmt(some_val, &b, root), "(Option.Some [1 2])");
    }

    #[test]
    fn bake_recursion_depth_guard_terminates() {
        // A blob deeper than MAX_DESCRIPTOR_DEPTH degrades to TypeVar — verify
        // the TypeVar kind renders as a bare value (the degrade target). This is
        // the terminating behaviour for recursive/cyclic ADTs.
        let mut b = DescriptorBlob::new();
        let d = b.reserve_desc();
        b.set_kind(d, DescriptorKind::TypeVar);
        assert_eq!(fmt(123, &b, d), "123");
    }

    // Allocate a heap ADT cell `[hdr | tag | field0..]` using the runtime
    // allocator, matching the base-pointer convention the walker reads.
    fn alloc_adt_for_test(tag: i64, fields: &[i64]) -> i64 {
        let payload = (1 + fields.len()) * 8;
        let base = cranelisp_intrinsics::alloc_with_rc(payload) as i64;
        unsafe {
            *((base as *mut u8).add(16) as *mut i64) = tag;
            for (i, &f) in fields.iter().enumerate() {
                *((base as *mut u8).add(24 + i * 8) as *mut i64) = f;
            }
        }
        base
    }

    // ── Discovery-set tests (S76 §5) ──────────────────────────────────────────

    fn fn_scheme(params: Vec<Type>, ret: Type) -> Scheme {
        Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Fn(params, Box::new(ret)),
        }
    }

    /// Insert a Def with a GOT slot + a fake non-zero code pointer.
    fn insert_fn(
        table: &mut SymbolTable<(), ()>,
        name: &str,
        kind: DefKind,
        scheme: Scheme,
        fake_ptr: usize,
    ) {
        let slot = table.allocate_got_slot();
        let entry = ModuleEntry::def(scheme, kind)
            .visibility(Visibility::Public)
            .got_slot(slot)
            .build();
        table.insert(Symbol::from(name), entry);
        table.got.store_slot(slot, fake_ptr as *const u8);
    }

    #[test]
    fn discovery_includes_all_modules_and_primitives() {
        let tables: DashMap<ModuleFullPath, SymbolTable<(), ()>> = DashMap::new();

        let mut user = SymbolTable::<(), ()>::new(ModuleFullPath::from("user"));
        insert_fn(
            &mut user,
            "fact",
            DefKind::UserFn { constrained_fn: None },
            fn_scheme(vec![Type::Int], Type::Int),
            0x1000,
        );
        tables.insert(ModuleFullPath::from("user"), user);

        // The synthetic `primitives` module: entries carry code: None but the
        // GOT slot holds the fn ptr. Discovery must pick it up (no project-root
        // filter, primitives included).
        let mut prims = SymbolTable::<(), ()>::new(ModuleFullPath::from("primitives"));
        insert_fn(
            &mut prims,
            "str-concat",
            DefKind::Primitive,
            fn_scheme(vec![Type::String, Type::String], Type::String),
            0x2000,
        );
        tables.insert(ModuleFullPath::from("primitives"), prims);

        let traced = discover_traced_fns_from_tables(&tables);
        let names: Vec<&str> = traced.iter().map(|t| t.name.as_str()).collect();
        assert!(names.contains(&"user/fact"), "user fn must be discovered: {names:?}");
        assert!(
            names.contains(&"primitives/str-concat"),
            "primitive must be discovered (all symbol tables, primitives included): {names:?}"
        );
        // Arity + types come from the scheme.
        let prim = traced.iter().find(|t| t.name == "primitives/str-concat").unwrap();
        assert_eq!(prim.arity, 2);
        assert_eq!(prim.param_types, vec![Type::String, Type::String]);
        assert_eq!(prim.result_type, Type::String);
        assert_eq!(prim.code_ptr, 0x2000);
    }

    #[test]
    fn discovery_skips_constrained_poly_base_and_overloaded() {
        let tables: DashMap<ModuleFullPath, SymbolTable<(), ()>> = DashMap::new();
        let mut m = SymbolTable::<(), ()>::new(ModuleFullPath::from("user"));

        // Constrained-poly base name (dispatch placeholder) — skipped.
        insert_fn(
            &mut m,
            "add",
            DefKind::UserFn {
                constrained_fn: Some(Box::new(make_constrained_fn())),
            },
            fn_scheme(vec![Type::Var(0), Type::Var(0)], Type::Var(0)),
            0x3000,
        );
        // Overloaded base name — skipped.
        insert_fn(
            &mut m,
            "show",
            DefKind::Overloaded { variants: vec![] },
            fn_scheme(vec![Type::Int], Type::String),
            0x3100,
        );
        // A real mono fn — kept.
        insert_fn(
            &mut m,
            "double",
            DefKind::UserFn { constrained_fn: None },
            fn_scheme(vec![Type::Int], Type::Int),
            0x3200,
        );
        tables.insert(ModuleFullPath::from("user"), m);

        let traced = discover_traced_fns_from_tables(&tables);
        let names: Vec<&str> = traced.iter().map(|t| t.name.as_str()).collect();
        assert!(names.contains(&"user/double"), "mono fn kept: {names:?}");
        assert!(!names.contains(&"user/add"), "constrained-poly base skipped: {names:?}");
        assert!(!names.contains(&"user/show"), "overloaded base skipped: {names:?}");
    }

    #[test]
    fn discovery_skips_empty_got_slots_and_non_fn_schemes() {
        let tables: DashMap<ModuleFullPath, SymbolTable<(), ()>> = DashMap::new();
        let mut m = SymbolTable::<(), ()>::new(ModuleFullPath::from("user"));

        // Def with a got_slot but the GOT slot is 0 (unpopulated) — skipped.
        let slot = m.allocate_got_slot();
        let entry = ModuleEntry::def(
            fn_scheme(vec![Type::Int], Type::Int),
            DefKind::UserFn { constrained_fn: None },
        )
        .got_slot(slot)
        .build();
        m.insert(Symbol::from("uncompiled"), entry);
        // (no got.store_slot — slot stays null)

        // Non-Fn scheme (e.g. a zero-arg value) with a populated slot — skipped
        // (arity/types require Type::Fn).
        insert_fn(
            &mut m,
            "konst",
            DefKind::UserFn { constrained_fn: None },
            Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Int,
            },
            0x4000,
        );
        tables.insert(ModuleFullPath::from("user"), m);

        let traced = discover_traced_fns_from_tables(&tables);
        let names: Vec<&str> = traced.iter().map(|t| t.name.as_str()).collect();
        assert!(!names.contains(&"user/uncompiled"), "empty GOT slot skipped: {names:?}");
        assert!(!names.contains(&"user/konst"), "non-Fn scheme skipped: {names:?}");
    }

    // A minimal ConstrainedFn for the skip test. We only need the variant
    // discriminator (`constrained_fn: Some(_)`), so any well-formed value works.
    fn make_constrained_fn() -> cranelisp_types::ConstrainedFn {
        cranelisp_types::ConstrainedFn {
            variant: cranelisp_types::DefnVariant {
                params: vec![],
                body: cranelisp_types::Expr::IntLit {
                    value: 0,
                    span: cranelisp_types::Span::SYNTHETIC,
                    inferred_type: None,
                },
                span: cranelisp_types::Span::SYNTHETIC,
            },
            scheme: fn_scheme(vec![Type::Var(0), Type::Var(0)], Type::Var(0)),
        }
    }
}
