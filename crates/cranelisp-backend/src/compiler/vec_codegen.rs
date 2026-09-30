// Vec codegen: VecLit compilation and inline vec-get/vec-set/vec-push/vec-len.
//
// compile_vec_lit: allocate a Vec via runtime/vec_new, store each element
// compile_vec_get: bounds-checked element access with RC inc for heap elements
// compile_vec_set: COW inline + extern fallback
// compile_vec_push: COW inline + extern fallback
// compile_vec_len: inline load of len field
//
// Element inc/dec function generation for Vec copy-path externs.

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{
    ConcreteType, CranelispError, ErrorLocation, HeapHeader, MonoExpr, Span, Type,
};

use crate::heap::{self, HeapCategory, HeapVec, RcAtomicity};

use super::control_flow::emit_extern_call_in_wrapper;
use super::{FnCompiler, signature_heap_category};

/// Bundled operands for [`emit_vec_set_cow_core`] (argument-count budget — the
/// successor of the former `VecSetElem` bundle after the COW core was
/// builder-parameterized for the §12.7 wrapper emission).
///
/// The new-element consuming inc is the CALLER's decision (static sites gate on
/// `element_consuming_inc`; wrapper params arrive owned and transfer) — it is
/// NOT carried here and NOT emitted by the core.
pub(crate) struct VecSetCow {
    pub vec_val: Value,
    pub idx_val: Value,
    pub new_val: Value,
    /// Per-element-type RC inc fn pointer for the runtime copy helper's
    /// retained-element incs (iconst 0 for NeverHeap).
    pub inc_fn_ptr: Value,
    /// The OLD element's heap category (drives the mutate-in-place dec).
    pub old_elem_category: Option<HeapCategory>,
    pub dealloc_id: cranelift_module::FuncId,
    /// The consumed-source RC polarity (§13.3 Ruling 2) — whether the copy
    /// branch must release an owned reference to the source Vec.
    pub source_ownership: SourceOwnership,
    /// Increment-II static-uniqueness proof (§6.4): `true` when the source Vec
    /// node carries `unique_static == Some(true)` — proven a fresh unique single-
    /// use root. The dynamic `rc == 1` probe is then ELIDED (the branch is dead,
    /// take the in-place arm unconditionally); the reuse mechanism is unchanged,
    /// one load+cmp+brif fewer. `false` ⇒ emit the dynamic token verbatim
    /// (proof absent/`None` ⇒ Decision-24, the §2.2 else-arm discipline).
    pub elide_rc_check: bool,
}

/// Consumed-source RC polarity for the shared COW cores
/// (`design/backend/ownership-codegen.md` §13.7).
///
/// A COW op's **mutate** (`vec-set`) and **grow** (`vec-push`) branches (rc==1)
/// return the source box; its **copy** branch (rc>1) returns a new box. The
/// variant fixes what each branch does so that the result owns exactly one
/// reference on every branch:
///
/// | | mutate / grow | copy |
/// |---|---|---|
/// | `Owned` | transfers the consumed reference | releases the source |
/// | `Borrowed` | retains the returned box | releases nothing |
///
/// `Borrowed` has no retain-less form: a slot that keeps its reference also
/// releases it later (scope exit, a tail flush), so an unretained reused box
/// would be released twice (ACT-1024). Toggle-off (`CRANELISP_NO_OWNERSHIP`)
/// never builds `Borrowed`: the site counts a separately owned source instead,
/// so the runtime takes the copy branch (R14).
pub(crate) enum SourceOwnership {
    /// The site owns the reference it consumes: a fresh temporary, a `Var`
    /// whose site holds the consuming claim, or a wrapper/curry parameter.
    /// Carries the teardown materials the copy branch's release needs.
    Owned {
        vec_drop_func_id: cranelift_module::FuncId,
        elem_dec_fn_ptr: Value,
    },
    /// The source's slot keeps its reference and releases it later. Reachable
    /// only with analysis on.
    Borrowed,
}

/// Emit the copy-branch consumed-source release for a COW core (§13.7).
/// No-op for `Borrowed`; rc-checked `vec_drop` for `Owned`. Called AFTER the
/// copy extern (which reads + retains the shared source elements), so a
/// last-reference source teardown cannot free elements the new copy still holds.
fn release_consumed_source<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    vec_val: Value,
    source_ownership: &SourceOwnership,
) {
    if let SourceOwnership::Owned {
        vec_drop_func_id,
        elem_dec_fn_ptr,
    } = source_ownership
    {
        emit_vec_rc_dec_with_drop(
            builder,
            module,
            vec_val,
            *vec_drop_func_id,
            *elem_dec_fn_ptr,
        );
    }
}

/// Emit the mutate/grow-branch reused-source retention (§13.7). Those branches
/// return the source box, so a `Borrowed` source, whose slot keeps and later
/// releases its own reference, gives the result one more. `Owned` transfers
/// the consumed reference instead.
///
/// The symmetric partner of [`release_consumed_source`] (copy branch, release
/// iff `Owned`).
fn retain_reused_source<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    vec_val: Value,
    source_ownership: &SourceOwnership,
) {
    if matches!(source_ownership, SourceOwnership::Borrowed) {
        heap::emit_rc_inc(builder, module, vec_val);
    }
}

// =============================================================================
// §13.7 COW source classification. Pure, so the whole matrix is unit-testable
// without a live `FnCompiler`.
// =============================================================================

/// The vec builtins whose in-place branch returns the SOURCE pointer. `vec-get`/
/// `vec-len` are reads (no COW branch), so they are not COW sites.
pub(crate) fn is_cow_vec_op(name: &str) -> bool {
    matches!(name, "vec-set" | "vec-push")
}

/// Does this COW source have a **separate owner** that releases it
/// independently of this site? `claimed` says whether this exact site holds the
/// consuming claim, whose issuer suppresses the slot's own release.
///
/// An owned temporary has no separate owner: its sole reference transfers
/// here. The question is the value's provenance
/// (`fn_compiler::yields_owned_temporary`), not the node kind: an
/// `If`/`Match`/`Let` that yields a binding has one (FIXME 0781).
///
/// Analysis on, this is the `Borrowed` classification
/// ([`cow_source_is_borrowed`]); analysis off, it is the R14 force-count
/// condition (`FnCompiler::cow_source_needs_toggle_off_count`).
pub(crate) fn cow_source_has_separate_owner(source: &MonoExpr, claimed: bool) -> bool {
    !claimed && !crate::compiler::fn_compiler::yields_owned_temporary(source)
}

/// Is this COW source `Borrowed` (as opposed to `Owned`)? Only with analysis
/// on: toggle-off counts a separately owned source and lowers it `Owned` (R14).
/// The site's escape fact is not an input (§13.7).
pub(crate) fn cow_source_is_borrowed(source: &MonoExpr, claimed: bool, analysis_off: bool) -> bool {
    !analysis_off && cow_source_has_separate_owner(source, claimed)
}

/// **The one "is this node a COW-builtin site, and what is its source?"
/// question** — `Some(source)` iff `node` is an `Apply` that typecheck resolved
/// to a COW vec builtin (`ResolvedCall::BuiltinFn` naming `vec-set`/`vec-push`),
/// exactly as the producer's own dispatch keys (`compile_resolved_call`'s
/// `BuiltinFn` arm → `is_vec_primitive` → `compile_vec_op`).
///
/// `None` ⇒ not a COW-builtin site: a non-`Apply`, a **user-defined fn that
/// merely spells `vec-set`** (legal under `PreludeVariant::None`), a non-COW
/// builtin, or a trait/sig/curry dispatch. Both consuming-claim issuers
/// (`fn_compiler::consuming_cow_arguments`, `fn_compiler::return_cow_source_in_scope`)
/// ask this, never the callee's spelling (FIXME 0752, Principle 24).
pub(crate) fn cow_site_source(node: &MonoExpr) -> Option<&MonoExpr> {
    let MonoExpr::Apply {
        resolved_call,
        args,
        ..
    } = node
    else {
        return None;
    };
    let Some(cranelisp_types::ResolvedCall::BuiltinFn { name }) = resolved_call.as_deref() else {
        return None;
    };
    if !is_cow_vec_op(name.as_ref()) {
        return None;
    }
    args.first()
}

/// Read the increment-II `unique_static` write-path proof off a **fresh-
/// producing** Vec node (§6.4; `design/backend/ownership-codegen.md` HARD
/// requirement). The proof is a site fact emitted by typecheck on the value's
/// ORIGIN — a `VecLit` / `Apply` / `ConstrADT` / `StringLit` — never on a
/// consuming-use `Var` (which carries no `unique_static` field, so reading it
/// there would make every proof `None` ⇒ the optimization silently dead). A COW
/// site whose Vec arg IS such a fresh node (e.g. `(vec-set [1 2 3] 0 9)`) can
/// therefore elide its dynamic `rc == 1` probe; a `Var`-rooted COW keeps the
/// dynamic token (monotone-sound). `Some(true)` ⇒ proven unique; anything else
/// (`Some(false)` / `None` / a non-fresh node / analysis-off) ⇒ conservative.
pub(crate) fn node_unique_static(node: &MonoExpr) -> Option<bool> {
    match node {
        MonoExpr::VecLit { unique_static, .. }
        | MonoExpr::Apply { unique_static, .. }
        | MonoExpr::ConstrADT { unique_static, .. }
        | MonoExpr::StringLit { unique_static, .. } => *unique_static,
        // A `Var` (or any other node) carries no origin proof — conservative.
        _ => None,
    }
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Compile a Vec literal: `[e1 e2 e3]` → allocate Vec, store elements.
    pub(crate) fn compile_vec_lit(
        &mut self,
        elements: &[MonoExpr],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let vec_new_id = self
            .ctx
            .vec_new_func_id
            .ok_or_else(|| CranelispError::CodegenError {
                message: "runtime/vec_new not declared (need declare_intrinsics)".into(),
                location: ErrorLocation::from_span(span),
            })?;

        let len = elements.len() as i64;

        // Compile all element expressions first.
        let elem_vals: Vec<Value> = elements
            .iter()
            .map(|e| self.compile_expr(e))
            .collect::<Result<_, _>>()?;

        // Call runtime/vec_new(len) — allocates Vec struct + data buffer with len capacity.
        let len_val = self.builder.ins().iconst(types::I64, len);
        let vec_new_ref = self
            .module
            .declare_func_in_func(vec_new_id, self.builder.func);
        let call = self.builder.ins().call(vec_new_ref, &[len_val]);
        let vec_ptr = self.builder.inst_results(call)[0];

        // Load data_ptr from the Vec struct.
        let data_ptr = heap::heap_load(&mut self.builder, vec_ptr, HeapVec::DATA_PTR_OFFSET); // data_ptr: i64 (ptr-width)

        // Store each element into the data buffer at data_ptr + i * 8.
        //
        // Consuming discrimination (FIXME 0668 sub-fix — the vec-lit element store
        // routed through the SAME rule the call seam uses, `element_consuming_inc`
        // / DEF-2/DEF-3, Principle 7): a heap-typed `Var` element is an owned scope
        // binding whose scope-dec STILL fires, so the container must take its own
        // count (inc) — else the binding's scope-dec frees the element the returned
        // container holds (`(let [q [7 8 9]] [q])` → garbage BOTH toggles). A
        // temporary (literal / ctor call / fn result / COW result) starts at rc=1
        // and transfers its single reference into the Vec — no inc. The
        // discriminator is STRUCTURAL (Var-rootedness), analysis-independent, so
        // one rule is correct in BOTH toggles by construction; leak-side-safe (only
        // owned bindings inc); no loop interaction (recur args ride
        // `tail_transfer_skip`, not vec-lit). The match/alias-forward direction is
        // 0668's S114 design iteration — NOT touched here.
        for (i, (&val, elem)) in elem_vals.iter().zip(elements.iter()).enumerate() {
            let elem_category =
                signature_heap_category(&elem.ty().to_type(), Some(self.ctx.symbol_tables));
            match element_consuming_inc(elem, elem_category) {
                Some(HeapCategory::AlwaysHeap) => {
                    heap::emit_rc_inc(&mut self.builder, self.module, val);
                }
                Some(HeapCategory::Mixed) => {
                    heap::emit_rc_inc_guarded(&mut self.builder, self.module, val);
                }
                Some(HeapCategory::NeverHeap | HeapCategory::Value) | None => {}
            }
            let offset = (i * 8) as i32;
            heap::heap_store(&mut self.builder, val, data_ptr, offset);
        }

        // Set len = number of elements.
        let len_i64 = self.builder.ins().iconst(types::I64, len);
        heap::heap_store(&mut self.builder, len_i64, vec_ptr, HeapVec::LEN_OFFSET);

        Ok(vec_ptr)
    }

    /// Try to compile a Vec operation inline. Returns Some(val) if handled.
    ///
    /// Called from compile_apply when the callee is a known Vec primitive name.
    /// `args` are the original expressions (for last-use analysis).
    /// `arg_vals` are the pre-compiled argument Cranelift values.
    pub(crate) fn compile_vec_op(
        &mut self,
        name: &str,
        args: &[MonoExpr],
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Option<Value>, CranelispError> {
        match name {
            "vec-get" if args.len() == 2 => {
                let result = self.compile_vec_get(&args[0], arg_vals[0], arg_vals[1], span)?;
                // Drop temporary Vec after read — it's consumed but not returned.
                self.emit_vec_drop_if_temporary(&args[0], arg_vals[0], span)?;
                Ok(Some(result))
            }
            "vec-set" if args.len() == 3 => {
                let result = self.compile_vec_set(&args[0], &args[2], arg_vals, span)?;
                Ok(Some(result))
            }
            "vec-push" if args.len() == 2 => {
                let result = self.compile_vec_push(&args[0], &args[1], arg_vals, span)?;
                Ok(Some(result))
            }
            "vec-len" if args.len() == 1 => {
                let result = self.compile_vec_len(arg_vals[0]);
                // Drop temporary Vec after read — it's consumed but not returned.
                self.emit_vec_drop_if_temporary(&args[0], arg_vals[0], span)?;
                Ok(Some(result))
            }
            _ => Ok(None),
        }
    }

    /// Compile `vec-len`: inline load of len field at HeapVec::LEN_OFFSET.
    fn compile_vec_len(&mut self, vec_val: Value) -> Value {
        heap::heap_load(&mut self.builder, vec_val, HeapVec::LEN_OFFSET) // len: i64
    }

    /// Compile `vec-get`: bounds-checked element access.
    ///
    /// Delegates to the shared [`emit_vec_get_core`] (single source with the
    /// §12.7 fn-as-value wrapper emission — Principle 7); this method computes
    /// the element heap category from the Vec expression's concrete type.
    fn compile_vec_get(
        &mut self,
        vec_expr: &MonoExpr,
        vec_val: Value,
        idx_val: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let panic_id = self
            .ctx
            .panic_func_id
            .ok_or_else(|| CranelispError::CodegenError {
                message: "runtime/panic not declared".into(),
                location: ErrorLocation::from_span(span),
            })?;
        let elem_category = self
            .vec_elem_type(vec_expr)
            .map(|t| signature_heap_category(&t, Some(self.ctx.symbol_tables)));
        // §3.3 in-frame projection elision
        // (`design/backend/ownership-codegen.md` §3.3): elide the heap-element inc
        // when the CONSUMER of this exact `vec-get` requested it — the moded arg
        // path (`compile_entry_arg_list`) sets `elide_vecget_span` to
        // this node's span iff the read is a projection (site fact `provenance`)
        // being passed DIRECTLY into a `Borrowed` parameter. That is the sole
        // provably-safe elision: the borrowed element is consumed in-place by the
        // callee's borrow and never escapes the enclosing expression nor outlives
        // the root's fork-join-guaranteed liveness (the F1 machinery-tax collapse).
        // `None` (analysis off, or any read the consumer did not request) ⇒ inc
        // verbatim — byte-identical-off (§2.2).
        let elide_elem_inc = self.elide_vecget_span == Some(span);
        // §15 row 5 (tier-3 category-A, P25 "narrowing carries its check"): the
        // projection-inc elision is a narrowing; its check is the site fact. Pin
        // that elision fires ONLY with `elide_vecget_span` present — a future
        // refactor that sets `elide_elem_inc` from any other source (a bare /
        // analysis-off read) would drop a live element's inc → a UAF. Debug-only,
        // release-compiled-out, zero CLIF change.
        debug_assert!(
            !elide_elem_inc || self.elide_vecget_span == Some(span),
            "vec-get projection-inc elision fired without the `elide_vecget_span` \
             site fact (§3.3) — the borrowed-in-place consumer proof is absent"
        );
        emit_vec_get_core(
            &mut self.builder,
            self.module,
            panic_id,
            elem_category,
            vec_val,
            idx_val,
            span,
            elide_elem_inc,
        )
    }

    /// Compile `vec-set`: COW inline + extern fallback.
    ///
    /// arg_vals: [vec_val, idx_val, new_val]
    ///
    /// DEF-3 (FIXME 0417 — symmetric with `vec-push` / DEF-2): the new element
    /// follows the same consuming-Var rule as `vec-push` — the Vec gains a
    /// reference iff the element is a heap-typed **Var** (still owned by the
    /// enclosing scope, which dec's it at scope exit). A **temporary** element
    /// transfers its rc=1 reference into the Vec and MUST NOT be inc'd.
    ///
    /// The consuming inc is emitted **up-front in codegen** (gated by the shared
    /// `element_consuming_inc` predicate), exactly as `compile_vec_push` does —
    /// `vec_set_copy` does NOT inc the new `val` (it inc's only retained
    /// copied-over elements). This is the single division of labour: codegen
    /// owns the new-element consuming inc, the runtime owns the retained-element
    /// incs. (Prior to FIXME 0417 the COW path gated the inc here while the copy
    /// path relied on the runtime's unconditional inc + a codegen compensation
    /// dec — two opposite labour splits for one operation, now unified.)
    fn compile_vec_set(
        &mut self,
        vec_expr: &MonoExpr,
        elem_arg: &MonoExpr,
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let vec_val = arg_vals[0];
        let idx_val = arg_vals[1];
        let new_val = arg_vals[2];

        let elem_type = self.vec_elem_type(vec_expr);
        let inc_fn_ptr = self.resolve_elem_inc_fn_ptr(&elem_type, span)?;

        // Consuming inc for the new element, emitted up-front (mirrors
        // compile_vec_push). A heap-typed Var element forwarded into vec-set
        // (e.g. `c` in `(vec-set (cells-of g) idx c)`) is still owned by its
        // enclosing scope, which dec's it at scope exit; the Vec also stores a
        // reference. Without a caller-side inc the two race against the SAME
        // single reference. A temporary element transfers its rc=1 reference
        // into the Vec — no inc. Gated by the shared `element_consuming_inc`
        // decision (Principle 7), identical to vec-push (DEF-2).
        if let Some(elem_ty) = &elem_type {
            let category = signature_heap_category(elem_ty, Some(self.ctx.symbol_tables));
            match element_consuming_inc(elem_arg, category) {
                Some(HeapCategory::AlwaysHeap) => {
                    heap::emit_rc_inc(&mut self.builder, self.module, new_val);
                }
                Some(HeapCategory::Mixed) => {
                    heap::emit_rc_inc_guarded(&mut self.builder, self.module, new_val);
                }
                Some(HeapCategory::NeverHeap | HeapCategory::Value) | None => {}
            }
        }

        // Check if vec is at last use (compile-time).
        let is_last = self.is_vec_last_use(vec_expr);

        if is_last {
            // Runtime COW: check rc == 1. Shared core with the §12.7 wrapper
            // emission (Principle 7).
            let old_elem_category = elem_type
                .as_ref()
                .map(|t| signature_heap_category(t, Some(self.ctx.symbol_tables)));
            // Increment-II static-uniqueness proof (§6.4): if the Vec arg is a
            // FRESH-PRODUCING node proven unique (`unique_static == Some(true)`),
            // the dynamic rc==1 probe is dead — take the in-place arm and elide
            // the check. Read off the fresh node, NEVER a consuming-use Var.
            let elide_rc_check = node_unique_static(vec_expr) == Some(true);
            // R14 count-truth (toggle-off): count a live-`Var` source so rc≥2 ⇒
            // copy branch ⇒ conservative + correct. No-op analysis-ON.
            if self.cow_source_needs_toggle_off_count(vec_expr) {
                heap::emit_rc_inc(&mut self.builder, self.module, vec_val);
            }
            let source_ownership = self.cow_source_ownership(vec_expr, &elem_type, span)?;
            emit_vec_set_cow_core(
                &mut self.builder,
                self.module,
                VecSetCow {
                    vec_val,
                    idx_val,
                    new_val,
                    inc_fn_ptr,
                    old_elem_category,
                    dealloc_id: self.ctx.dealloc_func_id,
                    source_ownership,
                    elide_rc_check,
                },
                span,
            )
        } else {
            // Copy path (non-last-use Vec): call vec-set-copy extern. The runtime
            // inc's only the retained copied-over elements; the new `val`'s
            // consuming inc was already emitted up-front above.
            self.emit_extern_call(
                "vec-set-copy",
                &[vec_val, idx_val, new_val, inc_fn_ptr],
                span,
            )
        }
    }

    /// Compile `vec-push`: COW inline + extern fallback.
    ///
    /// arg_vals: [vec_val, new_val]
    fn compile_vec_push(
        &mut self,
        vec_expr: &MonoExpr,
        elem_arg: &MonoExpr,
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let vec_val = arg_vals[0];
        let new_val = arg_vals[1];

        let elem_type = self.vec_elem_type(vec_expr);
        let inc_fn_ptr = self.resolve_elem_inc_fn_ptr(&elem_type, span)?;

        // DEF-2: a heap-typed Var element forwarded into vec-push (e.g. the `x`
        // parameter of `(defn push2 [v x] (vec-push v x))`) is still owned by its
        // enclosing scope, which dec's it at scope exit. vec-push stores `new_val`
        // into the Vec WITHOUT inc'ing on the fast/grow/copy paths (the Vec takes
        // ownership of one reference). Without a caller-side consuming inc here, the
        // Vec's stored reference and the scope's dec race against the SAME single
        // reference — under-counting the element by 1 (COW then mutates an aliased
        // backing → over-count on read-back). Mirrors compile_consuming_arg_list
        // (Decision 24 §3.1): inc heap-typed Var args, transfer temporaries.
        if let Some(elem_ty) = &elem_type {
            let category = signature_heap_category(elem_ty, Some(self.ctx.symbol_tables));
            match element_consuming_inc(elem_arg, category) {
                Some(HeapCategory::AlwaysHeap) => {
                    heap::emit_rc_inc(&mut self.builder, self.module, new_val);
                }
                Some(HeapCategory::Mixed) => {
                    heap::emit_rc_inc_guarded(&mut self.builder, self.module, new_val);
                }
                Some(HeapCategory::NeverHeap | HeapCategory::Value) | None => {}
            }
        }

        let is_last = self.is_vec_last_use(vec_expr);

        if is_last {
            // Increment-II static-uniqueness proof (§6.4): elide the dynamic
            // rc==1 probe when the Vec arg is a fresh node proven unique.
            let elide_rc_check = node_unique_static(vec_expr) == Some(true);
            // R14 count-truth (toggle-off): count a live-`Var` source so rc≥2 ⇒
            // copy branch ⇒ conservative + correct. No-op analysis-ON.
            if self.cow_source_needs_toggle_off_count(vec_expr) {
                heap::emit_rc_inc(&mut self.builder, self.module, vec_val);
            }
            let source_ownership = self.cow_source_ownership(vec_expr, &elem_type, span)?;
            // Shared core with the §12.7 wrapper emission (Principle 7).
            emit_vec_push_cow_core(
                &mut self.builder,
                self.module,
                vec_val,
                new_val,
                inc_fn_ptr,
                source_ownership,
                elide_rc_check,
                span,
            )
        } else {
            // Copy path: call vec-push-copy extern.
            self.emit_extern_call("vec-push-copy", &[vec_val, new_val, inc_fn_ptr], span)
        }
    }

    // --- Helpers ---

    /// Extract the element type from a Vec expression's concrete type.
    ///
    /// `pub(crate)`: also read by `control_flow::fn_as_value::compile_auto_curry`
    /// to recover the element type from the applied Vec argument on the
    /// curried-vec-query path (§12.7).
    pub(crate) fn vec_elem_type(&self, vec_expr: &MonoExpr) -> Option<Type> {
        if let ConcreteType::ADT(fqtn, args) = vec_expr.ty()
            && fqtn.name.as_ref() == "Vec"
            && args.len() == 1
        {
            return Some(args[0].to_type());
        }
        None
    }

    /// Check if a Vec expression is at its last use (for COW eligibility).
    ///
    /// A non-`Var` expression is treated as unique ONLY when its value is this
    /// frame's to transfer (`fn_compiler::yields_owned_temporary`). The node
    /// kind is not the question: an `If`/`Match`/`Let` YIELDING a scope binding
    /// is not a `Var`, and the old unconditional `true` claimed uniqueness for
    /// a vector the enclosing scope still owns (FIXME 0781, the sibling of the
    /// `emit_vec_drop_if_temporary` shape test —
    /// `(let [w (vec-set (if b v v) 0 7)] (vec-get w 0))`, `--link` 134).
    pub(crate) fn is_vec_last_use(&self, vec_expr: &MonoExpr) -> bool {
        if let MonoExpr::Var { name, span, .. } = vec_expr {
            self.is_last_use(name, *span)
        } else {
            crate::compiler::fn_compiler::yields_owned_temporary(vec_expr)
        }
    }

    /// Release a temporary Vec expression's reference after an inline Vec op
    /// (vec-get / vec-len) consumed it. Named variables are cleaned up at scope
    /// exit; temporaries have no scope entry and would leak.
    ///
    /// The release is **rc-checked** (`emit_vec_rc_dec_with_drop`), NOT an
    /// unconditional `vec_drop`. A temporary Vec expression is not always the
    /// sole owner: when it is a borrowed ADT field — e.g. `(vec-get (gcells g) 0)`
    /// where `gcells` returns the inner Vec still owned by the live Grid `g` —
    /// the Vec's rc is > 1, and an unconditional `vec_drop` would free the data
    /// buffer + struct out from under the still-reachable Grid, corrupting the
    /// heap on the next write through the now-dangling pointer (the S97
    /// nested-ADT-wrapping-Vec double-use soundness defect; ring2-rc.md §5.5).
    /// The rc-checked dec frees only when this was the last reference (rc==1) —
    /// byte-identical to the old behaviour for a genuinely fresh rc==1 temporary,
    /// and correct (no free) for a shared borrowed-field temporary.
    fn emit_vec_drop_if_temporary(
        &mut self,
        vec_expr: &MonoExpr,
        vec_val: Value,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Release ONLY what this frame owns. The question is the value's
        // PROVENANCE (`fn_compiler::yields_owned_temporary`), never the node
        // kind: an `If`/`Match`/`Let` that merely YIELDS a scope binding is not
        // a `Var`, and the old `matches!(vec_expr, MonoExpr::Var { .. })` shape
        // test therefore dec'd a box the enclosing scope still owns
        // (FIXME 0781 — `(defn f [v b] (vec-get (if b v v) 0))`, `--link` 134).
        if !crate::compiler::fn_compiler::yields_owned_temporary(vec_expr) {
            return Ok(());
        }

        let vec_drop_id =
            self.ctx
                .vec_drop_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/vec_drop not declared".into(),
                    location: ErrorLocation::from_span(span),
                })?;

        let elem_type = self.vec_elem_type(vec_expr);
        let dec_fn_ptr = self.resolve_elem_dec_fn_ptr(&elem_type, span)?;

        emit_vec_rc_dec_with_drop(
            &mut self.builder,
            self.module,
            vec_val,
            vec_drop_id,
            dec_fn_ptr,
        );

        Ok(())
    }

    /// Resolve or generate a per-element-type inc function pointer.
    ///
    /// Returns iconst(0) for NeverHeap types (runtime skips the call).
    /// Returns a Cranelift func_addr for AlwaysHeap and Mixed types.
    fn resolve_elem_inc_fn_ptr(
        &mut self,
        elem_type: &Option<Type>,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let Some(ty) = &elem_type else {
            // Unknown element type: assume NeverHeap (safe default).
            return Ok(self.builder.ins().iconst(types::I64, 0));
        };

        let category = signature_heap_category(ty, Some(self.ctx.symbol_tables));
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

    /// Resolve or generate a per-element-type dec function pointer.
    ///
    /// Returns iconst(0) for NeverHeap types (runtime skips the call).
    /// For ADT element types with heap fields, builds a drop glue function
    /// so that fields are dec'd when the element reaches rc=0.
    /// The COW source classification for an in-place `vec-set`/`vec-push` site
    /// (§13.7).
    ///
    /// `Owned` when the source has no separate owner: a fresh temporary, a
    /// `Var` whose site holds the consuming claim
    /// ([`FnCompiler::holds_consuming_claim`]), or, with analysis off, any
    /// source (the site counted it, R14). Every other source is `Borrowed`.
    fn cow_source_ownership(
        &mut self,
        vec_expr: &MonoExpr,
        elem_type: &Option<Type>,
        span: Span,
    ) -> Result<SourceOwnership, CranelispError> {
        let claimed = self.holds_consuming_claim(vec_expr);
        if cow_source_is_borrowed(vec_expr, claimed, cranelisp_types::ownership_analysis_off()) {
            return Ok(SourceOwnership::Borrowed);
        }
        self.build_owned_source_release(elem_type, span)
    }

    /// Build the `SourceOwnership::Owned` release descriptor (the `vec_drop` fn-id
    /// + per-element dec fn ptr the copy-branch release needs).
    fn build_owned_source_release(
        &mut self,
        elem_type: &Option<Type>,
        span: Span,
    ) -> Result<SourceOwnership, CranelispError> {
        let vec_drop_func_id =
            self.ctx
                .vec_drop_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/vec_drop not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
                })?;
        let elem_dec_fn_ptr = self.resolve_elem_dec_fn_ptr(elem_type, span)?;
        Ok(SourceOwnership::Owned {
            vec_drop_func_id,
            elem_dec_fn_ptr,
        })
    }

    /// R14 count-truth (toggle-off): a separately owned COW source under
    /// `CRANELISP_NO_OWNERSHIP` is counted at the site, so its rc ≥ 2 sends the
    /// runtime to the copy branch and the in-place mutate never aliases a
    /// still-referenced vector. A claimed source and a fresh temporary have no
    /// separate owner. The toggle-inverted face of [`cow_source_is_borrowed`].
    fn cow_source_needs_toggle_off_count(&self, vec_expr: &MonoExpr) -> bool {
        cranelisp_types::ownership_analysis_off()
            && cow_source_has_separate_owner(vec_expr, self.holds_consuming_claim(vec_expr))
    }

    /// Resolve the per-element dec callback for `runtime/vec_drop`'s
    /// `(i64) -> i64` ABI — the canonical glue adapter (S118 slice S6).
    ///
    /// This used to build `runtime/vec_elem_dec_{heap,mixed}_{mangle}`, a
    /// SECOND per-instantiation named artifact keyed by a backend-local mangle
    /// rather than the types-owned identity. That was the same
    /// `drop-glue-underkey` class as the glue it wrapped, with a second key
    /// scheme; the registry's adapter over `drop_glue_symbol_name` is the one
    /// identity now. `iconst 0` is the ABI's null callback for a non-owning
    /// element type.
    fn resolve_elem_dec_fn_ptr(
        &mut self,
        elem_type: &Option<Type>,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let Some(id) = self.request_elem_dec_adapter(elem_type, span)? else {
            return Ok(self.builder.ins().iconst(types::I64, 0));
        };
        let func_ref = self.module.declare_func_in_func(id, self.builder.func);
        Ok(self.builder.ins().func_addr(types::I64, func_ref))
    }

    /// The registry request behind both `resolve_elem_dec_fn_ptr` forms — the
    /// only part that needs `&mut self` before a borrowed builder exists.
    fn request_elem_dec_adapter(
        &mut self,
        elem_type: &Option<Type>,
        span: Span,
    ) -> Result<Option<cranelift_module::FuncId>, CranelispError> {
        let Some(ty) = elem_type else {
            return Err(CranelispError::CodegenError {
                message: "Vec element release reached a missing element type; canonical drop glue requires a concrete type".into(),
                location: ErrorLocation::from_span(span),
            });
        };
        let concrete = cranelisp_types::ConcreteType::from_type(ty).map_err(|_| {
            CranelispError::CodegenError {
                message: format!(
                    "Vec element release reached a non-concrete element type {ty:?}; \
                     canonical drop glue is keyed on the concrete type and there is no \
                     shallow fallback (design/backend/transitive-drop-glue.md §3.4 D2)"
                ),
                location: ErrorLocation::from_span(span),
            }
        })?;
        self.glue
            .request_vec_elem_adapter(self.module, self.ctx.symbol_tables, &concrete)
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

    /// Build the `SourceOwnership::Owned` release descriptor for a COW core
    /// emitted into a wrapper/curry body (§13.3 Ruling 2): the source Vec's
    /// teardown func id + its per-element dec fn ptr. The op consumes an owned
    /// reference here (consuming-closure protocol), so the copy branch releases
    /// it via `vec_drop` (rc-checked). Mirrors the vec-get arm's teardown setup.
    fn owned_source_release(
        &mut self,
        elem_type: &Option<Type>,
        builder: &mut FunctionBuilder,
        span: Span,
    ) -> Result<SourceOwnership, CranelispError> {
        let vec_drop_func_id =
            self.ctx
                .vec_drop_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/vec_drop not declared".into(),
                    location: ErrorLocation::from_span(span),
                })?;
        let elem_dec_fn_ptr = self.resolve_elem_dec_fn_ptr_into(elem_type, builder, span)?;
        Ok(SourceOwnership::Owned {
            vec_drop_func_id,
            elem_dec_fn_ptr,
        })
    }

    fn resolve_elem_dec_fn_ptr_into(
        &mut self,
        elem_type: &Option<Type>,
        builder: &mut FunctionBuilder,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let Some(id) = self.request_elem_dec_adapter(elem_type, span)? else {
            return Ok(builder.ins().iconst(types::I64, 0));
        };
        let func_ref = self.module.declare_func_in_func(id, builder.func);
        Ok(builder.ins().func_addr(types::I64, func_ref))
    }

    /// Resolve or generate a per-element-type inc function pointer into a
    /// specific builder (for wrapper-body emission — the mirror of
    /// `resolve_elem_dec_fn_ptr_into`, and the `_into` sibling of
    /// `resolve_elem_inc_fn_ptr`, which emits into `self.builder`).
    fn resolve_elem_inc_fn_ptr_into(
        &mut self,
        elem_type: &Option<Type>,
        builder: &mut FunctionBuilder,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let Some(ty) = &elem_type else {
            return Ok(builder.ins().iconst(types::I64, 0));
        };

        let category = signature_heap_category(ty, Some(self.ctx.symbol_tables));
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
    /// RC polarity: every wrapper param arrives OWNED (consuming closure
    /// protocol), so the emission takes the owned-temporary polarity uniformly:
    ///
    /// - `vec-get` — bounds check + element load + element inc (per element
    ///   heap category), then a vec-aware rc-checked release of the consumed
    ///   Vec (the temporary branch of `emit_vec_drop_if_temporary`).
    /// - `vec-len` — length load, then the same rc-checked Vec release.
    /// - `vec-set` / `vec-push` — the element's reference TRANSFERS into the
    ///   Vec with NO consuming inc (the temporary branch of
    ///   `element_consuming_inc`), and the Vec is trivially at last use, so
    ///   the COW rc==1 path applies (the shared cores).
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
        elem_type: &Option<Type>,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let elem_category = elem_type
            .as_ref()
            .map(|t| signature_heap_category(t, Some(self.ctx.symbol_tables)));
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
                let panic_id =
                    self.ctx
                        .panic_func_id
                        .ok_or_else(|| CranelispError::CodegenError {
                            message: "runtime/panic not declared".into(),
                            location: ErrorLocation::from_span(span),
                        })?;
                let vec_drop_id =
                    self.ctx
                        .vec_drop_func_id
                        .ok_or_else(|| CranelispError::CodegenError {
                            message: "runtime/vec_drop not declared".into(),
                            location: ErrorLocation::from_span(span),
                        })?;
                let dec_fn_ptr = self.resolve_elem_dec_fn_ptr_into(elem_type, builder, span)?;
                let elem = emit_vec_get_core(
                    builder,
                    self.module,
                    panic_id,
                    elem_category,
                    params[0],
                    params[1],
                    span,
                    // Value-use wrapper body: the projection ALWAYS materializes
                    // (the closure protocol owes a fresh owned value), and the Vec
                    // arrives owned and is released below — never a borrowed
                    // projection. So the element inc is never elided here (§3.3).
                    false,
                )?;
                // Release the consumed (owned) Vec — rc-checked, and AFTER the
                // element inc inside the core, so the element survives a
                // last-reference Vec teardown.
                emit_vec_rc_dec_with_drop(builder, self.module, params[0], vec_drop_id, dec_fn_ptr);
                Ok(elem)
            }
            ("vec-set", 3) => {
                let inc_fn_ptr = self.resolve_elem_inc_fn_ptr_into(elem_type, builder, span)?;
                // Wrapper / curry body: params arrive OWNED (consuming-closure
                // protocol), so the copy branch must release the source Vec's
                // owned reference (§13.3 Ruling 2 — the FIXME-0474 cure). The
                // vec-get arm's release above is the precedent.
                let source_ownership = self.owned_source_release(elem_type, builder, span)?;
                emit_vec_set_cow_core(
                    builder,
                    self.module,
                    VecSetCow {
                        vec_val: params[0],
                        idx_val: params[1],
                        new_val: params[2],
                        inc_fn_ptr,
                        old_elem_category: elem_category,
                        dealloc_id: self.ctx.dealloc_func_id,
                        source_ownership,
                        // Wrapper/curry body: the Vec arrives as an OWNED closure
                        // param (a `Value`, not a fact-bearing MonoExpr node), so
                        // no static uniqueness proof is available here — keep the
                        // dynamic rc==1 token (conservative, §6.4).
                        elide_rc_check: false,
                    },
                    span,
                )
            }
            ("vec-push", 2) => {
                let inc_fn_ptr = self.resolve_elem_inc_fn_ptr_into(elem_type, builder, span)?;
                // Wrapper / curry body: params arrive owned — release the source
                // on the copy branch (§13.3 Ruling 2).
                let source_ownership = self.owned_source_release(elem_type, builder, span)?;
                emit_vec_push_cow_core(
                    builder,
                    self.module,
                    params[0],
                    params[1],
                    inc_fn_ptr,
                    source_ownership,
                    // Wrapper/curry body: no fact-bearing node — dynamic token.
                    false,
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

/// Shared emission core for `vec-get`: bounds check (trap via `runtime/panic`)
/// + element load + element RC inc per `elem_category`.
///
/// Builder-parameterized (the `emit_adt_construct_into` precedent) so ONE body
/// serves both the statically-resolved inline site (`compile_vec_get`, over
/// `self.builder`) and the §12.7 fn-as-value / auto-curry wrapper bodies
/// (`emit_vec_query_into`), which build in a separate Cranelift context.
/// Consuming the Vec (the temporary/owned release) is the CALLER's decision —
/// not emitted here.
#[allow(clippy::too_many_arguments)] // +1 for the §3.3 elide_elem_inc gate
pub(crate) fn emit_vec_get_core<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    panic_id: cranelift_module::FuncId,
    elem_category: Option<HeapCategory>,
    vec_val: Value,
    idx_val: Value,
    span: Span,
    // §3.3 in-frame projection elision
    // (`design/backend/ownership-codegen.md` §3.3): when `true` the heap-element
    // materialization inc is SKIPPED — the read is a borrowed projection rooted
    // in a live root (the enclosing `Apply`'s `provenance` fact). `false` ⇒ the
    // inc is emitted verbatim (byte-identical-off, and the value-use wrapper path
    // which always materializes).
    elide_elem_inc: bool,
) -> Result<Value, CranelispError> {
    // Load len from Vec.
    let len = heap::heap_load(builder, vec_val, HeapVec::LEN_OFFSET);

    // Bounds check: idx < 0 || idx >= len → panic.
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

    // Panic path: call runtime/panic with error message.
    builder.switch_to_block(panic_block);
    builder.seal_block(panic_block);
    emit_vec_bounds_panic(builder, module, panic_id, span)?;

    // OK path: load element.
    builder.switch_to_block(ok_block);
    builder.seal_block(ok_block);

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

    // If element type is heap, emit RC inc on the loaded value — UNLESS this read
    // is a borrowed projection (§3.3): then the element is a view into the still-
    // live root and its inc is elided (the F1 machinery-tax collapse). The root's
    // owner keeps the element alive; a consuming use of the projection
    // materializes it.
    if !elide_elem_inc {
        match elem_category {
            Some(HeapCategory::AlwaysHeap) => {
                heap::emit_rc_inc(builder, module, elem);
            }
            Some(HeapCategory::Mixed) => {
                heap::emit_rc_inc_guarded(builder, module, elem);
            }
            Some(HeapCategory::NeverHeap | HeapCategory::Value) | None => {}
        }
    }

    Ok(elem)
}

/// Shared emission core for the `vec-set` COW path: rc==1 → mutate-in-place
/// (dec old element, store new, return the same Vec); rc>1 → `vec-set-copy`
/// extern (the runtime inc's only the retained copied-over elements).
///
/// Builder-parameterized single source (Principle 7) for the static
/// `compile_vec_set` last-use arm and the §12.7 wrapper emission. The
/// new-element consuming inc is the CALLER's decision (static sites gate on
/// `element_consuming_inc`; wrapper params arrive owned and transfer) — both
/// sub-paths store `new_val` WITHOUT an additional inc.
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
        old_elem_category,
        dealloc_id,
        source_ownership,
        elide_rc_check,
    } = op;

    // Uniqueness discriminator (§6.4): with a static proof (`elide_rc_check`) the
    // in-place arm is proven-taken — emit `is_unique = true` and skip the rc
    // load+cmp (the copy block is then dead, DCE'd). Absent the proof, load rc
    // and compare == 1 (the dynamic token, verbatim pre-II behaviour).
    let is_unique = if elide_rc_check {
        builder.ins().iconst(types::I64, 1)
    } else {
        let rc = heap::heap_load(builder, vec_val, HeapHeader::RC_OFFSET);
        let one = builder.ins().iconst(types::I64, 1);
        builder.ins().icmp(IntCC::Equal, rc, one)
    };

    let mutate_block = builder.create_block();
    let copy_block = builder.create_block();
    let merge_block = builder.create_block();
    builder.append_block_param(merge_block, types::I64);

    builder
        .ins()
        .brif(is_unique, mutate_block, &[], copy_block, &[]);

    // Mutate-in-place path: dec old element, store new, return same vec.
    builder.switch_to_block(mutate_block);
    builder.seal_block(mutate_block);

    // Increment-II reuse tally (§6.5): the in-place arm reuses the owned buffer
    // (a reuse HIT — dynamically taken, or the proof-elided codegen-certain hit).
    // Runtime tally gated on the codegen-time `CRANELISP_RC_STATS` switch (off ⇒
    // no emitted IR).
    heap::emit_rc_stat_call_gated(builder, module, "runtime/reuse_hit");

    // Load data_ptr and old element.
    let data_ptr = heap::heap_load(builder, vec_val, HeapVec::DATA_PTR_OFFSET);
    let eight = builder.ins().iconst(types::I64, 8);
    let byte_off = builder.ins().imul(idx_val, eight);
    let elem_addr = builder.ins().iadd(data_ptr, byte_off);
    let old_elem = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), elem_addr, 0);

    // Dec the old element (if heap type).
    match old_elem_category {
        Some(HeapCategory::AlwaysHeap) => {
            heap::emit_rc_dec(builder, module, old_elem, dealloc_id, None);
        }
        Some(HeapCategory::Mixed) => {
            heap::emit_rc_dec_guarded(builder, module, old_elem, dealloc_id, None, true);
        }
        Some(HeapCategory::NeverHeap | HeapCategory::Value) | None => {}
    }

    // Store new value (the consuming inc was the caller's decision — none here).
    builder
        .ins()
        .store(MemFlags::trusted(), new_val, elem_addr, 0);

    // §13.7: a Borrowed source's result takes its own reference on this
    // same-pointer return.
    retain_reused_source(builder, module, vec_val, &source_ownership);

    builder.ins().jump(merge_block, &[vec_val]);

    // Copy path: call vec-set-copy extern.
    builder.switch_to_block(copy_block);
    builder.seal_block(copy_block);
    // Increment-II reuse tally (§6.5): the copy arm cannot reuse (rc>1) — a
    // reuse MISS. Gated on `CRANELISP_RC_STATS` (off ⇒ no emitted IR).
    heap::emit_rc_stat_call_gated(builder, module, "runtime/reuse_miss");
    let copy_result = emit_extern_call_in_wrapper(
        builder,
        module,
        "vec-set-copy",
        &[vec_val, idx_val, new_val, inc_fn_ptr],
        span,
    )?;
    // §13.3 Ruling 2: the copy branch returns a NEW Vec, so release the
    // consumed source's owned reference here (iff Owned). AFTER the copy extern
    // so its retained-element incs land before a last-reference source teardown.
    release_consumed_source(builder, module, vec_val, &source_ownership);
    builder.ins().jump(merge_block, &[copy_result]);

    // Merge.
    builder.switch_to_block(merge_block);
    builder.seal_block(merge_block);
    Ok(builder.block_params(merge_block)[0])
}

/// Shared emission core for the `vec-push` COW path: rc==1 → len<cap fast
/// store / `vec-push-grow` extern; rc>1 → `vec-push-copy` extern.
///
/// Builder-parameterized single source (Principle 7) for the static
/// `compile_vec_push` last-use arm and the §12.7 wrapper emission. The
/// new-element consuming inc is the CALLER's decision — not emitted here.
#[allow(clippy::too_many_arguments)] // +1 for the §6.4 elide_rc_check proof gate
pub(crate) fn emit_vec_push_cow_core<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    vec_val: Value,
    new_val: Value,
    inc_fn_ptr: Value,
    source_ownership: SourceOwnership,
    elide_rc_check: bool,
    span: Span,
) -> Result<Value, CranelispError> {
    // Uniqueness discriminator (§6.4): a static proof (`elide_rc_check`) makes the
    // unique arm proven-taken — emit `is_unique = true`, skip the rc load+cmp (the
    // copy block is dead, DCE'd). Absent the proof, the dynamic rc==1 token.
    let is_unique = if elide_rc_check {
        builder.ins().iconst(types::I64, 1)
    } else {
        let rc = heap::heap_load(builder, vec_val, HeapHeader::RC_OFFSET);
        let one = builder.ins().iconst(types::I64, 1);
        builder.ins().icmp(IntCC::Equal, rc, one)
    };

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

    // §13.7: both the fast and grow sub-paths return the source pointer; one
    // retention in `unique_block` covers both, for a Borrowed source.
    retain_reused_source(builder, module, vec_val, &source_ownership);

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
    // §13.3 Ruling 2: copy branch returns a NEW Vec — release the consumed
    // source's owned reference here (iff Owned), after the copy's retained incs.
    release_consumed_source(builder, module, vec_val, &source_ownership);
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
    emit_vec_rc_dec_with_drop_atomicity(
        builder,
        module,
        vec_val,
        vec_drop_func_id,
        elem_dec_fn_ptr,
        RcAtomicity::Atomic,
    );
}

/// Vec-aware RC dec with per-site [`RcAtomicity`] (B3.3, §5.2 — the one shared
/// vec-inventory item that IS per-site-emitted, so it CAN be gated). `Atomic`
/// is byte-identical to the pre-B3.3 path; `NonAtomic` emits the plain
/// load/`isub`/store count update (sound only on a Confined vec cell). The
/// `old == 1` → `vec_drop` free path (element decs + buffer free + dealloc) is
/// unchanged in both arms.
pub(crate) fn emit_vec_rc_dec_with_drop_atomicity<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    vec_val: Value,
    vec_drop_func_id: cranelift_module::FuncId,
    elem_dec_fn_ptr: Value,
    atomicity: RcAtomicity,
) {
    use cranelift_codegen::ir::AtomicRmwOp;

    let cont_block = builder.create_block();

    // §15 row 6 (tier-3 category-B): route the Vec-aware dec through the shared
    // `CRANELISP_RC_DEC_CHECK` seam so the DEC_CHECK lane sees the COW copy-branch
    // source release + every vec teardown/scope-exit dec — not only the header-dec
    // inline. Off by default ⇒ no emitted call ⇒ byte-identical codegen.
    crate::heap::emit_rc_dec_check_gated(builder, module, vec_val);

    // Dec RC — atomic_rmw, or the non-atomic plain load/isub/store arm on a
    // Confined vec cell (B3.3). The pre-decrement value stands in for the
    // atomic_rmw's returned old value in the non-atomic arm.
    let rc_addr = builder
        .ins()
        .iadd_imm(vec_val, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    let old_rc = if crate::heap::use_nonatomic_arm(atomicity) {
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

/// Emit a bounds-check panic for vec-get.
fn emit_vec_bounds_panic<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    panic_func_id: cranelift_module::FuncId,
    span: Span,
) -> Result<(), CranelispError> {
    // runtime/panic(msg_ptr, msg_len) records the error and returns; we return the sentinel.
    // We store the error message in a data section.
    let msg = b"vec-get: index out of bounds";
    let data_id =
        module
            .declare_anonymous_data(false, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare panic data: {e}"),
                location: ErrorLocation::from_span(span),
            })?;
    let mut desc = cranelift_module::DataDescription::new();
    desc.define(msg.to_vec().into_boxed_slice());
    module
        .define_data(data_id, &desc)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to define panic data: {e}"),
            location: ErrorLocation::from_span(span),
        })?;

    let gv = module.declare_data_in_func(data_id, builder.func);
    let msg_ptr = builder.ins().global_value(types::I64, gv);
    let msg_len = builder.ins().iconst(types::I64, msg.len() as i64);

    let panic_ref = module.declare_func_in_func(panic_func_id, builder.func);
    builder.ins().call(panic_ref, &[msg_ptr, msg_len]);

    // runtime_panic sets a thread-local error flag and returns.
    // Return a dummy 0 value — the caller checks take_runtime_error().
    let dummy = builder.ins().iconst(types::I64, 0);
    builder.ins().return_(&[dummy]);

    Ok(())
}

/// Decide whether a Vec-mutating primitive's new element argument needs a
/// caller-side consuming RC inc, and of which form. Shared by `vec-push`
/// (DEF-2) and `vec-set` (DEF-3) — the single source of the consuming-Var rule
/// for Vec element ownership (Principle 7).
///
/// Under the uniform consuming convention (Decision 24 / ring2-rc.md §3.1), a
/// `vec-push` / `vec-set` stores `new_val` into the Vec, transferring one
/// reference to the Vec's ownership (the Vec's drop glue dec's the element when
/// the Vec dies). For a **temporary** element expression (e.g. `(Box i)`) that
/// started at rc=1, this transfer is balanced — no caller action. But for a
/// **Var** element (e.g. the `x` parameter inside `(defn push2 [v x] (vec-push
/// v x))`, or `c` in `(vec-set (cells-of g) idx c)`) the Var is still owned by
/// its enclosing scope, which dec's it at scope exit; without a caller-side inc
/// the Vec's stored reference and the scope's dec race against the SAME single
/// reference:
///
///   - DEF-2 (`vec-push`): under-count by 1 — the heap element is freed too
///     early / read stale (a Var forwarded through a wrapper). The fix ADDS the
///     inc for the Var case.
///   - DEF-3 (`vec-set`): the prior code inc'd UNCONDITIONALLY, so a
///     **temporary** element (which transfers rc=1) got a permanent extra
///     reference the Vec never drops — a leak. The fix makes the inc
///     conditional, REMOVING it for temporaries while keeping it for Vars.
///
/// Both defects converge on the same end state: inc iff the element is a
/// heap-typed **Var**. This mirrors `compile_consuming_arg_list` exactly: inc
/// heap-typed Var arguments, leave temporaries to transfer. `NeverHeap`
/// elements (Int) and non-Var element expressions return `None` (no inc) —
/// which is why the scalar control and the direct-temporary path are unaffected.
///
/// Returns `Some(category)` (AlwaysHeap or Mixed) when the element is a heap-typed
/// Var that must be inc'd; `None` otherwise.
fn element_consuming_inc(elem_arg: &MonoExpr, elem_category: HeapCategory) -> Option<HeapCategory> {
    match elem_arg {
        MonoExpr::Var { .. } => match elem_category {
            HeapCategory::AlwaysHeap => Some(HeapCategory::AlwaysHeap),
            HeapCategory::Mixed => Some(HeapCategory::Mixed),
            HeapCategory::NeverHeap | HeapCategory::Value => None,
        },
        // Temporaries (constructor calls, function results, literals, …) start at
        // rc=1 and transfer their single reference into the Vec — no caller inc.
        _ => None,
    }
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
mod vec_push_rc_tests;

#[cfg(test)]
mod vec_set_rc_tests;

#[cfg(test)]
mod cow_polarity_tests;

#[cfg(test)]
mod cow_gate_tests;

#[cfg(test)]
mod cow_claim_tests;

#[cfg(test)]
mod temp_drop_rc_tests;

#[cfg(test)]
mod reuse_proof_tests;

#[cfg(test)]
mod vec_lit_consume_tests;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod element_release_tests;

#[cfg(test)]
mod guard_convergence_tests;
