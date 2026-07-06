//! RC / drop-glue emission and the heap classification it keys on.
//!
//! This is the single home for the heap-class match (`signature_heap_category`)
//! that the drop-glue field-dec sites and `pop_scope_with_cleanup`'s guard read
//! (audit Part 2 §2.7). The pure type-substitution helpers
//! (`build_adt_type_substitution`, `collect_var_ids_from_type`,
//! `substitute_type_inline`, `find_var_type_in_expr`) feed the drop-glue
//! field-dec path and live here too.

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use cranelisp_types::{ConcreteType, ModuleFullPath, MonoExpr, Symbol, SymbolTable, Type};

use crate::heap::{self, HeapCategory, RcAtomicity};

use super::{CtorMeta, FnCompiler};

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{

    /// Emit inline drop glue for an ADT: dec each AlwaysHeap field.
    ///
    /// This is a temporary measure until proper drop glue functions are
    /// generated. It handles the common case of ADTs with String or other
    /// heap-typed fields.
    ///
    /// For Mixed ADTs (with both nullary and data constructors), the field
    /// dec is guarded by a heap-pointer check: if the value is a bare
    /// nullary tag, no fields exist to dec.
    fn emit_inline_drop_glue(
        &mut self,
        adt_val: Value,
        ty: &Type,
        dealloc: FuncId,
        is_mixed: bool,
    ) {
        let fqtn = match ty {
            Type::ADT(fqtn, _) => fqtn,
            _ => return, // Not an ADT; nothing to do.
        };

        let type_def = match self.ctx.lookup_type_def(fqtn) {
            Some(td) => td,
            None => return,
        };

        // Constructor metadata is reconstructed from each ctor's
        // DefKind::Constructor Def post-S70.
        let all_ctors = self.ctx.constructor_metas(&type_def);
        let subst = build_adt_type_substitution(ty, &all_ctors);

        // Collect data constructors (those with fields).
        let data_ctors: Vec<CtorMeta> = all_ctors
            .into_iter()
            .filter(|c| !c.fields.is_empty())
            .collect();

        if data_ctors.is_empty() {
            return; // No data constructors, nothing to drop.
        }

        // Check if any data constructor has heap-typed fields.
        let has_heap_fields = data_ctors.iter().any(|ctor| {
            ctor.fields.iter().any(|f| {
                let resolved = substitute_type_inline(&f.ty, &subst);
                matches!(
                    signature_heap_category(&resolved, Some(self.ctx.symbol_tables)),
                    HeapCategory::AlwaysHeap | HeapCategory::Mixed
                )
            })
        });

        if !has_heap_fields {
            return; // No heap fields to drop.
        }

        // For Mixed ADTs, guard the field dec with a heap-pointer check.
        let cont_block = if is_mixed {
            Some(self.emit_mixed_adt_heap_guard(adt_val))
        } else {
            None
        };

        // Emit field decs for each data constructor.
        self.emit_drop_glue_field_decs(adt_val, &data_ctors, &subst, dealloc);

        // Jump to continuation for Mixed guard.
        if let Some(cont) = cont_block {
            self.builder.ins().jump(cont, &[]);
            self.builder.switch_to_block(cont);
            self.builder.seal_block(cont);
        }
    }

    /// Emit a heap-pointer guard for Mixed ADTs in drop glue.
    ///
    /// Creates a branch that skips field dec if the value is a bare nullary
    /// tag (below the heap threshold). Returns the continuation block that
    /// the caller must jump to when field dec is done.
    fn emit_mixed_adt_heap_guard(&mut self, adt_val: Value) -> Block {
        let cont = self.builder.create_block();
        let glue_block = self.builder.create_block();

        let threshold = self
            .builder
            .ins()
            .iconst(types::I64, heap::NULLARY_THRESHOLD_I64);
        let is_heap = self.builder.ins().icmp(
            IntCC::UnsignedGreaterThanOrEqual,
            adt_val,
            threshold,
        );
        self.builder
            .ins()
            .brif(is_heap, glue_block, &[], cont, &[]);

        self.builder.switch_to_block(glue_block);
        self.builder.seal_block(glue_block);
        cont
    }

    /// Emit field decs for data constructors in drop glue.
    ///
    /// For a single data constructor, dec fields directly.
    /// For multiple data constructors, emit tag-based dispatch
    /// (branch chain like match codegen).
    fn emit_drop_glue_field_decs(
        &mut self,
        adt_val: Value,
        data_ctors: &[CtorMeta],
        subst: &std::collections::HashMap<cranelisp_types::TypeId, Type>,
        dealloc: FuncId,
    ) {
        use crate::heap::HeapAdt;

        if data_ctors.len() == 1 {
            let ctor = &data_ctors[0];
            self.emit_field_decs(adt_val, ctor, subst, dealloc);
        } else {
            // Multiple data constructors: load the tag and branch to the
            // correct field-dec block for each variant.
            let heap_tag = heap::heap_load(
                &mut self.builder,
                adt_val,
                HeapAdt::TAG_OFFSET,
            );

            let done_block = self.builder.create_block();

            for (idx, ctor) in data_ctors.iter().enumerate() {
                let ctor_block = self.builder.create_block();
                let next_block = if idx + 1 < data_ctors.len() {
                    self.builder.create_block()
                } else {
                    // Last data constructor: fallthrough to done.
                    done_block
                };

                let tag_val = self.builder.ins().iconst(types::I64, ctor.tag as i64);
                let cmp = self.builder.ins().icmp(IntCC::Equal, heap_tag, tag_val);
                self.builder.ins().brif(cmp, ctor_block, &[], next_block, &[]);

                self.builder.switch_to_block(ctor_block);
                self.builder.seal_block(ctor_block);

                self.emit_field_decs(adt_val, ctor, subst, dealloc);
                self.builder.ins().jump(done_block, &[]);

                if idx + 1 < data_ctors.len() {
                    self.builder.switch_to_block(next_block);
                    self.builder.seal_block(next_block);
                }
            }

            self.builder.switch_to_block(done_block);
            self.builder.seal_block(done_block);
        }
    }

    /// Emit rc_dec for each heap-typed field of a single constructor.
    ///
    /// Used by `emit_inline_drop_glue` for both the single-constructor case
    /// and within each branch of the multi-constructor tag dispatch.
    ///
    /// For ADT-typed fields, uses `emit_rc_dec_with_inline_drop_glue` to
    /// recursively handle nested ADT field cleanup when the field's RC
    /// reaches 0. For non-ADT heap types (String, closures), uses plain
    /// `emit_rc_dec` since they have no sub-fields.
    fn emit_field_decs(
        &mut self,
        adt_val: Value,
        ctor: &CtorMeta,
        subst: &std::collections::HashMap<cranelisp_types::TypeId, Type>,
        dealloc: FuncId,
    ) {
        use crate::heap::HeapAdt;

        for (i, field) in ctor.fields.iter().enumerate() {
            let resolved_ty = substitute_type_inline(&field.ty, subst);
            let category = signature_heap_category(&resolved_ty, Some(self.ctx.symbol_tables));
            match category {
                HeapCategory::AlwaysHeap => {
                    let field_val = heap::heap_load(
                        &mut self.builder,
                        adt_val,
                        HeapAdt::field_offset(i),
                    );
                    // Vec-typed fields must route through vec_drop, not
                    // dealloc — otherwise elements and the data buffer leak.
                    if let Some(elem_ty) =
                        crate::compiler::vec_codegen::vec_element_type(&resolved_ty)
                    {
                        let elem_ty = elem_ty.clone();
                        // span not readily available here; use a synthetic span.
                        let span = cranelisp_types::Span::new(0, 0);
                        // Failing here is a backend-setup invariant breach
                        // (vec_drop must be declared whenever Vec types are
                        // in play). Swallow the Result rather than propagate
                        // — emit_field_decs is infallible by signature.
                        let _ = self.emit_vec_aware_rc_dec(field_val, &elem_ty, span, RcAtomicity::Atomic);
                    } else if matches!(resolved_ty, Type::ADT(_, _)) {
                        // For ADT-typed fields, recursively handle nested field cleanup.
                        self.emit_rc_dec_with_inline_drop_glue(
                            field_val, &resolved_ty, dealloc, false,
                        );
                    } else if matches!(resolved_ty, Type::Fn(_, _)) {
                        self.emit_closure_dec_inline(field_val, dealloc);
                    } else {
                        heap::emit_rc_dec(
                            &mut self.builder,
                            self.module,
                            field_val,
                            dealloc,
                            None,
                        );
                    }
                }
                HeapCategory::Mixed => {
                    let field_val = heap::heap_load(
                        &mut self.builder,
                        adt_val,
                        HeapAdt::field_offset(i),
                    );
                    // Mixed fields may be ADTs with nested heap fields.
                    if matches!(resolved_ty, Type::ADT(_, _)) {
                        self.emit_rc_dec_with_inline_drop_glue(
                            field_val, &resolved_ty, dealloc, true,
                        );
                    } else {
                        heap::emit_rc_dec_guarded(
                            &mut self.builder,
                            self.module,
                            field_val,
                            dealloc,
                            None,
                            true,
                        );
                    }
                }
                HeapCategory::NeverHeap | HeapCategory::Value => {}
            }
        }
    }

    /// If `skip_var` is None and the return value has a heap type, emit
    /// `rc_inc` on the value so it survives the subsequent scope cleanup.
    /// Scope cleanup will dec all heap bindings, which may include the
    /// value being returned (when the body is a non-trivial expression like
    /// `if` or `match` that resolves to a scope binding). The caller will
    /// dec it later, so the net ownership is correct.
    pub(crate) fn protect_return_value(
        &mut self,
        skip_var: &Option<Symbol>,
        body_val: Value,
        body: &MonoExpr,
    ) {
        if skip_var.is_some() {
            return; // The skip_var mechanism already protects the return value.
        }
        // Fresh allocations (Lambda, StringLit) cannot be the same as any
        // scope binding, so scope cleanup cannot affect them. Skip protect.
        if matches!(body, MonoExpr::Lambda { .. } | MonoExpr::StringLit { .. }) {
            return;
        }
        // Only protect if the current scope has heap-typed bindings that
        // scope cleanup will dec. Borrowed vars are skipped by
        // `pop_scope_with_cleanup`, so their presence alone does NOT justify
        // a protective inc — emitting one would leave the return value with
        // an inflated RC that the caller cannot balance.
        let has_cleanup_targets = self.scope_stack.last().is_some_and(|frame| {
            frame.iter().any(|name| {
                if self.borrowed_vars.contains(name) {
                    return false;
                }
                self.variable_types.get(name).is_some_and(|ty| self.is_heap_type(ty))
            })
        });
        if !has_cleanup_targets {
            return;
        }
        let category = HeapCategory::classify(body.ty(), Some(self.ctx.symbol_tables));
        // B3.3 (§5.1): the materialization inc on the returned cell goes
        // non-atomic when the producing node is Confined. `body` is the exact
        // producing node (the let/fn-body return expression), so its `confined`
        // site fact drives the atomicity. Fact-absent (analysis off) ⇒ Atomic,
        // byte-identical.
        let atomicity = self.rc_atomicity_for_node(body);
        match category {
            HeapCategory::AlwaysHeap => {
                heap::emit_rc_inc_atomicity(&mut self.builder, self.module, body_val, atomicity);
            }
            HeapCategory::Mixed => {
                heap::emit_rc_inc_guarded_atomicity(
                    &mut self.builder, self.module, body_val, atomicity,
                );
            }
            HeapCategory::NeverHeap | HeapCategory::Value => {}
        }
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
        use crate::heap::HeapClosure;
        use cranelisp_types::HeapHeader;
        use cranelift_codegen::ir::AtomicRmwOp;

        let cont_block = self.builder.create_block();

        // Decrement RC.
        let rc_addr = self
            .builder
            .ins()
            .iadd_imm(closure_val, i64::from(HeapHeader::RC_OFFSET));
        let one = self.builder.ins().iconst(types::I64, 1);
        let old_rc = self.builder.ins().atomic_rmw(
            types::I64,
            MemFlags::trusted(),
            AtomicRmwOp::Sub,
            rc_addr,
            one,
        );

        // Branch: if old_rc == 1, free the closure.
        let cmp = self.builder.ins().icmp(IntCC::Equal, old_rc, one);
        let free_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(cmp, free_block, &[], cont_block, &[]);

        // Free path.
        self.builder.switch_to_block(free_block);
        self.builder.seal_block(free_block);
        self.builder.ins().fence();

        // Load drop_glue_ptr from the closure.
        let drop_glue_ptr = heap::heap_load(
            &mut self.builder,
            closure_val,
            HeapClosure::DROP_GLUE_PTR_OFFSET,
        );

        // If drop_glue_ptr != 0, call it.
        let zero = self.builder.ins().iconst(types::I64, 0);
        let has_glue = self
            .builder
            .ins()
            .icmp(IntCC::NotEqual, drop_glue_ptr, zero);
        let glue_block = self.builder.create_block();
        let dealloc_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(has_glue, glue_block, &[], dealloc_block, &[]);

        // Call drop glue: (closure_ptr: i64) -> ()
        self.builder.switch_to_block(glue_block);
        self.builder.seal_block(glue_block);

        let mut glue_sig = self.module.make_signature();
        glue_sig.params.push(AbiParam::new(types::I64));
        let glue_sig_ref = self.builder.import_signature(glue_sig);
        self.builder
            .ins()
            .call_indirect(glue_sig_ref, drop_glue_ptr, &[closure_val]);
        self.builder.ins().jump(dealloc_block, &[]);

        // Dealloc the closure.
        self.builder.switch_to_block(dealloc_block);
        self.builder.seal_block(dealloc_block);
        let dealloc_ref = self
            .module
            .declare_func_in_func(dealloc_id, self.builder.func);
        self.builder.ins().call(dealloc_ref, &[closure_val]);
        self.builder.ins().jump(cont_block, &[]);

        // Continue.
        self.builder.switch_to_block(cont_block);
        self.builder.seal_block(cont_block);
    }

    /// Emit RC dec for an ADT value with inline drop glue in the dealloc path.
    ///
    /// Unlike the old `emit_inline_drop_glue` + `emit_rc_dec` pattern (which
    /// dec'd fields unconditionally before dec'ing the ADT), this method
    /// only dec's fields inside the "RC reached 0" branch. This prevents
    /// double-free when fields have independent references (e.g., extracted
    /// via pattern match binding).
    ///
    /// Flow:
    /// ```text
    /// if needs_guard && val < NULLARY_THRESHOLD: skip (bare tag)
    /// old_rc = atomic_sub(val.rc, 1)
    /// if old_rc == 1:
    ///     fence()
    ///     emit_inline_drop_glue(val)   // dec heap-typed fields
    ///     dealloc(val)
    /// ```
    pub(crate) fn emit_rc_dec_with_inline_drop_glue(
        &mut self,
        val: Value,
        ty: &Type,
        dealloc: FuncId,
        needs_guard: bool,
    ) {
        use cranelisp_types::HeapHeader;
        use cranelift_codegen::ir::AtomicRmwOp;

        // Depth limit for inline drop glue: prevents infinite IR for
        // recursive types (e.g., List contains List). Allows several
        // levels of nesting for non-recursive parametric types like
        // Option(Option(String)). Beyond the limit, fall back to plain
        // dec (fields leak — known limitation of inline drop glue,
        // to be replaced by proper drop-glue functions later).
        const MAX_DROP_GLUE_DEPTH: u32 = 4;
        if self.drop_glue_depth >= MAX_DROP_GLUE_DEPTH {
            if needs_guard {
                heap::emit_rc_dec_guarded(
                    &mut self.builder, self.module, val, dealloc, None, true,
                );
            } else {
                heap::emit_rc_dec(
                    &mut self.builder, self.module, val, dealloc, None,
                );
            }
            return;
        }
        self.drop_glue_depth += 1;

        let cont_block = self.builder.create_block();

        // Guard: if value is a bare nullary tag, skip the dec entirely.
        if needs_guard {
            let threshold = self
                .builder
                .ins()
                .iconst(types::I64, heap::NULLARY_THRESHOLD_I64);
            let is_tag = self.builder.ins().icmp(
                IntCC::UnsignedLessThan,
                val,
                threshold,
            );
            let dec_block = self.builder.create_block();
            self.builder
                .ins()
                .brif(is_tag, cont_block, &[], dec_block, &[]);
            self.builder.switch_to_block(dec_block);
            self.builder.seal_block(dec_block);
        }

        // Atomic dec RC.
        let rc_addr = self
            .builder
            .ins()
            .iadd_imm(val, i64::from(HeapHeader::RC_OFFSET));
        let one = self.builder.ins().iconst(types::I64, 1);
        let old_rc = self.builder.ins().atomic_rmw(
            types::I64,
            MemFlags::trusted(),
            AtomicRmwOp::Sub,
            rc_addr,
            one,
        );

        // Branch: if old_rc == 1 (last reference), free the object.
        let cmp = self.builder.ins().icmp(IntCC::Equal, old_rc, one);
        let free_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(cmp, free_block, &[], cont_block, &[]);

        // Free path: Acquire fence, drop glue for fields, then dealloc.
        self.builder.switch_to_block(free_block);
        self.builder.seal_block(free_block);
        self.builder.ins().fence();

        // Emit inline drop glue for ADT fields (only in the dealloc path).
        // This is safe because RC==0 means we are the sole owner.
        self.emit_inline_drop_glue(val, ty, dealloc, false);

        // Call runtime/dealloc.
        let dealloc_ref = self
            .module
            .declare_func_in_func(dealloc, self.builder.func);
        self.builder.ins().call(dealloc_ref, &[val]);
        self.builder.ins().jump(cont_block, &[]);

        // Continue path.
        self.builder.switch_to_block(cont_block);
        self.builder.seal_block(cont_block);

        // Restore depth counter.
        self.drop_glue_depth -= 1;
    }
}

// --- Free helper functions for type variable resolution ---

/// Build a substitution map from type variable IDs to concrete types
/// for an ADT value. Extracts the concrete type args from the ADT type
/// and maps them positionally to the Var IDs found in the type definition.
pub(crate) fn build_adt_type_substitution(
    ty: &Type,
    ctors: &[CtorMeta],
) -> std::collections::HashMap<cranelisp_types::TypeId, Type> {
    // Get concrete type args from the variable's type.
    let concrete_args = match ty {
        Type::ADT(_, args) => args.clone(),
        _ => return std::collections::HashMap::new(),
    };

    // Build substitution from Var ids to concrete types.
    let mut unique_var_ids: Vec<cranelisp_types::TypeId> = Vec::new();
    for c in ctors {
        for field in &c.fields {
            collect_var_ids_from_type(&field.ty, &mut unique_var_ids);
        }
    }
    unique_var_ids
        .iter()
        .zip(concrete_args.iter())
        .map(|(&id, arg)| (id, arg.clone()))
        .collect()
}

/// Collect all unique Var ids from a type, in order of first appearance.
pub(crate) fn collect_var_ids_from_type(ty: &Type, ids: &mut Vec<cranelisp_types::TypeId>) {
    match ty {
        Type::Var(id)
            if !ids.contains(id) => {
                ids.push(*id);
            }
        Type::ADT(_, args) => {
            for a in args {
                collect_var_ids_from_type(a, ids);
            }
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_var_ids_from_type(p, ids);
            }
            collect_var_ids_from_type(ret, ids);
        }
        _ => {}
    }
}

/// Substitute type variables in a type using a Var id -> Type mapping.
pub(crate) fn substitute_type_inline(
    ty: &Type,
    subst: &std::collections::HashMap<cranelisp_types::TypeId, Type>,
) -> Type {
    match ty {
        Type::Var(id) => {
            subst.get(id).cloned().unwrap_or_else(|| ty.clone())
        }
        Type::ADT(name, args) => {
            let new_args = args.iter().map(|a| substitute_type_inline(a, subst)).collect();
            Type::ADT(name.clone(), new_args)
        }
        Type::Fn(params, ret) => {
            let new_params = params.iter().map(|p| substitute_type_inline(p, subst)).collect();
            let new_ret = Box::new(substitute_type_inline(ret, subst));
            Type::Fn(new_params, new_ret)
        }
        _ => ty.clone(),
    }
}

/// Find the inferred type of a Var reference with the given name in an expression tree.
///
/// Walks the AST recursively and returns the first Var node's `inferred_type()`
/// that matches the name. Used by `derive_param_type_from_body` to find parameter
/// types from use sites when the defn-level type is not available.
pub(crate) fn find_var_type_in_expr(expr: &MonoExpr, name: &Symbol) -> Option<Type> {
    match expr {
        MonoExpr::Var { name: var_name, ty, .. } if var_name == name => {
            Some(ty.to_type())
        }
        MonoExpr::Let { bindings, body, .. } => {
            for (_, val) in bindings {
                if let Some(ty) = find_var_type_in_expr(val, name) {
                    return Some(ty);
                }
            }
            find_var_type_in_expr(body, name)
        }
        MonoExpr::If { cond, then_branch, else_branch, .. } => {
            find_var_type_in_expr(cond, name)
                .or_else(|| find_var_type_in_expr(then_branch, name))
                .or_else(|| find_var_type_in_expr(else_branch, name))
        }
        MonoExpr::Lambda { body, .. } => find_var_type_in_expr(body, name),
        MonoExpr::Apply { callee, args, .. } => {
            find_var_type_in_expr(callee, name)
                .or_else(|| args.iter().find_map(|a| find_var_type_in_expr(a, name)))
        }
        MonoExpr::Match { scrutinee, arms, .. } => {
            find_var_type_in_expr(scrutinee, name)
                .or_else(|| arms.iter().find_map(|arm| find_var_type_in_expr(&arm.body, name)))
        }
        MonoExpr::VecLit { elements, .. } => {
            elements.iter().find_map(|e| find_var_type_in_expr(e, name))
        }
        MonoExpr::Trace { body, .. } => find_var_type_in_expr(body, name),
        MonoExpr::ParBind { bindings, body, .. } => {
            for (_, val) in bindings {
                if let Some(ty) = find_var_type_in_expr(val, name) {
                    return Some(ty);
                }
            }
            find_var_type_in_expr(body, name)
        }
        // A `LaunchContinue` node's `launched` sub-tree (the detached
        // per-connection handler) is where a continuation parameter is often
        // used EXCLUSIVELY — e.g. `conn` in `(bind (read-conn conn) (fn [req]
        // … (send-conn conn …)))`. Omitting this arm left such a param
        // un-typed in `variable_types`, so `compile_consuming_arg_list` skipped
        // its consuming inc while the poll state-closure drop glue still dec'd
        // it → double-free of a borrowed heap value owned by an enclosing scope
        // (FIXME 0494 bug #2, the size-32 `Connection` stale RC-dec). Descending
        // both branches restores the inc that balances the drop-glue dec.
        MonoExpr::LaunchContinue { launched, continuation, .. } => {
            find_var_type_in_expr(launched, name)
                .or_else(|| find_var_type_in_expr(continuation, name))
        }
        MonoExpr::ConstrADT { fields, .. } => {
            fields.iter().find_map(|f| find_var_type_in_expr(f, name))
        }
        // Literals carry no sub-expression and no variable reference — no type
        // to find. This arm is deliberately EXHAUSTIVE (not `_ => None`) so that
        // adding a new `MonoExpr` variant carrying a sub-expression is a compile
        // error at this seam, forcing a conscious traversal decision. A silent
        // `_ => None` here is exactly how FIXME 0494's double-free shipped
        // (a `conn`-typed param used only inside a then-missing `LaunchContinue`
        // sub-tree fell through to `None` → skipped consuming inc → UAF). Kept
        // in lock-step with its two exhaustive sibling MonoExpr RC/lifetime
        // traversals (`heap.rs::collect_var_uses`,
        // `control_flow/free_vars.rs::collect_free_vars`); all three must stay
        // exhaustive.
        //
        // `Var { .. }` also lands here: the guarded `Var` arm above returns the
        // type only when the name matches (a guarded arm does not count toward
        // exhaustivity), so a non-matching `Var` yields no type.
        MonoExpr::Var { .. }
        | MonoExpr::IntLit { .. }
        | MonoExpr::FloatLit { .. }
        | MonoExpr::BoolLit { .. }
        | MonoExpr::StringLit { .. } => None,
    }
}

/// Heap-classify a SIGNATURE-PATH field/binding `Type` (concrete-boundary-type.md
/// §3.1.1, FIXME 0391/0394). The body-AST codegen walk classifies a `ConcreteType`
/// off each `MonoExpr` node directly — no `Var` by construction. But the
/// `Type`-typed RC machinery (`variable_types`, `CtorField`, `resolve_field_types`)
/// reads field/binding types from the **signature** (the `scheme`, `Type::Fn`
/// params), and a `Var` legitimately survives there in ONE case: the **generic
/// constructor `Def`'s own codegen**. A `(deftype (Option a) … (Some [:a val]))`
/// ctor `Def` is codegen'd ONCE as a generic template whose field param is
/// `Type::Var a` — its runtime representation is uniform (i64 tag-or-pointer), the
/// `Mixed` heap category. (§3.1.1's "ctor field types are always concrete at
/// codegen" holds for ctor USE sites — a `(Some 1)` instance pins `a := Int` — but
/// NOT for the generic ctor `Def`'s own template body; that gap is FIXME 0394.)
///
/// So this helper classifies a concrete field type via the total
/// `HeapCategory::classify(&ConcreteType, …)`, and maps a residual `Var`/`TyConApp`
/// (a generic-ctor-template field param) to `Mixed` — the uniform-representation
/// category, restoring the pre-Phase-3 generic-ctor-`Def` behaviour. This does NOT
/// widen the `ConcreteType` `classify` (which stays total, no `Var` arm) and does
/// NOT affect the body-AST path (still 100% `Var`-free by construction).
pub(crate) fn signature_heap_category<C, L>(
    ty: &Type,
    symbol_tables: Option<&dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>>,
) -> HeapCategory
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    match ConcreteType::from_type(ty) {
        Ok(ct) => HeapCategory::classify(&ct, symbol_tables),
        // A generic-ctor-template field param (`Type::Var`) / unresolved HKT head:
        // uniform i64 representation → `Mixed` (the guarded RC path). FIXME 0394.
        Err(_) => HeapCategory::Mixed,
    }
}

#[cfg(test)]
mod find_var_type_tests {
    use super::find_var_type_in_expr;
    use cranelisp_types::{
        ConcreteType, FQTypeName, ModuleFullPath, MonoExpr, Span, Symbol, TypeName,
    };

    fn conn_ty() -> ConcreteType {
        // A 1-field heap ADT, mirroring `web/Connection` (FIXME 0494 bug #2).
        ConcreteType::ADT(
            FQTypeName::new(ModuleFullPath::from("web"), TypeName::from("Connection")),
            vec![],
        )
    }

    fn var(name: &str, ty: ConcreteType) -> MonoExpr {
        MonoExpr::Var {
            name: Symbol::from(name),
            span: Span::SYNTHETIC,
            resolved_call: None,
            ty,
        }
    }

    fn apply(callee: MonoExpr, args: Vec<MonoExpr>) -> MonoExpr {
        MonoExpr::Apply {
            callee: Box::new(callee),
            args,
            span: Span::SYNTHETIC,
            resolved_call: None,
            ty: ConcreteType::Int,
            confined: None,
            escapes: None,
            provenance: None,
            unique_static: None,
        }
    }

    // spec: bounded-contexts.md §4b invariant 15 / ring2-rc.md §5.5 — a continuation
    // parameter used ONLY inside a launched (detached) sub-tree must still be
    // heap-typed so its consuming inc balances the poll state-closure drop-glue dec.
    // RED before the FIXME-0494 fix: `find_var_type_in_expr` had no `LaunchContinue`
    // arm, so it returned `None` for `conn` here and the consuming inc was skipped →
    // double-free of the borrowed `Connection`.
    #[test]
    fn find_var_type_descends_into_launchcontinue_launched_subtree() {
        // `(launch (read-conn conn) <continuation>)` — `conn` (a heap ADT) is used
        // ONLY inside the launched (detached) branch, never in the continuation.
        let launched = apply(var("read-conn", ConcreteType::Int), vec![var("conn", conn_ty())]);
        let continuation = var("_", ConcreteType::Int);
        let node = MonoExpr::LaunchContinue {
            launched: Box::new(launched),
            continuation: Box::new(continuation),
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
        };

        let found = find_var_type_in_expr(&node, &Symbol::from("conn"));
        assert_eq!(
            found,
            Some(conn_ty().to_type()),
            "conn used only in a LaunchContinue.launched sub-tree must still be \
             heap-typed (else its consuming inc is skipped → poll drop-glue double-free)"
        );
    }

    // A temporary (a non-`Var` sub-expression) inside the launched sub-tree is NOT a
    // named variable, so it is (correctly) not discovered as a param type — the
    // owned-temporary side of the borrowed-vs-owned discipline (no inc owed).
    #[test]
    fn find_var_type_absent_for_unnamed_var() {
        let launched = apply(var("read-conn", ConcreteType::Int), vec![var("conn", conn_ty())]);
        let node = MonoExpr::LaunchContinue {
            launched: Box::new(launched),
            continuation: Box::new(var("_", ConcreteType::Int)),
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
        };
        // A name not present anywhere resolves to None (no spurious type).
        assert_eq!(find_var_type_in_expr(&node, &Symbol::from("nope")), None);
    }
}
