// Let / If control forms.
//
// The binding-and-branch core: sequential + lenient `let` binding (the lenient
// path sparks independent bindings as parallel IVar tasks) and the conditional
// `if` branch-merge. `emit_rc_dec_for_ivar` is the lenient path's IVar-dec
// helper and lives with its only caller.

use std::collections::HashSet;

use cranelift::prelude::*;
use cranelift_module::Module;

use cranelisp_types::{ConcreteType, CranelispError, MonoExpr, Span, Symbol};

use super::sparkability::{find_sparkable_bindings, LENIENT_DISABLED};
use super::FnCompiler;

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // --- Let expression ---

    pub(crate) fn compile_let(
        &mut self,
        bindings: &[(Symbol, MonoExpr)],
        body: &MonoExpr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Check if lenient evaluation applies.
        // Skip sparkability analysis inside trace bodies — trace must
        // execute sequentially to produce deterministic trace trees.
        if !*LENIENT_DISABLED && !self.in_trace_body {
            // Collect known constructor names to exclude from sparking.
            // Collect constructor names from the current module's symbol table.
            let constructors: HashSet<Symbol> = self
                .ctx
                .symbol_tables
                .get(&self.ctx.current_module)
                .map(|table| {
                    table.symbols.iter()
                        .filter(|(_, entry)| matches!(
                            entry,
                            cranelisp_types::ModuleEntry::Def {
                                kind, ..
                            } if matches!(**kind, cranelisp_types::DefKind::Constructor { .. })
                        ))
                        .map(|(name, _)| name.clone())
                        .collect()
                })
                .unwrap_or_default();
            let sparkable = find_sparkable_bindings(bindings, &constructors);
            if sparkable.len() >= 2 {
                return self.compile_let_lenient(bindings, body, &sparkable, span);
            }
        }

        self.compile_let_sequential(bindings, body, span)
    }

    /// Compile a let expression sequentially (no lenient evaluation).
    fn compile_let_sequential(
        &mut self,
        bindings: &[(Symbol, MonoExpr)],
        body: &MonoExpr,
        _span: Span,
    ) -> Result<Value, CranelispError> {
        // Push a new scope frame.
        self.push_scope();

        // Compile each binding.
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;

        for (name, val_expr) in bindings {
            // Record the binding's concrete type (embedded as a `Type` for the
            // `Type`-keyed RC machinery).
            self.variable_types.insert(name.clone(), val_expr.ty().to_type());

            let val = self.compile_expr(val_expr)?;

            // If compile_expr produced a closure with drop glue, record it.
            if let Some(glue_id) = self.pending_closure_drop_glue.take() {
                self.closure_drop_glue.insert(name.clone(), glue_id);
            }

            let var = self.fresh_variable();
            self.builder.declare_var(var, types::I64);
            self.builder.def_var(var, val);
            self.variables.insert(name.clone(), var);
            self.scope_stack
                .last_mut()
                .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                .push(name.clone());
        }

        // Body inherits tail position.
        self.in_tail_position = saved_tail;

        // Determine which variable (if any) is the return value — its
        // ownership transfers to the caller, so skip dec for it.
        let skip_var = Self::return_var_in_scope(body, self.scope_stack.last());

        let result = self.compile_expr(body)?;

        // Protect the return value from scope cleanup if skip_var didn't
        // identify a specific variable to preserve (non-trivial body).
        self.protect_return_value(&skip_var, result, body);

        // Pop the scope frame, emitting rc_dec for heap-typed bindings
        // except the return value.
        self.pop_scope_with_cleanup(skip_var.as_ref());

        Ok(result)
    }

    /// Compile a let expression with lenient evaluation (parallel sparkable bindings).
    ///
    /// See design/backend/lenient-eval.md §4.2 for the algorithm.
    fn compile_let_lenient(
        &mut self,
        bindings: &[(Symbol, MonoExpr)],
        body: &MonoExpr,
        sparkable: &[usize],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let sparkable_set: HashSet<usize> = sparkable.iter().copied().collect();

        self.push_scope();
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;

        // Phase 1: Create and spark IVars for sparkable bindings.
        let mut ivar_map: std::collections::HashMap<usize, Value> = std::collections::HashMap::new();

        for &idx in sparkable {
            let (_name, val_expr) = &bindings[idx];

            // Wrap the value expression in a zero-arg lambda (thunk). The thunk's
            // concrete type is `(Fn [] T)` where `T` is the binding value's type.
            let thunk_expr = MonoExpr::Lambda {
                params: vec![],
                body: Box::new(val_expr.clone()),
                span: val_expr.span(),
                ty: ConcreteType::Fn(vec![], Box::new(val_expr.ty().clone())),
            };
            let thunk_val = self.compile_expr(&thunk_expr)?;

            // Call cranelisp_ivar_create(thunk_ptr) -> ivar_ptr
            let ivar_val = self.emit_extern_call(
                "cranelisp_ivar_create", &[thunk_val], span,
            )?;

            // Call cranelisp_ivar_spark(ivar_ptr)
            let _spark_result = self.emit_extern_call(
                "cranelisp_ivar_spark", &[ivar_val], span,
            )?;

            ivar_map.insert(idx, ivar_val);
        }

        // Phase 2: Process all bindings in order.
        for (i, (name, val_expr)) in bindings.iter().enumerate() {
            self.variable_types.insert(name.clone(), val_expr.ty().to_type());

            let val = if sparkable_set.contains(&i) {
                // Force the IVar and dec our reference.
                let ivar_val = ivar_map[&i];
                let forced_val = self.emit_extern_call(
                    "cranelisp_ivar_force", &[ivar_val], span,
                )?;

                // Dec the IVar (main thread's reference).
                // The IVar has atomic RC; the spark task also dec's.
                self.emit_rc_dec_for_ivar(ivar_val, span)?;

                forced_val
            } else {
                // Non-sparkable: compile normally.
                self.compile_expr(val_expr)?
            };

            if let Some(glue_id) = self.pending_closure_drop_glue.take() {
                self.closure_drop_glue.insert(name.clone(), glue_id);
            }

            let var = self.fresh_variable();
            self.builder.declare_var(var, types::I64);
            self.builder.def_var(var, val);
            self.variables.insert(name.clone(), var);
            self.scope_stack
                .last_mut()
                .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                .push(name.clone());
        }

        // Phase 3: Compile body.
        self.in_tail_position = saved_tail;
        let skip_var = Self::return_var_in_scope(body, self.scope_stack.last());
        let result = self.compile_expr(body)?;
        self.protect_return_value(&skip_var, result, body);
        self.pop_scope_with_cleanup(skip_var.as_ref());

        Ok(result)
    }

    /// Emit an inline RC dec for an IVar pointer.
    ///
    /// IVars use atomic RC at offset +8. When dec brings RC to 0, call
    /// `cranelisp_ivar_dealloc` to free — that intrinsic frees the IVar cell
    /// AND any ferried error String stashed in its `error` field by the
    /// fork-join error-slot ferry (a panicked thunk's message). Plain
    /// `runtime/dealloc` would leak that String; `cranelisp_ivar_dealloc` is the
    /// IVar-aware drop path (`ivar.rs`, test-discovery.md §6).
    fn emit_rc_dec_for_ivar(&mut self, ivar_val: Value, span: Span) -> Result<(), CranelispError> {
        // Load current RC from ivar + 8
        let rc_offset = self.builder.ins().iconst(types::I64, 8);
        let rc_addr = self.builder.ins().iadd(ivar_val, rc_offset);

        // atomic_rmw sub 1 -> old_rc
        let one = self.builder.ins().iconst(types::I64, 1);
        let old_rc = self.builder.ins().atomic_rmw(
            types::I64,
            MemFlags::new(),
            cranelift::codegen::ir::AtomicRmwOp::Sub,
            rc_addr,
            one,
        );

        // If old_rc == 1, free the IVar.
        let free_block = self.builder.create_block();
        let cont_block = self.builder.create_block();

        let one_val = self.builder.ins().iconst(types::I64, 1);
        let is_last = self.builder.ins().icmp(IntCC::Equal, old_rc, one_val);
        self.builder
            .ins()
            .brif(is_last, free_block, &[], cont_block, &[]);

        // Free block: call cranelisp_ivar_dealloc(ivar_ptr) — frees the cell
        // and any ferried error String (test-discovery.md §6).
        self.builder.switch_to_block(free_block);
        self.builder.seal_block(free_block);

        // Acquire fence before the IVar-aware dealloc reads the error field
        // (consistent with Decision 13).
        self.builder.ins().fence();

        let _dealloc_result = self
            .emit_extern_call("cranelisp_ivar_dealloc", &[ivar_val], span)?;
        self.builder.ins().jump(cont_block, &[]);

        // Continue.
        self.builder.switch_to_block(cont_block);
        self.builder.seal_block(cont_block);

        Ok(())
    }

    // --- If expression ---

    pub(crate) fn compile_if(
        &mut self,
        cond: &MonoExpr,
        then_branch: &MonoExpr,
        else_branch: &MonoExpr,
    ) -> Result<Value, CranelispError> {
        let saved_tail = self.in_tail_position;

        // Condition is never in tail position.
        self.in_tail_position = false;
        let cond_val = self.compile_expr(cond)?;

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);

        self.builder
            .ins()
            .brif(cond_val, then_block, &[], else_block, &[]);

        // Then branch.
        self.builder.switch_to_block(then_block);
        self.builder.seal_block(then_block);
        self.in_tail_position = saved_tail;
        let then_val = self.compile_expr(then_branch)?;
        self.builder.ins().jump(merge_block, &[then_val]);

        // Else branch.
        self.builder.switch_to_block(else_block);
        self.builder.seal_block(else_block);
        self.in_tail_position = saved_tail;
        let else_val = self.compile_expr(else_branch)?;
        self.builder.ins().jump(merge_block, &[else_val]);

        // Merge block.
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);

        Ok(self.builder.block_params(merge_block)[0])
    }
}
