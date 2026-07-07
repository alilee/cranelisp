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
    /// Collect the set of known ADT constructor names in the current module.
    ///
    /// Constructor calls are alloc+tag, not real work, so they are excluded from
    /// sparking. Single-source (Principle 7) for both lenient decision sites —
    /// the `let` path (`compile_let`) and the apply-argument path
    /// (`compile_apply`, lenient-eval.md §4.4).
    pub(crate) fn collect_module_constructors(&self) -> HashSet<Symbol> {
        self.ctx
            .symbol_tables
            .get(&self.ctx.current_module)
            .map(|table| {
                table
                    .symbols
                    .iter()
                    .filter(|(_, entry)| {
                        matches!(
                            entry,
                            cranelisp_types::ModuleEntry::Def { kind, .. }
                                if matches!(
                                    **kind,
                                    cranelisp_types::DefKind::Constructor { .. }
                                )
                        )
                    })
                    .map(|(name, _)| name.clone())
                    .collect()
            })
            .unwrap_or_default()
    }

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
        if !*LENIENT_DISABLED && !self.in_trace_body && !self.suppress_spark_gate {
            // Collect known constructor names to exclude from sparking (shared
            // with the apply-arg lenient site, Principle 7).
            let constructors = self.collect_module_constructors();
            let sparkable = find_sparkable_bindings(bindings, &constructors);
            if sparkable.len() >= 2 {
                // S104 Wave 0 — record the M-static classification of each
                // sparkable binding for the discrimination experiment
                // (measurement-only; gated on CRANELISP_SPARK_STATS; does NOT
                // change admission). `lenient-eval.md` §2.8.6.
                self.record_spark_sites_let(bindings, &sparkable);
                // Create-gate (§3.6.2): a runtime budget branch wraps the site.
                // Lenient arm = the spark path; direct arm = the existing
                // fully-sequential `let` (no IVars, no allocation) when over
                // budget. Both arms produce the body result; the gate joins them.
                let n = sparkable.len();
                return self.emit_create_gate(
                    n,
                    span,
                    |this| this.compile_let_lenient(bindings, body, &sparkable, span),
                    |this| this.compile_let_sequential(bindings, body, span),
                );
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
        //
        // Processed in `sparkable` order (ascending = source = topological
        // order, lenient-eval.md §2.6.1), so when a *dependent* binding's thunk
        // is built every IVar it depends on has already been created and recorded
        // in `sparked_name_to_ivar`.
        let mut ivar_map: std::collections::HashMap<usize, Value> = std::collections::HashMap::new();
        // Earlier sparked bindings: name -> (IVar pointer, value type). Used to
        // resolve a dependent binding's dependencies to their IVars (§4.5).
        let mut sparked_name_to_ivar: std::collections::HashMap<Symbol, (Value, ConcreteType)> =
            std::collections::HashMap::new();

        for &idx in sparkable {
            let (name, val_expr) = &bindings[idx];

            // A dependent binding references one or more EARLIER sparked
            // bindings. The relaxed admission rule (sparkability.rs §2.6)
            // guarantees every earlier-bound free var of a sparkable binding is
            // itself sparked, so any free var found in `sparked_name_to_ivar` is
            // a dependency to force on demand. Sorted for deterministic capture
            // layout.
            let mut deps: Vec<(Symbol, Value, cranelisp_types::Type)> =
                super::find_free_vars(val_expr, &[])
                    .into_iter()
                    .filter_map(|v| {
                        sparked_name_to_ivar
                            .get(&v)
                            .map(|(ivar, ty)| (v.clone(), *ivar, ty.to_type()))
                    })
                    .collect();
            deps.sort_by(|a, b| a.0.cmp(&b.0));

            let thunk_val = if deps.is_empty() {
                // Independent binding: wrap the value expression in a zero-arg
                // lambda (thunk). The thunk's concrete type is `(Fn [] T)` where
                // `T` is the binding value's type.
                let thunk_expr = MonoExpr::Lambda {
                    params: vec![],
                    body: Box::new(val_expr.clone()),
                    span: val_expr.span(),
                    ty: ConcreteType::Fn(vec![], Box::new(val_expr.ty().clone())),
                    confined: None,
                    escapes: None,
                    unique_static: None,
                };
                // Compile the spark-thunk body via the single-source helper
                // (`compile_spark_thunk`), which raises BOTH spark flags around the
                // thunk compile and restores them (error-safe):
                //  - Capture-by-borrow (S99, FIXME 0461; lenient-eval.md §4.4.1):
                //    this INDEPENDENT `let` spark is structurally joined — Phase 2
                //    forces it before the `let` body, so its heap captures are
                //    borrowed (toggle-gated).
                //  - Gate 5 (§4.3, FIXME 0525): the relocated construction in the
                //    thunk body declines stack allocation (dangles at the join).
                // The DEPENDENT branch below is deliberately handled separately: its
                // synthetic `§ivar_*` IVar-pointer captures are load-bearing
                // keepalives, not live-parent borrows (§4.4.1 carve-out), so the
                // borrow flag must NOT reach `compile_dependent_thunk` — but the
                // `in_spark_thunk` gate-5 flag MUST (set directly on its inner
                // compiler in `dependent_spark.rs`).
                self.compile_spark_thunk(&thunk_expr)?
            } else {
                // Dependent binding: build the thunk manually with a force
                // prologue that forces each dependency IVar on demand (§4.5).
                // NOTE: the borrow flag is NOT raised here — the §4.5 carve-out.
                self.compile_dependent_thunk(val_expr, &deps, span)?
            };

            // Call cranelisp_ivar_create(thunk_ptr) -> ivar_ptr
            let ivar_val = self.emit_extern_call(
                "cranelisp_ivar_create", &[thunk_val], span,
            )?;

            // Call cranelisp_ivar_spark(ivar_ptr)
            let _spark_result = self.emit_extern_call(
                "cranelisp_ivar_spark", &[ivar_val], span,
            )?;

            ivar_map.insert(idx, ivar_val);
            sparked_name_to_ivar.insert(name.clone(), (ivar_val, val_expr.ty().clone()));
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

    /// Emit the **create-gate** around a spark site (lenient-eval.md §3.6.2).
    ///
    /// At a sparkable site with `n` sparkable positions (`n ≥ 2`), the static
    /// sparkability decision is necessary but not sufficient — it cannot see
    /// dynamic recursion depth, so a naive over-sparking recursion would allocate
    /// `O(nodes)` IVars/thunks. The gate moves the budget decision *before*
    /// allocation: it calls `cranelisp_spark_budget_try_reserve(n)` and branches
    /// into a **lenient arm** (the caller's `lenient` closure — create+spark+force
    /// barrier, the only place allocation happens) on a granted batch, or a
    /// **direct arm** (the caller's `direct` closure — the existing fully-sequential
    /// lowering, zero allocation) when over budget. Both arms produce the site's
    /// result `Value` and `jump join_block(result)`; the gate returns the join
    /// param. This bounds total spark allocation to `O(cap)` regardless of tree
    /// size (§3.6.3 floor argument).
    ///
    /// Single-source (Principle 7) for both spark clients — the apply-argument
    /// site (`compile_apply`, §4.4) and the `let` site (`compile_let`, §4.2). The
    /// two call sites differ only in *which* lowering each arm runs; the gate
    /// shape (try_reserve → brif → two arms → join-with-param) is shared here.
    ///
    /// `CRANELISP_NO_LENIENT` / trace-body suppression and the TCO self-call fast
    /// paths are handled by the callers *above* the gate, so a suppressed or TCO
    /// site never reaches this helper (§2.5.3, §3.6.2).
    pub(crate) fn emit_create_gate(
        &mut self,
        n: usize,
        span: Span,
        lenient: impl FnOnce(&mut Self) -> Result<Value, CranelispError>,
        direct: impl FnOnce(&mut Self) -> Result<Value, CranelispError>,
    ) -> Result<Value, CranelispError> {
        // granted = call cranelisp_spark_budget_try_reserve(n)  (1 = lenient, 0 = direct)
        let n_val = self.builder.ins().iconst(types::I64, n as i64);
        let granted =
            self.emit_extern_call("cranelisp_spark_budget_try_reserve", &[n_val], span)?;

        let lenient_block = self.builder.create_block();
        let direct_block = self.builder.create_block();
        let join_block = self.builder.create_block();
        self.builder.append_block_param(join_block, types::I64);

        self.builder
            .ins()
            .brif(granted, lenient_block, &[], direct_block, &[]);

        // Both arms compile the SAME source expressions, so each arm gets a unique
        // discriminator token appended to `gate_arm_disc` for the duration of its
        // compilation (saved/restored, so nested gates accumulate). This keeps the
        // two arms' span-derived inner-function names (`__lambda_…`, `__wrap_…`)
        // distinct — without it the second arm's `define_function` collides.
        let gate_id = self.gate_counter;
        self.gate_counter += 1;
        let saved_disc = self.gate_arm_disc.clone();

        // Both arms must start from the SAME tail-position state — the value the
        // caller established at the gate site (false for the apply site, since
        // `compile_apply` clears it before the gate; the let's body tail-position
        // for the let site). The first arm's lowering mutates `in_tail_position`
        // (e.g. `dispatch_apply` restores it to `saved_tail` for the call), so
        // without restoring it the SECOND arm would compile under the wrong
        // tail-position — turning a non-tail recursive arg into a spurious TCO
        // self-jump to the loop header (observed: the direct arm of a recursive
        // `(add-i64 (f …) (f …))` jumped to the loop header instead of calling).
        let saved_itp = self.in_tail_position;

        // Lenient arm: budget granted — create+spark IVars, force barrier, dispatch.
        self.builder.switch_to_block(lenient_block);
        self.builder.seal_block(lenient_block);
        self.gate_arm_disc = format!("{saved_disc}g{gate_id}L_");
        self.in_tail_position = saved_itp;
        let val_l = lenient(&mut *self)?;
        self.gate_arm_disc = saved_disc.clone();
        self.builder.ins().jump(join_block, &[val_l]);

        // Direct arm: over budget — the existing sequential lowering, no
        // allocation. Suppress nested gates for the whole subtree: over budget at
        // this site ⇒ evaluate the subexpression serially (§3.6.3 floor), AND
        // this is what bounds codegen — without it a statically nested chain of
        // sparkable sites would re-compile its tail on both arms at every level,
        // giving O(2^depth) compile time.
        self.builder.switch_to_block(direct_block);
        self.builder.seal_block(direct_block);
        self.gate_arm_disc = format!("{saved_disc}g{gate_id}D_");
        self.in_tail_position = saved_itp;
        let saved_suppress = self.suppress_spark_gate;
        self.suppress_spark_gate = true;
        let val_d = direct(&mut *self)?;
        self.suppress_spark_gate = saved_suppress;
        self.gate_arm_disc = saved_disc;
        self.builder.ins().jump(join_block, &[val_d]);

        // Join: both arms produce the site's result as a single i64 Value.
        self.builder.switch_to_block(join_block);
        self.builder.seal_block(join_block);
        Ok(self.builder.block_params(join_block)[0])
    }

    /// Emit an inline RC dec for an IVar pointer.
    ///
    /// IVars use atomic RC at offset +8. When dec brings RC to 0, call
    /// `cranelisp_ivar_dealloc` to free — that intrinsic frees the IVar cell
    /// AND any ferried error String stashed in its `error` field by the
    /// fork-join error-slot ferry (a panicked thunk's message). Plain
    /// `runtime/dealloc` would leak that String; `cranelisp_ivar_dealloc` is the
    /// IVar-aware drop path (`ivar.rs`, test-discovery.md §6).
    pub(crate) fn emit_rc_dec_for_ivar(&mut self, ivar_val: Value, span: Span) -> Result<(), CranelispError> {
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

        // Condition is never in tail position, and is never a tail-call arg —
        // its value is consumed as the branch selector, not forwarded to the
        // loop param. Clear `tail_arg_protect` so a heap binding aliased inside a
        // nested `if`/`match` condition is not spuriously protected; the branches
        // (below) restore it.
        let saved_protect = self.tail_arg_protect;
        self.in_tail_position = false;
        self.tail_arg_protect = false;
        let cond_val = self.compile_expr(cond)?;
        self.tail_arg_protect = saved_protect;

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
        // Tail-call-arg alias protection (F1 UAF cure): if this `if` is a direct
        // tail-call argument and this branch yields a live heap let-binding the
        // tail-jump flush will dec, inc it so the value survives the flush. No-op
        // otherwise. Nested control flow inherits the flag → its branches protect
        // too; a non-control-flow branch (`(wrap v)`) is left unprotected.
        let then_val = self.maybe_protect_tail_arg_alias(then_branch, then_val);
        self.builder.ins().jump(merge_block, &[then_val]);

        // Else branch.
        self.builder.switch_to_block(else_block);
        self.builder.seal_block(else_block);
        self.in_tail_position = saved_tail;
        let else_val = self.compile_expr(else_branch)?;
        let else_val = self.maybe_protect_tail_arg_alias(else_branch, else_val);
        self.builder.ins().jump(merge_block, &[else_val]);

        // Merge block.
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);

        Ok(self.builder.block_params(merge_block)[0])
    }
}
