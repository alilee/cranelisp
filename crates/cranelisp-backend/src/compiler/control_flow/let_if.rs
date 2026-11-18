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

use super::FnCompiler;
use super::sparkability::{
    LENIENT_DISABLED, SPARK_ADMIT, SparkAdmit, binder_before, find_sparkable_bindings,
    find_sparkable_bindings_with,
};
use crate::compiler::ownership_plan::Intro;

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
                    .all_symbols()
                    .filter(|(_, entry)| {
                        matches!(
                            entry.callable().map(|callable| &callable.origin),
                            Some(cranelisp_types::CallableOrigin::Ctor { .. })
                        )
                    })
                    // I-1 (S109 W1.2 §10.4): the storage key is canonical
                    // `Type.Ctor` (`Maybe.Some`) for a sum ctor / the type name
                    // for a product; `is_worth_sparking` compares SOURCE-written
                    // callee names (bare `Some`, dotted `Maybe.Some`, FQ `m/Some`).
                    // Normalise BOTH sides through the ONE terminal-segment grammar
                    // (`bare_member_name`) so a sum-ctor call is not silently
                    // dropped from the spark-exclusion set (heuristic-only surface:
                    // terminal-segment granularity is acceptable).
                    .map(|(name, _)| Symbol::from(cranelisp_types::bare_member_name(name.as_ref())))
                    .collect()
            })
            .unwrap_or_default()
    }

    // --- Let expression ---

    pub(crate) fn compile_let(
        &mut self,
        node: &MonoExpr,
        bindings: &[(Symbol, MonoExpr)],
        body: &MonoExpr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Check if lenient evaluation applies. Inside a trace's extent the
        // create-gate declines at run time (trace-codegen.md §2).
        if !*LENIENT_DISABLED && !self.suppress_spark_gate {
            // Admission filter (lenient-eval.md §2.8.2 / §2.8.6): M-static (the
            // default) admits only recursive-SCC ∧ non-tail candidates via the
            // single-sourced classifier; `CRANELISP_SPARK_ADMIT=syntactic` selects
            // the pre-S104 §2.2 filter for `/qa`'s comparison row. The independence
            // carve-out (§2.6) and the ≥2 gate compose identically inside
            // `find_sparkable_bindings_with` for both filters (Principle 7).
            let sparkable = match *SPARK_ADMIT {
                SparkAdmit::Syntactic => {
                    // Constructor names are excluded from the syntactic cost
                    // heuristic (shared with the apply-arg site, Principle 7).
                    let constructors = self.collect_module_constructors();
                    find_sparkable_bindings(bindings, &constructors)
                }
                SparkAdmit::Mstatic => {
                    let recursive = self.mstatic_recursive_set();
                    find_sparkable_bindings_with(bindings, |e| {
                        self.mstatic_admits_candidate(e, &recursive)
                    })
                }
            };
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
                    |this| this.compile_let_lenient(node, bindings, body, &sparkable, span),
                    |this| this.compile_let_sequential(node, bindings, body),
                );
            }
        }

        self.compile_let_sequential(node, bindings, body)
    }

    /// Compile a let expression sequentially (no lenient evaluation). Each
    /// binder takes its initializer's owned value.
    fn compile_let_sequential(
        &mut self,
        node: &MonoExpr,
        bindings: &[(Symbol, MonoExpr)],
        body: &MonoExpr,
    ) -> Result<Value, CranelispError> {
        let key = crate::compiler::ownership_plan::node_key(node);
        self.push_scope();
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;
        for (index, (name, val_expr)) in bindings.iter().enumerate() {
            // §4.3: a repeated name's initializer sees the PRECEDING binder, so
            // nothing about this binder is published until its value exists.
            let val = self.compile_expr(val_expr)?;
            self.bind_binder(
                Intro::Let { node: key, index },
                name,
                val,
                val_expr.ty().clone(),
            )?;
        }
        self.in_tail_position = saved_tail;
        let result = self.compile_expr(body)?;
        self.pop_scope();
        Ok(result)
    }

    /// Compile a let expression with lenient evaluation (parallel sparkable bindings).
    ///
    /// See design/backend/lenient-eval.md §4.2 for the algorithm.
    fn compile_let_lenient(
        &mut self,
        node: &MonoExpr,
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
        // Per-binding-vector state, indexed by BINDING POSITION
        // (`design/backend/binding-scope.md` §"Binding environment") and read through the one
        // shared resolver `binder_before`. Keying it by name let a non-sparked
        // rebinding leave the displaced binder's IVar visible to a later
        // binding's dependency resolution, which then read the wrong value.
        let mut ivar_map: std::collections::HashMap<usize, (Value, ConcreteType)> =
            std::collections::HashMap::new();

        for &idx in sparkable {
            let (_, val_expr) = &bindings[idx];

            // A dependent binding references one or more EARLIER sparked
            // bindings. The relaxed admission rule (sparkability.rs §2.6)
            // guarantees every earlier-bound free var of a sparkable binding is
            // itself sparked, so any free var found in `sparked_name_to_ivar` is
            // a dependency to force on demand. Sorted for deterministic capture
            // layout.
            let mut deps: Vec<(Symbol, Value, ConcreteType)> = super::find_free_vars(val_expr, &[])
                .into_iter()
                .filter_map(|v| {
                    let at = binder_before(bindings, idx, &v)?;
                    let (ivar, ty) = ivar_map.get(&at)?;
                    Some((v.clone(), *ivar, ty.clone()))
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
                // The thunk duplicates its captures (`compile_spark_thunk`).
                self.compile_spark_thunk(&thunk_expr)?
            } else {
                // Dependent binding: build the thunk manually with a force
                // prologue that forces each dependency IVar on demand (§4.5).
                self.compile_dependent_thunk(val_expr, &deps, span)?
            };

            // Call cranelisp_ivar_create(thunk_ptr) -> ivar_ptr
            let ivar_val = self.emit_extern_call("cranelisp_ivar_create", &[thunk_val], span)?;

            // Call cranelisp_ivar_spark(ivar_ptr)
            let _spark_result = self.emit_extern_call("cranelisp_ivar_spark", &[ivar_val], span)?;

            ivar_map.insert(idx, (ivar_val, val_expr.ty().clone()));
        }

        // Phase 2: Process all bindings in order. A sparked binding's thunk
        // duplicated its captures, so the frame drops here what the sequential
        // initializer would have consumed (`emit_spark_consumption`).
        let key = crate::compiler::ownership_plan::node_key(node);
        for (i, (name, val_expr)) in bindings.iter().enumerate() {
            let val = if sparkable_set.contains(&i) {
                let (ivar_val, _) = ivar_map[&i];
                let forced = self.emit_extern_call("cranelisp_ivar_force", &[ivar_val], span)?;
                // Dec the IVar (main thread's reference); the spark task also dec's.
                self.emit_rc_dec_for_ivar(ivar_val, span)?;
                self.emit_spark_consumption(val_expr)?;
                forced
            } else {
                self.compile_expr(val_expr)?
            };
            self.bind_binder(
                Intro::Let {
                    node: key,
                    index: i,
                },
                name,
                val,
                val_expr.ty().clone(),
            )?;
        }

        // Phase 3: Compile body.
        self.in_tail_position = saved_tail;
        let result = self.compile_expr(body)?;
        self.pop_scope();

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
    pub(crate) fn emit_rc_dec_for_ivar(
        &mut self,
        ivar_val: Value,
        span: Span,
    ) -> Result<(), CranelispError> {
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

        let _dealloc_result = self.emit_extern_call("cranelisp_ivar_dealloc", &[ivar_val], span)?;
        self.builder.ins().jump(cont_block, &[]);

        // Continue.
        self.builder.switch_to_block(cont_block);
        self.builder.seal_block(cont_block);

        Ok(())
    }

    // --- If expression ---

    pub(crate) fn compile_if(
        &mut self,
        node: &MonoExpr,
        cond: &MonoExpr,
        then_branch: &MonoExpr,
        else_branch: &MonoExpr,
    ) -> Result<Value, CranelispError> {
        let key = crate::compiler::ownership_plan::node_key(node);
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;
        let cond_val = self.compile_expr(cond)?;

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);

        self.builder
            .ins()
            .brif(cond_val, then_block, &[], else_block, &[]);

        for (branch, (block, expr)) in [(then_block, then_branch), (else_block, else_branch)]
            .into_iter()
            .enumerate()
        {
            self.builder.switch_to_block(block);
            self.builder.seal_block(block);
            self.emit_entry_drops(key, branch)?;
            self.in_tail_position = saved_tail;
            let val = self.compile_expr(expr)?;
            self.builder.ins().jump(merge_block, &[val]);
        }

        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);
        Ok(self.builder.block_params(merge_block)[0])
    }
}

#[cfg(test)]
mod binder_publication_tests;
