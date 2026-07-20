// Function application codegen.
//
// compile_apply, compile_direct_call, compile_tail_self_call,
// emit_adt_construct, compile_extern_call,
// compile_closure_call

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_module::Module;

use cranelisp_types::{DefKind, ErrorLocation, ConcreteType, CranelispError, FQSymbol, HeapHeader, ModuleEntry, MonoExpr, ResolvedCall, Span, Symbol};
use crate::heap::HeapCategory;

use crate::heap::{self, HeapAdt, HeapClosure};
use crate::primitives_inline;

use super::control_flow::{
    find_sparkable_args, find_sparkable_args_with, SparkAdmit, LENIENT_DISABLED, SPARK_ADMIT,
};
use super::{signature_heap_category, FnCompiler};

/// Absolute byte offset of the `IO_TAG_EFFECT` node's fn-name handle field
/// (field-3) from the node **base** pointer.
///
/// The Effect node base layout is `[HeapHeader | tag | thunk_ptr | resource_token
/// | fn_name_handle]`. The platform constants `IO_EFFECT_RESOURCE_OFFSET` /
/// [`cranelisp_platform::IO_EFFECT_FN_NAME_OFFSET`] are **payload** offsets
/// (relative to the start of the payload, which sits one `HeapHeader` past the
/// base — see `CLIO::effect_on_resource`, `crates/cranelisp-platform/src/lib.rs`).
/// The trampoline reads fields at `base + HeapHeader::SIZE + payload_offset`
/// (`crates/cranelisp-intrinsics/src/io.rs` `FIELD_*_OFFSET`). So the absolute
/// offset is composed from the named constants — never hard-coded to 40 — so a
/// header-size or payload-layout change propagates here automatically (S81 /
/// FIXME 0327 the dispatch funnel, step 2/4; BC §5 invariant 9).
const EFFECT_FN_NAME_ABS_OFFSET: i64 =
    HeapHeader::SIZE as i64 + cranelisp_platform::IO_EFFECT_FN_NAME_OFFSET;

/// The set of let-scope bindings that the tail-jump flush must NOT dec because
/// their reference MOVES into a tail-call argument as a bare top-level `Var`
/// (compiled with no consuming inc — the loop param inherits the single
/// reference).
///
/// ONLY a literal top-level `MonoExpr::Var` argument is a move. A binding
/// aliased into a tail argument *through a control-flow form* (`(if c v v)`,
/// `(match … v)`) is deliberately EXCLUDED: those are protected by an explicit
/// inc at the control-flow branch tail (`tail_arg_protect`) and then flushed
/// uniformly, so adding them here would leak the protective inc (and, for
/// distinct-per-branch bindings like `(if c lo hi)`, would wrongly retain the
/// dead branch's binding). See `compile_tail_self_call` and the F1 UAF cure.
pub(crate) fn tail_transfer_skip(args: &[MonoExpr]) -> std::collections::HashSet<Symbol> {
    args.iter()
        .filter_map(|a| match a {
            MonoExpr::Var { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect()
}

/// A compiled argument value paired with the [`HeapCategory`] to release it by
/// — the element of a §3.1 post-call dec list (a temporary passed to a
/// `Borrowed` param that the callee/adapter will not dec).
type PostCallDec = (Value, HeapCategory);

/// Result of [`FnCompiler::compile_consuming_arg_list_moded`]: the compiled arg
/// values and the post-call decs owed after the call returns.
type ModedArgList = (Vec<Value>, Vec<PostCallDec>);

/// The per-position RC action the §3.1 caller-side borrow-elision emits for one
/// argument (`design/backend/ownership-codegen.md` §3.1). The pure decision
/// core of [`FnCompiler::compile_consuming_arg_list_moded`], factored out so the
/// full `{arg-kind} × {mode} × {category}` matrix (§13.5 apply row, Principle 23)
/// is unit-testable without a live `FnCompiler`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ModedArgRc {
    /// No RC op (scalar; or a transferred temporary; or an elided consuming inc).
    None,
    /// Pre-call consuming inc, unguarded (AlwaysHeap owned-binding to `Owned`).
    Inc,
    /// Pre-call consuming inc, guarded (Mixed owned-binding to `Owned`).
    IncGuarded,
    /// Post-call dec, unguarded (AlwaysHeap temporary to `Borrowed`).
    PostDec,
    /// Post-call dec, guarded (Mixed temporary to `Borrowed`).
    PostDecGuarded,
}

/// Decide the §3.1 per-argument RC action from the arg's heap category, the
/// callee's param mode, and whether the arg is an **owned-binding** (a local
/// variable whose enclosing scope decs it at exit) vs a **temporary** (a fresh
/// rc=1 value with no scope owner — a non-`Var`, OR a `Var` naming a
/// fn-as-value / constructor that mints a fresh closure/ADT).
///
/// The matrix (heap positions only; `NeverHeap` ⇒ [`ModedArgRc::None`] always):
///
/// | owned-binding | mode | action |
/// |---|---|---|
/// | yes | `Owned` | consuming inc (also the adaptation path) |
/// | yes | `Borrowed`/`Copy` | none (owner's scope-dec is the single accounting) |
/// | no (temp) | `Owned`/`Copy` | none (rc=1 transfers into the callee) |
/// | no (temp) | `Borrowed` | post-call dec (the callee/adapter will not dec it) |
///
/// `Copy` is never minted for a heap category in increment I; it is mapped to
/// pass-through here for total, defensive coverage.
/// §3.3: is `arg` a DIRECT `vec-get` read the ownership pass marked as a borrowed
/// projection (`provenance` site fact set)? This is the only shape whose in-frame
/// element inc `compile_consuming_arg_list_moded` elides — and only when the read
/// feeds a `Borrowed` parameter, so the borrowed element is consumed in-place and
/// never escapes. An accessor / user-fn `ProjectionOf`-call is NOT matched here:
/// its callee already materialized the result with an owned reference (its return
/// protect is kept, `return_is_fresh_by_summary`), so it is an ordinary owned
/// temporary at the call site. `provenance = None` (analysis off, or a read the
/// pass could not prove borrow-safe) ⇒ `false` ⇒ inc verbatim (§2.2).
fn is_direct_vecget_projection(arg: &MonoExpr) -> bool {
    matches!(
        arg,
        MonoExpr::Apply { provenance: Some(_), resolved_call: Some(rc), .. }
            if matches!(rc.as_ref(),
                ResolvedCall::BuiltinFn { name } if name.as_ref() == "vec-get")
    )
}

pub(crate) fn moded_arg_rc(
    category: HeapCategory,
    mode: cranelisp_types::Mode,
    owned_binding: bool,
) -> ModedArgRc {
    use cranelisp_types::Mode;
    match category {
        HeapCategory::NeverHeap | HeapCategory::Value => ModedArgRc::None,
        HeapCategory::AlwaysHeap | HeapCategory::Mixed => {
            let guarded = matches!(category, HeapCategory::Mixed);
            match (owned_binding, mode) {
                (true, Mode::Owned) => {
                    if guarded { ModedArgRc::IncGuarded } else { ModedArgRc::Inc }
                }
                (true, Mode::Borrowed | Mode::Copy) => ModedArgRc::None,
                (false, Mode::Owned | Mode::Copy) => ModedArgRc::None,
                (false, Mode::Borrowed) => {
                    if guarded { ModedArgRc::PostDecGuarded } else { ModedArgRc::PostDec }
                }
            }
        }
    }
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // --- Function application ---

    #[allow(clippy::too_many_arguments)] // +1 for the S110 W1 dispatch carrier
    pub(crate) fn compile_apply(
        &mut self,
        callee: &MonoExpr,
        args: &[MonoExpr],
        span: Span,
        resolved_call: Option<&ResolvedCall>,
        // S110 W1 (`backend-keyed-consumer.md` §1.1): the Apply-span
        // `resolved_target` — the STORAGE FQ typecheck resolved the dispatch leg
        // to. The keyed-read carrier for the `resolved_call`-present paths
        // (BuiltinFn / TraitMethod / SigDispatch). `None` for a bare-`Var`-callee
        // direct call (that carrier is on the callee `Var` node, read in
        // `compile_var_apply`).
        apply_target: Option<&FQSymbol>,
        apply_type: Option<&cranelisp_types::Type>,
        // B3.4 (§4.1): the NoEscape + eligibility verdict for a use-site
        // data-constructor call, computed at the `Apply` dispatch (the sole node
        // carrying the escape fact). Consumed only by `compile_var_apply`'s
        // constructor arm; `false` everywhere else ⇒ today's heap path verbatim.
        stack: bool,
        // §13.7 (FIXME 0664): the recorded escape fact (`node_escapes`) of THIS
        // `Apply`, threaded to the COW seam (`compile_builtin_fn_call` stashes it
        // for `cow_source_ownership`'s escape gate). `None` ⇒ absent ⇒ inc default.
        apply_escapes: Option<bool>,
    ) -> Result<Value, CranelispError> {
        // TCO fast-path: a tail self-call jumps to the loop header instead of
        // emitting a call. Self-call identity is decided by the ONE shared
        // `is_self_call` predicate (Principle 7 / Principle 24; `backend.md`
        // §2.7.1; BC §3 invariant 10) — NEVER by bare written-name equality (the
        // 0632 name-as-identity class). It covers both shapes in one place:
        //
        // - **carrier-keyed** — the callee `Var`'s `resolved_target` storage FQ ==
        //   this fn's storage identity `{ctx.current_module, current_fn_name}`
        //   (module AND symbol). typecheck records exactly this FQ for a genuine
        //   self-call and records NOTHING for a shadowing `let`/`fn`/param local
        //   (which resolves at a deeper frame) — so a carrier-absent callee never
        //   matches, falls through to `compile_var_apply`, whose local `variables`
        //   check finds the shadow and emits an indirect call (the `(defn s1 [x]
        //   (let [s1 (fn [y] y)] (s1 x)))` §4.6 lexical-shadow case — LOCAL wins,
        //   no hang). The pre-S113 bare `*name == *fn_name` match was DELETED (not
        //   demoted to a fallback — the keyed-read-else-re-resolve hybrid
        //   `backend-keyed-consumer.md` §1.2 REJECTs).
        // - **SigDispatch mangled-name** — the monomorphised constrained-poly
        //   self-recursion shape (compiling `user/countdown$Int`, its recursive
        //   `(countdown ...)` resolves to `SigDispatch{user/countdown$Int}` whose
        //   mangled name == `current_fn_name`). The 0519 `{home}/{bare}${sig}`
        //   mangle embeds the module, so a cross-module same-signature dispatch
        //   fails to match by construction.
        //
        // The same predicate is consumed by the B3.4 stack-alloc gate 3
        // (`body_has_self_call`) and the spark SCC classifier
        // (`classify_spark_callee`) — one source of truth, so the TCO back-edge
        // set and the stack-alloc decline can never diverge (FIXME 0654; the
        // divergence was a latent loop-carried stack-slot UAF).
        if self.in_tail_position
            && self.tail_loop_block.is_some()
            && args.len() == self.fn_param_count
            && crate::compiler::is_self_call(
                callee,
                resolved_call,
                &self.ctx.current_module,
                self.current_fn_name.as_ref(),
            )
        {
            return self.compile_tail_self_call(args);
        }

        // CRITICAL: Args are never in tail position.
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;

        // --- Lenient apply-argument pre-pass (lenient-eval.md §2.5, §4.4) ---
        //
        // This is reached ONLY on the non-tail, non-TCO-self-call arm: the two
        // TCO self-call fast paths above `return` early, so a tail self-jump can
        // never reach the spark/force barrier (§2.5.3 — a jump to the loop header
        // would bypass the force). Trace bodies and `CRANELISP_NO_LENIENT` suppress
        // sparking exactly as the `let` site does (§2.3, §2.4). When ≥2 arguments
        // are independently worth sparking, create+spark an IVar per sparkable
        // argument here (Phase 1); the dispatch below then FORCES each at its
        // left-to-right position (Phase 2, the barrier) before any call code is
        // emitted, and feeds the forced values through the unchanged apply
        // lowering (Phase 3). See `maybe_force_sparked_arg`.
        if !*LENIENT_DISABLED
            && !self.in_trace_body
            && !self.suppress_spark_gate
            && !is_io_combinator_call(resolved_call)
        {
            // Admission filter (lenient-eval.md §2.8.2 / §2.8.6): M-static (the
            // default) admits only recursive-SCC ∧ non-tail candidates via the
            // single-sourced classifier; `CRANELISP_SPARK_ADMIT=syntactic` selects
            // the pre-S104 §2.2 filter for `/qa`'s comparison row. Apply args carry
            // no independence carve-out (§2.5.2); the ≥2 gate composes identically
            // inside `find_sparkable_args_with` for both filters (Principle 7).
            let sparkable = match *SPARK_ADMIT {
                SparkAdmit::Syntactic => {
                    let constructors = self.collect_module_constructors();
                    find_sparkable_args(args, &constructors)
                }
                SparkAdmit::Mstatic => {
                    let recursive = self.mstatic_recursive_set();
                    find_sparkable_args_with(args, |e| {
                        self.mstatic_admits_candidate(e, &recursive)
                    })
                }
            };
            if sparkable.len() >= 2 {
                // S104 Wave 0 — record the M-static classification of each
                // sparkable argument for the discrimination experiment
                // (measurement-only; gated on CRANELISP_SPARK_STATS; does NOT
                // change admission). `lenient-eval.md` §2.8.6.
                self.record_spark_sites_apply(args, &sparkable);
                // Create-gate (§3.6.2): a runtime budget branch wraps the site,
                // shared with the `let` site via `emit_create_gate`. The lenient
                // arm runs the three-phase spark path (create+spark, force
                // barrier, dispatch); the direct arm runs the unchanged
                // sequential apply (no `sparked_args` installed ⇒ every argument
                // is `compile_expr`'d in place, nothing allocated). Both arms
                // dispatch the *same* call and produce its result Value; the gate
                // joins them. The TCO self-call fast paths `return` early ABOVE
                // this point, so a tail self-jump never reaches the gate (§2.5.3).
                let n = sparkable.len();
                return self.emit_create_gate(
                    n,
                    span,
                    // Lenient arm — budget granted.
                    |this| {
                        // Phase 1: create + spark an IVar per sparkable argument —
                        // verbatim the §4.2 Phase-1 emission applied to argument
                        // positions. Thunk bodies compile in fresh inner
                        // FnCompilers (no leakage). This is the ONLY arm that
                        // allocates IVars/thunks.
                        let mut map: HashMap<usize, Value> =
                            HashMap::with_capacity(sparkable.len());
                        for idx in sparkable {
                            let arg = &args[idx];
                            let thunk_expr = MonoExpr::Lambda {
                                params: vec![],
                                body: Box::new(arg.clone()),
                                span: arg.span(),
                                ty: ConcreteType::Fn(vec![], Box::new(arg.ty().clone())),
                                confined: None,
                                escapes: None,
                                unique_static: None,
                            };
                            // Compile the spark-thunk body via the single-source
                            // helper (`compile_spark_thunk`), which raises BOTH
                            // spark flags around the thunk compile and restores
                            // them (error-safe):
                            //  - Capture-by-borrow (S99, FIXME 0461; lenient-eval.md
                            //    §4.4.1): this apply-arg spark is structurally joined
                            //    — Phase 2's barrier forces every sparked IVar before
                            //    the call instruction, so the parent frame is provably
                            //    live across spark→join→call; the thunk's heap captures
                            //    are borrowed, not retained (toggle-gated).
                            //  - Gate 5 (§4.3, FIXME 0525): the relocated construction
                            //    in the thunk body declines stack allocation (its slot
                            //    would dangle at the join — hard UAF).
                            let thunk_val = this.compile_spark_thunk(&thunk_expr)?;
                            let ivar_val = this.emit_extern_call(
                                "cranelisp_ivar_create",
                                &[thunk_val],
                                span,
                            )?;
                            this.emit_extern_call("cranelisp_ivar_spark", &[ivar_val], span)?;
                            map.insert(idx, ivar_val);
                        }

                        // Install this apply's spark context (keyed by the
                        // argument-slice base pointer), dispatch through the
                        // unchanged lowering (Phase 2 barrier-forces each sparked
                        // position at its left-to-right slot, Phase 3 calls), then
                        // restore the enclosing apply's context. The pointer key
                        // makes a nested apply / constructor incapable of
                        // consulting this map.
                        let saved_spark = this.sparked_args.replace((args.as_ptr(), map));
                        // B3.4: the lenient/sparked arm keeps constructions on the
                        // heap (`stack = false`) — the sparked-arg interplay is out
                        // of the increment-I stack scope (§4.3). Sound: declining is
                        // always correct.
                        let result = this.dispatch_apply(
                            callee,
                            args,
                            span,
                            resolved_call,
                            apply_target,
                            apply_type,
                            saved_tail,
                            false,
                            apply_escapes,
                        );
                        this.sparked_args = saved_spark;
                        result
                    },
                    // Direct arm — over budget. The existing sequential apply,
                    // NO `sparked_args` installed ⇒ every argument `compile_expr`'d
                    // in place; nothing allocated (§3.6.3 floor).
                    |this| {
                        this.dispatch_apply(
                            callee,
                            args,
                            span,
                            resolved_call,
                            apply_target,
                            apply_type,
                            saved_tail,
                            false,
                            apply_escapes,
                        )
                    },
                );
            }
        }

        // Sequential apply (no sparkable arguments): dispatch unchanged. A
        // non-lenient apply does NOT touch `sparked_args`; the pointer-identity
        // guard in `maybe_force_sparked_arg` ensures its own argument slice never
        // matches an enclosing apply's installed map.
        self.dispatch_apply(callee, args, span, resolved_call, apply_target, apply_type, saved_tail, stack, apply_escapes)
    }

    /// Dispatch a (non-TCO, args-not-in-tail) application through the resolved-
    /// call / var-apply / closure-call lowering. Shared by the sequential and
    /// lenient apply paths so the lenient pre-pass reuses the *unchanged* apply
    /// lowering (lenient-eval.md §4.4 Phase 3) rather than forking it.
    #[allow(clippy::too_many_arguments)] // +1 for the B3.4 stack-eligibility hint
    fn dispatch_apply(
        &mut self,
        callee: &MonoExpr,
        args: &[MonoExpr],
        span: Span,
        resolved_call: Option<&ResolvedCall>,
        // S110 W1: the Apply-span dispatch carrier (§1.1). Consumed by the
        // `resolved_call`-present path (`compile_resolved_call`).
        apply_target: Option<&FQSymbol>,
        apply_type: Option<&cranelisp_types::Type>,
        saved_tail: bool,
        // B3.4 (§4.1): stack-eligibility hint for a use-site constructor call;
        // consumed by `compile_var_apply`.
        stack: bool,
        // §13.7 (FIXME 0664): this Apply's escape fact, threaded to the COW seam.
        apply_escapes: Option<bool>,
    ) -> Result<Value, CranelispError> {
        // Check for resolved call (builtin, trait method, sig-dispatch, auto-curry).
        if let Some(resolved) = resolved_call {
            return self.compile_resolved_call(resolved.clone(), args, span, saved_tail, apply_target, apply_escapes);
        }

        // Regular function call: callee must be a Var referring to a known function,
        // a data constructor, or a local variable holding a closure.
        if let MonoExpr::Var {
            name,
            span: var_span,
            ..
        } = callee
        {
            return self.compile_var_apply(name, *var_span, callee, args, span, saved_tail, stack);
        }

        // Callee is not a variable -- could be a closure call (Ring 1).
        // Closure body is a user function — consuming convention.
        let callee_val = self.compile_expr(callee)?;
        let arg_vals = self.compile_consuming_arg_list(args)?;
        self.in_tail_position = saved_tail;

        let result = self.compile_closure_call(callee_val, &arg_vals, span)?;

        // Protect the return value: if the result is heap-typed, inc it
        // before freeing the closure. The closure's drop glue will dec
        // all captured heap values — if the result aliases a capture,
        // the inc prevents premature deallocation. The caller's later
        // dec (scope cleanup or parent expression) restores balance.
        if let Some(ty) = apply_type {
            let category =
                signature_heap_category(ty, Some(self.ctx.symbol_tables));
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_inc(&mut self.builder, self.module, result);
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_inc_guarded(&mut self.builder, self.module, result);
                }
                HeapCategory::NeverHeap | HeapCategory::Value => {}
            }
        }

        // Dec the temporary closure after the call. The closure was a
        // temporary expression (not a named variable), so nobody else
        // will dec it. Load the drop glue pointer from the closure and
        // use it for cleaning up captured heap values.
        self.emit_closure_dec(callee_val, span);

        Ok(result)
    }

    /// Compile a call to a resolved callee (builtin, trait method, sig-dispatch,
    /// or auto-curry). Handles the four `ResolvedCall` variants — one named
    /// `FnCompiler` method per variant (S111 R5 §2 — pure protocol-boundary
    /// extraction, byte-identical). TraitMethod and SigDispatch share
    /// `compile_moded_user_call` (the P7 dedup: identical below the `sym` bind).
    fn compile_resolved_call(
        &mut self,
        resolved: ResolvedCall,
        args: &[MonoExpr],
        span: Span,
        saved_tail: bool,
        // S110 W1 (§1.1): the Apply-span `resolved_target` — the STORAGE FQ of
        // the dispatch-selected callee. For BuiltinFn/TraitMethod/SigDispatch this
        // is the keyed-read carrier the S1/S2/S5/S6/S7/S8/S9 sites consume;
        // AutoCurry (a value-seam leg) is untouched this wave.
        apply_target: Option<&FQSymbol>,
        // §13.7 (FIXME 0664): this Apply's escape fact, for the COW seam.
        apply_escapes: Option<bool>,
    ) -> Result<Value, CranelispError> {
        match resolved {
            ResolvedCall::BuiltinFn { name: ref op_name } => {
                self.compile_builtin_fn_call(op_name, args, span, saved_tail, apply_target, apply_escapes)
            }
            ResolvedCall::TraitMethod { ref mangled_name, .. } => {
                let sym = Symbol::from(mangled_name.as_ref());
                self.compile_moded_user_call(&sym, args, span, saved_tail, apply_target)
            }
            ResolvedCall::SigDispatch { mangled_name } => {
                let sym = Symbol::from(mangled_name.as_ref());
                self.compile_moded_user_call(&sym, args, span, saved_tail, apply_target)
            }
            ResolvedCall::AutoCurry {
                ref target_name,
                applied_count,
                total_count,
                ref trait_resolution,
            } => self.compile_auto_curry_call(
                target_name,
                args,
                applied_count,
                total_count,
                trait_resolution.as_deref(),
                span,
                saved_tail,
                apply_target,
            ),
            // `ResolvedCall` is `#[non_exhaustive]` (cranelisp-types crate-root
            // policy): a wildcard arm is required for cross-crate matches. Any
            // future variant the backend does not yet lower is a codegen error
            // naming the call rather than a silent miscompile.
            other => Err(CranelispError::CodegenError {
                message: format!("unsupported resolved-call variant in codegen: {other:?}"),
                location: ErrorLocation::from_span(span),
            }),
        }
    }

    /// S111 R5 §2.1 (Principle 7): the single "does the keyed entry carry a GOT
    /// slot" predicate, shared by the extern-primitive and platform GOT-dispatch
    /// arms (was the identical inline predicate at both — the §2.1 dedup). Pure
    /// (no side effects), so evaluating it at each arm's point is byte-identical
    /// to the two former inline copies.
    fn apply_target_has_got_slot(&self, apply_target: Option<&FQSymbol>) -> bool {
        apply_target
            .and_then(|fq| self.ctx.entry_at(fq))
            .is_some_and(|(_, e)| e.callable_got_slot().is_some())
    }

    /// The `ResolvedCall::BuiltinFn` arm (S111 R5 §2.3). A linear guard chain:
    /// the four inline-effect interceptors (`bind`/`select`/`race`/`sleep`), the
    /// vec-op and trace-accessor intercepts, then the three heavy dispatch
    /// classes (`compile_extern_primitive_call` / `compile_platform_or_direct_extern_call`
    /// / `compile_inline_ring0_call`), each delegating.
    fn compile_builtin_fn_call(
        &mut self,
        op_name: &Symbol,
        args: &[MonoExpr],
        span: Span,
        saved_tail: bool,
        apply_target: Option<&FQSymbol>,
        // §13.7 (FIXME 0664): this Apply's escape fact — stashed on `self` just
        // before `compile_vec_op` so `cow_source_ownership` reads it for the
        // escape gate. Set at the vec-op call (after args are compiled, so a
        // nested-arg apply cannot clobber it).
        apply_escapes: Option<bool>,
    ) -> Result<Value, CranelispError> {
        // Decision 24: uniform consuming convention. Extern primitives
        // dec their own heap args; inline builtins operate on NeverHeap
        // operands. The caller never emits a post-call temporary dec.

        // IO bind: intercept and compile inline.
        // bind uses consuming semantics: it takes ownership of both args
        // by storing them in the Bind node. For variables, inc to add
        // the Bind node's reference. For temporaries, transfer ownership
        // (temp starts at rc=1, Bind node inherits it — no inc/dec needed).
        if op_name.as_ref() == "bind" {
            let arg_vals = self.compile_consuming_arg_list(args)?;
            self.in_tail_position = saved_tail;
            return self.compile_bind_inline(&arg_vals, span);
        }

        // Race/select combinators (S96 Chunk C, slice 7): name-matched
        // here exactly like `bind` (the inline-primitive precedent — NOT
        // an inferred AST marker; `io-trampoline.md §16.2`). `select`
        // takes one branch `Vec (IO a)` (consuming convention, so a
        // temporary `[..]` literal transfers its rc and a `Var` is inc'd
        // once); `race a b` builds the same node over a 2-element branch
        // Vec from its two IO args (`compile_race` compiles the args
        // itself via `compile_vec_lit`). Both produce the one
        // `IO_TAG_SELECT` node (`io-trampoline.md §16.3/§16.4`).
        if op_name.as_ref() == "select" {
            let arg_vals = self.compile_consuming_arg_list(args)?;
            self.in_tail_position = saved_tail;
            return self.compile_select(&arg_vals, span);
        }
        if op_name.as_ref() == "race" {
            self.in_tail_position = saved_tail;
            return self.compile_race(args, span);
        }

        // `sleep` — the runtime timer poll leaf (S96 Chunk C4, slice 7;
        // `reactor.md §2.18`). Name-matched here like `race`/`select`/`bind`
        // (the inline-primitive precedent). `compile_sleep` builds an
        // `IO_TAG_EFFECT_POLL` node whose `code_ptr` is the RUNTIME symbol
        // `runtime/sleep_pollfn` (the new non-GOT runtime-symbol path —
        // distinct from `compile_poll_effect`'s GOT-slot load).
        if op_name.as_ref() == "sleep" {
            self.in_tail_position = saved_tail;
            return self.compile_sleep(args, span);
        }

        // Vec operations: intercept and compile inline.
        // Vec ops handle their own temporary cleanup internally
        // via emit_vec_drop_if_temporary (COW-specific, not post-call
        // convention). See ring2-rc.md §3.3.
        if is_vec_primitive(op_name) {
            let arg_vals = self.compile_arg_list(args)?;
            self.in_tail_position = saved_tail;
            // §13.7 (FIXME 0664): stash THIS COW Apply's escape fact for
            // `cow_source_ownership`. Set AFTER `compile_arg_list` (so a nested-arg
            // apply's own stash cannot clobber it) and immediately before the
            // vec-op dispatch — no apply is compiled between here and the read.
            self.pending_cow_escapes = apply_escapes;
            if let Some(val) = self.compile_vec_op(op_name, args, &arg_vals, span)? {
                return Ok(val);
            }
            // Fall through to extern if compile_vec_op returned None.
            return self.compile_extern_call(op_name, &arg_vals, span);
        }

        // Trace ADT field accessors (`name`/`params`/`result`/
        // `children`/`nanos`) are seeded by int's bootstrap as bare-named
        // `DefKind::Primitive` entries with NO GOT slot and NO code — the
        // bodies are the `cranelisp_trace_*` intrinsics in
        // `cranelisp-intrinsics::trace`, published via `intrinsics_table()`
        // (FIXME 0256). typecheck resolves the call as
        // `BuiltinFn { name: "nanos" }` with no rewrite, so without this
        // intercept the unknown-builtin arm below would emit
        // `Linkage::Import` for the undefined symbol `nanos`
        // ("can't resolve symbol nanos" — FIXME 0292 / 0285 defect 1).
        //
        // The bare-name → intrinsic-name mapping lost in the W1.5 trace
        // relocation is restored here: rewrite to `cranelisp_trace_<field>`
        // and route through `compile_extern_call`, which the catalog
        // resolves identically in JIT (`JITBuilder::symbol`), cache-hit
        // (`Linker::register_symbol`), and `--link` (archive force-link).
        // Scoped to a Trace-typed receiver (the single arg's inferred type
        // is `primitives/Trace`) so a user `nanos`/`name` field on an
        // unrelated ADT is not hijacked. The intrinsics use the consuming
        // convention (each consumes its Trace arg via `consume_trace_call`),
        // matching the other `cranelisp_trace_*` externs.
        if let Some(intrinsic) = self.trace_accessor_intrinsic(op_name, args) {
            let arg_vals = self.compile_consuming_arg_list(args)?;
            self.in_tail_position = saved_tail;
            return self.compile_extern_call(intrinsic, &arg_vals, span);
        }

        if is_extern_primitive(op_name) {
            return self.compile_extern_primitive_call(op_name, args, span, saved_tail, apply_target);
        }

        // Unrecognized builtin: a platform-effect function or a direct-extern.
        if !primitives_inline::is_known_builtin(op_name) {
            return self.compile_platform_or_direct_extern_call(
                op_name, args, span, saved_tail, apply_target,
            );
        }

        self.compile_inline_ring0_call(op_name, args, span, saved_tail, apply_target)
    }

    /// The extern-primitive dispatch class (S111 R5 §2.3; was the
    /// `is_extern_primitive` arm of `compile_builtin_fn_call`). Consuming
    /// convention with the `string-identity` no-consume exception + the `str-len`
    /// H3 RC-stat tally; then the §2.1 GOT-vs-direct-extern decision.
    fn compile_extern_primitive_call(
        &mut self,
        op_name: &Symbol,
        args: &[MonoExpr],
        span: Span,
        saved_tail: bool,
        apply_target: Option<&FQSymbol>,
    ) -> Result<Value, CranelispError> {
        // Decision 24 (Sprint 56 Step 2c): uniform consuming
        // convention. Every extern dec's its own heap args via
        // `rc::consume_shallow` (simple heap) or
        // `crate::drop::consume_*` (complex heap — SList, Sexp,
        // Vec, Trace ADT, IO tree). Caller incs heap-typed Var
        // args here so the Var's scope still holds a live
        // reference after the callee's dec. `string-identity`
        // is special: it inc-and-returns its arg, so callers
        // stay on plain arg compilation (the identity retains
        // the original reference).
        let arg_vals = if op_name.as_ref() == "string-identity" {
            self.compile_arg_list(args)?
        } else {
            self.compile_consuming_arg_list(args)?
        };
        // H3 per-extern adaptation-pair attribution (§9.2 / §13.2.1):
        // `str-len` is the single increment-I template instance of the
        // dual-symbol convention — a hand-audited only-read consuming
        // extern whose call sites pay a Decision-24 adaptation pair
        // (the consuming dec, plus an adaptation inc on a borrowed
        // arg). Tally the site into `CRANELISP_RC_STATS` so `/qa`'s
        // L-D5 lane reads the per-extern pair population. Runtime tally
        // (the pair is paid at run) gated on the codegen-time RC_STATS
        // switch (off ⇒ no emitted IR ⇒ byte-identical).
        if op_name.as_ref() == "str-len" {
            heap::emit_rc_stat_call_gated(
                &mut self.builder,
                self.module,
                "runtime/extern_adapt_str_len",
            );
        }
        self.in_tail_position = saved_tail;
        // Per Decision 0048 §"Structural invariant — backend
        // dep-ban": every PRIMITIVE call site MUST emit
        // GOT-indirect dispatch against `__cranelisp_got_primitives`
        // — never a `Linkage::Import` direct extern, which the
        // cache-mode in-process linker (`cache::linker::Linker`)
        // cannot resolve via dlsym. Primitives registered in
        // `PRIMITIVES_TABLE` (see `cranelisp-primitives::PRIMITIVES_TABLE`)
        // have a populated GOT slot.
        //
        // S110 W1 (§1.1/§1.3 — S1): the GOT-vs-direct-extern
        // discrimination is now a keyed read of the Apply carrier, not
        // a symbol-table scan. A slot-carried primitive (the fetched
        // entry answers `callable_got_slot()`) dispatches GOT-indirect;
        // otherwise it is the documented `resolved_target`-with-no-slot
        // / known-extern-name arm — an **int-hosted intrinsic** (Trace
        // ADT field accessors `cranelisp_trace_name`/`_params`/… or the
        // like) registered via `JITBuilder::symbol()` from
        // `int_intrinsics()` and NOT a GOT-dispatched SymbolTable entry;
        // it lowers as a by-name `Linkage::Import` the JIT/cache linker
        // resolves. (Rev-2: no scan fallback — a slotless carrier is the
        // extern arm, a bare miss is the extern arm; both by-name.)
        let sym = Symbol::from(op_name.as_ref());
        if self.apply_target_has_got_slot(apply_target) {
            return self.compile_direct_call(&sym, &arg_vals, span, apply_target);
        }
        self.compile_extern_call(op_name, &arg_vals, span)
    }

    /// The unrecognized-builtin dispatch class (S111 R5 §2.3; was the
    /// `!is_known_builtin` arm). Platform GOT-adopt arm (§2.1 decision) else the
    /// as-built direct-extern fallback.
    fn compile_platform_or_direct_extern_call(
        &mut self,
        op_name: &Symbol,
        args: &[MonoExpr],
        span: Span,
        saved_tail: bool,
        apply_target: Option<&FQSymbol>,
    ) -> Result<Value, CranelispError> {
        // Platform functions use the consuming convention — the DLL owns heap
        // args (e.g. `CLString::own()` captures the string).
        let arg_vals = self.compile_consuming_arg_list(args)?;
        self.in_tail_position = saved_tail;
        // Platform GOT-indirect dispatch arm (TARGET shape;
        // platform-interface.md §6.2/§6.3, BC §3 "the
        // platform-interface codegen role"). When the platform
        // entry carries the NEW shape — a populated `got_slot`
        // adopted from the DLL's exported GOT
        // (`__cranelisp_got_platform_<name>`, manifest index) —
        // dispatch GOT-indirect, structurally identical to
        // user-module GOT dispatch. Backend does NOT emit the
        // platform GOT (the DLL exports it); it emits the
        // dispatch, referencing the GOT data symbol as a
        // `Linkage::Import` (resolved by `dlsym` in JIT / `ld` in
        // `--link`).
        //
        // TRANSITIONAL MECHANICS: the fetched entry answers
        // `callable_got_slot()` IFF it carries the new `got_slot:
        // Some(_)` shape; the as-built shape carries `got_slot: None`
        // (the worker stores the fn ptr via a host-allocated slot +
        // `JITBuilder::symbol(jit_name, ptr)` direct extern, §9). So
        // this `if`-guard activates the new arm exactly when
        // int/platform flip to the DLL-exported-GOT model, and keeps
        // the as-built direct-extern path live until then — no mode
        // fork, no flag (Principle 11). When the flip completes the
        // `compile_extern_call` fallback below becomes dead for
        // platform fns (the expected narrowing signal).
        //
        // S110 W1 (§1.1/§1.3 — S2): keyed read of the Apply carrier
        // replaces the `resolve_got_target` scan; behaviour-identical
        // (the carrier records the same entry the scan terminated at).
        let sym = Symbol::from(op_name.as_ref());
        if self.apply_target_has_got_slot(apply_target) {
            // `compile_direct_call` emits the GOT-indirect dispatch AND
            // stamps the platform fn-name into the returned Effect
            // node's field-3 when the target is a `DefKind::PlatformEffect`
            // (step 2/4 of the fault-guarded dispatch funnel; S81 / FIXME
            // 0327; BC §3 + §5 invariant 9 Option A). The stamp lives at
            // that single chokepoint so EVERY dispatch path stamps —
            // this `BuiltinFn` arm and the bare-import `compile_var_apply`
            // path alike — and it lands at node-construction time (before
            // the force), so the baked name survives a thunk panic on the
            // fault path.
            return self.compile_direct_call(&sym, &arg_vals, span, apply_target);
        }
        // As-built fallback: direct `Linkage::Import` against the
        // mangled jit_name (the platform fn ptr reaches the JIT via
        // `JITBuilder::symbol(jit_name, ptr)`; the cache linker
        // registers it identically). Retires when the GOT flip
        // lands (§6.3 verdict).
        self.compile_extern_call(op_name, &arg_vals, span)
    }

    /// The inline Ring-0 primitive dispatch class (S111 R5 §2.3; was the inline
    /// arm). `try_emit_inline_primitive` with the drift fall-through to a
    /// GOT-indirect `compile_direct_call`.
    fn compile_inline_ring0_call(
        &mut self,
        op_name: &Symbol,
        args: &[MonoExpr],
        span: Span,
        saved_tail: bool,
        apply_target: Option<&FQSymbol>,
    ) -> Result<Value, CranelispError> {
        // Inline Ring 0 primitive (arithmetic, comparison, boolean).
        // All operands are NeverHeap (Int/Bool/Float) — no dec work.
        //
        // Per FIXME 0174 + `facades/backend.md` §"Non-goals / forbidden
        // patterns": `try_emit_inline_primitive` returns `None` for
        // names outside the inline table — the caller MUST fall
        // through to the GOT-indirect path. `is_known_builtin` is
        // checked above so by this point the name IS in the table,
        // but we still pattern-match the `Some` arm conservatively;
        // a None here would indicate the two tables drifted apart.
        let arg_vals = self.compile_arg_list(args)?;
        self.in_tail_position = saved_tail;
        match primitives_inline::try_emit_inline_primitive(
            &mut self.builder, op_name, &arg_vals, span,
            self.module, self.ctx.panic_func_id,
        ) {
            Some(result) => result,
            None => {
                // Drift between `is_known_builtin` and
                // `try_emit_inline_primitive`: fall through to the
                // GOT-indirect path (Ring 0 primitives have GOT
                // slots per FIXME 0174 resolution).
                let sym = Symbol::from(op_name.as_ref());
                self.compile_direct_call(&sym, &arg_vals, span, apply_target)
            }
        }
    }

    /// The shared TraitMethod / SigDispatch dispatch (S111 R5 §2.2 — the P7
    /// dedup: both `ResolvedCall` arms are IDENTICAL below the `sym` bind).
    ///
    /// Per Decision 43 + FIXME 0185: backend has no trait knowledge.
    /// The pre-D43 `primitive_for_trait_method((TraitName, Symbol,
    /// TypeName))` dispatch table — keyed on `(Num, "+", Int)` →
    /// `add-i64` — is the canonical D43-forbidden pattern and has
    /// been deleted. Backend dispatches uniformly: every
    /// ResolvedCall::TraitMethod goes via the trait-impl's
    /// mangled name (e.g., `Num.+$Int`), GOT-indirect like any
    /// user function.
    ///
    /// Performance note: trait operator calls now traverse one
    /// extra call frame compared to the pre-D43 inline-IR path
    /// (the impl body is `(defn + [a b] (add-i64 a b))` — one
    /// hop to the inline-substituted primitive). FIXME 0185
    /// tracks the typecheck-side migration that restores inline
    /// optimisation by having typecheck emit `BuiltinFn { name:
    /// "add-i64" }` directly for primitive-implemented trait
    /// methods, bypassing the `TraitMethod` route entirely.
    /// User (trait-impl) / sig-dispatch function — moded consuming convention
    /// (§3.1): the callee's `ModeSummary` keys the per-position inc; temporaries
    /// to `Borrowed` params owe a post-call dec.
    fn compile_moded_user_call(
        &mut self,
        sym: &Symbol,
        args: &[MonoExpr],
        span: Span,
        saved_tail: bool,
        apply_target: Option<&FQSymbol>,
    ) -> Result<Value, CranelispError> {
        let (arg_vals, post_call_decs) =
            self.compile_consuming_arg_list_moded(args, apply_target)?;
        self.in_tail_position = saved_tail;
        let result = self.compile_direct_call(sym, &arg_vals, span, apply_target)?;
        self.emit_post_call_decs(&post_call_decs);
        Ok(result)
    }

    /// The `ResolvedCall::AutoCurry` arm (S111 R5 §2.2).
    #[allow(clippy::too_many_arguments)]
    fn compile_auto_curry_call(
        &mut self,
        target_name: &Symbol,
        args: &[MonoExpr],
        applied_count: usize,
        total_count: usize,
        trait_resolution: Option<&ResolvedCall>,
        span: Span,
        saved_tail: bool,
        apply_target: Option<&FQSymbol>,
    ) -> Result<Value, CranelispError> {
        // Compile applied args with consuming convention:
        // the auto-curry closure captures them, and the wrapper
        // will inc before forwarding to the target function.
        let arg_vals = self.compile_consuming_arg_list(args)?;
        self.in_tail_position = saved_tail;
        // S110 W2 (row 17): the Apply-span carrier is the plain-fn curry
        // target's STORAGE key (callee-span transport, W0.1b), threaded to
        // the wrapper's GOT read.
        self.compile_auto_curry(
            target_name,
            &arg_vals,
            applied_count,
            total_count,
            args,
            span,
            trait_resolution,
            apply_target,
        )
    }

    /// Compile a function application where the callee is a Var.
    /// Dispatches between data constructor, local closure, and direct call.
    #[allow(clippy::too_many_arguments)] // +1 for the B3.4 stack-eligibility hint
    fn compile_var_apply(
        &mut self,
        name: &Symbol,
        var_span: Span,
        callee: &MonoExpr,
        args: &[MonoExpr],
        span: Span,
        saved_tail: bool,
        // B3.4 (§4.1): stack-eligibility hint for this call IF it is a data
        // constructor. `false` ⇒ heap. Ignored for non-constructor callees.
        stack: bool,
    ) -> Result<Value, CranelispError> {
        // === Locals-BEFORE-keyed-read (S110 W1, FIXME 0619 item 2 — the §1.1
        // pinned invariant). ===
        // The environment/locals binding is checked FIRST, before ANY keyed read
        // of the callee `Var`'s `resolved_target`. The producer's self-recursion
        // carve-out over-matches a same-named local (it records the enclosing
        // fn's storage FQ on a shadowing local Var), so a keyed read taken before
        // the locals check would mis-dispatch a local closure call to the
        // carrier's FQ. Checking `variables` first makes a shadowing local
        // unconditionally win the closure-call path — the carrier is never
        // consulted for it.
        if self.variables.contains_key(name) {
            let callee_val = self.compile_expr(callee)?;
            // Closure body is a user function — consuming convention.
            let arg_vals = self.compile_consuming_arg_list(args)?;
            self.in_tail_position = saved_tail;
            return self.compile_closure_call(callee_val, &arg_vals, span);
        }

        // The callee `Var`'s carrier — the terminal STORAGE key typecheck
        // resolved (§1.1.2). Computed ONCE here and reused by both the S3/S4
        // ctor branch and the S5/S7 direct-call branch. For a construction-
        // position ctor this is now the CANONICAL `m/Type.Ctor` `member_key`
        // (the W1.1/0620 recorder flip records `resolved.storage_fq()`, not the
        // bare alias), so the keyed `ctor_meta_at` read below lands on the real
        // `DefKind::Constructor` `Def` — a direct read, NO chain-follow.
        let callee_target = match callee {
            MonoExpr::Var { resolved_target, .. } => resolved_target.as_ref(),
            _ => None,
        };

        // === S3/S4 — data-constructor call (keyed, S110 W1). ===
        // Flipped from the legacy `lookup_constructor` chain-follow to the keyed
        // `ctor_meta_at` read off the callee's carrier — now safe because the
        // producer records the canonical `member_key` for ctors (FIXME 0620
        // recorder flip). This removes the last apply-site caller of
        // `lookup_constructor` (Rev-2 §1.2: the ctor kind flips whole, no
        // hybrid; the value-position nullary/ctor-as-value sites are the
        // untouched-legacy W2 kinds). A non-ctor carrier (or a fn callee)
        // returns `None` from `extract_constructor` and falls through to the
        // S5/S7 keyed direct-call arm below. Covers data AND nullary ctors so no
        // ctor Var callee reaches `compile_direct_call`.
        if let Some((fqtn, meta)) = callee_target.and_then(|fq| self.ctx.ctor_meta_at(fq)) {
            let field_count = meta.fields.len();
            if args.len() != field_count {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "constructor '{name}' expects {field_count} args, got {}",
                        args.len()
                    ),
                    location: ErrorLocation::from_span(span),
                });
            }

            // Decision 24 (Sprint 56 Step 2c): uniform consuming convention.
            // The constructor stores args as fields; the ADT's drop glue
            // dec's heap-typed fields when the ADT itself reaches rc=0.
            // For variable args we inc so the caller's binding survives
            // scope cleanup — the ADT holds its own independent reference.
            // For temporary args, rc=1 transfers directly into the field.
            let arg_vals = self.compile_consuming_arg_list(args)?;
            self.in_tail_position = saved_tail;
            // R5 (§7.1): a value-flattened single-ctor type constructs by a
            // bare-word move of its single field (no alloc/header/tag). Classify
            // by the ctor's parent type (`value_layout` ignores the ADT's type
            // args, so `ADT(fqtn, [])` classifies exactly). `None` off-toggle /
            // non-`Value` ⇒ the heap/stack path below, byte-identical. `fqtn`
            // comes off the SAME legacy lookup — no second scan.
            let adt_ty = ConcreteType::ADT(fqtn, vec![]);
            if let Some(v) = self.value_construct(&adt_ty, &arg_vals) {
                return Ok(v);
            }
            // B3.4 (§4.1/§4.2): a NoEscape, all-scalar-payload constructor call in
            // a non-self-recursive function places its aggregate on a Cranelift
            // stack slot (immortal-RC header) instead of the RC heap. `stack` is
            // the verdict from `constructor_call_stack_eligible`; `false` ⇒ heap
            // `emit_alloc`, byte-identical to pre-B3.4.
            return self.emit_adt_construct_stackable(meta.tag, &arg_vals, span, stack);
        }

        // S5/S7 — user function (keyed): moded consuming convention (§3.1). A bare
        // `Var` callee with no resolved_call reaches dispatch here; the keyed read
        // of the callee `Var`'s carrier (`callee_target`, computed above) keys the
        // per-position elision + GOT dispatch off the resolved callee,
        // byte-identical when the callee carries no summary. The ctor kind was
        // fully handled above, so a `None` carrier here is a genuine non-ctor
        // reference (a hard error downstream if the carrier is absent — Rev-2,
        // never a fall-through to the scan).
        let (arg_vals, post_call_decs) =
            self.compile_consuming_arg_list_moded(args, callee_target)?;
        self.in_tail_position = saved_tail;
        let result = self.compile_direct_call(name, &arg_vals, var_span, callee_target)?;
        self.emit_post_call_decs(&post_call_decs);
        Ok(result)
    }

    /// Compile a list of argument expressions into Cranelift values.
    ///
    /// Plain compilation: no RC adjustments. Used for inline builtins whose
    /// operands are NeverHeap (Int/Bool/Float), and for data-constructor
    /// call-site arg preparation where the consuming inc happens via
    /// `compile_consuming_arg_list` (which this method backs). Under
    /// Decision 24 (uniform consuming) the plain form has a narrow role:
    /// pure-value builtins where RC does not apply.
    fn compile_arg_list(&mut self, args: &[MonoExpr]) -> Result<Vec<Value>, CranelispError> {
        let args_ptr = args.as_ptr();
        let mut vals = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            // A sparked argument is forced at this position (the left-to-right
            // barrier) instead of recompiled; otherwise compile normally.
            if let Some(forced) = self.maybe_force_sparked_arg(i, args_ptr, arg.span())? {
                vals.push(forced);
            } else {
                vals.push(self.compile_expr(arg)?);
            }
        }
        Ok(vals)
    }

    /// If argument `idx` of the application whose argument slice has base pointer
    /// `args_ptr` was sparked by the lenient apply-arg pre-pass (lenient-eval.md
    /// §4.4), force its IVar HERE (the left-to-right Phase-2 barrier), dec the
    /// calling thread's cell reference (`emit_rc_dec_for_ivar` → the IVar-aware
    /// dealloc that also frees any ferried error String), and return the forced
    /// rc=1 temporary. Returns `None` for a non-sparked position (compile
    /// normally).
    ///
    /// The `args_ptr` pointer-identity check is load-bearing: `self.sparked_args`
    /// is set only for the duration of the owning apply's dispatch, but a nested
    /// apply / constructor compiled while it is set has a *different* argument
    /// slice (distinct allocation ⇒ distinct base pointer), so it can never match
    /// and never force the wrong IVar by index collision (Principle 18).
    ///
    /// No consuming inc is owed for a sparked position: the cost heuristic
    /// guarantees a non-trivial `Apply`, so the forced value is an rc=1 temporary
    /// that transfers into the callee exactly like a sequentially-compiled
    /// temporary argument (lenient-eval.md §4.4 "RC / consuming convention").
    fn maybe_force_sparked_arg(
        &mut self,
        idx: usize,
        args_ptr: *const MonoExpr,
        span: Span,
    ) -> Result<Option<Value>, CranelispError> {
        let ivar_val = match &self.sparked_args {
            Some((ptr, map)) if std::ptr::eq(*ptr, args_ptr) => map.get(&idx).copied(),
            _ => None,
        };
        let Some(ivar_val) = ivar_val else {
            return Ok(None);
        };
        let forced = self.emit_extern_call("cranelisp_ivar_force", &[ivar_val], span)?;
        self.emit_rc_dec_for_ivar(ivar_val, span)?;
        Ok(Some(forced))
    }

    /// Compile args for a consuming callee (user-defined function).
    ///
    /// The callee dec's all heap-typed parameters at exit. We inc
    /// heap-typed variable arguments so the caller's binding survives
    /// the callee's dec. Temporary expressions start at rc=1 and
    /// the callee's dec frees them — no caller action needed.
    fn compile_consuming_arg_list(
        &mut self,
        args: &[MonoExpr],
    ) -> Result<Vec<Value>, CranelispError> {
        let args_ptr = args.as_ptr();
        let mut vals = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            // Sparked argument: force at this position (left-to-right barrier),
            // dec our cell reference, and push the forced rc=1 temporary with NO
            // consuming inc (it transfers into the callee like any temporary).
            if let Some(forced) = self.maybe_force_sparked_arg(i, args_ptr, arg.span())? {
                vals.push(forced);
                continue;
            }

            let val = self.compile_expr(arg)?;

            // Inc heap-typed variable arguments for consuming convention.
            if let MonoExpr::Var { name, .. } = arg
                && let Some(ty) = self.variable_types.get(name) {
                    let category =
                        signature_heap_category(ty, Some(self.ctx.symbol_tables));
                    // B3.3-R (§5.1): the consuming inc is always atomic. This was
                    // a through-binding site (per-binding Confined carrier),
                    // dropped as dead + latent-race code (/review B3.3) — the
                    // analysis produces no confined let-bindings today. The
                    // `_atomicity` mechanism is retained (probe-reachable); it is
                    // fed `Atomic` here.
                    let atomicity = heap::RcAtomicity::Atomic;
                    match category {
                        HeapCategory::AlwaysHeap => {
                            heap::emit_rc_inc_atomicity(
                                &mut self.builder, self.module, val, atomicity,
                            );
                        }
                        HeapCategory::Mixed => {
                            heap::emit_rc_inc_guarded_atomicity(
                                &mut self.builder, self.module, val, atomicity,
                            );
                        }
                        HeapCategory::NeverHeap | HeapCategory::Value => {}
                    }
                }

            vals.push(val);
        }
        Ok(vals)
    }

    /// §3.1 borrow-elision, caller side
    /// (`design/backend/ownership-codegen.md` §3.1): compile args for a
    /// statically-resolved user-function call whose callee carries an ownership
    /// [`ModeSummary`], keying the per-position RC emission off the callee's
    /// param modes instead of the uniform Decision-24 consuming inc.
    ///
    /// Returns `(arg_vals, post_call_decs)`. The caller MUST emit the returned
    /// post-call decs (via [`Self::emit_post_call_decs`]) AFTER the call
    /// instruction returns — they release temporaries passed to `Borrowed`
    /// params that the callee will not dec.
    ///
    /// Per heap-typed position (scalars are never RC-touched):
    /// - **Var arg, param `Owned`** — `emit_rc_inc[_guarded]`, verbatim today.
    ///   This is ALSO the adaptation path (a caller-borrowed Var handed to an
    ///   `Owned` position incs here, exactly as a match-field binding does).
    /// - **Var arg, param `Borrowed`/`Copy`** — SKIP the inc; the caller retains
    ///   ownership and its scope-cleanup dec is the single accounting; the callee
    ///   (compiled against the same vector, §3.2) emits no param dec.
    /// - **Temporary arg, param `Owned`** — no inc (ownership transfers at rc=1).
    /// - **Temporary arg, param `Borrowed`** — no inc AND record a post-call dec
    ///   (the callee will not dec the rc=1 temporary).
    ///
    /// **Byte-identical-off:** a `None` summary (analysis off, or a non-summary
    /// callee) reads every param `Owned` through [`ModeSummary::param_mode`], so
    /// the emission collapses to exactly [`Self::compile_consuming_arg_list`] and
    /// `post_call_decs` is empty — no moded edge, no new instruction (§2.2).
    fn compile_consuming_arg_list_moded(
        &mut self,
        args: &[MonoExpr],
        // S110 W1 (§1.1/§1.3 — S5): the callee's STORAGE FQ. The `ModeSummary`
        // is read off the ONE fetched entry instead of the `resolve_callee_summary`
        // scan (the callee-name param the scan needed is retired). `None` ⇒ no
        // summary (the byte-identical-off fast path below).
        resolved_target: Option<&FQSymbol>,
    ) -> Result<ModedArgList, CranelispError> {
        let summary = resolved_target
            .and_then(|fq| self.ctx.entry_at(fq))
            .and_then(|(_, entry)| entry.mode_summary().cloned());
        // Fast path: no summary (or an ABI-conservative one) ⇒ the elision cannot
        // fire on any position, so route through the unmodified consuming helper.
        // This is the structural byte-identical-off guarantee — the moded arm
        // below is never entered when no summary exists.
        let Some(summary) = summary.filter(|s| !s.is_abi_conservative()) else {
            return Ok((self.compile_consuming_arg_list(args)?, Vec::new()));
        };

        let args_ptr = args.as_ptr();
        let mut vals = Vec::with_capacity(args.len());
        let mut post_call_decs: Vec<PostCallDec> = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            let mode = summary.param_mode(i);

            // Sparked argument: forced rc=1 temporary (like any temporary). With
            // an `Owned` param it transfers; with `Borrowed` it owes a post-call
            // dec.
            if let Some(forced) = self.maybe_force_sparked_arg(i, args_ptr, arg.span())? {
                if mode == cranelisp_types::Mode::Borrowed {
                    // The forced value is a heap IVar result (rc=1); guarded dec
                    // is layout-safe whether AlwaysHeap or Mixed.
                    post_call_decs.push((forced, HeapCategory::Mixed));
                }
                vals.push(forced);
                continue;
            }

            // §3.3 consumer-driven in-frame projection elision
            // (`design/backend/ownership-codegen.md` §3.3): when a heap-typed
            // borrowed PROJECTION (a `vec-get` read the ownership pass marked with
            // a `provenance` site fact) is passed DIRECTLY into a `Borrowed`
            // parameter, the whole inc+dec pair collapses: `compile_vec_get` skips
            // the element materialization inc (via `elide_vecget_span`) and NO
            // post-call dec is owed. This is the F1 machinery-tax collapse and the
            // SOLE provably-safe elision — the borrowed element is consumed
            // in-place by the callee's borrow, never escapes the call, and never
            // outlives the root's fork-join-guaranteed liveness. Propagating a
            // borrowed projection across ANY other edge (an `Owned` position, a
            // function return, a store) is parallel-unsound (an escaping view
            // races a concurrent COW/free — observed in f4_sudoku), so those keep
            // the materialization inc and take the ordinary temporary path below.
            let elide_projection = mode == cranelisp_types::Mode::Borrowed
                && is_direct_vecget_projection(arg)
                && matches!(
                    HeapCategory::classify(arg.ty(), Some(self.ctx.symbol_tables)),
                    HeapCategory::AlwaysHeap | HeapCategory::Mixed
                );
            if elide_projection {
                let saved = self.elide_vecget_span.replace(arg.span());
                let val = self.compile_expr(arg)?;
                self.elide_vecget_span = saved;
                vals.push(val);
                // No inc (elided) and NO post-call dec: the callee borrows the
                // view and the root's owner keeps the element alive.
                continue;
            }

            let val = self.compile_expr(arg)?;

            // An **owned-binding Var** is a local variable (present in
            // `variable_types`) whose owner (the enclosing scope) decs it at
            // scope exit. Anything else at a `Var` position — a fn-as-value name,
            // a bare constructor — mints a FRESH rc=1 value (no scope owner)
            // exactly like a non-`Var` temporary, so it takes the temporary path.
            // This mirrors the pre-S102 `compile_consuming_arg_list` gate, which
            // inc'd ONLY Vars found in `variable_types`. The arg's category comes
            // from that binding's authoritative type, else from the node type.
            let (owned_binding, category) = match arg {
                MonoExpr::Var { name, .. } if self.variable_types.contains_key(name) => {
                    let ty = self.variable_types.get(name).cloned().unwrap_or_else(|| {
                        unreachable!("contains_key checked above")
                    });
                    (true, signature_heap_category(&ty, Some(self.ctx.symbol_tables)))
                }
                _ => (false, HeapCategory::classify(arg.ty(), Some(self.ctx.symbol_tables))),
            };
            // B3.3-R (§5.1): the consuming inc (the adaptation path too) is
            // always atomic. This was a through-binding/arg site, dropped as dead
            // + latent-race code (/review B3.3) — an arg node is walked off-parent
            // (Crossing ⇒ Atomic) and the analysis produces no confined
            // let-bindings today. The `_atomicity` mechanism is retained
            // (probe-reachable); it is fed `Atomic` here.
            let atomicity = heap::RcAtomicity::Atomic;
            match moded_arg_rc(category, mode, owned_binding) {
                ModedArgRc::None => {}
                ModedArgRc::Inc => {
                    heap::emit_rc_inc_atomicity(&mut self.builder, self.module, val, atomicity)
                }
                ModedArgRc::IncGuarded => {
                    heap::emit_rc_inc_guarded_atomicity(
                        &mut self.builder, self.module, val, atomicity,
                    )
                }
                ModedArgRc::PostDec => post_call_decs.push((val, HeapCategory::AlwaysHeap)),
                ModedArgRc::PostDecGuarded => post_call_decs.push((val, HeapCategory::Mixed)),
            }

            vals.push(val);
        }
        Ok((vals, post_call_decs))
    }

    /// Emit the post-call decs recorded by
    /// [`Self::compile_consuming_arg_list_moded`] for temporaries passed to
    /// `Borrowed` params. Emitted AFTER the call returns; each releases an rc=1
    /// temporary the callee borrowed but did not consume (§3.1). Guarded/unguarded
    /// dec per the recorded [`HeapCategory`].
    fn emit_post_call_decs(&mut self, decs: &[PostCallDec]) {
        let dealloc_id = self.ctx.dealloc_func_id;
        for (val, category) in decs {
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_dec(&mut self.builder, self.module, *val, dealloc_id, None);
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_dec_guarded(
                        &mut self.builder,
                        self.module,
                        *val,
                        dealloc_id,
                        None,
                        true,
                    );
                }
                HeapCategory::NeverHeap | HeapCategory::Value => {}
            }
        }
    }

    /// Compile a call to a named function.
    ///
    /// When GOT slots are present: loads the function pointer from the GOT slot
    /// and emits a `call_indirect` instruction.
    /// Otherwise: emits a direct `call` instruction via FuncId.
    pub(crate) fn compile_direct_call(
        &mut self,
        name: &Symbol,
        arg_vals: &[Value],
        span: Span,
        // S110 W1 (`backend-keyed-consumer.md` §1.1/§1.3): the STORAGE FQ of the
        // callee. The ONE keyed fetch (`entry_at`) replaces the four
        // apply-site resolvers (`resolve_poll_effect_target`,
        // `resolve_got_target`, `resolve_platform_effect_target`,
        // `resolve_extern_target` — S6/S7/S8/S9). Locals are filtered upstream
        // (`compile_var_apply`), so a call reaching here MUST carry a target.
        resolved_target: Option<&FQSymbol>,
    ) -> Result<Value, CranelispError> {
        // Rev-2 (§1.2): NO soft fallback. A carrier-`None` on a table-reference
        // call is a hard `CodegenError` — never a fall-through to the retired
        // name-resolver scan; entry-miss likewise (§1.3, Principle 18).
        let fq = resolved_target.ok_or_else(|| CranelispError::CodegenError {
            message: format!(
                "call to '{name}' reached codegen with no resolved_target carrier \
                 (S110 W1 keyed read; backend-keyed-consumer.md §1.2)"
            ),
            location: ErrorLocation::from_span(span),
        })?;
        let (home, entry) = self.ctx.entry_at(fq).ok_or_else(|| CranelispError::CodegenError {
            message: format!(
                "resolved_target '{fq}' for call '{name}' fetched no symbol-table \
                 entry (S110 W1 entry-miss; backend-keyed-consumer.md §1.3)"
            ),
            location: ErrorLocation::from_span(span),
        })?;

        // Whether the fetched entry is a platform effect (drives S6 poll + S8
        // stamp). Read once off the ONE fetched entry.
        let platform_effect_poll: Option<(usize, Vec<cranelisp_types::Type>)> = match &entry {
            ModuleEntry::Def { kind, scheme, .. }
                if matches!(
                    kind.as_ref(),
                    DefKind::PlatformEffect { poll_shape: true, .. }
                ) =>
            {
                let DefKind::PlatformEffect { got_slot, .. } = kind.as_ref() else {
                    unreachable!("matched poll-shape PlatformEffect above")
                };
                // The effect's param types (for the state-closure capture-dec
                // glue). A platform effect's scheme is a concrete `Fn`.
                let params = match &scheme.ty {
                    cranelisp_types::Type::Fn(ps, _ret) => ps.clone(),
                    _ => Vec::new(),
                };
                Some((*got_slot, params))
            }
            _ => None,
        };
        let is_platform_effect = matches!(
            &entry,
            ModuleEntry::Def { kind, .. } if matches!(kind.as_ref(), DefKind::PlatformEffect { .. })
        );

        // --- S6: Poll-construction arm (FIXME 0457 / S94 R1, byte-identical-off) ---
        // A poll-shape platform effect (`DefKind::PlatformEffect { poll_shape:
        // true }`) is NOT called at the site; instead the backend loads its
        // poll-fn from the GOT and builds an `IO_TAG_EFFECT_POLL` node over a
        // host-built state-closure (`design/backend/io-trampoline.md §12`). Keyed
        // on the fetched entry's data field, no cargo feature; a blocking effect
        // (every v6 platform) is `None` here and takes the unchanged call path
        // below, so the default build constructs no poll node and is
        // byte-identical. `scheduling_class` gates only the producer-side
        // injection, not this consumer.
        if let Some((slot, param_types)) = platform_effect_poll {
            return self.compile_poll_effect(&home, slot, &param_types, arg_vals, span);
        }

        // --- S7: Unified GOT path (target: works for both JIT and object codegen) ---
        // Uses global_value(DataId) which Cranelift lowers to:
        //   JIT (is_pic=false): movz+movk (absolute address)
        //   Object (is_pic=true): ADRP+ADD (PC-relative relocation)
        //
        // The GOT slot is read off the ONE fetched entry via `callable_got_slot()`
        // (the same accessor `resolve_got_target`'s read closure used); the GOT
        // data symbol keys on the entry's STORAGE module (`home == fq.module`), so
        // the emitted (symbol, slot) pair is byte-identical to the pre-W1 scan.
        if let Some(slot) = entry.callable_got_slot() {
            let got_sym = crate::compiler::got_data_symbol_name(&home);
            let data_id = self.module
                .declare_data(&got_sym, cranelift_module::Linkage::Import, false, false)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to declare GOT data '{}': {e}", got_sym),
                    location: ErrorLocation::from_span(span),
                })?;
            let node_val = self.emit_got_indirect_call_via_data_id(data_id, slot, arg_vals)?;
            // --- S8: platform fn-name stamp ---
            // Step 2/4 of the fault-guarded dispatch funnel (S81 / FIXME 0327;
            // BC §3 + §5 invariant 9 Option A). When this GOT-indirect dispatch
            // resolved a `DefKind::PlatformEffect`, the call returned an
            // `IO_TAG_EFFECT` node whose field-3 the DLL initialised to null.
            // Bake the statically-known FQ fn-name and stamp the baked pointer
            // into field-3 so the intrinsics fault guard (step 3) can surface
            // `DispatchError { fn_name }` — including on the FAULT path, because
            // the stamp lands at node-construction time (immediately after the
            // `crash()`-style constructor returns), BEFORE the force, so it
            // survives a thunk panic at force time.
            //
            // The stamp lives HERE — at the single GOT-indirect dispatch chokepoint
            // every platform call flows through (the `ResolvedCall::BuiltinFn` arm
            // AND the plain `compile_var_apply` path both route into
            // `compile_direct_call`). A bare imported platform fn `(crash)` carries
            // `resolved_call: None`, so it reaches dispatch via `compile_var_apply`
            // → `compile_direct_call`, NOT the `BuiltinFn` arm — siting the stamp
            // here closes the fault-path `<unknown>` gap (FIXME 0337 residual) and
            // unifies the happy path (which was ALSO `<unknown>` for bare imports).
            // ONLY a `DefKind::PlatformEffect` target stamps — user fns / primitives
            // / trait methods reach `compile_direct_call` too and must not be
            // written to (their result is not an Effect node). The FQ name is
            // composed from the ONE fetched entry's storage identity
            // (`home`/`fq.symbol`) — byte-identical to the pre-W1
            // `resolve_platform_effect_target` `(eff_module, bare)`.
            if is_platform_effect {
                let fq_name = format!("{}/{}", home, fq.symbol);
                self.stamp_platform_fn_name(node_val, &fq_name, span)?;
            }
            return Ok(node_val);
        }

        // --- S9: Kind-driven `PrimitiveExtern` arm (test-discovery.md §6; BC §3
        // invariant 8 / §7 types). A host-promised extern (`discover-tests`)
        // carries no GOT slot, so the S7 arm above misses it; it has no `FuncId`
        // in `func_ids` either (no codegen body). Lower it as a `Linkage::Import`
        // against the entry key — the symbol-table key IS the ABI name — identical
        // in shape to the platform-effect / intrinsic import path. The body is
        // settled at JIT-finalize via `Jit::define_symbol` (int's session-init
        // promise) or surfaces as an unresolved-symbol link error in `--link`.
        if matches!(&entry, ModuleEntry::Def { kind, .. } if matches!(kind.as_ref(), DefKind::PrimitiveExtern))
        {
            return self.compile_extern_call(fq.symbol.as_ref(), arg_vals, span);
        }

        // Non-resolver tail: a direct `call` via a `FuncId` from the compilation
        // unit's `func_ids` map. This is NOT a name-resolver (a direct map lookup
        // by name — no import-chain walk, no precedence, no `symbol_tables` scan),
        // so it is Rev-2-compliant. It is reached only when the fetched entry
        // carries no dispatch mechanism (no GOT slot, not extern, not poll) — in
        // the live session path every callable carries a GOT slot, so the S7 arm
        // wins and this is effectively the batch/test-harness tail.
        let func_id = self.ctx.func_ids.get(name).ok_or_else(|| {
            CranelispError::CodegenError {
                message: format!("undefined function: {name}"),
                location: ErrorLocation::from_span(span),
            }
        })?;
        let local_func = self
            .module
            .declare_func_in_func(*func_id, self.builder.func);
        let call = self.builder.ins().call(local_func, arg_vals);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Bake the platform fn's fully-qualified name as a relocated, position-
    /// independent read-only data symbol and emit IR that stamps its address
    /// into the returned `IO_TAG_EFFECT` node's fn-name field (field-3), AFTER
    /// the platform-fn GOT-indirect call has returned the node pointer.
    ///
    /// This is step 2/4 of the fault-guarded dispatch funnel (S81 / FIXME 0327;
    /// BC §3 "the platform-dispatch fn-name bake" + §5 invariant 9 Option A).
    /// The DLL's `CLIO::effect*` constructor allocates the node and inits
    /// field-3 to null (it cannot know the cranelisp-level fn-name); the backend
    /// stamps the statically-known name here. The intrinsics IO trampoline reads
    /// field-3 in the fault guard (step 3) to surface
    /// `PlatformError::DispatchError { fn_name }`; a node the backend did NOT
    /// stamp keeps field-3 null and degrades to `"<unknown>"`, never a crash.
    ///
    /// The baked datum is a **NUL-terminated** UTF-8 byte sequence — the same
    /// self-describing C-string convention the layout-hash gate bakes
    /// (int's `src/exe.rs::define_cstr_data` — the backend copy was deleted S113
    /// W2b, FIXME 0635 I3) — so the trampoline reads it without a
    /// separate length channel. It is emitted via the **same data-symbol family
    /// as the trace `DisplayDescriptor` baker** (`emit_ro_data` →
    /// `declare_anonymous_data` + `define_data`), so it survives `.o` caching:
    /// the address is materialised by a `global_value` relocation (object mode)
    /// / JIT-patched runtime address (JIT mode), never a baked compiling-process
    /// pointer (mirrors `trace_codegen` FIXME 0275).
    ///
    /// `node_val` is the Effect node base pointer returned by the platform call.
    /// `fq_name` is the platform fn's fully-qualified `module/symbol` name.
    fn stamp_platform_fn_name(
        &mut self,
        node_val: Value,
        fq_name: &str,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Bake the FQ name as NUL-terminated read-only data (mode-agnostic,
        // cache-safe — same family as the trace name baker, trace_codegen.rs).
        let bytes = platform_fn_name_bytes(fq_name);
        let name_data_id = self.emit_ro_data(&bytes, 1, "platform fn-name", span)?;

        // Materialise the baked name's address (one relocation in object mode;
        // JIT patches the runtime address).
        let name_gv = self.module.declare_data_in_func(name_data_id, self.builder.func);
        let name_ptr = self.builder.ins().global_value(types::I64, name_gv);

        // Stamp it into field-3 at the absolute offset composed from the named
        // ABI constants (HeapHeader::SIZE + IO_EFFECT_FN_NAME_OFFSET), never a
        // hard-coded 40.
        self.builder.ins().store(
            MemFlags::trusted(),
            name_ptr,
            node_val,
            EFFECT_FN_NAME_ABS_OFFSET as i32,
        );
        Ok(())
    }

    /// Emit a GOT-indirect call using a data symbol reference.
    ///
    /// The data symbol IS the per-module GOT slab base address (no extra
    /// pointer-cell indirection). Works identically in both JIT and object
    /// codegen:
    ///   JIT:    `__cranelisp_got_{M}` registered via `JITBuilder::symbol()`
    ///           with `GotTable.base_ptr()`; lookup returns slab base directly.
    ///   Object: `__cranelisp_got_{M}` defined as `Linkage::Export` data
    ///           sized `slot_count * 8` with function-address relocations at
    ///           each slot — the symbol's load address IS the slab base.
    ///
    /// Codegen (one indirection at the literal-pool / system-GOT layer):
    ///   slab_base = global_value(data_id)         // ADRP+LDR via system GOT
    ///   fn_ptr    = load(slab_base + slot * 8)    // load slot from slab
    ///   call_indirect(fn_ptr, args)
    /// Load a function pointer out of a platform/module GOT slot — the shared
    /// load prefix of GOT-indirect dispatch (Principle 7). `emit_got_indirect_call_via_data_id`
    /// LOADs then `call_indirect`s; the poll-construction arm
    /// (`compile_poll_effect`) LOADs then bakes the pointer as the state-closure
    /// `code_ptr` (no call at the site). Both flow through this one helper so the
    /// GOT mechanism stays single-source (`design/backend/io-trampoline.md §12.3`).
    fn emit_got_slot_load(
        &mut self,
        data_id: cranelift_module::DataId,
        slot: usize,
    ) -> Value {
        // The symbol address IS the slab base (Decision 23 — unified shape).
        let gv = self.module.declare_data_in_func(data_id, self.builder.func);
        let slab_base = self.builder.ins().global_value(types::I64, gv);
        // Compute slot address: slab_base + slot * 8.
        let slot_addr = self.builder.ins().iadd_imm(slab_base, (slot * 8) as i64);
        // Load the function pointer from the GOT slot.
        self.builder
            .ins()
            .load(types::I64, MemFlags::trusted(), slot_addr, 0)
    }

    fn emit_got_indirect_call_via_data_id(
        &mut self,
        data_id: cranelift_module::DataId,
        slot: usize,
        arg_vals: &[Value],
    ) -> Result<Value, CranelispError> {
        // Load the function pointer from the GOT slot (the shared load prefix).
        let func_ptr = self.emit_got_slot_load(data_id, slot);

        // Build signature: all params and return are i64.
        let mut sig = self.module.make_signature();
        for _ in arg_vals {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));
        let sig_ref = self.builder.import_signature(sig);

        let call = self.builder.ins().call_indirect(sig_ref, func_ptr, arg_vals);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Poll-construction arm (FIXME 0457 / S94 R1) — build an `IO_TAG_EFFECT_POLL`
    /// node over a host-built state-closure for a poll-shape platform effect,
    /// instead of CALLING the effect fn (the blocking arm's behaviour). The
    /// poll-fn is LOADed from the platform GOT (`emit_got_slot_load`, the shared
    /// load prefix — Principle 7) and baked as the state-closure `code_ptr`; the
    /// effect's i64 args are marshaled as the closure's env captures; the
    /// trampoline supplies `HostCtx`/`Waker` and calls the poll-fn later
    /// (`design/backend/io-trampoline.md §12`, `design/int/reactor.md §2.5`).
    ///
    /// Operand convention (`io-trampoline.md §14.2` / SPRINT.md S96 Phase-3):
    ///   `arg_vals = [ token, capacity, resource_handle(=leaf_0), leaf_1, ... ]`.
    /// The backend peels the leading `(token, capacity)` pair and bakes the live
    /// values into the node carrier (fields 1/2); the leaf args (`arg_vals[2..]`)
    /// marshal into the state-closure env.
    ///
    /// State-closure (standard `HeapClosure`) env layout:
    ///   `capture(0)` = result slot (sentinel `0`, the poll-fn writes its result),
    ///   `capture(1+i)` = leaf arg `i` (`arg_vals[2+i]`). The trampoline passes the
    ///   env base (`closure + 32`) as `state`, so the poll-fn sees result at
    ///   `state+0`, the re-passed resource handle (`leaf_0`) at `state+8`. The node
    ///   holds tag + the state-closure pointer (field 0) + the LIVE `(token,
    ///   capacity)` carrier (fields 1 and 2 — S96 item 3, `io-trampoline.md §14`;
    ///   replaces the S95 `0`/`1` sentinels at the same abs 32 / 40 offsets).
    ///
    /// RC: leaf args reach here via the consuming convention
    /// (`compile_consuming_arg_list` in the platform-effect dispatch arm), so storing
    /// them into the env is an ownership transfer (no inc — like `ParBind`/`Bind`
    /// constructor convention); the state-closure drop glue
    /// (`build_poll_state_drop_glue`) dec's the heap-typed arg slots when the node is
    /// consumed (`consume_io_tree`). The baked `(token, capacity)` are `NeverHeap`
    /// scalars (no inc, no dec — §14.6).
    fn compile_poll_effect(
        &mut self,
        module_path: &cranelisp_types::ModuleFullPath,
        slot: usize,
        param_types: &[cranelisp_types::Type],
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id = self.ctx.alloc_func_id.ok_or_else(|| CranelispError::CodegenError {
            message: "runtime/alloc not declared (need declare_intrinsics)".into(),
            location: ErrorLocation::from_span(span),
        })?;

        // 0. v9 ctx-vtable (`io-trampoline.md §17.3`): the v8 leading-pair peel is
        //    DELETED. Under the ctx-vtable handle model the descriptor `(token,
        //    capacity)` is neither a cranelisp value nor a leaf arg nor anything stored
        //    on the node — the platform poll-fn computes its token from the handle it
        //    holds and calls `ctx.acquire` itself. So a poll leaf's natural args are
        //    its ONLY args: `leaf_args = arg_vals[0..]` directly, marshaled into the
        //    state-closure env at `capture(1+i)` (result @ `capture(0)`).
        let leaf_args = arg_vals;

        // 1. GOT-load the poll-fn (the shared load prefix — NO call at the site).
        let got_sym = crate::compiler::got_data_symbol_name(module_path);
        let data_id = self
            .module
            .declare_data(&got_sym, cranelift_module::Linkage::Import, false, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare platform GOT data '{got_sym}': {e}"),
                location: ErrorLocation::from_span(span),
            })?;
        let poll_fn = self.emit_got_slot_load(data_id, slot);

        // 2. Build the state-closure: env = result-slot + leaf arg captures (the
        //    leading `(token, capacity)` pair is NOT marshaled into the env — capacity
        //    is node-only; the resource handle reaches the env as the re-passed
        //    `leaf_0`).
        let leaf_count = leaf_args.len();
        let env_slots = 1 + leaf_count;
        let closure_size = HeapClosure::payload_size(env_slots) as i64;
        let clo = heap::emit_alloc(&mut self.builder, self.module, alloc_id, closure_size);

        // code_ptr = the GOT-loaded poll-fn.
        heap::heap_store(&mut self.builder, poll_fn, clo, HeapClosure::CODE_PTR_OFFSET);

        // drop_glue_ptr = capture-dec glue (null when no arg is heap-typed).
        //
        // The glue is keyed on the **leaf** param types — those aligned with the
        // env captures (`leaf_args` = `arg_vals[2..]`), NOT the full effect scheme.
        // A `ResourceSerial` leaf's scheme carries `(token, capacity)` as its first
        // two params (the S95 `pool-demo` convention, e.g. `poll-log : (Fn [Int Int
        // Int String] …)`), but those two operands are PEELED to the node fields
        // and are NOT marshaled into the env — so keying the glue on the full scheme
        // would mis-offset the dec walk (dec'ing a heap field at a capture slot that
        // does not exist → corruption). The leaf params are the TRAILING
        // `leaf_args.len()` entries of the scheme: for a `Commutative` leaf the
        // `(0,1)` pair is SYNTHESIZED by the producer injection (absent from the
        // scheme), so the trailing slice is the whole scheme; for a `ResourceSerial`
        // leaf it drops the two leading `(token, capacity)` params. One uniform
        // alignment rule, no `scheduling_class` branch here.
        let leaf_param_types = &param_types[param_types.len().saturating_sub(leaf_count)..];
        let drop_glue = self.build_poll_state_drop_glue(leaf_param_types, span)?;
        let drop_glue_val = if let Some(glue_id) = drop_glue {
            let glue_ref = self.module.declare_func_in_func(glue_id, self.builder.func);
            self.builder.ins().func_addr(types::I64, glue_ref)
        } else {
            self.builder.ins().iconst(types::I64, 0)
        };
        heap::heap_store(&mut self.builder, drop_glue_val, clo, HeapClosure::DROP_GLUE_PTR_OFFSET);

        // env(0) = result slot, init to the `0` sentinel (the poll-fn reads `0`
        // as "not yet armed"; `EffectPoll` reads the result here on Ready).
        let sentinel = self.builder.ins().iconst(types::I64, 0);
        heap::heap_store(&mut self.builder, sentinel, clo, HeapClosure::capture_offset(0));

        // env(1+i) = leaf arg i (ownership transfer, no inc — consuming conv).
        // leaf_args = arg_vals[2..]; leaf_0 (the re-passed resource handle) lands at
        // capture(1) = state+8 (the poll-fn's fd). The leading-pair peel does not
        // shift any arg the poll-fn relies on — env layout is unchanged from S94/S95.
        for (i, &arg) in leaf_args.iter().enumerate() {
            heap::heap_store(&mut self.builder, arg, clo, HeapClosure::capture_offset(1 + i));
        }

        // 3. Build the IO_TAG_EFFECT_POLL node — the v8-UNIFORM shape
        //    (`io-trampoline.md §17.2`): `[header | tag=4 | state_closure | _ | _]`.
        //
        // v9 ctx-vtable: the two former `(token, capacity)` admission slots carry
        // NOTHING the trampoline reads (`await_poll_node` is scheduling-blind — the
        // platform poll-fn does all scheduling via `ctx.acquire`). The node keeps the
        // `payload_size(3)` layout (so the read helpers + drop glue are byte-stable),
        // and the two slots are baked with INERT zero/sentinel `iconst`s. The node is
        // still a one-heap-field ADT (only field 0, the state-closure, is heap-typed);
        // the two inert fields are `NeverHeap` scalars (no `rc_inc`, drop glue
        // unchanged in shape, §14.6). No node growth (it does NOT grow 48→56), no
        // `role` field, no `desc_out` region (`io-trampoline.md §17.2`).
        let node_size = HeapAdt::payload_size(3) as i64;
        let node = heap::emit_alloc(&mut self.builder, self.module, alloc_id, node_size);
        // IO_TAG_EFFECT_POLL = 4 (the `cranelisp-platform` gated constant; a
        // literal here because the backend carries no `concurrency` feature —
        // same convention as the `IO_TAG_PAR = 3` literal in `par_bind.rs`).
        let tag = self.builder.ins().iconst(types::I64, 4);
        heap::heap_store(&mut self.builder, tag, node, HeapAdt::TAG_OFFSET);
        // field 0: ownership transfer of the state-closure (rc=1) into the node, no inc.
        heap::heap_store(&mut self.builder, clo, node, HeapAdt::field_offset(0));
        // fields 1/2: INERT under v9 (no scheduling state on the node) — zero/sentinel.
        let inert_token = self.builder.ins().iconst(types::I64, 0);
        heap::heap_store(&mut self.builder, inert_token, node, HeapAdt::field_offset(1));
        let inert_capacity = self.builder.ins().iconst(types::I64, 1);
        heap::heap_store(&mut self.builder, inert_capacity, node, HeapAdt::field_offset(2));

        Ok(node)
    }

    /// Compile a `(sleep d)` call — the runtime timer poll leaf (S96 Chunk C4,
    /// slice 7; `design/int/reactor.md §2.18`). `sleep : Int -> IO Int` arms the
    /// reactor's timer and resumes (with `0`) after `d` MILLISECONDS, reusing the
    /// **entire** `IO_TAG_EFFECT_POLL` / `EffectPoll` / acquire-around-poll /
    /// timer-`turn()` machinery — it is just another poll node.
    ///
    /// **The genuinely-new machinery vs `compile_poll_effect`: the `code_ptr` is a
    /// RUNTIME SYMBOL, not a GOT platform slot.** A `declare_platform!` poll effect
    /// loads its poll-fn from `__cranelisp_got_platform_<name>` (`emit_got_slot_load`);
    /// `sleep`'s poll-fn is the intrinsics `runtime/sleep_pollfn` (the control
    /// vocabulary is runtime-hosted, §9 — platforms never see it), so it is resolved
    /// as a `Linkage::Import` and `func_addr`-baked here (the non-GOT path). Both
    /// paths converge on the SAME state-closure shape; the trampoline reads the
    /// baked `code_ptr` uniformly (`io.rs::await_poll_node`) and does not care where
    /// it came from.
    ///
    /// `sleep` is **tokenless** — `(token = 0, capacity = 1)` ⇒ unrestricted overlap
    /// (many `sleep`s race concurrently; `token == 0` ⇒ the trampoline's no-acquire
    /// path). State-closure env (overlaid by the intrinsics `SleepState`): `env(0)` =
    /// result slot (`0`, the Unit the leaf writes on `Ready`), `env(1)` =
    /// `duration_nanos` (the `d`-ms arg × 1_000_000), `env(2)` = `deadline_nanos`
    /// (`0` — the first-poll "not yet armed" sentinel). All scalars ⇒ null drop glue.
    fn compile_sleep(
        &mut self,
        args: &[MonoExpr],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let arg_vals = self.compile_arg_list(args)?;
        let [d_ms] = arg_vals[..] else {
            return Err(CranelispError::CodegenError {
                message: "sleep takes exactly one (Int milliseconds) argument".into(),
                location: ErrorLocation::from_span(span),
            });
        };
        let alloc_id = self.ctx.alloc_func_id.ok_or_else(|| CranelispError::CodegenError {
            message: "runtime/alloc not declared (need declare_intrinsics)".into(),
            location: ErrorLocation::from_span(span),
        })?;

        // duration_nanos = d (milliseconds) × 1_000_000 (the leaf works in nanos —
        // `reactor.rs::sleep_pollfn` does `monotonic_nanos() + duration_nanos`).
        let duration_nanos = self.builder.ins().imul_imm(d_ms, 1_000_000);

        // code_ptr = the RUNTIME symbol `runtime/sleep_pollfn`, resolved as a
        // `Linkage::Import` and `func_addr`-baked (the non-GOT path — Principle 7
        // keeps the runtime-symbol bake distinct from `emit_got_slot_load`). The
        // signature MUST match the catalog arity (3 i64 params + i64 return) so the
        // JIT/`--link` symbol resolution agrees (`catalog.rs` `runtime/sleep_pollfn`).
        let mut sig = self.module.make_signature();
        for _ in 0..3 {
            sig.params.push(AbiParam::new(types::I64)); // state, host, waker
        }
        sig.returns.push(AbiParam::new(types::I64)); // Poll
        let poll_fn_id = self
            .module
            .declare_function("runtime/sleep_pollfn", cranelift_module::Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare runtime symbol 'runtime/sleep_pollfn': {e}"),
                location: ErrorLocation::from_span(span),
            })?;
        let poll_fn_ref = self.module.declare_func_in_func(poll_fn_id, self.builder.func);
        let poll_fn = self.builder.ins().func_addr(types::I64, poll_fn_ref);

        // State-closure: [header | code_ptr | drop_glue=0 | env(0)=result(0) |
        // env(1)=duration_nanos | env(2)=deadline(0)] — 3 env slots (SleepState).
        let closure_size = HeapClosure::payload_size(3) as i64;
        let clo = heap::emit_alloc(&mut self.builder, self.module, alloc_id, closure_size);
        heap::heap_store(&mut self.builder, poll_fn, clo, HeapClosure::CODE_PTR_OFFSET);
        let zero = self.builder.ins().iconst(types::I64, 0);
        // drop_glue = null (SleepState is all scalars — nothing to dec).
        heap::heap_store(&mut self.builder, zero, clo, HeapClosure::DROP_GLUE_PTR_OFFSET);
        // env(0) = result slot (Unit `0`; the poll-fn / EffectPoll read it on Ready).
        heap::heap_store(&mut self.builder, zero, clo, HeapClosure::capture_offset(0));
        // env(1) = duration_nanos (the baked d-ms × 1e6).
        heap::heap_store(&mut self.builder, duration_nanos, clo, HeapClosure::capture_offset(1));
        // env(2) = deadline_nanos = 0 (first-poll "not yet armed" sentinel).
        heap::heap_store(&mut self.builder, zero, clo, HeapClosure::capture_offset(2));

        // IO_TAG_EFFECT_POLL = 4 node: [header | tag=4 | state_closure | token=0 |
        // capacity=1]. Tokenless ⇒ token 0 (no-acquire), capacity 1 (the §2.18
        // "tokenless leaf passes (0,1) constants" convention). payload_size(3).
        let node_size = HeapAdt::payload_size(3) as i64;
        let node = heap::emit_alloc(&mut self.builder, self.module, alloc_id, node_size);
        let tag = self.builder.ins().iconst(types::I64, 4);
        heap::heap_store(&mut self.builder, tag, node, HeapAdt::TAG_OFFSET);
        heap::heap_store(&mut self.builder, clo, node, HeapAdt::field_offset(0));
        let token = self.builder.ins().iconst(types::I64, 0);
        heap::heap_store(&mut self.builder, token, node, HeapAdt::field_offset(1));
        let cap = self.builder.ins().iconst(types::I64, 1);
        heap::heap_store(&mut self.builder, cap, node, HeapAdt::field_offset(2));

        Ok(node)
    }

    /// Build the state-closure drop glue for a poll-shape effect node — dec's each
    /// heap-typed arg capture (at `capture_offset(1+i)`) when the node is consumed.
    /// Returns `None` when no arg is heap-typed (all-scalar effects, e.g. the
    /// `async-demo` `(Fn [Int] (IO Int))` leaf) — the node's closure-dec then just
    /// deallocs (null `drop_glue_ptr`). The result slot (`capture(0)`) is a plain
    /// i64 and is never dec'd here (per `io-trampoline.md §12.5`; the demo's result
    /// is `NeverHeap`). Mirrors `build_closure_drop_glue`, keyed on the effect's
    /// param types rather than captured-variable names.
    fn build_poll_state_drop_glue(
        &mut self,
        param_types: &[cranelisp_types::Type],
        span: Span,
    ) -> Result<Option<cranelift_module::FuncId>, CranelispError> {
        let dealloc_id = self.ctx.dealloc_func_id;

        let heap_args: Vec<(usize, HeapCategory)> = param_types
            .iter()
            .enumerate()
            .filter_map(|(i, ty)| {
                let category = signature_heap_category(ty, Some(self.ctx.symbol_tables));
                match category {
                    HeapCategory::AlwaysHeap | HeapCategory::Mixed => Some((i, category)),
                    HeapCategory::NeverHeap | HeapCategory::Value => None,
                }
            })
            .collect();

        if heap_args.is_empty() {
            return Ok(None);
        }

        let glue_name = format!(
            "runtime/poll_state_drop_glue_{}{}_{}",
            self.inner_fn_discriminator(),
            span.start,
            span.end
        );

        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // state-closure ptr

        let glue_func_id = self
            .module
            .declare_function(&glue_name, cranelift_module::Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare poll-state drop glue fn: {e}"),
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
        let closure_ptr = builder.block_params(entry)[0];

        // Heap arg `i` lives at `capture_offset(1 + i)` (env slot 0 is the result).
        for (arg_idx, category) in &heap_args {
            let cap_val = heap::heap_load(
                &mut builder,
                closure_ptr,
                HeapClosure::capture_offset(1 + *arg_idx),
            );
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_dec(&mut builder, self.module, cap_val, dealloc_id, None);
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_dec_guarded(
                        &mut builder,
                        self.module,
                        cap_val,
                        dealloc_id,
                        None,
                        true,
                    );
                }
                HeapCategory::NeverHeap | HeapCategory::Value => {} // filtered above
            }
        }

        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize();

        self.module
            .define_function(glue_func_id, &mut ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define poll-state drop glue fn: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        Ok(Some(glue_func_id))
    }

    /// Compile a tail self-recursive call as a jump to the loop header.
    fn compile_tail_self_call(&mut self, args: &[MonoExpr]) -> Result<Value, CranelispError> {
        // CRITICAL: Args are not in tail position.
        self.in_tail_position = false;

        // Compile all arguments. A control-flow arg (`if`/`match`) can alias a
        // live heap `let`-binding into the tail call with NO owning inc (the
        // branch value is a raw `use_var`) — the uniform flush below would then
        // free a value the next iteration still owns (F1 use-after-free). Under
        // `tail_arg_protect`, `compile_if` / `compile_match` emit a protective
        // inc on any branch/arm result that directly aliases a binding the flush
        // will dec, so the value handed forward owns exactly one reference.
        // A bare top-level `Var` arg needs no protection: it MOVES (no inc) and
        // is excluded from the flush by `tail_transfer_skip`; a non-Var, non-
        // control-flow arg (`(wrap v)`) already inc's any binding it consumes via
        // `compile_consuming_arg_list`, so the flush dec is balanced.
        let arg_vals: Vec<Value> = args
            .iter()
            .map(|a| {
                if matches!(a, MonoExpr::If { .. } | MonoExpr::Match { .. }) {
                    let saved = self.tail_arg_protect;
                    self.tail_arg_protect = true;
                    let v = self.compile_expr(a);
                    self.tail_arg_protect = saved;
                    v
                } else {
                    self.compile_expr(a)
                }
            })
            .collect::<Result<_, _>>()?;

        // Flush the live LET-scope heap bindings BEFORE the jump: the enclosing
        // `compile_let_sequential`'s `pop_scope_with_cleanup` runs only AFTER
        // `compile_expr(body)` returns, i.e. after this jump terminates the
        // block, so those decs land dead. Skip any binding whose reference
        // transfers into a tail argument as a bare top-level `Var` (a MOVE — no
        // consuming inc, so dec'ing it here would double-free the value the new
        // iteration owns). Control-flow-aliased bindings are NOT skipped — they
        // are flushed uniformly and balanced by the protective inc above.
        // (design/backend/ownership-codegen.md §13.3 — the TCO-flush skip-
        // predicate correctness contract; the F1 UAF cure.)
        let transfer_skip = tail_transfer_skip(args);
        self.flush_let_scopes_before_tail_jump(&transfer_skip);

        // Jump to loop header with new argument values.
        let loop_block = self.tail_loop_block.unwrap_or_else(|| {
            unreachable!("invariant: tail_loop_block is Some when compile_tail_self_call is called")
        });
        self.builder.ins().jump(loop_block, &arg_vals);

        // Create a dead block for subsequent code (unreachable, Cranelift eliminates it).
        let dead_block = self.builder.create_block();
        self.builder.switch_to_block(dead_block);
        self.builder.seal_block(dead_block);

        // Return dummy value -- this code is unreachable.
        Ok(self.builder.ins().iconst(types::I64, 0))
    }

    /// Compile an `Expr::ConstrADT` node — the language-level ADT construction
    /// operation synthesised as the body of every constructor's `Def`.
    ///
    /// Per `design/backend/compile-to-module.md` §2.6:
    /// - **Nullary** (`fields.is_empty()`, e.g. `None`, `Red`): fold to a bare
    ///   `iconst.i64 tag` — no heap allocation. Preserves the
    ///   `NULLARY_TAG_THRESHOLD` discrimination contract.
    /// - **Data** (e.g. `Some 42`, `Cons h t`): consuming-compile each field
    ///   left-to-right, `emit_alloc` a `HeapAdt` payload, store `tag` at
    ///   `TAG_OFFSET`, store each field `Value` at its `field_offset(i)`. The
    ///   result `Value` is the heap pointer.
    ///
    /// RC: field values are transferred into the constructor under the uniform
    /// consuming convention (Decision 24, BC invariant 2) — `compile_consuming_arg_list`
    /// inc's non-last-use Var fields before the store; last-use fields transfer
    /// their existing reference. The ADT's drop glue dec's heap-typed fields when
    /// the ADT itself reaches rc=0.
    ///
    /// First-class use `(map Some list)` — passing a constructor as a value via
    /// its `Def`'s `got_slot` (the same path as any other callable, no
    /// on-demand closure synthesis) — is a `// target (S77)` (int-produced).
    ///
    /// `compile_constr_adt` + `emit_adt_construct` are the two-path model
    /// (nullary `iconst tag` / data alloc+tag+stores). The older
    /// `literals::nullary_constructor_tag` + `literals::data_constructor_info`
    /// helpers still exist; their consolidation into this single handler (the
    /// "~200 LOC removed" cleanup) is a `// target (S77)` cleanup, not yet done.
    pub(crate) fn compile_constr_adt(
        &mut self,
        tag: usize,
        fields: &[MonoExpr],
        span: Span,
        ty: &ConcreteType,
    ) -> Result<Value, CranelispError> {
        // Consuming-compile fields (nullary → empty), then route through the
        // single core emitter. `emit_adt_construct` handles the nullary
        // (`iconst tag`) and data (`alloc + tag + stores`) arms.
        //
        // This handler compiles the SYNTHETIC constructor-function body (a
        // `ConstrADT` node), which always returns its value to the caller ⇒
        // heap (B3.4 §4.1 — never a stack site). The use-site construction
        // `(Rect n n)` is an `Apply` handled by `compile_var_apply`, which is
        // where the B3.4 stack decision is consumed.
        let field_vals = self.compile_consuming_arg_list(fields)?;
        // R5 (§7.1): a value-flattened single-ctor type constructs by a bare-word
        // move of its single field — NO alloc, NO header, NO tag. Keeps the
        // synthetic ctor body's representation identical to the use-site
        // `compile_var_apply` flattening, so `Cell`-as-a-value and `(Cell 5)`
        // agree. `value_construct` is `None` off-toggle / for non-`Value` types
        // ⇒ today's heap emitter, byte-identical.
        if let Some(v) = self.value_construct(ty, &field_vals) {
            return Ok(v);
        }
        self.emit_adt_construct(tag, &field_vals, span)
    }

    /// R5 value-flattening construction (§7.1): when `ty` classifies as
    /// [`HeapCategory::Value`], the construct is the **identity move** of the
    /// single flattened field into the value word — `Some(field_vals[0])` for a
    /// one-word single-field wrapper, `None` for a zero-word (fieldless) value
    /// (which routes to the existing nullary `iconst tag` path, harmless — a
    /// zero-information value). Returns `None` for every non-`Value` type and
    /// whenever the ownership toggle is off (`classify` never yields `Value`
    /// then), so callers fall through to today's heap emitter byte-identically.
    ///
    /// A `Value` type has **exactly one** field, guaranteed by `value_layout`'s
    /// single-field invariant (the Wave-3a /review single-source ruling — a
    /// ≥2-field product is `None`, never `Value`, even at ≤1 word). So
    /// `field_vals.len() == 1` always holds for a `Value` here; it is an
    /// invariant-consistent guard, not an independent predicate. The single field
    /// is itself value-eligible (nested values compose), so the move needs no
    /// per-field RC.
    pub(crate) fn value_construct(
        &self,
        ty: &ConcreteType,
        field_vals: &[Value],
    ) -> Option<Value> {
        if matches!(
            HeapCategory::classify(ty, Some(self.ctx.symbol_tables)),
            HeapCategory::Value
        ) && field_vals.len() == 1
        {
            return Some(field_vals[0]);
        }
        None
    }

    /// The single ADT-construct emitter — both paths route through here.
    ///
    /// Per `design/backend/compile-to-module.md` §2.6.1: takes an already-computed
    /// `tag` and the already-computed field `Value`s, and emits the construct.
    /// **RC-neutral** (§2.6.4): stores `field_vals` verbatim — the consuming-
    /// convention inc/transfer happens in the callers that produce `field_vals`
    /// (`compile_consuming_arg_list`). Do NOT add RC here; doing so would
    /// double-inc the Path-1 inline site.
    ///
    /// | Case | Emission |
    /// |---|---|
    /// | `field_vals.is_empty()` (nullary, e.g. `None`, `Red`) | bare `iconst.i64 tag`, no heap allocation — preserves the `NULLARY_TAG_THRESHOLD` discrimination contract |
    /// | `!field_vals.is_empty()` (data ctor) | `emit_alloc` a `HeapAdt`, store `tag` at `TAG_OFFSET`, store each field at `field_offset(i)`; result is the heap pointer |
    pub(crate) fn emit_adt_construct(
        &mut self,
        tag: usize,
        field_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Value-position / resolved-constructor-call callers reach here without an
        // escape verdict in hand — heap verbatim (`stack = false`).
        self.emit_adt_construct_stackable(tag, field_vals, span, false)
    }

    /// [`emit_adt_construct`] with the B3.4 (§4.1) stack-vs-heap decision made by
    /// the caller. `stack = true` places the data-ctor aggregate on a Cranelift
    /// stack slot with the immortal-RC header ([`heap::emit_stack_alloc`], §4.2);
    /// `false` is today's heap `emit_alloc`, byte-identical to pre-B3.4. Only the
    /// allocation instruction differs — the tag/field stores and the returned
    /// pointer contract are identical (no call-site anywhere changes for
    /// stack-ness). The nullary arm (bare tag, no allocation) ignores `stack`.
    pub(crate) fn emit_adt_construct_stackable(
        &mut self,
        tag: usize,
        field_vals: &[Value],
        span: Span,
        stack: bool,
    ) -> Result<Value, CranelispError> {
        if field_vals.is_empty() {
            // Nullary constructor: bare tag, no heap allocation.
            return Ok(self.builder.ins().iconst(types::I64, tag as i64));
        }

        let payload_size = HeapAdt::payload_size(field_vals.len()) as i64;
        let base_ptr = if stack {
            // B3.4: NoEscape scalar-payload ADT → Cranelift stack slot (§4.1/§4.2).
            heap::emit_stack_alloc(&mut self.builder, payload_size)
        } else {
            let alloc_id =
                self.ctx
                    .alloc_func_id
                    .ok_or_else(|| CranelispError::CodegenError {
                        message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                        location: ErrorLocation::from_span(span),
                    })?;
            heap::emit_alloc(&mut self.builder, self.module, alloc_id, payload_size)
        };

        // Store tag at HeapAdt::TAG_OFFSET (16).
        let tag_val = self.builder.ins().iconst(types::I64, tag as i64);
        heap::heap_store(&mut self.builder, tag_val, base_ptr, HeapAdt::TAG_OFFSET);

        // Store each field at HeapAdt::field_offset(i).
        for (i, &field_val) in field_vals.iter().enumerate() {
            heap::heap_store(
                &mut self.builder,
                field_val,
                base_ptr,
                HeapAdt::field_offset(i),
            );
        }

        Ok(base_ptr)
    }

    /// Compile a call to an extern primitive (declared as an imported JIT function).
    /// Map a bare Trace ADT field-accessor name to its `cranelisp_trace_*`
    /// intrinsic, scoped to a Trace-typed receiver.
    ///
    /// The accessors (`name`/`params`/`result`/`children`/`nanos`) are seeded
    /// by int's bootstrap (`src/bootstrap.rs::register_trace_type`) as bare-named
    /// `DefKind::Primitive` entries whose runtime bodies are the
    /// `cranelisp_trace_*` externs in `cranelisp-intrinsics::trace`. typecheck
    /// resolves a call as `BuiltinFn { name: "nanos" }` without rewriting to the
    /// ABI name, so backend supplies the bare-name → intrinsic-name mapping here
    /// (lost in the W1.5 trace relocation — FIXME 0292 / 0285 defect 1).
    ///
    /// Returns `Some("cranelisp_trace_<field>")` only when (a) the name is one of
    /// the five accessors AND (b) the call has exactly one argument whose inferred
    /// type is the synthetic `primitives/Trace` ADT — so a user `nanos`/`name`
    /// field on an unrelated ADT is not hijacked. `first_child_nanos` is NOT in
    /// this set: it is not a seeded field accessor (it is the `/run-tests`
    /// internal reader) and never reaches a `BuiltinFn` call site.
    fn trace_accessor_intrinsic(&self, name: &str, args: &[MonoExpr]) -> Option<&'static str> {
        let intrinsic = trace_accessor_abi_name(name)?;
        // Scope to a Trace-typed receiver: exactly one arg whose concrete type is
        // the `primitives/Trace` ADT.
        let [arg] = args else { return None };
        is_trace_typed_concrete(arg.ty()).then_some(intrinsic)
    }

    fn compile_extern_call(
        &mut self,
        name: &str,
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Declare the extern function as an import in the JIT module.
        let mut sig = self.module.make_signature();
        for _ in arg_vals {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self
            .module
            .declare_function(name, cranelift_module::Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare extern function '{name}': {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        let local_func = self
            .module
            .declare_func_in_func(func_id, self.builder.func);
        let call = self.builder.ins().call(local_func, arg_vals);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Compile a closure call: load code_ptr from the closure, then call_indirect
    /// with the closure pointer as the first argument (env_ptr).
    pub(crate) fn compile_closure_call(
        &mut self,
        closure_val: Value,
        arg_vals: &[Value],
        _span: Span,
    ) -> Result<Value, CranelispError> {
        // Load code_ptr from offset HeapClosure::CODE_PTR_OFFSET (16).
        let code_ptr = heap::heap_load(
            &mut self.builder,
            closure_val,
            HeapClosure::CODE_PTR_OFFSET,
        ); // code_ptr: i64

        // Build signature: (env_ptr, params...) -> i64
        let mut sig = self.module.make_signature();
        // env_ptr (the closure base pointer itself)
        sig.params.push(AbiParam::new(types::I64));
        for _ in arg_vals {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));
        let sig_ref = self.builder.import_signature(sig);

        // Build call args: [closure_ptr, arg_0, ..., arg_n]
        let mut call_args = vec![closure_val];
        call_args.extend_from_slice(arg_vals);

        let call = self
            .builder
            .ins()
            .call_indirect(sig_ref, code_ptr, &call_args);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Compile `bind` inline: allocate a Bind node [tag=2, inner_io, cont],
    /// inc both arguments.
    ///
    /// `bind :: (Fn [(IO a) (Fn [a] (IO b))] (IO b))`
    ///
    /// The Bind node is an IO ADT constructor (tag=2) with two fields:
    /// - inner_io (offset 24): pointer to an IO node
    /// - cont (offset 32): pointer to a continuation closure
    ///
    /// Both arguments are inc'd because the Bind node holds references to them
    /// that are independent of whatever references the caller already holds.
    /// The Bind node's drop glue (tag-based dispatch) will dec both fields
    /// when the Bind node itself is freed.
    ///
    /// See `design/backend/io-trampoline.md` §2 for the full design.
    fn compile_bind_inline(
        &mut self,
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        if arg_vals.len() != 2 {
            return Err(CranelispError::CodegenError {
                message: format!(
                    "bind requires 2 arguments, got {}",
                    arg_vals.len()
                ),
                location: ErrorLocation::from_span(span),
            });
        }

        let io_val = arg_vals[0]; // inner IO tree
        let cont_val = arg_vals[1]; // continuation closure

        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
                })?;

        // Allocate Bind node: 3 fields x 8 bytes = 24 bytes payload
        // (tag + inner_io + cont)
        let payload_size = HeapAdt::payload_size(2) as i64; // tag + 2 fields = 24 bytes
        let base_ptr = heap::emit_alloc(
            &mut self.builder,
            self.module,
            alloc_id,
            payload_size,
        );

        // Store tag=2 at TAG_OFFSET (16)
        let tag_val = self.builder.ins().iconst(types::I64, 2);
        heap::heap_store(&mut self.builder, tag_val, base_ptr, HeapAdt::TAG_OFFSET);

        // Store inner_io at field_offset(0) (24)
        heap::heap_store(&mut self.builder, io_val, base_ptr, HeapAdt::field_offset(0));

        // Store cont at field_offset(1) (32)
        heap::heap_store(&mut self.builder, cont_val, base_ptr, HeapAdt::field_offset(1));

        // RC: No explicit inc needed here.
        // bind uses consuming calling convention (compile_consuming_arg_list):
        // - Variable args are already inc'd by the consuming arg list
        // - Temporary args transfer ownership (rc=1 → Bind node inherits)
        // The Bind node's drop glue will dec both fields when freed.

        Ok(base_ptr)
    }

    /// Emit RC dec for a temporary closure value, using the shared method.
    pub(crate) fn emit_closure_dec(&mut self, closure_val: Value, _span: Span) {
        self.emit_closure_dec_inline(closure_val, self.ctx.dealloc_func_id);
    }
}

/// Check if a builtin name is an extern primitive (requires a call, not inline IR).
///
/// Under Decision 24 (uniform consuming convention) these externs dec their
/// own heap arguments in their Rust implementations. The backend uses
/// `compile_consuming_arg_list` at every call site — no per-callee classification.
fn is_extern_primitive(name: &str) -> bool {
    matches!(
        name,
        "str-concat"
            | "str-eq"
            | "str-len"
            | "string-identity"
            | "int-to-string"
            | "float-to-string"
            | "bool-to-string"
            | "parse-int"
            | "sconcat"
            | "quote-sexp"
            | "substring"
            | "char-at"
            | "split"
            | "join"
            | "replace"
            | "trim"
            | "starts-with?"
            | "ends-with?"
            | "contains?"
            | "to-upper"
            | "to-lower"
            // Trace ADT field accessors: consuming convention (Decision 24).
            // Each inc-and-returns the heap field being read; the Trace arg is
            // consumed on the Rust side via `consume_trace_call`.
            | "cranelisp_trace_name"
            | "cranelisp_trace_params"
            | "cranelisp_trace_result"
            | "cranelisp_trace_children"
            | "cranelisp_trace_nanos"
            | "cranelisp_trace_first_child_nanos"
    )
}

/// Check if a builtin name is a Vec primitive (compiled inline by vec_codegen).
fn is_vec_primitive(name: &str) -> bool {
    matches!(name, "vec-get" | "vec-set" | "vec-push" | "vec-len")
}

/// Check if a resolved call is one of the inline IO combinators that compile
/// their OWN arguments as IO sub-trees (`bind` / `select` / `race` / `sleep`),
/// rather than as ordinary values dispatched through the generic apply lowering.
///
/// These must be EXCLUDED from the lenient apply-argument spark pre-pass
/// (`compile_apply`, lenient-eval.md §2.5). Their arguments are IO computations
/// the trampoline runs (via the reactor / recursive trampolines), NOT values to
/// force on the rayon spark pool — sparking them is semantically wrong. It is
/// also a codegen-collision hazard: `compile_race` recompiles its arg IO sub-trees
/// via `compile_vec_lit` WITHOUT consulting `sparked_args`, so a Phase-1 spark
/// thunk and the recompiled inner lambda are emitted for the same source span,
/// declaring the same `__lambda_<span>__` symbol with incompatible signatures
/// (`{1 param}` thunk vs `{2 param}` closure). `select` shares the arm but takes a
/// single `[..]` VecLit carrier (not a sparkable Apply), so it never tripped this —
/// the guard makes the exclusion uniform across all four combinators.
fn is_io_combinator_call(resolved_call: Option<&ResolvedCall>) -> bool {
    matches!(
        resolved_call,
        Some(ResolvedCall::BuiltinFn { name })
            if matches!(name.as_ref(), "bind" | "select" | "race" | "sleep")
    )
}

/// The byte payload baked for a platform fn-name handle (S81 / FIXME 0327, the
/// dispatch funnel step 2/4): the FQ name as UTF-8 with a trailing NUL — the
/// self-describing C-string convention the trampoline fault guard reads (step 3)
/// without a separate length channel, mirroring int's `src/exe.rs::define_cstr_data`
/// (the backend copy was deleted S113 W2b, FIXME 0635 I3).
fn platform_fn_name_bytes(fq_name: &str) -> Vec<u8> {
    let mut bytes = fq_name.as_bytes().to_vec();
    bytes.push(0); // NUL terminator — C-string read by the trampoline guard.
    bytes
}

/// Map a bare Trace ADT field-accessor name to its `cranelisp_trace_*` intrinsic
/// ABI name. Returns `None` for any other name.
///
/// These five accessors are seeded as bare-named `DefKind::Primitive` entries by
/// int's bootstrap; their bodies are the intrinsics in
/// `cranelisp-intrinsics::trace` (published via `intrinsics_table()`). The
/// bare-name → ABI-name mapping is restored here (lost in the W1.5 trace
/// relocation — FIXME 0292 / 0285 defect 1). `first_child_nanos` is excluded
/// deliberately: it is the `/run-tests` internal reader, not a field accessor,
/// and never appears as a `BuiltinFn` call head.
fn trace_accessor_abi_name(name: &str) -> Option<&'static str> {
    Some(match name {
        "name" => "cranelisp_trace_name",
        "params" => "cranelisp_trace_params",
        "result" => "cranelisp_trace_result",
        "children" => "cranelisp_trace_children",
        "nanos" => "cranelisp_trace_nanos",
        _ => return None,
    })
}

/// Whether an inferred type is the synthetic `primitives/Trace` ADT — the
/// receiver-scope gate for the Trace accessor rewrite (so a user `nanos`/`name`
/// field on an unrelated ADT is not hijacked).
/// The receiver-scope gate for the Trace accessor rewrite over a `MonoExpr`
/// node's concrete type — a `primitives/Trace` ADT (so a user `nanos`/`name`
/// field on an unrelated ADT is not hijacked).
fn is_trace_typed_concrete(ty: &ConcreteType) -> bool {
    matches!(
        ty,
        ConcreteType::ADT(fqtn, _)
            if fqtn.module.as_ref() == "primitives" && fqtn.name.as_ref() == "Trace"
    )
}

#[cfg(test)]
mod trace_accessor_tests;

#[cfg(test)]
mod platform_fn_name_stamp_tests;

#[cfg(test)]
mod io_combinator_spark_tests;

#[cfg(test)]
mod dispatch_tests;

#[cfg(test)]
mod tail_transfer_skip_tests;

#[cfg(test)]
mod moded_arg_rc_tests;

#[cfg(test)]
mod keyed_miss_tests;

#[cfg(test)]
mod tco_self_call_carrier_tests;
