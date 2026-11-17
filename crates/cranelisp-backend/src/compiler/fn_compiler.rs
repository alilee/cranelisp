//! The per-function CLIF emitter: the `FnCompiler` struct, its construction
//! (`inner`, `compile_body`), the expression-dispatch entry (`compile_expr`),
//! binder lifecycle and the counting primitives the ownership plan drives, and
//! the small per-fn predicates. `MatchContext` is per-arm `FnCompiler` state,
//! kept adjacent to the struct it threads through.

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_module::Module;

use cranelisp_types::{
    ApplyRef, CranelispError, Defn, ModuleFullPath, MonoExpr, ResolvedCall, Span, Symbol, Type,
    VarRef,
};

use crate::heap::{self, HeapCategory};

use super::ownership_plan::{BinderId, CaptureEntry, Intro, Occurrence, OwnershipPlan, Use};
use super::scope_chain::{Binding, CaptureEnv, ScopeChain, resolve_binding};
use super::{
    CompileContext, find_var_type_in_expr, inner_fn_discriminator_for, signature_heap_category,
};

/// Match-arm-invariant data bundled to reduce parameter counts in
/// `compile_constructor_pattern`.
pub(crate) struct MatchContext {
    /// The compiled scrutinee value, which the match owns.
    pub scrut_val: Value,
    /// The inferred type of the scrutinee expression (for field type resolution).
    pub scrut_type: Option<Type>,
    /// The block to branch to if this arm does not match.
    pub next_block: Block,
    /// The merge block where all arms converge.
    pub merge_block: Block,
    /// The saved tail-position flag from before the match.
    pub saved_tail: bool,
    /// The match node's plan key.
    pub match_node: usize,
    /// This arm's index.
    pub arm: usize,
}

/// One owned binder's storage: its variable and recorded type.
#[derive(Clone, Debug)]
struct BinderStore {
    var: Variable,
    ty: Option<Type>,
}

/// Per-function compilation context.
///
/// Generic over `M: Module` so the same codegen can target both `JITModule`
/// (for immediate execution) and `ObjectModule` (for `.o` file generation).
/// See design/backend/module-caching.md §13.2 for rationale.
pub(crate) struct FnCompiler<'a, M: Module, C = (), L = ()>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Cranelift function builder.
    pub builder: FunctionBuilder<'a>,
    /// Reference to the compilation module (JITModule or ObjectModule).
    pub module: &'a mut M,
    /// The lexical binding environment — ONE SLOT PER BINDER, never per name
    /// (`design/backend/binding-scope.md` §3.1). It answers the dispatch
    /// question "does this name denote a local here"; ownership is the plan's.
    pub(crate) scope: ScopeChain,
    /// The names this body closed over (§3.2). NOT a scope frame: a capture is
    /// seeded once when the inner compiler is constructed and is released by
    /// the closure environment's drop glue, never by the body.
    pub(crate) captures: CaptureEnv,
    /// Shared immutable compilation context.
    pub(crate) ctx: CompileContext<'a, C, L>,
    /// The compilation-local canonical drop-glue registry
    /// (`design/backend/transitive-drop-glue.md` §3.4 D1). A field disjoint
    /// from [`Self::module`] and [`Self::ctx`], so
    /// `self.glue.request_if_owning(self.module, self.ctx.symbol_tables, ty)` is
    /// a legal three-way borrow; threaded into every inner compiler so nested
    /// bodies mint the same per-type body.
    pub(crate) glue: &'a mut crate::drop_glue::DropGlueRegistry,

    /// Next Cranelift Variable index (per-function counter).
    pub(crate) next_var: u32,

    /// The body's ownership plan (`design/backend/uniform-counting.md` §3): the
    /// only producer of move, duplicate and drop decisions. Emission reads it
    /// and decides nothing.
    pub(crate) plan: OwnershipPlan,
    /// Plan binder identity → its storage, recorded at each introduction.
    binders: HashMap<BinderId, BinderStore>,

    // --- TCO state ---
    //
    // Self-recursive tail calls are compiled as jumps to a loop header block
    // whose block params are the function params. Tail position propagates
    // into `if` branches, `let` bodies and match-arm bodies; arguments,
    // conditions and bindings are never in tail position.
    /// Name of the current function being compiled (for self-call detection).
    pub(crate) current_fn_name: Option<Symbol>,
    /// Loop header block for TCO (back-edge target for self-recursive tail calls).
    pub(crate) tail_loop_block: Option<Block>,
    /// Whether the current expression is in tail position.
    pub(crate) in_tail_position: bool,
    /// Number of parameters of the current function.
    pub(crate) fn_param_count: usize,

    /// Whether we are compiling inside a `(trace ...)` body.
    /// When true, sparkability analysis is disabled — trace bodies must
    /// execute sequentially to produce deterministic trace trees.
    pub(crate) in_trace_body: bool,

    /// Sparked apply-arguments for the function application currently being
    /// dispatched (lenient-eval.md §4.4). When `Some((args_ptr, map))`, the
    /// apply whose argument slice has base pointer `args_ptr` had its arguments
    /// at the indices in `map` sparked into IVars; the arg-list compilation
    /// FORCES those positions instead of recompiling them. Keyed by the
    /// argument-slice base pointer so a nested apply can never consult an
    /// enclosing apply's map.
    pub(crate) sparked_args: Option<(*const MonoExpr, HashMap<usize, Value>)>,

    /// Lazily-built, per-compiler cache of the recursive-SCC membership set over
    /// the loaded call graph — the M-static QUALITY-axis signal
    /// (`design/backend/lenient-eval.md` §2.8.2/§2.8.6).
    pub(crate) mstatic_recursive_cache: std::cell::RefCell<
        Option<std::rc::Rc<std::collections::HashSet<cranelisp_types::FQSymbol>>>,
    >,

    /// Accumulated create-gate **arm discriminator** for span-derived inner-
    /// function names (lenient-eval.md §3.6.2): the gate compiles the same
    /// expressions on both arms, so each arm's inner functions need distinct
    /// names. Empty outside any gate arm.
    pub(crate) gate_arm_disc: String,

    /// Monotonic per-compiler counter handing out unique create-gate ids.
    pub(crate) gate_counter: u32,

    /// When true, the create-gate (lenient-eval.md §3.6.2) is suppressed for
    /// the duration of a gate's direct (over-budget) arm, which bounds codegen
    /// for statically nested sparkable sites.
    pub(crate) suppress_spark_gate: bool,
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Create an inner `FnCompiler` for lambda bodies, continuations and spark
    /// thunks, planned by `plan`. The single construction point for inner
    /// compilers. TCO is disabled for inner functions.
    pub(crate) fn inner(
        builder: FunctionBuilder<'a>,
        module: &'a mut M,
        ctx: CompileContext<'a, C, L>,
        glue: &'a mut crate::drop_glue::DropGlueRegistry,
        fn_param_count: usize,
        plan: OwnershipPlan,
    ) -> Self {
        FnCompiler {
            builder,
            module,
            scope: ScopeChain::new(),
            captures: CaptureEnv::new(),
            ctx,
            glue,
            next_var: 0,
            plan,
            binders: HashMap::new(),
            current_fn_name: None,
            tail_loop_block: None,
            in_tail_position: false,
            fn_param_count,
            in_trace_body: false,
            sparked_args: None,
            mstatic_recursive_cache: std::cell::RefCell::new(None),
            gate_arm_disc: String::new(),
            gate_counter: 0,
            suppress_spark_gate: false,
        }
    }

    /// Plan a body and, in debug builds, check the plan's linearity before
    /// anything is emitted (`uniform-counting.md` §2, U1's seam assertion).
    pub(crate) fn plan_body(
        body: &MonoExpr,
        params: &[Symbol],
        captures: &[Symbol],
        owner: &str,
    ) -> Result<OwnershipPlan, CranelispError> {
        let plan = OwnershipPlan::build(
            body,
            params,
            captures,
            cranelisp_types::ownership_analysis_off(),
        );
        if cfg!(debug_assertions) {
            plan.check_linearity(body, params.len())
                .map_err(|violation| CranelispError::CodegenError {
                    message: format!(
                        "internal invariant violation: the ownership plan of '{owner}' is not \
                         linear: {}",
                        violation.0
                    ),
                    location: cranelisp_types::ErrorLocation::from_span(body.span()),
                })?;
        }
        Ok(plan)
    }

    /// Monomorphisation-aware discriminator for span-derived inner-function
    /// names (lambdas, fn-as-value wrappers, operator-as-value wrappers).
    ///
    /// **FIXME 0347 defect (1).** Inner functions are named by source span.
    /// When the ENCLOSING function is monomorphised, every instance re-emits
    /// the same span-derived name, so the enclosing function's mangled name is
    /// folded in as a per-instance discriminator; the create-gate arm token is
    /// folded in too.
    pub(crate) fn inner_fn_discriminator(&self) -> String {
        format!(
            "{}{}",
            inner_fn_discriminator_for(self.current_fn_name.as_ref()),
            self.gate_arm_disc,
        )
    }

    /// Compile a function definition body into Cranelift IR.
    ///
    /// Creates the entry block and the TCO loop header, binds parameters,
    /// compiles the body and returns its owned result. Every parameter is
    /// owned by the body and consumed where its plan says.
    // codegen threading: +glue (S118 S0 — the canonical drop-glue registry).
    #[allow(clippy::too_many_arguments)]
    pub fn compile_body(
        defn: &Defn,
        body: &MonoExpr,
        param_types: &[Option<Type>],
        func: &mut cranelift::codegen::ir::Function,
        func_ctx: &mut FunctionBuilderContext,
        module: &'a mut M,
        ctx: CompileContext<'a, C, L>,
        glue: &'a mut crate::drop_glue::DropGlueRegistry,
    ) -> Result<(), CranelispError> {
        let param_names: Vec<Symbol> = defn.params().iter().map(|(n, _)| n.clone()).collect();
        let plan = Self::plan_body(body, &param_names, &[], defn.name.as_ref())?;

        let mut builder = FunctionBuilder::new(func, func_ctx);

        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        // Loop header for TCO: one i64 block param per function param.
        let loop_header = builder.create_block();
        for _ in defn.params() {
            builder.append_block_param(loop_header, types::I64);
        }
        let entry_params: Vec<Value> = builder.block_params(entry_block).to_vec();
        builder.ins().jump(loop_header, &entry_params);
        // Not sealed yet: tail calls add back-edges during body compilation.
        builder.switch_to_block(loop_header);

        let mut compiler = FnCompiler::inner(builder, module, ctx, glue, defn.params().len(), plan);
        compiler.current_fn_name = Some(defn.name.clone());
        compiler.tail_loop_block = Some(loop_header);
        compiler.in_tail_position = true;

        for (i, param_name) in param_names.iter().enumerate() {
            let val = compiler.builder.block_params(loop_header)[i];
            let ty = match param_types.get(i) {
                Some(Some(ty)) => Some(ty.clone()),
                _ => Self::derive_param_type_from_body(body, param_name),
            };
            compiler.bind_binder(Intro::Param(i), param_name, val, ty)?;
        }

        let result = compiler.compile_expr(body)?;
        compiler.builder.ins().return_(&[result]);

        compiler.builder.seal_all_blocks();
        compiler.builder.finalize();
        Ok(())
    }

    /// Compile a monomorphised expression to an OWNED value: every heap value
    /// an expression yields carries one reference its receiver consumes
    /// (`uniform-counting.md` §1).
    pub fn compile_expr(&mut self, expr: &MonoExpr) -> Result<Value, CranelispError> {
        let value = self.compile_expr_kind(expr)?;
        self.emit_post_drops(expr)?;
        Ok(value)
    }

    fn compile_expr_kind(&mut self, expr: &MonoExpr) -> Result<Value, CranelispError> {
        match expr {
            MonoExpr::IntLit { value, .. } => self.compile_int_lit(*value),
            MonoExpr::FloatLit { value, .. } => self.compile_float_lit(*value),
            MonoExpr::BoolLit { value, .. } => self.compile_bool_lit(*value),
            MonoExpr::StringLit { value, span, .. } => self.compile_string_lit(value, *span),
            MonoExpr::Var {
                name,
                span,
                resolved_call,
                resolution,
                ty,
                ..
            } => {
                if let Some(occurrence) = self.plan.occurrence(expr) {
                    return self.compile_occurrence(name, occurrence, *span);
                }
                let inferred = ty.to_type();
                self.compile_var(
                    name,
                    *span,
                    resolved_call.as_deref(),
                    Some(&inferred),
                    resolution,
                )
            }
            MonoExpr::Let {
                bindings,
                body,
                span,
                ..
            } => self.compile_let(expr, bindings, body, *span),
            MonoExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.compile_if(expr, cond, then_branch, else_branch),
            MonoExpr::Lambda {
                params,
                body,
                span,
                ty,
                ..
            } => {
                let captures = self.plan.captures(expr).map(<[_]>::to_vec).ok_or_else(|| {
                    CranelispError::CodegenError {
                        message: "internal invariant violation: a lambda has no planned captures"
                            .into(),
                        location: cranelisp_types::ErrorLocation::from_span(*span),
                    }
                })?;
                let lambda_type = ty.to_type();
                self.compile_lambda(params, body, *span, Some(&lambda_type), &captures)
            }
            MonoExpr::Apply {
                callee,
                args,
                span,
                resolved_call,
                dispatch,
                ty,
                ..
            } => {
                let apply_type = ty.to_type();
                let apply_target = match dispatch {
                    ApplyRef::Dispatch(fq) => Some(fq),
                    ApplyRef::ViaCallee => None,
                };
                self.compile_apply(
                    expr,
                    callee,
                    args,
                    *span,
                    resolved_call.as_deref(),
                    apply_target,
                    Some(&apply_type),
                )
            }
            MonoExpr::Match {
                scrutinee,
                arms,
                span,
                ..
            } => self.compile_match(expr, scrutinee, arms, *span),
            MonoExpr::VecLit { span, .. } => self.compile_vec_lit(expr, *span),
            MonoExpr::Trace {
                modules,
                body,
                span,
                ..
            } => self.compile_trace(modules, body, *span),
            MonoExpr::ParBind {
                bindings,
                body,
                span,
                ..
            } => self.compile_par_bind(expr, bindings, body, *span),
            MonoExpr::LaunchContinue {
                launched,
                continuation,
                span,
                ..
            } => self.compile_launch_continue(expr, launched, continuation, *span),
            MonoExpr::ConstrADT { tag, span, ty, .. } => {
                self.compile_constr_adt(expr, *tag, *span, ty)
            }
        }
    }

    // --- The counting primitives the plan drives ---

    /// A variable occurrence the plan resolved: the binder's value, duplicated
    /// when the plan says so.
    fn compile_occurrence(
        &mut self,
        name: &Symbol,
        occurrence: Occurrence,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let (var, ty, use_) = match occurrence {
            Occurrence::Owned { binder, use_ } => {
                let store = self.binder_store(binder, span)?;
                (store.var, store.ty.clone(), use_)
            }
            Occurrence::Capture => {
                let capture =
                    self.captures
                        .get(name)
                        .ok_or_else(|| CranelispError::CodegenError {
                            message: format!(
                                "internal invariant violation: capture '{name}' is absent from the \
                             capture environment"
                            ),
                            location: cranelisp_types::ErrorLocation::from_span(span),
                        })?;
                (capture.var(), capture.ty().cloned(), Use::Duplicate)
            }
        };
        let val = self.builder.use_var(var);
        if use_ == Use::Duplicate {
            self.emit_dup(val, ty.as_ref());
        }
        Ok(val)
    }

    /// The type the value `node` yields is counted at.
    ///
    /// A planned variable occurrence yields its binder's value, so it is
    /// counted at the binder's recorded type, which a drop of that binder also
    /// reads (`uniform-counting.md` §3.4 item 2). A synthetic body's nodes carry
    /// the lenient builder's `Int` placeholder while its parameters carry the
    /// signature's type (item 1), so reading the node there loses the release.
    /// An occurrence whose binder has no recorded concrete type keeps its
    /// node's type: an unrecorded type owns no heap, and a residual variable is
    /// FIXME 0903's face, which item 4 leaves to the non-concrete release
    /// contract.
    pub(crate) fn counted_type(&self, node: &MonoExpr) -> Type {
        let recorded = match (self.plan.occurrence(node), node) {
            (Some(Occurrence::Owned { binder, .. }), _) => self
                .binders
                .get(&binder)
                .and_then(|store| store.ty.as_ref()),
            (Some(Occurrence::Capture), MonoExpr::Var { name, .. }) => {
                self.captures.get(name).and_then(|capture| capture.ty())
            }
            _ => None,
        };
        match recorded {
            Some(ty) if cranelisp_types::ConcreteType::from_type(ty).is_ok() => ty.clone(),
            _ => node.ty().to_type(),
        }
    }

    fn binder_store(&self, binder: BinderId, span: Span) -> Result<&BinderStore, CranelispError> {
        self.binders
            .get(&binder)
            .ok_or_else(|| CranelispError::CodegenError {
                message: format!(
                    "internal invariant violation: planned binder {binder:?} was never bound"
                ),
                location: cranelisp_types::ErrorLocation::from_span(span),
            })
    }

    /// Bind the binder the plan introduces at `intro` to the owned `val`, and
    /// drop it at once when the plan says it is dead at its introduction.
    pub(crate) fn bind_binder(
        &mut self,
        intro: Intro,
        name: &Symbol,
        val: Value,
        ty: Option<Type>,
    ) -> Result<(), CranelispError> {
        let var = self.bind_local(name, val, ty.clone());
        let Some(binder) = self.plan.binder_at(intro) else {
            return Err(CranelispError::CodegenError {
                message: format!(
                    "internal invariant violation: binder '{name}' was not planned at {intro:?}"
                ),
                location: cranelisp_types::ErrorLocation::from_span(Span::SYNTHETIC),
            });
        };
        self.binders.insert(binder, BinderStore { var, ty });
        if self.plan.dead_at_intro(binder) {
            self.emit_drop_binder(binder)?;
        }
        Ok(())
    }

    /// Bind a pattern field the plan says is used, or leave an unused one
    /// unowned. A used field is duplicated out of the scrutinee, which the arm
    /// then drops; an unused one is neither duplicated nor dropped, the fused
    /// form of a binder dead at its introduction.
    pub(crate) fn bind_field_binder(
        &mut self,
        intro: Intro,
        name: &Symbol,
        val: Value,
        ty: Option<Type>,
    ) -> Result<(), CranelispError> {
        let var = self.bind_local(name, val, ty.clone());
        let Some(binder) = self.plan.binder_at(intro) else {
            return Err(CranelispError::CodegenError {
                message: format!(
                    "internal invariant violation: field binder '{name}' was not planned"
                ),
                location: cranelisp_types::ErrorLocation::from_span(Span::SYNTHETIC),
            });
        };
        if !self.plan.dead_at_intro(binder) {
            self.binders.insert(binder, BinderStore { var, ty });
        }
        Ok(())
    }

    /// Is the pattern field at `intro` used, so the arm must duplicate it?
    pub(crate) fn field_is_used(&self, intro: Intro) -> bool {
        self.plan
            .binder_at(intro)
            .is_some_and(|binder| !self.plan.dead_at_intro(binder))
    }

    /// One increment of an owned heap value of type `ty`, guarded for a value
    /// that may be a bare nullary tag. A scalar or untyped value is untouched.
    pub(crate) fn emit_dup(&mut self, val: Value, ty: Option<&Type>) {
        let Some(ty) = ty else {
            return;
        };
        match signature_heap_category(ty, Some(self.ctx.symbol_tables)) {
            HeapCategory::AlwaysHeap => heap::emit_rc_inc(&mut self.builder, self.module, val),
            HeapCategory::Mixed => heap::emit_rc_inc_guarded(&mut self.builder, self.module, val),
            HeapCategory::NeverHeap | HeapCategory::Value => {}
        }
    }

    /// Release one owned heap value of type `ty` through its canonical glue.
    ///
    /// # The non-concrete arm — TYPE-keyed, and known to be the wrong key
    ///
    /// The disposition authority is
    /// `design/backend/non-concrete-release-contract.md` §4 and §7.4 (FIXME
    /// 0903). No frame's parameter is residual-typed: a codegen target is a
    /// `Life::Concrete` body, whose slot exists only for a concrete scheme. A
    /// residual type arrives from inside a body, chiefly a constructor field
    /// read from the declaration's scheme (contract §7.4), and takes the
    /// shallow guarded dec below. A frame key was implemented and measured at
    /// **+16 hard codegen refusals over the `spec_*` corpus**, so do not narrow
    /// the key on its own (contract §8 reject list).
    pub(crate) fn emit_release(
        &mut self,
        val: Value,
        ty: Option<&Type>,
    ) -> Result<(), CranelispError> {
        let Some(ty) = ty else {
            return Ok(());
        };
        if !self.is_heap_type(ty) {
            return Ok(());
        }
        if cranelisp_types::ConcreteType::from_type(ty).is_err() {
            let dealloc = self.ctx.dealloc_func_id;
            heap::emit_rc_dec_guarded(&mut self.builder, self.module, val, dealloc, None, true);
            return Ok(());
        }
        self.emit_typed_rc_dec(val, ty)
    }

    /// Drop the reference `binder` holds.
    pub(crate) fn emit_drop_binder(&mut self, binder: BinderId) -> Result<(), CranelispError> {
        let store = self.binder_store(binder, Span::SYNTHETIC)?.clone();
        let val = self.builder.use_var(store.var);
        self.emit_release(val, store.ty.as_ref())
    }

    fn emit_drops(&mut self, binders: &[BinderId]) -> Result<(), CranelispError> {
        for binder in binders {
            self.emit_drop_binder(*binder)?;
        }
        Ok(())
    }

    /// The drops the plan places on entry to branch `branch` of the `if` or
    /// `match` at `node`.
    pub(crate) fn emit_entry_drops(
        &mut self,
        node: usize,
        branch: usize,
    ) -> Result<(), CranelispError> {
        let drops = self.plan.entry_drops(node, branch).to_vec();
        self.emit_drops(&drops)
    }

    /// Moves off: the binders dropped at every arm entry of the match `node`.
    pub(crate) fn emit_scrutinee_drops(&mut self, node: usize) -> Result<(), CranelispError> {
        let drops = self.plan.scrutinee_drops(node).to_vec();
        self.emit_drops(&drops)
    }

    /// Moves off: the binders dropped once `node` has completed.
    pub(crate) fn emit_post_drops(&mut self, node: &MonoExpr) -> Result<(), CranelispError> {
        let drops = self.plan.post_drops(node).to_vec();
        self.emit_drops(&drops)
    }

    /// The frame's half of a lenient spark: the thunk duplicated every capture,
    /// so the frame drops the binders the sequential evaluation of `node` would
    /// have consumed, at the point that evaluation would have run.
    pub(crate) fn emit_spark_consumption(&mut self, node: &MonoExpr) -> Result<(), CranelispError> {
        let drops = self.plan.consumed_within(node);
        self.emit_drops(&drops)
    }

    /// The captures of a backend-synthesized closure over `body` that the plan
    /// never saw: every free name that resolves here, sorted, each duplicated.
    pub(crate) fn duplicating_captures(
        &self,
        params: &[Symbol],
        body: &MonoExpr,
    ) -> Vec<CaptureEntry> {
        let mut names: Vec<Symbol> = super::control_flow::find_free_vars(body, params)
            .into_iter()
            .filter(|name| self.binds(name))
            .collect();
        names.sort();
        names
            .into_iter()
            .map(|name| CaptureEntry {
                name,
                occurrence: Occurrence::Capture,
            })
            .collect()
    }

    /// Store one capture entry's value: the denoted binder's value, with one
    /// increment unless the plan moves the binder into the closure. Returns
    /// `None` for a name nothing here binds.
    pub(crate) fn capture_value(&mut self, entry: &CaptureEntry) -> Option<Value> {
        let binding = self.lookup_binding(&entry.name)?;
        let (var, ty) = (binding.var(), binding.ty().cloned());
        let val = self.builder.use_var(var);
        let moves = matches!(
            entry.occurrence,
            Occurrence::Owned {
                use_: Use::Move,
                ..
            }
        );
        if !moves {
            self.emit_dup(val, ty.as_ref());
        }
        Some(val)
    }

    /// Compile the backend-synthesized spark thunk `thunk_expr`, a zero-arg
    /// `MonoExpr::Lambda` over a clone the plan never saw. Its captures all
    /// duplicate; the caller drops what the sequential evaluation
    /// would have consumed ([`Self::emit_spark_consumption`]).
    pub(crate) fn compile_spark_thunk(
        &mut self,
        thunk_expr: &MonoExpr,
    ) -> Result<Value, CranelispError> {
        let MonoExpr::Lambda {
            params,
            body,
            span,
            ty,
            ..
        } = thunk_expr
        else {
            return Err(CranelispError::CodegenError {
                message: "internal invariant violation: a spark thunk is not a lambda".into(),
                location: cranelisp_types::ErrorLocation::from_span(thunk_expr.span()),
            });
        };
        let captures = self.duplicating_captures(params, body);
        let lambda_type = ty.to_type();
        self.compile_lambda(params, body, *span, Some(&lambda_type), &captures)
    }

    /// Allocate a fresh Cranelift Variable index.
    ///
    /// PRIVATE, and that visibility is load-bearing: it makes [`Self::bind_local`]
    /// and [`Self::bind_capture`] the only ways a `Variable` can come into
    /// existence (`binding-scope.md` §5).
    fn fresh_variable(&mut self) -> Variable {
        let idx = self.next_var;
        self.next_var += 1;
        Variable::new(idx as usize)
    }

    pub(crate) fn push_scope(&mut self) {
        self.scope.push_frame();
    }

    /// Leave a scope: the frame's slots go with it. Nothing is released at
    /// scope exit; every reference was consumed where the plan said.
    pub(crate) fn pop_scope(&mut self) {
        self.scope.pop_frame();
    }

    /// Bind ONE binder in the innermost frame: mint its `Variable`, define it,
    /// and publish its value and type TOGETHER, after its initializer has been
    /// compiled (`binding-scope.md` §3.3).
    pub(crate) fn bind_local(&mut self, name: &Symbol, val: Value, ty: Option<Type>) -> Variable {
        let var = self.fresh_variable();
        self.builder.declare_var(var, types::I64);
        self.builder.def_var(var, val);
        self.scope.bind(name.clone(), var, ty);
        var
    }

    /// Seed ONE capture into this (inner) compiler's capture environment: mint
    /// its `Variable`, define it from the loaded environment slot, and record
    /// its type (`binding-scope.md` §3.2).
    pub(crate) fn bind_capture(&mut self, name: &Symbol, val: Value, ty: Option<Type>) {
        let var = self.fresh_variable();
        self.builder.declare_var(var, types::I64);
        self.builder.def_var(var, val);
        self.captures.insert(name.clone(), var, ty);
    }

    /// What does `name` denote here? The chain answers first; a capture answers
    /// only for a name no live slot binds (`binding-scope.md` §3.2).
    pub(crate) fn lookup_binding(&self, name: &Symbol) -> Option<Binding<'_>> {
        resolve_binding(&self.scope, &self.captures, name)
    }

    /// The recorded type of the binder `name` denotes here, if one was recorded.
    pub(crate) fn lookup_type(&self, name: &Symbol) -> Option<Type> {
        self.lookup_binding(name).and_then(Binding::ty).cloned()
    }

    /// Is `name` a live binding (a scope slot or a capture)?
    pub(crate) fn binds(&self, name: &Symbol) -> bool {
        self.lookup_binding(name).is_some()
    }

    /// S118 slice S4 (§7.4) — request the canonical drop glue for a capture
    /// slot's type, from the ENCLOSING compiler, before the environment glue
    /// body's `FunctionBuilder` is created. `Ok(None)` ⇒ the slot owns nothing.
    pub(crate) fn request_capture_glue(
        &mut self,
        ty: &Type,
    ) -> Result<Option<cranelift_module::FuncId>, CranelispError> {
        let concrete = cranelisp_types::ConcreteType::from_type(ty).map_err(|_| {
            crate::compiler::rc_emission::release_site_type_error(self.current_fn_name.as_ref(), ty)
        })?;
        self.glue
            .request_if_owning(self.module, self.ctx.symbol_tables, concrete)
    }

    /// Check if a type is heap-allocated and needs RC management.
    pub(crate) fn is_heap_type(&self, ty: &Type) -> bool {
        matches!(
            signature_heap_category(ty, Some(self.ctx.symbol_tables)),
            HeapCategory::AlwaysHeap | HeapCategory::Mixed
        )
    }

    /// Derive a function parameter's type from the first `Var` reference to it
    /// in the body, when the signature does not supply one.
    pub(crate) fn derive_param_type_from_body(body: &MonoExpr, name: &Symbol) -> Option<Type> {
        find_var_type_in_expr(body, name)
    }
}

/// Read the `confined` site fact off a [`MonoExpr`] node, for the spark density
/// scorer (`design/backend/ownership-codegen.md` §13.4). Only the five
/// allocation/capture-producing variants carry the fact (`StringLit`, `Lambda`,
/// `Apply`, `VecLit`, `ConstrADT` — the enum-level rustdoc on `MonoExpr`);
/// every other variant has no cell of its own to confine and answers `None`.
/// Backend-local (no `cranelisp-types` accessor); kept a total match so a new
/// fact-bearing variant is a compile error here.
pub(crate) fn node_confined(node: &MonoExpr) -> Option<bool> {
    match node {
        MonoExpr::StringLit { confined, .. }
        | MonoExpr::Lambda { confined, .. }
        | MonoExpr::Apply { confined, .. }
        | MonoExpr::VecLit { confined, .. }
        | MonoExpr::ConstrADT { confined, .. } => *confined,
        MonoExpr::IntLit { .. }
        | MonoExpr::FloatLit { .. }
        | MonoExpr::BoolLit { .. }
        | MonoExpr::Var { .. }
        | MonoExpr::Let { .. }
        | MonoExpr::If { .. }
        | MonoExpr::Match { .. }
        | MonoExpr::Trace { .. }
        | MonoExpr::ParBind { .. }
        | MonoExpr::LaunchContinue { .. } => None,
    }
}

/// Read the `escapes` site fact off a [`MonoExpr`] node. Only the five
/// allocation/capture-producing variants carry the fact (same set as
/// [`node_confined`]); every other variant answers `None`. Its consumer is the
/// spark density scorer (`design/backend/ownership-codegen.md` §13.4). Kept a
/// total match so a new fact-bearing variant is a compile error here.
pub(crate) fn node_escapes(node: &MonoExpr) -> Option<bool> {
    match node {
        MonoExpr::StringLit { escapes, .. }
        | MonoExpr::Lambda { escapes, .. }
        | MonoExpr::Apply { escapes, .. }
        | MonoExpr::VecLit { escapes, .. }
        | MonoExpr::ConstrADT { escapes, .. } => *escapes,
        MonoExpr::IntLit { .. }
        | MonoExpr::FloatLit { .. }
        | MonoExpr::BoolLit { .. }
        | MonoExpr::Var { .. }
        | MonoExpr::Let { .. }
        | MonoExpr::If { .. }
        | MonoExpr::Match { .. }
        | MonoExpr::Trace { .. }
        | MonoExpr::ParBind { .. }
        | MonoExpr::LaunchContinue { .. } => None,
    }
}

/// The ONE self-call identity predicate (Principle 7 single-source-of-truth /
/// Principle 24 "Resolve once") — consumed by the TCO fast-path (`compile_apply`,
/// `apply.rs`) and the spark SCC classifier (`classify_spark_callee`,
/// `utilization.rs`), so the two cannot answer "is this a self-call?" divergently
/// (FIXME 0654).
///
/// A call is a self-call iff EITHER:
/// - **carrier-keyed (fp1 shape):** the callee `Var`'s `VarRef::Global` storage
///   FQ equals the current fn's storage identity `{current_module,
///   current_fn_name}` — module AND symbol (the S113 W2b carrier fix; S114 typed
///   flip re-types the compared value from `Option<FQSymbol>` to the
///   `VarRef::Global` arm). A match requires the recorded storage target to BE
///   the current fn's identity, so a false positive is impossible; a
///   `VarRef::Local` callee (e.g. a `let`/`fn`/param local shadowing the fn name)
///   never matches here — self-recursion arrives as `VarRef::Global`; OR
/// - **`SigDispatch`-mangled (fp2 shape):** `resolved_call` is `SigDispatch {
///   mangled_name }` and `mangled_name == current_fn_name` — the monomorphised
///   constrained-poly self-recursion shape, where the callee's written name is
///   the base name but the current fn is the `{home}/{bare}${sig}` mono variant.
///   The `{home}/` prefix embeds the module, so a cross-module same-signature
///   dispatch fails to match by construction (`backend.md` §2.7.1).
///
/// Decides by the KEYED carrier / resolved dispatch, NEVER by bare written-name
/// equality (the 0632 name-as-identity class). `None` `current_fn_name` ⇒ never.
pub(crate) fn is_self_call(
    callee: &MonoExpr,
    resolved_call: Option<&ResolvedCall>,
    current_module: &ModuleFullPath,
    current_fn_name: Option<&Symbol>,
) -> bool {
    let Some(fn_name) = current_fn_name else {
        return false;
    };
    if let MonoExpr::Var {
        resolution: VarRef::Global(fq),
        ..
    } = callee
        && fq.module == *current_module
        && fq.symbol == *fn_name
    {
        return true;
    }
    matches!(
        resolved_call,
        Some(ResolvedCall::SigDispatch { target })
            if crate::callable_target_owner(target)
                .is_some_and(|owner| owner.module == *current_module)
                && crate::callable_target_label(target)
                    .is_some_and(|label| label.as_ref() == fn_name.as_ref())
    )
}

#[cfg(test)]
mod node_escapes_and_self_call_tests {
    //! `node_escapes` is total over the variant set; `is_self_call` decides
    //! self-recursion by the storage carrier, module and symbol.
    use super::{is_self_call, node_escapes};
    use cranelisp_types::{
        ConcreteType, FQSymbol, FQTypeName, ModuleFullPath, MonoExpr, ResolvedCall, Span, Symbol,
        TypeName,
    };

    fn int() -> ConcreteType {
        ConcreteType::Int
    }
    /// The enclosing module for the gate-3 fixtures. The bare-name / SigDispatch
    /// arms are module-agnostic; only the carrier arm consults it.
    fn m() -> ModuleFullPath {
        ModuleFullPath::from("user")
    }
    fn var(name: &str) -> MonoExpr {
        // No carrier ⇒ a `VarRef::Local` (a scope-stack/shadow reference); the
        // is_self_call carrier arm never matches a `Local`.
        MonoExpr::Var {
            name: Symbol::from(name),
            span: Span::new(0, 1),
            resolved_call: None,
            ty: int(),
            resolution: cranelisp_types::VarRef::Local {
                binder: Symbol::from(name),
                binding_span: Span::SYNTHETIC,
            },
        }
    }
    /// A `Var` carrying a `VarRef::Global` storage FQ — the fp1 carrier shape.
    fn var_with_target(name: &str, module: &str, symbol: &str) -> MonoExpr {
        MonoExpr::Var {
            name: Symbol::from(name),
            span: Span::new(0, 1),
            resolved_call: None,
            ty: int(),
            resolution: cranelisp_types::VarRef::Global(FQSymbol {
                module: ModuleFullPath::from(module),
                symbol: Symbol::from(symbol),
            }),
        }
    }
    fn constr(escapes: Option<bool>) -> MonoExpr {
        MonoExpr::ConstrADT {
            type_name: FQTypeName::new(ModuleFullPath::from("m"), TypeName::from("T")),
            tag: 0,
            fields: vec![],
            span: Span::new(0, 1),
            ty: int(),
            escapes,
            confined: None,
            unique_static: None,
        }
    }
    /// An `(f args…)` apply with the given callee name, escape fact, and resolved call.
    fn apply(
        callee: &str,
        args: Vec<MonoExpr>,
        escapes: Option<bool>,
        resolved: Option<ResolvedCall>,
    ) -> MonoExpr {
        MonoExpr::Apply {
            dispatch: cranelisp_types::ApplyRef::ViaCallee,
            callee: Box::new(var(callee)),
            args,
            span: Span::new(0, 3),
            resolved_call: resolved.map(Box::new),
            ty: int(),
            escapes,
            confined: None,
            unique_static: None,
            provenance: None,
        }
    }

    // --- node_escapes: total match, fact-bearing vs non-bearing variants ------
    #[test]
    fn escapes_reads_the_five_fact_bearing_variants() {
        // spec: design/backend/ownership-codegen.md §13.4 — escapes on ConstrADT/Apply/…
        assert_eq!(node_escapes(&constr(Some(false))), Some(false));
        assert_eq!(node_escapes(&constr(Some(true))), Some(true));
        assert_eq!(node_escapes(&constr(None)), None);
        assert_eq!(
            node_escapes(&apply("f", vec![], Some(false), None)),
            Some(false)
        );
        assert_eq!(
            node_escapes(&MonoExpr::VecLit {
                elements: vec![],
                span: Span::new(0, 1),
                ty: int(),
                escapes: Some(false),
                confined: None,
                unique_static: None
            }),
            Some(false)
        );
        assert_eq!(
            node_escapes(&MonoExpr::Lambda {
                params: vec![],
                body: Box::new(var("x")),
                span: Span::new(0, 1),
                ty: ConcreteType::Fn(vec![], Box::new(int())),
                escapes: Some(true),
                confined: None,
                unique_static: None
            }),
            Some(true)
        );
    }
    #[test]
    fn escapes_is_none_for_non_allocating_variants() {
        // spec: design/backend/ownership-codegen.md §13.4 — non-fact-bearing ⇒ None
        assert_eq!(node_escapes(&var("v")), None);
        assert_eq!(
            node_escapes(&MonoExpr::IntLit {
                value: 0,
                span: Span::new(0, 1),
                ty: int()
            }),
            None
        );
    }

    // spec: design/backend/backend.md §2.7.1 — a callee whose storage carrier is
    // the current fn's identity is a self-call whatever its written name; a
    // carrier in another module is not.
    #[test]
    fn self_call_is_decided_by_the_carrier_module_and_symbol() {
        let f = Symbol::from("s1");
        let callee = var_with_target("qloop", "user", "s1");
        assert!(is_self_call(&callee, None, &m(), Some(&f)));
        let foreign = var_with_target("qloop", "other", "s1");
        assert!(!is_self_call(&foreign, None, &m(), Some(&f)));
        assert!(!is_self_call(&var("s1"), None, &m(), Some(&f)));
    }

    // spec: design/backend/backend.md §2.7.1 — the monomorphised SigDispatch shape.
    #[test]
    fn sig_dispatch_mangled_self_call_is_a_self_call() {
        let f = Symbol::from("f$Int");
        let resolved: ResolvedCall = crate::test_support::sig_binding("user", "f$Int");
        assert!(is_self_call(&var("f"), Some(&resolved), &m(), Some(&f)));
        assert!(!is_self_call(
            &var("f"),
            Some(&resolved),
            &m(),
            Some(&Symbol::from("g"))
        ));
    }
}

#[cfg(test)]
mod b33_node_confined_tests {
    //! `node_confined` reads the `confined` site fact off the five
    //! allocation/capture-producing variants and answers `None` for every other
    //! variant. Its consumer is the spark density scorer
    //! (`design/backend/ownership-codegen.md` §13.4).
    use super::node_confined;
    use cranelisp_types::{ConcreteType, FQTypeName, ModuleFullPath, MonoExpr, Span, TypeName};

    fn int() -> ConcreteType {
        ConcreteType::Int
    }

    // The five fact-bearing variants, each parameterised over its `confined`.
    fn string_lit(c: Option<bool>) -> MonoExpr {
        MonoExpr::StringLit {
            value: "x".into(),
            span: Span::new(0, 1),
            ty: ConcreteType::String,
            escapes: None,
            confined: c,
            unique_static: None,
        }
    }
    fn lambda(c: Option<bool>) -> MonoExpr {
        MonoExpr::Lambda {
            params: vec![],
            body: Box::new(MonoExpr::IntLit {
                value: 0,
                span: Span::new(0, 1),
                ty: int(),
            }),
            span: Span::new(0, 1),
            ty: ConcreteType::Fn(vec![], Box::new(int())),
            escapes: None,
            confined: c,
            unique_static: None,
        }
    }
    fn apply(c: Option<bool>) -> MonoExpr {
        MonoExpr::Apply {
            callee: Box::new(MonoExpr::Var {
                name: "f".into(),
                span: Span::new(0, 1),
                resolved_call: None,
                resolution: cranelisp_types::VarRef::Local {
                    binder: "f".into(),
                    binding_span: Span::SYNTHETIC,
                },
                ty: int(),
            }),
            args: vec![],
            span: Span::new(0, 2),
            resolved_call: None,
            ty: int(),
            escapes: None,
            confined: c,
            unique_static: None,
            provenance: None,
            dispatch: cranelisp_types::ApplyRef::ViaCallee,
        }
    }
    fn vec_lit(c: Option<bool>) -> MonoExpr {
        // node_confined reads only `confined`; the ty is immaterial here.
        MonoExpr::VecLit {
            elements: vec![],
            span: Span::new(0, 1),
            ty: int(),
            escapes: None,
            confined: c,
            unique_static: None,
        }
    }
    fn constr_adt(c: Option<bool>) -> MonoExpr {
        MonoExpr::ConstrADT {
            type_name: FQTypeName::new(ModuleFullPath::from("m"), TypeName::from("T")),
            tag: 0,
            fields: vec![],
            span: Span::new(0, 1),
            ty: int(),
            escapes: None,
            confined: c,
            unique_static: None,
        }
    }

    // POSITIVE: each fact-bearing variant reports its own confined field.
    #[test]
    fn fact_bearing_variants_report_confined() {
        for mk in [
            string_lit as fn(Option<bool>) -> MonoExpr,
            lambda,
            apply,
            vec_lit,
            constr_adt,
        ] {
            assert_eq!(node_confined(&mk(Some(true))), Some(true));
            assert_eq!(node_confined(&mk(Some(false))), Some(false));
            assert_eq!(node_confined(&mk(None)), None);
        }
    }

    // NEGATIVE: non-allocation variants have no cell of their own ⇒ None.
    // Var / Let / If / Match are the through-carriers,
    // never the fact source.
    #[test]
    fn non_fact_bearing_variants_are_none() {
        let var = MonoExpr::Var {
            name: "v".into(),
            span: Span::new(0, 1),
            resolved_call: None,
            resolution: cranelisp_types::VarRef::Local {
                binder: "v".into(),
                binding_span: Span::SYNTHETIC,
            },
            ty: int(),
        };
        let iflit = MonoExpr::If {
            cond: Box::new(MonoExpr::BoolLit {
                value: true,
                span: Span::new(0, 1),
                ty: ConcreteType::Bool,
            }),
            then_branch: Box::new(var.clone()),
            else_branch: Box::new(var.clone()),
            span: Span::new(0, 2),
            ty: int(),
        };
        let intlit = MonoExpr::IntLit {
            value: 0,
            span: Span::new(0, 1),
            ty: int(),
        };
        assert_eq!(node_confined(&var), None);
        assert_eq!(node_confined(&iflit), None);
        assert_eq!(node_confined(&intlit), None);
    }
}
