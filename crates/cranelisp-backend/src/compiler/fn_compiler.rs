//! The per-function CLIF emitter: the `FnCompiler` struct, its construction
//! (`inner`, `compile_body`, `bind_defn_params`), the expression-dispatch entry
//! (`compile_expr`), scope lifecycle, and the small per-fn predicates.
//! `MatchContext` is per-arm `FnCompiler` state, kept adjacent to the struct it
//! threads through.

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use cranelisp_types::{
    CranelispError, Defn, MonoExpr, ModuleEntry, Span, Symbol, Type,
};

use crate::heap::{self, HeapCategory};

use super::{
    find_var_type_in_expr, inner_fn_discriminator_for, signature_heap_category, CompileContext,
};

/// Match-arm-invariant data bundled to reduce parameter counts in
/// `compile_constructor_pattern`.
///
/// Narrowed to `pub(crate)` in S75 W3 — per-arm codegen state, no out-of-crate
/// consumer.
pub(crate) struct MatchContext {
    /// The compiled scrutinee value.
    pub scrut_val: Value,
    /// The inferred type of the scrutinee expression (for field type resolution).
    pub scrut_type: Option<Type>,
    /// The block to branch to if this arm does not match.
    pub next_block: Block,
    /// The merge block where all arms converge.
    pub merge_block: Block,
    /// The saved tail-position flag from before the match.
    pub saved_tail: bool,
}

/// Per-function compilation context.
///
/// Generic over `M: Module` so the same codegen can target both `JITModule`
/// (for immediate execution) and `ObjectModule` (for `.o` file generation).
/// See design/backend/module-caching.md §13.2 for rationale.
// Sprint 58 Wave 3b (Decision 35): generic over `C: CodeStore` and
// `L: LinkerStore` so it can hold `CompileContext<'a, C, L>`. Defaults
// to `<()>`-pinned for backward compat with the typecheck-product flavour.
//
// Narrowed to `pub(crate)` in S75 W3 — the per-function CLIF emitter; no
// out-of-crate consumer (int reaches codegen only via the free fn
// `compile_to_module`). Its `pub` methods/fields drop from the public API
// with the type.
pub(crate) struct FnCompiler<'a, M: Module, C = (), L = ()>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Cranelift function builder.
    pub builder: FunctionBuilder<'a>,
    /// Reference to the compilation module (JITModule or ObjectModule).
    pub module: &'a mut M,
    /// Local variable bindings (name -> Cranelift Variable).
    pub(crate) variables: HashMap<Symbol, Variable>,
    /// Scope stack: each frame is a list of variable names introduced.
    pub(crate) scope_stack: Vec<Vec<Symbol>>,
    /// Shared immutable compilation context.
    pub(crate) ctx: CompileContext<'a, C, L>,

    /// Next Cranelift Variable index (per-function counter).
    pub(crate) next_var: u32,

    // --- TCO state ---
    //
    // Tail Call Optimization (TCO): loop-based self-TCO.
    //
    // Self-recursive tail calls are compiled as jumps to a loop header block
    // instead of actual function calls. This converts recursion into iteration
    // with O(1) stack usage.
    //
    // The pattern:
    //   1. compile_body creates a loop_header block with block params for each fn param
    //   2. Entry block jumps to loop_header with initial param values
    //   3. Loop_header is NOT sealed eagerly (back-edges from tail calls added later)
    //   4. Body is compiled with in_tail_position = true
    //   5. Tail self-calls jump back to loop_header with new arg values
    //   6. All blocks sealed at the end
    //
    // CRITICAL: compile_apply must set in_tail_position = false before compiling args.
    // Tail position propagation:
    //   - If body / else body: inherits tail position
    //   - Let body: inherits tail position
    //   - Match arm bodies: inherit tail position
    //   - Args, conditions, bindings: NOT in tail position

    /// Name of the current function being compiled (for self-call detection).
    pub(crate) current_fn_name: Option<Symbol>,
    /// Loop header block for TCO (back-edge target for self-recursive tail calls).
    pub(crate) tail_loop_block: Option<Block>,
    /// Whether the current expression is in tail position.
    pub(crate) in_tail_position: bool,
    /// Number of parameters of the current function.
    pub(crate) fn_param_count: usize,

    // --- Ring 1 heap state (scaffolding for RC emission in Ring 2) ---

    /// Types of local variables, for RC management.
    pub(crate) variable_types: HashMap<Symbol, Type>,
    /// Last-use information: (var_name, span) -> is_last_use.
    pub(crate) last_uses: HashMap<(Symbol, Span), bool>,
    /// Set of variables whose ownership has been transferred (consumed).
    pub(crate) consumed_vars: std::collections::HashSet<Symbol>,
    /// Variables that borrow from a parent (e.g., pattern match field bindings).
    /// Borrowed vars skip both inc (at extraction) and dec (at scope exit).
    /// The owner (scrutinee) handles cleanup via its own RC management.
    pub(crate) borrowed_vars: std::collections::HashSet<Symbol>,
    /// Captured variable names (variables closed over by a lambda).
    /// These are NEVER eligible for last-use transfer.
    pub(crate) captured_vars: std::collections::HashSet<Symbol>,

    /// Drop glue FuncIds for closure variables.
    /// When a closure with heap-typed captures is bound to a variable,
    /// the drop glue function is stored here so that `pop_scope_with_cleanup`
    /// can pass it to `emit_rc_dec` when freeing the closure.
    pub(crate) closure_drop_glue: HashMap<Symbol, FuncId>,

    /// Depth counter for inline drop glue generation.
    /// Prevents infinite IR for recursive types (e.g., List).
    /// Allows limited nesting for non-recursive parametric types (e.g., Option(Option(String))).
    pub(crate) drop_glue_depth: u32,

    /// Pending closure drop glue from the last `compile_lambda` call.
    /// Set by `compile_lambda`, consumed by `compile_let` or `compile_body`
    /// when binding the closure value to a variable name.
    pub(crate) pending_closure_drop_glue: Option<FuncId>,

    /// Whether we are compiling inside a `(trace ...)` body.
    /// When true, sparkability analysis is disabled — trace bodies must
    /// execute sequentially to produce deterministic trace trees.
    pub(crate) in_trace_body: bool,
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{

    /// Create an inner `FnCompiler` for lambda bodies, continuations,
    /// or (future) drop glue. This is the single construction point for
    /// inner compilers (ring1-checklist section 5.9).
    ///
    /// TCO state is disabled for inner functions (no self-call detection,
    /// no tail loop). The scope and variable maps start fresh.
    pub(crate) fn inner(
        builder: FunctionBuilder<'a>,
        module: &'a mut M,
        ctx: CompileContext<'a, C, L>,
        fn_param_count: usize,
        last_uses: HashMap<(Symbol, Span), bool>,
    ) -> Self {
        FnCompiler {
            builder,
            module,
            variables: HashMap::new(),
            scope_stack: vec![vec![]],
            ctx,
            next_var: 0,
            current_fn_name: None,
            tail_loop_block: None,
            in_tail_position: false,
            fn_param_count,
            variable_types: HashMap::new(),
            last_uses,
            consumed_vars: std::collections::HashSet::new(),
            borrowed_vars: std::collections::HashSet::new(),
            captured_vars: std::collections::HashSet::new(),
            closure_drop_glue: HashMap::new(),
            drop_glue_depth: 0,
            pending_closure_drop_glue: None,
            in_trace_body: false,
        }
    }

    /// Monomorphisation-aware discriminator for span-derived inner-function
    /// names (lambdas, fn-as-value wrappers, operator-as-value wrappers).
    ///
    /// **FIXME 0347 defect (1).** Inner functions are named by source span
    /// (`__lambda_<start>_<end>__`, `__wrap_<name>_<start>_<end>__`). When the
    /// ENCLOSING function is monomorphised — the same source span compiled into
    /// N distinct monomorphic instances within ONE `Module` — every instance
    /// re-emits the same span-derived name, so the second `define_function`
    /// collides (`Duplicate definition of identifier`). The enclosing function's
    /// name IS the per-instance discriminator: each mono copy carries a distinct
    /// mangled name (`reduce$Int+Vec`, `id$Int`, …), so prefixing the inner
    /// name with it uniquifies the N copies. When no enclosing name is set
    /// (top-level expression, nested-lambda inner compiler), the span alone
    /// suffices for uniqueness within that scope, so the prefix is empty.
    ///
    /// Non-`[A-Za-z0-9_]` chars in the enclosing name (`$`, `+`, `/`, `.`) are
    /// mapped to `_` so the result is a clean Cranelift symbol.
    pub(crate) fn inner_fn_discriminator(&self) -> String {
        inner_fn_discriminator_for(self.current_fn_name.as_ref())
    }

    /// Compile a function definition body into Cranelift IR.
    ///
    /// This is the main entry point called by Jit::compile_defn.
    /// Creates the entry block, loop header (for TCO), binds parameters,
    /// compiles the body, and finalizes.
    pub fn compile_body(
        defn: &Defn,
        body: &MonoExpr,
        func: &mut cranelift::codegen::ir::Function,
        func_ctx: &mut FunctionBuilderContext,
        module: &'a mut M,
        ctx: CompileContext<'a, C, L>,
    ) -> Result<(), CranelispError> {
        let mut builder = FunctionBuilder::new(func, func_ctx);

        // Entry block: receives function parameters.
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        // Create loop header block for TCO: one i64 block param per function param.
        let loop_header = builder.create_block();
        for _ in defn.params() {
            builder.append_block_param(loop_header, types::I64);
        }

        // Jump from entry to loop header with initial parameter values.
        let entry_params: Vec<Value> = builder.block_params(entry_block).to_vec();
        builder.ins().jump(loop_header, &entry_params);

        // Switch to loop header. Do NOT seal it yet -- back-edges from tail calls
        // will be added during body compilation.
        builder.switch_to_block(loop_header);

        // Compute last-use info for the body.
        let last_uses = heap::compute_last_uses(body);

        let mut compiler = FnCompiler {
            builder,
            module,
            variables: HashMap::new(),
            scope_stack: vec![vec![]],
            ctx,
            next_var: 0,
            current_fn_name: Some(defn.name.clone()),
            tail_loop_block: Some(loop_header),
            in_tail_position: true,
            fn_param_count: defn.params().len(),
            variable_types: HashMap::new(),
            last_uses,
            consumed_vars: std::collections::HashSet::new(),
            borrowed_vars: std::collections::HashSet::new(),
            captured_vars: std::collections::HashSet::new(),
            closure_drop_glue: HashMap::new(),
            drop_glue_depth: 0,
            pending_closure_drop_glue: None,
            in_trace_body: false,
        };

        // Seed the function's parameters into scope + variable_types.
        compiler.bind_defn_params(defn, body, loop_header);

        // Compile the function body with scope cleanup for parameters.
        // This implements the consuming calling convention: the callee owns
        // heap-typed parameters and dec's them at exit. The caller inc's
        // variable arguments before the call.
        let skip_var = Self::return_var_in_scope(body, compiler.scope_stack.last());
        let result = compiler.compile_expr(body)?;
        compiler.protect_return_value(&skip_var, result, body);
        compiler.pop_scope_with_cleanup(skip_var.as_ref());

        // Return the result.
        compiler.builder.ins().return_(&[result]);

        // Seal all blocks (including loop_header which may have back-edges).
        compiler.builder.seal_all_blocks();
        compiler.builder.finalize();

        Ok(())
    }

    /// Seed the function's parameters into scope and `variable_types`.
    ///
    /// Binds each `defn` parameter from the loop-header block params (not the
    /// entry block — TCO back-edges feed the loop header) to a fresh Cranelift
    /// `Variable`, records the binding in the current scope frame, and records
    /// the parameter's authoritative type so scope cleanup can emit `rc_dec`
    /// for heap-typed parameters at function exit.
    fn bind_defn_params(&mut self, defn: &Defn, body: &MonoExpr, loop_header: Block) {
        // Look up the defn's inferred type to get authoritative parameter types.
        // This is essential for unused parameters: derive_param_type scans
        // use sites, so unused params (e.g., `_s` in `(defn f [:String _s] 42)`)
        // would have no type recorded and scope cleanup would skip their RC dec.
        //
        // Read from the symbol table's Scheme.ty (authoritative source) rather
        // than from expr_types side map (Step 1c: AST-sourced codegen).
        let defn_param_types: Vec<Option<Type>> = self.ctx.symbol_tables
            .get(&self.ctx.current_module)
            .and_then(|table| {
                if let Some(ModuleEntry::Def { scheme, .. }) = table.get(defn.name.as_ref())
                    && let Type::Fn(ref param_types, _) = scheme.ty {
                        return Some(param_types.iter().map(|t| Some(t.clone())).collect());
                }
                None
            })
            .unwrap_or_else(|| vec![None; defn.params().len()]);

        // Bind function parameters from loop header block params (not entry block).
        // Also record parameter types in variable_types so scope cleanup
        // can emit rc_dec for heap-typed parameters at function exit.
        for (i, (param_name, _)) in defn.params().iter().enumerate() {
            let val = self.builder.block_params(loop_header)[i];
            let var = self.fresh_variable();
            self.builder.declare_var(var, types::I64);
            self.builder.def_var(var, val);
            self.variables.insert(param_name.clone(), var);
            self
                .scope_stack
                .last_mut()
                .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                .push(param_name.clone());

            // Use the defn's inferred param type (from symbol table) first.
            // Fall back to derive_param_type_from_body (use-site inference) if the
            // defn type isn't available.
            if let Some(Some(ty)) = defn_param_types.get(i) {
                self.variable_types.insert(param_name.clone(), ty.clone());
            } else if let Some(ty) = Self::derive_param_type_from_body(body, param_name) {
                self.variable_types.insert(param_name.clone(), ty);
            }
        }
    }

    /// Compile a monomorphised expression, dispatching to the appropriate
    /// handler.
    ///
    /// The codegen walk is over [`MonoExpr`] (concrete-boundary-type.md §3.1,
    /// FIXME 0391): every node carries a `ty: ConcreteType` non-optionally, so a
    /// `Type::Var` is *unrepresentable* at every codegen-reaching position. The
    /// `Annotate` variant is erased at the `MonoExpr::from_expr` build, so it has
    /// no arm here.
    pub fn compile_expr(&mut self, expr: &MonoExpr) -> Result<Value, CranelispError> {
        match expr {
            MonoExpr::IntLit { value, .. } => self.compile_int_lit(*value),
            MonoExpr::FloatLit { value, .. } => self.compile_float_lit(*value),
            MonoExpr::BoolLit { value, .. } => self.compile_bool_lit(*value),
            MonoExpr::StringLit { value, span, .. } => self.compile_string_lit(value, *span),
            MonoExpr::Var {
                name,
                span,
                resolved_call,
                ty,
            } => {
                // The signature-path bridge: `compile_var` reads the variable's
                // type as a `&Type` (for the value-position trait-method arity).
                // The node's `ConcreteType` embeds losslessly into a `Type`.
                let inferred = ty.to_type();
                self.compile_var(name, *span, resolved_call.as_deref(), Some(&inferred))
            }
            MonoExpr::Let {
                bindings,
                body,
                span,
                ..
            } => self.compile_let(bindings, body, *span),
            MonoExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.compile_if(cond, then_branch, else_branch),
            MonoExpr::Lambda {
                params, body, span, ty,
            } => {
                let lambda_type = ty.to_type();
                self.compile_lambda(params, body, *span, Some(&lambda_type))
            }
            MonoExpr::Apply {
                callee,
                args,
                span,
                resolved_call,
                ty,
            } => {
                let apply_type = ty.to_type();
                self.compile_apply(
                    callee,
                    args,
                    *span,
                    resolved_call.as_deref(),
                    Some(&apply_type),
                )
            }
            MonoExpr::Match {
                scrutinee,
                arms,
                span,
                ..
            } => self.compile_match(scrutinee, arms, *span),
            MonoExpr::VecLit { elements, span, .. } => self.compile_vec_lit(elements, *span),
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
            } => self.compile_par_bind(bindings, body, *span),
            MonoExpr::ConstrADT {
                tag,
                fields,
                span,
                ..
            } => self.compile_constr_adt(*tag, fields, *span),
        }
    }

    /// Allocate a fresh Cranelift Variable index.
    pub(crate) fn fresh_variable(&mut self) -> Variable {
        let idx = self.next_var;
        self.next_var += 1;
        Variable::new(idx as usize)
    }

    pub(crate) fn push_scope(&mut self) {
        self.scope_stack.push(vec![]);
    }

    pub(crate) fn pop_scope(&mut self) {
        if let Some(frame) = self.scope_stack.pop() {
            for name in frame {
                self.variables.remove(&name);
                self.variable_types.remove(&name);
            }
        }
    }

    /// Pop a scope frame and emit `rc_dec` for all heap-typed bindings,
    /// except the variable named by `skip_var` (whose ownership transfers
    /// to the caller as the return value).
    ///
    /// Key invariant: "Scope cleanup emits dec for all heap-typed bindings
    /// EXCEPT the return value, consumed vars, and borrowed vars."
    ///
    /// Borrowed vars (e.g., pattern match field bindings) are skipped entirely —
    /// they share the owner's (scrutinee's) reference and the owner handles cleanup.
    ///
    /// ADT field cleanup happens inside the RC=0 dealloc path (via
    /// `emit_rc_dec_with_inline_drop_glue`), NOT as a separate step before dec.
    /// This prevents double-free when fields are independently referenced.
    pub(crate) fn pop_scope_with_cleanup(
        &mut self,
        skip_var: Option<&Symbol>,
    ) {
        if let Some(frame) = self.scope_stack.last() {
            // Collect bindings that need dec before we mutate state.
            let to_dec: Vec<(Symbol, Type, bool)> = frame
                .iter()
                .filter(|name| {
                    // Skip the return value variable.
                    if let Some(skip) = skip_var
                        && *name == skip {
                            return false;
                        }
                    // Skip consumed variables (ownership transferred to callee).
                    if self.consumed_vars.contains(*name) {
                        return false;
                    }
                    // Skip borrowed variables (owner handles cleanup).
                    if self.borrowed_vars.contains(*name) {
                        return false;
                    }
                    // Check if this binding is heap-typed.
                    if let Some(ty) = self.variable_types.get(*name) {
                        self.is_heap_type(ty)
                    } else {
                        false
                    }
                })
                .map(|name| {
                    let ty = self.variable_types.get(name).cloned()
                        .unwrap_or(Type::Int); // fallback, should not happen
                    let needs_guard = matches!(
                        signature_heap_category(&ty, Some(self.ctx.symbol_tables)),
                        HeapCategory::Mixed
                    );
                    (name.clone(), ty, needs_guard)
                })
                .collect();

            // Emit rc_dec for each heap-typed binding.
            let dealloc = self.ctx.dealloc_func_id;
            for (name, ty, needs_guard) in &to_dec {
                if let Some(var) = self.variables.get(name) {
                    let val = self.builder.use_var(*var);

                    // For closures (Type::Fn), use runtime-embedded drop glue.
                    // This handles both locally-created closures AND closures
                    // received as function parameters (where the static
                    // closure_drop_glue map has no entry).
                    if matches!(ty, Type::Fn(_, _)) {
                        self.emit_closure_dec_inline(val, dealloc);
                        continue;
                    }

                    // For Vec-typed bindings: must route through vec_drop to
                    // dec each element and free the data buffer; the generic
                    // rc_dec → dealloc path leaks both.
                    if let Some(elem_ty) =
                        crate::compiler::vec_codegen::vec_element_type(ty)
                    {
                        let elem_ty = elem_ty.clone();
                        let span = cranelisp_types::Span::new(0, 0);
                        let _ = self.emit_vec_aware_rc_dec(val, &elem_ty, span);
                        continue;
                    }

                    // For ADTs: emit RC dec with inline drop glue in the
                    // dealloc path. Field cleanup ONLY happens when RC
                    // reaches 0 (inside the free branch), not unconditionally.
                    // This prevents double-free when fields are independently
                    // referenced (e.g., extracted via pattern match).
                    self.emit_rc_dec_with_inline_drop_glue(val, ty, dealloc, *needs_guard);
                }
            }
        }

        // Now actually pop the scope (remove variables from maps).
        self.pop_scope();
    }

    /// If `body` is a direct variable reference to a name in the current scope
    /// frame, return that name. Used to skip rc_dec for the return value.
    pub(crate) fn return_var_in_scope(
        body: &MonoExpr,
        scope_frame: Option<&Vec<Symbol>>,
    ) -> Option<Symbol> {
        if let MonoExpr::Var { name, .. } = body
            && let Some(frame) = scope_frame
                && frame.contains(name) {
                    return Some(name.clone());
                }
        None
    }

    /// Check if a type is heap-allocated and needs RC management.
    pub(crate) fn is_heap_type(&self, ty: &Type) -> bool {
        matches!(
            signature_heap_category(ty, Some(self.ctx.symbol_tables)),
            HeapCategory::AlwaysHeap | HeapCategory::Mixed
        )
    }

    /// Derive a function parameter's type by finding a Var reference with the
    /// given name in the function body and reading its `inferred_type()`.
    ///
    /// Function parameters don't have their own `inferred_type`, but every
    /// Var reference to the parameter in the body does. We walk the body AST
    /// to find the first Var node matching the name.
    pub(crate) fn derive_param_type_from_body(body: &MonoExpr, name: &Symbol) -> Option<Type> {
        find_var_type_in_expr(body, name)
    }

    /// Check if a variable use is the last use (for ownership transfer).
    pub(crate) fn is_last_use(&self, name: &Symbol, span: Span) -> bool {
        if self.captured_vars.contains(name) {
            // Captured variables are NEVER eligible for last-use transfer.
            return false;
        }
        if self.borrowed_vars.contains(name) {
            // Borrowed variables (extracted from a match scrutinee's field)
            // do NOT own the value — the scrutinee still holds it. A
            // textually-last use of a borrowed var does not imply ownership
            // transfer, so Vec COW mutate-in-place on such a binding would
            // alias the scrutinee's field and cause a double-free once the
            // scrutinee's drop glue dec's the field independently. See
            // `design/backend/ring2-rc.md §3.1` (Decision 24 consuming
            // convention) and §5.5 (captured_vars rule — the borrowed_vars
            // rule is its structural twin: neither owns the value, so
            // neither may transfer ownership via last-use).
            // Regression: repro-slice2.cl — `(consume (Box [0]))` read len=0.
            return false;
        }
        self.last_uses
            .get(&(name.clone(), span))
            .copied()
            .unwrap_or(false)
    }

    /// Mark a variable as borrowed (skip scope-exit dec — owner handles cleanup).
    pub(crate) fn mark_borrowed(&mut self, name: &Symbol) {
        self.borrowed_vars.insert(name.clone());
    }
}
