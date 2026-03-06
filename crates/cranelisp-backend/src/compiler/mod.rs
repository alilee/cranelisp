// FnCompiler: per-function compilation context.
//
// Contains the FunctionBuilder and all state needed to compile one function.
// NOT a 21-parameter function -- addresses the prototype's primary structural debt.
//
// One dispatch method per Expr variant: compile_int_lit, compile_let, etc.

pub mod apply;
pub mod control_flow;
pub mod literals;
pub mod match_codegen;
pub mod vec_codegen;

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_jit::JITModule;
use cranelift_module::FuncId;

use cranelisp_types::{
    CompileMode, ConstructorInfo, CranelispError, Defn, Expr, HeapCategory, ModuleFullPath,
    ResolvedCall, Span, Symbol, Type, TypeDefInfo, TypeName,
};

use crate::heap;

// Variable allocation is per-FnCompiler instance via next_var field.

/// Named constant for the user trap code used when match exhaustion occurs.
pub const MATCH_EXHAUSTION_TRAP: u8 = 1;

/// Shared immutable context for compilation, bundling references that
/// are threaded through from `compile_body` to all expression compilers.
///
/// All fields are references or `Copy` types, so the struct is `Clone`+`Copy`.
/// This avoids verbose field-by-field copies when constructing inner compilers
/// (e.g., for lambda bodies).
#[derive(Clone, Copy)]
pub struct CompileContext<'a> {
    /// Method resolutions from the typechecker.
    pub method_resolutions: &'a HashMap<Span, ResolvedCall>,
    /// Expression types from the typechecker.
    pub expr_types: &'a HashMap<Span, Type>,
    /// Function IDs for direct calls (Batch mode).
    pub func_ids: &'a HashMap<Symbol, FuncId>,
    /// Function parameter counts, for generating closure wrappers.
    pub func_arities: &'a HashMap<Symbol, usize>,
    /// Compilation mode (Batch or Interactive).
    pub mode: CompileMode,
    /// Type definitions for ADT codegen.
    pub type_defs: &'a HashMap<TypeName, TypeDefInfo>,
    /// Constructor name -> parent type name mapping.
    pub constructor_to_type: &'a HashMap<Symbol, TypeName>,
    /// GOT slot assignments for each function name (Interactive mode only).
    /// In Batch/Release mode this is None; calls use direct `call` instructions.
    pub got_slots: Option<&'a HashMap<Symbol, usize>>,
    /// GOT base pointer as a raw i64 value (Interactive mode only).
    /// This is the address of the GOT table, baked into compiled IR as an iconst.
    pub got_base_ptr: Option<i64>,

    /// Cross-module GOT references for imported functions (Interactive mode only).
    ///
    /// Maps `(defining_module, function_name)` to `(got_base_ptr, slot_index)` so
    /// that calls to imported functions can use the defining module's GOT table
    /// instead of the caller's local GOT. This enables cross-module calls in
    /// Interactive mode without copying function pointers between GOT tables.
    ///
    /// In Batch/Release mode this is None; cross-module calls use Cranelift linking.
    pub cross_module_got: Option<&'a HashMap<(ModuleFullPath, Symbol), (i64, usize)>>,

    // --- Ring 1 intrinsic FuncIds ---
    /// FuncId for runtime/alloc. None in Ring 0 (no heap).
    pub alloc_func_id: Option<FuncId>,
    /// FuncId for runtime/dealloc. None in Ring 0 (no heap).
    pub dealloc_func_id: Option<FuncId>,
    /// FuncId for runtime/alloc_string. None in Ring 0 (no strings).
    pub alloc_string_func_id: Option<FuncId>,
    /// FuncId for runtime/panic. None in Ring 0 (uses trap instead).
    pub panic_func_id: Option<FuncId>,
    /// FuncId for runtime/vec_new. None in Ring 0 (no Vecs).
    pub vec_new_func_id: Option<FuncId>,
    /// FuncId for runtime/vec_drop. None in Ring 0 (no Vecs).
    pub vec_drop_func_id: Option<FuncId>,
}

/// Match-arm-invariant data bundled to reduce parameter counts in
/// `compile_constructor_pattern`.
pub struct MatchContext {
    /// The compiled scrutinee value.
    pub scrut_val: Value,
    /// The span of the scrutinee expression (for type lookup in expr_types).
    pub scrut_span: Span,
    /// The block to branch to if this arm does not match.
    pub next_block: Block,
    /// The merge block where all arms converge.
    pub merge_block: Block,
    /// The saved tail-position flag from before the match.
    pub saved_tail: bool,
}

/// Per-function compilation context.
pub struct FnCompiler<'a> {
    /// Cranelift function builder.
    pub builder: FunctionBuilder<'a>,
    /// Reference to the JIT module for declaring functions.
    pub module: &'a mut JITModule,
    /// Local variable bindings (name -> Cranelift Variable).
    pub(crate) variables: HashMap<Symbol, Variable>,
    /// Scope stack: each frame is a list of variable names introduced.
    pub(crate) scope_stack: Vec<Vec<Symbol>>,
    /// Shared immutable compilation context.
    pub(crate) ctx: CompileContext<'a>,

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
    #[allow(dead_code)]
    pub(crate) variable_types: HashMap<Symbol, Type>,
    /// Last-use information: (var_name, span) -> is_last_use.
    #[allow(dead_code)]
    pub(crate) last_uses: HashMap<(Symbol, Span), bool>,
    /// Set of variables whose ownership has been transferred (consumed).
    #[allow(dead_code)]
    pub(crate) consumed_vars: std::collections::HashSet<Symbol>,
    /// Captured variable names (variables closed over by a lambda).
    /// These are NEVER eligible for last-use transfer.
    #[allow(dead_code)]
    pub(crate) captured_vars: std::collections::HashSet<Symbol>,
}

impl<'a> FnCompiler<'a> {
    /// Create an inner `FnCompiler` for lambda bodies, continuations,
    /// or (future) drop glue. This is the single construction point for
    /// inner compilers (ring1-checklist section 5.9).
    ///
    /// TCO state is disabled for inner functions (no self-call detection,
    /// no tail loop). The scope and variable maps start fresh.
    pub(crate) fn inner(
        builder: FunctionBuilder<'a>,
        module: &'a mut JITModule,
        ctx: CompileContext<'a>,
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
            captured_vars: std::collections::HashSet::new(),
        }
    }

    /// Compile a function definition body into Cranelift IR.
    ///
    /// This is the main entry point called by Jit::compile_defn.
    /// Creates the entry block, loop header (for TCO), binds parameters,
    /// compiles the body, and finalizes.
    pub fn compile_body(
        defn: &Defn,
        func: &mut cranelift::codegen::ir::Function,
        func_ctx: &mut FunctionBuilderContext,
        module: &'a mut JITModule,
        ctx: CompileContext<'a>,
    ) -> Result<(), CranelispError> {
        let mut builder = FunctionBuilder::new(func, func_ctx);

        // Entry block: receives function parameters.
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        // Create loop header block for TCO: one i64 block param per function param.
        let loop_header = builder.create_block();
        for _ in &defn.params {
            builder.append_block_param(loop_header, types::I64);
        }

        // Jump from entry to loop header with initial parameter values.
        let entry_params: Vec<Value> = builder.block_params(entry_block).to_vec();
        builder.ins().jump(loop_header, &entry_params);

        // Switch to loop header. Do NOT seal it yet -- back-edges from tail calls
        // will be added during body compilation.
        builder.switch_to_block(loop_header);

        // Compute last-use info for the body.
        let last_uses = heap::compute_last_uses(&defn.body);

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
            fn_param_count: defn.params.len(),
            variable_types: HashMap::new(),
            last_uses,
            consumed_vars: std::collections::HashSet::new(),
            captured_vars: std::collections::HashSet::new(),
        };

        // Bind function parameters from loop header block params (not entry block).
        for (i, param_name) in defn.params.iter().enumerate() {
            let val = compiler.builder.block_params(loop_header)[i];
            let var = compiler.fresh_variable();
            compiler.builder.declare_var(var, types::I64);
            compiler.builder.def_var(var, val);
            compiler.variables.insert(param_name.clone(), var);
            compiler
                .scope_stack
                .last_mut()
                .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                .push(param_name.clone());
        }

        // Compile the function body.
        let result = compiler.compile_expr(&defn.body)?;

        // Return the result.
        compiler.builder.ins().return_(&[result]);

        // Seal all blocks (including loop_header which may have back-edges).
        compiler.builder.seal_all_blocks();
        compiler.builder.finalize();

        Ok(())
    }

    // --- Expression dispatch ---

    /// Compile an expression, dispatching to the appropriate handler.
    pub fn compile_expr(&mut self, expr: &Expr) -> Result<Value, CranelispError> {
        match expr {
            Expr::IntLit { value, .. } => self.compile_int_lit(*value),
            Expr::FloatLit { value, .. } => self.compile_float_lit(*value),
            Expr::BoolLit { value, .. } => self.compile_bool_lit(*value),
            Expr::StringLit { value, span } => self.compile_string_lit(value, *span),
            Expr::Var { name, span } => self.compile_var(name, *span),
            Expr::Let {
                bindings,
                body,
                span,
            } => self.compile_let(bindings, body, *span),
            Expr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.compile_if(cond, then_branch, else_branch),
            Expr::Lambda {
                params, body, span, ..
            } => self.compile_lambda(params, body, *span),
            Expr::Apply {
                callee,
                args,
                span,
            } => self.compile_apply(callee, args, *span),
            Expr::Match {
                scrutinee,
                arms,
                span,
                ..
            } => self.compile_match(scrutinee, arms, *span),
            Expr::Annotate { expr, .. } => self.compile_expr(expr),
            Expr::VecLit { elements, span } => self.compile_vec_lit(elements, *span),
            Expr::Trace { span, .. } => Err(CranelispError::CodegenError {
                message: "trace not supported until Ring 4".into(),
                span: *span,
            }),
            Expr::RunTests { span, .. } => Err(CranelispError::CodegenError {
                message: "run-tests not supported until Ring 4".into(),
                span: *span,
            }),
        }
    }

    // --- Variable allocation ---

    /// Allocate a fresh Cranelift Variable index.
    pub(crate) fn fresh_variable(&mut self) -> Variable {
        let idx = self.next_var;
        self.next_var += 1;
        Variable::new(idx as usize)
    }

    // --- Scope management ---

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
    /// EXCEPT the return value."
    ///
    /// For ADTs with AlwaysHeap fields, inline drop glue is emitted:
    /// each heap-typed field is dec'd before the ADT itself is freed.
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
                    if let Some(skip) = skip_var {
                        if *name == skip {
                            return false;
                        }
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
                        HeapCategory::classify(&ty, Some(self.ctx.type_defs)),
                        HeapCategory::Mixed
                    );
                    (name.clone(), ty, needs_guard)
                })
                .collect();

            // Emit rc_dec for each heap-typed binding.
            if let Some(dealloc) = self.ctx.dealloc_func_id {
                for (name, ty, needs_guard) in &to_dec {
                    if let Some(var) = self.variables.get(name) {
                        let val = self.builder.use_var(*var);

                        // For ADTs with known AlwaysHeap fields, emit inline
                        // drop glue: dec each heap-typed field before dec'ing
                        // the ADT itself. This prevents field value leaks.
                        // For Mixed ADTs, the field dec is guarded by a
                        // heap-pointer check (skip if value is a bare tag).
                        self.emit_inline_drop_glue(val, ty, dealloc, *needs_guard);

                        if *needs_guard {
                            heap::emit_rc_dec_guarded(
                                &mut self.builder,
                                self.module,
                                val,
                                dealloc,
                                None,
                                true, // Guard nullary tags
                            );
                        } else {
                            heap::emit_rc_dec(
                                &mut self.builder,
                                self.module,
                                val,
                                dealloc,
                                None,
                            );
                        }
                    }
                }
            }
        }

        // Now actually pop the scope (remove variables from maps).
        self.pop_scope();
    }

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
        use crate::heap::HeapAdt;

        let type_name = match ty {
            Type::ADT(name, _) => name,
            _ => return, // Not an ADT; nothing to do.
        };

        let type_def = match self.ctx.type_defs.get(type_name) {
            Some(td) => td.clone(),
            None => return,
        };

        // Get concrete type args from the variable's type.
        let concrete_args = match ty {
            Type::ADT(_, args) => args.clone(),
            _ => return,
        };

        // Build substitution from Var ids to concrete types.
        let mut unique_var_ids: Vec<cranelisp_types::TypeId> = Vec::new();
        for c in &type_def.constructors {
            for field in &c.fields {
                collect_var_ids_from_type(&field.ty, &mut unique_var_ids);
            }
        }
        let subst: std::collections::HashMap<cranelisp_types::TypeId, Type> = unique_var_ids
            .iter()
            .zip(concrete_args.iter())
            .map(|(&id, arg)| (id, arg.clone()))
            .collect();

        // Collect data constructors (those with fields).
        let data_ctors: Vec<_> = type_def.constructors.iter()
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
                    HeapCategory::classify(&resolved, Some(self.ctx.type_defs)),
                    HeapCategory::AlwaysHeap | HeapCategory::Mixed
                )
            })
        });

        if !has_heap_fields {
            return; // No heap fields to drop.
        }

        // For Mixed ADTs, guard the field dec with a heap-pointer check.
        let cont_block = if is_mixed {
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
            Some(cont)
        } else {
            None
        };

        // Emit field decs for each data constructor. For a single data
        // constructor, dec fields directly. For multiple data constructors,
        // emit tag-based dispatch (branch chain like match codegen).
        if data_ctors.len() == 1 {
            let ctor = data_ctors[0];
            self.emit_field_decs(adt_val, ctor, &subst, dealloc);
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

                self.emit_field_decs(adt_val, ctor, &subst, dealloc);
                self.builder.ins().jump(done_block, &[]);

                if idx + 1 < data_ctors.len() {
                    self.builder.switch_to_block(next_block);
                    self.builder.seal_block(next_block);
                }
            }

            self.builder.switch_to_block(done_block);
            self.builder.seal_block(done_block);
        }

        // Jump to continuation for Mixed guard.
        if let Some(cont) = cont_block {
            self.builder.ins().jump(cont, &[]);
            self.builder.switch_to_block(cont);
            self.builder.seal_block(cont);
        }
    }

    /// Emit rc_dec for each heap-typed field of a single constructor.
    ///
    /// Used by `emit_inline_drop_glue` for both the single-constructor case
    /// and within each branch of the multi-constructor tag dispatch.
    fn emit_field_decs(
        &mut self,
        adt_val: Value,
        ctor: &ConstructorInfo,
        subst: &std::collections::HashMap<cranelisp_types::TypeId, Type>,
        dealloc: FuncId,
    ) {
        use crate::heap::HeapAdt;

        for (i, field) in ctor.fields.iter().enumerate() {
            let resolved_ty = substitute_type_inline(&field.ty, subst);
            let category = HeapCategory::classify(&resolved_ty, Some(self.ctx.type_defs));
            match category {
                HeapCategory::AlwaysHeap => {
                    let field_val = heap::heap_load(
                        &mut self.builder,
                        adt_val,
                        HeapAdt::field_offset(i),
                    );
                    heap::emit_rc_dec(
                        &mut self.builder,
                        self.module,
                        field_val,
                        dealloc,
                        None,
                    );
                }
                HeapCategory::Mixed => {
                    let field_val = heap::heap_load(
                        &mut self.builder,
                        adt_val,
                        HeapAdt::field_offset(i),
                    );
                    heap::emit_rc_dec_guarded(
                        &mut self.builder,
                        self.module,
                        field_val,
                        dealloc,
                        None,
                        true,
                    );
                }
                HeapCategory::NeverHeap => {}
            }
        }
    }

    // --- Return value identification ---

    /// If `body` is a direct variable reference to a name in the current scope
    /// frame, return that name. Used to skip rc_dec for the return value.
    pub(crate) fn return_var_in_scope(
        body: &Expr,
        scope_frame: Option<&Vec<Symbol>>,
    ) -> Option<Symbol> {
        if let Expr::Var { name, .. } = body {
            if let Some(frame) = scope_frame {
                if frame.contains(name) {
                    return Some(name.clone());
                }
            }
        }
        None
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
        body: &Expr,
    ) {
        if skip_var.is_some() {
            return; // The skip_var mechanism already protects the return value.
        }
        if let Some(ty) = self.ctx.expr_types.get(&body.span()) {
            let category = HeapCategory::classify(ty, Some(self.ctx.type_defs));
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_inc(&mut self.builder, body_val);
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_inc_guarded(&mut self.builder, body_val);
                }
                HeapCategory::NeverHeap => {}
            }
        }
    }

    // --- Heap helpers (scaffolding for RC emission in Ring 2) ---

    /// Check if a type is heap-allocated and needs RC management.
    pub(crate) fn is_heap_type(&self, ty: &Type) -> bool {
        matches!(
            HeapCategory::classify(ty, Some(self.ctx.type_defs)),
            HeapCategory::AlwaysHeap | HeapCategory::Mixed
        )
    }

    /// Look up the type of an expression from the typechecker's expr_types.
    #[allow(dead_code)]
    pub(crate) fn expr_type(&self, span: Span) -> Option<&Type> {
        self.ctx.expr_types.get(&span)
    }

    /// Check if a variable use is the last use (for ownership transfer).
    #[allow(dead_code)]
    pub(crate) fn is_last_use(&self, name: &Symbol, span: Span) -> bool {
        if self.captured_vars.contains(name) {
            // Captured variables are NEVER eligible for last-use transfer.
            return false;
        }
        self.last_uses
            .get(&(name.clone(), span))
            .copied()
            .unwrap_or(false)
    }
}

// --- Free helper functions for type variable resolution ---

/// Collect all unique Var ids from a type, in order of first appearance.
pub(crate) fn collect_var_ids_from_type(ty: &Type, ids: &mut Vec<cranelisp_types::TypeId>) {
    match ty {
        Type::Var(id) => {
            if !ids.contains(id) {
                ids.push(*id);
            }
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

#[cfg(test)]
mod tests {
    // FnCompiler is tested via the public compile_and_run_expr API in lib.rs
    // and through the Jit::compile_defn path. Direct unit testing of FnCompiler
    // requires constructing a full Cranelift context, which is covered by
    // the integration tests.
}
