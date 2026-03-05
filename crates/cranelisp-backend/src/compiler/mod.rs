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
    CompileMode, CranelispError, Defn, Expr, HeapCategory, ResolvedCall, Span, Symbol, Type,
    TypeDefInfo, TypeName,
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

    // --- Heap helpers (scaffolding for RC emission in Ring 2) ---

    /// Check if a type is heap-allocated and needs RC management.
    #[allow(dead_code)]
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

#[cfg(test)]
mod tests {
    // FnCompiler is tested via the public compile_and_run_expr API in lib.rs
    // and through the Jit::compile_defn path. Direct unit testing of FnCompiler
    // requires constructing a full Cranelift context, which is covered by
    // the integration tests.
}
