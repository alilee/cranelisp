use std::collections::HashSet;
use std::sync::LazyLock;

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;

use cranelift_module::Module;

use crate::ast::Expr;
use crate::captures;
use crate::error::CranelispError;
use crate::names::resolve_bare_name;

use super::FnCompiler;

/// Whether lenient evaluation (automatic sparking) is disabled via env var.
static LENIENT_DISABLED: LazyLock<bool> =
    LazyLock::new(|| std::env::var("CRANELISP_NO_LENIENT").map_or(false, |v| v == "1"));

/// Known-cheap builtins that are not worth sparking.
const CHEAP_BUILTINS: &[&str] = &[
    "+", "-", "*", "/", "=", "<", ">", "<=", ">=", "not", "and", "or",
];

/// Check if an expression is worth sparking (non-trivial function call).
fn is_worth_sparking(expr: &Expr) -> bool {
    match expr {
        Expr::Apply { callee, .. } => {
            // Only spark if the callee is not a known-cheap builtin
            if let Expr::Var { name, .. } = callee.as_ref() {
                !CHEAP_BUILTINS.contains(&name.as_str())
            } else {
                true // Non-var callees (e.g. lambda applications) are worth sparking
            }
        }
        _ => false,
    }
}

/// Find binding indices that are independent (no dependency on earlier bindings)
/// and non-trivial (worth sparking). Returns empty vec if fewer than 2 qualify.
fn find_sparkable_bindings(
    bindings: &[(String, Expr)],
    globals: &HashSet<String>,
) -> Vec<usize> {
    let mut bound_names: HashSet<String> = HashSet::new();
    let mut sparkable = Vec::new();

    for (i, (name, val_expr)) in bindings.iter().enumerate() {
        let fv = captures::free_vars(val_expr, globals);
        let depends_on_earlier = fv.iter().any(|v| bound_names.contains(v));

        if !depends_on_earlier && is_worth_sparking(val_expr) {
            sparkable.push(i);
        }

        bound_names.insert(name.clone());
    }

    if sparkable.len() < 2 {
        Vec::new()
    } else {
        sparkable
    }
}

impl<'a, M: Module> FnCompiler<'a, M> {
    pub(crate) fn compile_expr(&mut self, expr: &Expr) -> Result<Value, CranelispError> {
        match expr {
            Expr::IntLit { value, .. } => Ok(self.builder.ins().iconst(types::I64, *value)),
            Expr::FloatLit { value, .. } => {
                let bits = value.to_bits() as i64;
                Ok(self.builder.ins().iconst(types::I64, bits))
            }
            Expr::BoolLit { value, .. } => {
                let val = if *value { 1i64 } else { 0i64 };
                Ok(self.builder.ins().iconst(types::I64, val))
            }
            Expr::StringLit { value, span } => {
                let bytes = value.as_bytes();
                let size = (8 + bytes.len()) as i64;
                let ptr = self.compile_alloc(size, *span)?;
                let len_val = self.builder.ins().iconst(types::I64, bytes.len() as i64);
                self.builder
                    .ins()
                    .store(MemFlags::trusted(), len_val, ptr, 0);
                for (i, &byte) in bytes.iter().enumerate() {
                    let byte_val = self.builder.ins().iconst(types::I64, byte as i64);
                    self.builder
                        .ins()
                        .istore8(MemFlags::trusted(), byte_val, ptr, (8 + i) as i32);
                }
                Ok(ptr)
            }
            Expr::Var { name, span } => {
                let bare = resolve_bare_name(name);
                // Local variable takes priority
                if let Some(var) = self.variables.get(bare) {
                    return Ok(self.builder.use_var(*var));
                }
                // Nullary constructor → return tag as i64
                if let Some(tag) = self.nullary_constructor_tag(bare) {
                    return Ok(self.builder.ins().iconst(types::I64, tag as i64));
                }
                // Data constructor used as value → wrap as closure
                if let Some(ctor_info) = self.data_constructor_info(bare) {
                    let field_count = ctor_info.fields.len();
                    let tag = ctor_info.tag;
                    return self.compile_constructor_as_closure(bare, tag, field_count, *span);
                }
                // Accessor used as value → wrap as closure
                if let Some(acc) = self.accessor_info(bare) {
                    return self.compile_accessor_as_closure(bare, &acc, *span);
                }
                // Top-level function used as a value → wrap as closure
                if self.is_known_function(bare) {
                    return self.compile_func_as_closure(bare, *span);
                }
                // Builtin used as a value → wrap as closure (resolution-based)
                if let Some(crate::typechecker::ResolvedCall::BuiltinFn(fq)) =
                    self.method_resolutions.get(span)
                {
                    if let Some(cm) = self.modules.get(&fq.module) {
                        if let Some(crate::module::ModuleEntry::Def {
                            kind:
                                crate::module::DefKind::Primitive {
                                    func_id: Some(fid), ..
                                },
                            param_names,
                            ..
                        }) = cm.get(fq.symbol.as_ref())
                        {
                            return self.compile_builtin_as_closure(
                                *fid,
                                param_names.len(),
                                *span,
                            );
                        }
                    }
                }
                // Operator symbol used as a value → wrap as closure
                if matches!(bare, "+" | "-" | "*" | "/" | "=" | "<" | ">" | "<=" | ">=") {
                    if let Some(&func_id) = self.builtin_methods.get(bare) {
                        return self.compile_builtin_as_closure(func_id, 2, *span);
                    }
                }
                Err(CranelispError::CodegenError {
                    message: format!("undefined variable: {}", name),
                    span: *span,
                })
            }
            Expr::Let { bindings, body, span } => {
                // Check for lenient evaluation opportunity.
                // Disabled inside `trace` bodies to ensure the full call tree is traced.
                let sparkable = if *LENIENT_DISABLED || self.in_trace_body {
                    Vec::new()
                } else {
                    find_sparkable_bindings(bindings, &self.globals)
                };

                if sparkable.is_empty() {
                    // Sequential path (unchanged)
                    self.compile_let_sequential(bindings, body)
                } else {
                    // Lenient path: spark independent bindings via IVars
                    self.compile_let_lenient(bindings, body, &sparkable, *span)
                }
            }
            Expr::If {
                cond,
                then_branch,
                else_branch,
                span: _,
            } => {
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

                self.builder.switch_to_block(then_block);
                self.builder.seal_block(then_block);
                self.in_tail_position = saved_tail;

                self.branch_depth += 1;
                let then_val = self.compile_expr(then_branch)?;
                self.branch_depth -= 1;

                self.builder
                    .ins()
                    .jump(merge_block, &[BlockArg::Value(then_val)]);

                self.builder.switch_to_block(else_block);
                self.builder.seal_block(else_block);
                self.in_tail_position = saved_tail;

                self.branch_depth += 1;
                let else_val = self.compile_expr(else_branch)?;
                self.branch_depth -= 1;

                self.builder
                    .ins()
                    .jump(merge_block, &[BlockArg::Value(else_val)]);

                self.builder.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);
                self.in_tail_position = false;
                let result = self.builder.block_params(merge_block)[0];
                Ok(result)
            }
            Expr::Lambda {
                params, body, span, ..
            } => {
                let saved_tail = self.in_tail_position;
                self.in_tail_position = false;
                let result = self.compile_lambda(params, body, expr, *span)?;
                self.in_tail_position = saved_tail;
                Ok(result)
            }
            Expr::Apply {
                callee, args, span, ..
            } => self.compile_apply(callee, args, span),
            Expr::Match {
                scrutinee,
                arms,
                span,
                ..
            } => self.compile_match(scrutinee, arms, *span),
            Expr::VecLit { elements, span, .. } => self.compile_vec_lit(elements, *span),
            Expr::Annotate { expr: inner, .. } => {
                // Inherits tail position
                self.compile_expr(inner)
            }
            Expr::ParLet {
                bindings,
                body,
                span,
            } => self.compile_par_let(bindings, body, *span),
            Expr::ParBind {
                bindings,
                body,
                span,
            } => self.compile_par_bind(bindings, body, *span),
            Expr::Trace {
                modules,
                body,
                span,
            } => self.compile_trace(modules, body, *span),
            Expr::RunTests {
                modules,
                init,
                pass_fn,
                fail_fn,
                span,
            } => self.compile_run_tests(modules, init, pass_fn, fail_fn, *span),
        }
    }

    /// Compile a Vec literal: allocate header (24 bytes) + data buffer (n * 8 bytes),
    /// store len, cap, data_ptr in header, store each element in data buffer.
    pub(crate) fn compile_vec_lit(
        &mut self,
        elements: &[Expr],
        span: crate::error::Span,
    ) -> Result<Value, CranelispError> {
        // Compile each element expression
        let mut elem_vals = Vec::new();
        for elem in elements {
            let val = self.compile_expr(elem)?;
            elem_vals.push(val);
        }

        let n = elements.len();

        // Allocate Vec header: [len: i64, cap: i64, data_ptr: i64] = 24 bytes
        let header_ptr = self.compile_alloc(24, span)?;

        // Allocate data buffer (or null for empty)
        let data_ptr = if n > 0 {
            self.compile_alloc((n * 8) as i64, span)?
        } else {
            self.builder.ins().iconst(types::I64, 0)
        };

        // Store len
        let len_val = self.builder.ins().iconst(types::I64, n as i64);
        self.builder
            .ins()
            .store(MemFlags::trusted(), len_val, header_ptr, 0);

        // Store cap (= len for literals)
        self.builder
            .ins()
            .store(MemFlags::trusted(), len_val, header_ptr, 8);

        // Store data_ptr
        self.builder
            .ins()
            .store(MemFlags::trusted(), data_ptr, header_ptr, 16);

        // Store each element in data buffer
        for (i, val) in elem_vals.iter().enumerate() {
            self.builder
                .ins()
                .store(MemFlags::trusted(), *val, data_ptr, (i * 8) as i32);
        }

        Ok(header_ptr)
    }

    /// Compile par-let: wrap each binding expression in a zero-arg thunk (closure),
    /// call cranelisp_par_eval to evaluate them in parallel, then load results.
    pub(crate) fn compile_par_let(
        &mut self,
        bindings: &[(String, Expr)],
        body: &Expr,
        span: crate::error::Span,
    ) -> Result<Value, CranelispError> {
        let saved_tail = self.in_tail_position;
        self.push_scope();
        self.in_tail_position = false;

        let n = bindings.len();

        // Compile each binding as a zero-arg thunk (closure)
        let mut thunk_ptrs = Vec::with_capacity(n);
        for (_name, val_expr) in bindings {
            // Wrap in a synthetic lambda: (fn [] val_expr)
            let thunk_expr = Expr::Lambda {
                params: vec![],
                param_annotations: vec![],
                body: Box::new(val_expr.clone()),
                span: val_expr.span(),
            };
            let thunk_ptr = self.compile_expr(&thunk_expr)?;
            thunk_ptrs.push(thunk_ptr);
        }

        // Allocate heap array of thunk pointers
        let array_size = (n * 8) as i64;
        let thunks_array = self.compile_alloc(array_size, span)?;
        for (i, &thunk) in thunk_ptrs.iter().enumerate() {
            self.builder
                .ins()
                .store(MemFlags::trusted(), thunk, thunks_array, (i * 8) as i32);
        }

        // Call cranelisp_par_eval(thunks_array, count) -> results_ptr
        let par_eval_ref = self
            .module
            .declare_func_in_func(self.par_eval_func_id, self.builder.func);
        let count_val = self.builder.ins().iconst(types::I64, n as i64);
        let call = self
            .builder
            .ins()
            .call(par_eval_ref, &[thunks_array, count_val]);
        let results_ptr = self.builder.inst_results(call)[0];

        // Load each result and bind to variable
        for (i, (name, val_expr)) in bindings.iter().enumerate() {
            let result_val = self.builder.ins().load(
                types::I64,
                MemFlags::trusted(),
                results_ptr,
                (i * 8) as i32,
            );
            let var = self.fresh_var(types::I64);
            self.builder.def_var(var, result_val);
            self.variables.insert(name.clone(), var);

            // Track variable type for RC
            if let Some(ty) = self.expr_types.get(&val_expr.span()) {
                self.variable_types.insert(name.clone(), ty.clone());
                if ty.is_heap_type() {
                    self.track_binding(name.clone(), var, ty.clone());
                }
            }
        }

        self.in_tail_position = saved_tail;
        let result = self.compile_expr(body)?;
        self.in_tail_position = false;
        self.pop_scope_for_value(result);
        Ok(result)
    }

    /// Compile par-bind!: compile IO expressions, allocate Par node,
    /// wrap body as continuation closure, allocate Bind node.
    pub(crate) fn compile_par_bind(
        &mut self,
        bindings: &[(String, Expr)],
        body: &Expr,
        span: crate::error::Span,
    ) -> Result<Value, CranelispError> {
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;

        let n = bindings.len();

        // Compile all IO binding expressions
        let mut io_vals = Vec::with_capacity(n);
        for (_name, val_expr) in bindings {
            let io_val = self.compile_expr(val_expr)?;
            io_vals.push(io_val);
        }

        // Allocate Par node: [tag=3, count, io0, io1, ...]
        let par_size = ((2 + n) * 8) as i64;
        let par_ptr = self.compile_alloc(par_size, span)?;
        let tag_val = self.builder.ins().iconst(types::I64, 3); // IO_TAG_PAR
        self.builder
            .ins()
            .store(MemFlags::trusted(), tag_val, par_ptr, 0);
        let count_val = self.builder.ins().iconst(types::I64, n as i64);
        self.builder
            .ins()
            .store(MemFlags::trusted(), count_val, par_ptr, 8);
        for (i, &io_val) in io_vals.iter().enumerate() {
            self.builder.ins().store(
                MemFlags::trusted(),
                io_val,
                par_ptr,
                ((2 + i) * 8) as i32,
            );
            // Inc RC on each IO value since Par node holds a reference
            self.emit_inc_inline(io_val);
        }

        // Build continuation closure that unpacks results and evaluates body
        // The continuation takes (env_ptr, results_ptr) -> IO result
        let cont_ptr = self.compile_par_bind_continuation(bindings, body, span)?;

        // Allocate Bind node: [tag=2, par_ptr, cont_ptr]
        let bind_ptr = self.compile_alloc(24, span)?;
        let bind_tag = self.builder.ins().iconst(types::I64, 2); // IO_TAG_BIND
        self.builder
            .ins()
            .store(MemFlags::trusted(), bind_tag, bind_ptr, 0);
        self.builder
            .ins()
            .store(MemFlags::trusted(), par_ptr, bind_ptr, 8);
        self.builder
            .ins()
            .store(MemFlags::trusted(), cont_ptr, bind_ptr, 16);
        // Inc both: Bind node holds references
        self.emit_inc_inline(par_ptr);
        self.emit_inc_inline(cont_ptr);

        self.in_tail_position = saved_tail;
        Ok(bind_ptr)
    }

    /// Compile the continuation closure for par-bind!.
    /// Signature: (env_ptr: i64, results_ptr: i64) -> i64
    /// Loads N results from results_ptr, binds to names, compiles body.
    fn compile_par_bind_continuation(
        &mut self,
        bindings: &[(String, Expr)],
        body: &Expr,
        span: crate::error::Span,
    ) -> Result<Value, CranelispError> {
        use cranelift::codegen::ir::Function;
        use std::collections::HashMap;

        let binding_names: std::collections::HashSet<String> =
            bindings.iter().map(|(n, _)| n.clone()).collect();

        // Compute captures: free vars of body minus binding names.
        // Use empty globals so parameter names don't collide with global function names.
        let empty_globals = std::collections::HashSet::new();
        let body_fv = crate::captures::free_vars(body, &empty_globals);
        let mut capture_names: Vec<String> = body_fv
            .into_iter()
            .filter(|v| !binding_names.contains(v) && self.variables.contains_key(v))
            .collect();
        // Sort for deterministic closure layout (important for cached .o files)
        capture_names.sort();

        // Build signature: (env_ptr: i64, results_ptr: i64) -> i64
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // env_ptr
        sig.params.push(AbiParam::new(types::I64)); // results_ptr
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self.module.declare_anonymous_function(&sig).map_err(|e| {
            CranelispError::CodegenError {
                message: format!("failed to declare par-bind! continuation: {}", e),
                span,
            }
        })?;

        // Compile continuation body in a fresh Function
        {
            let mut cont_func = Function::with_name_signature(
                cranelift::codegen::ir::UserFuncName::user(0, func_id.as_u32()),
                sig.clone(),
            );
            let mut cont_func_ctx = FunctionBuilderContext::new();
            let mut cont_builder = FunctionBuilder::new(&mut cont_func, &mut cont_func_ctx);

            let entry_block = cont_builder.create_block();
            cont_builder.append_block_params_for_function_params(entry_block);
            cont_builder.switch_to_block(entry_block);
            cont_builder.seal_block(entry_block);

            let inner_call_mode = match &self.call_mode {
                super::CallMode::Direct { func_ids } => super::CallMode::Direct {
                    func_ids: func_ids.clone(),
                },
                super::CallMode::Indirect { fn_slots } => {
                    super::CallMode::Indirect { fn_slots }
                }
            };

            let mut inner = super::FnCompiler {
                builder: cont_builder,
                module: self.module,
                variables: HashMap::new(),
                call_mode: inner_call_mode,
                alloc_func_id: self.alloc_func_id,
                globals: self.globals.clone(),
                liveness_globals: self.liveness_globals.clone(),
                method_resolutions: self.method_resolutions,
                fn_specific_resolutions: self.fn_specific_resolutions,
                builtin_methods: self.builtin_methods,
                modules: self.modules,
                type_defs: self.type_defs,
                constructor_to_type: self.constructor_to_type,
                panic_func_id: self.panic_func_id,
                expr_types: self.expr_types,
                free_func_id: self.free_func_id,
                par_eval_func_id: self.par_eval_func_id,
                ivar_create_func_id: self.ivar_create_func_id,
                ivar_spark_func_id: self.ivar_spark_func_id,
                ivar_force_func_id: self.ivar_force_func_id,
                variable_types: HashMap::new(),
                scope_stack: vec![vec![]],
                drop_fn_cache: HashMap::new(),
                vec_elem_inc_cache: HashMap::new(),
                current_fn_name: None,
                tail_loop_block: None,
                in_tail_position: false,
                fn_param_count: 0,
                last_uses: crate::liveness::compute_last_uses(body, &self.liveness_globals),
                consumed_vars: std::collections::HashSet::new(),
                branch_depth: 0,
                unique_vars: std::collections::HashSet::new(),
                borrowed_vars: std::collections::HashSet::new(),
                borrowed_temps: std::collections::HashSet::new(),
                in_trace_body: self.in_trace_body,
            };

            let block_params: Vec<Value> = inner.builder.block_params(entry_block).to_vec();
            let env_ptr_val = block_params[0];
            let results_ptr_val = block_params[1];

            // Load captures from env_ptr
            // Layout: [code_ptr, drop_ptr, cap0, cap1, ...]
            for (i, cap_name) in capture_names.iter().enumerate() {
                let offset = ((i + 2) * 8) as i32;
                let cap_val = inner.builder.ins().load(
                    types::I64,
                    MemFlags::trusted(),
                    env_ptr_val,
                    offset,
                );
                let var = inner.fresh_var(types::I64);
                inner.builder.def_var(var, cap_val);
                inner.variables.insert(cap_name.clone(), var);
            }

            // Load N results from results_ptr and bind to names
            // Note: expr_types has IO T for the binding expression, but the trampoline
            // unwraps it, so the actual value type is the inner T (not IO T).
            for (i, (name, val_expr)) in bindings.iter().enumerate() {
                let result_val = inner.builder.ins().load(
                    types::I64,
                    MemFlags::trusted(),
                    results_ptr_val,
                    (i * 8) as i32,
                );
                let var = inner.fresh_var(types::I64);
                inner.builder.def_var(var, result_val);
                inner.variables.insert(name.clone(), var);

                // Track type for RC — unwrap IO T to get inner T
                if let Some(ty) = inner.expr_types.get(&val_expr.span()) {
                    let inner_ty = match ty {
                        crate::types::Type::ADT(name, args) if name == "IO" && !args.is_empty() => {
                            args[0].clone()
                        }
                        _ => ty.clone(),
                    };
                    inner.variable_types.insert(name.clone(), inner_ty.clone());
                    if inner_ty.is_heap_type() {
                        inner.track_binding(name.clone(), var, inner_ty);
                    }
                }
            }

            let result = inner.compile_expr(body)?;
            inner.pop_scope_for_value(result);
            inner.builder.ins().return_(&[result]);
            inner.builder.seal_all_blocks();
            inner.builder.finalize();

            let mut ctx = cranelift::codegen::Context::for_function(cont_func);
            self.module
                .define_function(func_id, &mut ctx)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to define par-bind! continuation: {}", e),
                    span,
                })?;
        }

        // Allocate closure: [code_ptr, drop_ptr(null), cap0, cap1, ...]
        let closure_size = ((2 + capture_names.len()) * 8) as i64;
        let closure_ptr = self.compile_alloc(closure_size, span)?;

        // Store code_ptr at offset 0
        let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
        let code_ptr = self.builder.ins().func_addr(types::I64, func_ref);
        self.builder
            .ins()
            .store(MemFlags::trusted(), code_ptr, closure_ptr, 0);

        // Store null drop_ptr at offset 8
        let null_drop = self.builder.ins().iconst(types::I64, 0);
        self.builder
            .ins()
            .store(MemFlags::trusted(), null_drop, closure_ptr, 8);

        // Store captures at offsets 16, 24, ... (i+2)*8
        for (i, cap_name) in capture_names.iter().enumerate() {
            let cap_val = if let Some(var) = self.variables.get(cap_name) {
                self.builder.use_var(*var)
            } else {
                return Err(CranelispError::CodegenError {
                    message: format!("undefined capture in par-bind! continuation: {}", cap_name),
                    span,
                });
            };
            let offset = ((i + 2) * 8) as i32;
            self.builder
                .ins()
                .store(MemFlags::trusted(), cap_val, closure_ptr, offset);

            // RC inc: capturing creates an additional reference
            if let Some(ty) = self.variable_types.get(cap_name).cloned() {
                self.emit_inc(cap_val, &ty);
            }
        }

        Ok(closure_ptr)
    }

    /// Compile a sequential let expression (standard path, no lenient evaluation).
    fn compile_let_sequential(
        &mut self,
        bindings: &[(String, Expr)],
        body: &Expr,
    ) -> Result<Value, CranelispError> {
        let saved_tail = self.in_tail_position;
        self.push_scope();
        self.in_tail_position = false;
        for (name, val_expr) in bindings {
            let val = self.compile_expr(val_expr)?;
            let var = self.fresh_var(types::I64);
            self.builder.def_var(var, val);
            self.variables.insert(name.clone(), var);

            // Track variable type for RC
            if let Some(ty) = self.expr_types.get(&val_expr.span()) {
                self.variable_types.insert(name.clone(), ty.clone());
                if ty.is_heap_type() {
                    self.track_binding(name.clone(), var, ty.clone());

                    // Check if val is a borrowed temp → promote to borrowed var
                    if self.is_borrowed_temp(val) {
                        self.mark_borrowed_var(var);
                    } else if matches!(val_expr, Expr::Var { .. }) {
                        if self.is_last_use(val_expr) {
                            if let Expr::Var { name: src_name, .. } = val_expr {
                                let bare_src = crate::names::resolve_bare_name(src_name);
                                if let Some(&src_var) = self.variables.get(bare_src) {
                                    self.mark_consumed(src_var);
                                    if self.is_unique(src_var) {
                                        self.mark_unique(var);
                                    }
                                }
                            }
                        } else {
                            self.emit_inc(val, ty);
                            if let Expr::Var { name: src_name, .. } = val_expr {
                                let bare_src = crate::names::resolve_bare_name(src_name);
                                if let Some(&src_var) = self.variables.get(bare_src) {
                                    self.remove_unique(src_var);
                                }
                            }
                        }
                    } else {
                        let is_fresh_alloc = matches!(
                            val_expr,
                            Expr::StringLit { .. }
                            | Expr::VecLit { .. }
                            | Expr::Lambda { .. }
                            | Expr::Apply { .. }
                            | Expr::Match { .. }
                            | Expr::If { .. }
                        );
                        if is_fresh_alloc {
                            self.mark_unique(var);
                        }
                    }
                }
            }
        }
        self.in_tail_position = saved_tail;
        let result = self.compile_expr(body)?;
        self.in_tail_position = false;
        self.pop_scope_for_value(result);
        Ok(result)
    }

    /// Compile a let expression with lenient evaluation: sparkable bindings are
    /// evaluated in parallel via IVars, then forced at a barrier before the body.
    fn compile_let_lenient(
        &mut self,
        bindings: &[(String, Expr)],
        body: &Expr,
        sparkable: &[usize],
        _span: crate::error::Span,
    ) -> Result<Value, CranelispError> {
        let saved_tail = self.in_tail_position;
        self.push_scope();
        self.in_tail_position = false;

        let sparkable_set: HashSet<usize> = sparkable.iter().copied().collect();

        // Phase 1: Create IVars for sparkable bindings and spark them
        let mut ivar_map: std::collections::HashMap<usize, Value> =
            std::collections::HashMap::new();

        for &idx in sparkable {
            let (_, val_expr) = &bindings[idx];
            // Wrap the binding expr in a zero-arg thunk (closure)
            let thunk_expr = Expr::Lambda {
                params: vec![],
                param_annotations: vec![],
                body: Box::new(val_expr.clone()),
                span: val_expr.span(),
            };
            let thunk_ptr = self.compile_expr(&thunk_expr)?;

            // Call ivar_create(thunk) -> ivar_ptr
            let create_ref = self
                .module
                .declare_func_in_func(self.ivar_create_func_id, self.builder.func);
            let call = self.builder.ins().call(create_ref, &[thunk_ptr]);
            let ivar_ptr = self.builder.inst_results(call)[0];

            // Call ivar_spark(ivar) — submit to rayon pool
            let spark_ref = self
                .module
                .declare_func_in_func(self.ivar_spark_func_id, self.builder.func);
            self.builder.ins().call(spark_ref, &[ivar_ptr]);

            ivar_map.insert(idx, ivar_ptr);
        }

        // Phase 2: Process bindings in order
        for (i, (name, val_expr)) in bindings.iter().enumerate() {
            let val = if sparkable_set.contains(&i) {
                // Force the IVar to get the result
                let ivar_ptr = ivar_map[&i];
                let force_ref = self
                    .module
                    .declare_func_in_func(self.ivar_force_func_id, self.builder.func);
                let call = self.builder.ins().call(force_ref, &[ivar_ptr]);
                let forced_val = self.builder.inst_results(call)[0];

                // Dec the IVar cell (our reference; spark's dec happens in its closure)
                self.emit_dec_inline(ivar_ptr, None);

                forced_val
            } else {
                // Non-sparkable: compile normally
                self.compile_expr(val_expr)?
            };

            let var = self.fresh_var(types::I64);
            self.builder.def_var(var, val);
            self.variables.insert(name.clone(), var);

            // RC tracking for bindings
            if let Some(ty) = self.expr_types.get(&val_expr.span()) {
                self.variable_types.insert(name.clone(), ty.clone());
                if ty.is_heap_type() {
                    self.track_binding(name.clone(), var, ty.clone());

                    if sparkable_set.contains(&i) {
                        // Forced value is a fresh result — mark unique
                        self.mark_unique(var);
                    } else if self.is_borrowed_temp(val) {
                        self.mark_borrowed_var(var);
                    } else if matches!(val_expr, Expr::Var { .. }) {
                        if self.is_last_use(val_expr) {
                            if let Expr::Var { name: src_name, .. } = val_expr {
                                let bare_src = crate::names::resolve_bare_name(src_name);
                                if let Some(&src_var) = self.variables.get(bare_src) {
                                    self.mark_consumed(src_var);
                                    if self.is_unique(src_var) {
                                        self.mark_unique(var);
                                    }
                                }
                            }
                        } else {
                            self.emit_inc(val, ty);
                            if let Expr::Var { name: src_name, .. } = val_expr {
                                let bare_src = crate::names::resolve_bare_name(src_name);
                                if let Some(&src_var) = self.variables.get(bare_src) {
                                    self.remove_unique(src_var);
                                }
                            }
                        }
                    } else {
                        let is_fresh_alloc = matches!(
                            val_expr,
                            Expr::StringLit { .. }
                            | Expr::VecLit { .. }
                            | Expr::Lambda { .. }
                            | Expr::Apply { .. }
                            | Expr::Match { .. }
                            | Expr::If { .. }
                        );
                        if is_fresh_alloc {
                            self.mark_unique(var);
                        }
                    }
                }
            }
        }

        // Phase 3: Compile body and cleanup
        self.in_tail_position = saved_tail;
        let result = self.compile_expr(body)?;
        self.in_tail_position = false;
        self.pop_scope_for_value(result);
        Ok(result)
    }
}
