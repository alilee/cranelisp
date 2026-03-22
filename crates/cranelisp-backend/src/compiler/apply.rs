// Function application codegen.
//
// compile_apply, compile_direct_call, compile_tail_self_call,
// compile_data_constructor_call, compile_extern_call,
// compile_closure_call

use cranelift::prelude::*;
use cranelift_module::Module;

use cranelisp_types::{CompileMode, CranelispError, Expr, HeapCategory, ResolvedCall, Span, Symbol};

use crate::heap::{self, HeapAdt, HeapClosure};
use crate::operators;

use super::FnCompiler;

impl<'a, M: Module> FnCompiler<'a, M> {
    // --- Function application ---

    pub(crate) fn compile_apply(
        &mut self,
        callee: &Expr,
        args: &[Expr],
        span: Span,
    ) -> Result<Value, CranelispError> {
        // TCO check: self-recursive call in tail position -> jump to loop header.
        if self.in_tail_position
            && let Expr::Var { name, .. } = callee
            && let Some(ref fn_name) = self.current_fn_name
            && *name == *fn_name
            && self.tail_loop_block.is_some()
            && args.len() == self.fn_param_count
        {
            return self.compile_tail_self_call(args);
        }

        // CRITICAL: Args are never in tail position.
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;

        // Check for resolved call (builtin, trait method, sig-dispatch, auto-curry).
        if let Some(resolved) = self.ctx.method_resolutions.get(&span) {
            return self.compile_resolved_call(resolved.clone(), args, span, saved_tail);
        }

        // Regular function call: callee must be a Var referring to a known function,
        // a data constructor, or a local variable holding a closure.
        if let Expr::Var {
            name,
            span: var_span,
        } = callee
        {
            return self.compile_var_apply(name, *var_span, callee, args, span, saved_tail);
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
        if let Some(ty) = self.ctx.expr_types.get(&span) {
            let category = HeapCategory::classify(ty, Some(self.ctx.type_defs));
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_inc(&mut self.builder, result);
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_inc_guarded(&mut self.builder, result);
                }
                HeapCategory::NeverHeap => {}
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
    /// or auto-curry). Handles the four `ResolvedCall` variants.
    fn compile_resolved_call(
        &mut self,
        resolved: ResolvedCall,
        args: &[Expr],
        span: Span,
        saved_tail: bool,
    ) -> Result<Value, CranelispError> {
        match resolved {
            ResolvedCall::BuiltinFn { name: ref op_name } => {
                // Builtins are borrowing: they don't dec params.
                // We dec temporary (non-variable) heap args after the call.

                // IO bind: intercept and compile inline.
                // bind uses consuming semantics: it takes ownership of both args
                // by storing them in the Bind node. For variables, inc to add
                // the Bind node's reference. For temporaries, transfer ownership
                // (temp starts at rc=1, Bind node inherits it — no inc/dec needed).
                //
                // CRITICAL: do NOT call dec_temporary_args after bind. Unlike
                // borrowing builtins, bind stores its args. dec_temporary_args
                // would call emit_inline_drop_glue which dec's ADT fields
                // while the node is still alive, causing use-after-free.
                if op_name.as_ref() == "bind" {
                    let arg_vals = self.compile_consuming_arg_list(args)?;
                    self.in_tail_position = saved_tail;
                    let result = self.compile_bind_inline(&arg_vals, span)?;
                    // No dec_temporary_args — bind owns the args.
                    return Ok(result);
                }

                // Vec operations: intercept and compile inline.
                // Vec ops handle their own temporary cleanup internally
                // via emit_vec_drop_if_temporary — do NOT call dec_temporary_args.
                if is_vec_primitive(op_name) {
                    let arg_vals = self.compile_arg_list(args)?;
                    self.in_tail_position = saved_tail;
                    if let Some(val) = self.compile_vec_op(op_name, args, &arg_vals, span)? {
                        return Ok(val);
                    }
                    // Fall through to extern if compile_vec_op returned None.
                    return self.compile_extern_call(op_name, &arg_vals, span);
                }

                if is_extern_primitive(op_name) {
                    let arg_vals = self.compile_arg_list(args)?;
                    self.in_tail_position = saved_tail;
                    let result = self.compile_extern_call(op_name, &arg_vals, span)?;
                    self.dec_temporary_args(args, &arg_vals);
                    return Ok(result);
                }

                // Unrecognized builtin: treat as extern call.
                // This covers platform effect functions (PlatformEffect) whose
                // JIT symbol names are resolved by the typechecker. Platform
                // functions use consuming convention — the DLL owns heap args
                // (e.g., CLString::own() captures the string).
                if !operators::is_known_builtin(op_name) {
                    let arg_vals = self.compile_consuming_arg_list(args)?;
                    self.in_tail_position = saved_tail;
                    return self.compile_extern_call(op_name, &arg_vals, span);
                }

                let arg_vals = self.compile_arg_list(args)?;
                self.in_tail_position = saved_tail;
                let result =
                    operators::emit_builtin_op(
                        &mut self.builder, op_name, &arg_vals, span,
                        self.module, self.ctx.panic_func_id,
                    )?;
                self.dec_temporary_args(args, &arg_vals);
                Ok(result)
            }
            ResolvedCall::TraitMethod {
                ref trait_name,
                ref method_name,
                ref impl_type,
                ref mangled_name,
            } => {
                // Check if this is a known primitive trait method (inline IR).
                if let Some(prim_name) =
                    operators::primitive_for_trait_method(trait_name, method_name, impl_type)
                {
                    // Primitive trait methods are borrowing.
                    if is_extern_primitive(prim_name) {
                        let arg_vals = self.compile_arg_list(args)?;
                        self.in_tail_position = saved_tail;
                        let result = self.compile_extern_call(prim_name, &arg_vals, span)?;
                        self.dec_temporary_args(args, &arg_vals);
                        return Ok(result);
                    }

                    // neq-string: call str-eq (extern) and negate the result.
                    if prim_name == "neq-string" {
                        let arg_vals = self.compile_arg_list(args)?;
                        self.in_tail_position = saved_tail;
                        let eq_result = self.compile_extern_call("str-eq", &arg_vals, span)?;
                        let result = self.builder.ins().bxor_imm(eq_result, 1);
                        self.dec_temporary_args(args, &arg_vals);
                        return Ok(result);
                    }

                    let arg_vals = self.compile_arg_list(args)?;
                    self.in_tail_position = saved_tail;
                    let result = operators::emit_builtin_op(
                        &mut self.builder, prim_name, &arg_vals, span,
                        self.module, self.ctx.panic_func_id,
                    )?;
                    self.dec_temporary_args(args, &arg_vals);
                    return Ok(result);
                }

                // Not a primitive: user function — consuming convention.
                let sym = Symbol::from(mangled_name.as_ref());
                let arg_vals = self.compile_consuming_arg_list(args)?;
                self.in_tail_position = saved_tail;
                self.compile_direct_call(&sym, &arg_vals, span)
            }
            ResolvedCall::SigDispatch { mangled_name } => {
                // User function — consuming convention.
                let arg_vals = self.compile_consuming_arg_list(args)?;
                self.in_tail_position = saved_tail;
                let sym = Symbol::from(mangled_name.as_ref());
                self.compile_direct_call(&sym, &arg_vals, span)
            }
            ResolvedCall::AutoCurry {
                ref target_name,
                applied_count,
                total_count,
                ref trait_resolution,
            } => {
                // Compile applied args with consuming convention:
                // the auto-curry closure captures them, and the wrapper
                // will inc before forwarding to the target function.
                let arg_vals = self.compile_consuming_arg_list(args)?;
                self.in_tail_position = saved_tail;
                self.compile_auto_curry(
                    target_name,
                    &arg_vals,
                    applied_count,
                    total_count,
                    args,
                    span,
                    trait_resolution.as_deref(),
                )
            }
        }
    }

    /// Compile a function application where the callee is a Var.
    /// Dispatches between data constructor, local closure, and direct call.
    fn compile_var_apply(
        &mut self,
        name: &Symbol,
        var_span: Span,
        callee: &Expr,
        args: &[Expr],
        span: Span,
        saved_tail: bool,
    ) -> Result<Value, CranelispError> {
        // Check if this is a data constructor call.
        if let Some((tag, field_count)) = self.data_constructor_info(name) {
            if args.len() != field_count {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "constructor '{name}' expects {field_count} args, got {}",
                        args.len()
                    ),
                    span,
                });
            }

            // Data constructors store args as fields; no function body
            // to dec them. ADT drop glue handles field cleanup.
            let arg_vals = self.compile_arg_list(args)?;
            self.in_tail_position = saved_tail;
            return self.compile_data_constructor_call(tag, &arg_vals, span);
        }

        // Check if the callee is a local variable (holding a closure value).
        if self.variables.contains_key(name) {
            let callee_val = self.compile_expr(callee)?;
            // Closure body is a user function — consuming convention.
            let arg_vals = self.compile_consuming_arg_list(args)?;
            self.in_tail_position = saved_tail;
            return self.compile_closure_call(callee_val, &arg_vals, span);
        }

        // Not a local variable: user function — consuming convention.
        let arg_vals = self.compile_consuming_arg_list(args)?;
        self.in_tail_position = saved_tail;
        self.compile_direct_call(name, &arg_vals, var_span)
    }

    /// Compile a list of argument expressions into Cranelift values.
    ///
    /// Plain compilation: no RC adjustments. The caller is responsible for
    /// any inc/dec depending on whether the callee is consuming (user fn)
    /// or borrowing (builtin/extern).
    fn compile_arg_list(&mut self, args: &[Expr]) -> Result<Vec<Value>, CranelispError> {
        args.iter()
            .map(|arg| self.compile_expr(arg))
            .collect()
    }

    /// Compile args for a consuming callee (user-defined function).
    ///
    /// The callee dec's all heap-typed parameters at exit. We inc
    /// heap-typed variable arguments so the caller's binding survives
    /// the callee's dec. Temporary expressions start at rc=1 and
    /// the callee's dec frees them — no caller action needed.
    fn compile_consuming_arg_list(
        &mut self,
        args: &[Expr],
    ) -> Result<Vec<Value>, CranelispError> {
        let mut vals = Vec::with_capacity(args.len());
        for arg in args {
            let val = self.compile_expr(arg)?;

            // Inc heap-typed variable arguments for consuming convention.
            if let Expr::Var { name, .. } = arg
                && let Some(ty) = self.variable_types.get(name) {
                    let category =
                        HeapCategory::classify(ty, Some(self.ctx.type_defs));
                    match category {
                        HeapCategory::AlwaysHeap => {
                            heap::emit_rc_inc(&mut self.builder, val);
                        }
                        HeapCategory::Mixed => {
                            heap::emit_rc_inc_guarded(&mut self.builder, val);
                        }
                        HeapCategory::NeverHeap => {}
                    }
                }

            vals.push(val);
        }
        Ok(vals)
    }

    /// Dec temporary (non-variable) heap-typed arguments after a
    /// borrowing call (builtin/extern). Variable arguments are owned
    /// by their scope and will be dec'd by `pop_scope_with_cleanup`.
    ///
    /// ADT field cleanup is done inside the dealloc path (RC=0) via
    /// `emit_rc_dec_with_inline_drop_glue`, not unconditionally.
    fn dec_temporary_args(&mut self, args: &[Expr], arg_vals: &[Value]) {
        let dealloc_id = match self.ctx.dealloc_func_id {
            Some(id) => id,
            None => return,
        };

        for (arg, &val) in args.iter().zip(arg_vals.iter()) {
            // Only dec temporaries (non-variable expressions).
            if matches!(arg, Expr::Var { .. }) {
                continue;
            }
            // Check if the expression produces a heap-typed value.
            if let Some(ty) = self.ctx.expr_types.get(&arg.span()).cloned() {
                let category = HeapCategory::classify(&ty, Some(self.ctx.type_defs));
                match category {
                    HeapCategory::AlwaysHeap => {
                        if matches!(ty, cranelisp_types::Type::Fn(_, _)) {
                            self.emit_closure_dec_inline(val, dealloc_id);
                        } else {
                            self.emit_rc_dec_with_inline_drop_glue(
                                val, &ty, dealloc_id, false,
                            );
                        }
                    }
                    HeapCategory::Mixed => {
                        self.emit_rc_dec_with_inline_drop_glue(
                            val, &ty, dealloc_id, true,
                        );
                    }
                    HeapCategory::NeverHeap => {}
                }
            }
        }
    }

    /// Compile a call to a named function.
    ///
    /// In Batch/Release mode: emits a direct `call` instruction.
    /// In Interactive mode: loads the function pointer from the GOT slot
    /// and emits a `call_indirect` instruction.
    pub(crate) fn compile_direct_call(
        &mut self,
        name: &Symbol,
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        match self.ctx.mode {
            CompileMode::Batch | CompileMode::Release => {
                // Direct call: look up FuncId and emit `call`.
                let func_id = self.ctx.func_ids.get(name).ok_or_else(|| {
                    CranelispError::CodegenError {
                        message: format!("undefined function: {name}"),
                        span,
                    }
                })?;

                let local_func = self
                    .module
                    .declare_func_in_func(*func_id, self.builder.func);
                let call = self.builder.ins().call(local_func, arg_vals);
                Ok(self.builder.inst_results(call)[0])
            }
            CompileMode::Interactive => {
                // GOT-indirect call: load function pointer from GOT slot.
                //
                // First try the local module's GOT. If the function isn't found
                // locally, fall back to the cross-module GOT which maps imported
                // functions to their defining module's GOT base and slot.
                let (got_base, slot) = self.resolve_got_entry(name, span)?;

                // Compute the address of the GOT slot: got_base + slot * 8
                let slot_offset = (slot * 8) as i64;
                let base_val = self.builder.ins().iconst(types::I64, got_base);
                let slot_addr = self.builder.ins().iadd_imm(base_val, slot_offset);

                // Load the function pointer from the GOT slot.
                let func_ptr = self.builder.ins().load(
                    types::I64,
                    MemFlags::trusted(),
                    slot_addr,
                    0,
                );

                // Build the signature for call_indirect: all params and return are i64.
                let mut sig = self.module.make_signature();
                for _ in arg_vals {
                    sig.params.push(AbiParam::new(types::I64));
                }
                sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = self.builder.import_signature(sig);

                // Emit call_indirect.
                let call = self.builder.ins().call_indirect(sig_ref, func_ptr, arg_vals);
                Ok(self.builder.inst_results(call)[0])
            }
        }
    }

    /// Resolve a function name to a `(got_base_ptr, slot_index)` pair.
    ///
    /// Lookup order:
    /// 1. Local module GOT (`ctx.got_slots` + `ctx.got_base_ptr`)
    /// 2. Cross-module GOT (`ctx.cross_module_got`) — for imported functions
    ///
    /// Returns `(got_base_ptr_as_i64, slot_index)` or an error if not found.
    pub(crate) fn resolve_got_entry(
        &self,
        name: &Symbol,
        span: Span,
    ) -> Result<(i64, usize), CranelispError> {
        // Try local GOT first.
        if let (Some(got_slots), Some(got_base)) = (self.ctx.got_slots, self.ctx.got_base_ptr)
            && let Some(&slot) = got_slots.get(name) {
                return Ok((got_base, slot));
            }

        // Try cross-module GOT: scan all entries for a matching function name.
        // The cross-module map is keyed by (ModuleFullPath, Symbol), so we search
        // for any entry whose Symbol component matches.
        if let Some(xmod_got) = self.ctx.cross_module_got {
            for ((_, sym), &(base, slot)) in xmod_got {
                if sym == name {
                    return Ok((base, slot));
                }
            }
        }

        // Neither local nor cross-module GOT has this function.
        Err(CranelispError::CodegenError {
            message: format!("no GOT slot for function: {name}"),
            span,
        })
    }

    /// Compile a tail self-recursive call as a jump to the loop header.
    fn compile_tail_self_call(&mut self, args: &[Expr]) -> Result<Value, CranelispError> {
        // CRITICAL: Args are not in tail position.
        self.in_tail_position = false;

        // Compile all arguments.
        let arg_vals: Vec<Value> = args
            .iter()
            .map(|a| self.compile_expr(a))
            .collect::<Result<_, _>>()?;

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

    /// Compile a data constructor call: allocate heap, store tag + fields.
    fn compile_data_constructor_call(
        &mut self,
        tag: usize,
        field_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    span,
                })?;

        let payload_size = HeapAdt::payload_size(field_vals.len()) as i64;
        let base_ptr = heap::emit_alloc(
            &mut self.builder,
            self.module,
            alloc_id,
            payload_size,
        );

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
                span,
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
                span,
            });
        }

        let io_val = arg_vals[0]; // inner IO tree
        let cont_val = arg_vals[1]; // continuation closure

        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    span,
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
        if let Some(dealloc_id) = self.ctx.dealloc_func_id {
            self.emit_closure_dec_inline(closure_val, dealloc_id);
        }
    }
}

/// Check if a builtin name is an extern primitive (requires a call, not inline IR).
///
/// Extern primitives use borrowing convention: arguments are not consumed.
/// The caller dec's temporaries after the call via `dec_temporary_args`.
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
            // Trace ADT field accessors: borrowing convention (just read a field).
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
