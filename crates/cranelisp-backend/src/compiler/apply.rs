// Function application codegen.
//
// compile_apply, compile_direct_call, compile_tail_self_call,
// compile_data_constructor_call, compile_extern_call,
// compile_closure_call

use cranelift::prelude::*;
use cranelift_module::Module;

use cranelisp_types::{CranelispError, Expr, HeapCategory, ResolvedCall, Span, Symbol};

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
        resolved_call: Option<&ResolvedCall>,
        apply_type: Option<&cranelisp_types::Type>,
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

        // TCO check for monomorphised constrained-poly self-recursion:
        // When compiling `countdown$Int`, the body's recursive call is
        // `(countdown ...)` which the typechecker resolves to
        // `SigDispatch { mangled_name: "countdown$Int" }`. The callee
        // AST name ("countdown") doesn't match the current fn name
        // ("countdown$Int"), so the check above misses it. We detect
        // this case by checking whether the resolved call's mangled name
        // matches the current function.
        if self.in_tail_position
            && self.tail_loop_block.is_some()
            && args.len() == self.fn_param_count
            && let Some(ResolvedCall::SigDispatch { mangled_name }) = resolved_call
            && let Some(ref fn_name) = self.current_fn_name
            && fn_name.as_ref() == mangled_name.as_ref()
        {
            return self.compile_tail_self_call(args);
        }

        // CRITICAL: Args are never in tail position.
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;

        // Check for resolved call (builtin, trait method, sig-dispatch, auto-curry).
        if let Some(resolved) = resolved_call {
            return self.compile_resolved_call(resolved.clone(), args, span, saved_tail);
        }

        // Regular function call: callee must be a Var referring to a known function,
        // a data constructor, or a local variable holding a closure.
        if let Expr::Var {
            name,
            span: var_span,
            ..
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
        if let Some(ty) = apply_type {
            let category = HeapCategory::classify(ty, Some(self.ctx.symbol_tables));
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

                // Vec operations: intercept and compile inline.
                // Vec ops handle their own temporary cleanup internally
                // via emit_vec_drop_if_temporary (COW-specific, not post-call
                // convention). See ring2-rc.md §3.3.
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
                    self.in_tail_position = saved_tail;
                    return self.compile_extern_call(op_name, &arg_vals, span);
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

                // Inline builtin operators (arithmetic, comparison, boolean).
                // All operands are NeverHeap (Int/Bool/Float) — no dec work.
                let arg_vals = self.compile_arg_list(args)?;
                self.in_tail_position = saved_tail;
                operators::emit_builtin_op(
                    &mut self.builder, op_name, &arg_vals, span,
                    self.module, self.ctx.panic_func_id,
                )
            }
            ResolvedCall::TraitMethod {
                ref trait_name,
                ref method_name,
                ref impl_type,
                ref mangled_name,
            } => {
                // Check if this is a known primitive trait method (inline IR).
                if let Some(prim_name) =
                    operators::primitive_for_trait_method(&trait_name.name, method_name, &impl_type.name)
                {
                    // Decision 24 (Sprint 56 Step 2c): consuming convention —
                    // mirror the BuiltinFn arm above.
                    if is_extern_primitive(prim_name) {
                        let arg_vals = if prim_name == "string-identity" {
                            self.compile_arg_list(args)?
                        } else {
                            self.compile_consuming_arg_list(args)?
                        };
                        self.in_tail_position = saved_tail;
                        return self.compile_extern_call(prim_name, &arg_vals, span);
                    }

                    // neq-string: call str-eq (extern) and negate the result.
                    // str-eq is a simple-heap consuming extern — use consuming args.
                    if prim_name == "neq-string" {
                        let arg_vals = self.compile_consuming_arg_list(args)?;
                        self.in_tail_position = saved_tail;
                        let eq_result = self.compile_extern_call("str-eq", &arg_vals, span)?;
                        return Ok(self.builder.ins().bxor_imm(eq_result, 1));
                    }

                    // Inline primitive trait method (NeverHeap operands).
                    let arg_vals = self.compile_arg_list(args)?;
                    self.in_tail_position = saved_tail;
                    return operators::emit_builtin_op(
                        &mut self.builder, prim_name, &arg_vals, span,
                        self.module, self.ctx.panic_func_id,
                    );
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

            // Decision 24 (Sprint 56 Step 2c): uniform consuming convention.
            // The constructor stores args as fields; the ADT's drop glue
            // dec's heap-typed fields when the ADT itself reaches rc=0.
            // For variable args we inc so the caller's binding survives
            // scope cleanup — the ADT holds its own independent reference.
            // For temporary args, rc=1 transfers directly into the field.
            let arg_vals = self.compile_consuming_arg_list(args)?;
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
    /// Plain compilation: no RC adjustments. Used for inline builtins whose
    /// operands are NeverHeap (Int/Bool/Float), and for data-constructor
    /// call-site arg preparation where the consuming inc happens via
    /// `compile_consuming_arg_list` (which this method backs). Under
    /// Decision 24 (uniform consuming) the plain form has a narrow role:
    /// pure-value builtins where RC does not apply.
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
                        HeapCategory::classify(ty, Some(self.ctx.symbol_tables));
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
    ) -> Result<Value, CranelispError> {
        // --- Unified GOT path (target: works for both JIT and object codegen) ---
        // Uses global_value(DataId) which Cranelift lowers to:
        //   JIT (is_pic=false): movz+movk (absolute address)
        //   Object (is_pic=true): ADRP+ADD (PC-relative relocation)
        //
        // Slot assignments are read directly from `symbol_tables` — no env
        // abstraction. See design/backend/compile-to-module.md §12.
        if let Some((module_path, slot)) = crate::compiler::resolve_got_target(
            self.ctx.symbol_tables,
            &self.ctx.current_module,
            name,
        ) {
            let got_sym = crate::compiler::got_data_symbol_name(&module_path);
            let data_id = self.module
                .declare_data(&got_sym, cranelift_module::Linkage::Import, false, false)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to declare GOT data '{}': {e}", got_sym),
                    span,
                })?;
            return self.emit_got_indirect_call_via_data_id(data_id, slot, arg_vals);
        }

        // Direct call: look up FuncId and emit `call`.
        {
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
    fn emit_got_indirect_call_via_data_id(
        &mut self,
        data_id: cranelift_module::DataId,
        slot: usize,
        arg_vals: &[Value],
    ) -> Result<Value, CranelispError> {
        // The symbol address IS the slab base (Decision 23 — unified shape).
        let gv = self.module.declare_data_in_func(data_id, self.builder.func);
        let slab_base = self.builder.ins().global_value(types::I64, gv);

        // Compute slot address: slab_base + slot * 8
        let slot_addr = self.builder.ins().iadd_imm(slab_base, (slot * 8) as i64);

        // Load the function pointer from the GOT slot.
        let func_ptr = self.builder.ins().load(
            types::I64,
            MemFlags::trusted(),
            slot_addr,
            0,
        );

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

    /// Resolve a function name to `(defining_module, slot_index)` by walking
    /// the shared symbol-table map. Returns an error if no GOT slot is found.
    ///
    /// Replacement for the Sprint-56-retracted `CompilationEnv::resolve_got`.
    /// Callers that need a concrete base-pointer should emit a `global_value`
    /// against the `__cranelisp_got_{module}` data symbol (see §12) rather
    /// than embedding a compile-time constant.
    pub(crate) fn resolve_got_entry(
        &self,
        name: &Symbol,
        span: Span,
    ) -> Result<(cranelisp_types::ModuleFullPath, usize), CranelispError> {
        crate::compiler::resolve_got_target(
            self.ctx.symbol_tables,
            &self.ctx.current_module,
            name,
        )
        .ok_or_else(|| CranelispError::CodegenError {
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
