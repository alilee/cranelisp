// Function application codegen.
//
// compile_apply, compile_direct_call, compile_tail_self_call

use cranelift::prelude::*;
use cranelift_module::Module;

use cranelisp_types::{CompileMode, CranelispError, Expr, ResolvedCall, Span, Symbol};

use crate::operators;

use super::FnCompiler;

impl<'a> FnCompiler<'a> {
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

        // Check for builtin operator resolution.
        if let Some(resolved) = self.ctx.method_resolutions.get(&span) {
            match resolved {
                ResolvedCall::BuiltinFn { name: op_name } => {
                    // Compile arguments.
                    let arg_vals: Vec<Value> = args
                        .iter()
                        .map(|a| self.compile_expr(a))
                        .collect::<Result<_, _>>()?;

                    self.in_tail_position = saved_tail;

                    return operators::emit_builtin_op(
                        &mut self.builder,
                        op_name,
                        &arg_vals,
                        span,
                    );
                }
                ResolvedCall::TraitMethod { mangled_name, .. } => {
                    // Ring 2: trait method dispatch. Not yet implemented.
                    return Err(CranelispError::CodegenError {
                        message: format!(
                            "trait method dispatch not supported in Ring 0: {mangled_name}"
                        ),
                        span,
                    });
                }
                ResolvedCall::SigDispatch { mangled_name } => {
                    return Err(CranelispError::CodegenError {
                        message: format!(
                            "multi-sig dispatch not supported in Ring 0: {mangled_name}"
                        ),
                        span,
                    });
                }
                ResolvedCall::AutoCurry { target_name, .. } => {
                    return Err(CranelispError::CodegenError {
                        message: format!("auto-curry not supported in Ring 0: {target_name}"),
                        span,
                    });
                }
            }
        }

        // Regular function call: callee must be a Var referring to a known function.
        if let Expr::Var {
            name,
            span: var_span,
        } = callee
        {
            // Compile arguments.
            let arg_vals: Vec<Value> = args
                .iter()
                .map(|a| self.compile_expr(a))
                .collect::<Result<_, _>>()?;

            self.in_tail_position = saved_tail;

            return self.compile_direct_call(name, &arg_vals, *var_span);
        }

        // Callee is not a variable -- could be a lambda application (Ring 1+).
        Err(CranelispError::CodegenError {
            message:
                "indirect function calls not supported in Ring 0 (closures require Ring 1)".into(),
            span,
        })
    }

    /// Compile a call to a named function.
    ///
    /// In Batch/Release mode: emits a direct `call` instruction.
    /// In Interactive mode: loads the function pointer from the GOT slot
    /// and emits a `call_indirect` instruction. This enables function
    /// redefinition in the REPL — updating the GOT slot updates all
    /// call sites.
    fn compile_direct_call(
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
                let got_slots = self.ctx.got_slots.ok_or_else(|| {
                    CranelispError::CodegenError {
                        message: "Interactive mode requires GOT slot assignments".into(),
                        span,
                    }
                })?;
                let got_base = self.ctx.got_base_ptr.ok_or_else(|| {
                    CranelispError::CodegenError {
                        message: "Interactive mode requires GOT base pointer".into(),
                        span,
                    }
                })?;
                let slot = got_slots.get(name).ok_or_else(|| {
                    CranelispError::CodegenError {
                        message: format!("no GOT slot for function: {name}"),
                        span,
                    }
                })?;

                // Compute the address of the GOT slot: got_base + slot * 8
                let slot_offset = (*slot * 8) as i64;
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
}
