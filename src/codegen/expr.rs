use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;

use cranelift_module::Module;

use crate::ast::Expr;
use crate::error::CranelispError;
use crate::names::resolve_bare_name;

use super::FnCompiler;

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
            Expr::Let { bindings, body, .. } => {
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
                            // Inc for variable aliases (Var RHS = additional reference)
                            if matches!(val_expr, Expr::Var { .. }) {
                                self.emit_inc(val, ty);
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
                let then_val = self.compile_expr(then_branch)?;
                self.builder
                    .ins()
                    .jump(merge_block, &[BlockArg::Value(then_val)]);

                self.builder.switch_to_block(else_block);
                self.builder.seal_block(else_block);
                self.in_tail_position = saved_tail;
                let else_val = self.compile_expr(else_branch)?;
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
            } => self.compile_match(scrutinee, arms, *span),
            Expr::VecLit { elements, span, .. } => self.compile_vec_lit(elements, *span),
            Expr::Annotate { expr: inner, .. } => {
                // Inherits tail position
                self.compile_expr(inner)
            }
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
}
