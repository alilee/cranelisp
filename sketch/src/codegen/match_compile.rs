use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;
use cranelift_module::Module;

use crate::error::CranelispError;
use crate::names::resolve_bare_name;

use super::FnCompiler;

impl<'a, M: Module> FnCompiler<'a, M> {
    pub(crate) fn compile_match(
        &mut self,
        scrutinee: &crate::ast::Expr,
        arms: &[crate::ast::MatchArm],
        span: crate::error::Span,
    ) -> Result<Value, CranelispError> {
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;
        let scrut_val = self.compile_expr(scrutinee)?;
        let scrutinee_type = self.expr_types.get(&scrutinee.span()).cloned();
        // Track whether scrutinee is a temporary (non-Var) — needs dec after match
        let scrutinee_is_temporary = !matches!(scrutinee, crate::ast::Expr::Var { .. });

        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);

        let panic_block = self.builder.create_block();

        // Compile each arm as a test-and-branch chain
        let mut arm_blocks: Vec<cranelift::prelude::Block> = Vec::new();
        for _ in arms {
            arm_blocks.push(self.builder.create_block());
        }

        // Check if scrutinee is a unique Var (before entering branch arms).
        // If so, field extractions can borrow instead of inc'ing.
        let scrutinee_is_unique = if let crate::ast::Expr::Var { name, .. } = scrutinee {
            let bare = crate::names::resolve_bare_name(name);
            self.branch_depth == 0 && self.is_var_unique(bare)
        } else {
            false
        };

        // Jump to first test
        if arms.is_empty() {
            self.builder.ins().jump(panic_block, &[]);
        } else {
            self.builder.ins().jump(arm_blocks[0], &[]);
        }

        for (i, arm) in arms.iter().enumerate() {
            let next_block = if i + 1 < arms.len() {
                arm_blocks[i + 1]
            } else {
                panic_block
            };

            self.builder.switch_to_block(arm_blocks[i]);
            self.builder.seal_block(arm_blocks[i]);

            match &arm.pattern {
                crate::ast::Pattern::Wildcard { .. } => {
                    // Always matches — compile body and jump to merge
                    self.in_tail_position = saved_tail;

                    self.branch_depth += 1;
                    let body_val = self.compile_expr(&arm.body)?;
                    self.branch_depth -= 1;

                    self.builder
                        .ins()
                        .jump(merge_block, &[BlockArg::Value(body_val)]);
                }
                crate::ast::Pattern::Var { name, .. } => {
                    // Bind scrutinee to variable, always matches
                    self.push_scope();
                    let var = self.fresh_var(types::I64);
                    self.builder.def_var(var, scrut_val);
                    self.variables.insert(name.clone(), var);
                    // Track binding with scrutinee type for RC
                    if let Some(ty) = &scrutinee_type {
                        self.variable_types.insert(name.clone(), ty.clone());
                        if ty.is_heap_type() {
                            self.track_binding(name.clone(), var, ty.clone());
                            // Inc because match var creates additional reference
                            self.emit_inc(scrut_val, ty);
                        }
                    }
                    self.in_tail_position = saved_tail;

                    self.branch_depth += 1;
                    let body_val = self.compile_expr(&arm.body)?;
                    self.branch_depth -= 1;

                    self.pop_scope_for_value(body_val);
                    self.builder
                        .ins()
                        .jump(merge_block, &[BlockArg::Value(body_val)]);
                }
                crate::ast::Pattern::Constructor { name, bindings, .. } => {
                    let bare = resolve_bare_name(name);
                    let ctor_info = self.type_defs.as_ref().and_then(|tds| {
                        let type_name = self.constructor_to_type.as_ref()?.get(bare)?;
                        let td = tds.get(type_name)?;
                        td.constructors.iter().find(|c| c.name == bare)
                    });

                    let (tag, _field_count, is_nullary) = match ctor_info {
                        Some(ci) => (ci.tag, ci.fields.len(), ci.fields.is_empty()),
                        None => {
                            return Err(CranelispError::CodegenError {
                                message: format!("unknown constructor: {}", name),
                                span,
                            });
                        }
                    };

                    let tag_val = self.builder.ins().iconst(types::I64, tag as i64);

                    // Resolve concrete field types for RC tracking
                    let field_types: Vec<crate::types::Type> = if let Some(st) = &scrutinee_type {
                        self.resolve_field_types(bare, st)
                    } else {
                        Vec::new()
                    };

                    if is_nullary {
                        // Compare scrutinee directly against tag value
                        let cmp = self.builder.ins().icmp(IntCC::Equal, scrut_val, tag_val);
                        let body_block = self.builder.create_block();
                        self.builder
                            .ins()
                            .brif(cmp, body_block, &[], next_block, &[]);

                        self.builder.switch_to_block(body_block);
                        self.builder.seal_block(body_block);
                        self.in_tail_position = saved_tail;

                        self.branch_depth += 1;
                        let body_val = self.compile_expr(&arm.body)?;
                        self.branch_depth -= 1;

                        self.builder
                            .ins()
                            .jump(merge_block, &[BlockArg::Value(body_val)]);
                    } else {
                        // Data constructor: check if it's a heap pointer first.
                        // For mixed types, need to check if scrut_val could be a nullary tag.
                        // Load tag from heap[0] and compare
                        let type_name = self
                            .constructor_to_type
                            .as_ref()
                            .and_then(|m| m.get(bare))
                            .cloned()
                            .unwrap_or_default();
                        let has_nullary = self
                            .type_defs
                            .as_ref()
                            .and_then(|tds| tds.get(&type_name))
                            .map(|td| td.constructors.iter().any(|c| c.fields.is_empty()))
                            .unwrap_or(false);

                        if has_nullary {
                            // Mixed type: first check if scrut is a small tag (not a pointer)
                            let max_nullary_tag = self
                                .type_defs
                                .as_ref()
                                .and_then(|tds| tds.get(&type_name))
                                .map(|td| {
                                    td.constructors
                                        .iter()
                                        .filter(|c| c.fields.is_empty())
                                        .map(|c| c.tag)
                                        .max()
                                        .unwrap_or(0)
                                })
                                .unwrap_or(0);
                            let threshold = self
                                .builder
                                .ins()
                                .iconst(types::I64, (max_nullary_tag + 1) as i64);
                            let is_heap_ptr = self.builder.ins().icmp(
                                IntCC::UnsignedGreaterThanOrEqual,
                                scrut_val,
                                threshold,
                            );
                            let heap_check_block = self.builder.create_block();
                            self.builder.ins().brif(
                                is_heap_ptr,
                                heap_check_block,
                                &[],
                                next_block,
                                &[],
                            );

                            self.builder.switch_to_block(heap_check_block);
                            self.builder.seal_block(heap_check_block);
                        }

                        let loaded_tag =
                            self.builder
                                .ins()
                                .load(types::I64, MemFlags::trusted(), scrut_val, 0);
                        let cmp = self.builder.ins().icmp(IntCC::Equal, loaded_tag, tag_val);
                        let body_block = self.builder.create_block();
                        self.builder
                            .ins()
                            .brif(cmp, body_block, &[], next_block, &[]);

                        self.builder.switch_to_block(body_block);
                        self.builder.seal_block(body_block);

                        // Load fields and bind to variables
                        self.push_scope();
                        for (fi, binding) in bindings.iter().enumerate() {
                            let offset = ((fi + 1) * 8) as i32;
                            let field_val = self.builder.ins().load(
                                types::I64,
                                MemFlags::trusted(),
                                scrut_val,
                                offset,
                            );
                            let var = self.fresh_var(types::I64);
                            self.builder.def_var(var, field_val);
                            self.variables.insert(binding.clone(), var);
                            // Track field binding with concrete type for RC
                            if let Some(ft) = field_types.get(fi) {
                                self.variable_types.insert(binding.clone(), ft.clone());
                                if ft.is_heap_type() {
                                    self.track_binding(binding.clone(), var, ft.clone());
                                    if scrutinee_is_unique {
                                        // Borrow: skip inc, mark as borrowed var.
                                        // Safe because only one arm executes and
                                        // uniqueness was verified before branching.
                                        self.mark_borrowed_var(var);
                                    } else {
                                        // Inc: extracting a field creates a new reference
                                        self.emit_inc(field_val, ft);
                                    }
                                }
                            }
                        }

                        self.in_tail_position = saved_tail;

                        self.branch_depth += 1;
                        let body_val = self.compile_expr(&arm.body)?;
                        self.branch_depth -= 1;

                        self.pop_scope_for_value(body_val);
                        self.builder
                            .ins()
                            .jump(merge_block, &[BlockArg::Value(body_val)]);
                    }
                }
            }
        }

        self.in_tail_position = false;

        // Panic block: match failed
        self.builder.switch_to_block(panic_block);
        self.builder.seal_block(panic_block);
        self.emit_panic_with_message("match failed", span)?;
        // Unreachable after panic, but cranelift needs a terminator
        let zero = self.builder.ins().iconst(types::I64, 0);
        self.builder
            .ins()
            .jump(merge_block, &[BlockArg::Value(zero)]);

        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);
        let result = self.builder.block_params(merge_block)[0];

        // RC: dec temporary scrutinee — its reference is no longer needed.
        // Var scrutinees are managed by their original scope (let-binding, outer match, etc.).
        // Field extraction in constructor patterns inc's each field, so they survive this dec.
        if scrutinee_is_temporary {
            if let Some(ty) = &scrutinee_type {
                if ty.is_heap_type() {
                    self.emit_dec(scrut_val, ty);
                }
            }
        }

        Ok(result)
    }
}
