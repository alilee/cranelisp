// Match expression codegen.
//
// compile_match, compile_constructor_pattern, emit_match_panic

use cranelift::prelude::*;

use cranelisp_types::{CranelispError, Expr, MatchArm, Pattern, Span, Symbol};

use super::{FnCompiler, MatchContext, MATCH_EXHAUSTION_TRAP};

impl<'a> FnCompiler<'a> {
    // --- Match expression ---

    pub(crate) fn compile_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let saved_tail = self.in_tail_position;

        // Scrutinee is never in tail position.
        self.in_tail_position = false;
        let scrut_val = self.compile_expr(scrutinee)?;

        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);

        let panic_block = self.builder.create_block();

        // Create one block per match arm.
        let mut arm_blocks: Vec<Block> = Vec::new();
        for _ in arms {
            arm_blocks.push(self.builder.create_block());
        }

        // Jump to first test (or panic if no arms).
        if arms.is_empty() {
            self.builder.ins().jump(panic_block, &[]);
        } else {
            self.builder.ins().jump(arm_blocks[0], &[]);
        }

        // Compile each arm as a test-and-branch chain.
        for (i, arm) in arms.iter().enumerate() {
            let next_block = if i + 1 < arms.len() {
                arm_blocks[i + 1]
            } else {
                panic_block
            };

            self.builder.switch_to_block(arm_blocks[i]);
            self.builder.seal_block(arm_blocks[i]);

            match &arm.pattern {
                Pattern::Wildcard { .. } => {
                    // Always matches -- compile body and jump to merge.
                    self.in_tail_position = saved_tail;
                    let body_val = self.compile_expr(&arm.body)?;
                    self.builder.ins().jump(merge_block, &[body_val]);
                }
                Pattern::Var { name, .. } => {
                    // Bind scrutinee to variable, always matches.
                    self.push_scope();
                    let var = self.fresh_variable();
                    self.builder.declare_var(var, types::I64);
                    self.builder.def_var(var, scrut_val);
                    self.variables.insert(name.clone(), var);
                    self.scope_stack
                        .last_mut()
                        .unwrap_or_else(|| {
                            unreachable!("invariant: scope_stack non-empty")
                        })
                        .push(name.clone());

                    self.in_tail_position = saved_tail;
                    let body_val = self.compile_expr(&arm.body)?;
                    self.pop_scope();
                    self.builder.ins().jump(merge_block, &[body_val]);
                }
                Pattern::Constructor { name, bindings, .. } => {
                    let match_ctx = MatchContext {
                        scrut_val,
                        next_block,
                        merge_block,
                        saved_tail,
                    };
                    self.compile_constructor_pattern(name, bindings, &match_ctx, &arm.body, span)?;
                }
            }
        }

        // Panic block: non-exhaustive match.
        self.builder.switch_to_block(panic_block);
        self.builder.seal_block(panic_block);
        self.emit_match_panic(scrut_val)?;

        // Merge block.
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);

        Ok(self.builder.block_params(merge_block)[0])
    }

    /// Compile a constructor pattern arm.
    fn compile_constructor_pattern(
        &mut self,
        name: &Symbol,
        bindings: &[Symbol],
        match_ctx: &MatchContext,
        body: &Expr,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Look up constructor info.
        let type_name =
            self.ctx
                .constructor_to_type
                .get(name)
                .ok_or_else(|| CranelispError::CodegenError {
                    message: format!("unknown constructor: {name}"),
                    span,
                })?;
        let type_def =
            self.ctx
                .type_defs
                .get(type_name)
                .ok_or_else(|| CranelispError::CodegenError {
                    message: format!("unknown type: {type_name}"),
                    span,
                })?;
        let ctor = type_def
            .constructors
            .iter()
            .find(|c| c.name == *name)
            .ok_or_else(|| CranelispError::CodegenError {
                message: format!("constructor '{name}' not found in type '{type_name}'"),
                span,
            })?;

        let tag = ctor.tag;
        let is_nullary = ctor.fields.is_empty();

        let tag_val = self
            .builder
            .ins()
            .iconst(types::I64, tag as i64);

        if is_nullary && bindings.is_empty() {
            // Nullary constructor: compare scrutinee directly against tag value.
            let cmp = self
                .builder
                .ins()
                .icmp(IntCC::Equal, match_ctx.scrut_val, tag_val);
            let body_block = self.builder.create_block();
            self.builder
                .ins()
                .brif(cmp, body_block, &[], match_ctx.next_block, &[]);

            self.builder.switch_to_block(body_block);
            self.builder.seal_block(body_block);
            self.in_tail_position = match_ctx.saved_tail;
            let body_val = self.compile_expr(body)?;
            self.builder
                .ins()
                .jump(match_ctx.merge_block, &[body_val]);
        } else {
            // Data constructor with fields: not supported in Ring 0 (enum-only).
            return Err(CranelispError::CodegenError {
                message: format!(
                    "data constructor patterns with bindings not supported in Ring 0: {name}"
                ),
                span,
            });
        }

        Ok(())
    }

    /// Emit a trap for non-exhaustive match.
    ///
    /// The typechecker verifies exhaustiveness at compile time, so this is
    /// a defensive backstop — it should never be reached. We emit a Cranelift
    /// trap rather than calling a runtime function.
    fn emit_match_panic(&mut self, _scrut_val: Value) -> Result<(), CranelispError> {
        self.builder
            .ins()
            .trap(TrapCode::unwrap_user(MATCH_EXHAUSTION_TRAP));

        Ok(())
    }
}
