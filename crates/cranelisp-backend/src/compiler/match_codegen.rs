// Match expression codegen.
//
// compile_match, compile_constructor_pattern, emit_match_panic
//
// Ring 1: supports data constructors with field bindings and
// mixed nullary/data ADT discrimination.

use cranelift::prelude::*;

use cranelisp_types::{CranelispError, Expr, MatchArm, Pattern, Span, Symbol};

use crate::heap::{self, HeapAdt};

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
                    self.compile_constructor_pattern(
                        name, bindings, &match_ctx, &arm.body, span,
                    )?;
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
    ///
    /// Supports both nullary constructors (bare i64 tags) and data constructors
    /// with field bindings (heap-allocated values).
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
        let is_mixed = heap::is_mixed_adt(self.ctx.type_defs, type_name);

        if is_nullary && bindings.is_empty() {
            self.compile_nullary_pattern(
                tag, is_mixed, match_ctx, body,
            )
        } else if !is_nullary && bindings.len() == ctor.fields.len() {
            self.compile_data_pattern(
                tag, is_mixed, bindings, match_ctx, body,
            )
        } else {
            Err(CranelispError::CodegenError {
                message: format!(
                    "constructor '{name}' has {} fields but pattern has {} bindings",
                    ctor.fields.len(),
                    bindings.len()
                ),
                span,
            })
        }
    }

    /// Compile a nullary constructor pattern (bare tag comparison).
    fn compile_nullary_pattern(
        &mut self,
        tag: usize,
        is_mixed: bool,
        match_ctx: &MatchContext,
        body: &Expr,
    ) -> Result<(), CranelispError> {
        let body_block = self.builder.create_block();

        if is_mixed {
            // Mixed ADT: first check that scrutinee < NULLARY_TAG_THRESHOLD
            // (i.e., it's a nullary tag, not a heap pointer).
            let threshold = self
                .builder
                .ins()
                .iconst(types::I64, heap::NULLARY_THRESHOLD_I64);
            let is_tag = self.builder.ins().icmp(
                IntCC::UnsignedLessThan,
                match_ctx.scrut_val,
                threshold,
            );

            let tag_check_block = self.builder.create_block();
            self.builder
                .ins()
                .brif(is_tag, tag_check_block, &[], match_ctx.next_block, &[]);

            self.builder.switch_to_block(tag_check_block);
            self.builder.seal_block(tag_check_block);

            // Now compare the tag value.
            let tag_val = self.builder.ins().iconst(types::I64, tag as i64);
            let cmp = self
                .builder
                .ins()
                .icmp(IntCC::Equal, match_ctx.scrut_val, tag_val);
            self.builder
                .ins()
                .brif(cmp, body_block, &[], match_ctx.next_block, &[]);
        } else {
            // Non-mixed: compare scrutinee directly against tag value.
            let tag_val = self.builder.ins().iconst(types::I64, tag as i64);
            let cmp = self
                .builder
                .ins()
                .icmp(IntCC::Equal, match_ctx.scrut_val, tag_val);
            self.builder
                .ins()
                .brif(cmp, body_block, &[], match_ctx.next_block, &[]);
        }

        self.builder.switch_to_block(body_block);
        self.builder.seal_block(body_block);
        self.in_tail_position = match_ctx.saved_tail;
        let body_val = self.compile_expr(body)?;
        self.builder
            .ins()
            .jump(match_ctx.merge_block, &[body_val]);

        Ok(())
    }

    /// Compile a data constructor pattern (heap-allocated, with field bindings).
    fn compile_data_pattern(
        &mut self,
        tag: usize,
        is_mixed: bool,
        bindings: &[Symbol],
        match_ctx: &MatchContext,
        body: &Expr,
    ) -> Result<(), CranelispError> {
        let tag_check_block = self.builder.create_block();
        let body_block = self.builder.create_block();

        if is_mixed {
            // Mixed ADT: first check that scrutinee >= NULLARY_TAG_THRESHOLD
            // (i.e., it's a heap pointer, not a nullary tag).
            let threshold = self
                .builder
                .ins()
                .iconst(types::I64, heap::NULLARY_THRESHOLD_I64);
            let is_heap = self.builder.ins().icmp(
                IntCC::UnsignedGreaterThanOrEqual,
                match_ctx.scrut_val,
                threshold,
            );

            self.builder.ins().brif(
                is_heap,
                tag_check_block,
                &[],
                match_ctx.next_block,
                &[],
            );
        } else {
            // Non-mixed (all data constructors): jump directly to tag check.
            self.builder.ins().jump(tag_check_block, &[]);
        }

        // Load tag from heap object and compare.
        self.builder.switch_to_block(tag_check_block);
        self.builder.seal_block(tag_check_block);

        let heap_tag = heap::heap_load(
            &mut self.builder,
            match_ctx.scrut_val,
            HeapAdt::TAG_OFFSET,
        ); // tag: i64
        let expected_tag = self.builder.ins().iconst(types::I64, tag as i64);
        let cmp = self.builder.ins().icmp(IntCC::Equal, heap_tag, expected_tag);
        self.builder
            .ins()
            .brif(cmp, body_block, &[], match_ctx.next_block, &[]);

        // Body: bind fields from known offsets.
        self.builder.switch_to_block(body_block);
        self.builder.seal_block(body_block);

        self.push_scope();
        for (i, binding_name) in bindings.iter().enumerate() {
            let field_val = heap::heap_load(
                &mut self.builder,
                match_ctx.scrut_val,
                HeapAdt::field_offset(i),
            ); // field_i: i64
            let var = self.fresh_variable();
            self.builder.declare_var(var, types::I64);
            self.builder.def_var(var, field_val);
            self.variables.insert(binding_name.clone(), var);
            self.scope_stack
                .last_mut()
                .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                .push(binding_name.clone());
        }

        self.in_tail_position = match_ctx.saved_tail;
        let body_val = self.compile_expr(body)?;
        self.pop_scope();
        self.builder
            .ins()
            .jump(match_ctx.merge_block, &[body_val]);

        Ok(())
    }

    /// Emit a trap for non-exhaustive match.
    ///
    /// The typechecker verifies exhaustiveness at compile time, so this is
    /// a defensive backstop -- it should never be reached. We emit a Cranelift
    /// trap rather than calling a runtime function.
    fn emit_match_panic(&mut self, _scrut_val: Value) -> Result<(), CranelispError> {
        self.builder
            .ins()
            .trap(TrapCode::unwrap_user(MATCH_EXHAUSTION_TRAP));

        Ok(())
    }
}
