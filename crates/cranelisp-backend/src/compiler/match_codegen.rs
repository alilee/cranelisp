// Match expression codegen.
//
// compile_match, compile_constructor_pattern, emit_match_panic
//
// Ring 1: supports data constructors with field bindings and
// mixed nullary/data ADT discrimination.

use cranelift::prelude::*;

use cranelisp_types::{CranelispError, Expr, HeapCategory, MatchArm, Pattern, Span, Symbol};

use crate::heap::{self, HeapAdt};

use super::{FnCompiler, MatchContext, MATCH_EXHAUSTION_TRAP, bare_ctor_name, collect_var_ids_from_type, substitute_type_inline};

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
                    self.compile_var_pattern_arm(
                        name, scrut_val, scrutinee, &arm.body,
                        saved_tail, merge_block,
                    )?;
                }
                Pattern::Constructor { name, bindings, .. } => {
                    let match_ctx = MatchContext {
                        scrut_val,
                        scrut_span: scrutinee.span(),
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

        // Dec temporary scrutinee after all arms have used it.
        self.dec_temporary_scrutinee(scrutinee, scrut_val);

        Ok(self.builder.block_params(merge_block)[0])
    }

    /// Compile a variable-binding pattern arm: bind the scrutinee to a
    /// name, compile the body in a new scope, then jump to the merge block.
    fn compile_var_pattern_arm(
        &mut self,
        name: &Symbol,
        scrut_val: Value,
        scrutinee: &Expr,
        body: &Expr,
        saved_tail: bool,
        merge_block: Block,
    ) -> Result<(), CranelispError> {
        // Bind scrutinee to variable, always matches.
        self.push_scope();
        let var = self.fresh_variable();
        self.builder.declare_var(var, types::I64);
        self.builder.def_var(var, scrut_val);
        self.variables.insert(name.clone(), var);
        // Record type for RC management.
        if let Some(ty) = self.ctx.expr_types.get(&scrutinee.span()) {
            self.variable_types.insert(name.clone(), ty.clone());
        }

        // P7 fix: Only register the alias in scope_stack for RC cleanup
        // when the scrutinee is NOT an existing variable. When the scrutinee
        // IS a variable, the original variable's owning scope will dec it.
        // Registering the alias would cause a double-dec: once for the
        // alias's scope exit, and once for the original variable's scope exit.
        let is_alias = matches!(scrutinee, Expr::Var { .. });
        if !is_alias {
            self.scope_stack
                .last_mut()
                .unwrap_or_else(|| {
                    unreachable!("invariant: scope_stack non-empty")
                })
                .push(name.clone());
        }

        self.in_tail_position = saved_tail;
        let skip_var = Self::return_var_in_scope(body, self.scope_stack.last());
        let body_val = self.compile_expr(body)?;
        self.protect_return_value(&skip_var, body_val, body);
        self.pop_scope_with_cleanup(skip_var.as_ref());
        self.builder.ins().jump(merge_block, &[body_val]);

        Ok(())
    }

    /// Emit rc_dec for the scrutinee if it is a heap-typed temporary.
    ///
    /// Variable references are dec'd by their owning scope -- only
    /// temporaries (non-Var expressions) need dec here. This also emits
    /// inline drop glue for ADT fields before dec'ing the scrutinee itself.
    fn dec_temporary_scrutinee(&mut self, scrutinee: &Expr, scrut_val: Value) {
        let is_temp = !matches!(scrutinee, Expr::Var { .. });
        if is_temp
            && let Some(scrut_ty) = self.ctx.expr_types.get(&scrutinee.span()) {
                let category = HeapCategory::classify(scrut_ty, Some(self.ctx.type_defs));
                if let (Some(dealloc), HeapCategory::AlwaysHeap | HeapCategory::Mixed) =
                    (self.ctx.dealloc_func_id, category)
                {
                    let needs_guard = matches!(category, HeapCategory::Mixed);
                    // Emit inline drop glue for ADT fields before dec'ing
                    // the scrutinee itself.
                    self.emit_inline_drop_glue(scrut_val, scrut_ty, dealloc, needs_guard);

                    heap::emit_rc_dec_guarded(
                        &mut self.builder,
                        self.module,
                        scrut_val,
                        dealloc,
                        None,
                        needs_guard,
                    );
                }
            }
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
        // For module-qualified names like "macros/SCons", strip the module
        // prefix for registry lookups (which store unqualified names).
        let bare_name: &str = if let Some(slash_pos) = name.as_ref().find('/') {
            &name.as_ref()[slash_pos + 1..]
        } else {
            name.as_ref()
        };

        // Look up constructor info.
        let type_name =
            self.ctx
                .constructor_to_type
                .get(bare_name)
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
            .find(|c| c.name.as_ref() == bare_name)
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
                name, tag, is_mixed, bindings, match_ctx, body,
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
        ctor_name: &Symbol,
        tag: usize,
        is_mixed: bool,
        bindings: &[Symbol],
        match_ctx: &MatchContext,
        body: &Expr,
    ) -> Result<(), CranelispError> {
        let body_block = self.emit_data_pattern_tag_check(
            tag, is_mixed, match_ctx,
        );

        // Body: bind fields from known offsets.
        self.builder.switch_to_block(body_block);
        self.builder.seal_block(body_block);

        // Resolve concrete field types by looking at the scrutinee's type
        // and matching against the constructor's fields. This allows us to
        // determine which extracted fields are heap-typed for RC management.
        let field_types = self.resolve_field_types(ctor_name, match_ctx);

        self.push_scope();
        self.bind_data_pattern_fields(bindings, &field_types, match_ctx.scrut_val);

        self.in_tail_position = match_ctx.saved_tail;
        let skip_var = Self::return_var_in_scope(body, self.scope_stack.last());
        let body_val = self.compile_expr(body)?;
        self.protect_return_value(&skip_var, body_val, body);
        self.pop_scope_with_cleanup(skip_var.as_ref());
        self.builder
            .ins()
            .jump(match_ctx.merge_block, &[body_val]);

        Ok(())
    }

    /// Emit the heap-pointer guard (for mixed ADTs) and tag comparison
    /// for a data constructor pattern. Returns the body block where
    /// field bindings should be emitted.
    fn emit_data_pattern_tag_check(
        &mut self,
        tag: usize,
        is_mixed: bool,
        match_ctx: &MatchContext,
    ) -> Block {
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

        body_block
    }

    /// Extract fields from a data constructor and bind them as local
    /// variables, emitting rc_inc for heap-typed fields.
    ///
    /// Each heap-typed field gets its own RC reference so that when the
    /// parent ADT is dec'd/freed, the extracted binding survives.
    fn bind_data_pattern_fields(
        &mut self,
        bindings: &[Symbol],
        field_types: &[cranelisp_types::Type],
        scrut_val: Value,
    ) {
        for (i, binding_name) in bindings.iter().enumerate() {
            let field_val = heap::heap_load(
                &mut self.builder,
                scrut_val,
                HeapAdt::field_offset(i),
            ); // field_i: i64

            // AlwaysHeap: unconditional inc.
            // Mixed: guarded inc (skip for bare nullary tags).
            // NeverHeap: no inc needed.
            if let Some(ft) = field_types.get(i) {
                let category = HeapCategory::classify(ft, Some(self.ctx.type_defs));
                match category {
                    HeapCategory::AlwaysHeap => {
                        heap::emit_rc_inc(&mut self.builder, field_val);
                        self.variable_types.insert(binding_name.clone(), ft.clone());
                    }
                    HeapCategory::Mixed => {
                        heap::emit_rc_inc_guarded(&mut self.builder, field_val);
                        self.variable_types.insert(binding_name.clone(), ft.clone());
                    }
                    HeapCategory::NeverHeap => {
                        // No RC management needed.
                    }
                }
            }

            let var = self.fresh_variable();
            self.builder.declare_var(var, types::I64);
            self.builder.def_var(var, field_val);
            self.variables.insert(binding_name.clone(), var);
            self.scope_stack
                .last_mut()
                .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                .push(binding_name.clone());
        }
    }

    /// Resolve concrete field types for a constructor pattern by examining
    /// the scrutinee's type and matching type parameters against the
    /// constructor's declared field types.
    ///
    /// For `(Option String)` matching `(Some s)`, this returns `[String]`.
    /// For `(Point Int Int)` matching `(Point x y)`, returns `[Int, Int]`.
    fn resolve_field_types(
        &self,
        ctor_name: &Symbol,
        match_ctx: &MatchContext,
    ) -> Vec<cranelisp_types::Type> {
        use cranelisp_types::Type;

        // Strip module prefix for registry lookups (which store bare names).
        let bare = bare_ctor_name(ctor_name);

        // Look up the parent type name for this constructor.
        let type_name = match self.ctx.constructor_to_type.get(bare) {
            Some(tn) => tn,
            None => return Vec::new(),
        };

        // Look up the type definition.
        let type_def = match self.ctx.type_defs.get(type_name) {
            Some(td) => td,
            None => return Vec::new(),
        };

        // Find the constructor info.
        let ctor = match type_def.constructors.iter().find(|c| c.name.as_ref() == bare) {
            Some(c) => c,
            None => return Vec::new(),
        };

        // Try to get the scrutinee's concrete type from expr_types.
        // This gives us e.g. `ADT("Option", [String])` which we can use
        // to substitute type variables in the field types.
        let concrete_type_args: Vec<Type> = self.ctx.expr_types
            .get(&match_ctx.scrut_span)
            .and_then(|ty| match ty {
                Type::ADT(_, args) => Some(args.clone()),
                _ => None,
            })
            .unwrap_or_default();

        if concrete_type_args.is_empty() && !type_def.type_params.is_empty() {
            // Can't resolve field types without concrete type args.
            return ctor.fields.iter().map(|f| f.ty.clone()).collect();
        }

        if type_def.type_params.is_empty() {
            // Monomorphic type — field types are already concrete.
            return ctor.fields.iter().map(|f| f.ty.clone()).collect();
        }

        // Build a substitution map from Var ids to concrete type args.
        // Collect all unique Var ids across the type's constructors, ordered
        // by first appearance. These correspond positionally to type_params.
        let mut unique_var_ids: Vec<cranelisp_types::TypeId> = Vec::new();
        for c in &type_def.constructors {
            for field in &c.fields {
                collect_var_ids_from_type(&field.ty, &mut unique_var_ids);
            }
        }

        let subst: std::collections::HashMap<cranelisp_types::TypeId, Type> = unique_var_ids
            .iter()
            .zip(concrete_type_args.iter())
            .map(|(&id, arg)| (id, arg.clone()))
            .collect();

        // Resolve each field's type by substituting type variables.
        ctor.fields
            .iter()
            .map(|field| substitute_type_inline(&field.ty, &subst))
            .collect()
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
