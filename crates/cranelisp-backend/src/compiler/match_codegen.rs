// Match expression codegen.
//
// compile_match, compile_constructor_pattern, emit_match_panic
//
// Ring 1: supports data constructors with field bindings and
// mixed nullary/data ADT discrimination.

use cranelift::prelude::*;
use cranelift_module::Module;

use cranelisp_types::{ErrorLocation, CranelispError, MonoExpr, MonoMatchArm, Pattern, Span, Symbol};
use crate::heap::{HeapCategory, RcAtomicity};

use crate::heap::{self, HeapAdt};

use super::{FnCompiler, MatchContext, collect_var_ids_from_type, signature_heap_category, substitute_type_inline};

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // --- Match expression ---

    pub(crate) fn compile_match(
        &mut self,
        scrutinee: &MonoExpr,
        arms: &[MonoMatchArm],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let saved_tail = self.in_tail_position;

        // Scrutinee is never in tail position, and is never itself a tail-call
        // arg — it is consumed by the match, not forwarded to the loop param.
        // Clear `tail_arg_protect` so a heap binding aliased in the scrutinee is
        // not spuriously protected; the arm bodies restore it below.
        let saved_protect = self.tail_arg_protect;
        self.in_tail_position = false;
        self.tail_arg_protect = false;
        let scrut_val = self.compile_expr(scrutinee)?;
        self.tail_arg_protect = saved_protect;

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
                    // Always matches -- compile body and jump to merge. A
                    // wildcard arm pushes no bindings, so the body's value is the
                    // arm value directly; protect it when this match is a tail-
                    // call arg aliasing a live let-binding (F1 UAF cure).
                    self.in_tail_position = saved_tail;
                    let body_val = self.compile_expr(&arm.body)?;
                    let body_val =
                        self.maybe_protect_tail_arg_alias(&arm.body, body_val);
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
                        scrut_type: Some(scrutinee.ty().to_type()),
                        next_block,
                        merge_block,
                        saved_tail,
                    };
                    // `Pattern::Constructor.name` is a syntactic-stage
                    // `SymbolRef` (S70). Its `Display` yields `module/name`
                    // (qualified) or bare `name` — exactly the lookup string
                    // `lookup_constructor` parses.
                    let ctor_name = Symbol::from(name.to_string());
                    self.compile_constructor_pattern(
                        &ctor_name, bindings, &match_ctx, &arm.body, span,
                    )?;
                }
            }
        }

        // Panic block: non-exhaustive match.
        self.builder.switch_to_block(panic_block);
        self.builder.seal_block(panic_block);
        self.emit_match_panic()?;

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
        scrutinee: &MonoExpr,
        body: &MonoExpr,
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
        self.variable_types.insert(name.clone(), scrutinee.ty().to_type());

        // P7 fix: Only register the alias in scope_stack for RC cleanup
        // when the scrutinee is NOT an existing variable. When the scrutinee
        // IS a variable, the original variable's owning scope will dec it.
        // Registering the alias would cause a double-dec: once for the
        // alias's scope exit, and once for the original variable's scope exit.
        let is_alias = matches!(scrutinee, MonoExpr::Var { .. });
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
        // In a tail-call-arg context (`(recur (match … v))`) use the tail-arg
        // alias protection instead of `protect_return_value`: the tail-jump flush
        // is the balancing dec, not a caller, so an unconditional protect inc on
        // a fresh arm value would leak. `maybe_protect_tail_arg_alias` incs only a
        // direct scope-binding-`Var` arm the flush will dec (F1 UAF cure).
        if self.tail_arg_protect {
            self.maybe_protect_tail_arg_alias(body, body_val);
        } else {
            self.protect_return_value(&skip_var, body_val, body);
        }
        self.pop_scope_with_cleanup(skip_var.as_ref());
        self.builder.ins().jump(merge_block, &[body_val]);

        Ok(())
    }

    /// Emit rc_dec for the scrutinee if it is a heap-typed temporary.
    ///
    /// Variable references are dec'd by their owning scope -- only
    /// temporaries (non-Var expressions) need dec here.
    ///
    /// ADT field cleanup is done inside the dealloc path (RC=0) via
    /// `emit_rc_dec_with_inline_drop_glue`, not unconditionally.
    /// This prevents double-free when fields are borrowed by pattern bindings.
    fn dec_temporary_scrutinee(&mut self, scrutinee: &MonoExpr, scrut_val: Value) {
        let is_temp = !matches!(scrutinee, MonoExpr::Var { .. });
        if is_temp {
                let scrut_ty = scrutinee.ty().to_type();
                let category = HeapCategory::classify(scrutinee.ty(), Some(self.ctx.symbol_tables));
                if matches!(category, HeapCategory::AlwaysHeap | HeapCategory::Mixed) {
                    // Vec-typed scrutinee: route through vec_drop so element
                    // RCs and the data buffer are released on rc=0.
                    if let Some(elem_ty) =
                        crate::compiler::vec_codegen::vec_element_type(&scrut_ty)
                    {
                        let elem_ty = elem_ty.clone();
                        let span = cranelisp_types::Span::new(0, 0);
                        let _ = self.emit_vec_aware_rc_dec(scrut_val, &elem_ty, span, RcAtomicity::Atomic);
                        return;
                    }
                    let needs_guard = matches!(category, HeapCategory::Mixed);
                    self.emit_rc_dec_with_inline_drop_glue(
                        scrut_val, &scrut_ty, self.ctx.dealloc_func_id, needs_guard,
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
        body: &MonoExpr,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Look up constructor info. lookup_constructor handles both
        // qualified names ("macros/SCons") and bare names ("Some").
        let (fqtn, ctor_info) =
            self.ctx
                .lookup_constructor(name.as_ref())
                .ok_or_else(|| CranelispError::CodegenError {
                    message: format!("unknown constructor: {name}"),
                    location: ErrorLocation::from_span(span),
                })?;
        let _type_def =
            self.ctx
                .lookup_type_def(&fqtn)
                .ok_or_else(|| CranelispError::CodegenError {
                    message: format!("unknown type: {fqtn}"),
                    location: ErrorLocation::from_span(span),
                })?;

        let tag = ctor_info.tag;
        let is_nullary = ctor_info.fields.is_empty();
        let is_mixed = heap::is_mixed_adt(self.ctx.symbol_tables, &fqtn);

        if is_nullary && bindings.is_empty() {
            self.compile_nullary_pattern(
                tag, is_mixed, match_ctx, body,
            )
        } else if !is_nullary && bindings.len() == ctor_info.fields.len() {
            self.compile_data_pattern(
                name, tag, is_mixed, bindings, match_ctx, body,
            )
        } else {
            Err(CranelispError::CodegenError {
                message: format!(
                    "constructor '{name}' has {} fields but pattern has {} bindings",
                    ctor_info.fields.len(),
                    bindings.len()
                ),
                location: ErrorLocation::from_span(span),
            })
        }
    }

    /// Compile a nullary constructor pattern (bare tag comparison).
    fn compile_nullary_pattern(
        &mut self,
        tag: usize,
        is_mixed: bool,
        match_ctx: &MatchContext,
        body: &MonoExpr,
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
        body: &MonoExpr,
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

        // Auto-upgrade: if the return value is a borrowed var, inc it to
        // create an owning reference. Borrowed vars share the scrutinee's
        // reference, but the return value must survive the scrutinee's
        // eventual dec. This is the sketch's "auto-upgrade borrowed on return".
        if let Some(ref sv) = skip_var
            && self.borrowed_vars.contains(sv)
        {
            if let Some(ty) = self.variable_types.get(sv).cloned() {
                let category = signature_heap_category(&ty, Some(self.ctx.symbol_tables));
                // B3.3-R (§5.1): the auto-upgrade materialization inc is always
                // atomic. This was a through-binding site (per-binding Confined
                // carrier), dropped as dead + latent-race code (/review B3.3) —
                // the analysis produces no confined let-bindings today. The
                // `_atomicity` mechanism is retained (probe-reachable); it is fed
                // `Atomic` here.
                let atomicity = RcAtomicity::Atomic;
                match category {
                    HeapCategory::AlwaysHeap => {
                        heap::emit_rc_inc_atomicity(
                            &mut self.builder, self.module, body_val, atomicity,
                        );
                    }
                    HeapCategory::Mixed => {
                        heap::emit_rc_inc_guarded_atomicity(
                            &mut self.builder, self.module, body_val, atomicity,
                        );
                    }
                    HeapCategory::NeverHeap => {}
                }
            }
        } else if self.tail_arg_protect {
            // Tail-call-arg context: the tail-jump flush is the balancing dec
            // (not a caller), so protect only a direct scope-binding-`Var` arm
            // the flush will dec — never an unconditional inc on a fresh value,
            // which would leak here (F1 UAF cure).
            self.maybe_protect_tail_arg_alias(body, body_val);
        } else {
            self.protect_return_value(&skip_var, body_val, body);
        }

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
    /// variables. Field bindings are BORROWED from the scrutinee.
    ///
    /// Borrowed semantics: no inc on extraction, no dec at scope exit.
    /// The scrutinee's RC management handles field cleanup when the
    /// scrutinee itself is freed (via drop glue in the dealloc path).
    ///
    /// This prevents double-free: if a field is independently passed to
    /// a consuming function (which inc's/dec's it), the field's RC
    /// tracks those independent references correctly. The scrutinee's
    /// eventual dealloc-path drop glue provides the final dec.
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

            // Record the field type for RC classification (needed by
            // protect_return_value and consuming arg lists). Ctor/accessor field
            // types come from the SIGNATURE (concrete-boundary-type.md §3.1.1,
            // FIXME 0391 site 3): convert the field `Type` → `ConcreteType` here
            // (must succeed — §3.11.1 guarantees concreteness upstream).
            if let Some(ft) = field_types.get(i) {
                let category = signature_heap_category(ft, Some(self.ctx.symbol_tables));
                if matches!(category, HeapCategory::AlwaysHeap | HeapCategory::Mixed) {
                    self.variable_types.insert(binding_name.clone(), ft.clone());
                    // Mark as borrowed: skip scope-exit dec (owner handles cleanup).
                    self.mark_borrowed(binding_name);
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

        // Look up the constructor and its parent type.
        // lookup_constructor handles both qualified and bare names.
        let (fqtn, ctor_info) = match self.ctx.lookup_constructor(ctor_name.as_ref()) {
            Some(pair) => pair,
            None => return Vec::new(),
        };

        // Look up the type definition.
        let type_def = match self.ctx.lookup_type_def(&fqtn) {
            Some(td) => td,
            None => return Vec::new(),
        };

        // Use the constructor info directly.
        let ctor = &ctor_info;

        // Try to get the scrutinee's concrete type from the match context.
        // This gives us e.g. `ADT("Option", [String])` which we can use
        // to substitute type variables in the field types.
        let concrete_type_args: Vec<Type> = match_ctx.scrut_type.as_ref()
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
        for c in &self.ctx.constructor_metas(&type_def) {
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

    /// Emit a runtime panic for non-exhaustive match.
    ///
    /// Calls `runtime_panic("match failed")` so that `catch_unwind` at the
    /// REPL eval boundary can recover, then emits a trailing trap as an
    /// unreachable terminator (Cranelift requires one).
    fn emit_match_panic(&mut self) -> Result<(), CranelispError> {
        let panic_id = self.ctx.panic_func_id.ok_or_else(|| {
            CranelispError::CodegenError {
                message: "runtime/panic not declared".into(),
                location: ErrorLocation::from_span(Span::new(0, 0)),
            }
        })?;

        let msg = b"match failed";
        let data_id = self
            .module
            .declare_anonymous_data(false, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare panic data: {e}"),
                location: ErrorLocation::from_span(Span::new(0, 0)),
            })?;
        let mut desc = cranelift_module::DataDescription::new();
        desc.define(msg.to_vec().into_boxed_slice());
        self.module
            .define_data(data_id, &desc)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define panic data: {e}"),
                location: ErrorLocation::from_span(Span::new(0, 0)),
            })?;

        let gv = self.module.declare_data_in_func(data_id, self.builder.func);
        let msg_ptr = self.builder.ins().global_value(types::I64, gv);
        let msg_len = self.builder.ins().iconst(types::I64, msg.len() as i64);

        let panic_ref = self.module.declare_func_in_func(panic_id, self.builder.func);
        self.builder.ins().call(panic_ref, &[msg_ptr, msg_len]);

        // runtime_panic sets a thread-local error flag and returns.
        // Return a dummy 0 value — the caller checks take_runtime_error().
        let dummy = self.builder.ins().iconst(types::I64, 0);
        self.builder.ins().return_(&[dummy]);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    // Relocated crate-root tests (FIXME 0495 step 1); harness via
    // `crate::test_support`. Verbatim bodies from the former `src/tests.rs`.
    use crate::test_support::*;


// spec: 12-runtime §12.1.4 — data constructor heap layout [tag | fields]
#[test]
fn test_compile_adt_data_constructor() {
    // Expression: (Some 42)
    let some_span = Span::new(0, 10);
    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("Some"),
            span: Span::new(1, 5),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::IntLit {
            value: 42,
            span: Span::new(6, 8),
            inferred_type: None,
        }],
        span: some_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = empty_check();
    let tables = option_type_tables();

    let result = test_compile_and_run(&expr, &check, &tables);
    assert!(result.is_ok(), "ADT constructor should compile: {result:?}");
    let ptr = result.unwrap();
    assert!(ptr > 1024, "expected heap pointer, got {ptr}");

    // Verify the heap layout: [header(16) | tag(1) | field(42)]
    unsafe {
        let base = ptr as *const u8;
        let tag = *(base.add(16) as *const i64);
        assert_eq!(tag, 1, "tag should be 1 for Some");
        let val = *(base.add(24) as *const i64);
        assert_eq!(val, 42, "field should be 42");
    }

    cranelisp_intrinsics::alloc::heap_dealloc(ptr);
}


// spec: 04-expressions §4.8 — match expression with constructor patterns and field extraction
#[test]
fn test_compile_match_with_fields() {
    use cranelisp_types::{MatchArm, Pattern};

    // (match (Some 99) [(Some x) x (None) 0])
    let some_span = Span::new(10, 20);
    let match_span = Span::new(0, 50);
    let scrutinee = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("Some"),
            span: Span::new(11, 15),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::IntLit {
            value: 99,
            span: Span::new(16, 18),
            inferred_type: None,
        }],
        span: some_span,
        resolved_call: None,
        inferred_type: None,
    };

    let expr = Expr::Match {
        scrutinee: Box::new(scrutinee),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("Some")),
                    bindings: vec![Symbol::from("x")],
                    span: Span::new(22, 30),
                },
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: Span::new(31, 32),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(22, 32),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("None")),
                    bindings: vec![],
                    span: Span::new(34, 40),
                },
                body: Expr::IntLit {
                    value: 0,
                    span: Span::new(41, 42),
                    inferred_type: None,
                },
                span: Span::new(34, 42),
            },
        ],
        span: match_span,
        compiler_generated: false,
        inferred_type: None,
    };

    let check = empty_check();
    let tables = option_type_tables();

    let result = test_compile_and_run(&expr, &check, &tables);
    assert!(result.is_ok(), "match with fields should compile: {result:?}");
    assert_eq!(result.unwrap(), 99, "match should extract field value");
}

}
