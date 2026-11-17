// Match expression codegen.
//
// compile_match, compile_constructor_pattern, emit_match_panic
//
// Ring 1: supports data constructors with field bindings and
// mixed nullary/data ADT discrimination.

use cranelift::prelude::*;
use cranelift_module::Module;

use crate::heap::HeapCategory;
use cranelisp_types::{
    CranelispError, ErrorLocation, MonoExpr, MonoMatchArm, Pattern, Span, Symbol,
};

use crate::heap::{self, HeapAdt};

use super::ownership_plan::Intro;
use super::{FnCompiler, MatchContext};

/// A field binder records its type only when the field owns something heap,
/// which keeps a scalar field out of every counting site.
fn heap_field_type<M: Module, C, L>(
    compiler: &FnCompiler<'_, M, C, L>,
    field_types: &[cranelisp_types::ConcreteType],
    slot: usize,
) -> Option<cranelisp_types::Type>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    field_types
        .get(slot)
        .map(cranelisp_types::ConcreteType::to_type)
        .filter(|ty| compiler.is_heap_type(ty))
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // --- Match expression ---

    /// Compile a match. The match owns the scrutinee value
    /// (`uniform-counting.md` §4): a variable pattern's binder takes it, a
    /// constructor arm duplicates each used field and then drops it, and a
    /// nullary or wildcard arm drops it at entry.
    pub(crate) fn compile_match(
        &mut self,
        node: &MonoExpr,
        scrutinee: &MonoExpr,
        arms: &[MonoMatchArm],
    ) -> Result<Value, CranelispError> {
        let key = crate::compiler::ownership_plan::node_key(node);
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;
        let scrut_val = self.compile_expr(scrutinee)?;
        let scrut_ty = self.counted_type(scrutinee);

        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);

        let panic_block = self.builder.create_block();

        let mut arm_blocks: Vec<Block> = Vec::new();
        for _ in arms {
            arm_blocks.push(self.builder.create_block());
        }

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
                Pattern::Wildcard { .. } => {
                    self.emit_typed_rc_dec(scrut_val, &scrut_ty)?;
                    self.enter_arm(key, i)?;
                    self.in_tail_position = saved_tail;
                    let body_val = self.compile_expr(&arm.body)?;
                    self.builder.ins().jump(merge_block, &[body_val]);
                }
                Pattern::Var { name, .. } => {
                    self.enter_arm(key, i)?;
                    self.push_scope();
                    self.bind_binder(
                        Intro::Arm {
                            node: key,
                            arm: i,
                            slot: 0,
                        },
                        name,
                        scrut_val,
                        Some(scrut_ty.clone()),
                    )?;
                    self.in_tail_position = saved_tail;
                    let body_val = self.compile_expr(&arm.body)?;
                    self.pop_scope();
                    self.builder.ins().jump(merge_block, &[body_val]);
                }
                Pattern::Constructor {
                    name,
                    bindings,
                    span: pattern_span,
                } => {
                    let match_ctx = MatchContext {
                        scrut_val,
                        scrut_type: Some(scrut_ty.clone()),
                        next_block,
                        merge_block,
                        saved_tail,
                        match_node: key,
                        arm: i,
                    };
                    let ctor_name = Symbol::from(name.to_string());
                    self.compile_constructor_pattern(
                        &ctor_name,
                        bindings,
                        arm.resolved_ctor.as_ref(),
                        &match_ctx,
                        &arm.body,
                        *pattern_span,
                    )?;
                }
            }
        }

        // Panic block: non-exhaustive match. A panic ends the process, so it
        // owes no release.
        self.builder.switch_to_block(panic_block);
        self.builder.seal_block(panic_block);
        self.emit_match_panic()?;

        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);
        Ok(self.builder.block_params(merge_block)[0])
    }

    /// The plan's arm-entry drops, once the arm has taken the scrutinee.
    fn enter_arm(&mut self, node: usize, arm: usize) -> Result<(), CranelispError> {
        self.emit_scrutinee_drops(node)?;
        self.emit_entry_drops(node, arm)
    }

    /// Compile a constructor pattern arm.
    ///
    /// Supports both nullary constructors (bare i64 tags) and data constructors
    /// with field bindings (heap-allocated values).
    fn compile_constructor_pattern(
        &mut self,
        name: &Symbol,
        bindings: &[Symbol],
        resolved_ctor: Option<&cranelisp_types::FQSymbol>,
        match_ctx: &MatchContext,
        body: &MonoExpr,
        span: Span,
    ) -> Result<(), CranelispError> {
        // **Pattern position gets exactly ONE resolver (S109 W1.2, §10.3).** The
        // arm's `resolved_ctor` is typecheck's STORAGE identity for this pattern
        // ctor (canonical `Type.Ctor` for a sum ctor; the type-name key for a
        // product; carried from `pattern_ctors`). Read the `Def` DIRECTLY under
        // that key — NO name resolution, NO import-chain walk, NO DashMap-order
        // global fallback. This is the DC-11 cure: a scrutinee-directed
        // same-named ctor resolves to exactly the candidate typecheck picked,
        // run-to-run deterministically, instead of `lookup_constructor`'s
        // context-free re-resolution (arbitrary-iteration wrong-tag / `match
        // failed` nondeterminism).
        // W3 (S19 delete — `backend-keyed-consumer.md` §4/§5): the former
        // `None`-arm `lookup_constructor` fallback is DELETED. Since W0.b
        // typecheck is the SOLE mono-view producer and populates `resolved_ctor`
        // for EVERY codegen-reached ctor pattern — user `defn` bodies via the
        // `pattern_ctors` sidecar (S109 §10), synthesised accessor bodies
        // directly at synthesis (`Span::SYNTHETIC`, structurally outside
        // span-keyed transport). A `None` here is therefore keying drift, not a
        // legitimate lenient body — fail LOUDLY (Principle 18; Rev-2
        // no-soft-fallback: no resolver remains to fall back to).
        let fq = resolved_ctor.ok_or_else(|| CranelispError::CodegenError {
            message: format!(
                "pattern constructor '{name}' reached codegen with no resolved_ctor \
                 carrier (typecheck keying drift; every ctor pattern carries its \
                 storage identity post-W0.b)"
            ),
            location: ErrorLocation::from_span(span),
        })?;
        let (fqtn, ctor_info) =
            self.ctx
                .pattern_ctor_meta(fq, match_ctx.scrut_type.as_ref(), span, &self.census)?;
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
        // R5 (§7.1): a value-flattened single-ctor type has NO heap
        // representation — its match binds the field to the scrutinee word
        // directly (no tag word, no dereference). `Value` off-toggle is never
        // yielded, so this is `false` and today's heap match path runs verbatim.
        // (A zero-field value routes to the nullary path — an `iconst tag`
        // compare that already works; only the 1-field data pattern flattens.)
        let is_value = matches!(
            HeapCategory::classify(
                &cranelisp_types::ConcreteType::ADT(fqtn.clone(), vec![]),
                Some(self.ctx.symbol_tables),
            ),
            HeapCategory::Value
        );

        if is_nullary && bindings.is_empty() {
            return self.compile_nullary_pattern(tag, is_mixed, match_ctx, body);
        }
        let field_types =
            self.ctx
                .ctor_field_types(fq, match_ctx.scrut_type.as_ref(), span, &self.census)?;
        if field_types.is_empty() || bindings.len() != field_types.len() {
            return Err(CranelispError::CodegenError {
                message: format!(
                    "constructor '{name}' has {} fields but pattern has {} bindings",
                    field_types.len(),
                    bindings.len()
                ),
                location: ErrorLocation::from_span(span),
            });
        }
        self.compile_data_pattern(
            tag,
            is_mixed,
            is_value,
            bindings,
            &field_types,
            match_ctx,
            body,
        )
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
            let is_tag =
                self.builder
                    .ins()
                    .icmp(IntCC::UnsignedLessThan, match_ctx.scrut_val, threshold);

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

        // The arm matched a bare tag, which carries no reference to release.
        self.builder.switch_to_block(body_block);
        self.builder.seal_block(body_block);
        self.enter_arm(match_ctx.match_node, match_ctx.arm)?;
        self.in_tail_position = match_ctx.saved_tail;
        let body_val = self.compile_expr(body)?;
        self.builder.ins().jump(match_ctx.merge_block, &[body_val]);
        Ok(())
    }

    /// Compile a data constructor pattern (heap-allocated, with field bindings).
    #[allow(clippy::too_many_arguments)] // +1 for the R5 `is_value` flatten hint
    fn compile_data_pattern(
        &mut self,
        tag: usize,
        is_mixed: bool,
        is_value: bool,
        bindings: &[Symbol],
        field_types: &[cranelisp_types::ConcreteType],
        match_ctx: &MatchContext,
        body: &MonoExpr,
    ) -> Result<(), CranelispError> {
        let body_block = if is_value {
            // R5 (§7.1): the scrutinee IS the flattened value word — there is no
            // heap tag to load (a `heap_load` on the bare word would dereference
            // an integer). A value type is single-constructor, so the arm always
            // matches: jump unconditionally to the body. `next_block` (no-match)
            // is unreachable for this exhaustive single-ctor arm.
            let body_block = self.builder.create_block();
            self.builder.ins().jump(body_block, &[]);
            body_block
        } else {
            self.emit_data_pattern_tag_check(tag, is_mixed, match_ctx)
        };

        self.builder.switch_to_block(body_block);
        self.builder.seal_block(body_block);

        // Duplicate each used heap field out of the scrutinee, then drop the
        // scrutinee: the arm's binders now own their fields (§4).
        let field_vals = self.load_data_pattern_fields(is_value, bindings, match_ctx);
        if !is_value {
            for (slot, &field_val) in field_vals.iter().enumerate() {
                let intro = Intro::Arm {
                    node: match_ctx.match_node,
                    arm: match_ctx.arm,
                    slot,
                };
                if self.field_is_used(intro) {
                    let ty = heap_field_type(self, field_types, slot);
                    self.emit_dup(field_val, ty.as_ref());
                }
            }
            if let Some(scrut_ty) = &match_ctx.scrut_type {
                self.emit_typed_rc_dec(match_ctx.scrut_val, scrut_ty)?;
            }
        }
        self.enter_arm(match_ctx.match_node, match_ctx.arm)?;

        self.push_scope();
        for (slot, (binding_name, field_val)) in bindings.iter().zip(field_vals).enumerate() {
            let ty = heap_field_type(self, field_types, slot);
            self.bind_field_binder(
                Intro::Arm {
                    node: match_ctx.match_node,
                    arm: match_ctx.arm,
                    slot,
                },
                binding_name,
                field_val,
                ty,
            )?;
        }

        self.in_tail_position = match_ctx.saved_tail;
        let body_val = self.compile_expr(body)?;
        self.pop_scope();
        self.builder.ins().jump(match_ctx.merge_block, &[body_val]);
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

            self.builder
                .ins()
                .brif(is_heap, tag_check_block, &[], match_ctx.next_block, &[]);
        } else {
            // Non-mixed (all data constructors): jump directly to tag check.
            self.builder.ins().jump(tag_check_block, &[]);
        }

        // Load tag from heap object and compare.
        self.builder.switch_to_block(tag_check_block);
        self.builder.seal_block(tag_check_block);

        let heap_tag = heap::heap_load(&mut self.builder, match_ctx.scrut_val, HeapAdt::TAG_OFFSET); // tag: i64
        let expected_tag = self.builder.ins().iconst(types::I64, tag as i64);
        let cmp = self
            .builder
            .ins()
            .icmp(IntCC::Equal, heap_tag, expected_tag);
        self.builder
            .ins()
            .brif(cmp, body_block, &[], match_ctx.next_block, &[]);

        body_block
    }

    /// Load the fields a data pattern binds. A value-flattened scrutinee IS
    /// its single payload word (R5, §7.1), so its field is the scrutinee itself.
    fn load_data_pattern_fields(
        &mut self,
        is_value: bool,
        bindings: &[Symbol],
        match_ctx: &MatchContext,
    ) -> Vec<Value> {
        (0..bindings.len())
            .map(|i| {
                if is_value {
                    match_ctx.scrut_val
                } else {
                    heap::heap_load(
                        &mut self.builder,
                        match_ctx.scrut_val,
                        HeapAdt::field_offset(i),
                    )
                }
            })
            .collect()
    }

    /// Raise `"match failed"`: every arm's test failed.
    fn emit_match_panic(&mut self) -> Result<(), CranelispError> {
        let span = Span::new(0, 0);
        let panic_id = crate::raise::declared(self.ctx.panic_func_id, span)?;
        crate::raise::emit_raise(
            &mut self.builder,
            self.module,
            panic_id,
            crate::raise::PanicSource::MatchFailed,
            span,
        )
    }
}

#[cfg(test)]
mod synthetic_scrutinee_tests;

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

        // W1 (KC-W0-6): the S3/S4 ctor `Apply` now reads the callee Var's carrier.
        // `option_type_tables` stores `Some` bare in `main`, so the storage FQ is
        // `main/Some` — `ctor_meta_at` reads the Constructor Def there.
        let mut check = empty_check();
        check.resolved_targets.insert(
            Span::new(1, 5),
            cranelisp_types::FQSymbol {
                module: ModuleFullPath::from("main"),
                symbol: Symbol::from("Some"),
            },
        );
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

        // W1 (KC-W0-6): the scrutinee `(Some 99)` ctor `Apply` reads the callee Var
        // carrier (`main/Some`, the bare storage key in `option_type_tables`).
        // W3 (KC-W0-6): the S19 `lookup_constructor` fallback is deleted, so each
        // match ARM ctor pattern now REQUIRES a `pattern_ctors` carrier keyed by the
        // pattern span → the ctor's storage FQ (both bare in `main`).
        let mut check = empty_check();
        check.resolved_targets.insert(
            Span::new(11, 15),
            cranelisp_types::FQSymbol {
                module: ModuleFullPath::from("main"),
                symbol: Symbol::from("Some"),
            },
        );
        check.pattern_ctors.insert(
            Span::new(22, 30),
            cranelisp_types::FQSymbol {
                module: ModuleFullPath::from("main"),
                symbol: Symbol::from("Some"),
            },
        );
        check.pattern_ctors.insert(
            Span::new(34, 40),
            cranelisp_types::FQSymbol {
                module: ModuleFullPath::from("main"),
                symbol: Symbol::from("None"),
            },
        );
        let tables = option_type_tables();

        let result = test_compile_and_run(&expr, &check, &tables);
        assert!(
            result.is_ok(),
            "match with fields should compile: {result:?}"
        );
        assert_eq!(result.unwrap(), 99, "match should extract field value");
    }
}
