// Lambda / closure compilation.
//
// Closure site allocation, the inner-fn body and its capture environment, and
// drop glue. A capture used in the body is duplicated
// (`design/backend/uniform-counting.md` §3). `build_closure_drop_glue`
// is called by `compile_lambda` and by `par_bind.rs`'s continuation closure
// (cross-module via the shared `impl FnCompiler`).

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{CranelispError, ErrorLocation, MonoExpr, Span, Symbol, Type};

use crate::heap::{self, HeapClosure};

use super::{CaptureRelease, CaptureReleaseKind, FnCompiler, emit_capture_dec_into};
use crate::compiler::ownership_plan::{CaptureEntry, Intro};
use crate::compiler::signature_heap_category;

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // --- Lambda expression (Ring 1: closures with captures) ---

    /// Compile a lambda expression.
    ///
    /// Strategy:
    /// 1. Determine which variables are captured from the enclosing scope.
    /// 2. Compile an inner function with signature (env_ptr, params...) -> i64
    ///    that loads captured values from the environment.
    /// 3. At the lambda site, allocate a closure: [header | code_ptr | captures...]
    /// 4. Store the inner function pointer and captured values.
    pub(crate) fn compile_lambda(
        &mut self,
        params: &[Symbol],
        body: &MonoExpr,
        span: Span,
        lambda_type: Option<&Type>,
        capture_entries: &[CaptureEntry],
    ) -> Result<Value, CranelispError> {
        let alloc_id = self
            .ctx
            .alloc_func_id
            .ok_or_else(|| CranelispError::CodegenError {
                message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                location: ErrorLocation::from_span(span),
            })?;

        // The captured names, in layout order, come from the plan (or, for a
        // synthesized spark thunk, from `duplicating_captures`).
        let captures: Vec<Symbol> = capture_entries.iter().map(|e| e.name.clone()).collect();

        // Compile the inner function as a separate function definition.
        // Signature: (env_ptr: i64, param_0: i64, ..., param_n: i64) -> i64
        //
        // The name is span-derived AND monomorphisation-discriminated
        // (FIXME 0347 defect 1): when the enclosing fn is monomorphised, N mono
        // instances share this lambda's span, so the enclosing-fn discriminator
        // keeps the N emitted symbols distinct (else the 2nd define_function
        // collides — `Duplicate definition of identifier: __lambda_…__`).
        let inner_name = format!(
            "__lambda_{}{}_{}__",
            self.inner_fn_discriminator(),
            span.start,
            span.end
        );

        let inner_param_count = 1 + params.len(); // env_ptr + user params
        let mut sig = self.module.make_signature();
        for _ in 0..inner_param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let inner_func_id = self
            .module
            .declare_function(&inner_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare lambda function: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        // Compile the inner function body using a new Cranelift context.
        self.compile_lambda_body(
            inner_func_id,
            &inner_name,
            params,
            &captures,
            body,
            span,
            lambda_type,
        )?;

        // At the lambda site: allocate closure [header | code_ptr | captures...]
        let payload_size = HeapClosure::payload_size(captures.len()) as i64;
        let base_ptr = heap::emit_alloc(&mut self.builder, self.module, alloc_id, payload_size);

        // Get the inner function address.
        let inner_func_ref = self
            .module
            .declare_func_in_func(inner_func_id, self.builder.func);
        let code_ptr = self.builder.ins().func_addr(types::I64, inner_func_ref);

        // Store code_ptr at HeapClosure::CODE_PTR_OFFSET (16).
        heap::heap_store(
            &mut self.builder,
            code_ptr,
            base_ptr,
            HeapClosure::CODE_PTR_OFFSET,
        );

        // Build closure drop glue and store pointer at DROP_GLUE_PTR_OFFSET (24).
        // Must be built BEFORE storing captures (build_closure_drop_glue needs
        // self.module which is borrowed mutably during function definition).
        let drop_glue = self.build_closure_drop_glue(&captures, span)?;
        let drop_glue_val = if let Some(glue_id) = drop_glue {
            let glue_ref = self.module.declare_func_in_func(glue_id, self.builder.func);
            self.builder.ins().func_addr(types::I64, glue_ref)
        } else {
            self.builder.ins().iconst(types::I64, 0)
        };
        heap::heap_store(
            &mut self.builder,
            drop_glue_val,
            base_ptr,
            HeapClosure::DROP_GLUE_PTR_OFFSET,
        );

        // Store each captured value: moved when the plan says it is the
        // binder's last use, otherwise duplicated, so the environment owns
        // one reference to each, which its drop glue releases.
        for (i, entry) in capture_entries.iter().enumerate() {
            if let Some(cap_val) = self.capture_value(entry) {
                heap::heap_store(
                    &mut self.builder,
                    cap_val,
                    base_ptr,
                    HeapClosure::capture_offset(i),
                );
            }
        }

        Ok(base_ptr)
    }

    /// Build a closure drop glue function: `(ptr: i64) -> ()`.
    ///
    /// For each heap-typed capture, loads the value from the closure env
    /// at its known offset and emits `rc_dec` (with guard for Mixed types).
    /// Returns `None` if no captures are heap-typed.
    ///
    /// `pub(crate)` because `par_bind.rs`'s continuation-closure allocation
    /// calls it cross-module on the shared `impl FnCompiler`.
    pub(crate) fn build_closure_drop_glue(
        &mut self,
        captures: &[Symbol],
        span: Span,
    ) -> Result<Option<cranelift_module::FuncId>, CranelispError> {
        // Collect (capture_index, release mechanism) for heap-typed captures —
        // the capture layout specific this builder supplies. The capture's TYPE
        // decides both membership and mechanism (`CaptureRelease::classify`):
        // a `Fn`-typed capture is a closure box that owns its own captures and
        // must be released through its embedded drop glue (FIXME 0749).
        // S118 slice S4 (§7.4): the glue BODY builds in a separate Cranelift
        // context, so every owning slot's canonical glue is requested HERE,
        // before that builder exists, and the body emits only the call.
        let mut heap_captures: Vec<(usize, CaptureRelease)> = Vec::new();
        for (i, cap_name) in captures.iter().enumerate() {
            let Some(ty) = self.lookup_type(cap_name) else {
                continue;
            };
            let category = signature_heap_category(&ty, Some(self.ctx.symbol_tables));
            let Some(kind) =
                CaptureReleaseKind::classify(category, matches!(ty, cranelisp_types::Type::Fn(..)))
            else {
                continue;
            };
            match kind {
                CaptureReleaseKind::ClosureBox => {
                    heap_captures.push((i, CaptureRelease::ClosureBox));
                }
                CaptureReleaseKind::Glue => {
                    if let Some(id) = self.request_capture_glue(&ty)? {
                        heap_captures.push((i, CaptureRelease::Glue(id)));
                    }
                }
            }
        }

        // Naming identity (FIXME 0350): span-derived AND mono-discriminated via
        // the SAME `inner_fn_discriminator()` scheme as the lambda body name, so
        // the body+drop-glue symbol pair stay paired per mono instance. The name
        // is composed by the ONE naming fn (S111 R6 §4.1,
        // `resolution::closure_drop_glue_name`); the envelope
        // (`emit_capture_dec_glue`) owns idempotency + declare/build/define.
        let glue_name =
            crate::compiler::closure_drop_glue_name(&self.inner_fn_discriminator(), span);
        self.emit_capture_dec_glue(&glue_name, span, &heap_captures)
    }

    /// The shared capture-dec drop-glue envelope (S111 R6 §4 — the ONE
    /// glue-emission helper owning naming identity + idempotency + the
    /// `FunctionBuilder` boilerplate; the closure and auto-curry builders supply
    /// only their capture layout `heap_captures`). Their bodies were byte-for-byte
    /// identical flat capture-dec loops (a fixed `for (idx, cat)` over the closure
    /// env), so the body is baked here rather than passed as a closure — sidestepping
    /// the §4.3 `&mut self` re-borrow the generic-body shape would face.
    ///
    /// Envelope responsibilities (§4.1): (1) **idempotency skip** — a `get_name`
    /// hit means the SAME mono instance at the SAME span, so `heap_captures` are
    /// identical by construction and returning the existing FuncId is sound (the
    /// closure mirror GAINS this skip here — deliberate hardening closing the last
    /// asymmetry with the curry/ADT builders; byte-identical in practice because
    /// the span+disc name is unique per mono, so it never fires); (2) declare
    /// `Linkage::Local`, one `i64` (object ptr) param, no return; (3) the
    /// FunctionBuilder boilerplate; (4) the flat capture-dec loop; (5) finish +
    /// `define_function`, mapping errors to `CodegenError` with `span`.
    pub(crate) fn emit_capture_dec_glue(
        &mut self,
        glue_name: &str,
        span: Span,
        heap_captures: &[(usize, CaptureRelease)],
    ) -> Result<Option<cranelift_module::FuncId>, CranelispError> {
        if heap_captures.is_empty() {
            return Ok(None);
        }

        // Idempotency skip (§4.1): `declare_function` is idempotent but
        // `define_function` is NOT — a second definition of the same identifier
        // is a hard `Duplicate definition` error (e.g. a create-gate compiling
        // the SAME expression on BOTH its lenient and sequential arms — the
        // 0350 / ledger-25 class). A `get_name` hit ⇒ same mono+span ⇒ identical
        // captures ⇒ share the one definition.
        if let Some(cranelift_module::FuncOrDataId::Func(existing_id)) =
            self.module.get_name(glue_name)
        {
            return Ok(Some(existing_id));
        }

        let dealloc_id = self.ctx.dealloc_func_id;

        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // object ptr

        let glue_func_id = self
            .module
            .declare_function(glue_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare capture drop glue fn: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        let mut ctx = self.module.make_context();
        let mut func_ctx = FunctionBuilderContext::new();
        ctx.func.signature = sig;

        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);

        let closure_ptr = builder.block_params(entry)[0];

        // For each heap-typed capture, load from its offset and release it by
        // its classified mechanism (FIXME 0749 — a closure-box capture goes
        // through its EMBEDDED drop glue, never a bare dec).
        for (cap_idx, release) in heap_captures {
            let cap_val = heap::heap_load(
                &mut builder,
                closure_ptr,
                HeapClosure::capture_offset(*cap_idx),
            );
            emit_capture_dec_into(&mut builder, self.module, *release, cap_val, dealloc_id);
        }

        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize();

        self.module
            .define_function(glue_func_id, &mut ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define capture drop glue fn: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        Ok(Some(glue_func_id))
    }

    /// Compile the body of a lambda as a separate JIT function.
    ///
    /// The inner function has signature (env_ptr, params...) -> i64.
    /// Captured values are loaded from the environment.
    #[allow(clippy::too_many_arguments)] // +inner_name seeds the body compiler's discriminator
    fn compile_lambda_body(
        &mut self,
        func_id: cranelift_module::FuncId,
        inner_name: &str,
        params: &[Symbol],
        captures: &[Symbol],
        body: &MonoExpr,
        span: Span,
        lambda_type: Option<&Type>,
    ) -> Result<(), CranelispError> {
        // Build the inner function using a separate codegen context.
        let mut inner_ctx = self.module.make_context();
        let mut inner_func_ctx = FunctionBuilderContext::new();

        // Signature: (env_ptr, params...) -> i64
        let total_params = 1 + params.len();
        for _ in 0..total_params {
            inner_ctx
                .func
                .signature
                .params
                .push(AbiParam::new(types::I64));
        }
        inner_ctx
            .func
            .signature
            .returns
            .push(AbiParam::new(types::I64));

        let mut builder = FunctionBuilder::new(&mut inner_ctx.func, &mut inner_func_ctx);

        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let block_params = builder.block_params(entry_block).to_vec();
        let env_ptr = block_params[0];

        // The captures' types, read from the ENCLOSING environment before the
        // inner compiler takes this compiler's module borrow.
        let capture_types: Vec<Option<Type>> = captures
            .iter()
            .map(|cap_name| self.lookup_type(cap_name))
            .collect();

        let plan = Self::plan_body(body, params, captures, inner_name)?;
        let mut inner_compiler = FnCompiler::inner(
            builder,
            self.module,
            self.ctx.clone(),
            self.glue,
            params.len(),
            plan,
        );

        // Seed the inner compiler's discriminator with this lambda's
        // globally-unique name. Inner functions emitted within the body
        // (nested lambdas, spark thunks, fn-as-value/gate wrappers) are named by
        // `inner_fn_discriminator()`, which keys off `current_fn_name`. Without a
        // seed the inner compiler resets it to `None`, so the same source span
        // reached via two distinct compilation paths — e.g. the create-gate
        // (lenient-eval.md §3.6.2) compiles the same subexpression on BOTH arms,
        // and each gate arm's all-lenient thunk descent re-enters fresh inner
        // compilers — would re-emit identical module-global names and the second
        // `define_function` would collide (`Duplicate definition of identifier`).
        // Seeding with the unique lambda name makes every name within the body
        // uniquely prefixed. TCO self-call detection is unaffected: inner
        // compilers have `tail_loop_block = None`, which gates the self-call fast
        // path regardless of `current_fn_name`.
        inner_compiler.current_fn_name = Some(Symbol::from(inner_name));

        // Bind captured variables from the environment, with their types, into
        // the CAPTURE ENVIRONMENT: the closure env's drop glue releases them,
        // so every use in the body duplicates (the body's plan says so).
        for (i, cap_name) in captures.iter().enumerate() {
            let cap_val = heap::heap_load(
                &mut inner_compiler.builder,
                env_ptr,
                HeapClosure::capture_offset(i),
            ); // capture_i: i64
            inner_compiler.bind_capture(cap_name, cap_val, capture_types.get(i).cloned().flatten());
        }

        // The lambda's inferred type supplies parameter types, so an unused
        // parameter (e.g. `_s` in `(fn [_s] 42)`) still has the type its drop
        // at introduction needs.
        let lambda_param_types: Vec<Option<Type>> =
            if let Some(Type::Fn(param_types, _)) = lambda_type {
                param_types.iter().map(|t| Some(t.clone())).collect()
            } else {
                vec![None; params.len()]
            };

        // Bind lambda parameters (after env_ptr): the body owns each one.
        for (i, param_name) in params.iter().enumerate() {
            let val = block_params[i + 1];
            let ty = match lambda_param_types.get(i) {
                Some(Some(ty)) => Some(ty.clone()),
                _ => Self::derive_param_type_from_body(body, param_name),
            };
            inner_compiler.bind_binder(Intro::Param(i), param_name, val, ty)?;
        }

        let result = inner_compiler.compile_expr(body)?;
        inner_compiler.builder.ins().return_(&[result]);
        inner_compiler.builder.seal_all_blocks();
        inner_compiler.builder.finalize();

        // Define the function in the JIT module.
        self.module
            .define_function(func_id, &mut inner_ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define lambda function: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    // Relocated crate-root tests (FIXME 0495 step 1); harness via
    // `crate::test_support`. Verbatim bodies from the former `src/tests.rs`.
    use crate::test_support::*;

    // spec: 04-expressions §4.5 — lambda capture, closure allocation, and indirect call
    #[test]
    fn test_compile_lambda_closure() {
        // (let [n 5] ((fn [x] (+ n x)) 10))
        // This tests: lambda capture of 'n', closure allocation, closure call.
        use cranelisp_types::ResolvedCall;

        let add_span = Span::new(30, 37);
        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            add_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("add-i64"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("n"),
                Expr::IntLit {
                    value: 5,
                    span: Span::new(5, 6),
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Lambda {
                    params: vec![(Symbol::from("x"), None)],
                    body: Box::new(Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("+"),
                            span: Span::new(31, 32),
                            resolved_call: None,
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var {
                                name: Symbol::from("n"),
                                span: Span::new(33, 34),
                                resolved_call: None,
                                inferred_type: None,
                            },
                            Expr::Var {
                                name: Symbol::from("x"),
                                span: Span::new(35, 36),
                                resolved_call: None,
                                inferred_type: None,
                            },
                        ],
                        span: add_span,
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    span: Span::new(10, 40),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 10,
                    span: Span::new(42, 44),
                    inferred_type: None,
                }],
                span: Span::new(10, 45),
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(0, 46),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            resolved_targets: HashMap::new(),
            pattern_ctors: HashMap::new(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "closure should compile: {result:?}");
        assert_eq!(result.unwrap(), 15, "5 + 10 = 15");
    }

    // spec: design/backend/uniform-counting.md §3 — a capture used in a body
    // is duplicated, so a closure returning its capture hands the caller its
    // own reference and the environment's drop glue releases the other.
    //
    // Test shape: `(let [s "hello"] ((fn [_] s) 0))`. The returned pointer is
    // still live after the closure's release and reads back as "hello".
    #[test]
    fn lambda_returning_its_capture_hands_the_caller_a_live_reference() {
        // AST: (let [s "hello"] ((fn [_] s) 0))
        //
        // Explicit `inferred_type` on the String literal so the binder
        // records `s: String`: the capture is then a counted String slot, and
        // the plan's duplicate of its body occurrence is a real increment.
        let string_ty = Type::String;
        let s_span = Span::new(5, 12);
        let lam_body_span = Span::new(20, 21);
        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("s"),
                Expr::StringLit {
                    value: "hello".to_string(),
                    span: s_span,
                    inferred_type: Some(Box::new(string_ty.clone())),
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Lambda {
                    params: vec![(Symbol::from("_"), None)],
                    body: Box::new(Expr::Var {
                        name: Symbol::from("s"),
                        span: lam_body_span,
                        resolved_call: None,
                        inferred_type: Some(Box::new(string_ty.clone())),
                    }),
                    span: Span::new(15, 22),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 0,
                    span: Span::new(24, 25),
                    inferred_type: None,
                }],
                span: Span::new(14, 26),
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(0, 27),
            inferred_type: None,
        };

        let check = empty_check();
        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(
            result.is_ok(),
            "captured-heap-return should compile and run: {result:?}"
        );
        let ptr = result.unwrap();
        // Heap pointer (> NULLARY_TAG_THRESHOLD).
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // The returned pointer is STILL LIVE: the body's occurrence of the
        // capture was duplicated, so releasing the closure environment
        // dropped only the environment's own reference.
        #[cfg(debug_assertions)]
        assert!(
            cranelisp_intrinsics::alloc::is_live(ptr as usize),
            "returned string pointer must still be live after lambda return; \
         a returned capture is a duplicate, not the environment's reference"
        );

        // Readable round-trip: the contents survived the environment's
        // release.
        let s = unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(ptr) };
        assert_eq!(s, "hello", "captured string must round-trip");

        // The test owns the returned reference as the receiver of the
        // body's result; release it here.
        cranelisp_intrinsics::alloc::heap_dealloc(ptr);
    }
}
