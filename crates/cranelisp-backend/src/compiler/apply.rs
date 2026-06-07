// Function application codegen.
//
// compile_apply, compile_direct_call, compile_tail_self_call,
// emit_adt_construct, compile_extern_call,
// compile_closure_call

use cranelift::prelude::*;
use cranelift_module::Module;

use cranelisp_types::{ErrorLocation, CranelispError, Expr, ResolvedCall, Span, Symbol};
use crate::heap::HeapCategory;

use crate::heap::{self, HeapAdt, HeapClosure};
use crate::primitives_inline;

use super::FnCompiler;

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
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
                    // Per Decision 0048 §"Structural invariant — backend
                    // dep-ban": every PRIMITIVE call site MUST emit
                    // GOT-indirect dispatch against `__cranelisp_got_primitives`
                    // — never a `Linkage::Import` direct extern, which the
                    // cache-mode in-process linker (`cache::linker::Linker`)
                    // cannot resolve via dlsym. Primitives registered in
                    // `PRIMITIVES_TABLE` (see `cranelisp-primitives::PRIMITIVES_TABLE`)
                    // resolve through `resolve_got_target`'s global-fallback
                    // walk of `symbol_tables`.
                    //
                    // `is_extern_primitive` also covers Trace ADT field
                    // accessors (`cranelisp_trace_name`, `_params`, `_result`,
                    // `_children`, `_nanos`, `_first_child_nanos`) which are
                    // **int-hosted intrinsics**, registered via
                    // `JITBuilder::symbol()` from `int_intrinsics()` (see
                    // `src/session_v4.rs`). They are NOT in any module's
                    // SymbolTable. For those names, fall back to direct
                    // extern — the JIT's symbol_lookup_fn resolves them.
                    // The cache linker similarly registers them at load
                    // time via `linker.register_symbol(name, ptr)`.
                    let sym = Symbol::from(op_name.as_ref());
                    if crate::compiler::resolve_got_target(
                        self.ctx.symbol_tables,
                        self.ctx.module_aliases,
                        &self.ctx.current_module,
                        &sym,
                    )
                    .is_some()
                    {
                        return self.compile_direct_call(&sym, &arg_vals, span);
                    }
                    return self.compile_extern_call(op_name, &arg_vals, span);
                }

                // Unrecognized builtin: a platform-effect function or a
                // direct-extern. Platform functions use the consuming
                // convention — the DLL owns heap args (e.g. `CLString::own()`
                // captures the string).
                if !primitives_inline::is_known_builtin(op_name) {
                    let arg_vals = self.compile_consuming_arg_list(args)?;
                    self.in_tail_position = saved_tail;
                    // Platform GOT-indirect dispatch arm (TARGET shape;
                    // platform-interface.md §6.2/§6.3, BC §3 "the
                    // platform-interface codegen role"). When the platform
                    // entry carries the NEW shape — a populated `got_slot`
                    // adopted from the DLL's exported GOT
                    // (`__cranelisp_got_platform_<name>`, manifest index) —
                    // dispatch GOT-indirect, structurally identical to
                    // user-module GOT dispatch. Backend does NOT emit the
                    // platform GOT (the DLL exports it); it emits the
                    // dispatch, referencing the GOT data symbol as a
                    // `Linkage::Import` (resolved by `dlsym` in JIT / `ld` in
                    // `--link`).
                    //
                    // TRANSITIONAL MECHANICS: `resolve_got_target` returns
                    // `Some((module, slot))` IFF the entry carries the new
                    // `got_slot: Some(_)` shape; the as-built shape carries
                    // `got_slot: None` (the worker stores the fn ptr via a
                    // host-allocated slot + `JITBuilder::symbol(jit_name,
                    // ptr)` direct extern, §9). So this `if`-guard activates
                    // the new arm exactly when int/platform flip to the
                    // DLL-exported-GOT model, and keeps the as-built
                    // direct-extern path live until then — no mode fork, no
                    // flag (Principle 11). When the flip completes the
                    // `compile_extern_call` fallback below becomes dead for
                    // platform fns (the expected narrowing signal).
                    let sym = Symbol::from(op_name.as_ref());
                    if crate::compiler::resolve_got_target(
                        self.ctx.symbol_tables,
                        self.ctx.module_aliases,
                        &self.ctx.current_module,
                        &sym,
                    )
                    .is_some()
                    {
                        return self.compile_direct_call(&sym, &arg_vals, span);
                    }
                    // As-built fallback: direct `Linkage::Import` against the
                    // mangled jit_name (the platform fn ptr reaches the JIT via
                    // `JITBuilder::symbol(jit_name, ptr)`; the cache linker
                    // registers it identically). Retires when the GOT flip
                    // lands (§6.3 verdict).
                    return self.compile_extern_call(op_name, &arg_vals, span);
                }

                // Inline Ring 0 primitive (arithmetic, comparison, boolean).
                // All operands are NeverHeap (Int/Bool/Float) — no dec work.
                //
                // Per FIXME 0174 + `facades/backend.md` §"Non-goals / forbidden
                // patterns": `try_emit_inline_primitive` returns `None` for
                // names outside the inline table — the caller MUST fall
                // through to the GOT-indirect path. `is_known_builtin` is
                // checked above so by this point the name IS in the table,
                // but we still pattern-match the `Some` arm conservatively;
                // a None here would indicate the two tables drifted apart.
                let arg_vals = self.compile_arg_list(args)?;
                self.in_tail_position = saved_tail;
                match primitives_inline::try_emit_inline_primitive(
                    &mut self.builder, op_name, &arg_vals, span,
                    self.module, self.ctx.panic_func_id,
                ) {
                    Some(result) => result,
                    None => {
                        // Drift between `is_known_builtin` and
                        // `try_emit_inline_primitive`: fall through to the
                        // GOT-indirect path (Ring 0 primitives have GOT
                        // slots per FIXME 0174 resolution).
                        let sym = Symbol::from(op_name.as_ref());
                        self.compile_direct_call(&sym, &arg_vals, span)
                    }
                }
            }
            ResolvedCall::TraitMethod {
                ref mangled_name,
                ..
            } => {
                // Per Decision 43 + FIXME 0185: backend has no trait knowledge.
                // The pre-D43 `primitive_for_trait_method((TraitName, Symbol,
                // TypeName))` dispatch table — keyed on `(Num, "+", Int)` →
                // `add-i64` — is the canonical D43-forbidden pattern and has
                // been deleted. Backend dispatches uniformly: every
                // ResolvedCall::TraitMethod goes via the trait-impl's
                // mangled name (e.g., `Num.+$Int`), GOT-indirect like any
                // user function.
                //
                // Performance note: trait operator calls now traverse one
                // extra call frame compared to the pre-D43 inline-IR path
                // (the impl body is `(defn + [a b] (add-i64 a b))` — one
                // hop to the inline-substituted primitive). FIXME 0185
                // tracks the typecheck-side migration that restores inline
                // optimisation by having typecheck emit `BuiltinFn { name:
                // "add-i64" }` directly for primitive-implemented trait
                // methods, bypassing the `TraitMethod` route entirely.
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
            // `ResolvedCall` is `#[non_exhaustive]` (cranelisp-types crate-root
            // policy): a wildcard arm is required for cross-crate matches. Any
            // future variant the backend does not yet lower is a codegen error
            // naming the call rather than a silent miscompile.
            other => Err(CranelispError::CodegenError {
                message: format!("unsupported resolved-call variant in codegen: {other:?}"),
                location: ErrorLocation::from_span(span),
            }),
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
                    location: ErrorLocation::from_span(span),
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
            return self.emit_adt_construct(tag, &arg_vals, span);
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
            self.ctx.module_aliases,
            &self.ctx.current_module,
            name,
        ) {
            let got_sym = crate::compiler::got_data_symbol_name(&module_path);
            let data_id = self.module
                .declare_data(&got_sym, cranelift_module::Linkage::Import, false, false)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to declare GOT data '{}': {e}", got_sym),
                    location: ErrorLocation::from_span(span),
                })?;
            return self.emit_got_indirect_call_via_data_id(data_id, slot, arg_vals);
        }

        // Kind-driven `PrimitiveExtern` arm (test-discovery.md §6; BC §3
        // invariant 8 / §7 types). A host-promised extern (`discover-tests`)
        // carries `got_slot: None`, so the GOT-indirect resolution above
        // misses it; it has no `FuncId` in `func_ids` either (no codegen body).
        // Lower it as a `Linkage::Import` against the entry key — the symbol
        // table key IS the ABI name — identical in shape to the platform-effect
        // / intrinsic import path. The body is settled at JIT-finalize via
        // `Jit::define_symbol` (int's session-init promise) or surfaces as an
        // unresolved-symbol link error in `--link` (no friendly rejection).
        if let Some(abi_key) = crate::compiler::resolve_extern_target(
            self.ctx.symbol_tables,
            self.ctx.module_aliases,
            &self.ctx.current_module,
            name,
        ) {
            return self.compile_extern_call(&abi_key, arg_vals, span);
        }

        // Direct call: look up FuncId and emit `call`.
        {
            let func_id = self.ctx.func_ids.get(name).ok_or_else(|| {
                CranelispError::CodegenError {
                    message: format!("undefined function: {name}"),
                    location: ErrorLocation::from_span(span),
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
            self.ctx.module_aliases,
            &self.ctx.current_module,
            name,
        )
        .ok_or_else(|| CranelispError::CodegenError {
            message: format!("no GOT slot for function: {name}"),
            location: ErrorLocation::from_span(span),
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

    /// Compile an `Expr::ConstrADT` node — the language-level ADT construction
    /// operation synthesised as the body of every constructor's `Def`.
    ///
    /// Per `design/backend/compile-to-module.md` §2.6:
    /// - **Nullary** (`fields.is_empty()`, e.g. `None`, `Red`): fold to a bare
    ///   `iconst.i64 tag` — no heap allocation. Preserves the
    ///   `NULLARY_TAG_THRESHOLD` discrimination contract.
    /// - **Data** (e.g. `Some 42`, `Cons h t`): consuming-compile each field
    ///   left-to-right, `emit_alloc` a `HeapAdt` payload, store `tag` at
    ///   `TAG_OFFSET`, store each field `Value` at its `field_offset(i)`. The
    ///   result `Value` is the heap pointer.
    ///
    /// RC: field values are transferred into the constructor under the uniform
    /// consuming convention (Decision 24, BC invariant 2) — `compile_consuming_arg_list`
    /// inc's non-last-use Var fields before the store; last-use fields transfer
    /// their existing reference. The ADT's drop glue dec's heap-typed fields when
    /// the ADT itself reaches rc=0.
    ///
    /// First-class use `(map Some list)` — passing a constructor as a value via
    /// its `Def`'s `got_slot` (the same path as any other callable, no
    /// on-demand closure synthesis) — is a `// target (S77)` (int-produced).
    ///
    /// `compile_constr_adt` + `emit_adt_construct` are the two-path model
    /// (nullary `iconst tag` / data alloc+tag+stores). The older
    /// `literals::nullary_constructor_tag` + `literals::data_constructor_info`
    /// helpers still exist; their consolidation into this single handler (the
    /// "~200 LOC removed" cleanup) is a `// target (S77)` cleanup, not yet done.
    pub(crate) fn compile_constr_adt(
        &mut self,
        tag: usize,
        fields: &[Expr],
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Consuming-compile fields (nullary → empty), then route through the
        // single core emitter. `emit_adt_construct` handles the nullary
        // (`iconst tag`) and data (`alloc + tag + stores`) arms.
        let field_vals = self.compile_consuming_arg_list(fields)?;
        self.emit_adt_construct(tag, &field_vals, span)
    }

    /// The single ADT-construct emitter — both paths route through here.
    ///
    /// Per `design/backend/compile-to-module.md` §2.6.1: takes an already-computed
    /// `tag` and the already-computed field `Value`s, and emits the construct.
    /// **RC-neutral** (§2.6.4): stores `field_vals` verbatim — the consuming-
    /// convention inc/transfer happens in the callers that produce `field_vals`
    /// (`compile_consuming_arg_list`). Do NOT add RC here; doing so would
    /// double-inc the Path-1 inline site.
    ///
    /// | Case | Emission |
    /// |---|---|
    /// | `field_vals.is_empty()` (nullary, e.g. `None`, `Red`) | bare `iconst.i64 tag`, no heap allocation — preserves the `NULLARY_TAG_THRESHOLD` discrimination contract |
    /// | `!field_vals.is_empty()` (data ctor) | `emit_alloc` a `HeapAdt`, store `tag` at `TAG_OFFSET`, store each field at `field_offset(i)`; result is the heap pointer |
    pub(crate) fn emit_adt_construct(
        &mut self,
        tag: usize,
        field_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        if field_vals.is_empty() {
            // Nullary constructor: bare tag, no heap allocation.
            return Ok(self.builder.ins().iconst(types::I64, tag as i64));
        }

        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
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
                location: ErrorLocation::from_span(span),
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
                location: ErrorLocation::from_span(span),
            });
        }

        let io_val = arg_vals[0]; // inner IO tree
        let cont_val = arg_vals[1]; // continuation closure

        let alloc_id =
            self.ctx
                .alloc_func_id
                .ok_or_else(|| CranelispError::CodegenError {
                    message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                    location: ErrorLocation::from_span(span),
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
