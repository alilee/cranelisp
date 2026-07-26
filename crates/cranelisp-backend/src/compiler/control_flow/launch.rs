// Launch-and-continue codegen: the `IO_TAG_LAUNCH` node emission.
//
// Compiles a `MonoExpr::LaunchContinue` (produced by `/int`'s bind-chain
// independence analysis at the §10.12.7 launch shape — a result-discarded,
// token-disjoint effect) into the documented IO-tree structure: a thin
// single-field `IO_TAG_LAUNCH` node wrapping the launched sub-tree, wrapped by a
// `IO_TAG_BIND` node linking it to a continuation closure that ignores the
// (discarded `Pure Unit`) launch result and evaluates the continuation.
//
// See `design/backend/io-trampoline.md §15` (the launch node + bake + the
// move-out RC contract) and `design/int/reactor.md §2.11` (the runtime detach).
// The launch node is the structural twin of the `Par` node in `Bind(Par(..),
// cont)` (`par_bind.rs`) — the trampoline's "inner yields a value, pop the
// continuation" contract is reused verbatim; `Launch`'s value is always `Unit`.

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{CranelispError, ErrorLocation, MonoExpr, Span, Symbol};

use crate::heap::{self, HeapAdt, HeapClosure};

use super::{FnCompiler, find_free_vars};

/// `IO_TAG_LAUNCH` — emitted as the literal `5` at the bake (the backend carries
/// no `concurrency` feature and reads no platform const at codegen, the
/// `par_bind.rs` `IO_TAG_PAR = 3` / `compile_poll_effect` `= 4` convention).
/// Canonical home: `cranelisp_platform::IO_TAG_LAUNCH`.
const IO_TAG_LAUNCH: i64 = 5;
/// `IO_TAG_BIND` — the wrapping Bind node tag (mirrors `par_bind.rs`).
const IO_TAG_BIND: i64 = 2;

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Compile a `MonoExpr::LaunchContinue` — emit `Bind(Launch(launched), cont)`.
    ///
    /// 1. Build the thin `IO_TAG_LAUNCH` node holding the launched sub-tree
    ///    (`compile_launch`).
    /// 2. Build a continuation closure `(fn [_] continuation)` — it ignores the
    ///    discarded launch result (`Pure Unit`) and evaluates the continuation.
    /// 3. Allocate a `IO_TAG_BIND` node linking the Launch node → continuation
    ///    (the same bind codegen `par_bind` / `compile_bind_inline` emit).
    ///
    /// RC follows the constructor convention (Decision 20/24): ownership transfer,
    /// no inc on store. The launched sub-tree (rc=1 temporary) moves into the
    /// Launch node's field 0; the continuation (rc=1) and Launch node move into
    /// the Bind node's fields. The Launch node's field-0 drop is **null-guarded**
    /// (`design/backend/io-trampoline.md §15.5`) — realized by the
    /// `consume_io_tree` `IO_TAG_LAUNCH` arm (intrinsics) reading the `0` sentinel
    /// the trampoline writes back after moving the sub-tree into the strand.
    pub(crate) fn compile_launch_continue(
        &mut self,
        launched: &MonoExpr,
        continuation: &MonoExpr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id = self
            .ctx
            .alloc_func_id
            .ok_or_else(|| CranelispError::CodegenError {
                message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                location: ErrorLocation::from_span(span),
            })?;

        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;

        // 1. Build the Launch node wrapping the launched sub-tree.
        let launch_ptr = self.compile_launch(launched, span)?;

        // 2. Build the continuation closure — discards the launch result.
        let cont_ptr = self.compile_launch_continuation(continuation, span)?;

        // 3. Allocate the wrapping Bind node: [header | tag=2 | inner | cont].
        let bind_payload_size = HeapAdt::payload_size(2) as i64; // tag + 2 fields = 24
        let bind_ptr =
            heap::emit_alloc(&mut self.builder, self.module, alloc_id, bind_payload_size);

        let bind_tag = self.builder.ins().iconst(types::I64, IO_TAG_BIND);
        heap::heap_store(&mut self.builder, bind_tag, bind_ptr, HeapAdt::TAG_OFFSET);
        // inner = the Launch node; cont = the continuation closure. No RC inc —
        // ownership transfer (constructor convention, Decision 20/24).
        heap::heap_store(
            &mut self.builder,
            launch_ptr,
            bind_ptr,
            HeapAdt::field_offset(0),
        );
        heap::heap_store(
            &mut self.builder,
            cont_ptr,
            bind_ptr,
            HeapAdt::field_offset(1),
        );

        self.in_tail_position = saved_tail;
        Ok(bind_ptr)
    }

    /// Build the thin `IO_TAG_LAUNCH` node (`io-trampoline.md §15.4`):
    /// `[header(16) | tag=5 | launched_subtree]` — `HeapAdt::payload_size(1)` (32
    /// bytes total). The compiled launched sub-tree (a fresh IO tree at rc=1)
    /// moves into field 0 with **no `rc_inc`** — a plain ownership transfer
    /// (identical to how `compile_par_bind` stores its branch pointers and
    /// `compile_poll_effect` stores its state-closure, Decision 20/24).
    fn compile_launch(&mut self, launched: &MonoExpr, span: Span) -> Result<Value, CranelispError> {
        let alloc_id = self
            .ctx
            .alloc_func_id
            .ok_or_else(|| CranelispError::CodegenError {
                message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                location: ErrorLocation::from_span(span),
            })?;

        // Compile the detached sub-tree — a fresh IO tree at rc=1 (temporary).
        let launched_val = self.compile_expr(launched)?;

        // Allocate the thin node: tag + 1 field = HeapAdt::payload_size(1) = 16
        // payload (32 total with the 16-byte header).
        let payload_size = HeapAdt::payload_size(1) as i64;
        let node = heap::emit_alloc(&mut self.builder, self.module, alloc_id, payload_size);

        let tag = self.builder.ins().iconst(types::I64, IO_TAG_LAUNCH);
        heap::heap_store(&mut self.builder, tag, node, HeapAdt::TAG_OFFSET);
        // field 0: ownership transfer of the launched sub-tree (rc=1) — NO inc.
        heap::heap_store(
            &mut self.builder,
            launched_val,
            node,
            HeapAdt::field_offset(0),
        );

        Ok(node)
    }

    /// Build the continuation closure for a launch-and-continue node.
    ///
    /// The continuation is a standard bind continuation `(Fn [a] (IO b))` whose
    /// argument (the discarded `Pure Unit` launch result) is **ignored**:
    ///   `extern "C" fn(env_ptr: i64, _discarded: i64) -> i64`
    /// It loads captures from `env_ptr`, compiles the continuation (which binds NO
    /// result name — the launch result is discarded), and returns the body result
    /// (a new IO tree pointer). Returns the closure base pointer (rc=1).
    ///
    /// Reuses `alloc_par_cont_closure` (`par_bind.rs`) for the closure-site alloc
    /// (code-ptr, drop-glue, capture stores — Principle 7). The only difference
    /// from the par-bind continuation is that this body loads no per-binding
    /// results buffer.
    fn compile_launch_continuation(
        &mut self,
        continuation: &MonoExpr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Captures: free variables of the continuation that are in scope here.
        let cont_free = find_free_vars(continuation, &[]);
        let mut captures: Vec<Symbol> = cont_free
            .into_iter()
            .filter(|v| self.variables.contains_key(v))
            .collect();
        captures.sort(); // deterministic layout

        // Declare the continuation function: (env_ptr, discarded_result) -> i64.
        let cont_name = format!(
            "__launch_cont_{}{}_{}__",
            self.inner_fn_discriminator(),
            span.start,
            span.end
        );
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // env_ptr
        sig.params.push(AbiParam::new(types::I64)); // discarded launch result (Pure Unit)
        sig.returns.push(AbiParam::new(types::I64));

        let cont_func_id = self
            .module
            .declare_function(&cont_name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare launch continuation: {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        self.define_launch_cont_body(cont_func_id, &captures, continuation, sig, span)?;

        // Reuse the par-bind closure-site allocation (Principle 7).
        self.alloc_par_cont_closure(cont_func_id, &captures, span)
    }

    /// Define the launch continuation function body in a separate Cranelift
    /// context. Loads captures from `env_ptr` (ignoring the discarded result
    /// param), compiles `continuation`, and returns the body result.
    fn define_launch_cont_body(
        &mut self,
        cont_func_id: cranelift_module::FuncId,
        captures: &[Symbol],
        continuation: &MonoExpr,
        sig: cranelift::codegen::ir::Signature,
        span: Span,
    ) -> Result<(), CranelispError> {
        let mut inner_ctx = self.module.make_context();
        let mut inner_func_ctx = FunctionBuilderContext::new();
        inner_ctx.func.signature = sig;

        let mut builder = FunctionBuilder::new(&mut inner_ctx.func, &mut inner_func_ctx);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let block_params = builder.block_params(entry_block).to_vec();
        let env_ptr = block_params[0];
        // block_params[1] is the discarded launch result (Pure Unit) — unused.

        let last_uses = heap::compute_last_uses(continuation);
        let mut inner = FnCompiler::inner(
            builder,
            self.module,
            self.ctx.clone(),
            self.glue,
            0, // fn_param_count=0: no binding names enter from the discarded result
            last_uses,
        );

        // Load captured variables from env_ptr at CAPTURES_START + i*8.
        for (i, cap_name) in captures.iter().enumerate() {
            let cap_val =
                heap::heap_load(&mut inner.builder, env_ptr, HeapClosure::capture_offset(i));
            let var = inner.fresh_variable();
            inner.builder.declare_var(var, types::I64);
            inner.builder.def_var(var, cap_val);
            inner.variables.insert(cap_name.clone(), var);
            // Seed the capture's TYPE into the inner compiler so a consuming
            // call in the continuation body emits the required caller-side
            // `rc_inc` on a heap-typed capture before passing it to a consuming
            // callee. `compile_lambda_body` parity (ring2-rc.md §5.5 / the S60
            // capture-type bug). Without it, the launch-and-continue tail
            // `(fn [_] (serve-loop listener))` passes the captured `listener` to
            // the recursive `serve-loop` WITHOUT the inc; the callee dec's it at
            // scope exit AND the closure drop glue dec's it again → `listener`
            // freed after the first detached iteration, and the next accept loop
            // reuses the freed address (FIXME 0472 — the launched web handler
            // "ConnectionReset"/heap-corruption defect).
            if let Some(ty) = self.variable_types.get(cap_name) {
                inner.variable_types.insert(cap_name.clone(), ty.clone());
            }
        }
        // Mark captures so they are not eligible for last-use transfer/cleanup —
        // the closure env owns them; its drop glue dec's them (par_bind parity).
        for cap_name in captures {
            inner.captured_vars.insert(cap_name.clone());
        }

        // Compile the continuation body. It binds NO result name (the launch
        // result is discarded), so there is no per-binding load + no results
        // buffer to dec — the one simplification over the par-bind continuation.
        inner.push_scope();
        let skip_var = FnCompiler::<M>::return_var_in_scope(continuation, inner.scope_stack.last());
        let result = inner.compile_expr(continuation)?;
        inner.protect_return_value(&skip_var, result, continuation);
        inner.pop_scope_with_cleanup(skip_var.as_ref())?;

        inner.builder.ins().return_(&[result]);
        inner.builder.seal_all_blocks();
        inner.builder.finalize();

        self.module
            .define_function(cont_func_id, &mut inner_ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define launch continuation: {e}"),
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

    // spec: design/backend/io-trampoline.md §15 — FIXME 0472 regression guard.
    //
    // A launch-and-continue continuation that passes a CAPTURED heap variable to a
    // consuming call MUST emit the caller-side `rc_inc` on that capture
    // (`compile_lambda_body` parity / ring2-rc.md §5.5). The launched web serve loop
    // `(do (bind (read-conn …) …) (serve-loop listener))` lowers the tail to a launch
    // continuation `(fn [_] (serve-loop listener))` — exactly this shape: the captured
    // `listener` is passed to the recursive `serve-loop` (a consuming call). Pre-fix,
    // `define_launch_cont_body` did NOT seed the capture's TYPE into the inner
    // compiler, so the consuming call skipped the inc; the callee dec'd `listener` at
    // scope exit AND the continuation closure's drop glue dec'd it again → `listener`
    // freed after the FIRST detached iteration, the next accept loop reused the freed
    // address, and the recursive serve loop's `match` read a dangling pointer (the
    // observed ConnectionReset / heap corruption on the 2nd request).
    //
    // This guard isolates the inner launch-continuation codegen WITHOUT the reactor:
    // build the `Bind(Launch, cont)` tree via backend codegen, extract the
    // continuation closure, invoke it directly (so it runs `(keep h)` over the
    // captured String `h`), then run the closure's drop glue (`consume_closure` — the
    // IO trampoline's fresh-continuation release path). With the fix `h` SURVIVES the
    // drop (the consuming-call inc balanced it); pre-fix `h` is freed → is_live false.
    #[test]
    fn launch_continuation_consuming_call_on_capture_keeps_it_live() {
        use cranelisp_types::{JitSymbol, ResolvedCall};

        // (defn keep$String [v] v) — identity over a heap String: a consuming
        // function (its param ref is consumed-then-returned, RC-neutral).
        let keep = Defn {
            name: Symbol::from("keep$String"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("v"), None)],
                body: Expr::Var {
                    name: Symbol::from("v"),
                    span: Span::new(40, 41),
                    resolved_call: None,
                    inferred_type: Some(Box::new(Type::String)),
                },
                span: Span::new(30, 45),
            }],
            visibility: Visibility::Public,
            span: Span::new(30, 45),
        };

        // (defn entry [] (let [h "hello"] (launch-continue 0 (keep$String h))))
        // The LaunchContinue continuation `(keep$String h)` captures the heap `h` and
        // passes it to the consuming `keep$String` call. `launched` is an int stand-in
        // (0) — never interpreted; this test invokes only the continuation closure.
        let call_span = Span::new(70, 82);
        let sig_dispatch = || {
            Some(Box::new(ResolvedCall::SigDispatch {
                mangled_name: JitSymbol::from("keep$String"),
            }))
        };
        let continuation = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("keep$String"),
                span: call_span,
                resolved_call: sig_dispatch(),
                inferred_type: Some(Box::new(Type::Fn(
                    vec![Type::String],
                    Box::new(Type::String),
                ))),
            }),
            args: vec![Expr::Var {
                name: Symbol::from("h"),
                span: Span::new(78, 79),
                resolved_call: None,
                inferred_type: Some(Box::new(Type::String)),
            }],
            span: call_span,
            resolved_call: sig_dispatch(),
            inferred_type: Some(Box::new(Type::String)),
        };
        let entry_body = Expr::Let {
            bindings: vec![(
                Symbol::from("h"),
                Expr::StringLit {
                    value: "hello".to_string(),
                    span: Span::new(60, 67),
                    inferred_type: Some(Box::new(Type::String)),
                },
            )],
            body: Box::new(Expr::LaunchContinue {
                launched: Box::new(Expr::IntLit {
                    value: 0,
                    span: Span::new(55, 56),
                    inferred_type: Some(Box::new(Type::Int)),
                }),
                continuation: Box::new(continuation),
                span: Span::new(50, 83),
                inferred_type: Some(Box::new(Type::String)),
            }),
            span: Span::new(48, 84),
            inferred_type: Some(Box::new(Type::String)),
        };
        let entry = Defn {
            name: Symbol::from("entry"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: entry_body,
                span: Span::new(46, 85),
            }],
            visibility: Visibility::Public,
            span: Span::new(46, 85),
        };

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        let tables = empty_tables();
        // W1 (KC-W0-6): the continuation's `(keep$String h)` call reads the callee's
        // `resolved_target`. Seed a NotDetermined stub so `entry_at` resolves it (→
        // FuncId tail, byte-identical) and thread the carrier at the call span.
        {
            let mut st = SymbolTable::new(ModuleFullPath::from("user"));
            insert_user_fn_stub(&mut st, "keep$String", 1);
            tables.insert(ModuleFullPath::from("user"), st);
        }
        let entry_targets = call_carriers(
            entry.body(),
            &ModuleFullPath::from("user"),
            &["keep$String"],
        );

        // S111 R4 §1.3: compile keep$String + entry through the PRODUCTION per-body
        // seam (`compile_defn_in_module`), preserving their hand-built String schemes
        // (heap-classification-sensitive — the whole point of this RC guard). No
        // finalize here; the caller finalizes + runs.
        crate::test_support::compile_defns_in_module(
            &[&keep, &entry],
            &[],
            &entry_targets,
            &tables,
            ModuleFullPath::from("user"),
            jit.jit_module(),
        );
        let entry_ptr = jit.finalize_and_get_ptr(&Symbol::from("entry"), 0).unwrap();

        // Run entry() → the Bind(Launch, cont) IO tree.
        let entry_fn: extern "C" fn() -> i64 = unsafe { std::mem::transmute(entry_ptr) };
        let tree = entry_fn();
        assert!(
            tree > 1024,
            "entry must return a heap IO-tree pointer, got {tree}"
        );

        // Bind layout: [header(16) | tag@16 | inner@24 | cont@32]. Extract the cont.
        let cont_ptr = unsafe { *((tree + 32) as *const i64) };
        assert!(
            cont_ptr > 1024,
            "Bind.cont (field 1 @ offset 32) must be a heap closure pointer, got {cont_ptr}"
        );

        // Invoke the continuation directly: code_ptr at closure+16, called as
        // fn(env_ptr=closure_base, discarded_launch_result=0). Runs `(keep$String h)`.
        let code_ptr = unsafe { *((cont_ptr + 16) as *const i64) };
        let cont_fn: extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(code_ptr) };
        let result_h = cont_fn(cont_ptr, 0);
        assert!(
            result_h > 1024,
            "continuation must return the heap String `h`, got {result_h}"
        );

        // Run the continuation closure's drop glue (the IO trampoline's
        // consume_closure path) — it dec's the captured `h`. The discriminating
        // assertion: WITH the consuming-call inc `h` survives this drop; pre-fix the
        // double-dec frees it (the corruption that wrecked the launched serve loop).
        cranelisp_intrinsics::drop::consume_closure(cont_ptr);

        #[cfg(debug_assertions)]
        assert!(
            cranelisp_intrinsics::alloc::is_live(result_h as usize),
            "the captured String passed to a consuming call in a launch continuation \
         must survive the continuation closure's drop glue (FIXME 0472 — the \
         launched serve loop freed `listener` after one detached iteration)"
        );
        let s = unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(result_h) };
        assert_eq!(
            s, "hello",
            "captured String must round-trip after the drop glue"
        );

        // Balance the surviving caller-side reference (the Bind + Launch nodes are
        // intentionally left — this guard asserts the capture's liveness, not a full
        // tree-balance; the process exits at test end).
        cranelisp_intrinsics::alloc::heap_dealloc(result_h);
    }
}
