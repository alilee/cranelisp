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

use super::{find_free_vars, FnCompiler};

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
        let alloc_id =
            self.ctx
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
        let bind_ptr = heap::emit_alloc(&mut self.builder, self.module, alloc_id, bind_payload_size);

        let bind_tag = self.builder.ins().iconst(types::I64, IO_TAG_BIND);
        heap::heap_store(&mut self.builder, bind_tag, bind_ptr, HeapAdt::TAG_OFFSET);
        // inner = the Launch node; cont = the continuation closure. No RC inc —
        // ownership transfer (constructor convention, Decision 20/24).
        heap::heap_store(&mut self.builder, launch_ptr, bind_ptr, HeapAdt::field_offset(0));
        heap::heap_store(&mut self.builder, cont_ptr, bind_ptr, HeapAdt::field_offset(1));

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
        let alloc_id =
            self.ctx
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
        heap::heap_store(&mut self.builder, launched_val, node, HeapAdt::field_offset(0));

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
        let skip_var =
            FnCompiler::<M>::return_var_in_scope(continuation, inner.scope_stack.last());
        let result = inner.compile_expr(continuation)?;
        inner.protect_return_value(&skip_var, result, continuation);
        inner.pop_scope_with_cleanup(skip_var.as_ref());

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
