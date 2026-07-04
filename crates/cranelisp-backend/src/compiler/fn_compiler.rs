//! The per-function CLIF emitter: the `FnCompiler` struct, its construction
//! (`inner`, `compile_body`, `bind_defn_params`), the expression-dispatch entry
//! (`compile_expr`), scope lifecycle, and the small per-fn predicates.
//! `MatchContext` is per-arm `FnCompiler` state, kept adjacent to the struct it
//! threads through.

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use cranelisp_types::{
    CranelispError, Defn, MonoExpr, ModuleEntry, Span, Symbol, Type,
};

use crate::heap::{self, HeapCategory};

use super::{
    find_var_type_in_expr, inner_fn_discriminator_for, signature_heap_category, CompileContext,
};

/// Match-arm-invariant data bundled to reduce parameter counts in
/// `compile_constructor_pattern`.
///
/// Narrowed to `pub(crate)` in S75 W3 — per-arm codegen state, no out-of-crate
/// consumer.
pub(crate) struct MatchContext {
    /// The compiled scrutinee value.
    pub scrut_val: Value,
    /// The inferred type of the scrutinee expression (for field type resolution).
    pub scrut_type: Option<Type>,
    /// The block to branch to if this arm does not match.
    pub next_block: Block,
    /// The merge block where all arms converge.
    pub merge_block: Block,
    /// The saved tail-position flag from before the match.
    pub saved_tail: bool,
}

/// Per-function compilation context.
///
/// Generic over `M: Module` so the same codegen can target both `JITModule`
/// (for immediate execution) and `ObjectModule` (for `.o` file generation).
/// See design/backend/module-caching.md §13.2 for rationale.
// Sprint 58 Wave 3b (Decision 35): generic over `C: CodeStore` and
// `L: LinkerStore` so it can hold `CompileContext<'a, C, L>`. Defaults
// to `<()>`-pinned for backward compat with the typecheck-product flavour.
//
// Narrowed to `pub(crate)` in S75 W3 — the per-function CLIF emitter; no
// out-of-crate consumer (int reaches codegen only via the free fn
// `compile_to_module`). Its `pub` methods/fields drop from the public API
// with the type.
pub(crate) struct FnCompiler<'a, M: Module, C = (), L = ()>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Cranelift function builder.
    pub builder: FunctionBuilder<'a>,
    /// Reference to the compilation module (JITModule or ObjectModule).
    pub module: &'a mut M,
    /// Local variable bindings (name -> Cranelift Variable).
    pub(crate) variables: HashMap<Symbol, Variable>,
    /// Scope stack: each frame is a list of variable names introduced.
    pub(crate) scope_stack: Vec<Vec<Symbol>>,
    /// Shared immutable compilation context.
    pub(crate) ctx: CompileContext<'a, C, L>,

    /// Next Cranelift Variable index (per-function counter).
    pub(crate) next_var: u32,

    // --- TCO state ---
    //
    // Tail Call Optimization (TCO): loop-based self-TCO.
    //
    // Self-recursive tail calls are compiled as jumps to a loop header block
    // instead of actual function calls. This converts recursion into iteration
    // with O(1) stack usage.
    //
    // The pattern:
    //   1. compile_body creates a loop_header block with block params for each fn param
    //   2. Entry block jumps to loop_header with initial param values
    //   3. Loop_header is NOT sealed eagerly (back-edges from tail calls added later)
    //   4. Body is compiled with in_tail_position = true
    //   5. Tail self-calls jump back to loop_header with new arg values
    //   6. All blocks sealed at the end
    //
    // CRITICAL: compile_apply must set in_tail_position = false before compiling args.
    // Tail position propagation:
    //   - If body / else body: inherits tail position
    //   - Let body: inherits tail position
    //   - Match arm bodies: inherit tail position
    //   - Args, conditions, bindings: NOT in tail position

    /// Name of the current function being compiled (for self-call detection).
    pub(crate) current_fn_name: Option<Symbol>,
    /// Loop header block for TCO (back-edge target for self-recursive tail calls).
    pub(crate) tail_loop_block: Option<Block>,
    /// Whether the current expression is in tail position.
    pub(crate) in_tail_position: bool,
    /// Number of parameters of the current function.
    pub(crate) fn_param_count: usize,

    // --- Ring 1 heap state (scaffolding for RC emission in Ring 2) ---

    /// Types of local variables, for RC management.
    pub(crate) variable_types: HashMap<Symbol, Type>,
    /// Last-use information: (var_name, span) -> is_last_use.
    pub(crate) last_uses: HashMap<(Symbol, Span), bool>,
    /// Variables that borrow from a parent (e.g., pattern match field bindings).
    /// Borrowed vars skip both inc (at extraction) and dec (at scope exit).
    /// The owner (scrutinee) handles cleanup via its own RC management.
    pub(crate) borrowed_vars: std::collections::HashSet<Symbol>,
    /// Captured variable names (variables closed over by a lambda).
    /// These are NEVER eligible for last-use transfer.
    pub(crate) captured_vars: std::collections::HashSet<Symbol>,

    /// The ownership summary ([`cranelisp_types::ModeSummary`]) of the function
    /// currently being compiled — read from its `codegen_view`
    /// (`MonoDefnVariant.mode_summary`) on the `compile_to_module` path;
    /// `None` on the lenient JIT/REPL path (no `codegen_view`) and for every
    /// inner compiler (lambda / continuation / drop-glue bodies).
    ///
    /// Borrow-elision consumer (B3.2, `design/backend/ownership-codegen.md`
    /// §3.3): `protect_return_value` skips its protective inc when this summary
    /// is **present** with `result == ResultMode::Fresh` — a Fresh result is
    /// provably not aliased to any scope binding (the analysis widens any
    /// returned/escaping param away from Fresh before emitting the summary),
    /// so scope cleanup cannot free it and no protection is owed. Gated on
    /// PRESENCE — absent ⇒ Decision-24 (protect), so `CRANELISP_NO_OWNERSHIP`
    /// (which suppresses all summaries) is byte-identical to pre-B3.2.
    pub(crate) current_mode_summary: Option<cranelisp_types::ModeSummary>,

    /// Set while compiling an `if`/`match` that is itself a **direct tail-call
    /// argument** (`compile_tail_self_call`). Under this flag, `compile_if` /
    /// `compile_match` emit a protective `rc_inc` on any branch/arm result that
    /// directly aliases a live heap `let`-scope binding the subsequent tail-jump
    /// flush will `rc_dec` (`flush_let_scopes_before_tail_jump`). The inc balances
    /// the uniform flush dec so the value handed to the next iteration's loop
    /// param owns exactly one reference — curing the F1 use-after-free where a
    /// control-flow-aliased binding was flushed while still reachable
    /// (`design/backend/ownership-codegen.md` §13.3 — the TCO-flush skip-predicate
    /// correctness contract). Saved/restored per-arg so it never leaks into a
    /// sibling or nested non-tail position.
    pub(crate) tail_arg_protect: bool,

    /// Drop glue FuncIds for closure variables.
    /// When a closure with heap-typed captures is bound to a variable,
    /// the drop glue function is stored here so that `pop_scope_with_cleanup`
    /// can pass it to `emit_rc_dec` when freeing the closure.
    pub(crate) closure_drop_glue: HashMap<Symbol, FuncId>,

    /// Depth counter for inline drop glue generation.
    /// Prevents infinite IR for recursive types (e.g., List).
    /// Allows limited nesting for non-recursive parametric types (e.g., Option(Option(String))).
    pub(crate) drop_glue_depth: u32,

    /// Pending closure drop glue from the last `compile_lambda` call.
    /// Set by `compile_lambda`, consumed by `compile_let` or `compile_body`
    /// when binding the closure value to a variable name.
    pub(crate) pending_closure_drop_glue: Option<FuncId>,

    /// Whether we are compiling inside a `(trace ...)` body.
    /// When true, sparkability analysis is disabled — trace bodies must
    /// execute sequentially to produce deterministic trace trees.
    pub(crate) in_trace_body: bool,

    /// Sparked apply-arguments for the function application currently being
    /// dispatched (lenient-eval.md §4.4). When `Some((args_ptr, map))`, the
    /// apply whose argument slice has base pointer `args_ptr` had its arguments
    /// at the indices in `map` sparked into IVars by the lenient pre-pass; the
    /// arg-list compilation FORCES those positions (at the left-to-right
    /// barrier) instead of recompiling them, with no consuming inc (the forced
    /// value is an rc=1 temporary that transfers into the callee).
    ///
    /// Keyed by the argument-slice base pointer so a nested apply / constructor
    /// whose own argument slice differs (different allocation ⇒ different
    /// pointer) can never consult an enclosing apply's index→IVar map — the
    /// pointer-identity guard makes cross-apply leakage structurally impossible
    /// (Principle 18). Set/restored around each lenient `compile_apply` dispatch.
    pub(crate) sparked_args: Option<(*const MonoExpr, HashMap<usize, Value>)>,

    /// Accumulated create-gate **arm discriminator** for span-derived inner-
    /// function names (lenient-eval.md §3.6.2). The create-gate compiles the
    /// *same* source expressions on BOTH its lenient and direct arms, so without
    /// a per-arm component the two arms would re-emit identical span-derived
    /// inner-function names (`__lambda_<span>__`, `__wrap_…`) and the second
    /// `define_function` would collide (`Duplicate definition of identifier`).
    /// `emit_create_gate` appends a `g{id}{L|D}_` token here around each arm's
    /// compilation (saved/restored, so nesting accumulates); `inner_fn_discriminator`
    /// folds it into every inner-function name, making the two arms' (and nested
    /// gates') copies distinct. Empty outside any gate arm.
    pub(crate) gate_arm_disc: String,

    /// Monotonic per-compiler counter handing out unique create-gate ids, so
    /// nested gates within one function body get distinct arm discriminators.
    pub(crate) gate_counter: u32,

    /// When true, the create-gate (lenient-eval.md §3.6.2) is suppressed —
    /// sparkable apply/`let` sites compile fully sequentially with no runtime
    /// budget branch. Set for the duration of a gate's **direct (over-budget)
    /// arm** so its lowering does not emit nested gates.
    ///
    /// Without this, the gate compiles the same lowering on BOTH arms, so a
    /// STATICALLY nested chain of sparkable sites — e.g. `(add-i64 a (add-i64 b
    /// (add-i64 c …)))`, every pair sparkable — would re-compile its tail on
    /// each arm, giving `O(2^depth)` codegen (observed: a deep nested-add hung
    /// the compiler). Suppressing gates inside the over-budget arm is both the
    /// fix and the intended semantics: over budget at a site ⇒ evaluate that
    /// whole subexpression serially (§3.6.3 floor). Runtime recursion through a
    /// function whose body has ONE gate is unaffected (the body is compiled
    /// once); only static source nesting was the blowup.
    pub(crate) suppress_spark_gate: bool,

    /// When true, the closure currently being compiled is a **structurally-
    /// joined spark thunk** (an apply-argument spark, an independent-`let`
    /// spark, or a `ParBind` continuation) whose heap captures are **borrows**,
    /// not retains — the capture-by-borrow optimisation (Sprint 99 Wave 1b,
    /// FIXME 0461; `ring2-rc.md` §5.5.2, `lenient-eval.md` §4.4.1). The join
    /// proves the capturing parent frame outlives every spark, so the parent's
    /// own scope-cleanup dec is the single dec that accounts for the cell.
    ///
    /// Set (RAII save/restore) at exactly the three joined emission sites —
    /// `apply.rs` (§4.4 lenient arm), `let_if.rs` (§4.2 Phase 1 *independent*
    /// thunk), `par_bind.rs` (continuation build) — and **only** when
    /// `CAPTURE_BORROW_ENABLED` (the `CRANELISP_CAPTURE_BORROW=1` toggle) is on;
    /// off ⇒ the flag stays false everywhere ⇒ byte-identical to pre-S99.
    ///
    /// When set, the capture-store inc (`lambda.rs` / `par_bind.rs
    /// alloc_par_cont_closure`) **and** the matching `build_closure_drop_glue`
    /// heap-capture dec are **both** skipped, symmetrically — exactly §5.5's
    /// borrowed-`Var` rule (skip inc at introduction *and* dec at release).
    /// Skipping only one is an under/over-count bug.
    ///
    /// **Never** raised on the `launch.rs` `LaunchContinue` (detached, fire-and-
    /// forget) path — a detached strand has no join inside the parent's extent,
    /// so its captures MUST retain (§5.5.2.1 exclusion). It is also scoped to
    /// the *standard* `compile_lambda` capture path: the §4.5 dependent-thunk
    /// synthetic `§ivar_*` keepalive captures are emitted by the manual
    /// `dependent_spark.rs` path (never reached with the flag set) and stay
    /// retained (§4.4.1 carve-out). Fresh inner compilers reset it to false, so
    /// it governs only the immediate thunk's capture store, not nested closures.
    pub(crate) spark_capture_borrow: bool,
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{

    /// Create an inner `FnCompiler` for lambda bodies, continuations,
    /// or (future) drop glue. This is the single construction point for
    /// inner compilers (ring1-checklist section 5.9).
    ///
    /// TCO state is disabled for inner functions (no self-call detection,
    /// no tail loop). The scope and variable maps start fresh.
    pub(crate) fn inner(
        builder: FunctionBuilder<'a>,
        module: &'a mut M,
        ctx: CompileContext<'a, C, L>,
        fn_param_count: usize,
        last_uses: HashMap<(Symbol, Span), bool>,
    ) -> Self {
        FnCompiler {
            builder,
            module,
            variables: HashMap::new(),
            scope_stack: vec![vec![]],
            ctx,
            next_var: 0,
            current_fn_name: None,
            tail_loop_block: None,
            in_tail_position: false,
            fn_param_count,
            variable_types: HashMap::new(),
            last_uses,
            borrowed_vars: std::collections::HashSet::new(),
            captured_vars: std::collections::HashSet::new(),
            current_mode_summary: None,
            tail_arg_protect: false,
            closure_drop_glue: HashMap::new(),
            drop_glue_depth: 0,
            pending_closure_drop_glue: None,
            in_trace_body: false,
            sparked_args: None,
            gate_arm_disc: String::new(),
            gate_counter: 0,
            suppress_spark_gate: false,
            spark_capture_borrow: false,
        }
    }

    /// Monomorphisation-aware discriminator for span-derived inner-function
    /// names (lambdas, fn-as-value wrappers, operator-as-value wrappers).
    ///
    /// **FIXME 0347 defect (1).** Inner functions are named by source span
    /// (`__lambda_<start>_<end>__`, `__wrap_<name>_<start>_<end>__`). When the
    /// ENCLOSING function is monomorphised — the same source span compiled into
    /// N distinct monomorphic instances within ONE `Module` — every instance
    /// re-emits the same span-derived name, so the second `define_function`
    /// collides (`Duplicate definition of identifier`). The enclosing function's
    /// name IS the per-instance discriminator: each mono copy carries a distinct
    /// mangled name (`reduce$Int+Vec`, `id$Int`, …), so prefixing the inner
    /// name with it uniquifies the N copies. When no enclosing name is set
    /// (top-level expression, nested-lambda inner compiler), the span alone
    /// suffices for uniqueness within that scope, so the prefix is empty.
    ///
    /// Non-`[A-Za-z0-9_]` chars in the enclosing name (`$`, `+`, `/`, `.`) are
    /// mapped to `_` so the result is a clean Cranelift symbol.
    pub(crate) fn inner_fn_discriminator(&self) -> String {
        // Fold in the create-gate arm discriminator (§3.6.2): the gate compiles
        // the same expressions on both arms, so the per-arm `g{id}{L|D}_` token
        // is what keeps the two arms' span-derived inner-function names distinct.
        // Empty outside any gate arm ⇒ byte-identical names to the pre-gate path.
        format!(
            "{}{}",
            inner_fn_discriminator_for(self.current_fn_name.as_ref()),
            self.gate_arm_disc,
        )
    }

    /// B3.2 borrow-elision return-protect gate
    /// (`design/backend/ownership-codegen.md` §3.3): `true` iff the function's
    /// ownership summary proves its return value is a fresh (non-aliased) value,
    /// so `protect_return_value`'s inc is dead weight and is elided (curing the
    /// G2 / item-26 over-inc leak).
    ///
    /// One condition, sufficient for soundness post-FIXME-0520:
    ///
    /// - **A summary is PRESENT with `result == Fresh`.** Absent ⇒ Decision-24
    ///   (protect verbatim), so a `CRANELISP_NO_OWNERSHIP` build (no summaries)
    ///   is byte-identical to pre-B3.2.
    ///
    /// The Apply-body restriction the partial slice (`d7b6a0f`) carried is
    /// **dropped** here: FIXME 0520 cured the typecheck-side result-mode collapse
    /// (`join_origin` no longer widens a partial control-flow param-return toward
    /// the dangerous `Fresh` — a `(if (eq i n) v (build …))` base-case-returns-`v`
    /// body now reports `AliasOf(0)`, not `Fresh`). `result == Fresh` is therefore
    /// now sound for *any* body shape: it means no reachable return path carries a
    /// param, so the returned value is genuinely fresh and scope cleanup can never
    /// free it. Verified: `04_vec_cow_loop`'s `build` (result `AliasOf(0)`) keeps
    /// its protect and runs correct under the unrestricted gate.
    pub(crate) fn return_is_fresh_by_summary(&self, body: &MonoExpr) -> bool {
        return_is_fresh_by_summary(body, self.current_mode_summary.as_ref())
    }

    /// Compile a function definition body into Cranelift IR.
    ///
    /// This is the main entry point called by Jit::compile_defn.
    /// Creates the entry block, loop header (for TCO), binds parameters,
    /// compiles the body, and finalizes.
    pub fn compile_body(
        defn: &Defn,
        body: &MonoExpr,
        mode_summary: Option<cranelisp_types::ModeSummary>,
        func: &mut cranelift::codegen::ir::Function,
        func_ctx: &mut FunctionBuilderContext,
        module: &'a mut M,
        ctx: CompileContext<'a, C, L>,
    ) -> Result<(), CranelispError> {
        let mut builder = FunctionBuilder::new(func, func_ctx);

        // Entry block: receives function parameters.
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        // Create loop header block for TCO: one i64 block param per function param.
        let loop_header = builder.create_block();
        for _ in defn.params() {
            builder.append_block_param(loop_header, types::I64);
        }

        // Jump from entry to loop header with initial parameter values.
        let entry_params: Vec<Value> = builder.block_params(entry_block).to_vec();
        builder.ins().jump(loop_header, &entry_params);

        // Switch to loop header. Do NOT seal it yet -- back-edges from tail calls
        // will be added during body compilation.
        builder.switch_to_block(loop_header);

        // Compute last-use info for the body.
        let last_uses = heap::compute_last_uses(body);

        let mut compiler = FnCompiler {
            builder,
            module,
            variables: HashMap::new(),
            scope_stack: vec![vec![]],
            ctx,
            next_var: 0,
            current_fn_name: Some(defn.name.clone()),
            tail_loop_block: Some(loop_header),
            in_tail_position: true,
            fn_param_count: defn.params().len(),
            variable_types: HashMap::new(),
            last_uses,
            borrowed_vars: std::collections::HashSet::new(),
            captured_vars: std::collections::HashSet::new(),
            current_mode_summary: mode_summary,
            tail_arg_protect: false,
            closure_drop_glue: HashMap::new(),
            drop_glue_depth: 0,
            pending_closure_drop_glue: None,
            in_trace_body: false,
            sparked_args: None,
            gate_arm_disc: String::new(),
            gate_counter: 0,
            suppress_spark_gate: false,
            spark_capture_borrow: false,
        };

        // Seed the function's parameters into scope + variable_types.
        compiler.bind_defn_params(defn, body, loop_header);

        // Compile the function body with scope cleanup for parameters.
        // This implements the consuming calling convention: the callee owns
        // heap-typed parameters and dec's them at exit. The caller inc's
        // variable arguments before the call.
        let skip_var = Self::return_var_in_scope(body, compiler.scope_stack.last());
        // §3.2 soundness tripwire (`design/backend/ownership-codegen.md` §3.2):
        // a `Borrowed` param must NEVER be the function's returned value — the
        // ownership analysis widens any returned/escaping param off `Borrowed`
        // (to `Owned`/`AliasOf`) before the summary is emitted (typecheck
        // §3.3/§4.2 rule 5). If a returned bare `Var` names a `borrowed_vars`
        // member, the analysis violated that rule and the elided caller-side inc
        // + elided callee-side dec would hand the caller a borrowed view it then
        // frees (UAF). Cheap debug-build guard; no emission rule is owed.
        debug_assert!(
            skip_var
                .as_ref()
                .is_none_or(|rv| !compiler.borrowed_vars.contains(rv)),
            "§3.2 invariant violated: Borrowed param {skip_var:?} reached the return path \
             — the ownership analysis must widen returned params off Borrowed"
        );
        let result = compiler.compile_expr(body)?;
        // B3.2 borrow-elision (`design/backend/ownership-codegen.md` §3.3): skip
        // the function-return protect inc when the ownership summary proves this
        // function's result is `Fresh`. Applied ONLY here (the function's actual
        // return expression, where `current_mode_summary.result` describes the
        // value) — never at the nested `let`/`match` protect sites, whose bodies
        // are not the function's tail return.
        if !compiler.return_is_fresh_by_summary(body) {
            compiler.protect_return_value(&skip_var, result, body);
        }
        compiler.pop_scope_with_cleanup(skip_var.as_ref());

        // Return the result.
        compiler.builder.ins().return_(&[result]);

        // Seal all blocks (including loop_header which may have back-edges).
        compiler.builder.seal_all_blocks();
        compiler.builder.finalize();

        Ok(())
    }

    /// Seed the function's parameters into scope and `variable_types`.
    ///
    /// Binds each `defn` parameter from the loop-header block params (not the
    /// entry block — TCO back-edges feed the loop header) to a fresh Cranelift
    /// `Variable`, records the binding in the current scope frame, and records
    /// the parameter's authoritative type so scope cleanup can emit `rc_dec`
    /// for heap-typed parameters at function exit.
    fn bind_defn_params(&mut self, defn: &Defn, body: &MonoExpr, loop_header: Block) {
        // Look up the defn's inferred type to get authoritative parameter types.
        // This is essential for unused parameters: derive_param_type scans
        // use sites, so unused params (e.g., `_s` in `(defn f [:String _s] 42)`)
        // would have no type recorded and scope cleanup would skip their RC dec.
        //
        // Read from the symbol table's Scheme.ty (authoritative source) rather
        // than from expr_types side map (Step 1c: AST-sourced codegen).
        let defn_param_types: Vec<Option<Type>> = self.ctx.symbol_tables
            .get(&self.ctx.current_module)
            .and_then(|table| {
                if let Some(ModuleEntry::Def { scheme, .. }) = table.get(defn.name.as_ref())
                    && let Type::Fn(ref param_types, _) = scheme.ty {
                        return Some(param_types.iter().map(|t| Some(t.clone())).collect());
                }
                None
            })
            .unwrap_or_else(|| vec![None; defn.params().len()]);

        // Bind function parameters from loop header block params (not entry block).
        // Also record parameter types in variable_types so scope cleanup
        // can emit rc_dec for heap-typed parameters at function exit.
        for (i, (param_name, _)) in defn.params().iter().enumerate() {
            let val = self.builder.block_params(loop_header)[i];
            let var = self.fresh_variable();
            self.builder.declare_var(var, types::I64);
            self.builder.def_var(var, val);
            self.variables.insert(param_name.clone(), var);
            self
                .scope_stack
                .last_mut()
                .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                .push(param_name.clone());

            // Use the defn's inferred param type (from symbol table) first.
            // Fall back to derive_param_type_from_body (use-site inference) if the
            // defn type isn't available.
            if let Some(Some(ty)) = defn_param_types.get(i) {
                self.variable_types.insert(param_name.clone(), ty.clone());
            } else if let Some(ty) = Self::derive_param_type_from_body(body, param_name) {
                self.variable_types.insert(param_name.clone(), ty);
            }
        }

        // §3.2 borrow-elision, callee side
        // (`design/backend/ownership-codegen.md` §3.2): each parameter whose
        // ownership summary says `Borrowed` joins `borrowed_vars`. Everything
        // then follows from the existing §5.5 discipline with ZERO new emission
        // logic — no dec at `pop_scope_with_cleanup` (the caller owns the
        // reference), never eligible for last-use ownership transfer
        // (`is_last_use` gate), and passed onward to an `Owned` position gets the
        // ordinary Var consuming inc (§3.1's adaptation). This is the spine §8.2
        // subsumption made literal: an inferred `Borrowed` param is *implemented
        // as* the discipline `borrowed_vars` already enforces for match-arm field
        // bindings. Summary absent (⇒ every param `Owned`) or a `Copy`/scalar
        // param ⇒ nothing inserted, so the callee body is byte-identical to the
        // pre-S102 consuming compilation under `CRANELISP_NO_OWNERSHIP`.
        if let Some(summary) = self.current_mode_summary.clone() {
            for (i, (param_name, _)) in defn.params().iter().enumerate() {
                if summary.param_mode(i) == cranelisp_types::Mode::Borrowed {
                    // Borrowed only ever applies to a heap-typed reference; the
                    // heap-typedness check keeps a mis-shaped summary (a Borrowed
                    // mode on a scalar position) from wrongly suppressing a dec
                    // that never existed — a no-op either way, but explicit.
                    let is_heap = self
                        .variable_types
                        .get(param_name)
                        .is_some_and(|ty| self.is_heap_type(ty));
                    if is_heap {
                        self.mark_borrowed(param_name);
                    }
                }
            }
        }
    }

    /// Compile a monomorphised expression, dispatching to the appropriate
    /// handler.
    ///
    /// The codegen walk is over [`MonoExpr`] (concrete-boundary-type.md §3.1,
    /// FIXME 0391): every node carries a `ty: ConcreteType` non-optionally, so a
    /// `Type::Var` is *unrepresentable* at every codegen-reaching position. The
    /// `Annotate` variant is erased at the `MonoExpr::from_expr` build, so it has
    /// no arm here.
    pub fn compile_expr(&mut self, expr: &MonoExpr) -> Result<Value, CranelispError> {
        match expr {
            MonoExpr::IntLit { value, .. } => self.compile_int_lit(*value),
            MonoExpr::FloatLit { value, .. } => self.compile_float_lit(*value),
            MonoExpr::BoolLit { value, .. } => self.compile_bool_lit(*value),
            MonoExpr::StringLit { value, span, .. } => self.compile_string_lit(value, *span),
            MonoExpr::Var {
                name,
                span,
                resolved_call,
                ty,
            } => {
                // The signature-path bridge: `compile_var` reads the variable's
                // type as a `&Type` (for the value-position trait-method arity).
                // The node's `ConcreteType` embeds losslessly into a `Type`.
                let inferred = ty.to_type();
                self.compile_var(name, *span, resolved_call.as_deref(), Some(&inferred))
            }
            MonoExpr::Let {
                bindings,
                body,
                span,
                ..
            } => self.compile_let(bindings, body, *span),
            MonoExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.compile_if(cond, then_branch, else_branch),
            MonoExpr::Lambda {
                params, body, span, ty, ..
            } => {
                let lambda_type = ty.to_type();
                self.compile_lambda(params, body, *span, Some(&lambda_type))
            }
            MonoExpr::Apply {
                callee,
                args,
                span,
                resolved_call,
                ty,
                ..
            } => {
                let apply_type = ty.to_type();
                self.compile_apply(
                    callee,
                    args,
                    *span,
                    resolved_call.as_deref(),
                    Some(&apply_type),
                )
            }
            MonoExpr::Match {
                scrutinee,
                arms,
                span,
                ..
            } => self.compile_match(scrutinee, arms, *span),
            MonoExpr::VecLit { elements, span, .. } => self.compile_vec_lit(elements, *span),
            MonoExpr::Trace {
                modules,
                body,
                span,
                ..
            } => self.compile_trace(modules, body, *span),
            MonoExpr::ParBind {
                bindings,
                body,
                span,
                ..
            } => self.compile_par_bind(bindings, body, *span),
            MonoExpr::LaunchContinue {
                launched,
                continuation,
                span,
                ..
            } => self.compile_launch_continue(launched, continuation, *span),
            MonoExpr::ConstrADT {
                tag,
                fields,
                span,
                ..
            } => self.compile_constr_adt(*tag, fields, *span),
        }
    }

    /// Allocate a fresh Cranelift Variable index.
    pub(crate) fn fresh_variable(&mut self) -> Variable {
        let idx = self.next_var;
        self.next_var += 1;
        Variable::new(idx as usize)
    }

    pub(crate) fn push_scope(&mut self) {
        self.scope_stack.push(vec![]);
    }

    pub(crate) fn pop_scope(&mut self) {
        if let Some(frame) = self.scope_stack.pop() {
            for name in frame {
                self.variables.remove(&name);
                self.variable_types.remove(&name);
            }
        }
    }

    /// Pop a scope frame and emit `rc_dec` for all heap-typed bindings,
    /// except the variable named by `skip_var` (whose ownership transfers
    /// to the caller as the return value).
    ///
    /// Key invariant: "Scope cleanup emits dec for all heap-typed bindings
    /// EXCEPT the return value, consumed vars, and borrowed vars."
    ///
    /// Borrowed vars (e.g., pattern match field bindings) are skipped entirely —
    /// they share the owner's (scrutinee's) reference and the owner handles cleanup.
    ///
    /// ADT field cleanup happens inside the RC=0 dealloc path (via
    /// `emit_rc_dec_with_inline_drop_glue`), NOT as a separate step before dec.
    /// This prevents double-free when fields are independently referenced.
    pub(crate) fn pop_scope_with_cleanup(
        &mut self,
        skip_var: Option<&Symbol>,
    ) {
        if let Some(frame) = self.scope_stack.last() {
            let frame = frame.clone();
            let to_dec = self.collect_frame_heap_decs(&frame, |this, name| {
                // Skip the return value variable.
                if let Some(skip) = skip_var
                    && name == skip {
                        return true;
                    }
                // Skip borrowed variables (owner handles cleanup).
                this.borrowed_vars.contains(name)
            });
            self.emit_heap_binding_decs(&to_dec);
        }

        // Now actually pop the scope (remove variables from maps).
        self.pop_scope();
    }

    /// Collect the heap-typed bindings in `frame` that need an `rc_dec`, minus
    /// those `skip` returns `true` for. Extracted so `pop_scope_with_cleanup`
    /// and the tail-call scope flush (`flush_let_scopes_before_tail_jump`) share
    /// one filter + type-resolution (Principle 7).
    fn collect_frame_heap_decs(
        &self,
        frame: &[Symbol],
        skip: impl Fn(&Self, &Symbol) -> bool,
    ) -> Vec<(Symbol, Type, bool)> {
        frame
            .iter()
            .filter(|name| {
                if skip(self, name) {
                    return false;
                }
                if let Some(ty) = self.variable_types.get(*name) {
                    self.is_heap_type(ty)
                } else {
                    false
                }
            })
            .map(|name| {
                let ty = self.variable_types.get(name).cloned().unwrap_or(Type::Int);
                let needs_guard = matches!(
                    signature_heap_category(&ty, Some(self.ctx.symbol_tables)),
                    HeapCategory::Mixed
                );
                (name.clone(), ty, needs_guard)
            })
            .collect()
    }

    /// Emit the `rc_dec` for each collected heap binding (closures → embedded
    /// drop glue; Vec → `vec_drop`; ADT → inline drop glue in the dealloc path).
    /// Shared by scope-pop cleanup and the tail-call flush.
    fn emit_heap_binding_decs(&mut self, to_dec: &[(Symbol, Type, bool)]) {
        let dealloc = self.ctx.dealloc_func_id;
        for (name, ty, needs_guard) in to_dec {
            if let Some(var) = self.variables.get(name) {
                let val = self.builder.use_var(*var);

                // For closures (Type::Fn), use runtime-embedded drop glue.
                // This handles both locally-created closures AND closures
                // received as function parameters (where the static
                // closure_drop_glue map has no entry).
                if matches!(ty, Type::Fn(_, _)) {
                    self.emit_closure_dec_inline(val, dealloc);
                    continue;
                }

                // For Vec-typed bindings: must route through vec_drop to
                // dec each element and free the data buffer; the generic
                // rc_dec → dealloc path leaks both.
                if let Some(elem_ty) = crate::compiler::vec_codegen::vec_element_type(ty) {
                    let elem_ty = elem_ty.clone();
                    let span = cranelisp_types::Span::new(0, 0);
                    let _ = self.emit_vec_aware_rc_dec(val, &elem_ty, span);
                    continue;
                }

                // For ADTs: emit RC dec with inline drop glue in the
                // dealloc path. Field cleanup ONLY happens when RC
                // reaches 0 (inside the free branch), not unconditionally.
                // This prevents double-free when fields are independently
                // referenced (e.g., extracted via pattern match).
                self.emit_rc_dec_with_inline_drop_glue(val, ty, dealloc, *needs_guard);
            }
        }
    }

    /// Flush `rc_dec` for the live LET-scope bindings BEFORE a tail self-call
    /// jump (`compile_tail_self_call`). Without this, the enclosing
    /// `compile_let_sequential` emits `pop_scope_with_cleanup` AFTER
    /// `compile_expr(body)` — but the tail-call jump has already terminated the
    /// block, so those decs land in the dead post-jump block and never execute:
    /// every heap-typed `let` binding that survives to a tail-recursive scope
    /// exit leaks one allocation per iteration (the S102 drafting `vec_cow_value_use`
    /// guards; the true root cause the §13.3 Ruling-2 COW-copy attribution missed).
    ///
    /// Scope frames `[1..]` are the `let`/match/lambda frames; frame `0` is the
    /// function's parameter frame, which the TCO loop header *reuses* (its block
    /// params are overwritten each iteration) — its RC is out of this fix's scope
    /// (unchanged behaviour). `transfer_skip` names bindings whose reference
    /// transfers into a tail-call argument (a direct `Var` arg — no consuming inc
    /// is emitted for it), so dec'ing them here would double-free the value the
    /// new iteration now owns. Consumed / borrowed bindings are skipped as in
    /// `pop_scope_with_cleanup`. The frames are NOT popped — the enclosing
    /// `compile_let_sequential` still pops them (into the now-dead block).
    pub(crate) fn flush_let_scopes_before_tail_jump(
        &mut self,
        transfer_skip: &std::collections::HashSet<Symbol>,
    ) {
        if self.scope_stack.len() <= 1 {
            return;
        }
        // Innermost-first: collect all eligible bindings across the let frames.
        let mut to_dec: Vec<(Symbol, Type, bool)> = Vec::new();
        for frame in self.scope_stack[1..].iter().rev() {
            let frame = frame.clone();
            let mut frame_decs = self.collect_frame_heap_decs(&frame, |this, name| {
                if transfer_skip.contains(name) {
                    return true;
                }
                this.borrowed_vars.contains(name)
            });
            to_dec.append(&mut frame_decs);
        }
        self.emit_heap_binding_decs(&to_dec);
    }

    /// True iff `flush_let_scopes_before_tail_jump` would emit an `rc_dec` for
    /// `name`: it lives in a `let`/match/lambda frame (`scope_stack[1..]` — NOT
    /// the param frame `[0]`, which the loop header reuses and the flush leaves
    /// untouched), is heap-typed, and is not borrowed. This is the exact
    /// predicate the flush's `collect_frame_heap_decs` filter applies, so a
    /// protective inc gated on it balances the flush dec one-for-one.
    pub(crate) fn tail_flush_will_dec(&self, name: &Symbol) -> bool {
        let in_let_frame = self
            .scope_stack
            .iter()
            .skip(1)
            .any(|frame| frame.contains(name));
        if !in_let_frame || self.borrowed_vars.contains(name) {
            return false;
        }
        self.variable_types
            .get(name)
            .is_some_and(|ty| self.is_heap_type(ty))
    }

    /// Under `tail_arg_protect` (set while compiling an `if`/`match` that is a
    /// direct tail-call argument), emit a protective `rc_inc` on `val` iff
    /// `branch` is a bare `Var` that directly aliases a live heap `let`-binding
    /// the tail-jump flush will `rc_dec` (`tail_flush_will_dec`).
    ///
    /// Why this is correct for the F1 cases (design/backend/ownership-codegen.md
    /// §13.3):
    /// - `(recur (if c v v))` — each branch result is the binding `v`; one branch
    ///   runs, incs `v` once, the flush decs it once → the loop param owns `v`.
    /// - `(recur (if c lo hi))` — distinct bindings: the taken branch incs its
    ///   binding, the flush decs BOTH `lo` and `hi`, so the moved one nets to the
    ///   loop param and the dead one is freed — impossible with a single static
    ///   skip-dec, which is why per-branch protection + uniform flush is used.
    /// - `(recur (if c (wrap v) v))` — the `wrap` branch result is fresh (an
    ///   `Apply`, not a scope-binding `Var`) so it is NOT protected; `wrap`
    ///   already inc'd `v` internally and the flush's dec of `v` balances it. The
    ///   bare-`v` branch IS protected. Both runtime paths balance.
    ///
    /// A branch whose result reaches the tail through a nested scope exit
    /// (`(if c (let [w …] v) …)`) is already protected by that scope's own
    /// `protect_return_value` inc (the tail flush being the balancing "caller"
    /// dec), so this helper only needs to cover the DIRECT bare-`Var` branch.
    /// Returns `val` unchanged so callers can thread it inline.
    pub(crate) fn maybe_protect_tail_arg_alias(
        &mut self,
        branch: &MonoExpr,
        val: Value,
    ) -> Value {
        if !self.tail_arg_protect {
            return val;
        }
        if let MonoExpr::Var { name, .. } = branch
            && self.tail_flush_will_dec(name)
            && let Some(ty) = self.variable_types.get(name).cloned()
        {
            match signature_heap_category(&ty, Some(self.ctx.symbol_tables)) {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_inc(&mut self.builder, self.module, val);
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_inc_guarded(&mut self.builder, self.module, val);
                }
                HeapCategory::NeverHeap => {}
            }
        }
        val
    }

    /// If `body` is a direct variable reference to a name in the current scope
    /// frame, return that name. Used to skip rc_dec for the return value.
    pub(crate) fn return_var_in_scope(
        body: &MonoExpr,
        scope_frame: Option<&Vec<Symbol>>,
    ) -> Option<Symbol> {
        if let MonoExpr::Var { name, .. } = body
            && let Some(frame) = scope_frame
                && frame.contains(name) {
                    return Some(name.clone());
                }
        None
    }

    /// Check if a type is heap-allocated and needs RC management.
    pub(crate) fn is_heap_type(&self, ty: &Type) -> bool {
        matches!(
            signature_heap_category(ty, Some(self.ctx.symbol_tables)),
            HeapCategory::AlwaysHeap | HeapCategory::Mixed
        )
    }

    /// Derive a function parameter's type by finding a Var reference with the
    /// given name in the function body and reading its `inferred_type()`.
    ///
    /// Function parameters don't have their own `inferred_type`, but every
    /// Var reference to the parameter in the body does. We walk the body AST
    /// to find the first Var node matching the name.
    pub(crate) fn derive_param_type_from_body(body: &MonoExpr, name: &Symbol) -> Option<Type> {
        find_var_type_in_expr(body, name)
    }

    /// Check if a variable use is the last use (for ownership transfer).
    pub(crate) fn is_last_use(&self, name: &Symbol, span: Span) -> bool {
        if self.captured_vars.contains(name) {
            // Captured variables are NEVER eligible for last-use transfer.
            return false;
        }
        if self.borrowed_vars.contains(name) {
            // Borrowed variables (extracted from a match scrutinee's field)
            // do NOT own the value — the scrutinee still holds it. A
            // textually-last use of a borrowed var does not imply ownership
            // transfer, so Vec COW mutate-in-place on such a binding would
            // alias the scrutinee's field and cause a double-free once the
            // scrutinee's drop glue dec's the field independently. See
            // `design/backend/ring2-rc.md §3.1` (Decision 24 consuming
            // convention) and §5.5 (captured_vars rule — the borrowed_vars
            // rule is its structural twin: neither owns the value, so
            // neither may transfer ownership via last-use).
            // Regression: repro-slice2.cl — `(consume (Box [0]))` read len=0.
            return false;
        }
        self.last_uses
            .get(&(name.clone(), span))
            .copied()
            .unwrap_or(false)
    }

    /// Mark a variable as borrowed (skip scope-exit dec — owner handles cleanup).
    pub(crate) fn mark_borrowed(&mut self, name: &Symbol) {
        self.borrowed_vars.insert(name.clone());
    }
}

/// B3.2 borrow-elision return-protect decision
/// (`design/backend/ownership-codegen.md` §3.3): `true` iff the compiled
/// function's return-protect inc (`protect_return_value`) may be elided because
/// its ownership summary proves the return value is a fresh (non-aliased) value.
///
/// Sound-consumer contract (post-FIXME-0520, see
/// [`FnCompiler::return_is_fresh_by_summary`] for the full rationale):
/// `summary` is `Some` with `result == ResultMode::Fresh`. `None` ⇒ Decision-24
/// (protect verbatim) — the byte-identical-`CRANELISP_NO_OWNERSHIP` guarantee.
///
/// `Fresh` is sound for **any** body shape now that `join_origin` no longer
/// collapses a partial control-flow param-return to `Fresh` (a body that returns
/// a param on any reachable path reports `AliasOf`/`ProjectionOf`, never
/// `Fresh`). `_body` is retained for the seam signature but no longer read.
pub(crate) fn return_is_fresh_by_summary(
    _body: &MonoExpr,
    summary: Option<&cranelisp_types::ModeSummary>,
) -> bool {
    summary.is_some_and(|s| s.result == cranelisp_types::ResultMode::Fresh)
}

#[cfg(test)]
mod return_protect_tests {
    //! B3.2 return-protect elision decision matrix (Principle 23 —
    //! `design/backend/ownership-codegen.md` §13.5 apply/rc_emission row):
    //! body-variant × result-mode × summary-presence → skip-protect verdict.
    use super::return_is_fresh_by_summary;
    use cranelisp_types::{ConcreteType, ModeSummary, MonoExpr, ResultMode, Span, Symbol};

    fn int_ty() -> ConcreteType {
        ConcreteType::Int
    }

    fn apply_body() -> MonoExpr {
        MonoExpr::Apply {
            callee: Box::new(MonoExpr::Var {
                name: Symbol::from("f"),
                span: Span::new(0, 1),
                resolved_call: None,
                ty: int_ty(),
            }),
            args: vec![],
            span: Span::new(0, 3),
            resolved_call: None,
            ty: int_ty(),
            escapes: None,
            confined: None,
            unique_static: None,
            provenance: None,
        }
    }

    fn if_body() -> MonoExpr {
        MonoExpr::If {
            cond: Box::new(MonoExpr::BoolLit { value: true, span: Span::new(0, 1), ty: ConcreteType::Bool }),
            then_branch: Box::new(MonoExpr::Var { name: Symbol::from("v"), span: Span::new(1, 2), resolved_call: None, ty: int_ty() }),
            else_branch: Box::new(MonoExpr::Var { name: Symbol::from("w"), span: Span::new(2, 3), resolved_call: None, ty: int_ty() }),
            span: Span::new(0, 4),
            ty: int_ty(),
        }
    }

    fn var_body() -> MonoExpr {
        MonoExpr::Var { name: Symbol::from("v"), span: Span::new(0, 1), resolved_call: None, ty: int_ty() }
    }

    fn fresh() -> ModeSummary {
        ModeSummary { result: ResultMode::Fresh, ..Default::default() }
    }
    fn alias0() -> ModeSummary {
        ModeSummary { result: ResultMode::AliasOf(0), ..Default::default() }
    }
    fn proj0() -> ModeSummary {
        ModeSummary { result: ResultMode::ProjectionOf(0), ..Default::default() }
    }

    // POSITIVE: a PRESENT Fresh summary elides for ANY body shape (post-0520 —
    // the Apply-body restriction is dropped; `Fresh` is now sound for if/match/
    // var bodies because `join_origin` never collapses a partial param-return to
    // `Fresh`).
    #[test]
    fn fresh_summary_elides_all_body_shapes() {
        assert!(return_is_fresh_by_summary(&apply_body(), Some(&fresh())));
        assert!(return_is_fresh_by_summary(&if_body(), Some(&fresh())));
        assert!(return_is_fresh_by_summary(&var_body(), Some(&fresh())));
    }

    // NEGATIVE (byte-identical-off): no summary ⇒ never elide, ANY body.
    #[test]
    fn absent_summary_never_elides() {
        assert!(!return_is_fresh_by_summary(&apply_body(), None));
        assert!(!return_is_fresh_by_summary(&if_body(), None));
        assert!(!return_is_fresh_by_summary(&var_body(), None));
    }

    // NEGATIVE (aliasing result modes): AliasOf / ProjectionOf keep protect —
    // the returned value aliases a param and scope cleanup may free it.
    #[test]
    fn aliasing_result_modes_never_elide() {
        assert!(!return_is_fresh_by_summary(&apply_body(), Some(&alias0())));
        assert!(!return_is_fresh_by_summary(&apply_body(), Some(&proj0())));
    }
}
