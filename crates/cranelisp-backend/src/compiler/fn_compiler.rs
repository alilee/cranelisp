//! The per-function CLIF emitter: the `FnCompiler` struct, its construction
//! (`inner`, `compile_body`, `bind_defn_params`), the expression-dispatch entry
//! (`compile_expr`), scope lifecycle, and the small per-fn predicates.
//! `MatchContext` is per-arm `FnCompiler` state, kept adjacent to the struct it
//! threads through.

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use cranelisp_types::{
    CranelispError, Defn, MonoExpr, ModuleEntry, ResolvedCall, Span, Symbol, Type,
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

    /// Lazily-built, per-compiler cache of the recursive-SCC membership set over
    /// the loaded call graph — the M-static QUALITY-axis signal
    /// (`design/backend/lenient-eval.md` §2.8.2/§2.8.6). Populated on first use by
    /// `mstatic_recursive_set` (interior-mutable so the `&self` admission path can
    /// fill it) and read at every spark-eligible `let`/apply site under
    /// `CRANELISP_SPARK_ADMIT=mstatic` (the default), so the O(defs) Tarjan pass
    /// runs once per compiler instance rather than per candidate site. Empty until
    /// the first M-static admission decision; never built under the `syntactic`
    /// filter or when no site is spark-eligible.
    pub(crate) mstatic_recursive_cache:
        std::cell::RefCell<Option<std::rc::Rc<std::collections::HashSet<cranelisp_types::FQSymbol>>>>,

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

    /// B3.4 gate 3 (`design/backend/ownership-codegen.md` §4.1): `true` iff the
    /// function body being compiled contains a self-recursive call (a potential
    /// TCO loop back-edge). When set, stack-slot placement is declined for the
    /// WHOLE function ([`stack_eligible`] → false) — a stack slot allocated once
    /// per frame and reused across TCO iterations would clobber a loop-carried
    /// value. Computed once by [`body_has_self_call`] in [`compile_body`];
    /// `false` for every inner compiler (lambda / continuation / drop-glue
    /// bodies), which is sound (they only DECLINE more, never enable — those
    /// bodies' own allocations are compiled with the outer decision, and inner
    /// bodies are heap by construction pending the spark/escape gates §4.3).
    pub(crate) fn_has_self_call: bool,

    /// B3.4 gate 5 (`design/backend/ownership-codegen.md` §4.3; FIXME 0525
    /// `/arch` ruling 2026-07-05): `true` while compiling a **backend-synthesized
    /// spark-thunk body** — the `MonoExpr::Lambda` (or dependent-thunk RHS) the
    /// backend relocates a lenient-sparked construction into. When set,
    /// [`constructor_call_stack_eligible`] declines stack placement: the thunk
    /// frame pops at the spark→join while the parent consumes the value, so a
    /// stack slot built there dangles (hard UAF — the FIXME 0525 signature).
    /// This is the identical frame-restructuring shape to gate 3 (TCO back-edge),
    /// one strand over: the escape fact is correct for the strict `MonoExpr`
    /// frame the analysis ran over, but the backend rewrites that frame structure
    /// underneath it. Raised by [`FnCompiler::compile_spark_thunk`] (apply-arg +
    /// independent-`let` sparks) and set directly on the dependent-thunk inner
    /// compiler (`dependent_spark.rs`); propagated into the thunk-body inner
    /// `FnCompiler` by `compile_lambda_body`. Declining is always sound; under
    /// `NO_LENIENT` no thunk is synthesized so this never sets and the full
    /// stack-alloc win lands.
    pub(crate) in_spark_thunk: bool,

    /// §3.3 in-frame projection elision — consumer-driven
    /// (`design/backend/ownership-codegen.md` §3.3): the span of the ONE
    /// `vec-get` node whose heap-element materialization inc `compile_vec_get`
    /// should SKIP, or `None`. Set (with save/restore) by
    /// [`FnCompiler::compile_consuming_arg_list_moded`] to the span of a borrowed
    /// projection argument (site fact `provenance`) being passed DIRECTLY into a
    /// `Borrowed` parameter — the sole provably-safe elision: the borrowed element
    /// is consumed in-place by the callee's borrow, never escapes the enclosing
    /// expression, and never outlives the root's fork-join-guaranteed liveness
    /// (the F1 machinery-tax collapse). Span-matched so exactly that read elides
    /// and no other. `None` ⇒ every `vec-get` incs verbatim — byte-identical-off
    /// (§2.2).
    pub(crate) elide_vecget_span: Option<Span>,

    /// The heap scope binding whose reference the function's TAIL COW op
    /// (`(vec-set v …)` / `(vec-push v …)`) moves into the returned Vec, or
    /// `None`. Set once at function-body setup ([`FnCompiler::compile_body`])
    /// from [`FnCompiler::return_cow_source_in_scope`].
    ///
    /// A COW op's in-place arm (rc==1) returns the SAME Vec pointer, so its
    /// source reference transfers into the returned value; but the source is a
    /// scope binding that scope-exit would `rc_dec`, freeing the just-returned
    /// Vec (the `tests/vec_assoc_param_mutate_return_uaf.rs` premature-free). Two
    /// coordinated effects key on this field: (1) the source var is passed as the
    /// `skip_var` so `pop_scope_with_cleanup` suppresses its scope-exit dec (the
    /// ref lives on as the return value); (2) `compile_vec_set`/`compile_vec_push`
    /// switch the COW **copy** branch from `Borrowed` to `Owned` so the copy path
    /// (which returns a FRESH Vec, leaving the source unreferenced) releases the
    /// source itself — scope cleanup no longer does. Both arms are then correct:
    /// in-place transfers, copy releases, and the source is decremented exactly
    /// once on every path. `None` ⇒ every COW site keeps its `Borrowed` polarity,
    /// byte-identical to pre-fix.
    pub(crate) return_cow_source: Option<Symbol>,
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
            mstatic_recursive_cache: std::cell::RefCell::new(None),
            gate_arm_disc: String::new(),
            gate_counter: 0,
            suppress_spark_gate: false,
            spark_capture_borrow: false,
            // Inner compilers (lambda / continuation / drop-glue bodies) never
            // enable stack placement of their own (§4.1/§4.3 — those bodies are
            // heap by construction pending the spark/escape gates); `false` is
            // the sound default.
            fn_has_self_call: false,
            // Gate 5 (§4.3): default off; spark-thunk-body inner compilers set it
            // explicitly (`compile_lambda_body` propagates the outer flag;
            // `dependent_spark.rs` sets it directly on its dedicated inner).
            in_spark_thunk: false,
            elide_vecget_span: None,
            return_cow_source: None,
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

        // B3.4 gate 3 (§4.1): a self-recursive call becomes a TCO loop back-edge;
        // a stack slot (one per frame) reused across iterations would clobber a
        // loop-carried value. Decline stack placement for the whole function when
        // the body self-calls (conservative — see `body_has_self_call`).
        let fn_has_self_call = body_has_self_call(body, &defn.name);

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
            mstatic_recursive_cache: std::cell::RefCell::new(None),
            gate_arm_disc: String::new(),
            gate_counter: 0,
            suppress_spark_gate: false,
            spark_capture_borrow: false,
            fn_has_self_call,
            // Gate 5 (§4.3): a top-level `defn` body is never itself a spark thunk;
            // the flag is raised only around the backend-synthesized thunk compiles.
            in_spark_thunk: false,
            elide_vecget_span: None,
            return_cow_source: None,
        };

        // Seed the function's parameters into scope + variable_types.
        compiler.bind_defn_params(defn, body, loop_header);

        // Compile the function body with scope cleanup for parameters.
        // This implements the consuming calling convention: the callee owns
        // heap-typed parameters and dec's them at exit. The caller inc's
        // variable arguments before the call.
        let skip_var = Self::return_var_in_scope(body, compiler.scope_stack.last());
        // vec-assoc UAF fix (`tests/vec_assoc_param_mutate_return_uaf.rs`): a tail
        // COW op (`(vec-set v …)` / `(vec-push v …)`) on a heap scope binding `v`
        // returns `v`'s backing (in-place arm) — the returned Vec IS `v`. Suppress
        // `v`'s scope-exit dec (fold it into `skip_var`, mutually exclusive with a
        // bare-Var return) and record it so the COW site flips its copy branch to
        // the `Owned` polarity (see the `return_cow_source` field rustdoc).
        let cow_return_source =
            return_cow_source_in_scope(body, compiler.scope_stack.last());
        compiler.return_cow_source = cow_return_source.clone();
        let skip_var = skip_var.or(cow_return_source);
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
                resolved_target,
                ty,
                ..
            } => {
                // The signature-path bridge: `compile_var` reads the variable's
                // type as a `&Type` (for the value-position trait-method arity).
                // The node's `ConcreteType` embeds losslessly into a `Type`.
                //
                // S110 W2 (`backend-keyed-consumer.md` §4; S10–S18): the Var's
                // `resolved_target` — the terminal STORAGE key typecheck resolved
                // (§1.1.2) — is threaded to the value-seam keyed reads (fn-as-value
                // gate, nullary-ctor fold, ctor-as-value, arity, summary, vec-query,
                // GOT entry). A local/lambda-param Var carries `None` (the backend
                // `variables` check precedes any keyed read — KC-N6).
                let inferred = ty.to_type();
                self.compile_var(
                    name,
                    *span,
                    resolved_call.as_deref(),
                    Some(&inferred),
                    resolved_target.as_ref(),
                )
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
                resolved_target,
                ty,
                ..
            } => {
                // B3.4 (§4.1): a use-site data-constructor call `(Rect n n)` is
                // an `Apply` whose result is allocated in THIS (the caller's)
                // frame (inlined via `emit_adt_construct`). The escape fact is on
                // the `Apply` node (dropped by this dispatch), so compute the
                // stack-vs-heap verdict here and thread it down — the constructor
                // arm of `compile_var_apply` is the sole consumer. `false` ⇒
                // today's heap path verbatim. (The synthetic `ConstrADT`
                // constructor-function body is NOT a stack site — it returns its
                // value to the caller and stays heap.)
                let stack = self.constructor_call_stack_eligible(expr, args);
                let apply_type = ty.to_type();
                self.compile_apply(
                    callee,
                    args,
                    *span,
                    resolved_call.as_deref(),
                    // S110 W1: the Apply-span dispatch carrier (`backend-keyed-
                    // consumer.md` §1.1) — the STORAGE FQ typecheck's dispatch
                    // selection resolved to (trait/sig-dispatch/auto-curry/operator
                    // legs). The backend keys its ONE fetch on this instead of
                    // re-scanning the symbol tables. `None` for a Var-callee direct
                    // call (that carrier rides on the callee `Var` node).
                    resolved_target.as_ref(),
                    Some(&apply_type),
                    stack,
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
                ty,
                ..
            } => self.compile_constr_adt(*tag, fields, *span, ty),
        }
    }

    /// B3.3 (`design/backend/ownership-codegen.md` §5.1): the per-site RC
    /// atomicity for a value produced DIRECTLY by `node` — `NonAtomic` iff the
    /// node carries `confined = Some(true)`. Used at emission sites where the
    /// allocation/capture-producing node is in hand (materialization incs).
    /// `Some(false)` (Crossing) / `None` (fact absent / analysis off) ⇒
    /// `Atomic`, verbatim today.
    pub(crate) fn rc_atomicity_for_node(&self, node: &MonoExpr) -> heap::RcAtomicity {
        let confined = node_confined(node);
        // N3 (S105, `design/backend/ownership-codegen.md` §13.2.2): record this
        // confinement-classified RC site for the residual-atomic-RC attribution dump
        // (`[RC_SITE_STATS]`). Gated on `CRANELISP_RC_STATS`, host-side, no emitted IR
        // ⇒ byte-identical-off. The emitting node's span + the enclosing fn FQ +
        // the confinement class are all in hand here (the live `node_confined`
        // consumer), so this is the site the dump keys on.
        crate::rc_site_stats::record_rc_site_if_enabled(
            &self.ctx.current_module,
            self.current_fn_name.as_ref(),
            node.span(),
            confined,
        );
        match confined {
            Some(true) => heap::RcAtomicity::NonAtomic,
            _ => heap::RcAtomicity::Atomic,
        }
    }

    /// B3.4 (`design/backend/ownership-codegen.md` §4.1): is the use-site
    /// data-constructor call `apply` (a `MonoExpr::Apply` whose callee is a
    /// constructor, e.g. `(Rect n n)`) eligible for a Cranelift **stack slot**
    /// (immortal-RC sentinel, §4.2) in the caller's frame instead of the RC heap?
    ///
    /// The construction is inlined in the caller's frame (`emit_adt_construct`,
    /// `apply.rs`), so the caller's escape fact — carried on this `Apply` node —
    /// authoritatively decides whether the aggregate may live on the stack. (The
    /// synthetic `ConstrADT` constructor-*body* is a different node that always
    /// returns to its caller and stays heap; it never reaches this predicate.)
    ///
    /// **All four eligibility gates, backend-local, CONSERVATIVE by default —
    /// when in doubt, HEAP:**
    /// 1. **Statically sized** — always true (`HeapAdt::payload_size(n_fields)`;
    ///    the arg/field count is fixed).
    /// 2. **All-scalar payload** — every constructor arg (= stored field)
    ///    classifies `NeverHeap` (Int / Bool / Float / nullary tag). A stack
    ///    aggregate holding a heap-typed field would owe a frame-exit field
    ///    release its drop glue never runs (§4.2 — the immortal sentinel means the
    ///    ADT never reaches rc=0, so its drop glue never decs the field ⇒ a leak).
    ///    The zero-obligation scalar class ships first.
    /// 3. **Not reachable by a TCO back-edge** — declined for the whole function
    ///    when it self-calls ([`FnCompiler::fn_has_self_call`] / `body_has_self_call`).
    /// 4. **Extern-produced values are ineligible by construction** — an inlined
    ///    constructor allocation is backend-emitted, not an extern `alloc_with_rc`
    ///    body; there is no allocator seam to redirect in increment I.
    ///
    /// 5. **Not relocated across a spark boundary** ([`FnCompiler::in_spark_thunk`],
    ///    §4.3; FIXME 0525 `/arch` ruling 2026-07-05) — a construction the backend
    ///    relocates into a synthesized spark-thunk body (lenient apply-arg /
    ///    independent-`let` / dependent-`let` sparks) lives in a thunk frame that
    ///    pops at the join, so its stack slot dangles once the parent consumes the
    ///    value. This is gate 3's frame-restructuring shape one strand over: the
    ///    escape fact is correct for the strict `MonoExpr` frame the analysis ran
    ///    over, but the backend rewrites that frame structure underneath it. The
    ///    backend owns the spark-placement decision, so it is the only actor that can
    ///    gate here — a backend-local emission sharpening, not an analysis fact.
    ///    Declining is always sound; under `NO_LENIENT` no thunk is synthesized, the
    ///    flag never sets, and the full stack-alloc win lands.
    ///
    /// The `escapes = Some(false)` precondition is the analysis' NoEscape verdict
    /// (the FIRST hard consumer of the escape fact). `Some(true)` / `None`
    /// (analysis off) ⇒ heap — so `CRANELISP_NO_OWNERSHIP` is byte-identical to
    /// pre-B3.4 (no node carries `Some(false)`, this returns false everywhere).
    ///
    /// **Downstream guard:** the returned `bool` is a *hint*; it only becomes a
    /// stack allocation if `compile_var_apply` confirms the callee is actually a
    /// data constructor (`data_constructor_info`). For any other `Apply` shape
    /// the hint is ignored — the aggregate emission (`emit_adt_construct`) is not
    /// reached.
    pub(crate) fn constructor_call_stack_eligible(
        &self,
        apply: &MonoExpr,
        args: &[MonoExpr],
    ) -> bool {
        // ===================================================================
        // B3.4 ACTIVATED (2026-07-05, FIXME 0525 `/arch` ruling). The escape fact
        // (comprehensively sound post-FIXME 0523/0524) is the precondition; gate 5
        // (`in_spark_thunk`) closes the lenient-eval-vs-stack-alloc structural gap.
        //
        // The `STACK_ALLOC_ESCAPE_FACT_SOUND` const is now the analysis-off oracle
        // switch: `false` restores the pre-B3.4 all-heap conservative point
        // (byte-identical). With it `true`, a construction is stack-eligible iff the
        // analysis proved it NoEscape (gate: escape precondition) AND none of the
        // backend-local sharpenings (gates 3, 5) declines it.
        // N4 (S105, §13.2.2): the FINE stack-oracle gate. `stack_alloc_enabled()`
        // AND-s the `STACK_ALLOC_ESCAPE_FACT_SOUND` const default with a runtime
        // env read of `CRANELISP_NO_STACK_ALLOC` — declining stack-alloc ONLY
        // (borrow / non-atomic-RC / reuse stay live), the fine granularity the
        // COARSE `CRANELISP_NO_OWNERSHIP` cannot give. Codegen-time read (once,
        // via `OnceLock`), so ZERO runtime cost; with the env unset it returns the
        // const default (`true`) ⇒ byte-identical codegen to today (§2.2).
        if !stack_alloc_enabled() {
            return false;
        }
        // Precondition: the analysis must have proved this allocation NoEscape.
        if node_escapes(apply) != Some(false) {
            return false;
        }
        // Gate 3: decline for any self-recursive (TCO-back-edge-bearing) function.
        if self.fn_has_self_call {
            return false;
        }
        // Gate 5 (FIXME 0525, §4.3): decline any construction the backend relocates
        // into a spark thunk. Under lenient eval the backend synthesizes a
        // `MonoExpr::Lambda` spark-thunk body (apply-arg / independent-`let` /
        // dependent-`let` sparks) whose frame pops at the join; a stack slot built
        // there dangles once the parent consumes the freed value (`match failed` —
        // hard UAF, the 0525 signature). The escape fact is CORRECT for the strict
        // `MonoExpr` frame the analysis ran over — the backend REWRITES that frame
        // underneath it (gate 3's shape one strand over). Raised by
        // `compile_spark_thunk` / `define_dependent_thunk_body` and propagated into
        // the thunk-body inner `FnCompiler`. Declining is always sound; under
        // `NO_LENIENT` no thunk is synthesized so this never fires and the full win
        // lands.
        if self.in_spark_thunk {
            return false;
        }
        // Gate 1 (statically sized: always) + Gate 2 (all-scalar payload) + Gate 4
        // (backend-emitted). A zero-arg (nullary) constructor is a bare tag with no
        // allocation, so `all` is vacuously true but the emission never reaches a
        // stack slot — harmless.
        !args.is_empty() && args.iter().all(|a| self.node_is_scalar(a.ty()))
    }

    /// B3.4 gate 2 helper: does `ty` classify as a scalar (`NeverHeap`) payload —
    /// Int / Bool / Float / a nullary-only ADT (bare tag)? `AlwaysHeap` and
    /// `Mixed` both fail (conservative: a `Mixed` field may be a live heap
    /// pointer whose reference the stack aggregate's never-run drop glue would
    /// leak).
    fn node_is_scalar(&self, ty: &cranelisp_types::ConcreteType) -> bool {
        matches!(
            HeapCategory::classify(ty, Some(self.ctx.symbol_tables)),
            HeapCategory::NeverHeap
        )
    }

    /// Compile `thunk_expr` as a backend-synthesized **spark-thunk body**
    /// (`design/backend/ownership-codegen.md` §4.3; FIXME 0525 gate 5). Single
    /// source (Principle 7) for the lenient-eval spark sites that relocate a
    /// construction into a `MonoExpr::Lambda` thunk running on a separate strand:
    /// the apply-arg spark (`apply.rs`) and the independent-`let` spark
    /// (`let_if.rs`). It raises two flags for the duration of the thunk compile and
    /// restores them (save/set/restore; restored on the error path too so a `?` in
    /// the caller never leaks a raised flag):
    ///
    /// - **`spark_capture_borrow`** (toggle-gated by `CAPTURE_BORROW_ENABLED`) — the
    ///   S99 capture-by-borrow flag, consumed in the OUTER frame's closure
    ///   capture-store (`compile_lambda` / `build_closure_drop_glue`).
    /// - **`in_spark_thunk`** (unconditional) — gate 5: propagated into the INNER
    ///   `FnCompiler` that compiles the thunk's `Lambda` body (`compile_lambda_body`),
    ///   where the relocated construction lives, so stack allocation is declined
    ///   there (the thunk frame pops at the join — a stack slot dangles).
    ///
    /// The dependent-`let` spark (`dependent_spark.rs`) does NOT use this helper: it
    /// deliberately EXCLUDES `spark_capture_borrow` (the §4.5 carve-out — its
    /// synthetic IVar-pointer captures are keepalives, not live-parent borrows) and
    /// sets `in_spark_thunk` directly on its dedicated inner compiler.
    pub(crate) fn compile_spark_thunk(
        &mut self,
        thunk_expr: &MonoExpr,
    ) -> Result<Value, CranelispError> {
        let saved_borrow = self.spark_capture_borrow;
        let saved_in_spark = self.in_spark_thunk;
        self.spark_capture_borrow = *super::control_flow::CAPTURE_BORROW_ENABLED;
        self.in_spark_thunk = true;
        let res = self.compile_expr(thunk_expr);
        self.spark_capture_borrow = saved_borrow;
        self.in_spark_thunk = saved_in_spark;
        res
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
                    // B3.3-R (§5.2): the scope-cleanup Vec dec is always atomic.
                    // The through-binding half (per-binding Confined carrier) was
                    // dropped as dead + latent-race code (/review B3.3); the
                    // analysis produces no confined let-bindings today, so this
                    // dec was provably always atomic. The `_atomicity` mechanism
                    // is retained (probe-reachable); it is fed `Atomic` here.
                    let _ = self.emit_vec_aware_rc_dec(
                        val, &elem_ty, span, heap::RcAtomicity::Atomic,
                    );
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
            // B3.3-R (§5.1): the protective inc balancing the tail-flush dec is
            // always atomic. This was a through-binding site (per-binding
            // Confined carrier), dropped as dead + latent-race code (/review
            // B3.3) — the analysis produces no confined let-bindings today, so
            // the inc was provably always atomic. The `_atomicity` mechanism is
            // retained (probe-reachable); it is fed `Atomic` here.
            let atomicity = heap::RcAtomicity::Atomic;
            match signature_heap_category(&ty, Some(self.ctx.symbol_tables)) {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_inc_atomicity(&mut self.builder, self.module, val, atomicity);
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_inc_guarded_atomicity(
                        &mut self.builder, self.module, val, atomicity,
                    );
                }
                HeapCategory::NeverHeap | HeapCategory::Value => {}
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

/// B3.3 (`design/backend/ownership-codegen.md` §5.1): read the `confined` site
/// fact off a [`MonoExpr`] node. Only the five allocation/capture-producing
/// variants carry the fact (`StringLit`, `Lambda`, `Apply`, `VecLit`,
/// `ConstrADT` — the enum-level rustdoc on `MonoExpr`); every other variant has
/// no cell of its own to confine and answers `None` (⇒ conservative `Atomic`).
/// Backend-local (no `cranelisp-types` accessor); kept a total match so a new
/// fact-bearing variant is a compile error here.
pub(crate) fn node_confined(node: &MonoExpr) -> Option<bool> {
    match node {
        MonoExpr::StringLit { confined, .. }
        | MonoExpr::Lambda { confined, .. }
        | MonoExpr::Apply { confined, .. }
        | MonoExpr::VecLit { confined, .. }
        | MonoExpr::ConstrADT { confined, .. } => *confined,
        MonoExpr::IntLit { .. }
        | MonoExpr::FloatLit { .. }
        | MonoExpr::BoolLit { .. }
        | MonoExpr::Var { .. }
        | MonoExpr::Let { .. }
        | MonoExpr::If { .. }
        | MonoExpr::Match { .. }
        | MonoExpr::Trace { .. }
        | MonoExpr::ParBind { .. }
        | MonoExpr::LaunchContinue { .. } => None,
    }
}

/// B3.4 activation flag (`design/backend/ownership-codegen.md` §4; FIXME 0523/
/// 0524/0525). **ACTIVATED (2026-07-05) — now the analysis-off oracle switch:**
/// `true` enables stack-slot allocation for NoEscape scalar-payload constructor
/// calls (gated by the escape precondition + gates 3 & 5); `false` restores the
/// conservative all-heap point (byte-identical to pre-B3.4), reachable as the
/// differential oracle.
///
/// Activation history — three blockers, all resolved:
/// FIXME 0523 (`d0c7684`) cured the closure/spark-CAPTURE escape gap; FIXME 0524
/// (`936404b`) cured the escape CLASS — the whole value-outflow edge space
/// (named-return / lambda-body-return / capture / HOF-flow / store-into-escaping /
/// spark-suspension / nested), 9-cell strategy matrix. After 0524 the classifier
/// is comprehensively sound. The THIRD blocker (FIXME 0525) was NOT a classifier
/// gap: under LENIENT (spark) eval the backend sparks a call's args onto separate
/// strands — a backend-internal transformation the strict-`MonoExpr` `escapes`
/// analysis cannot see — so a stack slot built for a lenient-sparked arg lives in
/// a thunk frame popped at the join, and a call with two or more stack-allocated
/// scalar-ADT args dangled (`runtime error: match failed` — hard UAF). The /arch
/// ruling (2026-07-05, direction (d)) resolved it with a backend-local **gate 5**
/// (`FnCompiler::in_spark_thunk`), mirroring gate 3's TCO-back-edge decline:
/// decline stack-alloc for any construction the backend relocates into a spark
/// thunk. Declining is always sound; under `NO_LENIENT` no thunk is synthesized so
/// the full stack-alloc win still lands. With gate 5 in place the flag flips to
/// `true` and the mechanism activates. `false` ⇒ byte-identical to pre-B3.4.
const STACK_ALLOC_ESCAPE_FACT_SOUND: bool = true;

/// N4 (S105, `design/backend/ownership-codegen.md` §13.2.2): the pure gate value
/// for the FINE stack oracle — the const default AND-ed with the *negation* of the
/// `CRANELISP_NO_STACK_ALLOC` env presence. Factored out of [`stack_alloc_enabled`]
/// so both polarities are unit-testable without touching the process-global env
/// (the `OnceLock` in the wrapper caches the first read, so an in-process env flip
/// is unreliable — the same reason `nonatomic_rc_codegen_enabled`'s arms are tested
/// through the pure emit path, not an env flip).
///
/// `no_stack_alloc_env == false` (env unset) ⇒ the const default (`true`) ⇒
/// **byte-identical** to pre-N4 codegen. `no_stack_alloc_env == true` ⇒ `false` ⇒
/// stack-alloc declines everywhere (the FINE oracle OFF), leaving borrow / RC /
/// reuse live.
const fn stack_alloc_gate_value(no_stack_alloc_env: bool) -> bool {
    STACK_ALLOC_ESCAPE_FACT_SOUND && !no_stack_alloc_env
}

/// N4 (S105, §13.2.2): codegen-time FINE stack-oracle gate. Reads
/// `CRANELISP_NO_STACK_ALLOC` **once** into a process-global `OnceLock` (so a whole
/// run is consistent), exactly the sibling of [`crate::heap::nonatomic_rc_codegen_enabled`]
/// (`heap.rs`). Codegen-time ⇒ no runtime cost regardless; env-unset ⇒ the const
/// default (byte-identical-off, §2.2). It sits ABOVE the `node_escapes` / gate-3 /
/// gate-5 chain in [`FnCompiler::constructor_call_stack_eligible`], so every
/// soundness sharpening is unaffected.
fn stack_alloc_enabled() -> bool {
    static E: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *E.get_or_init(|| stack_alloc_gate_value(std::env::var_os("CRANELISP_NO_STACK_ALLOC").is_some()))
}

/// B3.4 (`design/backend/ownership-codegen.md` §4.1): read the `escapes` site
/// fact off a [`MonoExpr`] node. Only the five allocation/capture-producing
/// variants carry the fact (same set as [`node_confined`]); every other variant
/// has no allocation of its own to place and answers `None` (⇒ the conservative
/// heap path). `Some(false)` (NoEscape) is the eligibility precondition for
/// stack-slot placement; `Some(true)` (escapes) / `None` (fact absent / analysis
/// off) ⇒ heap, verbatim today. Kept a total match so a new fact-bearing variant
/// is a compile error here.
pub(crate) fn node_escapes(node: &MonoExpr) -> Option<bool> {
    match node {
        MonoExpr::StringLit { escapes, .. }
        | MonoExpr::Lambda { escapes, .. }
        | MonoExpr::Apply { escapes, .. }
        | MonoExpr::VecLit { escapes, .. }
        | MonoExpr::ConstrADT { escapes, .. } => *escapes,
        MonoExpr::IntLit { .. }
        | MonoExpr::FloatLit { .. }
        | MonoExpr::BoolLit { .. }
        | MonoExpr::Var { .. }
        | MonoExpr::Let { .. }
        | MonoExpr::If { .. }
        | MonoExpr::Match { .. }
        | MonoExpr::Trace { .. }
        | MonoExpr::ParBind { .. }
        | MonoExpr::LaunchContinue { .. } => None,
    }
}

/// B3.4 gate 3 (`design/backend/ownership-codegen.md` §4.1): does `body` contain
/// a **self-recursive call** that the TCO lowering turns into a loop back-edge?
///
/// A stack slot is allocated **once per frame**; a TCO loop reuses the frame
/// across iterations via a jump to the loop header. If a stack-allocated value
/// flows into a `recur` argument it becomes loop-carried — live across the
/// back-edge — while the same slot site is re-reached and re-initialised on the
/// next iteration, clobbering the value the previous iteration handed forward
/// (a hard use-after-free the RC-balance guards cannot catch, per
/// `memory/feedback_verify_fix_not_symptom_absence`). The escape fact is
/// per-*frame*, not per-*iteration*, so it does not distinguish this case.
///
/// **First-landing gate (conservative, always sound to decline):** if the
/// function body contains ANY self-referential call — call- or value-position,
/// tail or not — decline stack allocation for the WHOLE function. This
/// over-approximates the set of TCO back-edges (a non-tail self-call is a real
/// call, not a back-edge, and is harmless — but declining is free correctness),
/// which eliminates any chance of a per-flow scanner error placing a
/// loop-carried value on the stack. Matches the two self-call shapes the TCO
/// lowering detects (`compile_apply`): a `Var` callee naming the function, or a
/// `SigDispatch` whose mangled name is the function. The sharper per-flow check
/// ("only decline when the value flows into a `recur` arg") is a noted follow-on.
pub(crate) fn body_has_self_call(body: &MonoExpr, fn_name: &Symbol) -> bool {
    use cranelisp_types::MonoExpr as E;
    fn is_self(callee: &E, resolved: Option<&ResolvedCall>, fn_name: &Symbol) -> bool {
        if let E::Var { name, .. } = callee
            && name == fn_name
        {
            return true;
        }
        matches!(
            resolved,
            Some(ResolvedCall::SigDispatch { mangled_name }) if mangled_name.as_ref() == fn_name.as_ref()
        )
    }
    fn walk(e: &E, fn_name: &Symbol) -> bool {
        match e {
            E::Apply { callee, args, resolved_call, .. } => {
                is_self(callee, resolved_call.as_deref(), fn_name)
                    || walk(callee, fn_name)
                    || args.iter().any(|a| walk(a, fn_name))
            }
            E::Let { bindings, body, .. } => {
                bindings.iter().any(|(_, v)| walk(v, fn_name)) || walk(body, fn_name)
            }
            E::If { cond, then_branch, else_branch, .. } => {
                walk(cond, fn_name) || walk(then_branch, fn_name) || walk(else_branch, fn_name)
            }
            E::Lambda { body, .. } => walk(body, fn_name),
            E::Match { scrutinee, arms, .. } => {
                walk(scrutinee, fn_name) || arms.iter().any(|a| walk(&a.body, fn_name))
            }
            E::VecLit { elements, .. } => elements.iter().any(|el| walk(el, fn_name)),
            E::Trace { body, .. } => walk(body, fn_name),
            E::ParBind { bindings, body, .. } => {
                bindings.iter().any(|(_, v)| walk(v, fn_name)) || walk(body, fn_name)
            }
            E::LaunchContinue { launched, continuation, .. } => {
                walk(launched, fn_name) || walk(continuation, fn_name)
            }
            E::ConstrADT { fields, .. } => fields.iter().any(|f| walk(f, fn_name)),
            E::IntLit { .. }
            | E::FloatLit { .. }
            | E::BoolLit { .. }
            | E::StringLit { .. }
            | E::Var { .. } => false,
        }
    }
    walk(body, fn_name)
}

#[cfg(test)]
mod b34_stack_eligibility_tests {
    //! B3.4 stack-slot eligibility gate predicates (Principle 23 —
    //! `design/backend/ownership-codegen.md` §13.5 stack-slots row): the pure,
    //! backend-local halves of `constructor_call_stack_eligible` —
    //! `node_escapes` (the NoEscape precondition, total over the variant set),
    //! `body_has_self_call` (gate 3, the TCO-back-edge decline), and the composed
    //! method itself (gate 5, the FIXME-0525 spark-relocation decline). B3.4 is
    //! ACTIVATED (2026-07-05); these pin every gate.
    use super::{
        body_has_self_call, node_escapes, stack_alloc_enabled, stack_alloc_gate_value,
        STACK_ALLOC_ESCAPE_FACT_SOUND,
    };
    use cranelisp_types::{
        ConcreteType, FQTypeName, JitSymbol, ModuleFullPath, MonoExpr, ResolvedCall, Span, Symbol,
        TypeName,
    };

    fn int() -> ConcreteType {
        ConcreteType::Int
    }
    fn var(name: &str) -> MonoExpr {
        MonoExpr::Var { name: Symbol::from(name), span: Span::new(0, 1), resolved_call: None, ty: int(), resolved_target: None }
    }
    fn constr(escapes: Option<bool>) -> MonoExpr {
        MonoExpr::ConstrADT {
            type_name: FQTypeName::new(ModuleFullPath::from("m"), TypeName::from("T")),
            tag: 0, fields: vec![], span: Span::new(0, 1), ty: int(),
            escapes, confined: None, unique_static: None,
        }
    }
    /// An `(f args…)` apply with the given callee name, escape fact, and resolved call.
    fn apply(callee: &str, args: Vec<MonoExpr>, escapes: Option<bool>, resolved: Option<ResolvedCall>) -> MonoExpr {
        MonoExpr::Apply {
            resolved_target: None,
            callee: Box::new(var(callee)), args, span: Span::new(0, 3),
            resolved_call: resolved.map(Box::new), ty: int(),
            escapes, confined: None, unique_static: None, provenance: None,
        }
    }

    // --- node_escapes: total match, fact-bearing vs non-bearing variants ------
    #[test]
    fn escapes_reads_the_five_fact_bearing_variants() {
        // spec: design/backend/ownership-codegen.md §4.1 — escapes on ConstrADT/Apply/…
        assert_eq!(node_escapes(&constr(Some(false))), Some(false));
        assert_eq!(node_escapes(&constr(Some(true))), Some(true));
        assert_eq!(node_escapes(&constr(None)), None);
        assert_eq!(node_escapes(&apply("f", vec![], Some(false), None)), Some(false));
        assert_eq!(
            node_escapes(&MonoExpr::VecLit { elements: vec![], span: Span::new(0, 1), ty: int(), escapes: Some(false), confined: None, unique_static: None }),
            Some(false)
        );
        assert_eq!(
            node_escapes(&MonoExpr::Lambda { params: vec![], body: Box::new(var("x")), span: Span::new(0, 1), ty: ConcreteType::Fn(vec![], Box::new(int())), escapes: Some(true), confined: None, unique_static: None }),
            Some(true)
        );
    }
    #[test]
    fn escapes_is_none_for_non_allocating_variants() {
        // spec: design/backend/ownership-codegen.md §4.1 — non-fact-bearing ⇒ None ⇒ heap
        assert_eq!(node_escapes(&var("v")), None);
        assert_eq!(node_escapes(&MonoExpr::IntLit { value: 0, span: Span::new(0, 1), ty: int() }), None);
    }

    // --- body_has_self_call (gate 3): the TCO-back-edge whole-function decline --
    #[test]
    fn detects_direct_self_call() {
        // spec: design/backend/ownership-codegen.md §4.1 gate 3 — self-call present
        let f = Symbol::from("f");
        assert!(body_has_self_call(&apply("f", vec![], None, None), &f));
    }
    #[test]
    fn detects_self_call_nested_in_let_if_match_and_arg() {
        let f = Symbol::from("f");
        let call = || apply("f", vec![], None, None);
        // in a let body
        assert!(body_has_self_call(
            &MonoExpr::Let { bindings: vec![], body: Box::new(call()), span: Span::new(0, 4), ty: int() }, &f));
        // in an if branch
        assert!(body_has_self_call(
            &MonoExpr::If { cond: Box::new(var("c")), then_branch: Box::new(var("a")), else_branch: Box::new(call()), span: Span::new(0, 5), ty: int() }, &f));
        // in an ARGUMENT position (non-tail self-call — still declined, conservative)
        assert!(body_has_self_call(&apply("g", vec![call()], None, None), &f));
    }
    #[test]
    fn detects_sig_dispatch_mangled_self_call() {
        // spec: design/backend/ownership-codegen.md §4.1 gate 3 — mono self-call by mangled name
        let f = Symbol::from("f$Int");
        let e = apply("f", vec![], None, Some(ResolvedCall::SigDispatch { mangled_name: JitSymbol::from("f$Int") }));
        assert!(body_has_self_call(&e, &f));
    }
    #[test]
    fn no_self_call_for_foreign_callee() {
        // spec: design/backend/ownership-codegen.md §4.1 gate 3 — a different name is not self
        let f = Symbol::from("f");
        assert!(!body_has_self_call(&apply("g", vec![var("x")], None, None), &f));
        assert!(!body_has_self_call(&var("x"), &f));
    }

    // --- the composed method is ACTIVATED (2026-07-05, FIXME 0525 ruling) -------
    // spec: design/backend/ownership-codegen.md §4 — B3.4 activated. The escape
    // classifier is comprehensively sound (FIXME 0523 + 0524); the third blocker
    // (FIXME 0525 — lenient spark-relocation UAF) is cured by gate 5
    // (`in_spark_thunk`), a backend-local emission decline mirroring gate 3.
    // Compile-time guard so an accidental revert of the activation cannot land
    // without this test file being revisited (byte-identical-off stays reachable
    // under the const=false / `CRANELISP_NO_OWNERSHIP` oracle path).
    const _: () = assert!(STACK_ALLOC_ESCAPE_FACT_SOUND);

    // --- N4 (S105 §13.2.2): the FINE stack-oracle env gate ----------------------

    // spec: design/backend/ownership-codegen.md §13.2.2 N4 — the pure gate value:
    // env-unset ⇒ the const default (byte-identical-off); env-set ⇒ stack-alloc
    // OFF (the fine oracle, borrow/RC/reuse untouched). Both polarities pinned
    // without touching the process-global env (the OnceLock caches its first read).
    #[test]
    fn n4_stack_alloc_gate_value_both_polarities() {
        // env unset ⇒ const default ⇒ byte-identical-off. Since the const is
        // ACTIVATED (`true`), the unset gate must be `true` (stack path fires).
        assert_eq!(
            stack_alloc_gate_value(false),
            STACK_ALLOC_ESCAPE_FACT_SOUND,
            "env unset must yield the const default (byte-identical-off, §2.2)"
        );
        assert!(stack_alloc_gate_value(false), "with the const activated, env-unset fires the stack path");
        // env set (CRANELISP_NO_STACK_ALLOC=1) ⇒ the FINE oracle OFF ⇒ decline.
        assert!(
            !stack_alloc_gate_value(true),
            "CRANELISP_NO_STACK_ALLOC set must decline stack-alloc (the fine oracle OFF)"
        );
    }

    // spec: design/backend/ownership-codegen.md §13.2.2 N4 — in THIS test process
    // (env unset) the production OnceLock gate equals the const default, i.e. the
    // gate introduces no divergence when the toggle is absent (byte-identical-off).
    #[test]
    fn n4_stack_alloc_enabled_defaults_to_const_when_env_unset() {
        assert_eq!(
            stack_alloc_enabled(),
            STACK_ALLOC_ESCAPE_FACT_SOUND,
            "with CRANELISP_NO_STACK_ALLOC unset the gate must equal the const default"
        );
    }

    // spec: design/backend/ownership-codegen.md §13.2.2 N4 — the gate is the FIRST
    // short-circuit in `constructor_call_stack_eligible`: when the gate value is
    // false, an otherwise-eligible NoEscape scalar constructor is declined (the
    // stack path flips OFF), independent of the escape/gate-3/gate-5 chain. Driven
    // through the pure gate value so no env flip / OnceLock poisoning is needed.
    #[test]
    fn n4_gate_false_declines_an_otherwise_eligible_construction() {
        // An otherwise-fully-eligible node (NoEscape, scalar payload, no self-call,
        // not spark-relocated) — the exact shape the `gate5` test proves eligible.
        let app = apply("Some", vec![var("x")], Some(false), None);
        let args = match &app {
            MonoExpr::Apply { args, .. } => args.clone(),
            _ => unreachable!(),
        };
        // node_escapes precondition holds (Some(false)); the ONLY thing that turns
        // eligibility off for this shape is the N4 gate. Model the composed method's
        // gate-first decision: gate=false ⇒ declined regardless of the rest.
        let escape_ok = node_escapes(&app) == Some(false);
        assert!(escape_ok && !args.is_empty(), "fixture is otherwise eligible");
        let eligible_when_gate_off =
            stack_alloc_gate_value(true) && escape_ok; // gate is the leading conjunct
        assert!(
            !eligible_when_gate_off,
            "with the N4 gate OFF, even a fully-eligible NoEscape scalar constructor is declined"
        );
        // And with the gate ON the leading conjunct does not itself block the win.
        assert!(stack_alloc_gate_value(false), "gate ON must not block the eligible shape");
    }

    // --- gate 5 (FIXME 0525): a spark-relocated construction stays HEAP ---------
    #[test]
    fn gate5_declines_stack_alloc_for_a_spark_relocated_construction() {
        // spec: design/backend/ownership-codegen.md §4.3 gate 5 (FIXME 0525) — a
        // NoEscape scalar-payload constructor the backend relocates into a spark
        // thunk (`in_spark_thunk`) is declined stack placement (would dangle at the
        // join — hard UAF). The same node NOT inside a spark thunk is eligible (the
        // win survives). Exercises the composed method, not just the sub-predicates.
        use cranelift::codegen::ir::{Function, UserFuncName};
        use cranelift::prelude::*;
        use cranelift_module::Module;
        use std::collections::HashMap as Map;

        let tables: dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable> =
            dashmap::DashMap::new();
        let module_path = ModuleFullPath::from("user");
        let mut jit = crate::jit::Jit::new_with_symbols(&[]).unwrap();
        let intrinsic_ids = crate::jit::declare_intrinsics_generic(jit.jit_module()).unwrap();
        let aliases = cranelisp_types::ModuleAliases::default();
        let func_ids: Map<Symbol, cranelift_module::FuncId> = Map::new();
        let func_arities: Map<Symbol, usize> = Map::new();
        let ctx = crate::compiler::CompileContext {
            func_ids: &func_ids,
            func_arities: &func_arities,
            symbol_tables: &tables,
            module_aliases: &aliases,
            current_module: module_path,
            alloc_func_id: intrinsic_ids.alloc,
            dealloc_func_id: intrinsic_ids.dealloc.unwrap(),
            alloc_string_func_id: intrinsic_ids.alloc_string,
            panic_func_id: intrinsic_ids.panic,
            vec_new_func_id: intrinsic_ids.vec_new,
            vec_drop_func_id: intrinsic_ids.vec_drop,
        };
        let mut sig = jit.jit_module().make_signature();
        sig.returns.push(AbiParam::new(types::I64));
        let mut func = Function::with_name_signature(UserFuncName::user(0, 0), sig);
        let mut fctx = FunctionBuilderContext::new();
        let builder = FunctionBuilder::new(&mut func, &mut fctx);
        let mut compiler =
            crate::compiler::FnCompiler::inner(builder, jit.jit_module(), ctx, 0, Map::new());

        // An otherwise-eligible NoEscape scalar-payload constructor call.
        let app = apply("Some", vec![var("x")], Some(false), None);
        let args = match &app {
            MonoExpr::Apply { args, .. } => args.clone(),
            _ => unreachable!(),
        };

        // The win: not relocated, no TCO self-call ⇒ eligible (stack-allocates).
        compiler.fn_has_self_call = false;
        compiler.in_spark_thunk = false;
        assert!(
            compiler.constructor_call_stack_eligible(&app, &args),
            "a genuinely-local NoEscape scalar constructor must stay stack-eligible"
        );

        // Gate 5: relocated into a spark thunk ⇒ declined (heap) — the 0525 cure.
        compiler.in_spark_thunk = true;
        assert!(
            !compiler.constructor_call_stack_eligible(&app, &args),
            "a spark-relocated construction must decline stack placement (0525)"
        );
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
/// `Fresh`). A `ProjectionOf`/`AliasOf` result KEEPS the protect: the callee
/// materializes the returned projection with an owned reference (its `vec-get`
/// inc, an accessor call, or `protect_return_value` under cleanup targets), so a
/// direct caller consumes it as an ordinary owned temporary — the §3.3 in-frame
/// elision is confined to the CONSUMER seam (`compile_consuming_arg_list_moded`),
/// never propagated across a function-return boundary (that propagation is
/// parallel-unsound — an escaping borrowed view races a concurrent COW/free,
/// observed in f4_sudoku). `_body` is retained for the seam signature but no
/// longer read.
pub(crate) fn return_is_fresh_by_summary(
    _body: &MonoExpr,
    summary: Option<&cranelisp_types::ModeSummary>,
) -> bool {
    summary.is_some_and(|s| s.result == cranelisp_types::ResultMode::Fresh)
}

/// The heap scope binding a TAIL COW op moves into the function's return value,
/// or `None` — the [`FnCompiler::return_cow_source`] determinant (vec-assoc UAF
/// fix, `tests/vec_assoc_param_mutate_return_uaf.rs`).
///
/// Matches ONLY the direct shape: the whole body is `(vec-set v …)` /
/// `(vec-push v …)` whose FIRST argument is a bare `Var` naming a member of the
/// current scope frame. Restricting to the direct body guarantees `v` is used
/// exactly once (as the COW source), so it is genuinely at last use (the in-place
/// COW arm fires) and suppressing its scope-exit dec cannot strand a live
/// reference. A more complex body (`v` used elsewhere, a COW inside an `if`/`let`,
/// the element argument aliasing `v`) does NOT match — conservative,
/// byte-identical to pre-fix. Reads the `Apply` callee `Var` name directly: the
/// vec-query primitive names are canonical and never aliased at a value site.
/// Free function (not an associated fn) so the ownership DECISION is unit-testable
/// without constructing a generic `FnCompiler` — the `return_is_fresh_by_summary`
/// precedent.
pub(crate) fn return_cow_source_in_scope(
    body: &MonoExpr,
    scope_frame: Option<&Vec<Symbol>>,
) -> Option<Symbol> {
    let MonoExpr::Apply { callee, args, .. } = body else {
        return None;
    };
    let MonoExpr::Var { name: callee_name, .. } = callee.as_ref() else {
        return None;
    };
    if !matches!(callee_name.as_ref(), "vec-set" | "vec-push") {
        return None;
    }
    let Some(MonoExpr::Var { name: src, .. }) = args.first() else {
        return None;
    };
    let frame = scope_frame?;
    if frame.contains(src) {
        Some(src.clone())
    } else {
        None
    }
}

#[cfg(test)]
mod return_cow_source_tests {
    //! vec-assoc UAF fix (`tests/vec_assoc_param_mutate_return_uaf.rs`): the
    //! last-use/ownership DECISION seam — which scope binding a tail COW op
    //! (`vec-set`/`vec-push`) moves into the function return, so its scope-exit
    //! dec is suppressed and the COW copy branch flips to `Owned`. VA-3 unit pin.
    use super::return_cow_source_in_scope;
    use cranelisp_types::{ConcreteType, MonoExpr, Span, Symbol};

    fn int_ty() -> ConcreteType {
        ConcreteType::Int
    }

    fn var(name: &str) -> MonoExpr {
        MonoExpr::Var {
            name: Symbol::from(name),
            span: Span::new(0, 1),
            resolved_call: None,
            resolved_target: None,
            ty: int_ty(),
        }
    }

    fn cow_call(prim: &str, src: MonoExpr) -> MonoExpr {
        MonoExpr::Apply {
            resolved_target: None,
            callee: Box::new(var(prim)),
            args: vec![src, var("i"), var("x")],
            span: Span::new(0, 9),
            resolved_call: None,
            ty: ConcreteType::ADT(
                cranelisp_types::FQTypeName::new(
                    cranelisp_types::ModuleFullPath::from("primitives"),
                    cranelisp_types::TypeName::from("Vec"),
                ),
                vec![int_ty()],
            ),
            escapes: None,
            confined: None,
            unique_static: None,
            provenance: None,
        }
    }

    fn frame(names: &[&str]) -> Vec<Symbol> {
        names.iter().map(|n| Symbol::from(*n)).collect()
    }

    // (i) `(vec-set v i x)` returning a scope-bound param `v` ⇒ suppress v's
    // scope-exit dec (the in-place COW returns v's backing).
    #[test]
    fn vec_set_on_returned_scope_param_is_the_cow_source() {
        let f = frame(&["v", "i", "x"]);
        assert_eq!(
            return_cow_source_in_scope(&cow_call("vec-set", var("v")), Some(&f)),
            Some(Symbol::from("v"))
        );
    }

    // (ii) `vec-push` sibling — same suppression.
    #[test]
    fn vec_push_on_returned_scope_param_is_the_cow_source() {
        let f = frame(&["v", "i", "x"]);
        assert_eq!(
            return_cow_source_in_scope(&cow_call("vec-push", var("v")), Some(&f)),
            Some(Symbol::from("v"))
        );
    }

    // (iii) control: the identity-fn return (bare `Var`, not a COW) is NOT a COW
    // source — it is handled by `return_var_in_scope` instead, and MUST NOT be
    // flagged here (no over-correction: the copy branch stays `Borrowed`).
    #[test]
    fn identity_bare_var_return_is_not_a_cow_source() {
        let f = frame(&["v"]);
        assert_eq!(return_cow_source_in_scope(&var("v"), Some(&f)), None);
    }

    // Control: a COW on a NON-frame source (a temporary / fresh literal wrapped
    // as a Var not in scope) is NOT flagged — only a scope-managed binding whose
    // scope-exit dec would otherwise fire needs suppression.
    #[test]
    fn cow_on_non_frame_source_is_not_flagged() {
        let f = frame(&["i", "x"]); // `v` deliberately absent from the frame
        assert_eq!(return_cow_source_in_scope(&cow_call("vec-set", var("v")), Some(&f)), None);
    }

    // Control: a non-COW callee (`vec-get`) is not a mutating op — no source move.
    #[test]
    fn non_cow_primitive_is_not_flagged() {
        let f = frame(&["v", "i"]);
        assert_eq!(
            return_cow_source_in_scope(&cow_call("vec-get", var("v")), Some(&f)),
            None
        );
    }
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
            resolved_target: None,
            callee: Box::new(MonoExpr::Var {
                resolved_target: None,
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
            then_branch: Box::new(MonoExpr::Var { name: Symbol::from("v"), span: Span::new(1, 2), resolved_call: None, resolved_target: None, ty: int_ty() }),
            else_branch: Box::new(MonoExpr::Var { name: Symbol::from("w"), span: Span::new(2, 3), resolved_call: None, resolved_target: None, ty: int_ty() }),
            span: Span::new(0, 4),
            ty: int_ty(),
        }
    }

    fn var_body() -> MonoExpr {
        MonoExpr::Var { name: Symbol::from("v"), span: Span::new(0, 1), resolved_call: None, ty: int_ty(), resolved_target: None }
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

    // NEGATIVE (aliasing result modes): AliasOf / ProjectionOf keep protect — the
    // callee materializes the returned projection with an owned reference (§3.3
    // confines the in-frame elision to the consumer seam, never a function
    // return), so a direct caller consumes it as an owned temporary.
    #[test]
    fn aliasing_result_modes_never_elide() {
        assert!(!return_is_fresh_by_summary(&apply_body(), Some(&alias0())));
        assert!(!return_is_fresh_by_summary(&apply_body(), Some(&proj0())));
    }
}

#[cfg(test)]
mod b33_node_confined_tests {
    //! B3.3 confined-fact classifier (`design/backend/ownership-codegen.md`
    //! §5.1; §13.5): `node_confined` reads the `confined` site fact off the five
    //! allocation/capture-producing variants and answers `None` for every other
    //! variant. The atomicity derivation is `Some(true) ⇒ NonAtomic`, else
    //! `Atomic` — the classifier is the pure seam under it.
    use super::node_confined;
    use crate::heap::RcAtomicity;
    use cranelisp_types::{ConcreteType, FQTypeName, ModuleFullPath, MonoExpr, Span, TypeName};

    fn int() -> ConcreteType { ConcreteType::Int }

    // The five fact-bearing variants, each parameterised over its `confined`.
    fn string_lit(c: Option<bool>) -> MonoExpr {
        MonoExpr::StringLit { value: "x".into(), span: Span::new(0, 1), ty: ConcreteType::String, escapes: None, confined: c, unique_static: None }
    }
    fn lambda(c: Option<bool>) -> MonoExpr {
        MonoExpr::Lambda { params: vec![], body: Box::new(MonoExpr::IntLit { value: 0, span: Span::new(0, 1), ty: int() }), span: Span::new(0, 1), ty: ConcreteType::Fn(vec![], Box::new(int())), escapes: None, confined: c, unique_static: None }
    }
    fn apply(c: Option<bool>) -> MonoExpr {
        MonoExpr::Apply { callee: Box::new(MonoExpr::Var { name: "f".into(), span: Span::new(0, 1), resolved_call: None, resolved_target: None, ty: int() }), args: vec![], span: Span::new(0, 2), resolved_call: None, ty: int(), escapes: None, confined: c, unique_static: None, provenance: None, resolved_target: None }
    }
    fn vec_lit(c: Option<bool>) -> MonoExpr {
        // node_confined reads only `confined`; the ty is immaterial here.
        MonoExpr::VecLit { elements: vec![], span: Span::new(0, 1), ty: int(), escapes: None, confined: c, unique_static: None }
    }
    fn constr_adt(c: Option<bool>) -> MonoExpr {
        MonoExpr::ConstrADT { type_name: FQTypeName::new(ModuleFullPath::from("m"), TypeName::from("T")), tag: 0, fields: vec![], span: Span::new(0, 1), ty: int(), escapes: None, confined: c, unique_static: None }
    }

    // POSITIVE: each fact-bearing variant reports its own confined field.
    #[test]
    fn fact_bearing_variants_report_confined() {
        for mk in [string_lit as fn(Option<bool>) -> MonoExpr, lambda, apply, vec_lit, constr_adt] {
            assert_eq!(node_confined(&mk(Some(true))), Some(true));
            assert_eq!(node_confined(&mk(Some(false))), Some(false));
            assert_eq!(node_confined(&mk(None)), None);
        }
    }

    // NEGATIVE: non-allocation variants have no cell of their own ⇒ None
    // (⇒ conservative Atomic). Var / Let / If / Match are the through-carriers,
    // never the fact source.
    #[test]
    fn non_fact_bearing_variants_are_none() {
        let var = MonoExpr::Var { name: "v".into(), span: Span::new(0, 1), resolved_call: None, resolved_target: None, ty: int() };
        let iflit = MonoExpr::If { cond: Box::new(MonoExpr::BoolLit { value: true, span: Span::new(0, 1), ty: ConcreteType::Bool }), then_branch: Box::new(var.clone()), else_branch: Box::new(var.clone()), span: Span::new(0, 2), ty: int() };
        let intlit = MonoExpr::IntLit { value: 0, span: Span::new(0, 1), ty: int() };
        assert_eq!(node_confined(&var), None);
        assert_eq!(node_confined(&iflit), None);
        assert_eq!(node_confined(&intlit), None);
    }

    // The atomicity derivation: Some(true) ⇒ NonAtomic; Some(false)/None ⇒ Atomic.
    // (mirrors `FnCompiler::rc_atomicity_for_node`; the classifier is the seam).
    #[test]
    fn atomicity_derivation_from_confined_fact() {
        let map = |c: Option<bool>| match c { Some(true) => RcAtomicity::NonAtomic, _ => RcAtomicity::Atomic };
        assert_eq!(map(node_confined(&constr_adt(Some(true)))), RcAtomicity::NonAtomic);
        assert_eq!(map(node_confined(&constr_adt(Some(false)))), RcAtomicity::Atomic);
        assert_eq!(map(node_confined(&constr_adt(None))), RcAtomicity::Atomic);
    }
}
