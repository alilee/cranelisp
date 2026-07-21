//! The per-function CLIF emitter: the `FnCompiler` struct, its construction
//! (`inner`, `compile_body`, `bind_defn_params`), the expression-dispatch entry
//! (`compile_expr`), scope lifecycle, and the small per-fn predicates.
//! `MatchContext` is per-arm `FnCompiler` state, kept adjacent to the struct it
//! threads through.

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use cranelisp_types::{
    ApplyRef, CranelispError, Defn, ModuleFullPath, MonoExpr, ModuleEntry, ResolvedCall, Span,
    Symbol, Type, VarRef,
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
    /// Variables that borrow from a parent (e.g., pattern match field bindings,
    /// R1 alias-`let` bindings, `Borrowed` params). Borrowed vars skip both inc
    /// (at extraction) and dec (at scope exit) — the owner (scrutinee / aliased
    /// root / caller) handles cleanup via its own RC management.
    ///
    /// SCOPE-STRATIFIED, parallel to `scope_stack` (FIXME 0692): the borrowed
    /// mark is a property of a *binder*, not a *name* (Principle 20). The set at
    /// index `i` holds the borrowed names of `scope_stack[i]`, so a later
    /// shadow/sibling binding of the same name to an OWNED value is NOT wrongly
    /// treated as borrowed. `is_borrowed` resolves a name against its INNERMOST
    /// binding. The prior fn-lifetime, name-keyed set leaked a second owned
    /// binding whenever a name was reused (a regression the R1 widening exposed).
    borrowed_stack: Vec<std::collections::HashSet<Symbol>>,
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
    /// is **present** with `result == ResultMode::Fresh`. `Fresh` is sound to
    /// elide on iff the summary chain's **leaf facts are truthful AND
    /// reachable** — three classes had to close: 0520 cured the join-collapse
    /// (a partial param-return reports not-`Fresh`), and S111 §3.7 cured the
    /// false-declaration (`vec-set`/`vec-push` now `MayAliasOf(0)`, not `Fresh`)
    /// and the unreachable-declaration (the ownership envs resolve leaf facts
    /// prelude-fallback-aware) classes. `MayAliasOf`/`AliasOf`/`ProjectionOf`
    /// all read not-`Fresh` ⇒ protect KEPT (Principle 18: the safe direction for
    /// any non-`Fresh` variant). Gated on PRESENCE — absent ⇒ Decision-24
    /// (protect), so `CRANELISP_NO_OWNERSHIP` (which suppresses all summaries) is
    /// byte-identical to pre-B3.2.
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
    /// The recorded escape fact (`node_escapes`) of the COW `Apply` currently
    /// being lowered — stashed by `compile_builtin_fn_call` immediately before
    /// `compile_vec_op` (after the args are compiled, so a nested-arg apply cannot
    /// clobber it), read by `cow_source_ownership` for the §13.7 escape gate
    /// (FIXME 0664 /arch ruling). `None` ⇒ absent fact ⇒ the UAF-safe inc default
    /// (P25). Analysis-OFF ignores it (toggle-off is all-Owned, R14).
    pub(crate) pending_cow_escapes: Option<bool>,

    /// FIXME 0693 — the producer's OWN retain decision per COW site, keyed by
    /// the COW `Apply`'s span, written by
    /// `vec_codegen.rs::cow_source_ownership` at the moment it classifies the
    /// source, and read by the R3 match-consume seam
    /// ([`FnCompiler::scrutinee_cow_retains_reused`]). This makes the dec side a
    /// DERIVATION of the producer's decision rather than a re-derivation from
    /// the callee spelling (Principle 7 single source of truth / Principle 24
    /// resolve once).
    ///
    /// `Some(v)` = one consistent verdict recorded at that span; `None` =
    /// AMBIGUOUS (two distinct COW sites collapsed onto one span — reachable
    /// only for `Span::SYNTHETIC` bodies), read as the leak-safe verdict
    /// (suppress the dec; never a spurious dec, i.e. never the UAF direction).
    /// Absent key = the producer never ran in THIS compiler frame.
    pub(crate) cow_retain_decisions: HashMap<Span, Option<bool>>,

    /// FIXME 0720 (S115 W3 change-set 2) — the `Borrowed` heap params this frame
    /// has PROMOTED to frame-owned for the duration of a TCO loop, because a tail
    /// self-call SUPERSEDES their slot with a value the caller does not own.
    ///
    /// A `Borrowed` param means "the caller owns this reference; do not dec it".
    /// That contract holds for the value the caller actually passed — but a TCO
    /// back-edge OVERWRITES the slot with the tail argument, and for a
    /// non-transferring argument (a temporary such as `(set0 g m)`) that value is
    /// owned by THIS frame, not by any caller. With the slot skipped as "borrowed"
    /// on every iteration, nothing ever released it: the ADT-wrapped supersede
    /// loop leaked its box AND its fields, 2 objects per iteration.
    ///
    /// The cure keeps the borrow contract intact and makes the frame's ownership
    /// uniform instead: [`FnCompiler::compile_body`] emits ONE `rc_inc` on the
    /// caller's incoming value in the ENTRY block (so the caller's reference is
    /// never the one released), and the param is then treated as frame-owned by
    /// exactly two consumers — the tail-jump param flush and the function-exit
    /// scope cleanup. Invariant: **the frame owns exactly one reference to
    /// whatever occupies the slot** — established at entry by the inc, preserved
    /// at each back-edge (flush decs the old value; the fresh argument arrives
    /// frame-owned), discharged at exit by the scope cleanup.
    ///
    /// `is_borrowed` itself is NOT cleared: last-use ownership transfer and
    /// in-place COW mutation must stay refused for these params (they may still
    /// alias the caller's value on the first iteration).
    pub(crate) tco_owned_params: std::collections::HashSet<Symbol>,
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
            borrowed_stack: vec![std::collections::HashSet::new()],
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
            pending_cow_escapes: None,
            cow_retain_decisions: HashMap::new(),
            tco_owned_params: std::collections::HashSet::new(),
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
    /// One condition, sound iff the summary's leaf facts are truthful+reachable:
    ///
    /// - **A summary is PRESENT with `result == Fresh`.** Absent ⇒ Decision-24
    ///   (protect verbatim), so a `CRANELISP_NO_OWNERSHIP` build (no summaries)
    ///   is byte-identical to pre-B3.2.
    ///
    /// The Apply-body restriction the partial slice (`d7b6a0f`) carried is
    /// **dropped** here, sound now that THREE `Fresh`-falsity classes are closed:
    /// (1) FIXME 0520 cured the typecheck-side result-mode join-collapse
    /// (`join_origin` no longer widens a partial control-flow param-return toward
    /// the dangerous `Fresh` — a `(if (eq i n) v (build …))` base-case-returns-`v`
    /// body now reports not-`Fresh`); (2) S111 §3.7 cured the FALSE-declaration
    /// class (`vec-set`/`vec-push` declare `MayAliasOf(0)`, not `Fresh`); (3)
    /// S111 §3.7(a3) cured the UNREACHABLE-declaration class (the ownership envs
    /// now resolve leaf facts through the prelude fallback, so a user module's
    /// `(vec-set …)` actually sees the COW facts instead of defaulting to
    /// `Fresh`). With all three closed, `result == Fresh` means no reachable
    /// return path carries a param through a truthful+reachable summary chain, so
    /// the returned value is genuinely fresh and scope cleanup can never free it
    /// — NOT an unconditional property of the enum value alone. A
    /// `MayAliasOf`/`AliasOf`/`ProjectionOf` result KEEPS the protect. Verified:
    /// `04_vec_cow_loop`'s `build` keeps its protect and runs correct.
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

        // FIXME 0720 (S115 W3 change-set 2) — promote `Borrowed` heap params that a
        // tail self-call SUPERSEDES to frame-owned, with ONE `rc_inc` here in the
        // entry block (the caller's incoming value, executed exactly once — NOT
        // per iteration, which the loop header would give). See the
        // `tco_owned_params` field rustdoc for the invariant this establishes.
        let promoted =
            tco_promoted_borrowed_params(defn, body, mode_summary.as_ref(), &ctx);
        let entry_params: Vec<Value> = builder.block_params(entry_block).to_vec();
        for (i, _, category) in &promoted {
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_inc(&mut builder, module, entry_params[*i]);
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_inc_guarded(&mut builder, module, entry_params[*i]);
                }
                HeapCategory::NeverHeap | HeapCategory::Value => {}
            }
        }

        // Jump from entry to loop header with initial parameter values.
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
        let fn_has_self_call = body_has_self_call(body, &defn.name, &ctx.current_module);

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
            borrowed_stack: vec![std::collections::HashSet::new()],
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
            pending_cow_escapes: None,
            cow_retain_decisions: HashMap::new(),
            tco_owned_params: std::collections::HashSet::new(),
        };

        // Seed the function's parameters into scope + variable_types.
        compiler.bind_defn_params(defn, body, loop_header);
        compiler.tco_owned_params =
            promoted.into_iter().map(|(_, name, _)| name).collect();

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
                .is_none_or(|rv| !compiler.is_borrowed(rv)),
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
        let defn_param_types: Vec<Option<Type>> = defn_param_types(&self.ctx, defn);

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
                resolution,
                ty,
                ..
            } => {
                // The signature-path bridge: `compile_var` reads the variable's
                // type as a `&Type` (for the value-position trait-method arity).
                // The node's `ConcreteType` embeds losslessly into a `Type`.
                //
                // S114 carrier flip (`typed-resolution-carrier.md` §4; the S110 W2
                // `backend-keyed-consumer.md` §4 S10–S18 seams): the Var's typed
                // `resolution` verdict — `VarRef::Global(storage_fq)` (a table
                // reference, drives the value-seam keyed reads) or `VarRef::Local`
                // (a scope-stack reference; the backend `variables` check precedes
                // any keyed read — KC-N6; a scope-stack miss is a hard invariant
                // failure carrying the binder identity, §2.7.2). `compile_var`
                // matches the closed sum exhaustively.
                let inferred = ty.to_type();
                self.compile_var(
                    name,
                    *span,
                    resolved_call.as_deref(),
                    Some(&inferred),
                    resolution,
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
                dispatch,
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
                // §13.7 (FIXME 0664): this Apply's recorded escape fact, threaded
                // to the COW seam (`cow_source_ownership`'s escape gate).
                let apply_escapes = node_escapes(expr);
                // S114 carrier flip (`typed-resolution-carrier.md` §4): the Apply's
                // typed dispatch verdict → the `Option<&FQSymbol>` the keyed fetch
                // consumes. Exhaustive on the closed `ApplyRef` sum (no `_` arm):
                // `Dispatch(fq)` carries the STORAGE FQ typecheck's dispatch
                // selection resolved to (trait/sig-dispatch/auto-curry/operator
                // legs); `ViaCallee` is the POSITIVE no-Apply-level-dispatch verdict
                // (the identity rides the callee `Var` node) → `None`.
                let apply_target = match dispatch {
                    ApplyRef::Dispatch(fq) => Some(fq),
                    ApplyRef::ViaCallee => None,
                };
                self.compile_apply(
                    callee,
                    args,
                    *span,
                    resolved_call.as_deref(),
                    apply_target,
                    Some(&apply_type),
                    stack,
                    apply_escapes,
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
        // Keep `borrowed_stack` frame-synced with `scope_stack` (FIXME 0692):
        // the new frame's borrowed marks live at the matching index.
        self.borrowed_stack.push(std::collections::HashSet::new());
    }

    pub(crate) fn pop_scope(&mut self) {
        // Pop the parallel borrowed frame with the scope frame so a re-bound name
        // in an enclosing frame recovers its own borrowed status (FIXME 0692).
        self.borrowed_stack.pop();
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
                // Skip borrowed variables (owner handles cleanup) — EXCEPT a
                // TCO-promoted param, whose frame-owned reference (the entry inc)
                // this exit dec discharges (FIXME 0720).
                this.is_borrowed(name) && !this.tco_owned_params.contains(name)
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
                this.is_borrowed(name)
            });
            to_dec.append(&mut frame_decs);
        }
        self.emit_heap_binding_decs(&to_dec);
    }

    /// MS-P8 (FIXME 0688 verdict a; `s114-test-plan.md` §2.1) — the PARAM sibling
    /// of [`FnCompiler::flush_let_scopes_before_tail_jump`]. On a tail self-call
    /// the loop header OVERWRITES each param slot (scope frame `[0]`) with the new
    /// argument value; a heap-typed param whose slot is superseded by a FRESH,
    /// independently-owned value leaks its slot reference — the `conj`/`assoc`
    /// persistent-op loop's 1-Vec-per-iteration leak (each `conj` COPIES because
    /// the go-side arg-pass inc makes rc≥2, so the old `v` is always superseded;
    /// the copy path is the EXPOSURE, the missing slot-dec is the SEAM). Dec each
    /// superseded heap param before the jump, EXCEPT:
    ///  - a param whose reference TRANSFERS into a tail argument as a bare `Var`
    ///    (a MOVE — `transfer_skip`, self- or cross-slot): the box carries forward,
    ///    so dec'ing it would double-free the value the next iteration owns (the
    ///    exact contract the let flush honors);
    ///  - a borrowed param (the caller owns it);
    ///  - **analysis-ON only** — a param that SOME tail arg is an in-place COW
    ///    rooted at (`(vec-set p …)` / `(vec-push p …)` anywhere in the arg list,
    ///    not only at `p`'s own position — FIXME 0691): the mutate branch returns
    ///    `p`'s OWN box and forwards it into that slot, so the slot is NOT
    ///    superseded — dec'ing it would free the carried box; SKIP = leak-safe,
    ///    the both-polarity fence's safe direction: never an under-count / UAF.
    ///    Under `CRANELISP_NO_OWNERSHIP` the COW always copies (rc≥2 force-count),
    ///    so nothing is carried forward and the dec is always owed — the exemption
    ///    does NOT apply toggle-off (FIXME 0695). `conj`/`assoc` are USER-fn
    ///    calls, not these primitives, so the persistent-op leak is still fixed.
    ///
    /// The frames are NOT popped (the loop header reuses the param slots) — this
    /// only releases the superseded slot references.
    pub(crate) fn flush_superseded_heap_params_before_tail_jump(
        &mut self,
        args: &[MonoExpr],
        transfer_skip: &std::collections::HashSet<Symbol>,
    ) {
        let param_frame = match self.scope_stack.first() {
            Some(f) => f.clone(),
            None => return,
        };
        let analysis_off = cranelisp_types::ownership_analysis_off();
        let to_dec = self.collect_frame_heap_decs(&param_frame, |this, name| {
            // A borrowed param is the caller's to release — EXCEPT one this frame
            // PROMOTED because the back-edge supersedes its slot with a value the
            // caller does not own (FIXME 0720; the entry inc keeps the caller's
            // own reference out of reach of this dec).
            if transfer_skip.contains(name)
                || (this.is_borrowed(name) && !this.tco_owned_params.contains(name))
            {
                return true;
            }
            // In-place COW hazard (analysis-ON only): if SOME tail arg is an
            // in-place COW rooted at this param, the mutate branch may forward
            // the param's OWN box into that slot — dec'ing it would free the
            // carried box (skip, leak-safe). Positional-blind: the COW can feed
            // a DIFFERENT slot than the param's own (FIXME 0691). Toggle-off
            // always copies, so the dec is always owed (FIXME 0695).
            param_flush_exempts_inplace_cow(args, name, analysis_off)
        });
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
        if !in_let_frame || self.is_borrowed(name) {
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
        if self.is_borrowed(name) {
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
    /// The mark is recorded on the INNERMOST scope frame (FIXME 0692), so it is
    /// released when that frame pops and never bleeds into a later shadow/sibling
    /// binding of the same name.
    pub(crate) fn mark_borrowed(&mut self, name: &Symbol) {
        if let Some(top) = self.borrowed_stack.last_mut() {
            top.insert(name.clone());
        }
    }

    /// Is `name`'s CURRENT (innermost) binding borrowed? Resolves against the
    /// scope-stratified `borrowed_stack` (FIXME 0692): find the innermost scope
    /// frame that binds `name` and report THAT frame's borrowed mark. A borrowed
    /// mark on a name-colliding OUTER binding must not classify an inner
    /// shadow/sibling binding as borrowed (Principle 20 — borrowed is a property
    /// of a binder, not a name).
    pub(crate) fn is_borrowed(&self, name: &Symbol) -> bool {
        resolve_borrowed(&self.scope_stack, &self.borrowed_stack, name)
    }

    // === 0668 binding-indirection consume contract (W-B1 classifier) ==========
    //
    // `design/backend/binding-indirection-consume.md` §1/§2. The ONE shared
    // provenance classifier every consume/cleanup position keys off, instead of
    // its local node syntax. It answers the value-flow question — "does this
    // operand deliver (or forward) an independently-owned count, or is it an
    // ALIAS of a live binding that carries none?" — by tracing the operand to its
    // provenance root THROUGH binding-indirection (`let`-forward, match-var-arm
    // forward, nesting). It reads ONLY the scope stack (`variables` — "is this a
    // live binding"), NEVER an ownership fact, so it answers IDENTICALLY in both
    // `CRANELISP_NO_OWNERSHIP` toggle states by construction (§2, the load-bearing
    // contrast with the escape gate that makes 0668 a SEPARATE family from the
    // R14 producer ruling).

    /// The live-binding provenance ROOT of `node`, traced through
    /// binding-indirection, or `None` if the operand delivers an independent owned
    /// count (a producing op / fresh temporary transfers its own reference).
    ///
    /// `Some(root)` ⇒ the operand is an ALIAS of the live scope binding `root`:
    /// it carries NO independent count, so a consume position that stores/captures
    /// it must take one reference (R2) and a cleanup position must NOT dec it (R1).
    /// `None` ⇒ an owned temporary that transfers.
    ///
    /// Structural only (Var-rootedness / alias-forwarding) — analysis-independent.
    pub(crate) fn operand_live_binding_root(&self, node: &MonoExpr) -> Option<Symbol> {
        operand_live_binding_root(node, &|name| self.variables.contains_key(name))
    }

    /// Is `body` a FRESHLY-CONSTRUCTED value (a brand-new heap box that cannot
    /// alias any scope binding)? The thin `&self` wrapper over the pure
    /// [`is_fresh_construction`] (the ctor probe is the only context-dependent
    /// part; the shape rules are unit-tested directly).
    pub(crate) fn body_is_fresh_construction(&self, body: &MonoExpr) -> bool {
        is_fresh_construction(body, &|fq| self.ctx.ctor_meta_at(fq).is_some())
    }

    /// The dec side of the §13.7 COW escape gate, read at the match consume seam
    /// so R3 (forwarding-suppresses-dec) and the COW producer's escape-inc stay a
    /// MATCHED PAIR. Returns `true` iff `node` is a COW `vec-set`/`vec-push` site
    /// whose in-place/mutate branch emitted the retention inc on the returned
    /// pointer; then the scrutinee-dec is that inc's BALANCING dec and MUST fire.
    /// When it does not hold (non-COW temp, alias, toggle-off, or a
    /// nested/non-escaping COW whose gate declined the inc), the forwarding dec
    /// is spurious and R3 suppresses it. NOT a "distinguish wrong-`Some(false)`"
    /// workaround (R14/F4): a `Some(false)` is treated uniformly as "no
    /// escape-inc ⇒ suppress", never corrected.
    ///
    /// **FIXME 0693 (S115 W3 change-set 1) — consolidated.** This was a MIRROR
    /// that re-derived the site's identity from the syntactic callee spelling
    /// (`matches!(callee_name, "vec-set" | "vec-push")`) plus a `variables`
    /// liveness condition the producer does not have — the resolver-mirror class
    /// (P24: the name is a trigger, the CARRIER is the identity), with a latent
    /// UAF channel (a user fn literally named `vec-set` under
    /// `PreludeVariant::None` made the name test true although the producer's COW
    /// gate never ran; masked today only by typecheck recording
    /// `escapes = Some(false)` on that scrutinee — a mask the W4 escape-fact
    /// correction can lift). It is now a DERIVATION on two levels:
    ///
    /// 1. the site identity + gate condition come from the ONE shared predicate
    ///    [`cow_site_retain_verdict`], which the producer's
    ///    `cow_source_ownership` also calls (via `cow_source_is_borrowed` /
    ///    `cow_retains_reused_gate`) and which keys on the RESOLUTION CARRIER;
    /// 2. the value actually returned is the producer's OWN recorded decision
    ///    (`cow_retain_decisions`, span-keyed) whenever it is available.
    ///
    /// **The disagreement fence** is the `debug_assert_eq!` inside
    /// [`reconcile_cow_retain_verdict`]: if the recorded decision and the
    /// shared-predicate derivation ever disagree, the producer ran a different
    /// gate than this seam believes, which is exactly the spurious-dec (UAF)
    /// channel 0693 named. Release builds take the LEAK-SAFE verdict — see that
    /// function for why "trust the record" is the wrong polarity (FIXME 0751).
    pub(crate) fn scrutinee_cow_retains_reused(&self, node: &MonoExpr) -> bool {
        let Some(derived) = crate::compiler::vec_codegen::cow_site_retain_verdict(
            node,
            self.return_cow_source.as_ref(),
            cranelisp_types::ownership_analysis_off(),
        ) else {
            // Not a carrier-identified COW site ⇒ no retention inc exists.
            return false;
        };
        let MonoExpr::Apply { span, .. } = node else {
            return false;
        };
        reconcile_cow_retain_verdict(self.cow_retain_decisions.get(span).copied(), derived, *span)
    }
}

/// Reconcile the producer's RECORDED retain decision at a COW site's span
/// against the R3 seam's own shared-predicate DERIVATION (FIXME 0693 / 0751).
///
/// `recorded`: `Some(Some(v))` = one consistent verdict recorded at that span;
/// `Some(None)` = AMBIGUOUS (two distinct COW sites collapsed onto one span,
/// reachable only for `Span::SYNTHETIC` bodies); `None` = the producer never ran
/// in THIS compiler frame (the site was lowered by an inner compiler), so the
/// shared predicate is the answer.
///
/// **Every uncertain case takes the leak-safe verdict `false`** — suppress the
/// dec. A `true` the producer did not actually back with an inc is a spurious
/// dec, i.e. the UAF direction; a suppressed dec is at worst a leak.
///
/// The DISAGREEMENT arm (`Some(Some(recorded))` with `recorded != derived`) is
/// the one FIXME 0751 corrected. Its rustdoc used to claim a release build
/// "degrades to the producer's truth rather than to a guess" — but a
/// disagreement is precisely the state in which the seam does NOT know that the
/// record belongs to THIS site. The reachable shape: two COW sites share a
/// synthetic span; site A ran the producer and recorded `Some(true)`; site B —
/// the node being asked about — never recorded (its lowering took the
/// non-last-use copy path, which never calls `cow_source_ownership`, so no
/// collapse to the ambiguous marker happened); `derived(B) = false`. Returning
/// the record then fires B's dec with no inc behind it. The record is a
/// DIFFERENT SITE's truth, so it gets the same polarity the ambiguous arm
/// already had.
pub(crate) fn reconcile_cow_retain_verdict(
    recorded: Option<Option<bool>>,
    derived: bool,
    span: Span,
) -> bool {
    match recorded {
        // Agreement: the producer emitted exactly what this seam derived.
        Some(Some(recorded)) if recorded == derived => recorded,
        // Disagreement: loud in development, leak-safe in release.
        Some(Some(recorded)) => {
            debug_assert!(
                false,
                "FIXME 0693 disagreement fence: the COW producer \
                 (vec_codegen::cow_source_ownership) recorded retain_reused={recorded} at \
                 span {span:?}, but the R3 match-consume seam's shared-predicate derivation \
                 says {derived}. The two sides of the §13.7 escape gate MUST agree — a \
                 consumer-side `true` without a producer inc is a spurious dec (UAF)."
            );
            false
        }
        // Ambiguous span (two COW sites under one synthetic span).
        Some(None) => false,
        // The producer did not run in THIS compiler frame. Fall back to the
        // shared predicate — the same answer the consolidated gate gives, never
        // a re-derivation from the callee spelling.
        None => derived,
    }
}

/// Resolve a name's borrowed status against the scope-stratified stacks
/// (FIXME 0692). Finds the INNERMOST scope frame that binds `name` and reports
/// that frame's borrowed mark; a name-colliding OUTER binding's mark never bleeds
/// into an inner shadow/sibling binding. Pure over the two parallel stacks so the
/// shadow/sibling resolution is unit-testable without a live `FnCompiler`.
fn resolve_borrowed(
    scope_stack: &[Vec<Symbol>],
    borrowed_stack: &[std::collections::HashSet<Symbol>],
    name: &Symbol,
) -> bool {
    scope_stack
        .iter()
        .zip(borrowed_stack)
        .rev()
        .find(|(frame, _)| frame.contains(name))
        .is_some_and(|(_, borrowed)| borrowed.contains(name))
}

/// The MS-P8 param-flush in-place-COW exemption decision (pure — FIXMEs 0691,
/// 0695). A superseded heap param is EXEMPT from the tail-jump dec (SKIP,
/// leak-safe) iff analysis is ON **and** SOME tail arg is an in-place COW rooted
/// at the param:
///
/// - **Positional-blind (0691):** the scan is over ALL args, not just the arg at
///   the param's own position. An in-place `vec-set`/`vec-push` on param `p` can
///   forward `p`'s OWN box into a DIFFERENT slot (e.g. `(go (vec-set v 0 n) …)`
///   where `v`'s own slot takes a fresh value); the positional-only check dec'd
///   `v` and freed the carried box (UAF). Any-arg scan is leak-safe in the copy
///   case, correct in the mutate case — honouring the flush's own invariant
///   (never an under-count / UAF).
/// - **Toggle-off never exempts (0695):** under `CRANELISP_NO_OWNERSHIP` the COW
///   source is force-counted (rc≥2) so the op ALWAYS copies — nothing is carried
///   forward in place, the mutate-in-place rationale never holds, and the
///   superseded param's dec is always owed.
pub(crate) fn param_flush_exempts_inplace_cow(
    args: &[MonoExpr],
    name: &Symbol,
    analysis_off: bool,
) -> bool {
    if analysis_off {
        return false;
    }
    args.iter().any(|arg| arg_is_inplace_cow_on(arg, name))
}

/// Structural: is `arg` an IN-PLACE COW primitive (`vec-set`/`vec-push`) whose
/// source is the bare `Var` `name`? Such an op can return `name`'s OWN box when it
/// reuses in place, so the MS-P8 param-flush must not dec that param (the box is
/// carried forward). Free fn (no liveness) — a pure AST-shape predicate.
///
/// The COW-site identity comes from [`cow_site_source`] — the RESOLUTION
/// CARRIER, shared with the §13.7 gate (FIXME 0752 / Principle 24). A user fn
/// that merely SPELLS `vec-set` is not an in-place COW, and exempting its param
/// from the flush would suppress a dec that is owed.
pub(crate) fn arg_is_inplace_cow_on(arg: &MonoExpr, name: &Symbol) -> bool {
    let Some((source, _)) = crate::compiler::vec_codegen::cow_site_source(arg) else {
        return false;
    };
    matches!(source, MonoExpr::Var { name: s, .. } if s == name)
}

/// Structural: does `body` forward the binding `name` out as its value? True for
/// the bare `Var(name)` return and for a `let`/`match` that itself forwards it —
/// the value-flow shape a match var-pattern arm `[r <body>]` uses to pass the
/// scrutinee through (0668 §2 match-forward row). Never consults liveness — it is
/// a pure AST-shape predicate over the arm body.
pub(crate) fn body_forwards_binding(body: &MonoExpr, name: &Symbol) -> bool {
    match body {
        MonoExpr::Var { name: n, .. } => n == name,
        MonoExpr::Let { body, .. } => body_forwards_binding(body, name),
        MonoExpr::Match { arms, .. } => {
            // A nested match forwards `name` iff its selected var-pattern arm
            // rebinds the (forwarded) scrutinee and forwards THAT binder — the
            // §2 nesting row. Conservative: only the var-pattern-arm shape.
            arms.iter().any(|arm| match &arm.pattern {
                cranelisp_types::Pattern::Var { name: bound, .. } => {
                    body_forwards_binding(&arm.body, bound)
                }
                _ => false,
            })
        }
        _ => false,
    }
}

/// Structural: does this match FORWARD its scrutinee's provenance to the result?
/// True iff some arm is a var-pattern `[r <body forwarding r>]` (0668 §2). A
/// var-pattern is irrefutable, so in the tested family it is the sole/last arm and
/// this is exact; a mixed constructor+var match is out of the acceptance set.
pub(crate) fn match_forwards_scrutinee(arms: &[cranelisp_types::MonoMatchArm]) -> bool {
    arms.iter().any(|arm| match &arm.pattern {
        cranelisp_types::Pattern::Var { name, .. } => body_forwards_binding(&arm.body, name),
        _ => false,
    })
}

/// The W-B1 classifier core (0668 §1/§2), factored as a free function over a
/// liveness predicate so the provenance trace is unit-testable without a full
/// `FnCompiler` (the `return_cow_source_in_scope` precedent). `is_live(name)`
/// answers "is `name` a live scope binding" (the `variables` read the method
/// wrapper supplies). Traces Var-root → let-forward → match-var-forward → nested.
pub(crate) fn operand_live_binding_root(
    node: &MonoExpr,
    is_live: &impl Fn(&Symbol) -> bool,
) -> Option<Symbol> {
    match node {
        MonoExpr::Var { name, .. } => {
            if is_live(name) {
                Some(name.clone())
            } else {
                None
            }
        }
        MonoExpr::Let { body, .. } => operand_live_binding_root(body, is_live),
        MonoExpr::Match { scrutinee, arms, .. } => {
            if match_forwards_scrutinee(arms) {
                operand_live_binding_root(scrutinee, is_live)
            } else {
                None
            }
        }
        // Every producing op — vec-lit, ctor, COW result, string/lambda literal —
        // delivers its own count and transfers it: no live-binding root.
        _ => None,
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
/// loop-carried value on the stack.
///
/// **Self-call detection uses the SHARED [`is_self_call`] predicate** (FIXME
/// 0654) so gate 3 can never diverge from what the TCO lowering treats as a
/// back-edge: the carrier-keyed identity (fp1) + the `SigDispatch` mangled-name
/// shape (fp2). Before S113 W2b this gate scanned by BARE written name, which
/// MISSED fp1's carrier-matching / name-differing self-call (e.g. a qualified
/// `(user/qloop x)` self-ref) — for which the TCO lowering emits a back-edge but
/// the bare-name gate reported "no self-call", permitting a loop-carried stack
/// slot: a hard use-after-free. The bare written-name `Var` arm is RETAINED,
/// OR'd in as a documented over-approximation (declining stack alloc for a
/// non-back-edge is free correctness), so gate 3 stays a strict SUPERSET of the
/// TCO back-edge set AND of its own historical behaviour (the corpus is
/// byte-identical — the carrier-match / name-differ case is unreachable today,
/// see FIXME 0654 reachability probes). The sharper per-flow check ("only
/// decline when the value flows into a `recur` arg") is a noted follow-on.
/// Is `body` a FRESHLY-CONSTRUCTED value — a brand-new heap box that cannot
/// alias any scope binding? (The item-26 return-protect predicate; the license
/// for suppressing `protect_return_value`, S115 W3 change-set 2 / FIXME 0696.)
///
/// True for every **box-minting** node kind — the node's own lowering
/// unconditionally allocates: `ConstrADT`, `Lambda` (`compile_lambda`),
/// `StringLit`, `VecLit` (`compile_vec_lit`), an `Apply` whose callee resolves
/// to a constructor (`is_ctor` hits its carrier), and an `Apply` carrying the
/// `ResolvedCall::AutoCurry` resolution (`compile_auto_curry` `emit_alloc`s a
/// fresh curry env on every arm). A general `Apply` (a user/trait call) may
/// RETURN an aliased argument (e.g. `(id x)`), so it is NOT fresh and still
/// needs the return-protect — the §2.1 fence's G2/item-26 class, deliberately
/// untouched.
///
/// **FIXME 0749** widened the kind set from the two constructor shapes. Before
/// it, `Lambda`/`StringLit` were recognised by an ad-hoc `matches!` at the ONE
/// `protect_return_value` call site — fresh at depth 0, NOT fresh through a
/// `let` — and `VecLit`/auto-curry were not recognised anywhere. Every one of
/// those gaps was a live per-iteration leak the moment the minted box was
/// returned through binding indirection and consumed as a temporary by the
/// caller: the protect inc has no balancing dec, because the value is not a
/// scope binding for cleanup to dec and the caller's consuming dec is single.
/// Measured (100 iterations, `PrimitivesOnly`, `--run`):
/// `(defn mk [] (let [g (fn [a b] …)] (g 1)))` + `((mk) 2)` → allocs=201
/// deallocs=1 (the curry env AND its captured target stranded);
/// a lambda returned through two `let`s → allocs=301 deallocs=101;
/// a `VecLit` returned through one `let` → allocs=201 deallocs=101.
/// The kind set is the single source of freshness truth (Principle 7) —
/// `protect_return_value` no longer carries its own list.
///
/// Binding-indirection and control-flow joins FORWARD freshness:
/// - `Let` — a fresh construction returned through nested `let`s is still
///   fresh, so the suppression is SCALE-INVARIANT in heap-let depth (the R-3
///   fixed-residual signature);
/// - `If` / `Match` — fresh iff EVERY arm is fresh. One non-fresh arm (an arm
///   returning a scope binding, or a general `Apply` result) makes the join
///   non-fresh and the protect stands. This is what recognises the FIXME-0720
///   shape `(match g [(Gr cells) (Gr (vec-set cells 0 m))])` as the fresh
///   construction it is; the analysis-ON path already reached that verdict via
///   `return_is_fresh_by_summary`, so the two now agree by construction rather
///   than by coincidence (Principle 7).
///
/// Analysis-independent (reads only the ctor carrier, never an ownership fact),
/// so it answers identically under both `CRANELISP_NO_OWNERSHIP` states.
/// Pure over the node + the ctor probe, so the shape rules are unit-testable
/// without a live `FnCompiler` (the `operand_live_binding_root` precedent).
pub(crate) fn is_fresh_construction(
    body: &MonoExpr,
    is_ctor: &impl Fn(&cranelisp_types::FQSymbol) -> bool,
) -> bool {
    match body {
        // The box-MINTING node kinds: each unconditionally allocates a brand-new
        // box in its own lowering, so none can alias a scope binding.
        MonoExpr::ConstrADT { .. }
        | MonoExpr::Lambda { .. }
        | MonoExpr::StringLit { .. }
        | MonoExpr::VecLit { .. } => true,
        // An `Apply` is fresh iff its RESOLUTION CARRIER says it mints a box:
        // a constructor call, or an auto-curry (whose lowering
        // `compile_auto_curry` allocates a fresh curry env on every arm). Any
        // other call may RETURN an aliased argument (`(id x)`), so it is not
        // fresh — the identity comes from the carrier, never the callee's
        // spelling or shape (Principle 24).
        MonoExpr::Apply { callee, resolved_call, .. } => {
            if matches!(
                resolved_call.as_deref(),
                Some(cranelisp_types::ResolvedCall::AutoCurry { .. })
            ) {
                return true;
            }
            match callee.as_ref() {
                MonoExpr::Var { resolution: VarRef::Global(fq), .. } => is_ctor(fq),
                _ => false,
            }
        }
        MonoExpr::Let { body, .. } => is_fresh_construction(body, is_ctor),
        MonoExpr::If { then_branch, else_branch, .. } => {
            is_fresh_construction(then_branch, is_ctor)
                && is_fresh_construction(else_branch, is_ctor)
        }
        MonoExpr::Match { arms, .. } => {
            !arms.is_empty() && arms.iter().all(|arm| is_fresh_construction(&arm.body, is_ctor))
        }
        // EXHAUSTIVE, deliberately (no `_ =>`) — the standing instrument for
        // this predicate. The 0749 leak was a node kind that MINTS a box being
        // silently swept into a catch-all "not fresh", which emits a protect
        // inc no dec can balance. A new `MonoExpr` variant must now be
        // classified here explicitly rather than defaulting to a leak.
        //
        // Not fresh, each for its own reason:
        //  - `Var` IS a scope binding (the exact thing the protect exists for);
        //  - scalar literals are never heap, so the protect is a no-op anyway;
        //  - `Trace` forwards its inner expression's value — it may be a
        //    binding;
        //  - `ParBind` / `LaunchContinue` yield a joined/continued value whose
        //    provenance is not this frame's to claim.
        MonoExpr::Var { .. }
        | MonoExpr::IntLit { .. }
        | MonoExpr::FloatLit { .. }
        | MonoExpr::BoolLit { .. }
        | MonoExpr::Trace { .. }
        | MonoExpr::ParBind { .. }
        | MonoExpr::LaunchContinue { .. } => false,
    }
}

/// The authoritative per-position parameter types of `defn`, read from the
/// symbol table's `Scheme.ty` (Principle 7 — the ONE lookup shared by
/// [`FnCompiler::bind_defn_params`] and the FIXME-0720 promotion set, which must
/// classify heap-ness against exactly the types the binder records). `None` at a
/// position ⇒ no authoritative type (the binder falls back to use-site inference;
/// the promotion declines).
fn defn_param_types<C, L>(
    ctx: &CompileContext<'_, C, L>,
    defn: &Defn,
) -> Vec<Option<Type>>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    ctx.symbol_tables
        .get(&ctx.current_module)
        .and_then(|table| {
            if let Some(ModuleEntry::Def { scheme, .. }) = table.get(defn.name.as_ref())
                && let Type::Fn(ref param_types, _) = scheme.ty
            {
                return Some(param_types.iter().map(|t| Some(t.clone())).collect());
            }
            None
        })
        .unwrap_or_else(|| vec![None; defn.params().len()])
}

/// Is the tail self-call argument at position `i` a value that SUPERSEDES the
/// param slot — i.e. NOT a bare `Var` naming the param itself? (FIXME 0720.)
///
/// A bare `Var` of the same name CARRIES the slot forward (the `transfer_skip`
/// move contract: the same box occupies the slot after the jump, so nothing is
/// released and nothing needs to be owned). Anything else — a temporary, a
/// different binding, a control-flow join — replaces the slot's occupant, and the
/// old occupant's reference is the one that leaked.
///
/// Pure over the argument list, so the whole decision table is unit-testable
/// without a live `FnCompiler`.
pub(crate) fn tail_arg_supersedes_param(arg: &MonoExpr, param: &Symbol) -> bool {
    !matches!(arg, MonoExpr::Var { name, .. } if name == param)
}

/// The `Borrowed` heap params that a tail self-call supersedes — the set
/// [`FnCompiler::compile_body`] promotes to frame-owned (FIXME 0720; see the
/// `tco_owned_params` field rustdoc for the ownership invariant).
///
/// Narrow by construction: a param qualifies only when ALL of
/// 1. the ownership summary marks it `Borrowed` (an `Owned` param is already
///    flushed and released — the bare-vec twin, which must not change), and
/// 2. it is heap-typed (nothing to release otherwise), and
/// 3. some self-call in the body passes a SUPERSEDING argument at its position.
///
/// A function without a self-call, or one that only carries its params forward
/// (`(go v (- n 1))`), promotes nothing and is byte-identical.
fn tco_promoted_borrowed_params<C, L>(
    defn: &Defn,
    body: &MonoExpr,
    mode_summary: Option<&cranelisp_types::ModeSummary>,
    ctx: &CompileContext<'_, C, L>,
) -> Vec<(usize, Symbol, HeapCategory)>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let Some(summary) = mode_summary else {
        // Toggle-off / summary-absent ⇒ no param is `Borrowed` ⇒ nothing to
        // promote (the conservative all-`Owned` lowering already flushes).
        return Vec::new();
    };
    let param_types = defn_param_types(ctx, defn);
    defn.params()
        .iter()
        .enumerate()
        .filter_map(|(i, (param_name, _))| {
            if summary.param_mode(i) != cranelisp_types::Mode::Borrowed {
                return None;
            }
            let ty = param_types.get(i)?.as_ref()?;
            let category = signature_heap_category(ty, Some(ctx.symbol_tables));
            if !matches!(category, HeapCategory::AlwaysHeap | HeapCategory::Mixed) {
                return None;
            }
            if !self_call_supersedes_param(body, &defn.name, &ctx.current_module, i, param_name) {
                return None;
            }
            Some((i, param_name.clone(), category))
        })
        .collect()
}

/// Does some self-call in `body` pass a SUPERSEDING argument at position `i`?
/// (FIXME 0720 — the promotion trigger.)
fn self_call_supersedes_param(
    body: &MonoExpr,
    fn_name: &Symbol,
    current_module: &ModuleFullPath,
    index: usize,
    param: &Symbol,
) -> bool {
    let mut found = false;
    visit_self_calls(body, fn_name, current_module, &mut |args| {
        if args.len() > index && tail_arg_supersedes_param(&args[index], param) {
            found = true;
        }
    });
    found
}

pub(crate) fn body_has_self_call(
    body: &MonoExpr,
    fn_name: &Symbol,
    current_module: &ModuleFullPath,
) -> bool {
    let mut found = false;
    visit_self_calls(body, fn_name, current_module, &mut |_| found = true);
    found
}

/// Visit the argument list of every self-call in `body` (ONE walk, shared by the
/// B3.4 stack-alloc gate 3 [`body_has_self_call`] and the FIXME-0720 promotion
/// trigger [`self_call_supersedes_param`] — Principle 7: the two answer different
/// questions about the SAME call set, so they must not walk the tree twice with
/// two independently-maintained arm lists).
///
/// Self-call identity is the shared [`is_self_call`] carrier predicate OR the
/// historical bare-name over-approximation (always sound to over-report here:
/// gate 3 declines a stack slot, the 0720 promotion adds a balanced inc/dec pair).
/// The match is exhaustive over `MonoExpr` by construction — a new variant is a
/// compile error, not a silently unvisited subtree.
fn visit_self_calls(
    body: &MonoExpr,
    fn_name: &Symbol,
    current_module: &ModuleFullPath,
    f: &mut impl FnMut(&[MonoExpr]),
) {
    use cranelisp_types::MonoExpr as E;
    match body {
        E::Apply { callee, args, resolved_call, .. } => {
            if is_self_call(callee, resolved_call.as_deref(), current_module, Some(fn_name))
                || matches!(callee.as_ref(), E::Var { name, .. } if name == fn_name)
            {
                f(args);
            }
            visit_self_calls(callee, fn_name, current_module, f);
            for a in args {
                visit_self_calls(a, fn_name, current_module, f);
            }
        }
        E::Let { bindings, body, .. } | E::ParBind { bindings, body, .. } => {
            for (_, v) in bindings {
                visit_self_calls(v, fn_name, current_module, f);
            }
            visit_self_calls(body, fn_name, current_module, f);
        }
        E::If { cond, then_branch, else_branch, .. } => {
            visit_self_calls(cond, fn_name, current_module, f);
            visit_self_calls(then_branch, fn_name, current_module, f);
            visit_self_calls(else_branch, fn_name, current_module, f);
        }
        E::Lambda { body, .. } | E::Trace { body, .. } => {
            visit_self_calls(body, fn_name, current_module, f);
        }
        E::Match { scrutinee, arms, .. } => {
            visit_self_calls(scrutinee, fn_name, current_module, f);
            for a in arms {
                visit_self_calls(&a.body, fn_name, current_module, f);
            }
        }
        E::VecLit { elements, .. } => {
            for el in elements {
                visit_self_calls(el, fn_name, current_module, f);
            }
        }
        E::LaunchContinue { launched, continuation, .. } => {
            visit_self_calls(launched, fn_name, current_module, f);
            visit_self_calls(continuation, fn_name, current_module, f);
        }
        E::ConstrADT { fields, .. } => {
            for fl in fields {
                visit_self_calls(fl, fn_name, current_module, f);
            }
        }
        E::IntLit { .. }
        | E::FloatLit { .. }
        | E::BoolLit { .. }
        | E::StringLit { .. }
        | E::Var { .. } => {}
    }
}

/// The ONE self-call identity predicate (Principle 7 single-source-of-truth /
/// Principle 24 "Resolve once") — consumed by the TCO fast-path (`compile_apply`,
/// `apply.rs`), the B3.4 stack-allocation gate 3 ([`body_has_self_call`]), and
/// the spark SCC classifier (`classify_spark_callee`, `utilization.rs`). Before
/// S113 W2b (FIXME 0654) these three answered "is this a self-call?" three
/// divergent ways — carrier-keyed (fp1) vs bare written-name (gate 3 + spark) —
/// a Principle-7 violation whose gate-3 face is a latent loop-carried stack-slot
/// UAF (a carrier-matching / name-differing self-call TCO-loops while a bare-name
/// gate permits the stack slot).
///
/// A call is a self-call iff EITHER:
/// - **carrier-keyed (fp1 shape):** the callee `Var`'s `VarRef::Global` storage
///   FQ equals the current fn's storage identity `{current_module,
///   current_fn_name}` — module AND symbol (the S113 W2b carrier fix; S114 typed
///   flip re-types the compared value from `Option<FQSymbol>` to the
///   `VarRef::Global` arm). A match requires the recorded storage target to BE
///   the current fn's identity, so a false positive is impossible; a
///   `VarRef::Local` callee (e.g. a `let`/`fn`/param local shadowing the fn name)
///   never matches here — self-recursion arrives as `VarRef::Global`; OR
/// - **`SigDispatch`-mangled (fp2 shape):** `resolved_call` is `SigDispatch {
///   mangled_name }` and `mangled_name == current_fn_name` — the monomorphised
///   constrained-poly self-recursion shape, where the callee's written name is
///   the base name but the current fn is the `{home}/{bare}${sig}` mono variant.
///   The `{home}/` prefix embeds the module, so a cross-module same-signature
///   dispatch fails to match by construction (`backend.md` §2.7.1).
///
/// Decides by the KEYED carrier / resolved dispatch, NEVER by bare written-name
/// equality (the 0632 name-as-identity class). `None` `current_fn_name` ⇒ never.
pub(crate) fn is_self_call(
    callee: &MonoExpr,
    resolved_call: Option<&ResolvedCall>,
    current_module: &ModuleFullPath,
    current_fn_name: Option<&Symbol>,
) -> bool {
    let Some(fn_name) = current_fn_name else {
        return false;
    };
    if let MonoExpr::Var { resolution: VarRef::Global(fq), .. } = callee
        && fq.module == *current_module
        && fq.symbol == *fn_name
    {
        return true;
    }
    matches!(
        resolved_call,
        Some(ResolvedCall::SigDispatch { mangled_name })
            if mangled_name.as_ref() == fn_name.as_ref()
    )
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
    use super::is_self_call;
    use cranelisp_types::{
        ConcreteType, FQSymbol, FQTypeName, JitSymbol, ModuleFullPath, MonoExpr, ResolvedCall,
        Span, Symbol, TypeName,
    };

    fn int() -> ConcreteType {
        ConcreteType::Int
    }
    /// The enclosing module for the gate-3 fixtures. The bare-name / SigDispatch
    /// arms are module-agnostic; only the carrier arm consults it.
    fn m() -> ModuleFullPath {
        ModuleFullPath::from("user")
    }
    fn var(name: &str) -> MonoExpr {
        // No carrier ⇒ a `VarRef::Local` (a scope-stack/shadow reference); the
        // is_self_call carrier arm never matches a `Local`.
        MonoExpr::Var { name: Symbol::from(name), span: Span::new(0, 1), resolved_call: None, ty: int(), resolution: cranelisp_types::VarRef::Local { binder: Symbol::from(name), binding_span: Span::SYNTHETIC } }
    }
    /// A `Var` carrying a `VarRef::Global` storage FQ — the fp1 carrier shape.
    fn var_with_target(name: &str, module: &str, symbol: &str) -> MonoExpr {
        MonoExpr::Var {
            name: Symbol::from(name), span: Span::new(0, 1), resolved_call: None, ty: int(),
            resolution: cranelisp_types::VarRef::Global(FQSymbol { module: ModuleFullPath::from(module), symbol: Symbol::from(symbol) }),
        }
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
            dispatch: cranelisp_types::ApplyRef::ViaCallee,
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
        assert!(body_has_self_call(&apply("f", vec![], None, None), &f, &m()));
    }
    #[test]
    fn detects_self_call_nested_in_let_if_match_and_arg() {
        let f = Symbol::from("f");
        let call = || apply("f", vec![], None, None);
        // in a let body
        assert!(body_has_self_call(
            &MonoExpr::Let { bindings: vec![], body: Box::new(call()), span: Span::new(0, 4), ty: int() }, &f, &m()));
        // in an if branch
        assert!(body_has_self_call(
            &MonoExpr::If { cond: Box::new(var("c")), then_branch: Box::new(var("a")), else_branch: Box::new(call()), span: Span::new(0, 5), ty: int() }, &f, &m()));
        // in an ARGUMENT position (non-tail self-call — still declined, conservative)
        assert!(body_has_self_call(&apply("g", vec![call()], None, None), &f, &m()));
    }
    #[test]
    fn detects_sig_dispatch_mangled_self_call() {
        // spec: design/backend/ownership-codegen.md §4.1 gate 3 — mono self-call by mangled name
        let f = Symbol::from("f$Int");
        let e = apply("f", vec![], None, Some(ResolvedCall::SigDispatch { mangled_name: JitSymbol::from("f$Int") }));
        assert!(body_has_self_call(&e, &f, &m()));
    }
    #[test]
    fn no_self_call_for_foreign_callee() {
        // spec: design/backend/ownership-codegen.md §4.1 gate 3 — a different name is not self
        let f = Symbol::from("f");
        assert!(!body_has_self_call(&apply("g", vec![var("x")], None, None), &f, &m()));
        assert!(!body_has_self_call(&var("x"), &f, &m()));
    }

    // spec: design/backend/ownership-codegen.md §4.1 gate 3 — FIXME 0654: gate 3
    // and the TCO lowering must decide self-call by the SAME (carrier-keyed)
    // predicate. A callee whose `resolved_target` storage FQ equals the current
    // fn's identity but whose WRITTEN name differs (e.g. a qualified
    // `(user/qloop x)` self-ref where the fn is `s1`) IS a TCO back-edge (fp1
    // fires on the carrier); gate 3 MUST therefore decline stack allocation for
    // it. The pre-S113 bare-name scan MISSED this (name differs) → the fp1/gate-3
    // divergence that is a latent loop-carried stack-slot UAF. This pins that the
    // two decisions cannot diverge: `body_has_self_call` returns true here exactly
    // because it now consults `is_self_call`, and `is_self_call` (the predicate
    // fp1 also calls) returns true for the same node.
    #[test]
    fn gate3_agrees_with_tco_on_carrier_matching_name_differing_self_call() {
        let f = Symbol::from("s1");
        // callee written `qloop` but carrier == the current fn's storage FQ.
        let callee = var_with_target("qloop", "user", "s1");
        let node = MonoExpr::Apply {
            dispatch: cranelisp_types::ApplyRef::ViaCallee,
            callee: Box::new(callee.clone()), args: vec![], span: Span::new(0, 3),
            resolved_call: None, ty: int(),
            escapes: None, confined: None, unique_static: None, provenance: None,
        };
        // The TCO lowering's predicate fires (carrier match, module+symbol)…
        assert!(is_self_call(&callee, None, &m(), Some(&f)));
        // …so gate 3 MUST also fire (no divergence → no loop-carried stack UAF).
        assert!(body_has_self_call(&node, &f, &m()));
        // Guard the module-precision: a carrier in a DIFFERENT module is NOT self.
        let foreign = var_with_target("qloop", "other", "s1");
        assert!(!is_self_call(&foreign, None, &m(), Some(&f)));
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
        let func_ids: Map<Symbol, cranelift_module::FuncId> = Map::new();
        let func_arities: Map<Symbol, usize> = Map::new();
        let ctx = crate::compiler::CompileContext {
            func_ids: &func_ids,
            func_arities: &func_arities,
            symbol_tables: &tables,
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
/// Sound-consumer contract (post-FIXME-0520 + S111 §3.7, see
/// [`FnCompiler::return_is_fresh_by_summary`] for the full rationale):
/// `summary` is `Some` with `result == ResultMode::Fresh`. `None` ⇒ Decision-24
/// (protect verbatim) — the byte-identical-`CRANELISP_NO_OWNERSHIP` guarantee.
///
/// `Fresh` is sound to elide on iff the summary chain's leaf facts are
/// truthful+reachable: 0520 cured the join-collapse and S111 §3.7 cured the
/// false-declaration (`vec-set`/`vec-push` → `MayAliasOf(0)`) + unreachable-
/// declaration (prelude-fallback-aware envs) classes. A body that returns a
/// param on any reachable path reports `MayAliasOf`/`AliasOf`/`ProjectionOf`,
/// never `Fresh`. A `MayAliasOf`/`ProjectionOf`/`AliasOf` result KEEPS the
/// protect (the binary `== Fresh` read is safe-direction for every non-`Fresh`
/// variant, Principle 18): the callee
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
/// byte-identical to pre-fix.
///
/// **The COW-site identity comes from [`cow_site_source`]** — the RESOLUTION
/// CARRIER, shared with the §13.7 gate (FIXME 0752 / Principle 24). It used to
/// read the callee `Var`'s written name, defended by "the vec-query primitive
/// names are canonical and never aliased at a value site" — the claim FIXME
/// 0693 falsified for the sibling seam. This site is the sharper one of the
/// pair: its product [`FnCompiler::return_cow_source`] is an INPUT to
/// `cow_source_is_borrowed`, so a user fn spelled `vec-set` perturbed the
/// CONSOLIDATED gate from one level upstream.
///
/// Free function (not an associated fn) so the ownership DECISION is unit-testable
/// without constructing a generic `FnCompiler` — the `return_is_fresh_by_summary`
/// precedent.
pub(crate) fn return_cow_source_in_scope(
    body: &MonoExpr,
    scope_frame: Option<&Vec<Symbol>>,
) -> Option<Symbol> {
    let (source, _) = crate::compiler::vec_codegen::cow_site_source(body)?;
    let MonoExpr::Var { name: src, .. } = source else {
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
            resolution: cranelisp_types::VarRef::Local { binder: Symbol::from(name), binding_span: Span::SYNTHETIC },
            ty: int_ty(),
        }
    }

    /// A COW site as typecheck RESOLVES it — carrier present (FIXME 0752 / P24).
    fn cow_call(prim: &str, src: MonoExpr) -> MonoExpr {
        cow_call_carrier(prim, src, Some(prim))
    }

    /// `carrier: None` = a user-defined fn that merely SPELLS `prim`.
    fn cow_call_carrier(prim: &str, src: MonoExpr, carrier: Option<&str>) -> MonoExpr {
        MonoExpr::Apply {
            dispatch: cranelisp_types::ApplyRef::ViaCallee,
            callee: Box::new(var(prim)),
            args: vec![src, var("i"), var("x")],
            span: Span::new(0, 9),
            resolved_call: carrier.map(|n| {
                Box::new(cranelisp_types::ResolvedCall::BuiltinFn { name: Symbol::from(n) })
            }),
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

    // spec: FIXME 0752 (NEGATIVE, the SHARP cell) — this producer FEEDS the
    // consolidated R3 gate (`return_cow_source` is an input to
    // `cow_source_is_borrowed`), so a spelling read here re-opens the exact
    // channel 0693 closed, one level upstream. A user fn named `vec-set` must
    // not make its argument the function's return-COW-source: that would
    // suppress a scope-exit dec nothing else discharges AND flip a real COW
    // site's copy branch to `Owned`.
    #[test]
    fn a_user_fn_spelled_vec_set_is_not_the_return_cow_source_neg() {
        let f = frame(&["v", "i", "x"]);
        assert_eq!(
            return_cow_source_in_scope(&cow_call_carrier("vec-set", var("v"), None), Some(&f)),
            None
        );
        // ...and the carrier's NAME is what is read, not the callee Var's.
        assert_eq!(
            return_cow_source_in_scope(
                &cow_call_carrier("vec-set", var("v"), Some("vec-get")),
                Some(&f)
            ),
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
            dispatch: cranelisp_types::ApplyRef::ViaCallee,
            callee: Box::new(MonoExpr::Var {
                resolution: cranelisp_types::VarRef::Local { binder: Symbol::from("f"), binding_span: Span::SYNTHETIC },
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
            then_branch: Box::new(MonoExpr::Var { name: Symbol::from("v"), span: Span::new(1, 2), resolved_call: None, resolution: cranelisp_types::VarRef::Local { binder: Symbol::from("v"), binding_span: Span::SYNTHETIC }, ty: int_ty() }),
            else_branch: Box::new(MonoExpr::Var { name: Symbol::from("w"), span: Span::new(2, 3), resolved_call: None, resolution: cranelisp_types::VarRef::Local { binder: Symbol::from("w"), binding_span: Span::SYNTHETIC }, ty: int_ty() }),
            span: Span::new(0, 4),
            ty: int_ty(),
        }
    }

    fn var_body() -> MonoExpr {
        MonoExpr::Var { name: Symbol::from("v"), span: Span::new(0, 1), resolved_call: None, ty: int_ty(), resolution: cranelisp_types::VarRef::Local { binder: Symbol::from("v"), binding_span: Span::SYNTHETIC } }
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
        MonoExpr::Apply { callee: Box::new(MonoExpr::Var { name: "f".into(), span: Span::new(0, 1), resolved_call: None, resolution: cranelisp_types::VarRef::Local { binder: "f".into(), binding_span: Span::SYNTHETIC }, ty: int() }), args: vec![], span: Span::new(0, 2), resolved_call: None, ty: int(), escapes: None, confined: c, unique_static: None, provenance: None, dispatch: cranelisp_types::ApplyRef::ViaCallee }
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
        let var = MonoExpr::Var { name: "v".into(), span: Span::new(0, 1), resolved_call: None, resolution: cranelisp_types::VarRef::Local { binder: "v".into(), binding_span: Span::SYNTHETIC }, ty: int() };
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

#[cfg(test)]
mod binding_indirection_classifier_tests {
    //! W-B1 unit matrix (`design/backend/binding-indirection-consume.md` §5): the
    //! ONE shared provenance classifier `operand_live_binding_root` +
    //! `match_forwards_scrutinee`. Structural, analysis-independent — reads only a
    //! liveness predicate, never an ownership fact. Cells: Var-root, producing-op
    //! temp, let-forward, match-var-forward, nested; a non-live Var ⇒ None.
    use super::{match_forwards_scrutinee, operand_live_binding_root};
    use cranelisp_types::{
        ConcreteType, MonoExpr, MonoMatchArm, Pattern, Span, Symbol, VarRef,
    };

    fn var(name: &str) -> MonoExpr {
        MonoExpr::Var {
            name: Symbol::from(name),
            span: Span::new(0, 1),
            resolved_call: None,
            resolution: VarRef::Local {
                binder: Symbol::from(name),
                binding_span: Span::SYNTHETIC,
            },
            ty: ConcreteType::Int,
        }
    }

    fn vec_lit() -> MonoExpr {
        MonoExpr::VecLit {
            elements: vec![],
            span: Span::new(0, 1),
            ty: ConcreteType::Int,
            escapes: None,
            confined: None,
            unique_static: None,
        }
    }

    // `(match <scrut> [r r])` — a single var-pattern arm forwarding its binder.
    fn var_match(scrut: MonoExpr, binder: &str) -> MonoExpr {
        MonoExpr::Match {
            scrutinee: Box::new(scrut),
            arms: vec![MonoMatchArm {
                pattern: Pattern::Var {
                    name: Symbol::from(binder),
                    span: Span::new(0, 1),
                },
                body: var(binder),
                span: Span::new(0, 1),
                provenance: None,
                resolved_ctor: None,
            }],
            span: Span::new(0, 1),
            compiler_generated: false,
            ty: ConcreteType::Int,
        }
    }

    fn live<'a>(names: &'a [&'a str]) -> impl Fn(&Symbol) -> bool + 'a {
        move |n: &Symbol| names.iter().any(|x| *x == n.as_ref())
    }

    // Cell 1 — a bare `Var` naming a live binding is that binding's alias (root).
    #[test]
    fn var_root_of_live_binding() {
        assert_eq!(
            operand_live_binding_root(&var("v"), &live(&["v"])),
            Some(Symbol::from("v"))
        );
    }

    // Cell 2 — a `Var` naming NO live binding (a fn-as-value name / free ref) is
    // NOT an alias: it mints its own value ⇒ None (a NeverHeap/fresh Var ⇒ no inc).
    #[test]
    fn var_not_live_is_not_an_alias() {
        assert_eq!(operand_live_binding_root(&var("v"), &live(&["other"])), None);
    }

    // Cell 3 — a producing op (vec-lit, ctor, …) delivers its own count ⇒ None.
    #[test]
    fn producing_op_temp_is_not_an_alias() {
        assert_eq!(operand_live_binding_root(&vec_lit(), &live(&["v"])), None);
    }

    // Cell 4 — a `let` forwards its BODY's provenance: `(let [q …] v)` roots at v.
    #[test]
    fn let_forwards_body_root() {
        let node = MonoExpr::Let {
            bindings: vec![(Symbol::from("q"), vec_lit())],
            body: Box::new(var("v")),
            span: Span::new(0, 1),
            ty: ConcreteType::Int,
        };
        assert_eq!(
            operand_live_binding_root(&node, &live(&["v"])),
            Some(Symbol::from("v"))
        );
    }

    // Cell 5 — a var-pattern match forwards the scrutinee's provenance:
    // `(match v [r r])` roots at v.
    #[test]
    fn match_var_pattern_forwards_scrutinee_root() {
        assert_eq!(
            operand_live_binding_root(&var_match(var("v"), "r"), &live(&["v"])),
            Some(Symbol::from("v"))
        );
    }

    // Cell 6 — NESTED forward: `(match (match v [r r]) [q q])` traces to v (cell F).
    #[test]
    fn nested_match_forwards_to_root() {
        let inner = var_match(var("v"), "r");
        assert_eq!(
            operand_live_binding_root(&var_match(inner, "q"), &live(&["v"])),
            Some(Symbol::from("v"))
        );
    }

    // Cell 7 — a match forwarding a producing-op temp has NO live-binding root
    // (the temp transfers its own count), but IS a forwarding match structurally.
    #[test]
    fn match_forwarding_fresh_temp_has_no_root_but_forwards() {
        let m = var_match(vec_lit(), "r");
        assert_eq!(operand_live_binding_root(&m, &live(&["v"])), None);
        if let MonoExpr::Match { arms, .. } = &m {
            assert!(match_forwards_scrutinee(arms), "single [r r] arm forwards");
        }
    }

    /// A COW site as typecheck RESOLVES it — carrier present
    /// (`ResolvedCall::BuiltinFn`), which is what identifies a COW builtin
    /// (FIXME 0752 / P24).
    fn cow_call(prim: &str, src: MonoExpr) -> MonoExpr {
        cow_call_carrier(prim, src, Some(prim))
    }

    /// A call that merely SPELLS `prim` but resolved elsewhere. `carrier: None`
    /// is the user-defined fn named `vec-set` (legal under
    /// `PreludeVariant::None`) — the latent channel FIXME 0693 closed at the R3
    /// seam and 0752 closed here.
    fn cow_call_carrier(prim: &str, src: MonoExpr, carrier: Option<&str>) -> MonoExpr {
        MonoExpr::Apply {
            dispatch: cranelisp_types::ApplyRef::ViaCallee,
            callee: Box::new(var(prim)),
            args: vec![src, var("i"), var("x")],
            span: Span::new(0, 1),
            resolved_call: carrier.map(|n| {
                Box::new(cranelisp_types::ResolvedCall::BuiltinFn { name: Symbol::from(n) })
            }),
            ty: ConcreteType::Int,
            escapes: None,
            confined: None,
            unique_static: None,
            provenance: None,
        }
    }

    // MS-P8 in-place guard — `(vec-set p …)` / `(vec-push p …)` on a param `p` may
    // return `p`'s own box, so the param-flush must SKIP it (never dec the carried
    // box → the both-polarity fence's leak-safe direction).
    #[test]
    fn arg_is_inplace_cow_on_matches_vecset_and_vecpush_on_param() {
        use super::arg_is_inplace_cow_on;
        let p = Symbol::from("v");
        assert!(arg_is_inplace_cow_on(&cow_call("vec-set", var("v")), &p));
        assert!(arg_is_inplace_cow_on(&cow_call("vec-push", var("v")), &p));
        // A COW on a DIFFERENT source is not in-place on `v` (v IS superseded ⇒
        // must be dec'd, so it is NOT skipped).
        assert!(!arg_is_inplace_cow_on(&cow_call("vec-set", var("w")), &p));
        // A user-fn call (`conj`) is NOT an in-place primitive — the persistent-op
        // leak MUST still be fixed (dec fires).
        assert!(!arg_is_inplace_cow_on(&cow_call("conj", var("v")), &p));
        // A non-COW primitive is not skipped.
        assert!(!arg_is_inplace_cow_on(&cow_call("vec-get", var("v")), &p));
    }

    // spec: FIXME 0752 (NEGATIVE, the load-bearing cell) — COW-site identity at
    // the MS-P8 param-flush seam comes from the RESOLUTION CARRIER, never the
    // callee's written spelling. A user fn literally named `vec-set` (legal
    // under `PreludeVariant::None`) is NOT an in-place COW: exempting its param
    // from the tail-jump flush suppresses a dec that IS owed (a leak), and the
    // "the vec primitive names are canonical" rationale is the claim 0693
    // falsified for the sibling seam.
    #[test]
    fn a_user_fn_spelled_vec_set_is_not_an_inplace_cow_neg() {
        use super::{arg_is_inplace_cow_on, param_flush_exempts_inplace_cow};
        let p = Symbol::from("v");
        let spelled = cow_call_carrier("vec-set", var("v"), None);
        assert!(!arg_is_inplace_cow_on(&spelled, &p));
        assert!(!param_flush_exempts_inplace_cow(&[spelled], &p, false));
        // ...and a COW SPELLING that resolved to a different builtin is likewise
        // not a COW site (the carrier's NAME is read, not the callee Var's).
        let mislabelled = cow_call_carrier("vec-set", var("v"), Some("vec-get"));
        assert!(!arg_is_inplace_cow_on(&mislabelled, &p));
    }

    // MS-P8 exemption matrix (FIXMEs 0691, 0695) — the param-flush in-place-COW
    // exemption decision, over {position × toggle}. Analysis-ON, exempt iff SOME
    // arg is an in-place COW rooted at the param (positional-blind); toggle-off,
    // never exempt.
    #[test]
    fn param_flush_exempts_inplace_cow_all_positions_analysis_on() {
        use super::param_flush_exempts_inplace_cow;
        let v = Symbol::from("v");
        // Own position: `(go (vec-set v …) …)`, `v` at slot 0.
        let own = [cow_call("vec-set", var("v")), var("n")];
        assert!(param_flush_exempts_inplace_cow(&own, &v, false));
        // CROSS position (0691): the COW on `v` feeds slot 0 (param `a`) while
        // `v`'s own slot (1) takes a fresh `[1 2 3]`. Positional-blind ⇒ exempt.
        let cross = [cow_call("vec-set", var("v")), vec_lit(), var("n")];
        assert!(param_flush_exempts_inplace_cow(&cross, &v, false));
        // No arg is an in-place COW rooted at `v` ⇒ NOT exempt (dec owed).
        let none = [var("v"), vec_lit(), var("n")];
        assert!(!param_flush_exempts_inplace_cow(&none, &v, false));
        // A user-fn call (`conj`) is not an in-place primitive ⇒ NOT exempt.
        let conj = [cow_call("conj", var("v")), var("n")];
        assert!(!param_flush_exempts_inplace_cow(&conj, &v, false));
    }

    #[test]
    fn param_flush_never_exempts_toggle_off() {
        use super::param_flush_exempts_inplace_cow;
        let v = Symbol::from("v");
        // Even the own-position in-place COW is NOT exempt toggle-off (0695): the
        // COW always copies (rc≥2 force-count), so the superseded dec is owed.
        let own = [cow_call("vec-set", var("v")), var("n")];
        assert!(!param_flush_exempts_inplace_cow(&own, &v, /* analysis_off = */ true));
        let cross = [cow_call("vec-set", var("v")), vec_lit(), var("n")];
        assert!(!param_flush_exempts_inplace_cow(&cross, &v, true));
    }

    // R1 borrowed-mark scope stratification (FIXME 0692) — `resolve_borrowed`
    // reports the INNERMOST binding's mark, so a name-colliding outer alias never
    // bleeds into an inner shadow/sibling binding.
    #[test]
    fn resolve_borrowed_is_innermost_binding_shadow_aware() {
        use super::resolve_borrowed;
        use std::collections::HashSet;
        let q = Symbol::from("q");
        let set = |names: &[&str]| -> HashSet<Symbol> {
            names.iter().map(|n| Symbol::from(*n)).collect()
        };
        let frame = |names: &[&str]| -> Vec<Symbol> {
            names.iter().map(|n| Symbol::from(*n)).collect()
        };

        // Shadow: outer `q` borrowed (frame 1), inner `q` OWNED (frame 2). The
        // inner binding resolves to its OWN (empty) mark ⇒ NOT borrowed.
        let scope = [frame(&["v"]), frame(&["q"]), frame(&["q"])];
        let borrowed = [set(&[]), set(&["q"]), set(&[])];
        assert!(!resolve_borrowed(&scope, &borrowed, &q));

        // After the inner frame pops, the OUTER borrowed `q` is recovered.
        let scope = [frame(&["v"]), frame(&["q"])];
        let borrowed = [set(&[]), set(&["q"])];
        assert!(resolve_borrowed(&scope, &borrowed, &q));

        // A borrowed param in frame 0 resolves when unshadowed.
        let scope = [frame(&["v"])];
        let borrowed = [set(&["v"])];
        assert!(resolve_borrowed(&scope, &borrowed, &Symbol::from("v")));

        // An unbound name is not borrowed.
        assert!(!resolve_borrowed(&scope, &borrowed, &q));
    }

    // F-R1 fresh-construction — a `ConstrADT` and a `let`-forwarded `ConstrADT` are
    // fresh (suppress main's IO-return protect); a general (non-ctor) `Apply` may
    // return an aliased arg and is NOT fresh (protect KEPT). The ctor-`Apply` arm
    // needs a live ctx and is covered e2e (`entry_main_heap_let_teardown_balances_r2`).
    #[test]
    fn body_forwards_binding_traces_through_let_and_match() {
        use super::body_forwards_binding;
        let name = Symbol::from("r");
        // Bare Var forwards.
        assert!(body_forwards_binding(&var("r"), &name));
        // A different Var does not.
        assert!(!body_forwards_binding(&var("q"), &name));
        // A let forwarding its body's `r`.
        let l = MonoExpr::Let {
            bindings: vec![(Symbol::from("z"), vec_lit())],
            body: Box::new(var("r")),
            span: Span::new(0, 1),
            ty: ConcreteType::Int,
        };
        assert!(body_forwards_binding(&l, &name));
        // A fresh producing op does not forward.
        assert!(!body_forwards_binding(&vec_lit(), &name));
    }

    // Cell 8 — a match whose var-arm does NOT forward its binder (body is a
    // different value) is not a forwarding match.
    #[test]
    fn match_var_arm_not_forwarding_is_not_a_forward() {
        let m = MonoExpr::Match {
            scrutinee: Box::new(var("v")),
            arms: vec![MonoMatchArm {
                pattern: Pattern::Var {
                    name: Symbol::from("r"),
                    span: Span::new(0, 1),
                },
                body: vec_lit(),
                span: Span::new(0, 1),
                provenance: None,
                resolved_ctor: None,
            }],
            span: Span::new(0, 1),
            compiler_generated: false,
            ty: ConcreteType::Int,
        };
        if let MonoExpr::Match { arms, .. } = &m {
            assert!(!match_forwards_scrutinee(arms));
        }
        assert_eq!(operand_live_binding_root(&m, &live(&["v"])), None);
    }
}

#[cfg(test)]
mod rc_release_sweep_tests {
    //! S115 W3 change-set 2 — the RC-release sweep's two backend seams
    //! (`design/backend/s115-carrier-and-rc-sweep.md` §2; `tests/plan/s115-test-plan.md`
    //! §6.5). Both are pinned at the exact predicate the emission keys on, so a
    //! revert of either mechanism flips these RED without needing a live JIT.
    //!
    //! 1. **Item-26 fresh-construction return** ([`is_fresh_construction`]) — the
    //!    license for suppressing `protect_return_value`. Generalised this sprint
    //!    from the `main`-keyed F-R1 special case (FIXME 0696: name-as-identity)
    //!    to freshness, and extended across control-flow joins, which is what
    //!    makes the toggle-OFF half of FIXME 0720 balance.
    //! 2. **TCO borrowed-param promotion** ([`tail_arg_supersedes_param`] /
    //!    [`self_call_supersedes_param`]) — the trigger that decides which
    //!    `Borrowed` heap params the frame must own across a TCO back-edge, the
    //!    toggle-ON half of FIXME 0720.

    use super::{is_fresh_construction, self_call_supersedes_param, tail_arg_supersedes_param};
    use cranelisp_types::{
        ConcreteType, FQSymbol, ModuleFullPath, MonoExpr, MonoMatchArm, Pattern, Span, Symbol,
        VarRef,
    };

    fn fq(module: &str, symbol: &str) -> FQSymbol {
        FQSymbol { module: ModuleFullPath::from(module), symbol: Symbol::from(symbol) }
    }

    fn var(name: &str) -> MonoExpr {
        MonoExpr::Var {
            resolution: VarRef::Local {
                binder: Symbol::from(name),
                binding_span: Span::SYNTHETIC,
            },
            name: Symbol::from(name),
            span: Span::SYNTHETIC,
            resolved_call: None,
            ty: ConcreteType::Int,
        }
    }

    fn global_var(module: &str, name: &str) -> MonoExpr {
        MonoExpr::Var {
            resolution: VarRef::Global(fq(module, name)),
            name: Symbol::from(name),
            span: Span::SYNTHETIC,
            resolved_call: None,
            ty: ConcreteType::Int,
        }
    }

    fn ctor_adt() -> MonoExpr {
        MonoExpr::ConstrADT {
            type_name: cranelisp_types::FQTypeName::new(
                ModuleFullPath::from("user"),
                cranelisp_types::TypeName::from("G2"),
            ),
            tag: 0,
            fields: vec![],
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
            escapes: None,
            confined: None,
            unique_static: None,
        }
    }

    fn apply(callee: MonoExpr, args: Vec<MonoExpr>) -> MonoExpr {
        MonoExpr::Apply {
            callee: Box::new(callee),
            args,
            span: Span::SYNTHETIC,
            resolved_call: None,
            dispatch: cranelisp_types::ApplyRef::ViaCallee,
            ty: ConcreteType::Int,
            escapes: None,
            confined: None,
            unique_static: None,
            provenance: None,
        }
    }

    fn match_of(scrutinee: MonoExpr, bodies: Vec<MonoExpr>) -> MonoExpr {
        MonoExpr::Match {
            scrutinee: Box::new(scrutinee),
            compiler_generated: false,
            arms: bodies
                .into_iter()
                .map(|body| MonoMatchArm {
                    pattern: Pattern::Var { name: Symbol::from("x"), span: Span::SYNTHETIC },
                    body,
                    span: Span::SYNTHETIC,
                    provenance: None,
                    resolved_ctor: None,
                })
                .collect(),
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
        }
    }

    fn let_of(body: MonoExpr) -> MonoExpr {
        MonoExpr::Let {
            bindings: vec![(Symbol::from("s"), var("t"))],
            body: Box::new(body),
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
        }
    }

    /// Ctor probe: `user/Gr` is a constructor, nothing else is.
    fn is_ctor(f: &FQSymbol) -> bool {
        f.symbol.as_ref() == "Gr"
    }

    // ---- 1. item-26 fresh-construction ------------------------------------

    // spec: design/backend/s115-carrier-and-rc-sweep.md §2.1 / FIXME 0696 — a
    // freshly-constructed return needs no protect, in ANY function.
    #[test]
    fn constr_adt_and_ctor_apply_are_fresh() {
        assert!(is_fresh_construction(&ctor_adt(), &is_ctor));
        assert!(is_fresh_construction(
            &apply(global_var("user", "Gr"), vec![var("c")]),
            &is_ctor
        ));
    }

    // spec: §2.1 fence — the general G2/item-26 protect MUST NOT weaken: a plain
    // user/trait `Apply` may return an ALIASED argument (`(id x)`), and a bare
    // `Var` return IS a scope binding. Both keep their protect.
    #[test]
    fn general_apply_and_var_returns_are_not_fresh_neg() {
        assert!(!is_fresh_construction(
            &apply(global_var("user", "id"), vec![var("x")]),
            &is_ctor
        ));
        assert!(!is_fresh_construction(&var("v"), &is_ctor));
        // A LOCAL-resolved callee (a closure value) is never a ctor.
        assert!(!is_fresh_construction(&apply(var("f"), vec![]), &is_ctor));
    }

    // spec: §2.1 — `let` forwards freshness, so the suppression is scale-invariant
    // in heap-let depth (the R-3 fixed-residual signature).
    #[test]
    fn let_forwards_freshness_both_ways() {
        assert!(is_fresh_construction(&let_of(ctor_adt()), &is_ctor));
        assert!(is_fresh_construction(&let_of(let_of(ctor_adt())), &is_ctor));
        assert!(!is_fresh_construction(&let_of(var("v")), &is_ctor));
    }

    // spec: §2.2 (FIXME 0720 toggle-OFF half) — a control-flow JOIN is fresh iff
    // EVERY arm is fresh. This is the `set0` shape
    // `(match g [(Gr cells) (Gr (vec-set cells 0 m))])`; without it the protect
    // inc left every loop-carried box at rc≥2 and the TCO flush never reached 0.
    #[test]
    fn control_flow_join_is_fresh_iff_every_arm_is() {
        assert!(is_fresh_construction(
            &match_of(var("g"), vec![ctor_adt()]),
            &is_ctor
        ));
        assert!(is_fresh_construction(
            &match_of(var("g"), vec![ctor_adt(), ctor_adt()]),
            &is_ctor
        ));
        let if_fresh = MonoExpr::If {
            cond: Box::new(var("c")),
            then_branch: Box::new(ctor_adt()),
            else_branch: Box::new(ctor_adt()),
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
        };
        assert!(is_fresh_construction(&if_fresh, &is_ctor));
    }

    // spec: §2.1 fence (NEGATIVE, the load-bearing half) — ONE non-fresh arm makes
    // the join non-fresh and the protect STANDS. Without this the join rule would
    // be an under-count: an arm returning a scope binding would lose the inc that
    // keeps it alive past scope cleanup (the UAF direction).
    #[test]
    fn one_non_fresh_arm_makes_the_join_non_fresh_neg() {
        assert!(!is_fresh_construction(
            &match_of(var("g"), vec![ctor_adt(), var("v")]),
            &is_ctor
        ));
        assert!(!is_fresh_construction(
            &match_of(var("g"), vec![var("v"), ctor_adt()]),
            &is_ctor
        ));
        let if_mixed = MonoExpr::If {
            cond: Box::new(var("c")),
            then_branch: Box::new(ctor_adt()),
            else_branch: Box::new(var("v")),
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
        };
        assert!(!is_fresh_construction(&if_mixed, &is_ctor));
        // An arm-less match yields no value that could be fresh.
        assert!(!is_fresh_construction(&match_of(var("g"), vec![]), &is_ctor));
    }

    // ---- 1b. the box-MINTING node kinds (FIXME 0749) -----------------------

    /// An `Apply` carrying the `AutoCurry` resolution — `compile_auto_curry`
    /// unconditionally `emit_alloc`s a fresh curry env for every arm.
    fn auto_curry_apply(callee: MonoExpr) -> MonoExpr {
        let MonoExpr::Apply { callee, args, span, dispatch, ty, .. } = apply(callee, vec![])
        else {
            unreachable!()
        };
        MonoExpr::Apply {
            callee,
            args,
            span,
            resolved_call: Some(Box::new(cranelisp_types::ResolvedCall::AutoCurry {
                target_name: Symbol::from("g"),
                applied_count: 1,
                total_count: 2,
                trait_resolution: None,
            })),
            dispatch,
            ty,
            escapes: None,
            confined: None,
            unique_static: None,
            provenance: None,
        }
    }

    fn lambda() -> MonoExpr {
        MonoExpr::Lambda {
            params: vec![],
            body: Box::new(var("x")),
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
            escapes: None,
            confined: None,
            unique_static: None,
        }
    }

    fn string_lit() -> MonoExpr {
        MonoExpr::StringLit {
            value: "hi".to_string(),
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
            escapes: None,
            confined: None,
            unique_static: None,
        }
    }

    fn vec_lit() -> MonoExpr {
        MonoExpr::VecLit {
            elements: vec![],
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
            escapes: None,
            confined: None,
            unique_static: None,
        }
    }

    // spec: design/backend/s115-carrier-and-rc-sweep.md §2.1 / FIXME 0749 — the
    // freshness predicate covers EVERY box-minting node kind, not just the two
    // constructor shapes. `Lambda`/`StringLit` were recognised only by an
    // ad-hoc `matches!` at the ONE call site, so they were fresh at depth 0 and
    // NOT fresh through a `let`; `VecLit` and the auto-curry `Apply` were not
    // recognised at all. Each mints a brand-new box that cannot alias a scope
    // binding, so each needs no return-protect.
    #[test]
    fn every_box_minting_node_kind_is_fresh() {
        assert!(is_fresh_construction(&lambda(), &is_ctor));
        assert!(is_fresh_construction(&string_lit(), &is_ctor));
        assert!(is_fresh_construction(&vec_lit(), &is_ctor));
        assert!(is_fresh_construction(&auto_curry_apply(var("g")), &is_ctor));
    }

    // spec: §2.1 / FIXME 0749 — the SCALE-INVARIANCE half: a minted box returned
    // through binding indirection is still fresh. This is the measured leak —
    // `(defn mk [] (let [g (fn [a b] …)] (g 1)))` returned a curry env carrying
    // an unbalanceable protect inc, so neither it nor its captured target was
    // ever freed (allocs=201 deallocs=1 over 100 iterations); the plain-lambda
    // twin leaked identically at TWO `let`s of depth.
    #[test]
    fn minted_boxes_forward_freshness_through_binding_indirection() {
        assert!(is_fresh_construction(&let_of(auto_curry_apply(var("g"))), &is_ctor));
        assert!(is_fresh_construction(&let_of(let_of(lambda())), &is_ctor));
        assert!(is_fresh_construction(&let_of(let_of(string_lit())), &is_ctor));
        assert!(is_fresh_construction(&let_of(vec_lit()), &is_ctor));
        assert!(is_fresh_construction(
            &match_of(var("g"), vec![lambda(), auto_curry_apply(var("h"))]),
            &is_ctor
        ));
    }

    // spec: §2.1 fence (NEGATIVE) — the widening keys on the RESOLUTION CARRIER
    // (`ResolvedCall::AutoCurry`), never on the callee's shape or spelling. A
    // full application through the same local-closure callee mints nothing of
    // its own and may return an aliased argument, so it keeps its protect.
    #[test]
    fn a_non_curry_apply_through_the_same_callee_is_not_fresh_neg() {
        assert!(!is_fresh_construction(&apply(var("g"), vec![var("x")]), &is_ctor));
        assert!(!is_fresh_construction(&let_of(apply(var("g"), vec![])), &is_ctor));
        // ...and one non-minting arm still poisons the join.
        assert!(!is_fresh_construction(
            &match_of(var("g"), vec![lambda(), var("v")]),
            &is_ctor
        ));
    }

    // ---- 2. TCO borrowed-param promotion trigger ---------------------------

    // spec: design/backend/s115-carrier-and-rc-sweep.md §2.2 (FIXME 0720) — a bare
    // `Var` of the SAME param CARRIES the slot forward (the `transfer_skip` move
    // contract): nothing is superseded, nothing is owed.
    #[test]
    fn bare_same_var_arg_does_not_supersede_neg() {
        assert!(!tail_arg_supersedes_param(&var("g"), &Symbol::from("g")));
    }

    // spec: §2.2 — every other argument REPLACES the slot's occupant, so the old
    // occupant's reference is the one that leaked: a temporary, a different
    // binding, a control-flow join.
    #[test]
    fn temporary_other_binding_and_join_args_supersede() {
        let g = Symbol::from("g");
        assert!(tail_arg_supersedes_param(
            &apply(global_var("user", "set0"), vec![var("g"), var("m")]),
            &g
        ));
        assert!(tail_arg_supersedes_param(&var("w"), &g));
        assert!(tail_arg_supersedes_param(&ctor_adt(), &g));
        assert!(tail_arg_supersedes_param(&match_of(var("g"), vec![ctor_adt()]), &g));
    }

    // spec: §2.2 — the promotion TRIGGER: the exact 0720 body
    // `(if (eq-i64 m 0) … (go (set0 g m) (add-i64 m -1)))` supersedes slot 0 and
    // carries slot 1's scalar. Position-exact.
    #[test]
    fn self_call_supersede_detection_is_position_exact() {
        let module = ModuleFullPath::from("user");
        let go = Symbol::from("go");
        let body = MonoExpr::If {
            cond: Box::new(var("c")),
            then_branch: Box::new(var("r")),
            else_branch: Box::new(apply(
                var("go"),
                vec![
                    apply(global_var("user", "set0"), vec![var("g"), var("m")]),
                    var("m"),
                ],
            )),
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
        };
        assert!(self_call_supersedes_param(&body, &go, &module, 0, &Symbol::from("g")));
        assert!(!self_call_supersedes_param(&body, &go, &module, 1, &Symbol::from("m")));
    }

    // spec: §2.2 (NEGATIVE / byte-identical fence) — a body with NO self-call, and
    // a self-call that only CARRIES its params forward, promote nothing. This is
    // what keeps every non-TCO function and the `(go v (- n 1))` shape emission-
    // identical: no entry inc, no changed flush.
    #[test]
    fn no_self_call_or_carry_only_call_promotes_nothing_neg() {
        let module = ModuleFullPath::from("user");
        let go = Symbol::from("go");
        let v = Symbol::from("v");
        let no_self_call = apply(global_var("user", "other"), vec![var("v")]);
        assert!(!self_call_supersedes_param(&no_self_call, &go, &module, 0, &v));
        let carry_only = apply(var("go"), vec![var("v"), apply(global_var("user", "dec"), vec![var("n")])]);
        assert!(!self_call_supersedes_param(&carry_only, &go, &module, 0, &v));
        // ...and the SECOND position of that same call IS superseded (the walk
        // reaches nested calls, so the detection is not accidentally position-blind).
        assert!(self_call_supersedes_param(&carry_only, &go, &module, 1, &Symbol::from("n")));
    }
}

#[cfg(test)]
mod cow_retain_reconciliation_tests {
    //! FIXME 0693 / 0751 — the record-vs-derivation reconciliation at the R3
    //! COW dec-side seam ([`reconcile_cow_retain_verdict`]).
    //!
    //! Sibling of `vec_codegen/cow_gate_tests.rs`, which pins the two PURE
    //! predicates the producer and consumer share; this module pins what the
    //! consumer does with the producer's span-keyed RECORD on top of them.
    //!
    //! The load-bearing cell is the DISAGREEMENT arm. It resolved to the
    //! recorded verdict (rustdoc: "degrades to the producer's truth"), which is
    //! only true when the record belongs to the same site — and disagreement is
    //! exactly the state in which the seam cannot know that. A recorded `true`
    //! with a derived `false` then fired a dec with no producer inc behind it —
    //! the spurious-dec/UAF channel 0693 was opened to close, and the polarity
    //! the sibling ambiguity arm already had right.

    use super::reconcile_cow_retain_verdict;
    use cranelisp_types::Span;

    // spec: design/backend/ownership-codegen.md §13.7 — agreement is a pass-through
    // in BOTH polarities (the byte-identical fence: the overwhelmingly common
    // case must be untouched by the 0751 correction).
    #[test]
    fn agreement_passes_the_verdict_through() {
        assert!(reconcile_cow_retain_verdict(Some(Some(true)), true, Span::SYNTHETIC));
        assert!(!reconcile_cow_retain_verdict(Some(Some(false)), false, Span::SYNTHETIC));
    }

    // spec: §13.7 — an ambiguous span (two COW sites collapsed under one
    // synthetic span) takes the leak-safe verdict.
    #[test]
    fn ambiguous_record_is_leak_safe() {
        assert!(!reconcile_cow_retain_verdict(Some(None), true, Span::SYNTHETIC));
        assert!(!reconcile_cow_retain_verdict(Some(None), false, Span::SYNTHETIC));
    }

    // spec: §13.7 — an ABSENT record means the producer ran in another compiler
    // frame; the shared predicate is then the answer, in both polarities.
    #[test]
    fn absent_record_falls_back_to_the_shared_predicate() {
        assert!(reconcile_cow_retain_verdict(None, true, Span::SYNTHETIC));
        assert!(!reconcile_cow_retain_verdict(None, false, Span::SYNTHETIC));
    }

    // spec: §13.7 / FIXME 0751 — DEBUG builds keep the loud fence: a
    // producer/consumer disagreement is a compiler-invariant breach and must be
    // impossible to miss in development.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "disagreement fence")]
    fn disagreement_trips_the_debug_fence() {
        let _ = reconcile_cow_retain_verdict(Some(Some(true)), false, Span::SYNTHETIC);
    }

    // spec: §13.7 / FIXME 0751 — RELEASE builds take the LEAK-SAFE verdict, not
    // the record. The record belongs to a DIFFERENT site (that is what
    // disagreement means), so trusting it emits a dec with no inc behind it.
    // Both directions of the disagreement resolve to `false`.
    #[cfg(not(debug_assertions))]
    #[test]
    fn disagreement_takes_the_leak_safe_verdict_in_release_neg() {
        assert!(!reconcile_cow_retain_verdict(Some(Some(true)), false, Span::SYNTHETIC));
        assert!(!reconcile_cow_retain_verdict(Some(Some(false)), true, Span::SYNTHETIC));
    }
}
