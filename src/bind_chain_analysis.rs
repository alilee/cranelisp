//! Bind chain independence analysis: transforms `bind!`-expanded nested
//! bind/lambda forms into `Expr::ParBind` nodes for automatic IO scheduling.
//!
//! This pass runs after macro expansion and AST building, before typechecking.
//! It reads each callee's scheduling class directly from the symbol-table
//! entry (Sprint 57 Wave 3 G8 — `PlatformRegistry` was deleted and
//! `scheduling_class` moved into `PrimitiveKind::PlatformEffect`).
//!
//! Algorithm (per design/int/bind-chain-analysis.md):
//! 1. Detect the `bind` chain pattern: `Apply(Var("bind"), [io_expr, Lambda([name], body)])`.
//! 2. Collect the flat list of `(name, io_expr)` steps plus the final body.
//! 3. Classify each step's scheduling class via the symbol tables.
//! 4. Group data-independent, non-Sequential steps into `ParBind` nodes.
//! 5. Rebuild the nested expression from the grouped segments.

use std::collections::HashSet;

use cranelisp_platform::SchedulingClass;
use cranelisp_types::{
    CodeStore, DefKind, Defn, Expr, LinkerStore, MatchArm, ModuleEntry, ModuleFullPath, Span,
    Symbol, SymbolTable, TypeExpr, free_vars_expr,
};

/// Per-module symbol tables used for scheduling-class lookup.
///
/// After Sprint 57 Wave 3 G8 `bind_chain_analysis` walks the symbol tables
/// directly — following `ModuleEntry::Import` chains to the defining
/// `ModuleEntry::Def` and destructuring `DefKind::Primitive {
/// primitive_kind: PrimitiveKind::PlatformEffect { scheduling_class }, .. }`
/// to get the class. This replaces the previous `PlatformRegistry` side map.
///
/// Generic over the symbol table's store params (`C`, `L`) so the pass can run
/// against the session's live `SymbolTable<Code, ()>` directly (S85, FIXME 0367
/// — `apply_bind_chain_analysis` call site). The pass reads only `C`-independent
/// fields (`DefKind::PlatformEffect { scheduling_class }` and
/// `ModuleEntry::Import { source }`), so genericizing imposes no behavioural
/// change — the body never touches `Code`.
pub type SymbolTables<C = (), L = ()> = dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Transform bind chains in a function body into `ParBind` nodes where safe.
///
/// Takes ownership of the body via `std::mem::replace` with a dummy expression,
/// transforms it, and puts the result back. The dummy is never observed.
pub fn auto_schedule_defn<C: CodeStore, L: LinkerStore>(
    defn: &mut Defn,
    symbol_tables: &SymbolTables<C, L>,
    current_module: &ModuleFullPath,
) {
    // Single-sig only (multi-sig functions are not auto-scheduled). This is a
    // caller-defended invariant: `apply_bind_chain_analysis`'s multi-sig guard
    // guarantees this function is never reached for a multi-sig defn — so a
    // violation is a programmer logic bug, never user input (src/CLAUDE.md
    // §Error Handling — `unreachable!`, never `panic!`/`assert!` on user input).
    if defn.is_multi_sig() {
        unreachable!("invariant: auto_schedule_defn called on multi-sig defn");
    }
    let body = std::mem::replace(
        &mut defn.variants[0].body,
        Expr::BoolLit { value: false, span: defn.span, inferred_type: None },
    );
    defn.variants[0].body = transform_expr(body, symbol_tables, current_module);
}

/// Transform bind chains in a standalone expression (REPL eval path).
///
/// Sprint 67 hack-back: REPL eval-expression path currently does not invoke
/// auto-scheduling (only `auto_schedule_defn` runs in `session.rs`). Retained
/// for future activation; narrowed + `#[allow(dead_code)]`.
#[allow(dead_code)]
pub(crate) fn auto_schedule_expr<C: CodeStore, L: LinkerStore>(
    expr: &mut Expr,
    symbol_tables: &SymbolTables<C, L>,
    current_module: &ModuleFullPath,
) {
    let owned = std::mem::replace(
        expr,
        Expr::BoolLit { value: false, span: Span::SYNTHETIC, inferred_type: None },
    );
    *expr = transform_expr(owned, symbol_tables, current_module);
}

/// Transform bind chains in an owned expression (for DefnVariant bodies).
///
/// Sprint 67 hack-back: no current consumer. Retained as a primitive; narrowed
/// + `#[allow(dead_code)]`.
#[allow(dead_code)]
pub(crate) fn auto_schedule_expr_owned<C: CodeStore, L: LinkerStore>(
    expr: Expr,
    symbol_tables: &SymbolTables<C, L>,
    current_module: &ModuleFullPath,
) -> Expr {
    transform_expr(expr, symbol_tables, current_module)
}

// ---------------------------------------------------------------------------
// Expression transformation
// ---------------------------------------------------------------------------

/// Recursively transform an expression, optimizing bind chains into ParBind.
fn transform_expr<C: CodeStore, L: LinkerStore>(
    expr: Expr,
    symbol_tables: &SymbolTables<C, L>,
    current_module: &ModuleFullPath,
) -> Expr {
    if is_bind_chain_start(&expr) {
        let (chain, final_body) = collect_bind_chain(expr);
        rebuild_chain(chain, final_body, symbol_tables, current_module)
    } else {
        recurse_children(expr, symbol_tables, current_module)
    }
}

/// True if `expr` is `Apply(Var("bind"/"*/bind"), [io_expr, Lambda([name], body)])`.
fn is_bind_chain_start(expr: &Expr) -> bool {
    matches!(expr, Expr::Apply { callee, args, .. }
        if is_bind_var(callee)
        && args.len() == 2
        && matches!(&args[1], Expr::Lambda { params, .. } if params.len() == 1))
}

/// True if `expr` is a reference to the `bind` primitive.
fn is_bind_var(expr: &Expr) -> bool {
    match expr {
        Expr::Var { name, .. } => name.as_ref() == "bind" || name.ends_with("/bind"),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Chain collection
// ---------------------------------------------------------------------------

/// A single step in a bind chain:
/// `(bound_name, io_expr, annotation, span, bind_callee)`.
///
/// `bind_callee` is the ORIGINAL `bind` callee name as it appeared in the
/// expanded AST (e.g. `primitives/bind` — the `bind!` macro expands to a
/// qualified `primitives/bind` reference, stdlib/io/monad.cl). Sequential
/// reconstruction (`make_bind`) MUST re-emit this exact name; emitting a bare
/// `bind` would not resolve in a module that only imports `Pure`/the qualified
/// `primitives/bind` and silently breaks the chain (S85 wiring defect — the
/// sketch's `make_bind` hardcoded bare `"bind"`, valid only for its own
/// bare-`bind` expansion, not the reimpl's qualified one).
type BindStep = (Symbol, Expr, Option<TypeExpr>, Span, Symbol);

/// Collect a complete bind chain into a flat vec of steps plus the final body.
///
/// The chain must be non-empty (caller checks via `is_bind_chain_start`).
/// The `annotation` field preserves the Lambda parameter's optional type
/// annotation for round-tripping. The `bind_callee` field preserves the
/// original (possibly qualified) `bind` name so reconstruction is faithful.
fn collect_bind_chain(expr: Expr) -> (Vec<BindStep>, Expr) {
    let Expr::Apply { callee, mut args, span, .. } = expr else {
        unreachable!("invariant: collect_bind_chain called on non-bind expr")
    };

    // Preserve the original bind callee name (e.g. `primitives/bind`).
    let bind_callee = match callee.as_ref() {
        Expr::Var { name, .. } => name.clone(),
        // `is_bind_chain_start` guarantees the callee is a `Var`.
        _ => unreachable!("invariant: bind callee is not a Var"),
    };

    // args[1] is the Lambda; extract it first to avoid borrow conflicts.
    let lambda = args.remove(1);
    let io_expr = args.remove(0);

    let Expr::Lambda {
        mut params,
        body,
        ..
    } = lambda
    else {
        unreachable!("invariant: bind lambda is not a Lambda")
    };

    // S70: `param_annotations` folded into `params: Vec<(Symbol,
    // Option<TypeExpr>)>`. The per-param annotation rides on the tuple.
    let (name, annotation) = params.remove(0);
    let inner = *body;
    let binding_span = span;

    if is_bind_chain_start(&inner) {
        let (mut rest, final_body) = collect_bind_chain(inner);
        rest.insert(0, (name, io_expr, annotation, binding_span, bind_callee));
        (rest, final_body)
    } else {
        (vec![(name, io_expr, annotation, binding_span, bind_callee)], inner)
    }
}

// ---------------------------------------------------------------------------
// Scheduling classification
// ---------------------------------------------------------------------------

/// Return the `SchedulingClass` of the platform function called by `io_expr`.
///
/// Falls back to `Sequential` for anything other than a direct platform call.
/// Only direct calls to platform functions are eligible — wrapper functions
/// that call platform functions are conservatively treated as sequential.
///
/// Reads the scheduling class via symbol-table lookup (Sprint 57 Wave 3 G8):
/// resolves the callee's name in `current_module`, follows Import chains to the
/// defining `ModuleEntry::Def`, and destructures
/// `DefKind::Primitive { primitive_kind: PrimitiveKind::PlatformEffect { scheduling_class }, .. }`.
fn classify_expr<C: CodeStore, L: LinkerStore>(
    expr: &Expr,
    symbol_tables: &SymbolTables<C, L>,
    current_module: &ModuleFullPath,
) -> SchedulingClass {
    effect_descriptor(expr, symbol_tables, current_module)
        .map(|(sc, _poll_shape)| sc)
        .unwrap_or(SchedulingClass::Sequential)
}

/// The launch-relevant slice of a direct platform-effect call's descriptor:
/// `(scheduling_class, poll_shape)`. `None` for anything that is NOT a direct
/// call to a `DefKind::PlatformEffect` primitive (a user-fn wrapper, a pure
/// expression, a literal — all conservatively NON-launchable, §4.1 E3).
///
/// `poll_shape` is needed by the §4.1 E3 token-0 refusal: a poll-shape
/// `ResourceSerial` leaf carries its DYNAMIC resource token as the leading
/// operand (the `(token, capacity)` pair convention, `poll-support.md §3.4`), so
/// a literal-`0` leading operand is the shared-singleton token-0 the launch must
/// refuse. A blocking effect has no such leading-pair convention.
fn effect_descriptor<C: CodeStore, L: LinkerStore>(
    expr: &Expr,
    symbol_tables: &SymbolTables<C, L>,
    current_module: &ModuleFullPath,
) -> Option<(SchedulingClass, bool)> {
    if let Expr::Apply { callee, .. } = expr
        && let Expr::Var { name, .. } = callee.as_ref()
    {
        // Qualified name "platform.stdio/print": split module/symbol and
        // look up directly in the defining module.
        if let Some(pos) = name.rfind('/') {
            let mod_part = ModuleFullPath::from(&name[..pos]);
            let sym_part = &name[pos + 1..];
            if let Some(d) = effect_descriptor_from_table(symbol_tables, &mod_part, sym_part) {
                return Some(d);
            }
        }
        // Bare name: resolve via the current module (follows Import chains).
        if let Some(d) = effect_descriptor_from_table(symbol_tables, current_module, name.as_ref()) {
            return Some(d);
        }
    }
    None
}

/// Resolve `name` in `module` (following Import/Reexport chains) and return its
/// `(scheduling_class, poll_shape)` if the entry is a `PlatformEffect` primitive.
///
/// Returns `None` if the name is absent, resolves to a non-`PlatformEffect`
/// entry, or the Import chain does not terminate in a `Def`.
fn effect_descriptor_from_table<C: CodeStore, L: LinkerStore>(
    symbol_tables: &SymbolTables<C, L>,
    module: &ModuleFullPath,
    name: &str,
) -> Option<(SchedulingClass, bool)> {
    fn walk<C: CodeStore, L: LinkerStore>(
        tables: &SymbolTables<C, L>,
        module: &ModuleFullPath,
        name: &str,
        depth: usize,
    ) -> Option<(SchedulingClass, bool)> {
        if depth > 16 {
            return None;
        }
        let table = tables.get(module)?;
        let entry = table.get(name)?;
        match entry {
            ModuleEntry::Def { kind, .. } => {
                if let DefKind::PlatformEffect { scheduling_class, poll_shape, .. } = kind.as_ref() {
                    Some((*scheduling_class, *poll_shape))
                } else {
                    None
                }
            }
            ModuleEntry::Import { source, .. } => {
                let next_mod = source.module.clone();
                let next_sym: String = source.symbol.as_ref().to_string();
                drop(table);
                walk(tables, &next_mod, &next_sym, depth + 1)
            }
            _ => None,
        }
    }
    walk(symbol_tables, module, name, 0)
}

/// True if none of the names in `bound_names` appear free in `expr`.
fn is_independent(expr: &Expr, bound_names: &HashSet<Symbol>) -> bool {
    if bound_names.is_empty() {
        return true;
    }
    let globals = HashSet::new();
    free_vars_expr(expr, &globals).is_disjoint(bound_names)
}

// ---------------------------------------------------------------------------
// Launch-and-continue eligibility — the E1/E2/E3 predicate
// (design/arch/effect-concurrency.md §4.1; spec/10-io.md §10.12.7)
// ---------------------------------------------------------------------------

/// The launch-eligibility predicate (§4.1). A bind step `(bind io_expr (fn [name]
/// continuation))` whose `io_expr` is either a single platform effect OR a whole
/// discarded **bind sub-tree** may be lowered as a detached supervised strand
/// (`Expr::LaunchContinue`) instead of an ordinary `Bind` iff ALL of:
///
/// - **(E1) Result-discarded** — `name` is unused in `continuation`
///   (`!free_vars(continuation).contains(name)`): no one awaits the launched
///   value, so detaching does not change the program's value (§10.12.7 step 1).
/// - **(E2) Value-locality** — the launched effect's resource value must not flow
///   into a same-token continuation effect. A fresh, non-shared value (the
///   `accept`-minted `conn`) yields a fresh, disjoint token by construction (§4
///   fact 2). This is the load-bearing disjointness *witness*: token VALUES are
///   dynamic/runtime (§5/§8.1), so disjointness is derived from value provenance,
///   not token comparison. **Sub-tree arm:** plain free-var disjointness
///   (`free_vars(sub-tree) ∩ free_vars(cont) == ∅`) — sound because the sub-tree
///   binds its resource internally, so a shared free var IS an external handle. A
///   module-global pool handle appears as a shared free var ⇒ refused.
///   **Single-step arm (FIXME 0478):** a NARROWER handle-locality check
///   (`continuation_shares_resource_handle`) — refuse iff the launched leaf's
///   resource HANDLE (its leading token operand) flows into a `ResourceSerial`
///   effect in the continuation. Plain disjointness would over-refuse the §B4
///   launch LOOP, whose counter var is shared with the continuation as a pure
///   *value* (a loop index passed to `recur`), not a same-token continuation
///   effect; the handle-locality check permits that while still refusing the
///   reorder-unsound `(send-conn conn r1)`→`(send-conn conn r2)` shape.
/// - **(E3) No shared-singleton-token effect** — every effect position in the
///   launched expression must be a `ResourceSerial` per-value-minted-token leaf,
///   never `Commutative` (token-0, unrestricted) nor `Sequential` (the global
///   token-1), and (for poll-shape leaves) never a literal-`0` leading token
///   operand (the dynamic shared singleton). An **opaque user-fn** in an effect
///   position is an unknown footprint and is likewise refused — which is why the
///   handler must be inlined to platform leaves for the launch to fire. **Timer
///   refinement:** a resource-free `sleep` timer leaf (`is_sleep_timer_leaf`) is
///   ALSO permitted as a sub-tree effect position — it carries no shared token and
///   no observable side-effect stream, so it reorders nothing observable when
///   detached as a sub-tree member (it is NOT independently launch-shaped; the
///   single-step arm below still refuses it).
///
/// Declining to detach is ALWAYS sound (§10.12.7), so every failure path lowers
/// as an ordinary `Bind`.
fn launch_eligible<C: CodeStore, L: LinkerStore>(
    name: &Symbol,
    io_expr: &Expr,
    continuation: &Expr,
    symbol_tables: &SymbolTables<C, L>,
    current_module: &ModuleFullPath,
) -> bool {
    let globals: HashSet<Symbol> = HashSet::new();

    // (E1) Result-discarded — the launched binder is unused in the continuation.
    if free_vars_expr(continuation, &globals).contains(name) {
        return false;
    }

    if is_bind_chain_start(io_expr) {
        // SUB-TREE case (the S96 C-fanout extension): walk every effect position
        // of the already-collected local bind sub-tree (Principle 7 — no
        // interprocedural analysis; the handler is inlined down to platform
        // leaves so the footprint is purely local).
        for effect in subtree_effect_positions(io_expr) {
            // A `ResourceSerial` per-value-minted-token leaf (E3) OR the
            // resource-free `sleep` timer leaf (the §4.1 timer-leaf refinement —
            // see `is_sleep_timer_leaf`). A timer touches no shared resource and
            // produces no observable side-effect stream, so it is sound to carry
            // INSIDE a launched sub-tree (it is NOT independently launch-shaped —
            // the single-step arm below still refuses it).
            if !is_launchable_leaf(effect, symbol_tables, current_module)
                && !is_sleep_timer_leaf(effect, symbol_tables, current_module)
            {
                return false; // (E3) — non-ResourceSerial / token-0 / opaque.
            }
        }
        // (E2) Value-locality witness: no free variable shared with the
        // continuation (a fresh, non-shared value ⇒ a disjoint token).
        let s_free = free_vars_expr(io_expr, &globals);
        let c_free = free_vars_expr(continuation, &globals);
        s_free.is_disjoint(&c_free)
    } else {
        // SINGLE-STEP case: E3 (`is_launchable_leaf` — ResourceSerial only, refuse
        // Commutative/Sequential/token-0/opaque) + E2 (value-locality, FIXME 0478).
        //
        // E2 for a single leaf is NARROWER than the sub-tree arm's plain free-var
        // disjointness (`s_free.is_disjoint(&c_free)` above). Plain disjointness is
        // sound for a sub-tree because the sub-tree binds its resource internally,
        // so its residual free vars ARE external handles. A bare leaf's free vars
        // include its per-call dynamic-token operand, which the legitimate §B4
        // launch LOOP legitimately shares with the continuation as a pure VALUE (a
        // loop index passed to `recur`, NOT a same-token continuation effect) — so
        // plain disjointness would wrongly refuse it. E2 here refuses ONLY the
        // reorder-unsound shape §3.7 names: the launched leaf's resource HANDLE (its
        // leading token operand, when a `Var`) flowing into a same-token
        // `ResourceSerial` effect in the continuation (e.g. a discarded
        // `(send-conn conn r1)` whose continuation does `(send-conn conn r2)` —
        // same handle ⇒ same dynamic token ⇒ detaching reorders). The counter loop
        // `(rd n c f)` → `(recur (sub n))` shares `n` as a value only (no cont
        // `ResourceSerial` effect uses `n` as its handle) ⇒ E2 passes, unchanged.
        is_launchable_leaf(io_expr, symbol_tables, current_module)
            && !continuation_shares_resource_handle(
                io_expr,
                continuation,
                symbol_tables,
                current_module,
            )
    }
}

/// (E2 single-step, FIXME 0478 / §3.7) True iff the launched leaf's resource HANDLE
/// — its leading token operand, when a `Var` — flows into a `ResourceSerial` effect
/// position in `continuation` as THAT effect's leading operand. Such a shared handle
/// is the same per-value dynamic token, so detaching the launched step would reorder
/// two same-token effects across the launch boundary — the E2 value-locality refusal.
///
/// This witnesses token-locality WITHOUT resolving concrete tokens (they are
/// runtime/dynamic, §5/§8.1): the refusal keys on the handle *var*, not a token
/// comparison. A leaf with a non-`Var` leading operand (a literal token) shares no
/// handle to reorder ⇒ vacuously value-local (`false`).
fn continuation_shares_resource_handle<C: CodeStore, L: LinkerStore>(
    io_expr: &Expr,
    continuation: &Expr,
    symbol_tables: &SymbolTables<C, L>,
    current_module: &ModuleFullPath,
) -> bool {
    let Some(handle) = leading_operand_var(io_expr) else {
        return false; // no `Var` handle ⇒ nothing to reorder.
    };
    let mut shared = false;
    visit_exprs(continuation, &mut |e| {
        if shared {
            return;
        }
        // A direct `ResourceSerial` platform effect in the continuation whose OWN
        // leading operand is the same handle ⇒ same dynamic token ⇒ reorder.
        if let Some((SchedulingClass::ResourceSerial, _)) =
            effect_descriptor(e, symbol_tables, current_module)
            && leading_operand_var(e).as_ref() == Some(&handle)
        {
            shared = true;
        }
    });
    shared
}

/// The leading operand of an `Apply`, when it is a `Var` — the resource handle /
/// dynamic-token operand of a poll-shape `(token, capacity, …)` leaf.
fn leading_operand_var(effect: &Expr) -> Option<Symbol> {
    match effect {
        Expr::Apply { args, .. } => match args.first() {
            Some(Expr::Var { name, .. }) => Some(name.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// Visit `expr` and every sub-expression (pre-order), invoking `f` on each. A
/// complete structural walk over the `Expr` variants that can carry a nested effect
/// position — used by the single-step E2 continuation scan (FIXME 0478). Conservative
/// by construction: every child that can hold an `Apply` is descended.
fn visit_exprs(expr: &Expr, f: &mut impl FnMut(&Expr)) {
    f(expr);
    match expr {
        Expr::Apply { callee, args, .. } => {
            visit_exprs(callee, f);
            for a in args {
                visit_exprs(a, f);
            }
        }
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            for (_, rhs) in bindings {
                visit_exprs(rhs, f);
            }
            visit_exprs(body, f);
        }
        Expr::If { cond, then_branch, else_branch, .. } => {
            visit_exprs(cond, f);
            visit_exprs(then_branch, f);
            visit_exprs(else_branch, f);
        }
        Expr::Lambda { body, .. } | Expr::Trace { body, .. } => visit_exprs(body, f),
        Expr::Match { scrutinee, arms, .. } => {
            visit_exprs(scrutinee, f);
            for arm in arms {
                visit_exprs(&arm.body, f);
            }
        }
        Expr::Annotate { expr, .. } => visit_exprs(expr, f),
        Expr::VecLit { elements, .. } => {
            for e in elements {
                visit_exprs(e, f);
            }
        }
        Expr::ConstrADT { fields, .. } => {
            for e in fields {
                visit_exprs(e, f);
            }
        }
        Expr::LaunchContinue { launched, continuation, .. } => {
            visit_exprs(launched, f);
            visit_exprs(continuation, f);
        }
        // Leaves with no nested `Expr`.
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. } => {}
    }
}

/// (E3) for a single effect position: a `ResourceSerial` per-value-minted-token
/// leaf, refusing `Commutative` (token-0) / `Sequential` (token-1) / opaque
/// user-fn / a literal-`0` dynamic token on a poll-shape leaf.
fn is_launchable_leaf<C: CodeStore, L: LinkerStore>(
    effect: &Expr,
    symbol_tables: &SymbolTables<C, L>,
    current_module: &ModuleFullPath,
) -> bool {
    match effect_descriptor(effect, symbol_tables, current_module) {
        Some((SchedulingClass::ResourceSerial, poll_shape)) => {
            // The token-0 refusal: a poll-shape leaf's DYNAMIC token is the
            // leading operand; a literal `0` is the shared singleton (token-0).
            !(poll_shape && leading_token_is_zero(effect))
        }
        // Commutative (token-0), Sequential (token-1), or not a direct platform
        // effect (opaque user fn / pure expression) → refuse.
        _ => false,
    }
}

/// True if `effect` is a direct call to the `sleep` timer primitive (a
/// `DefKind::PrimitiveExtern` whose terminal symbol is `sleep`), resolved through
/// the import chain.
///
/// The timer is a per-call, **resource-free** delay leaf (`bootstrap.rs` —
/// `(Fn [Int] (IO Int))`, the reactor armed-timer `runtime/sleep_pollfn`): it
/// carries **no resource token** and produces **no observable side-effect stream**
/// (unlike a token-0 shared-`stdout` `print`). So, unlike the §4.1 E3 refusal of
/// `Commutative`/`Sequential` shared-singleton-token effects (whose detachment
/// REORDERS an observable same-token stream), detaching a timer **as a member of a
/// larger launched sub-tree** reorders nothing observable — it is sound. This is
/// the §4.1 *timer-leaf refinement* of E3: the inlined connection handler legally
/// contains a `(sleep d)` delay step and the whole handler still launches.
///
/// It is deliberately **NOT** accepted by the single-step launch arm
/// (`launch_eligible`'s `else` branch keeps using `is_launchable_leaf`): a *lone*
/// detached `sleep` is pointless, and detaching a `sleep` that the continuation's
/// effect relies on (e.g. `(bind (sleep d) (fn [_] (send …)))`) would let the
/// continuation run BEFORE the delay — defeating a delay the program wrote on
/// purpose. So the timer is launch-eligible only as a sub-tree *member*, never as
/// the launched root.
fn is_sleep_timer_leaf<C: CodeStore, L: LinkerStore>(
    effect: &Expr,
    symbol_tables: &SymbolTables<C, L>,
    current_module: &ModuleFullPath,
) -> bool {
    let Expr::Apply { callee, .. } = effect else {
        return false;
    };
    let Expr::Var { name, .. } = callee.as_ref() else {
        return false;
    };
    // Qualified form: resolve in the named module directly.
    if let Some(pos) = name.rfind('/') {
        let mod_part = ModuleFullPath::from(&name[..pos]);
        if resolves_to_sleep_extern(symbol_tables, &mod_part, &name[pos + 1..], 0) {
            return true;
        }
    }
    // Bare form: resolve via the current module (follows Import chains).
    resolves_to_sleep_extern(symbol_tables, current_module, name.as_ref(), 0)
}

/// Resolve `name` in `module` (following Import chains) and return `true` iff it
/// terminates in a `DefKind::PrimitiveExtern` whose terminal symbol is `sleep`.
fn resolves_to_sleep_extern<C: CodeStore, L: LinkerStore>(
    symbol_tables: &SymbolTables<C, L>,
    module: &ModuleFullPath,
    name: &str,
    depth: usize,
) -> bool {
    if depth > 16 {
        return false;
    }
    let Some(table) = symbol_tables.get(module) else {
        return false;
    };
    let Some(entry) = table.get(name) else {
        return false;
    };
    match entry {
        ModuleEntry::Def { kind, .. } => {
            matches!(kind.as_ref(), DefKind::PrimitiveExtern) && name == "sleep"
        }
        ModuleEntry::Import { source, .. } => {
            let next_mod = source.module.clone();
            let next_sym: String = source.symbol.as_ref().to_string();
            drop(table);
            resolves_to_sleep_extern(symbol_tables, &next_mod, &next_sym, depth + 1)
        }
        _ => false,
    }
}

/// True if `effect` is an `Apply` whose first argument is a literal `0` — the
/// token-0 shared-singleton dynamic token of a poll-shape `(token, capacity, …)`
/// leaf (§4.1 E3 / `poll-support.md §3.4`).
fn leading_token_is_zero(effect: &Expr) -> bool {
    matches!(effect, Expr::Apply { args, .. }
        if matches!(args.first(), Some(Expr::IntLit { value: 0, .. })))
}

/// Collect the effect positions of a launched bind sub-tree: each `bind` step's
/// `io_expr` plus the tail expression. A non-`bind` tail (a `Pure`, a literal, a
/// user-fn call) is included so `is_launchable_leaf` refuses any non-leaf tail.
/// Reference-only walk (does not consume) — `collect_bind_chain`'s consuming twin
/// is reused everywhere else; here the sub-tree must stay borrowed.
fn subtree_effect_positions(subtree: &Expr) -> Vec<&Expr> {
    let mut effects: Vec<&Expr> = Vec::new();
    let mut cursor = subtree;
    loop {
        if is_bind_chain_start(cursor)
            && let Expr::Apply { args, .. } = cursor
        {
            effects.push(&args[0]); // the step's io_expr (an effect position)
            if let Expr::Lambda { body, .. } = &args[1] {
                cursor = body;
                continue;
            }
        }
        effects.push(cursor); // the tail expression (also an effect position)
        break;
    }
    effects
}

// ---------------------------------------------------------------------------
// Chain rebuilding
// ---------------------------------------------------------------------------

/// A segment in the rebuilt chain.
enum Segment {
    /// A single sequential bind step: (name, io_expr, annotation, span, bind_callee).
    /// `io_expr` is boxed to keep the variant size balanced against `Parallel`
    /// (the `Expr` payload is large; boxing avoids a `large_enum_variant` lint).
    Sequential(Symbol, Box<Expr>, Option<TypeExpr>, Span, Symbol),
    /// A group of data-independent non-Sequential steps to run in parallel.
    Parallel(Vec<(Symbol, Expr, Span)>),
}

/// Flush the current parallel group into `segments`, updating `bound_so_far`.
///
/// - If the group has >= 2 entries: emit a `Parallel` segment.
/// - If the group has exactly 1 entry: demote to `Sequential`.
/// - If empty: no-op.
fn flush_par_group(
    segments: &mut Vec<Segment>,
    bound_so_far: &mut HashSet<Symbol>,
    group: Vec<BindStep>,
) {
    if group.is_empty() {
        return;
    }
    for (name, _, _, _, _) in &group {
        bound_so_far.insert(name.clone());
    }
    if group.len() >= 2 {
        let par_bindings: Vec<(Symbol, Expr, Span)> =
            group.into_iter().map(|(n, e, _, s, _)| (n, e, s)).collect();
        segments.push(Segment::Parallel(par_bindings));
    } else {
        let (name, io_expr, annotation, span, bind_callee) = group.into_iter().next()
            .expect("invariant: group is non-empty");
        segments.push(Segment::Sequential(name, Box::new(io_expr), annotation, span, bind_callee));
    }
}

/// Group a flat bind chain and rebuild it into an optimised nested expression.
fn rebuild_chain<C: CodeStore, L: LinkerStore>(
    chain: Vec<BindStep>,
    final_body: Expr,
    symbol_tables: &SymbolTables<C, L>,
    current_module: &ModuleFullPath,
) -> Expr {
    let mut segments: Vec<Segment> = Vec::new();
    let mut current_par: Vec<BindStep> = Vec::new();
    let mut bound_so_far: HashSet<Symbol> = HashSet::new();

    for (name, io_expr, annotation, span, bind_callee) in chain {
        let sc = classify_expr(&io_expr, symbol_tables, current_module);

        // Names already committed + names in the current parallel group.
        let mut all_bound = bound_so_far.clone();
        for (n, _, _, _, _) in &current_par {
            all_bound.insert(n.clone());
        }

        if sc != SchedulingClass::Sequential && is_independent(&io_expr, &all_bound) {
            current_par.push((name, io_expr, annotation, span, bind_callee));
        } else {
            // This entry can't join the parallel group — flush first.
            flush_par_group(
                &mut segments,
                &mut bound_so_far,
                std::mem::take(&mut current_par),
            );
            bound_so_far.insert(name.clone());
            segments.push(Segment::Sequential(name, Box::new(io_expr), annotation, span, bind_callee));
        }
    }
    // Flush any remaining parallel group.
    flush_par_group(
        &mut segments,
        &mut bound_so_far,
        std::mem::take(&mut current_par),
    );

    // Rebuild from right to left: innermost expression is the transformed final_body.
    let mut result = transform_expr(final_body, symbol_tables, current_module);
    for segment in segments.into_iter().rev() {
        result = match segment {
            Segment::Sequential(name, io_expr, annotation, span, bind_callee) => {
                let io_expr = transform_expr(*io_expr, symbol_tables, current_module);
                // Launch-and-continue eligibility (design/arch/effect-concurrency.md
                // §4.1 / spec/10-io.md §10.12.7): a bind step whose RESULT IS
                // DISCARDED and whose effects act only on per-value-minted
                // ResourceSerial tokens disjoint from the continuation may be lowered
                // as a detached supervised strand (`Expr::LaunchContinue`) rather than
                // an ordinary `Bind`. The `io_expr` is either a single platform-effect
                // step OR a whole discarded bind SUB-TREE (the inlined connection
                // handler — the C-fanout extension). `launch_eligible` applies the
                // exact E1/E2/E3 predicate; reuses the existing cores
                // (`collect`/`classify`/`free_vars`, Principle 7). CONSERVATIVE
                // DEFAULT: any step that fails E1-E3 lowers as an ordinary `Bind`
                // (declining to detach is always sound, §10.12.7).
                if launch_eligible(&name, &io_expr, &result, symbol_tables, current_module) {
                    Expr::LaunchContinue {
                        launched: Box::new(io_expr),
                        continuation: Box::new(result),
                        span,
                        inferred_type: None,
                    }
                } else {
                    make_bind(bind_callee, name, io_expr, annotation, result, span)
                }
            }
            Segment::Parallel(bindings_with_span) => {
                let span = bindings_with_span[0].2;
                let bindings: Vec<(Symbol, Expr)> = bindings_with_span
                    .into_iter()
                    .map(|(name, io_expr, _span)| {
                        (name, transform_expr(io_expr, symbol_tables, current_module))
                    })
                    .collect();
                Expr::ParBind {
                    bindings,
                    body: Box::new(result),
                    span,
                    inferred_type: None,
                }
            }
        };
    }
    result
}

/// Reconstruct a sequential `(<bind_callee> io_expr (fn [name] body))` expr.
///
/// `bind_callee` is the original (possibly qualified, e.g. `primitives/bind`)
/// callee name captured during chain collection — it MUST be re-emitted exactly
/// so the reconstructed call resolves the same way the unexpanded chain did.
fn make_bind(
    bind_callee: Symbol,
    name: Symbol,
    io_expr: Expr,
    annotation: Option<TypeExpr>,
    body: Expr,
    span: Span,
) -> Expr {
    // S70: `param_annotations` folded into `params: Vec<(Symbol,
    // Option<TypeExpr>)>` — the annotation rides on the param tuple.
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: bind_callee,
            span,
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            io_expr,
            Expr::Lambda {
                params: vec![(name, annotation)],
                body: Box::new(body),
                span,
                inferred_type: None,
            },
        ],
        span,
        resolved_call: None,
        inferred_type: None,
    }
}

// ---------------------------------------------------------------------------
// Child recursion
// ---------------------------------------------------------------------------

/// Recurse into sub-expressions without touching this node's structure.
///
/// Called for any expression that is not itself a bind chain start.
fn recurse_children<C: CodeStore, L: LinkerStore>(
    expr: Expr,
    symbol_tables: &SymbolTables<C, L>,
    current_module: &ModuleFullPath,
) -> Expr {
    match expr {
        Expr::Let { bindings, body, span, inferred_type } => Expr::Let {
            bindings: bindings
                .into_iter()
                .map(|(n, v)| (n, transform_expr(v, symbol_tables, current_module)))
                .collect(),
            body: Box::new(transform_expr(*body, symbol_tables, current_module)),
            span,
            inferred_type,
        },
        Expr::If { cond, then_branch, else_branch, span, inferred_type } => Expr::If {
            cond: Box::new(transform_expr(*cond, symbol_tables, current_module)),
            then_branch: Box::new(transform_expr(*then_branch, symbol_tables, current_module)),
            else_branch: Box::new(transform_expr(*else_branch, symbol_tables, current_module)),
            span,
            inferred_type,
        },
        Expr::Lambda { params, body, span, inferred_type } => Expr::Lambda {
            params,
            body: Box::new(transform_expr(*body, symbol_tables, current_module)),
            span,
            inferred_type,
        },
        Expr::Apply { callee, args, span, resolved_call, inferred_type } => Expr::Apply {
            callee: Box::new(transform_expr(*callee, symbol_tables, current_module)),
            args: args
                .into_iter()
                .map(|a| transform_expr(a, symbol_tables, current_module))
                .collect(),
            span,
            resolved_call,
            inferred_type,
        },
        Expr::Match { scrutinee, arms, span, compiler_generated, inferred_type } => Expr::Match {
            scrutinee: Box::new(transform_expr(*scrutinee, symbol_tables, current_module)),
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: transform_expr(arm.body, symbol_tables, current_module),
                    span: arm.span,
                })
                .collect(),
            span,
            compiler_generated,
            inferred_type,
        },
        Expr::VecLit { elements, span, inferred_type } => Expr::VecLit {
            elements: elements
                .into_iter()
                .map(|e| transform_expr(e, symbol_tables, current_module))
                .collect(),
            span,
            inferred_type,
        },
        Expr::Annotate { annotation, expr, span, inferred_type } => Expr::Annotate {
            annotation,
            expr: Box::new(transform_expr(*expr, symbol_tables, current_module)),
            span,
            inferred_type,
        },
        Expr::ParBind { bindings, body, span, inferred_type } => Expr::ParBind {
            bindings: bindings
                .into_iter()
                .map(|(n, v)| (n, transform_expr(v, symbol_tables, current_module)))
                .collect(),
            body: Box::new(transform_expr(*body, symbol_tables, current_module)),
            span,
            inferred_type,
        },
        Expr::Trace { modules, body, span, inferred_type } => Expr::Trace {
            modules,
            body: Box::new(transform_expr(*body, symbol_tables, current_module)),
            span,
            inferred_type,
        },
        // Idempotency (§5.2): a pre-existing `LaunchContinue` (from a prior pass, or
        // built by a future caller) recurses its children without re-grouping —
        // exactly like the `ParBind` arm above.
        Expr::LaunchContinue { launched, continuation, span, inferred_type } => Expr::LaunchContinue {
            launched: Box::new(transform_expr(*launched, symbol_tables, current_module)),
            continuation: Box::new(transform_expr(*continuation, symbol_tables, current_module)),
            span,
            inferred_type,
        },
        Expr::ConstrADT { type_name, tag, fields, span, inferred_type } => Expr::ConstrADT {
            type_name,
            tag,
            fields: fields
                .into_iter()
                .map(|f| transform_expr(f, symbol_tables, current_module))
                .collect(),
            span,
            inferred_type,
        },
        // Leaf nodes.
        leaf @ (Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. }) => leaf,
    }
}

// ---------------------------------------------------------------------------
// Scheduling lookup (symbol-table path)
// ---------------------------------------------------------------------------

/// Look up the scheduling class for a platform function name.
///
/// Accepts either a qualified form (`platform.stdio/print`) or a bare name
/// that resolves via the current module's imports. Returns `Sequential` when
/// the name does not resolve to a `PlatformEffect` primitive.
///
/// Sprint 67 hack-back: no current external consumer (used only by tests in
/// this module). Narrowed + `#[allow(dead_code)]`.
#[allow(dead_code)]
pub(crate) fn scheduling_of<C: CodeStore, L: LinkerStore>(
    symbol_tables: &SymbolTables<C, L>,
    current_module: &ModuleFullPath,
    name: &str,
) -> SchedulingClass {
    if let Some(pos) = name.rfind('/') {
        let mod_part = ModuleFullPath::from(&name[..pos]);
        let sym_part = &name[pos + 1..];
        if let Some((sc, _)) = effect_descriptor_from_table(symbol_tables, &mod_part, sym_part) {
            return sc;
        }
    }
    effect_descriptor_from_table(symbol_tables, current_module, name)
        .map(|(sc, _)| sc)
        .unwrap_or(SchedulingClass::Sequential)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
