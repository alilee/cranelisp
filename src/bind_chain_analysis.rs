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
    if let Expr::Apply { callee, .. } = expr
        && let Expr::Var { name, .. } = callee.as_ref()
    {
        // Qualified name "platform.stdio/print": split module/symbol and
        // look up directly in the defining module.
        if let Some(pos) = name.rfind('/') {
            let mod_part = ModuleFullPath::from(&name[..pos]);
            let sym_part = &name[pos + 1..];
            if let Some(sc) = scheduling_class_from_table(symbol_tables, &mod_part, sym_part) {
                return sc;
            }
        }
        // Bare name: resolve via the current module (follows Import chains).
        if let Some(sc) = scheduling_class_from_table(symbol_tables, current_module, name.as_ref())
        {
            return sc;
        }
    }
    SchedulingClass::Sequential
}

/// Resolve `name` in `module` (following Import/Reexport chains) and return
/// its scheduling class if the entry is a `PlatformEffect` primitive.
///
/// Returns `None` if the name is absent, resolves to a non-`PlatformEffect`
/// entry, or the Import chain does not terminate in a `Def`.
fn scheduling_class_from_table<C: CodeStore, L: LinkerStore>(
    symbol_tables: &SymbolTables<C, L>,
    module: &ModuleFullPath,
    name: &str,
) -> Option<SchedulingClass> {
    fn walk<C: CodeStore, L: LinkerStore>(
        tables: &SymbolTables<C, L>,
        module: &ModuleFullPath,
        name: &str,
        depth: usize,
    ) -> Option<SchedulingClass> {
        if depth > 16 {
            return None;
        }
        let table = tables.get(module)?;
        let entry = table.get(name)?;
        match entry {
            ModuleEntry::Def { kind, .. } => {
                if let DefKind::PlatformEffect { scheduling_class, .. } = kind.as_ref() {
                    Some(*scheduling_class)
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
                make_bind(bind_callee, name, io_expr, annotation, result, span)
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
        if let Some(sc) = scheduling_class_from_table(symbol_tables, &mod_part, sym_part) {
            return sc;
        }
    }
    scheduling_class_from_table(symbol_tables, current_module, name)
        .unwrap_or(SchedulingClass::Sequential)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
