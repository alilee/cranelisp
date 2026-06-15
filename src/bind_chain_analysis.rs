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
    DefKind, Defn, Expr, MatchArm, ModuleEntry, ModuleFullPath, Span,
    Symbol, SymbolTable, TypeExpr, free_vars_expr,
};

/// Per-module symbol tables used for scheduling-class lookup.
///
/// After Sprint 57 Wave 3 G8 `bind_chain_analysis` walks the symbol tables
/// directly — following `ModuleEntry::Import` chains to the defining
/// `ModuleEntry::Def` and destructuring `DefKind::Primitive {
/// primitive_kind: PrimitiveKind::PlatformEffect { scheduling_class }, .. }`
/// to get the class. This replaces the previous `PlatformRegistry` side map.
pub type SymbolTables = dashmap::DashMap<ModuleFullPath, SymbolTable>;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Transform bind chains in a function body into `ParBind` nodes where safe.
///
/// Takes ownership of the body via `std::mem::replace` with a dummy expression,
/// transforms it, and puts the result back. The dummy is never observed.
pub fn auto_schedule_defn(
    defn: &mut Defn,
    symbol_tables: &SymbolTables,
    current_module: &ModuleFullPath,
) {
    // Single-sig only (multi-sig functions are not auto-scheduled)
    assert!(!defn.is_multi_sig(), "auto_schedule_defn called on multi-sig defn");
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
pub(crate) fn auto_schedule_expr(
    expr: &mut Expr,
    symbol_tables: &SymbolTables,
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
pub(crate) fn auto_schedule_expr_owned(
    expr: Expr,
    symbol_tables: &SymbolTables,
    current_module: &ModuleFullPath,
) -> Expr {
    transform_expr(expr, symbol_tables, current_module)
}

// ---------------------------------------------------------------------------
// Expression transformation
// ---------------------------------------------------------------------------

/// Recursively transform an expression, optimizing bind chains into ParBind.
fn transform_expr(
    expr: Expr,
    symbol_tables: &SymbolTables,
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

/// A single step in a bind chain: (bound_name, io_expr, annotation, span).
type BindStep = (Symbol, Expr, Option<TypeExpr>, Span);

/// Collect a complete bind chain into a flat vec of steps plus the final body.
///
/// The chain must be non-empty (caller checks via `is_bind_chain_start`).
/// The `annotation` field preserves the Lambda parameter's optional type
/// annotation for round-tripping.
fn collect_bind_chain(expr: Expr) -> (Vec<BindStep>, Expr) {
    let Expr::Apply { mut args, span, .. } = expr else {
        unreachable!("invariant: collect_bind_chain called on non-bind expr")
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
        rest.insert(0, (name, io_expr, annotation, binding_span));
        (rest, final_body)
    } else {
        (vec![(name, io_expr, annotation, binding_span)], inner)
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
fn classify_expr(
    expr: &Expr,
    symbol_tables: &SymbolTables,
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
fn scheduling_class_from_table(
    symbol_tables: &SymbolTables,
    module: &ModuleFullPath,
    name: &str,
) -> Option<SchedulingClass> {
    fn walk(
        tables: &SymbolTables,
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
    /// A single sequential bind step.
    Sequential(Symbol, Expr, Option<TypeExpr>, Span),
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
    for (name, _, _, _) in &group {
        bound_so_far.insert(name.clone());
    }
    if group.len() >= 2 {
        let par_bindings: Vec<(Symbol, Expr, Span)> =
            group.into_iter().map(|(n, e, _, s)| (n, e, s)).collect();
        segments.push(Segment::Parallel(par_bindings));
    } else {
        let (name, io_expr, annotation, span) = group.into_iter().next()
            .expect("invariant: group is non-empty");
        segments.push(Segment::Sequential(name, io_expr, annotation, span));
    }
}

/// Group a flat bind chain and rebuild it into an optimised nested expression.
fn rebuild_chain(
    chain: Vec<BindStep>,
    final_body: Expr,
    symbol_tables: &SymbolTables,
    current_module: &ModuleFullPath,
) -> Expr {
    let mut segments: Vec<Segment> = Vec::new();
    let mut current_par: Vec<BindStep> = Vec::new();
    let mut bound_so_far: HashSet<Symbol> = HashSet::new();

    for (name, io_expr, annotation, span) in chain {
        let sc = classify_expr(&io_expr, symbol_tables, current_module);

        // Names already committed + names in the current parallel group.
        let mut all_bound = bound_so_far.clone();
        for (n, _, _, _) in &current_par {
            all_bound.insert(n.clone());
        }

        if sc != SchedulingClass::Sequential && is_independent(&io_expr, &all_bound) {
            current_par.push((name, io_expr, annotation, span));
        } else {
            // This entry can't join the parallel group — flush first.
            flush_par_group(
                &mut segments,
                &mut bound_so_far,
                std::mem::take(&mut current_par),
            );
            bound_so_far.insert(name.clone());
            segments.push(Segment::Sequential(name, io_expr, annotation, span));
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
            Segment::Sequential(name, io_expr, annotation, span) => {
                let io_expr = transform_expr(io_expr, symbol_tables, current_module);
                make_bind(name, io_expr, annotation, result, span)
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

/// Reconstruct a sequential `(bind io_expr (fn [name] body))` expression.
fn make_bind(
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
            name: Symbol::from("bind"),
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
fn recurse_children(
    expr: Expr,
    symbol_tables: &SymbolTables,
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
pub(crate) fn scheduling_of(
    symbol_tables: &SymbolTables,
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
mod tests {
    use super::*;
    use cranelisp_types::{FQSymbol, Scheme, Span, Symbol, Type, Visibility};

    fn make_var(name: &str) -> Expr {
        Expr::Var { name: Symbol::from(name), span: Span::SYNTHETIC, resolved_call: None, inferred_type: None }
    }

    fn make_int(value: i64) -> Expr {
        Expr::IntLit { value, span: Span::SYNTHETIC, inferred_type: None }
    }

    fn make_apply(callee: &str, args: Vec<Expr>) -> Expr {
        Expr::Apply {
            callee: Box::new(make_var(callee)),
            args,
            span: Span::SYNTHETIC,
            resolved_call: None,
            inferred_type: None,
        }
    }

    fn make_bind_expr(io_expr: Expr, name: &str, body: Expr) -> Expr {
        Expr::Apply {
            callee: Box::new(make_var("bind")),
            args: vec![
                io_expr,
                Expr::Lambda {
                    params: vec![(Symbol::from(name), None)],
                    body: Box::new(body),
                    span: Span::SYNTHETIC,
                    inferred_type: None,
                },
            ],
            span: Span::SYNTHETIC,
            resolved_call: None,
            inferred_type: None,
        }
    }

    fn platform_effect_entry(sc: SchedulingClass) -> ModuleEntry {
        ModuleEntry::def(
            Scheme {
                type_vars: vec![],
                constraints: std::collections::HashMap::new(),
                ty: Type::Int,
            },
            DefKind::PlatformEffect { scheduling_class: sc, got_slot: 0 },
        )
        .visibility(Visibility::Public)
        .build()
    }

    /// Build a symbol table setup for bind-chain tests. Creates the
    /// `platform.test` module with entries for `get-time`, `http-get`, and
    /// `print`, plus a `user` module that imports all three bare.
    fn commutative_tables() -> (SymbolTables, ModuleFullPath) {
        let tables: SymbolTables = dashmap::DashMap::new();
        let user_mod = ModuleFullPath::from("user");
        let plat_mod = ModuleFullPath::from("platform.test");

        let mut plat = SymbolTable::new(plat_mod.clone());
        plat.insert(Symbol::from("get-time"), platform_effect_entry(SchedulingClass::Commutative));
        plat.insert(Symbol::from("http-get"), platform_effect_entry(SchedulingClass::Commutative));
        plat.insert(Symbol::from("print"), platform_effect_entry(SchedulingClass::Sequential));
        tables.insert(plat_mod.clone(), plat);

        let mut user = SymbolTable::new(user_mod.clone());
        for name in &["get-time", "http-get", "print"] {
            user.insert(
                Symbol::from(*name),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: plat_mod.clone(),
                        symbol: Symbol::from(*name),
                    },
                    visibility: Visibility::Private,
                },
            );
        }
        tables.insert(user_mod.clone(), user);

        (tables, user_mod)
    }

    // spec: 10-io §10.12.1 — pattern recognition
    #[test]
    fn test_is_bind_chain_start() {
        let expr = make_bind_expr(make_apply("get-time", vec![]), "t", make_int(0));
        assert!(is_bind_chain_start(&expr));
    }

    #[test]
    fn test_non_bind_not_chain_start() {
        let expr = make_apply("foo", vec![make_int(1)]);
        assert!(!is_bind_chain_start(&expr));
    }

    // spec: 10-io §10.12.1 — chain collection
    #[test]
    fn test_collect_two_step_chain() {
        // (bind (get-time) (fn [t1] (bind (get-time) (fn [t2] body))))
        let inner = make_bind_expr(
            make_apply("get-time", vec![]),
            "t2",
            make_int(42),
        );
        let expr = make_bind_expr(
            make_apply("get-time", vec![]),
            "t1",
            inner,
        );
        let (chain, body) = collect_bind_chain(expr);
        assert_eq!(chain.len(), 2);
        assert_eq!(chain[0].0.as_ref(), "t1");
        assert_eq!(chain[1].0.as_ref(), "t2");
        assert!(matches!(body, Expr::IntLit { value: 42, .. }));
    }

    // spec: 10-io §10.12.1 — scheduling classification
    #[test]
    fn test_classify_commutative() {
        let (tables, m) = commutative_tables();
        let expr = make_apply("get-time", vec![]);
        assert_eq!(classify_expr(&expr, &tables, &m), SchedulingClass::Commutative);
    }

    #[test]
    fn test_classify_sequential_default() {
        let (tables, m) = commutative_tables();
        let expr = make_apply("unknown-fn", vec![]);
        assert_eq!(classify_expr(&expr, &tables, &m), SchedulingClass::Sequential);
    }

    #[test]
    fn test_classify_qualified_name_fallback() {
        let (tables, m) = commutative_tables();
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("platform.test/get-time"),
                span: Span::SYNTHETIC,
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![],
            span: Span::SYNTHETIC,
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(classify_expr(&expr, &tables, &m), SchedulingClass::Commutative);
    }

    // spec: 10-io §10.12.1 — independence check
    #[test]
    fn test_independent_expressions() {
        let expr = make_apply("get-time", vec![]);
        let bound: HashSet<Symbol> = [Symbol::from("x")].into();
        assert!(is_independent(&expr, &bound));
    }

    #[test]
    fn test_dependent_expression() {
        let expr = make_apply("http-get", vec![make_var("x")]);
        let bound: HashSet<Symbol> = [Symbol::from("x")].into();
        assert!(!is_independent(&expr, &bound));
    }

    // spec: 10-io §10.12.1 — two commutative independent steps become ParBind
    #[test]
    fn test_two_commutative_independent_become_par_bind() {
        let (tables, m) = commutative_tables();
        // (bind (get-time) (fn [t1] (bind (http-get "url") (fn [t2] body))))
        let inner = make_bind_expr(
            make_apply("http-get", vec![make_var("url")]),
            "t2",
            make_int(99),
        );
        let expr = make_bind_expr(
            make_apply("get-time", vec![]),
            "t1",
            inner,
        );
        let result = transform_expr(expr, &tables, &m);
        // Should produce a ParBind with 2 bindings.
        match &result {
            Expr::ParBind { bindings, .. } => {
                assert_eq!(bindings.len(), 2);
                assert_eq!(bindings[0].0.as_ref(), "t1");
                assert_eq!(bindings[1].0.as_ref(), "t2");
            }
            other => panic!("expected ParBind, got {:?}", other),
        }
    }

    // spec: 10-io §10.12.1 — sequential stays sequential
    #[test]
    fn test_sequential_stays_sequential() {
        let (tables, m) = commutative_tables();
        // (bind (print "hi") (fn [_] (bind (print "bye") (fn [_] 0))))
        let inner = make_bind_expr(
            make_apply("print", vec![make_var("s2")]),
            "_b",
            make_int(0),
        );
        let expr = make_bind_expr(
            make_apply("print", vec![make_var("s1")]),
            "_a",
            inner,
        );
        let result = transform_expr(expr, &tables, &m);
        // Should remain as nested Apply (no ParBind).
        assert!(!matches!(result, Expr::ParBind { .. }));
    }

    // spec: 10-io §10.12.1 — dependent commutative stays sequential
    #[test]
    fn test_dependent_commutative_stays_sequential() {
        let (tables, m) = commutative_tables();
        // (bind (get-time) (fn [t1] (bind (http-get t1) (fn [t2] body))))
        // t1 appears free in the second io_expr → dependent → no parallelism.
        let inner = make_bind_expr(
            make_apply("http-get", vec![make_var("t1")]),
            "t2",
            make_int(0),
        );
        let expr = make_bind_expr(
            make_apply("get-time", vec![]),
            "t1",
            inner,
        );
        let result = transform_expr(expr, &tables, &m);
        assert!(!matches!(result, Expr::ParBind { .. }));
    }

    // spec: 10-io §10.12.1 — single-element group demotion
    #[test]
    fn test_single_element_demoted() {
        let (tables, m) = commutative_tables();
        // Single bind step — should not produce ParBind.
        let expr = make_bind_expr(
            make_apply("get-time", vec![]),
            "t1",
            make_int(0),
        );
        let result = transform_expr(expr, &tables, &m);
        assert!(!matches!(result, Expr::ParBind { .. }));
    }

    // spec: 10-io §10.12 — empty tables skips analysis
    #[test]
    fn test_empty_tables_no_transform() {
        let tables: SymbolTables = dashmap::DashMap::new();
        let m = ModuleFullPath::from("user");
        tables.insert(m.clone(), SymbolTable::new(m.clone()));
        let inner = make_bind_expr(
            make_apply("get-time", vec![]),
            "t2",
            make_int(0),
        );
        let expr = make_bind_expr(
            make_apply("get-time", vec![]),
            "t1",
            inner,
        );
        let result = transform_expr(expr, &tables, &m);
        // With no platform entries, all calls are Sequential → no ParBind.
        assert!(!matches!(result, Expr::ParBind { .. }));
    }

    // spec: 10-io §10.12.1 — scheduling_of lookup
    #[test]
    fn test_scheduling_of_bare_name() {
        let (tables, m) = commutative_tables();
        assert_eq!(scheduling_of(&tables, &m, "get-time"), SchedulingClass::Commutative);
        assert_eq!(scheduling_of(&tables, &m, "print"), SchedulingClass::Sequential);
        assert_eq!(scheduling_of(&tables, &m, "unknown"), SchedulingClass::Sequential);
    }

    #[test]
    fn test_scheduling_of_qualified_name() {
        let (tables, m) = commutative_tables();
        assert_eq!(
            scheduling_of(&tables, &m, "platform.test/get-time"),
            SchedulingClass::Commutative,
        );
    }

    // spec: design/int/platform-registry-removal.md §9.1 —
    // bind_chain_analysis reads scheduling_class from ModuleEntry::Def
    // (post-G8 migration: no PlatformRegistry).
    #[test]
    fn bind_chain_analysis_reads_scheduling_class_from_entry() {
        // Only a single platform-effect entry carrying SchedulingClass::Commutative
        // is needed. Build it minimally and verify the reader path via the
        // symbol-table lookup.
        let tables: SymbolTables = dashmap::DashMap::new();
        let m = ModuleFullPath::from("caller");
        let plat = ModuleFullPath::from("platform.t");
        let mut pst = SymbolTable::new(plat.clone());
        pst.insert(
            Symbol::from("op"),
            platform_effect_entry(SchedulingClass::Commutative),
        );
        tables.insert(plat.clone(), pst);
        let mut cst = SymbolTable::new(m.clone());
        cst.insert(
            Symbol::from("op"),
            ModuleEntry::Import {
                source: FQSymbol { module: plat.clone(), symbol: Symbol::from("op") },
                visibility: Visibility::Private,
            },
        );
        tables.insert(m.clone(), cst);

        // Classify a direct call to `op` — must pick up the Commutative class
        // via the Import-chain walk.
        let expr = make_apply("op", vec![]);
        assert_eq!(
            classify_expr(&expr, &tables, &m),
            SchedulingClass::Commutative,
            "classify_expr should read SchedulingClass::Commutative through the Import chain \
             to the PlatformEffect entry"
        );
    }
}
