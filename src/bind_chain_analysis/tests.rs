use super::*;
use cranelisp_types::{FQSymbol, Scheme, Span, Symbol, Type, Visibility};

fn make_var(name: &str) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span: Span::SYNTHETIC,
        resolved_call: None,
        inferred_type: None,
    }
}

fn make_int(value: i64) -> Expr {
    Expr::IntLit {
        value,
        span: Span::SYNTHETIC,
        inferred_type: None,
    }
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
    make_bind_expr_with_callee("bind", io_expr, name, body)
}

/// Like `make_bind_expr` but with an explicit (possibly qualified) `bind`
/// callee name — used to verify the original callee is threaded faithfully
/// through chain collection → segment reconstruction → `make_bind`.
fn make_bind_expr_with_callee(callee: &str, io_expr: Expr, name: &str, body: Expr) -> Expr {
    Expr::Apply {
        callee: Box::new(make_var(callee)),
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
        DefKind::PlatformEffect {
            scheduling_class: sc,
            poll_shape: false,
            got_slot: 0,
            mode_summary: None,
        },
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
    plat.insert(
        Symbol::from("get-time"),
        platform_effect_entry(SchedulingClass::Commutative),
    );
    plat.insert(
        Symbol::from("http-get"),
        platform_effect_entry(SchedulingClass::Commutative),
    );
    plat.insert(
        Symbol::from("print"),
        platform_effect_entry(SchedulingClass::Sequential),
    );
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
    let inner = make_bind_expr(make_apply("get-time", vec![]), "t2", make_int(42));
    let expr = make_bind_expr(make_apply("get-time", vec![]), "t1", inner);
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
    assert_eq!(
        classify_expr(&expr, &tables, &m),
        SchedulingClass::Commutative
    );
}

#[test]
fn test_classify_sequential_default() {
    let (tables, m) = commutative_tables();
    let expr = make_apply("unknown-fn", vec![]);
    assert_eq!(
        classify_expr(&expr, &tables, &m),
        SchedulingClass::Sequential
    );
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
    assert_eq!(
        classify_expr(&expr, &tables, &m),
        SchedulingClass::Commutative
    );
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
    let expr = make_bind_expr(make_apply("get-time", vec![]), "t1", inner);
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
    let inner = make_bind_expr(make_apply("print", vec![make_var("s2")]), "_b", make_int(0));
    let expr = make_bind_expr(make_apply("print", vec![make_var("s1")]), "_a", inner);
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
    let expr = make_bind_expr(make_apply("get-time", vec![]), "t1", inner);
    let result = transform_expr(expr, &tables, &m);
    assert!(!matches!(result, Expr::ParBind { .. }));
}

// spec: 10-io §10.12.1 — single-element group demotion
#[test]
fn test_single_element_demoted() {
    let (tables, m) = commutative_tables();
    // Single bind step whose result is USED (`t1` in the continuation) — not
    // launch-eligible, so it demotes to a sequential bind, never a ParBind.
    let expr = make_bind_expr(make_apply("get-time", vec![]), "t1", make_var("t1"));
    let result = transform_expr(expr, &tables, &m);
    assert!(!matches!(result, Expr::ParBind { .. }));
    // A used result is the conservative-Bind path, not a detached launch.
    assert!(!matches!(result, Expr::LaunchContinue { .. }));
}

// spec: 10-io.md §10.12.1 — qualified `bind` callee is preserved through
// Sequential reconstruction (S85 wiring defect). The `bind!` macro expands
// to a *qualified* `primitives/bind` callee; the sketch's `make_bind`
// hardcoded a bare `"bind"`, which would not resolve in a module that only
// imports the qualified name. This pins that the original callee is threaded
// BindStep → Segment::Sequential → make_bind verbatim.
//
// Path exercised: a single eligible (Commutative, independent) step enters
// the parallel group, then `flush_par_group` demotes the 1-element group to
// `Segment::Sequential`, and `make_bind` re-emits `bind_callee`. Under the
// old hardcoded bare-`"bind"` code the reconstructed callee would be `bind`,
// failing this assertion.
#[test]
fn test_qualified_bind_callee_preserved_through_sequential() {
    let (tables, m) = commutative_tables();
    // (primitives/bind (get-time) (fn [t1] t1)) — single step, demoted to
    // Sequential during rebuild. The continuation USES `t1` (the result is NOT
    // discarded), so this is NOT launch-eligible (§10.12.7) and round-trips as
    // an ordinary `bind` Apply — exactly the sequential-reconstruction path
    // this test pins. (A discarded result would instead lower to
    // `LaunchContinue`; see `test_launch_*` below.)
    let expr = make_bind_expr_with_callee(
        "primitives/bind",
        make_apply("get-time", vec![]),
        "t1",
        make_var("t1"),
    );
    let result = transform_expr(expr, &tables, &m);
    // A single step never becomes a ParBind — it round-trips as a Sequential
    // bind Apply.
    let Expr::Apply { callee, .. } = &result else {
        panic!("expected a reconstructed bind Apply, got {result:?}");
    };
    let Expr::Var { name, .. } = callee.as_ref() else {
        panic!("expected a Var callee, got {callee:?}");
    };
    assert_eq!(
        name.as_ref(),
        "primitives/bind",
        "reconstructed bind callee must preserve the qualified name, \
             not collapse to a bare `bind`"
    );
}

// spec: 10-io §10.12 — empty tables skips analysis
#[test]
fn test_empty_tables_no_transform() {
    let tables: SymbolTables = dashmap::DashMap::new();
    let m = ModuleFullPath::from("user");
    tables.insert(m.clone(), SymbolTable::new(m.clone()));
    let inner = make_bind_expr(make_apply("get-time", vec![]), "t2", make_int(0));
    let expr = make_bind_expr(make_apply("get-time", vec![]), "t1", inner);
    let result = transform_expr(expr, &tables, &m);
    // With no platform entries, all calls are Sequential → no ParBind.
    assert!(!matches!(result, Expr::ParBind { .. }));
}

// spec: 10-io §10.12.1 — scheduling_of lookup
#[test]
fn test_scheduling_of_bare_name() {
    let (tables, m) = commutative_tables();
    assert_eq!(
        scheduling_of(&tables, &m, "get-time"),
        SchedulingClass::Commutative
    );
    assert_eq!(
        scheduling_of(&tables, &m, "print"),
        SchedulingClass::Sequential
    );
    assert_eq!(
        scheduling_of(&tables, &m, "unknown"),
        SchedulingClass::Sequential
    );
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
// spec: 10-io.md §10.12.1 — idempotency (the retry-from-top requirement, §5.2).
// `finalize_cluster` may run the pass multiple times against larger live state;
// re-running on an already-ParBind-transformed tree must be a no-op.
#[test]
fn test_transform_idempotent() {
    let (tables, m) = commutative_tables();
    // (bind (get-time) (fn [t1] (bind (http-get "url") (fn [t2] body))))
    let inner = make_bind_expr(
        make_apply("http-get", vec![make_var("url")]),
        "t2",
        make_int(99),
    );
    let expr = make_bind_expr(make_apply("get-time", vec![]), "t1", inner);

    let once = transform_expr(expr, &tables, &m);
    // First pass produced a ParBind.
    assert!(
        matches!(once, Expr::ParBind { .. }),
        "first pass should ParBind"
    );
    let twice = transform_expr(once.clone(), &tables, &m);
    // Re-running must produce the identical tree (recurse_children's ParBind
    // arm recurses children without re-grouping). `Expr` does not derive
    // `PartialEq` (only Debug/Clone/Serialize/Deserialize, ast.rs:147), so
    // structural `assert_eq!` is unavailable here — Debug-string equality is
    // the available structural comparison (S-2: PartialEq is NOT added just
    // for this test).
    assert_eq!(
        format!("{once:?}"),
        format!("{twice:?}"),
        "transform must be idempotent: apply-twice == apply-once"
    );
}

// spec: 10-io.md §10.12.1 — mixed segmentation. A
// [independent, independent, dependent, independent] chain produces
// ParBind(2) → Sequential → Sequential (the dependent step flushes the
// group, then stands alone). Pins flush_par_group boundary behaviour.
#[test]
fn test_mixed_chain_segments() {
    let (tables, m) = commutative_tables();
    // (bind (get-time)           (fn [a]
    //   (bind (http-get "u")     (fn [b]
    //     (bind (http-get b)     (fn [c]      ; depends on b → flush
    //       (bind (get-time)     (fn [d] (add c d)))))))))
    // The final body USES `c` and `d`, so neither step is launch-eligible
    // (results not discarded) — they take the sequential / demoted-sequential
    // paths this test pins (a discarded result would lower to LaunchContinue).
    let l4 = make_bind_expr(
        make_apply("get-time", vec![]),
        "d",
        make_apply("add", vec![make_var("c"), make_var("d")]),
    );
    let l3 = make_bind_expr(make_apply("http-get", vec![make_var("b")]), "c", l4);
    let l2 = make_bind_expr(make_apply("http-get", vec![make_var("u")]), "b", l3);
    let l1 = make_bind_expr(make_apply("get-time", vec![]), "a", l2);

    let result = transform_expr(l1, &tables, &m);
    // Outermost: a ParBind grouping a + b (both independent, non-Sequential).
    let Expr::ParBind { bindings, body, .. } = &result else {
        panic!("expected outer ParBind, got {result:?}");
    };
    assert_eq!(bindings.len(), 2, "first group is a + b");
    assert_eq!(bindings[0].0.as_ref(), "a");
    assert_eq!(bindings[1].0.as_ref(), "b");
    // Next: c is dependent on b → sequential bind, NOT another ParBind.
    let Expr::Apply { callee, args, .. } = body.as_ref() else {
        panic!("expected sequential bind for c, got {body:?}");
    };
    assert!(is_bind_var(callee), "c must be a sequential bind");
    // Inside c's lambda body: d is a single eligible step → demoted to
    // sequential (1-element group), never a ParBind.
    let Expr::Lambda { body: c_body, .. } = &args[1] else {
        panic!("expected lambda for c");
    };
    assert!(
        !matches!(c_body.as_ref(), Expr::ParBind { .. }),
        "trailing single eligible step d must be demoted to sequential, got {c_body:?}"
    );
}

// spec: 10-io.md §10.12.1 — data-dependency negative via a Let-RHS free var
// (Gap G1: free_vars_expr must see the var captured inside a Let binding RHS).
// A later io_expr that references an earlier-bound name through a Let → the
// binding is dependent → no ParBind.
#[test]
fn test_dependent_via_let_rhs_stays_sequential() {
    let (tables, m) = commutative_tables();
    // second io_expr: (http-get (let [y t1] y)) — t1 is free via the Let RHS.
    let let_expr = Expr::Let {
        bindings: vec![(Symbol::from("y"), make_var("t1"))],
        body: Box::new(make_var("y")),
        span: Span::SYNTHETIC,
        inferred_type: None,
    };
    let inner = make_bind_expr(make_apply("http-get", vec![let_expr]), "t2", make_int(0));
    let expr = make_bind_expr(make_apply("get-time", vec![]), "t1", inner);
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::ParBind { .. }),
        "data-dependency through a Let RHS must keep the chain sequential"
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
            source: FQSymbol {
                module: plat.clone(),
                symbol: Symbol::from("op"),
            },
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

// === Launch-and-continue emission (S96 Chunk B, spec §10.12.7) =============

// spec: 10-io.md §10.12.7 — NEGATIVE (E3 token-0 refusal): a discarded
// `Commutative` (token-0, shared-singleton) effect is NOT launch-eligible.
// design: effect-concurrency.md §4.1 — E3 refuses `Commutative` (the
// value-provenance witness cannot prove a shared singleton disjoint; detaching
// it would REORDER same-token effects across the detach boundary). This
// TIGHTENS the pre-S96 single-step arm (whose `class != Sequential &&
// result-discarded` test wrongly detached a discarded `Commutative`).
#[test]
fn test_no_launch_for_commutative_class_even_if_discarded() {
    let (tables, m) = commutative_tables();
    // (bind (get-time) (fn [_ignored] 0)) — get-time is Commutative (token-0);
    // result discarded, BUT token-0 ⇒ E3 REFUSAL ⇒ ordinary Bind, no launch.
    let expr = make_bind_expr(make_apply("get-time", vec![]), "t1", make_int(0));
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::LaunchContinue { .. }),
        "a discarded Commutative (token-0) effect must NOT launch (E3 refusal), got {result:?}"
    );
    assert!(
        matches!(result, Expr::Apply { .. }),
        "must be an ordinary bind Apply"
    );
}

// spec: 10-io.md §10.12.7 — a ResourceSerial (poll-pool-style) effect with a
// discarded result also launches (a non-Sequential class carries a resource
// token; the analysis approximates token-disjointness by class per Gap G2, the
// trampoline owns the live token decision). This is the §B4 accept-loop shape.
#[test]
fn test_launch_emitted_for_discarded_resource_serial_result() {
    let tables: SymbolTables = dashmap::DashMap::new();
    let m = ModuleFullPath::from("user");
    let plat = ModuleFullPath::from("platform.test");
    let mut pst = SymbolTable::new(plat.clone());
    pst.insert(
        Symbol::from("rd"),
        platform_effect_entry(SchedulingClass::ResourceSerial),
    );
    tables.insert(plat.clone(), pst);
    let mut cst = SymbolTable::new(m.clone());
    cst.insert(
        Symbol::from("rd"),
        ModuleEntry::Import {
            source: FQSymbol {
                module: plat.clone(),
                symbol: Symbol::from("rd"),
            },
            visibility: Visibility::Private,
        },
    );
    tables.insert(m.clone(), cst);

    // (bind (rd) (fn [r] 7)) — r discarded; rd is ResourceSerial.
    let expr = make_bind_expr(make_apply("rd", vec![]), "r", make_int(7));
    let result = transform_expr(expr, &tables, &m);
    assert!(
        matches!(result, Expr::LaunchContinue { .. }),
        "a discarded-result ResourceSerial step must launch, got {result:?}"
    );
}

// spec: 10-io.md §10.12.7 — NEGATIVE: result USED ⇒ NOT launch (conservative
// Bind). The continuation references the binder, so the effect's result is not
// discarded — declining to detach is always sound.
#[test]
fn test_no_launch_when_result_used() {
    let (tables, m) = commutative_tables();
    // (bind (get-time) (fn [t1] t1)) — t1 USED → ordinary bind, no launch.
    let expr = make_bind_expr(make_apply("get-time", vec![]), "t1", make_var("t1"));
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::LaunchContinue { .. }),
        "a USED result must NOT launch (conservative Bind), got {result:?}"
    );
    assert!(
        matches!(result, Expr::Apply { .. }),
        "must be an ordinary bind Apply"
    );
}

// spec: 10-io.md §10.12.7 — NEGATIVE: a `Sequential`-class effect (no disjoint
// resource token) NEVER launches, even with a discarded result. Sequencing of
// Sequential effects must be preserved (§10.12.2).
#[test]
fn test_no_launch_for_sequential_class_even_if_discarded() {
    let (tables, m) = commutative_tables();
    // (bind (print) (fn [_p] 0)) — print is Sequential; discarded result, but
    // Sequential class ⇒ NOT launch-eligible (tokens not disjoint).
    let expr = make_bind_expr(make_apply("print", vec![]), "p", make_int(0));
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::LaunchContinue { .. }),
        "a Sequential-class effect must NOT launch, got {result:?}"
    );
}

// spec: 10-io.md §10.12.7 — idempotency: re-running the pass on an
// already-`LaunchContinue`-transformed tree is a no-op (recurse_children's
// LaunchContinue arm recurses children without re-grouping), mirroring the
// ParBind idempotency requirement (§5.2).
#[test]
fn test_launch_transform_idempotent() {
    // A ResourceSerial (per-token) discarded step IS launch-eligible (E3
    // permits ResourceSerial; Commutative/token-0 is refused — see
    // `test_no_launch_for_commutative_class_even_if_discarded`).
    let (tables, m) = resource_serial_tables();
    let expr = make_bind_expr(make_apply("rd", vec![]), "t1", make_int(0));
    let once = transform_expr(expr, &tables, &m);
    assert!(
        matches!(once, Expr::LaunchContinue { .. }),
        "first pass should launch"
    );
    let twice = transform_expr(once.clone(), &tables, &m);
    assert_eq!(
        format!("{once:?}"),
        format!("{twice:?}"),
        "launch transform must be idempotent: apply-twice == apply-once"
    );
}

// === The C-fanout E1/E2/E3 launch-eligibility matrix ======================
// design: effect-concurrency.md §4.1 — the inferred-launch eligibility
// predicate over a discarded bind SUB-TREE (the inlined connection handler).
// FIXME 0470 (/arch lighter-path ruling, option 2). spec: §10.12.7.

/// A poll-shape platform-effect entry (`poll_shape == true`) — the leading
/// operand is the DYNAMIC token (the `(token, capacity, …)` convention), so
/// these exercise the E3 token-0 refusal.
fn poll_effect_entry(sc: SchedulingClass) -> ModuleEntry {
    ModuleEntry::def(
        Scheme {
            type_vars: vec![],
            constraints: std::collections::HashMap::new(),
            ty: Type::Int,
        },
        DefKind::PlatformEffect {
            scheduling_class: sc,
            poll_shape: true,
            got_slot: 0,
            mode_summary: None,
        },
    )
    .visibility(Visibility::Public)
    .build()
}

/// Tables for the C-fanout matrix: a `platform.web`-shaped module exporting
/// poll-shape leaves `rd`/`wr` (the read-conn/send-conn analogues,
/// `ResourceSerial`), a `cm` (`Commutative` = token-0) and a `seq`
/// (`Sequential` = token-1), imported bare into `user`.
fn fanout_tables() -> (SymbolTables, ModuleFullPath) {
    let tables: SymbolTables = dashmap::DashMap::new();
    let user_mod = ModuleFullPath::from("user");
    let plat = ModuleFullPath::from("platform.web");
    let mut p = SymbolTable::new(plat.clone());
    p.insert(
        Symbol::from("rd"),
        poll_effect_entry(SchedulingClass::ResourceSerial),
    );
    p.insert(
        Symbol::from("wr"),
        poll_effect_entry(SchedulingClass::ResourceSerial),
    );
    p.insert(
        Symbol::from("cm"),
        poll_effect_entry(SchedulingClass::Commutative),
    );
    p.insert(
        Symbol::from("seq"),
        poll_effect_entry(SchedulingClass::Sequential),
    );
    tables.insert(plat.clone(), p);
    let mut u = SymbolTable::new(user_mod.clone());
    for n in &["rd", "wr", "cm", "seq"] {
        u.insert(
            Symbol::from(*n),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: plat.clone(),
                    symbol: Symbol::from(*n),
                },
                visibility: Visibility::Private,
            },
        );
    }
    // The `sleep` timer leaf — a `DefKind::PrimitiveExtern` (mirrors
    // `bootstrap.rs`'s `sleep`). A resource-free timer: launch-eligible only as
    // a sub-tree MEMBER (the §4.1 timer refinement), never the single-step root.
    u.insert(
        Symbol::from("sleep"),
        ModuleEntry::def(
            Scheme {
                type_vars: vec![],
                constraints: std::collections::HashMap::new(),
                ty: Type::Int,
            },
            DefKind::PrimitiveExtern,
        )
        .visibility(Visibility::Public)
        .build(),
    );
    tables.insert(user_mod.clone(), u);
    (tables, user_mod)
}

/// Single-platform-leaf ResourceSerial tables (poll_shape=false `rd`) — the
/// `test_launch_transform_idempotent` single-step shape.
fn resource_serial_tables() -> (SymbolTables, ModuleFullPath) {
    fanout_tables()
}

/// Build the inlined connection-handler sub-tree
/// `(bind (<read> <token> c f) (fn [req] (<write> <token> c f req)))` — the
/// shape `/port` inlines into the serve loop down to platform leaves.
fn handler_subtree(read: &str, token: Expr, write: &str) -> Expr {
    make_bind_expr(
        make_apply(read, vec![token.clone(), make_var("c"), make_var("f")]),
        "req",
        make_apply(
            write,
            vec![token, make_var("c"), make_var("f"), make_var("req")],
        ),
    )
}

/// `(bind <subtree> (fn [binder] <continuation>))` — the discarded-launch
/// outer step the serve loop's accept continuation desugars to.
fn launch_outer(subtree: Expr, binder: &str, continuation: Expr) -> Expr {
    make_bind_expr(subtree, binder, continuation)
}

/// The DECOUPLED §B4 single-step launch shape (FIXME 0478):
/// `(let [m (sub-i64 n 1)] (bind (<read> n c f) (fn [_] (recur m))))` — hoists
/// the loop control value `m` OUT of the token operand `n`, so io free {n} and
/// cont free {m} are DISJOINT and the unified E2 (same literal free-var
/// disjointness as the sub-tree arm) permits the launch. This is the accept-loop
/// desugaring the compiler front-half supplies.
fn decoupled_counter_loop(read: &str) -> Expr {
    Expr::Let {
        bindings: vec![(
            Symbol::from("m"),
            make_apply("sub-i64", vec![make_var("n")]),
        )],
        body: Box::new(make_bind_expr(
            make_apply(read, vec![make_var("n"), make_var("c"), make_var("f")]),
            "_",
            make_apply("recur", vec![make_var("m")]),
        )),
        span: Span::SYNTHETIC,
        inferred_type: None,
    }
}

/// Assert `result` is a `Let` whose body is a `LaunchContinue` — the shape the
/// decoupled single-step launch produces (the outer `(let [m …] …)` hoist wraps
/// the launched bind step).
fn assert_let_wraps_launch(result: &Expr) {
    let Expr::Let { body, .. } = result else {
        panic!("expected a Let wrapping the launch, got {result:?}");
    };
    assert!(
        matches!(body.as_ref(), Expr::LaunchContinue { .. }),
        "the decoupled single-step loop must LAUNCH inside the Let body, got {body:?}"
    );
}

// spec: 10-io.md §10.12.7 — POSITIVE: a discarded, value-local, ResourceSerial
// bind SUB-TREE (the inlined `read→handle→send` handler over a fresh `conn`
// token) lowers to `LaunchContinue`. design: effect-concurrency.md §4.1
// (E1 discarded + E2 value-local + E3 ResourceSerial-only).
#[test]
fn test_launch_subtree_discarded_value_local_resource_serial() {
    let (tables, m) = fanout_tables();
    // outer: (bind (bind (rd t c f) (fn [req] (wr t c f req))) (fn [_] (recur listener)))
    let subtree = handler_subtree("rd", make_var("t"), "wr");
    let cont = make_apply("recur", vec![make_var("listener")]);
    let expr = launch_outer(subtree, "_", cont);
    let result = transform_expr(expr, &tables, &m);
    let Expr::LaunchContinue {
        launched,
        continuation,
        ..
    } = &result
    else {
        panic!("a discarded value-local ResourceSerial sub-tree must LAUNCH, got {result:?}");
    };
    // The launched arm is the (transformed) handler sub-tree; the continuation
    // is the accept-loop recursion.
    assert!(
        is_bind_chain_start(launched),
        "launched arm must be the handler sub-tree"
    );
    assert!(
        matches!(continuation.as_ref(), Expr::Apply { .. }),
        "continuation must be the accept-loop recursion"
    );
}

// spec: 10-io.md §10.12.7 — NEGATIVE (E1): the launched binder is USED in the
// continuation ⇒ the result is awaited ⇒ NOT launch (ordinary Bind).
#[test]
fn test_no_launch_subtree_when_result_used() {
    let (tables, m) = fanout_tables();
    let subtree = handler_subtree("rd", make_var("t"), "wr");
    // continuation references the binder `h` → E1 fails.
    let expr = launch_outer(subtree, "h", make_var("h"));
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::LaunchContinue { .. }),
        "a USED sub-tree result must NOT launch (E1), got {result:?}"
    );
}

// spec: 10-io.md §10.12.7 — NEGATIVE (E2 value-shared-with-continuation): the
// sub-tree shares a free variable (`t`, the resource token) with the
// continuation ⇒ the value-provenance disjointness witness FAILS ⇒ NOT launch.
// design: effect-concurrency.md §4.1 — a module-global pool handle (shared
// across siblings) appears exactly as this shared free var.
#[test]
fn test_no_launch_subtree_when_value_shared_with_continuation() {
    let (tables, m) = fanout_tables();
    let subtree = handler_subtree("rd", make_var("t"), "wr");
    // continuation ALSO touches `t` (the shared token / pool handle).
    let cont = make_apply("recur", vec![make_var("t")]);
    let expr = launch_outer(subtree, "_", cont);
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::LaunchContinue { .. }),
        "a sub-tree sharing a free var (token) with the continuation must NOT \
             launch (E2), got {result:?}"
    );
}

// spec: 10-io.md §10.12.7 — NEGATIVE (E3 token-0 / Commutative): the sub-tree
// touches a `Commutative` (token-0, shared singleton) effect ⇒ REFUSED.
#[test]
fn test_no_launch_subtree_with_commutative_token0_effect() {
    let (tables, m) = fanout_tables();
    // The handler's tail is `cm` (Commutative / token-0) instead of `wr`.
    let subtree = handler_subtree("rd", make_var("t"), "cm");
    let cont = make_apply("recur", vec![make_var("listener")]);
    let expr = launch_outer(subtree, "_", cont);
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::LaunchContinue { .. }),
        "a sub-tree touching a Commutative (token-0) effect must NOT launch (E3), got {result:?}"
    );
}

// spec: 10-io.md §10.12.7 — NEGATIVE (E3 literal token-0 on a poll-shape leaf):
// a poll-shape ResourceSerial leaf whose DYNAMIC leading token operand is the
// literal `0` is the shared-singleton token-0 ⇒ REFUSED (the unit analogue of
// the `e3_token0_…` e2e). design: effect-concurrency.md §4.1.
#[test]
fn test_no_launch_subtree_with_literal_token0_leading_operand() {
    let (tables, m) = fanout_tables();
    // rd's leading token operand is the literal 0 (shared singleton).
    let subtree = handler_subtree("rd", make_int(0), "wr");
    let cont = make_apply("recur", vec![make_var("listener")]);
    let expr = launch_outer(subtree, "_", cont);
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::LaunchContinue { .. }),
        "a poll-shape leaf with a literal-0 leading token must NOT launch (E3 token-0), got {result:?}"
    );
}

// spec: 10-io.md §10.12.7 — NEGATIVE (E3 token-1 / Sequential): the sub-tree
// touches a `Sequential` (global token-1) effect ⇒ REFUSED.
#[test]
fn test_no_launch_subtree_with_sequential_token1_effect() {
    let (tables, m) = fanout_tables();
    let subtree = handler_subtree("rd", make_var("t"), "seq");
    let cont = make_apply("recur", vec![make_var("listener")]);
    let expr = launch_outer(subtree, "_", cont);
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::LaunchContinue { .. }),
        "a sub-tree touching a Sequential (token-1) effect must NOT launch (E3), got {result:?}"
    );
}

// spec: 10-io.md §10.12.7 — NEGATIVE (E3 opaque user fn in effect position):
// an unknown footprint (a non-platform-effect call in the sub-tree's effect
// position) is REFUSED — exactly the 0470 wall that forces the handler to be
// inlined down to platform leaves. design: effect-concurrency.md §4.1.
#[test]
fn test_no_launch_subtree_with_opaque_user_fn_effect() {
    let (tables, m) = fanout_tables();
    // The read step is an opaque user fn `(handle-conn conn)` (not a platform
    // effect) — the un-inlined 0470 shape.
    let subtree = make_bind_expr(
        make_apply("handle-conn", vec![make_var("conn")]),
        "req",
        make_apply(
            "wr",
            vec![make_var("t"), make_var("c"), make_var("f"), make_var("req")],
        ),
    );
    let cont = make_apply("recur", vec![make_var("listener")]);
    let expr = launch_outer(subtree, "_", cont);
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::LaunchContinue { .. }),
        "a sub-tree with an opaque user-fn effect position must NOT launch (E3 \
             unknown footprint — the 0470 wall), got {result:?}"
    );
}

// spec: 10-io.md §10.12.7 — SINGLE-STEP token-0 refusal: a discarded poll-shape
// ResourceSerial leaf with a literal-0 leading token must NOT launch (the
// tightened single-step arm; the unit analogue of the e3_token0 e2e ordering
// pin). design: effect-concurrency.md §4.1.
#[test]
fn test_no_launch_single_step_literal_token0() {
    let (tables, m) = fanout_tables();
    // (bind (rd 0 c f) (fn [_] (recur))) — token 0 ⇒ E3 refusal.
    let expr = make_bind_expr(
        make_apply("rd", vec![make_int(0), make_var("c"), make_var("f")]),
        "_",
        make_apply("recur", vec![]),
    );
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::LaunchContinue { .. }),
        "a single discarded poll-shape leaf on token 0 must NOT launch (E3), got {result:?}"
    );
}

// spec: 10-io.md §10.12.7 / design/int/bind-chain-analysis.md §3.7 (FIXME 0478)
// — SINGLE-STEP nonzero-token launch, DECOUPLED shape: the §B4 accept loop hoists
// its control value out of the token operand — `(let [m (sub-i64 n 1)] (bind (rd
// n c f) (fn [_] (recur m))))` — so io free {n} and cont free {m} are DISJOINT and
// the unified E2 (same literal free-var disjointness as the sub-tree arm) permits
// the launch. Under the retired narrow check the token var could be shared; the
// unified check requires the decouple, which the accept-loop desugaring supplies.
#[test]
fn test_launch_single_step_nonzero_token_shares_counter_var() {
    let (tables, m) = fanout_tables();
    let result = transform_expr(decoupled_counter_loop("rd"), &tables, &m);
    assert_let_wraps_launch(&result);
}

// spec: 10-io.md §10.12.7 / design/int/bind-chain-analysis.md §3.7 (FIXME 0478)
// — SINGLE-STEP E2 literal-disjointness REFUSAL: a discarded `ResourceSerial`
// step `(wr conn r1)` whose continuation performs a same-token effect `(wr conn
// r2)` on the SAME handle `conn` must NOT single-step launch — io free {conn,r1}
// and cont free {conn,r2} SHARE `conn`, so the unified E2 (same literal free-var
// disjointness as the sub-tree arm) refuses it: the shared value cannot be proven
// token-disjoint, so detaching would reorder two same-token effects across the
// launch boundary. This is the check the single-step arm was MISSING before 0478.
// RED-on-revert: dropping the E2 disjointness guard makes this wrongly launch.
#[test]
fn test_no_single_step_launch_when_handle_flows_into_same_token_continuation() {
    let (tables, m) = fanout_tables();
    // (bind (wr conn r1) (fn [_] (wr conn r2))) — conn is the shared handle;
    // both wr are ResourceSerial on token `conn`. E1 passes (result discarded);
    // E3 passes (ResourceSerial); E2 REFUSES (handle flows into a same-token
    // continuation effect).
    let expr = make_bind_expr(
        make_apply("wr", vec![make_var("conn"), make_var("r1")]),
        "_",
        make_apply("wr", vec![make_var("conn"), make_var("r2")]),
    );
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::LaunchContinue { .. }),
        "a discarded ResourceSerial step whose continuation performs a same-token \
             effect on the same handle must NOT launch (E2, FIXME 0478), got {result:?}"
    );
}

// spec: 10-io.md §10.12.7 / design/int/bind-chain-analysis.md §3.7 (FIXME 0478)
// — SINGLE-STEP E3 Commutative REFUSAL + the accept-loop-still-launches green
// guard (the two together confirm the single-step predicate). Part A: a discarded
// `Commutative` (token-0-class) single step is refused (E3 — ResourceSerial only).
// Part B: the §B4 counter loop STILL launches under the UNIFIED E2 (same literal
// free-var disjointness as the sub-tree arm), using the DECOUPLED shape that hoists
// the control value out of the token operand. Adding the literal-disjointness E2
// must NOT weaken this §B4 launch (the synthetic concurrency_fanout guard).
#[test]
fn test_single_step_commutative_refused_but_counter_loop_still_launches() {
    let (tables, m) = fanout_tables();

    // Part A — Commutative single step refused (E3).
    let commutative = make_bind_expr(
        make_apply("cm", vec![make_var("n"), make_var("c"), make_var("f")]),
        "_",
        make_apply("recur", vec![]),
    );
    assert!(
        !matches!(
            transform_expr(commutative, &tables, &m),
            Expr::LaunchContinue { .. }
        ),
        "a discarded Commutative (token-0-class) single step must NOT launch (E3)"
    );

    // Part B — the §B4 counter loop STILL launches under the unified E2, via the
    // DECOUPLED shape (io free {n}, cont free {m} ⇒ disjoint ⇒ launches).
    let loop_result = transform_expr(decoupled_counter_loop("rd"), &tables, &m);
    assert_let_wraps_launch(&loop_result);
}

// spec: 10-io.md §10.12.7 / design/int/bind-chain-analysis.md §3.7 (FIXME 0478)
// — SINGLE-STEP E2 REFUSAL, ALIASED HANDLE (closes hole 1): a discarded
// `ResourceSerial` step `(wr conn r1)` whose continuation ALIASES the handle
// through a Let — `(let [c conn] (wr c r2))` — must NOT launch. The unified E2
// (literal free-var disjointness) sees `conn` free in BOTH io and continuation
// (the Let RHS) ⇒ refused. The retired narrow `continuation_shares_resource_handle`
// compared the launched leaf's leading operand against a continuation effect's
// LEADING operand only — `(wr c r2)`'s leading operand is `c`, not `conn` — so it
// MISSED the alias and wrongly launched (the soundness hole). RED-on-revert.
#[test]
fn test_no_single_step_launch_when_handle_aliased_in_continuation() {
    let (tables, m) = fanout_tables();
    // (bind (wr conn r1) (fn [_] (let [c conn] (wr c r2)))) — conn aliased to c.
    let cont = Expr::Let {
        bindings: vec![(Symbol::from("c"), make_var("conn"))],
        body: Box::new(make_apply("wr", vec![make_var("c"), make_var("r2")])),
        span: Span::SYNTHETIC,
        inferred_type: None,
    };
    let expr = make_bind_expr(
        make_apply("wr", vec![make_var("conn"), make_var("r1")]),
        "_",
        cont,
    );
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::LaunchContinue { .. }),
        "an aliased handle flowing into a same-token continuation effect must NOT \
             launch (E2 literal disjointness — hole 1 closed), got {result:?}"
    );
}

// spec: 10-io.md §10.12.7 / design/int/bind-chain-analysis.md §3.7 (FIXME 0478)
// — SINGLE-STEP E2 REFUSAL, USER-FN-WRAPPED HANDLE (closes hole 2): a discarded
// `(wr conn r1)` whose continuation passes the handle to a USER fn `(my-send conn
// r2)` (which does a same-token send internally) must NOT launch. The unified E2
// sees `conn` free in BOTH ⇒ refused. The retired narrow check scanned the
// continuation ONLY for direct `ResourceSerial` platform effects; a user-fn
// wrapper is opaque to it, so it MISSED the same-token flow and wrongly launched
// (the soundness hole). RED-on-revert.
#[test]
fn test_no_single_step_launch_when_handle_wrapped_in_user_fn() {
    let (tables, m) = fanout_tables();
    // (bind (wr conn r1) (fn [_] (my-send conn r2))) — my-send is a user defn that
    // performs a same-token send on `conn` (opaque to a leading-operand scan).
    let expr = make_bind_expr(
        make_apply("wr", vec![make_var("conn"), make_var("r1")]),
        "_",
        make_apply("my-send", vec![make_var("conn"), make_var("r2")]),
    );
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::LaunchContinue { .. }),
        "a handle passed to a user-fn wrapper in the continuation must NOT launch \
             (E2 literal disjointness — hole 2 closed), got {result:?}"
    );
}

// spec: 10-io.md §10.12.7 — SINGLE-STEP launch PERMITTED when the token operand is
// disjoint from the continuation (pins that the unified E2 does NOT over-refuse the
// legitimate §B4 accept-loop launch). The DECOUPLED shape `(let [m (sub-i64 n 1)]
// (bind (rd n c f) (fn [_] (recur m))))` keeps the loop control value `m` out of
// the token operand `n`: io free {n}, cont free {m} ⇒ disjoint ⇒ launches.
#[test]
fn test_launch_single_step_permitted_when_token_disjoint_from_continuation() {
    let (tables, m) = fanout_tables();
    let result = transform_expr(decoupled_counter_loop("rd"), &tables, &m);
    assert_let_wraps_launch(&result);
}

/// The exact serve-loop handler shape (S96 C4 / FIXME 0470): an inlined
/// `read → (sleep (slow-ms req)) → send` sub-tree over the fresh connection
/// token, with a `sleep` TIMER step in the middle (the C4 deterministic delay).
/// `read`/`send` are `ResourceSerial` poll leaves; the middle step is a direct
/// `(sleep <arg>)` call (the arg `(slow-ms req)` is a pure user fn — an
/// ARGUMENT, not an effect position).
fn handler_subtree_with_sleep() -> Expr {
    make_bind_expr(
        make_apply("rd", vec![make_var("t"), make_var("c"), make_var("f")]),
        "req",
        make_bind_expr(
            make_apply("sleep", vec![make_apply("slow-ms", vec![make_var("req")])]),
            "_",
            make_apply(
                "wr",
                vec![make_var("t"), make_var("c"), make_var("f"), make_var("req")],
            ),
        ),
    )
}

// spec: 10-io.md §10.12.7 — POSITIVE (the C4 / 0470 fix): a discarded handler
// sub-tree containing an inlined `(sleep …)` TIMER step launches as ONE strand.
// The C4 regression was that `(slow-delay req)` was a USER FN returning IO in
// an effect position (opaque footprint ⇒ E3 refusal). Reshaped to a direct
// `(sleep (slow-ms req))`, the timer is the §4.1 resource-free timer leaf and
// the whole handler launches. design: effect-concurrency.md §4.1 (timer refinement).
// RED-on-revert: reverting `is_sleep_timer_leaf` makes the sub-tree refuse (the
// sleep effect position is neither ResourceSerial nor a recognised leaf).
#[test]
fn test_launch_subtree_with_inlined_sleep_timer_step() {
    let (tables, m) = fanout_tables();
    let subtree = handler_subtree_with_sleep();
    let cont = make_apply("serve-loop", vec![make_var("listener")]);
    let expr = launch_outer(subtree, "_", cont);
    let result = transform_expr(expr, &tables, &m);
    let Expr::LaunchContinue { launched, .. } = &result else {
        panic!(
            "a discarded handler sub-tree with an inlined sleep timer step must \
                 LAUNCH (§4.1 timer refinement, 0470 fix), got {result:?}"
        );
    };
    // The launched handler runs as ONE strand: read→sleep→send are SEQUENTIAL
    // binds inside it — the inner sleep step must NOT be a nested LaunchContinue
    // (that would let `send` run before the delay, defeating it).
    assert!(
        is_bind_chain_start(launched),
        "the launched handler must be the read→sleep→send bind sub-tree, got {launched:?}"
    );
    let Expr::Apply { args, .. } = launched.as_ref() else {
        panic!("launched handler is not an Apply: {launched:?}");
    };
    let Expr::Lambda {
        body: read_body, ..
    } = &args[1]
    else {
        panic!("read step has no lambda body");
    };
    assert!(
        !matches!(read_body.as_ref(), Expr::LaunchContinue { .. }),
        "the inner sleep step must NOT independently launch (it must stay a \
             sequential bind inside the handler strand), got {read_body:?}"
    );
}

// spec: 10-io.md §10.12.7 — NEGATIVE: a LONE discarded `sleep` step does NOT
// single-step launch. The timer is launch-eligible only as a sub-tree MEMBER,
// never as the launched root (a detached lone sleep is pointless, and detaching
// a sleep the continuation relies on would run the continuation before the
// delay). design: effect-concurrency.md §4.1 (timer refinement — single-step arm
// keeps refusing sleep).
#[test]
fn test_no_single_step_launch_for_lone_sleep_step() {
    let (tables, m) = fanout_tables();
    // (bind (sleep 100) (fn [_] (recur))) — discarded, but a LONE sleep.
    let expr = make_bind_expr(
        make_apply("sleep", vec![make_int(100)]),
        "_",
        make_apply("recur", vec![]),
    );
    let result = transform_expr(expr, &tables, &m);
    assert!(
        !matches!(result, Expr::LaunchContinue { .. }),
        "a lone discarded sleep step must NOT single-step launch (timer is a \
             sub-tree member only), got {result:?}"
    );
}
