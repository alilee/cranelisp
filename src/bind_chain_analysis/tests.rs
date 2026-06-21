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
        // (primitives/bind (get-time) (fn [t1] 0)) — single step, demoted to
        // Sequential during rebuild.
        let expr = make_bind_expr_with_callee(
            "primitives/bind",
            make_apply("get-time", vec![]),
            "t1",
            make_int(0),
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
        assert!(matches!(once, Expr::ParBind { .. }), "first pass should ParBind");
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
        //       (bind (get-time)     (fn [d] 0))))))))
        let l4 = make_bind_expr(make_apply("get-time", vec![]), "d", make_int(0));
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
        let inner = make_bind_expr(
            make_apply("http-get", vec![let_expr]),
            "t2",
            make_int(0),
        );
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
