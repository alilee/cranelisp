    use super::*;
    use cranelisp_types::Type;

    fn mono(ty: Type) -> Scheme {
        Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty,
        }
    }

    // spec: 03-types §3.5.3 — variable reference looks up name in environment
    #[test]
    fn test_basic_lookup() {
        let mut stack = ScopeStack::new();
        stack.bind(Symbol::from("x"), mono(Type::Int));
        assert_eq!(stack.lookup("x").unwrap().ty, Type::Int);
    }

    // spec: 04-expressions §4.2 — let bindings shadow outer scope
    #[test]
    fn test_shadowing() {
        let mut stack = ScopeStack::new();
        stack.bind(Symbol::from("x"), mono(Type::Int));
        stack.push_scope();
        stack.bind(Symbol::from("x"), mono(Type::Bool));
        assert_eq!(stack.lookup("x").unwrap().ty, Type::Bool);
        stack.pop_scope();
        assert_eq!(stack.lookup("x").unwrap().ty, Type::Int);
    }

    // spec: 03-types §3.5.3 — inner scope sees outer bindings; outer does not see inner
    #[test]
    fn test_lookup_outer_scope() {
        let mut stack = ScopeStack::new();
        stack.bind(Symbol::from("x"), mono(Type::Int));
        stack.push_scope();
        stack.bind(Symbol::from("y"), mono(Type::Bool));
        // Can still see x from outer scope
        assert_eq!(stack.lookup("x").unwrap().ty, Type::Int);
        assert_eq!(stack.lookup("y").unwrap().ty, Type::Bool);
        stack.pop_scope();
        assert!(stack.lookup("y").is_none());
    }

    // spec: 03-types §3.5.3 — unbound variable lookup returns None
    #[test]
    fn test_lookup_not_found() {
        let stack = ScopeStack::new();
        assert!(stack.lookup("x").is_none());
    }

    // spec: 03-types §3.5.1 — free vars in env excludes quantified scheme vars
    #[test]
    fn test_free_vars_in_env() {
        let mut stack = ScopeStack::new();
        // x : t0  (monomorphic -- t0 is free in env)
        stack.bind(Symbol::from("x"), mono(Type::Var(0)));
        let fv = stack.free_vars_in_env();
        assert!(fv.contains(&0));

        // y : forall [t1]. t1 -> t1  (t1 is quantified, not free)
        stack.bind(
            Symbol::from("y"),
            Scheme {
                type_vars: vec![1],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![Type::Var(1)], Box::new(Type::Var(1))),
            },
        );
        let fv = stack.free_vars_in_env();
        assert!(fv.contains(&0));
        assert!(!fv.contains(&1));
    }

    // -------------------------------------------------------------------
    // Negative / edge cells (S102 FIXME 0497 gap-fill — scope.rs was
    // happy-path-only). {edge, negative} for the scope-stack seams.
    // -------------------------------------------------------------------

    // spec: 03-types §3.5.3 — NEGATIVE: popping the base (module-level) frame is
    // a logic error and trips the invariant `debug_assert`. `pop_scope` must be
    // balanced against `push_scope`; the base frame is never popped.
    #[test]
    #[should_panic(expected = "cannot pop the base scope frame")]
    fn pop_base_frame_panics() {
        let mut stack = ScopeStack::new();
        // One frame (the base) — popping it violates the invariant.
        stack.pop_scope();
    }

    // spec: 04-expressions §4.2 — edge: re-binding the same name in the SAME
    // frame overwrites (last write wins) — this is redefinition within a scope,
    // distinct from shadowing across a pushed frame.
    #[test]
    fn bind_same_name_same_frame_overwrites() {
        let mut stack = ScopeStack::new();
        stack.bind(Symbol::from("x"), mono(Type::Int));
        stack.bind(Symbol::from("x"), mono(Type::Bool));
        assert_eq!(
            stack.lookup("x").unwrap().ty,
            Type::Bool,
            "same-frame re-bind overwrites (no pushed frame)"
        );
    }

    // spec: 03-types §3.5.1 — edge: `free_vars_in_env` unions across ALL frames,
    // and a var quantified by an inner-frame scheme is still excluded (it is not
    // free), while a free var bound in an outer frame is included.
    #[test]
    fn free_vars_in_env_spans_multiple_frames() {
        let mut stack = ScopeStack::new();
        // Outer frame: a : t0  (monomorphic — t0 is free in env)
        stack.bind(Symbol::from("a"), mono(Type::Var(0)));
        stack.push_scope();
        // Inner frame: b : forall [t1]. t1 -> t1  (t1 quantified, not free)
        stack.bind(
            Symbol::from("b"),
            Scheme {
                type_vars: vec![1],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![Type::Var(1)], Box::new(Type::Var(1))),
            },
        );
        let fv = stack.free_vars_in_env();
        assert!(fv.contains(&0), "outer-frame free var is in env");
        assert!(!fv.contains(&1), "inner-frame quantified var is NOT free");
    }

