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

