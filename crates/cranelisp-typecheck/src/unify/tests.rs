    use super::*;
    use cranelisp_types::{FQTypeName, ModuleFullPath, TypeName};

    /// Test helper: create an FQTypeName in a "test" module.
    fn test_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("test"), TypeName::from(name))
    }

    // spec: 03-types §3.8.1 — trivial unification of identical primitives
    #[test]
    fn test_unify_same_primitives() {
        let mut subst = Subst::new();
        assert!(unify(&mut subst, &Type::Int, &Type::Int).is_ok());
        assert!(unify(&mut subst, &Type::Bool, &Type::Bool).is_ok());
        assert!(unify(&mut subst, &Type::Float, &Type::Float).is_ok());
        assert!(unify(&mut subst, &Type::String, &Type::String).is_ok());
    }

    // spec: 03-types §3.8.6 — incompatible primitive types fail unification
    #[test]
    fn test_unify_different_primitives_fails() {
        let mut subst = Subst::new();
        assert!(unify(&mut subst, &Type::Int, &Type::Bool).is_err());
        assert!(unify(&mut subst, &Type::Float, &Type::String).is_err());
    }

    // spec: repl/spec.md §5.3 — a type-mismatch error names BOTH the expected and
    // actual type FULLY QUALIFIED (`primitives/Int`, not bare `Int`). Pins the
    // FQ-qualification at the unify error-renderer seam (design typecheck.md §8.3),
    // independent of the REPL stack.
    #[test]
    fn test_type_mismatch_message_is_fully_qualified() {
        let mut subst = Subst::new();
        let err = unify(&mut subst, &Type::Int, &Type::String).unwrap_err();
        let msg = err.message();
        assert!(
            msg.contains("primitives/Int"),
            "expected type must be FQ (`primitives/Int`); got: {msg}"
        );
        assert!(
            msg.contains("primitives/String"),
            "actual type must be FQ (`primitives/String`); got: {msg}"
        );
    }

    // spec: 03-types §3.8.2 — variable binding: Var(id) binds to concrete type
    #[test]
    fn test_unify_var_with_concrete() {
        let mut subst = Subst::new();
        unify(&mut subst, &Type::Var(0), &Type::Int).unwrap();
        assert_eq!(apply(&subst, &Type::Var(0)), Type::Int);
    }

    // spec: 03-types §3.8.2 — variable binding is symmetric
    #[test]
    fn test_unify_concrete_with_var() {
        let mut subst = Subst::new();
        unify(&mut subst, &Type::Int, &Type::Var(0)).unwrap();
        assert_eq!(apply(&subst, &Type::Var(0)), Type::Int);
    }

    // spec: 03-types §3.8.2 — two distinct type variables unify by merging
    #[test]
    fn test_unify_var_with_var() {
        let mut subst = Subst::new();
        unify(&mut subst, &Type::Var(0), &Type::Var(1)).unwrap();
        // One should be bound to the other
        let t0 = apply(&subst, &Type::Var(0));
        let t1 = apply(&subst, &Type::Var(1));
        assert_eq!(t0, t1);
    }

    // spec: 03-types §3.8.2 — same variable unifies with itself (no-op)
    #[test]
    fn test_unify_var_with_self() {
        let mut subst = Subst::new();
        // Var(0) unifying with Var(0) is ok (no binding needed)
        assert!(unify(&mut subst, &Type::Var(0), &Type::Var(0)).is_ok());
        assert!(subst.is_empty());
    }

    // spec: 03-types §3.8.3 — function types unify pairwise by params and return
    #[test]
    fn test_unify_fn_types() {
        let mut subst = Subst::new();
        let fn1 = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
        let fn2 = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
        assert!(unify(&mut subst, &fn1, &fn2).is_ok());
    }

    // spec: 03-types §3.8.3 — function type unification resolves type variables
    #[test]
    fn test_unify_fn_types_with_vars() {
        let mut subst = Subst::new();
        let fn1 = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(1)));
        let fn2 = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
        unify(&mut subst, &fn1, &fn2).unwrap();
        assert_eq!(apply(&subst, &Type::Var(0)), Type::Int);
        assert_eq!(apply(&subst, &Type::Var(1)), Type::Bool);
    }

    // spec: 03-types §3.8.3 — function arity mismatch fails unification
    #[test]
    fn test_unify_fn_arity_mismatch() {
        let mut subst = Subst::new();
        let fn1 = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let fn2 = Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int));
        let err = unify(&mut subst, &fn1, &fn2).unwrap_err();
        assert!(err.message().contains("arity mismatch"));
    }

    // spec: 03-types §3.8.4 — ADTs with same name unify
    #[test]
    fn test_unify_adt_same_name() {
        let mut subst = Subst::new();
        let a1 = Type::ADT(test_fqtn("Color"), vec![]);
        let a2 = Type::ADT(test_fqtn("Color"), vec![]);
        assert!(unify(&mut subst, &a1, &a2).is_ok());
    }

    // spec: 03-types §3.8.4 — ADTs with different names fail unification
    #[test]
    fn test_unify_adt_different_names() {
        let mut subst = Subst::new();
        let a1 = Type::ADT(test_fqtn("Color"), vec![]);
        let a2 = Type::ADT(test_fqtn("Shape"), vec![]);
        let err = unify(&mut subst, &a1, &a2).unwrap_err();
        assert!(err.message().contains("Color"));
        assert!(err.message().contains("Shape"));
    }

    // spec: 03-types §3.8.2 — occurs check prevents infinite types
    #[test]
    fn test_occurs_check_prevents_infinite_type() {
        let mut subst = Subst::new();
        // t0 = Fn([t0], t0) would be infinite
        let infinite_fn = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0)));
        let err = unify(&mut subst, &Type::Var(0), &infinite_fn).unwrap_err();
        assert!(err.message().contains("infinite type"));
    }

    // spec: 03-types §3.8.2 — occurs check detects variable in function type
    #[test]
    fn test_occurs_check_function() {
        let subst = Subst::new();
        let ty = Type::Fn(vec![Type::Var(0)], Box::new(Type::Int));
        assert!(occurs_check(&subst, 0, &ty));
        assert!(!occurs_check(&subst, 1, &ty));
    }

    // spec: 03-types §3.5.1 — fresh_var creates unique unification variables
    #[test]
    fn test_fresh_var() {
        let mut next_id: TypeId = 0;
        let t1 = fresh_var(&mut next_id);
        let t2 = fresh_var(&mut next_id);
        assert_eq!(t1, Type::Var(0));
        assert_eq!(t2, Type::Var(1));
        assert_eq!(next_id, 2);
    }

    // spec: 03-types §3.5.1 — fresh_var_id returns both type and id
    #[test]
    fn test_fresh_var_id() {
        let mut next_id: TypeId = 5;
        let (ty, id) = fresh_var_id(&mut next_id);
        assert_eq!(ty, Type::Var(5));
        assert_eq!(id, 5);
        assert_eq!(next_id, 6);
    }

    // spec: 03-types §3.5.1 — apply resolves transitive variable chains
    #[test]
    fn test_unify_transitive_vars() {
        let mut subst = Subst::new();
        // t0 = t1, t1 = Int => t0 = Int
        unify(&mut subst, &Type::Var(0), &Type::Var(1)).unwrap();
        unify(&mut subst, &Type::Var(1), &Type::Int).unwrap();
        assert_eq!(apply(&subst, &Type::Var(0)), Type::Int);
    }

    // spec: 03-types §3.8.3 — function param type mismatch fails unification
    #[test]
    fn test_unify_fn_param_type_mismatch() {
        let mut subst = Subst::new();
        let fn1 = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let fn2 = Type::Fn(vec![Type::Bool], Box::new(Type::Int));
        assert!(unify(&mut subst, &fn1, &fn2).is_err());
    }
