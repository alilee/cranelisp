    use super::*;

    #[test]
    fn test_ring0_primitive_count() {
        let prims = ring0_primitives();
        assert_eq!(
            prims.len(),
            27,
            "Ring 0 should define exactly 27 primitives (19 + eq-bool + 7 bitwise, FIXME 0416)"
        );
    }

    // spec: appendix-a-builtins §A.3 — bitwise integer ops (FIXME 0416, S91).
    // bit-and/bit-or/bit-xor/shl/shr are (Fn [Int Int] Int); bit-not/popcount
    // are (Fn [Int] Int).
    #[test]
    fn test_bitwise_types() {
        let prims = ring0_primitives();
        let binary = ["bit-and", "bit-or", "bit-xor", "shl", "shr"];
        let unary = ["bit-not", "popcount"];
        for name in binary {
            let p = prims.iter().find(|p| p.name.as_ref() == name).unwrap();
            assert_eq!(
                p.ty,
                Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
                "{name}: (Fn [Int Int] Int)"
            );
        }
        for name in unary {
            let p = prims.iter().find(|p| p.name.as_ref() == name).unwrap();
            assert_eq!(
                p.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                "{name}: (Fn [Int] Int)"
            );
        }
    }

    #[test]
    fn test_int_arithmetic_types() {
        let prims = ring0_primitives();
        let int_arith: Vec<_> = prims
            .iter()
            .filter(|p| ["add-i64", "sub-i64", "mul-i64", "div-i64"].contains(&p.name.as_ref()))
            .collect();
        assert_eq!(int_arith.len(), 4, "4 int arithmetic primitives");
        for p in &int_arith {
            match &p.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 2, "{} takes 2 params", p.name);
                    assert_eq!(params[0], Type::Int, "{} param[0] is Int", p.name);
                    assert_eq!(params[1], Type::Int, "{} param[1] is Int", p.name);
                    assert_eq!(**ret, Type::Int, "{} returns Int", p.name);
                }
                _ => panic!("{} should have Fn type", p.name),
            }
        }
    }

    #[test]
    fn test_float_arithmetic_types() {
        let prims = ring0_primitives();
        let float_arith: Vec<_> = prims
            .iter()
            .filter(|p| {
                ["add-f64", "sub-f64", "mul-f64", "div-f64"].contains(&p.name.as_ref())
            })
            .collect();
        assert_eq!(float_arith.len(), 4, "4 float arithmetic primitives");
        for p in &float_arith {
            match &p.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params[0], Type::Float, "{} param[0] is Float", p.name);
                    assert_eq!(params[1], Type::Float, "{} param[1] is Float", p.name);
                    assert_eq!(**ret, Type::Float, "{} returns Float", p.name);
                }
                _ => panic!("{} should have Fn type", p.name),
            }
        }
    }

    #[test]
    fn test_int_comparison_types() {
        let prims = ring0_primitives();
        let int_cmp: Vec<_> = prims
            .iter()
            .filter(|p| {
                ["eq-i64", "lt-i64", "gt-i64", "le-i64", "ge-i64"].contains(&p.name.as_ref())
            })
            .collect();
        assert_eq!(int_cmp.len(), 5, "5 int comparison primitives");
        for p in &int_cmp {
            match &p.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params[0], Type::Int, "{} param[0] is Int", p.name);
                    assert_eq!(params[1], Type::Int, "{} param[1] is Int", p.name);
                    assert_eq!(**ret, Type::Bool, "{} returns Bool", p.name);
                }
                _ => panic!("{} should have Fn type", p.name),
            }
        }
    }

    #[test]
    fn test_float_comparison_types() {
        let prims = ring0_primitives();
        let float_cmp: Vec<_> = prims
            .iter()
            .filter(|p| {
                ["eq-f64", "lt-f64", "gt-f64", "le-f64", "ge-f64"]
                    .contains(&p.name.as_ref())
            })
            .collect();
        assert_eq!(float_cmp.len(), 5, "5 float comparison primitives");
        for p in &float_cmp {
            match &p.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params[0], Type::Float, "{} param[0] is Float", p.name);
                    assert_eq!(params[1], Type::Float, "{} param[1] is Float", p.name);
                    assert_eq!(**ret, Type::Bool, "{} returns Bool", p.name);
                }
                _ => panic!("{} should have Fn type", p.name),
            }
        }
    }

    #[test]
    fn test_not_type() {
        let prims = ring0_primitives();
        let not = prims.iter().find(|p| p.name.as_ref() == "not").unwrap();
        assert_eq!(
            not.ty,
            Type::Fn(vec![Type::Bool], Box::new(Type::Bool)),
            "not: (Fn [Bool] Bool)"
        );
    }

    #[test]
    fn test_all_primitives_have_fn_type() {
        for p in ring0_primitives() {
            assert!(
                matches!(&p.ty, Type::Fn(_, _)),
                "primitive {} should have Fn type",
                p.name
            );
        }
    }

    #[test]
    fn test_all_primitives_have_param_names() {
        for p in ring0_primitives() {
            match &p.ty {
                Type::Fn(params, _) => {
                    assert_eq!(
                        p.param_names.len(),
                        params.len(),
                        "primitive {} param_names length must match param count",
                        p.name
                    );
                }
                _ => panic!("{} should have Fn type", p.name),
            }
        }
    }

    #[test]
    fn test_no_type_vars_in_primitives() {
        for p in ring0_primitives() {
            if let Type::Fn(params, ret) = &p.ty {
                for param in params {
                    assert!(
                        !matches!(param, Type::Var(_)),
                        "primitive {} should have no type vars, got {:?}",
                        p.name,
                        param
                    );
                }
                assert!(
                    !matches!(ret.as_ref(), Type::Var(_)),
                    "primitive {} return type should not be a Var",
                    p.name
                );
            }
        }
    }

    // spec: appendix-a-builtins §A.4 — ring3 primitives count
    #[test]
    fn test_ring3_primitive_count() {
        let prims = ring3_primitives();
        assert_eq!(prims.len(), 1, "Ring 3 should define exactly 1 primitive (quote-sexp)");
    }

    // spec: appendix-a-builtins §A.4 — quote-sexp type is (Fn [Sexp] Sexp)
    #[test]
    fn test_quote_sexp_type() {
        let prims = ring3_primitives();
        let qs = prims.iter().find(|p| p.name.as_ref() == "quote-sexp").unwrap();
        let sexp_type = Type::adt(ModuleFullPath::from("macros"), TypeName::from("Sexp"), vec![]);
        assert_eq!(
            qs.ty,
            Type::Fn(vec![sexp_type.clone()], Box::new(sexp_type)),
            "quote-sexp: (Fn [Sexp] Sexp)"
        );
    }
