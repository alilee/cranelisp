    use super::*;

    /// Helper: parse source text into a single Sexp.
    fn parse_one(src: &str) -> Sexp {
        let sexps = crate::reader::parse(src).expect("parse failed");
        assert_eq!(sexps.len(), 1, "expected exactly one sexp");
        sexps.into_iter().next().unwrap()
    }

    /// Helper: check if a Sexp is a list whose head symbol matches `name`.
    fn is_list_headed_by(sexp: &Sexp, name: &str) -> bool {
        matches!(sexp, Sexp::List(ch, _) if !ch.is_empty()
            && matches!(&ch[0], Sexp::Symbol(s, _) if s == name))
    }

    /// Helper: recursively check if a symbol appears anywhere in a Sexp tree.
    fn contains_symbol(sexp: &Sexp, name: &str) -> bool {
        match sexp {
            Sexp::Symbol(s, _) => s == name,
            Sexp::List(children, _) | Sexp::Bracket(children, _) => {
                children.iter().any(|c| contains_symbol(c, name))
            }
            _ => false,
        }
    }

    // -- is_defmacro --

    // spec: 09-macros.md section 9.2.1 -- defmacro detection
    #[test]
    fn is_defmacro_positive() {
        let sexp = parse_one("(defmacro foo [x] x)");
        assert!(is_defmacro(&sexp));
    }

    // spec: 09-macros.md section 9.2.1 -- defmacro- detection
    #[test]
    fn is_defmacro_private_positive() {
        let sexp = parse_one("(defmacro- foo [x] x)");
        assert!(is_defmacro(&sexp));
    }

    // spec: 09-macros.md section 9.2.1 -- non-defmacro detection
    #[test]
    fn is_defmacro_negative() {
        let sexp = parse_one("(defn foo [x] x)");
        assert!(!is_defmacro(&sexp));
    }

    #[test]
    fn is_defmacro_negative_atom() {
        let sexp = parse_one("42");
        assert!(!is_defmacro(&sexp));
    }

    // -- is_begin --

    // spec: 09-macros.md section 9.6 -- begin detection
    #[test]
    fn is_begin_positive() {
        let sexp = parse_one("(begin 1 2 3)");
        assert!(is_begin(&sexp));
    }

    // spec: 09-macros.md section 9.6 -- non-begin detection
    #[test]
    fn is_begin_negative() {
        let sexp = parse_one("(defn foo [] 1)");
        assert!(!is_begin(&sexp));
    }

    // -- flatten_begin --

    // spec: 09-macros.md section 9.6 -- begin flattening
    #[test]
    fn flatten_begin_extracts_forms() {
        let sexp = parse_one("(begin 1 2 3)");
        let forms = flatten_begin(sexp);
        assert_eq!(forms.len(), 3);
        assert!(matches!(&forms[0], Sexp::Int(1, _)));
        assert!(matches!(&forms[1], Sexp::Int(2, _)));
        assert!(matches!(&forms[2], Sexp::Int(3, _)));
    }

    // spec: 09-macros.md section 9.6 -- nested begin flattening
    #[test]
    fn flatten_begin_nested() {
        let sexp = parse_one("(begin 1 (begin 2 3) 4)");
        let forms = flatten_begin(sexp);
        assert_eq!(forms.len(), 4);
    }

    // spec: 09-macros.md section 9.6 -- non-begin passthrough
    #[test]
    fn flatten_begin_non_begin() {
        let sexp = parse_one("42");
        let forms = flatten_begin(sexp);
        assert_eq!(forms.len(), 1);
        assert!(matches!(&forms[0], Sexp::Int(42, _)));
    }

    // -- parse_defmacro --

    // spec: 09-macros.md section 9.2.1 -- single-clause parse
    #[test]
    fn parse_single_clause() {
        let sexp = parse_one("(defmacro my-if [c t e] `(if ~c ~t ~e))");
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.name.as_ref(), "my-if");
        assert!(!info.is_private);
        assert!(info.docstring.is_none());
        assert_eq!(info.clauses.len(), 1);
        assert_eq!(info.clauses[0].fixed_params.len(), 3);
        assert!(info.clauses[0].rest_param.is_none());
    }

    // spec: 09-macros.md section 9.2.6 -- multi-clause parse
    #[test]
    fn parse_multi_clause() {
        // Note: reimplemented reader parses `&rest` as a single symbol "&rest"
        let sexp = parse_one("(defmacro cond ([x] x) ([x body &rest] `(if ~x ~body (cond ~@rest))))");
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.name.as_ref(), "cond");
        assert_eq!(info.clauses.len(), 2);
        // First clause: 1 fixed param, no rest
        assert_eq!(info.clauses[0].fixed_params.len(), 1);
        assert!(info.clauses[0].rest_param.is_none());
        // Second clause: 2 fixed params + rest
        assert_eq!(info.clauses[1].fixed_params.len(), 2);
        assert!(info.clauses[1].rest_param.is_some());
    }

    // spec: 09-macros.md section 9.2.2 -- rest parameter parse (no space)
    #[test]
    fn parse_rest_param() {
        // Reader parses `&args` as a single symbol "&args"
        let sexp = parse_one("(defmacro my-add [&args] `(+ ~@args))");
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.clauses[0].fixed_params.len(), 0);
        assert_eq!(info.clauses[0].rest_param.as_ref().unwrap().as_ref(), "args");
    }

    // spec: 09-macros.md section 9.2.2 -- rest parameter parse (with space)
    #[test]
    fn parse_rest_param_with_space() {
        // Reader now accepts `& args` (with space) — Clojure convention
        let sexp = parse_one("(defmacro my-add [& args] `(+ ~@args))");
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.clauses[0].fixed_params.len(), 0);
        assert_eq!(info.clauses[0].rest_param.as_ref().unwrap().as_ref(), "args");
    }

    // spec: 09-macros.md section 9.2.3 -- variadic multi-clause with & rest (with space)
    #[test]
    fn parse_multi_clause_rest_with_space() {
        let sexp = parse_one("(defmacro my-cond ([x] x) ([x body & rest] `(if ~x ~body (my-cond ~@rest))))");
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.clauses.len(), 2);
        assert_eq!(info.clauses[1].fixed_params.len(), 2);
        assert!(info.clauses[1].rest_param.is_some());
        assert_eq!(info.clauses[1].rest_param.as_ref().unwrap().as_ref(), "rest");
    }

    // spec: 09-macros.md section 9.2.4 -- docstring extraction
    #[test]
    fn parse_docstring() {
        // Note: reimplemented reader parses `&elems` as a single symbol "&elems"
        let sexp = parse_one("(defmacro list \"Construct a list\" [&elems] `Nil)");
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.docstring.as_deref(), Some("Construct a list"));
    }

    // spec: 09-macros.md section 9.2.1 -- private macro
    #[test]
    fn parse_private_macro() {
        let sexp = parse_one("(defmacro- internal [x] x)");
        let info = parse_defmacro(&sexp).unwrap();
        assert!(info.is_private);
    }

    // spec: 09-macros.md section 9.2.7 -- bracket destructure parameter
    #[test]
    fn parse_bracket_destructure() {
        let sexp = parse_one("(defmacro my-let [[name expr] body] `(let [~name ~expr] ~body))");
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.clauses[0].fixed_params.len(), 2);
        match &info.clauses[0].fixed_params[0] {
            MacroParam::Bracket { fixed, rest } => {
                assert_eq!(fixed.len(), 2);
                assert_eq!(fixed[0].as_ref(), "name");
                assert_eq!(fixed[1].as_ref(), "expr");
                assert!(rest.is_none());
            }
            _ => panic!("expected bracket param"),
        }
        match &info.clauses[0].fixed_params[1] {
            MacroParam::Name(n) => assert_eq!(n.as_ref(), "body"),
            _ => panic!("expected name param"),
        }
    }

    // -- synthesize_macro_clause_defn --

    // spec: 09-macros.md section 9.2 -- synthesized defn structure
    #[test]
    fn synthesize_simple_clause() {
        let clause = MacroClause {
            fixed_params: vec![
                MacroParam::Name("a".into()),
                MacroParam::Name("b".into()),
            ],
            rest_param: None,
            body_sexp: Sexp::Symbol("a".to_string(), Span::SYNTHETIC),
        };
        let result = synthesize_macro_clause_defn("test", 0, &clause, Span::SYNTHETIC);

        // Should be (defn- __macro_test_clause_0 [...] (match ...))
        assert!(is_list_headed_by(&result, "defn-"));
        // Check function name
        if let Sexp::List(ch, _) = &result {
            assert!(matches!(&ch[1], Sexp::Symbol(s, _) if s == "__macro_test_clause_0"));
            // Should have nested match chain with macros/SCons patterns
            assert!(contains_symbol(&result, "macros/SCons"));
            assert!(contains_symbol(&result, "match"));
        }
    }

    // spec: 09-macros.md section 9.2 -- zero-arg clause
    #[test]
    fn synthesize_zero_arg_clause() {
        let clause = MacroClause {
            fixed_params: vec![],
            rest_param: None,
            body_sexp: Sexp::Int(42, Span::SYNTHETIC),
        };
        let result = synthesize_macro_clause_defn("const", 0, &clause, Span::SYNTHETIC);

        // Should be (defn- __macro_const_clause_0 [...] 42)
        assert!(is_list_headed_by(&result, "defn-"));
        // Body should be the integer directly (no match chain)
        if let Sexp::List(ch, _) = &result {
            // ch[3] is the body
            assert!(matches!(&ch[3], Sexp::Int(42, _)));
        }
    }

    // spec: 09-macros.md section 9.2.2 -- rest param in synthesized defn
    #[test]
    fn synthesize_rest_param_clause() {
        let clause = MacroClause {
            fixed_params: vec![MacroParam::Name("x".into())],
            rest_param: Some("rest".into()),
            body_sexp: Sexp::Symbol("x".to_string(), Span::SYNTHETIC),
        };
        let result = synthesize_macro_clause_defn("thread", 0, &clause, Span::SYNTHETIC);

        // The match chain should bind rest directly as the tail
        assert!(contains_symbol(&result, "rest"));
        assert!(contains_symbol(&result, "macros/SCons"));
    }

    // spec: 09-macros.md section 9.2.7 -- bracket destructure in synthesized defn
    #[test]
    fn synthesize_bracket_destructure_clause() {
        let clause = MacroClause {
            fixed_params: vec![
                MacroParam::Bracket {
                    fixed: vec!["x".into(), "y".into()],
                    rest: None,
                },
                MacroParam::Name("body".into()),
            ],
            rest_param: None,
            body_sexp: Sexp::Symbol("body".to_string(), Span::SYNTHETIC),
        };
        let result = synthesize_macro_clause_defn("mylet", 0, &clause, Span::SYNTHETIC);

        // Should contain SexpBracket pattern for bracket destructuring
        assert!(contains_symbol(&result, "macros/SexpBracket"));
        // Inner bindings should use __inner_t prefixed names (not __t)
        // The main param chain should use __t or direct bindings
        assert!(contains_symbol(&result, "macros/SCons"));
    }

    // -- Type annotation in synthesized param --

    // spec: 09-macros.md section 9.2 -- param type annotation
    #[test]
    fn synthesize_has_slist_sexp_annotation() {
        let clause = MacroClause {
            fixed_params: vec![MacroParam::Name("x".into())],
            rest_param: None,
            body_sexp: Sexp::Symbol("x".to_string(), Span::SYNTHETIC),
        };
        let result = synthesize_macro_clause_defn("test", 0, &clause, Span::SYNTHETIC);

        // The param bracket contains the reader-folded annotation shape, with
        // the FQ element type required for cross-module resolution.
        let Sexp::List(defn, _) = result else {
            panic!("expected synthesized defn list");
        };
        let Sexp::Bracket(params, _) = &defn[2] else {
            panic!("expected synthesized parameter bracket");
        };
        assert_eq!(params.len(), 1);
        let Sexp::Annotated {
            annotation,
            subject,
            ..
        } = &params[0]
        else {
            panic!("expected structural parameter annotation");
        };
        assert!(matches!(
            annotation.as_ref(),
            Sexp::List(items, _) if matches!(items.as_slice(),
                [Sexp::Symbol(list, _), Sexp::Symbol(element, _)]
                    if list == "macros/SList" && element == "macros/Sexp")
        ));
        assert!(matches!(subject.as_ref(), Sexp::Symbol(name, _) if name == "__args__"));
    }

    // -------------------------------------------------------------------
    // Rendered-diagnostic tier (FIXME 0500)
    //
    // `parse_defmacro` emits ParseError diagnostics for malformed defmacro
    // forms. This tier guards the P6 class (0485): a real source span, the
    // defmacro requirement named, and NO Debug-format struct dump in the
    // user-facing text. Submodule × scenario-class per METHOD §2.2.
    // spec: repl/spec.md §"Self-documenting REPL" — no opaque errors.
    // -------------------------------------------------------------------
    mod rendered_diagnostics {
        use super::*;

        const SYNTHETIC_SPAN_BASE: u32 = 1_000_000;

        fn err(src: &str) -> cranelisp_types::CranelispError {
            let sexp = parse_one(src);
            parse_defmacro(&sexp).expect_err("expected a defmacro error")
        }

        fn assert_real_span(e: &cranelisp_types::CranelispError, src: &str) {
            let s = e.span();
            assert!(
                s.start < SYNTHETIC_SPAN_BASE && s.end < SYNTHETIC_SPAN_BASE,
                "defmacro diagnostic carries a synthetic span {s}: {}",
                e.message(),
            );
            assert!(
                s.end as usize <= src.len(),
                "defmacro span {s} exceeds source length {} for {src:?}",
                src.len(),
            );
        }

        fn assert_no_debug_artifacts(e: &cranelisp_types::CranelispError) {
            let m = e.message();
            assert!(!m.contains("Span {"), "message leaks a Debug span struct: {m}");
            assert!(!m.contains("Sexp::"), "message leaks a Debug Sexp variant: {m}");
            assert!(!m.contains("ErrorLocation"), "message leaks ErrorLocation: {m}");
        }

        // -- positive: too-few-forms names the defmacro requirement --

        // spec: 07-macros §7.1 — defmacro requires a name and clause.
        #[test]
        fn defmacro_too_few_names_requirement_with_real_span() {
            let e = err("(defmacro)");
            assert!(e.message().contains("defmacro"), "got: {}", e.message());
            assert_real_span(&e, "(defmacro)");
            assert_no_debug_artifacts(&e);
        }

        // -- edge: non-symbol name is diagnosed --

        // spec: 07-macros §7.1 — defmacro name must be a symbol.
        #[test]
        fn defmacro_non_symbol_name_is_diagnosed_cleanly() {
            let e = err("(defmacro 5 [] 1)");
            assert!(
                e.message().contains("name must be a symbol"),
                "got: {}",
                e.message(),
            );
            assert_real_span(&e, "(defmacro 5 [] 1)");
            assert_no_debug_artifacts(&e);
        }

        // -- negative: no internal artifacts leak across a spread of shapes --

        #[test]
        fn no_defmacro_diagnostic_leaks_debug_or_synthetic_span() {
            for src in ["(defmacro)", "(defmacro foo)", "(defmacro 5 [] 1)"] {
                let e = err(src);
                assert_no_debug_artifacts(&e);
                assert_real_span(&e, src);
            }
        }
    }
