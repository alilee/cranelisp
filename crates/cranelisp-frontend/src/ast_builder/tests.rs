    use super::*;

    fn build_name_type(name: &str) -> TypeExpr {
        build_type_expr(&Sexp::Symbol(name.into(), Span::SYNTHETIC)).unwrap()
    }

    use cranelisp_types::TopLevel;

    /// Test-only adapter: builds a synthetic batch program from one or more
    /// source forms by calling `build_form`/`build_expr` and re-packaging the
    /// resulting `ParsedEntry` values into the legacy `Vec<TopLevel>` shape
    /// the existing assertions match against. The orchestrator now owns this
    /// re-packaging at runtime; the adapter exists only to preserve test
    /// surface during the Wave 3a-β cutover.
    type Program = Vec<TopLevel>;

    fn parsed_entry_to_top_level(entry: ParsedEntry) -> TopLevel {
        use cranelisp_types::Defn;
        match entry {
            ParsedEntry::Def {
                name,
                variants,
                visibility,
                docstring,
                span,
            } => TopLevel::Defn(Defn {
                name,
                docstring,
                variants,
                visibility,
                span,
            }),
            ParsedEntry::TypeDef {
                name,
                type_params,
                constructors,
                visibility,
                docstring,
                span,
            } => {
                // The legacy TopLevel::TypeDef carries type_params as Vec<Symbol>.
                let type_params_as_symbols: Vec<Symbol> = type_params
                    .into_iter()
                    .map(|t| Symbol::from(t.as_ref()))
                    .collect();
                TopLevel::TypeDef {
                    name,
                    docstring,
                    type_params: type_params_as_symbols,
                    constructors,
                    visibility,
                    span,
                }
            }
            ParsedEntry::TraitDecl { decl } => TopLevel::TraitDecl(decl),
            ParsedEntry::TraitImpl { impl_ } => TopLevel::TraitImpl(impl_),
            ParsedEntry::Macro { .. } | ParsedEntry::Constructor { .. } => {
                unreachable!(
                    "test adapter: parser-only entries (Macro/Constructor) should not appear in TopLevel-shaped assertions"
                )
            }
            _ => unreachable!("test adapter: unknown ParsedEntry variant"),
        }
    }

    /// Route through the PRODUCTION classifier so the test adapter cannot drift
    /// from the prod router (FIXME 0678, audit R3). The former verbatim head-list
    /// mirror is deleted — this delegates to `is_top_level_form_sexp` /
    /// `classify_head`, the single source of the top-level head vocabulary.
    fn is_top_level_form(sexp: &Sexp) -> bool {
        super::is_top_level_form_sexp(sexp)
    }

    fn parse_and_build_program(input: &str) -> Result<Program, CranelispError> {
        let sexps = crate::reader::parse(input)?;
        let mut out = Vec::new();
        for s in sexps {
            if matches!(s, Sexp::Comment(_, _)) {
                continue;
            }
            if is_top_level_form(&s) {
                // Top-level form: route through build_form and propagate
                // errors. Drop per-deftype Constructor entries — they were
                // not in the legacy `Program` shape; the TypeDef entry
                // alone carries the constructor list inline for assertion.
                let entries = build_form(&s)?;
                for entry in entries {
                    if matches!(entry, ParsedEntry::Constructor { .. }) {
                        continue;
                    }
                    out.push(parsed_entry_to_top_level(entry));
                }
            } else {
                let expr = build_expr(&s)?;
                out.push(TopLevel::Expr(expr));
            }
        }
        Ok(out)
    }

    fn parse_and_build_repl(input: &str) -> Result<TopLevel, CranelispError> {
        let sexps = crate::reader::parse(input)?;
        assert!(!sexps.is_empty(), "expected at least one sexp");
        if is_top_level_form(&sexps[0]) {
            let mut entries = build_form(&sexps[0])?;
            entries.retain(|e| !matches!(e, ParsedEntry::Constructor { .. }));
            assert!(!entries.is_empty(), "expected at least one TopLevel-shaped entry");
            Ok(parsed_entry_to_top_level(entries.remove(0)))
        } else {
            let expr = build_expr(&sexps[0])?;
            Ok(TopLevel::Expr(expr))
        }
    }

    fn parse_and_build_expr(input: &str) -> Result<Expr, CranelispError> {
        let sexps = crate::reader::parse(input)?;
        assert!(!sexps.is_empty(), "expected at least one sexp");
        build_expr(&sexps[0])
    }

    // spec: spec/04-expressions.md §4.5 (0575) — `fn` is SINGLE-arity; the
    // parenthesised multi-arity clause form `(fn ([p] …) ([p q] …))` is
    // defn-only. The parse error MUST name that constraint (single-arity + defn),
    // not the misleading "requires param list and body" (which reads as if `fn`
    // got no params). Message-construction seam test.
    #[test]
    fn fn_multi_arity_clause_form_names_single_arity_and_defn() {
        let err = parse_and_build_expr("(fn ([x] x) ([x y] x))")
            .expect_err("the multi-arity `fn` clause form is rejected (§4.5)");
        let msg = err.to_string();
        assert!(
            msg.contains("single-arity"),
            "the error names `fn` as single-arity; got: {msg}"
        );
        assert!(
            msg.contains("defn"),
            "the error points at `defn` for multiple arities; got: {msg}"
        );
        // A well-formed single-arity fn still builds.
        assert!(parse_and_build_expr("(fn [x] x)").is_ok());
    }

    // -- Literals --

    // spec: 02-grammar §2.3.1 — integer literal expression
    #[test]
    fn test_build_integer_literal() {
        match parse_and_build_expr("42").unwrap() {
            Expr::IntLit { value, .. } => assert_eq!(value, 42),
            other => panic!("expected IntLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.1 — negative integer literal expression
    #[test]
    fn test_build_negative_integer() {
        match parse_and_build_expr("-7").unwrap() {
            Expr::IntLit { value, .. } => assert_eq!(value, -7),
            other => panic!("expected IntLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.1 — float literal expression
    #[test]
    fn test_build_float_literal() {
        match parse_and_build_expr("2.72").unwrap() {
            Expr::FloatLit { value, .. } => assert!((value - 2.72).abs() < 1e-10),
            other => panic!("expected FloatLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.1 — boolean literal expression
    #[test]
    fn test_build_bool_literal() {
        match parse_and_build_expr("true").unwrap() {
            Expr::BoolLit { value, .. } => assert!(value),
            other => panic!("expected BoolLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.1 — string literal expression
    #[test]
    fn test_build_string_literal() {
        match parse_and_build_expr("\"hello\"").unwrap() {
            Expr::StringLit { value, .. } => assert_eq!(value, "hello"),
            other => panic!("expected StringLit, got {other:?}"),
        }
    }

    // -- Variable reference --

    // spec: 02-grammar §2.3.2 — variable reference
    #[test]
    fn test_build_variable() {
        match parse_and_build_expr("foo").unwrap() {
            Expr::Var { name, .. } => assert_eq!(name, "foo"),
            other => panic!("expected Var, got {other:?}"),
        }
    }

    // -- Let expression --

    // spec: 02-grammar §2.3.3 — let expression with single binding
    #[test]
    fn test_build_let() {
        match parse_and_build_expr("(let [x 42] x)").unwrap() {
            Expr::Let {
                bindings, body, ..
            } => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "x");
                match &bindings[0].1 {
                    Expr::IntLit { value, .. } => assert_eq!(*value, 42),
                    other => panic!("expected IntLit in binding, got {other:?}"),
                }
                match body.as_ref() {
                    Expr::Var { name, .. } => assert_eq!(name, "x"),
                    other => panic!("expected Var in body, got {other:?}"),
                }
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.3 — let expression with multiple bindings
    #[test]
    fn test_build_let_multiple_bindings() {
        match parse_and_build_expr("(let [x 1 y 2] (+ x y))").unwrap() {
            Expr::Let { bindings, .. } => {
                assert_eq!(bindings.len(), 2);
                assert_eq!(bindings[0].0, "x");
                assert_eq!(bindings[1].0, "y");
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.3 — let requires body expression
    #[test]
    fn test_build_let_wrong_arity() {
        assert!(parse_and_build_expr("(let [x 1])").is_err());
    }

    // -- If expression --

    // spec: 02-grammar §2.3.4 — if expression with three sub-expressions
    #[test]
    fn test_build_if() {
        match parse_and_build_expr("(if true 1 0)").unwrap() {
            Expr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                assert!(matches!(cond.as_ref(), Expr::BoolLit { value: true, .. }));
                assert!(matches!(then_branch.as_ref(), Expr::IntLit { value: 1, .. }));
                assert!(matches!(
                    else_branch.as_ref(),
                    Expr::IntLit { value: 0, .. }
                ));
            }
            other => panic!("expected If, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.4 — if requires exactly three sub-expressions
    #[test]
    fn test_build_if_wrong_arity() {
        assert!(parse_and_build_expr("(if true 1)").is_err());
    }

    // -- Lambda expression --

    // spec: 02-grammar §2.3.5 — fn lambda expression
    #[test]
    fn test_build_lambda() {
        match parse_and_build_expr("(fn [x] x)").unwrap() {
            Expr::Lambda { params, body, .. } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].0, "x");
                match body.as_ref() {
                    Expr::Var { name, .. } => assert_eq!(name, "x"),
                    other => panic!("expected Var, got {other:?}"),
                }
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.5 — lambda keyword alias for fn
    #[test]
    fn test_build_lambda_with_lambda_keyword() {
        match parse_and_build_expr("(lambda [x] x)").unwrap() {
            Expr::Lambda { params, .. } => {
                assert_eq!(params.len(), 1);
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.8.2 — annotated parameter in lambda
    #[test]
    fn test_build_lambda_annotated_params() {
        match parse_and_build_expr("(fn [:Int x] x)").unwrap() {
            Expr::Lambda { params, .. } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].0, "x");
                assert!(params[0].1.is_some());
                match params[0].1.as_ref().unwrap() {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                    other => panic!("expected Named(Int), got {other:?}"),
                }
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    // -- Apply expression --

    // spec: 02-grammar §2.3.6 — function application
    #[test]
    fn test_build_apply() {
        match parse_and_build_expr("(+ 1 2)").unwrap() {
            Expr::Apply {
                callee, args, ..
            } => {
                match callee.as_ref() {
                    Expr::Var { name, .. } => assert_eq!(name, "+"),
                    other => panic!("expected Var, got {other:?}"),
                }
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.8 — type annotation in function argument
    #[test]
    fn test_build_apply_with_annotation() {
        // (f :Int 42) -> Apply(f, [Annotate(:Int, 42)])
        match parse_and_build_expr("(f :Int 42)").unwrap() {
            Expr::Apply { args, .. } => {
                assert_eq!(args.len(), 1);
                match &args[0] {
                    Expr::Annotate { annotation, .. } => {
                        match annotation {
                            TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                            other => panic!("expected Named(Int), got {other:?}"),
                        }
                    }
                    other => panic!("expected Annotate, got {other:?}"),
                }
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // -- `:Type` annotation pairing in every position (S81; BC §1 inv 9) --

    // spec: 02-grammar §2.3.8 — a standalone/top-level `:Type form` binds the
    // following form into a single `Annotate` (NOT a `Var` + separate literal).
    #[test]
    fn build_forms_top_level_annotation_binds_following_form() {
        let sexps = crate::reader::parse(":Int 42").unwrap();
        let forms = build_forms(&sexps).unwrap();
        assert_eq!(forms.len(), 1, "`:Int 42` is ONE annotated form, not two");
        match &forms[0] {
            TopLevel::Expr(Expr::Annotate { annotation, expr, .. }) => {
                match annotation {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                    other => panic!("expected Named(Int), got {other:?}"),
                }
                assert!(
                    matches!(**expr, Expr::IntLit { value: 42, .. }),
                    "annotation must bind the literal 42, got {expr:?}"
                );
            }
            other => panic!("expected TopLevel::Expr(Annotate), got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.8 — a leading `:Type` inside a parenthesized list
    // annotates the SINGLE following element; the list is the application of
    // that one annotated element (callee is the `Annotate`, NOT `:Int`).
    #[test]
    fn list_head_annotation_is_application_of_annotated_element() {
        match parse_and_build_expr("(:Int 42)").unwrap() {
            Expr::Apply { callee, args, .. } => {
                assert!(args.is_empty(), "one-element list — no args");
                match *callee {
                    Expr::Annotate { annotation, expr, .. } => {
                        match annotation {
                            TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                            other => panic!("expected Named(Int), got {other:?}"),
                        }
                        assert!(
                            matches!(*expr, Expr::IntLit { value: 42, .. }),
                            "the annotated element is `42`, got {expr:?}"
                        );
                    }
                    other => panic!("callee must be the annotated `42`, got {other:?}"),
                }
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.8 — a genuine apply argument `(f :Int 42)` still
    // annotates the arg (callee `f` unannotated). Regression guard for the
    // build_apply pairing change.
    #[test]
    fn apply_arg_annotation_unchanged() {
        match parse_and_build_expr("(f :Int 42)").unwrap() {
            Expr::Apply { callee, args, .. } => {
                assert!(
                    matches!(*callee, Expr::Var { .. }),
                    "callee `f` is an unannotated Var, got {callee:?}"
                );
                assert_eq!(args.len(), 1, "`:Int 42` is one annotated arg");
                assert!(
                    matches!(args[0], Expr::Annotate { .. }),
                    "the sole arg is an Annotate, got {:?}",
                    args[0]
                );
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.4.5 / 02-grammar §2.3.8 — a dangling `:Type` with no
    // following form is a parse error in EVERY position.
    #[test]
    fn dangling_annotation_top_level_is_error() {
        let err = crate::reader::parse(":Int").unwrap_err();
        assert!(
            format!("{err:?}").contains("annotation missing expression"),
            "expected `annotation missing expression`, got {err:?}"
        );
    }

    // spec: 01-lexical §1.4.5 — a bare `:Type` symbol reaching expression
    // position with nothing to bind is a parse error, never a `Var`.
    #[test]
    fn dangling_annotation_expr_position_is_error() {
        let err = parse_and_build_expr(":Foo").unwrap_err();
        assert!(
            format!("{err:?}").contains("annotation missing expression"),
            "expected `annotation missing expression`, got {err:?}"
        );
    }

    // spec: 01-lexical §1.4.5 / 02-grammar §2.3.8 — a dangling `:Type` inside a
    // list (`(:Int)`) is a parse error: the annotation has no element to bind.
    #[test]
    fn dangling_annotation_in_empty_paren_is_error() {
        let err = parse_and_build_expr("(:Int)").unwrap_err();
        assert!(
            format!("{err:?}").contains("annotation missing expression"),
            "expected `annotation missing expression`, got {err:?}"
        );
    }

    // spec: 02-grammar §2.3.8 — build_forms delegates non-annotated forms
    // per-form: a `defn` becomes `TopLevel::Defn`, a following bare `:Int 42`
    // becomes one annotated `TopLevel::Expr`.
    #[test]
    fn build_forms_mixes_defn_and_annotated_expr() {
        let sexps = crate::reader::parse("(defn id [x] x)\n:Int 42").unwrap();
        let forms = build_forms(&sexps).unwrap();
        assert_eq!(forms.len(), 2);
        assert!(matches!(forms[0], TopLevel::Defn(_)), "first is the defn");
        assert!(
            matches!(forms[1], TopLevel::Expr(Expr::Annotate { .. })),
            "second is the annotated expr, got {:?}",
            forms[1]
        );
    }

    // -- Quasiquote/quote fold into build_forms/build_form (0613, S111) --

    // spec: 09-macros.md §9.4.4 — quasiquote is legal wherever an expression is
    // legal. A quasiquote in a plain `defn` body desugars at the `build_form`
    // fold (no longer dies at the backstop); the body becomes a `macros/`-ctor
    // application, not the raw `(quasiquote …)` head.
    #[test]
    fn build_form_folds_quasiquote_in_defn_body() {
        let sexps = crate::reader::parse("(defn helper [x] `(if ~x 1 0))").unwrap();
        let entries = build_form(&sexps[0]).expect("quasiquote in a defn body must fold, not error");
        assert!(
            entries.iter().any(|e| matches!(e, ParsedEntry::Def { .. })),
            "the defn builds to a Def after the fold"
        );
    }

    // spec: 09-macros.md §9.4.4 — the same at the build_forms slice boundary,
    // through the top-level dispatch.
    #[test]
    fn build_forms_folds_quote_in_defn_body() {
        let sexps = crate::reader::parse("(defn f [] '(1 2))").unwrap();
        let forms = build_forms(&sexps).expect("quote in a defn body must fold at build_forms");
        assert!(matches!(forms[0], TopLevel::Defn(_)));
    }

    // spec: 09-macros.md §9.4.4 — a bare top-level quote expression folds to a
    // `macros/`-constructor application (an ordinary expr of type Sexp), never
    // the backstop error.
    #[test]
    fn build_forms_folds_top_level_quote_expr() {
        let sexps = crate::reader::parse("'(1 2)").unwrap();
        let forms = build_forms(&sexps).expect("top-level quote folds to a Sexp-ctor expr");
        assert_eq!(forms.len(), 1);
        assert!(
            matches!(forms[0], TopLevel::Expr(Expr::Apply { .. })),
            "the quote desugars to a `macros/SexpList` application, got {:?}",
            forms[0]
        );
    }

    // spec: 09-macros.md §9.4.4 / quasiquote-fold.md §1.1 — desugar-then-pair is
    // order-safe: a leading `:Type` still binds the FOLLOWING (now desugared)
    // quote form into ONE Annotate (the annotation atom passes through the fold
    // untouched, and the quote maps to a single slice element).
    #[test]
    fn build_forms_annotation_binds_following_desugared_quote() {
        let sexps = crate::reader::parse(":macros/Sexp '(1 2)").unwrap();
        let forms = build_forms(&sexps).unwrap();
        assert_eq!(forms.len(), 1, "`:Sexp '(1 2)` is ONE annotated form");
        assert!(
            matches!(forms[0], TopLevel::Expr(Expr::Annotate { .. })),
            "the annotation binds the desugared quote, got {:?}",
            forms[0]
        );
    }

    // spec: 09-macros.md §9.4.4 / quasiquote-fold.md §2 — the fold is an
    // idempotent fixpoint: a second `expand_quasiquotes` pass is a structural
    // no-op, so a caller that already desugared (macro_clause.rs) re-desugars
    // harmlessly. Pin the fixpoint at the boundary the fold relies on.
    #[test]
    fn expand_quasiquotes_is_idempotent_fixpoint() {
        for src in ["'quote", "`(m ~x)", "`(a `(b ~(m 1)))", "'(1 2)"] {
            let sexps = crate::reader::parse(src).unwrap();
            let once = crate::quasiquote::expand_quasiquotes(&sexps[0]).unwrap();
            let twice = crate::quasiquote::expand_quasiquotes(&once).unwrap();
            assert_eq!(
                once.format_flat(),
                twice.format_flat(),
                "one pass must reach the fixpoint for `{src}`"
            );
        }
    }

    // spec: 09-macros.md §9.4.4 / quasiquote-fold.md §3 — the backstop stays:
    // `build_expr` does NOT fold (it is the internal recursion primitive), so a
    // raw `(quote …)` fed directly to it still hits the "should have been
    // expanded" rejection.
    #[test]
    fn build_expr_keeps_backstop_for_raw_quote() {
        let err = parse_and_build_expr("(quote (1 2))").unwrap_err();
        assert!(
            format!("{err:?}").contains("should have been expanded"),
            "build_expr keeps the backstop, got {err:?}"
        );
    }

    // -- 0591 annotation-position parse gaps (AP-1..4) --

    // spec: 03-types.md §3.9 / §2.3.8 (AP-1) — a multi-arity `defn` CLAUSE body
    // may carry a `:Type body` ascription, exactly as the single-arity body does
    // (FV-6). Previously died at parse ("defn variant requires params and body").
    #[test]
    fn build_form_multi_arity_clause_body_annotation() {
        let sexps =
            crate::reader::parse("(defn g ([:a x] :a x) ([:a x :Int n] x))").unwrap();
        let entries = build_form(&sexps[0]).expect("clause body ascription must parse (AP-1)");
        match entries.into_iter().find(|e| matches!(e, ParsedEntry::Def { .. })) {
            Some(ParsedEntry::Def { variants, .. }) => {
                assert_eq!(variants.len(), 2, "both clauses build");
                assert!(
                    matches!(variants[0].body, Expr::Annotate { .. }),
                    "first clause body is the `:a x` ascription, got {:?}",
                    variants[0].body
                );
            }
            other => panic!("expected a Def with two variants, got {other:?}"),
        }
    }

    // spec: 03-types.md §3.9 / §2.3.8 (AP-2) — a `fn` body may carry a
    // `:Type body` ascription. Previously died at parse (arity != 3).
    #[test]
    fn build_fn_body_annotation() {
        match parse_and_build_expr("(fn [:a x] :a x)").unwrap() {
            Expr::Lambda { body, params, .. } => {
                assert_eq!(params.len(), 1);
                assert!(
                    matches!(*body, Expr::Annotate { .. }),
                    "the fn body is the `:a x` ascription, got {body:?}"
                );
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    // spec: 03-types.md §3.9 / §2.3.8 (AP-3) — a match-arm BODY may carry a
    // `:Type body` ascription (the arm bracket then has an odd element count,
    // which the consume-based loop handles). Previously died at the parity gate.
    #[test]
    fn build_match_arm_body_annotation() {
        match parse_and_build_expr("(match 5 [n :Int n])").unwrap() {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 1);
                assert!(
                    matches!(arms[0].body, Expr::Annotate { .. }),
                    "the arm body is the `:Int n` ascription, got {:?}",
                    arms[0].body
                );
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // spec: 03-types.md §3.9 / §2.3.8 (AP-4) — an `if` branch may carry a
    // `:Type form` ascription. Previously died at parse (arity != 4).
    #[test]
    fn build_if_branch_annotation() {
        match parse_and_build_expr("(if true :Int 1 2)").unwrap() {
            Expr::If { then_branch, else_branch, .. } => {
                assert!(
                    matches!(*then_branch, Expr::Annotate { .. }),
                    "the then-branch is the `:Int 1` ascription, got {then_branch:?}"
                );
                assert!(
                    matches!(*else_branch, Expr::IntLit { value: 2, .. }),
                    "the else-branch is the bare `2`, got {else_branch:?}"
                );
            }
            other => panic!("expected If, got {other:?}"),
        }
    }

    // spec: 04-expressions.md §4.4 (AP-4 fence) — a plain `(if c t e)` with no
    // annotations is unchanged, and a truncated `if` still errors.
    #[test]
    fn build_if_plain_unchanged_and_arity_guarded() {
        assert!(matches!(
            parse_and_build_expr("(if true 1 2)").unwrap(),
            Expr::If { .. }
        ));
        let err = parse_and_build_expr("(if true 1)").unwrap_err();
        assert!(
            format!("{err:?}").contains("condition, then, and else"),
            "a truncated if still errors, got {err:?}"
        );
    }

    // -- Match expression --

    // spec: 02-grammar §2.3.7 — match expression with constructor patterns
    #[test]
    fn test_build_match() {
        match parse_and_build_expr("(match x [Red 1 Green 2 Blue 3])").unwrap() {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 3);
                match &arms[0].pattern {
                    Pattern::Constructor { name, bindings, .. } => {
                        assert_eq!(name.name.as_ref(), "Red");
                        assert!(bindings.is_empty());
                    }
                    other => panic!("expected Constructor, got {other:?}"),
                }
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.5.2 — wildcard pattern in match
    #[test]
    fn test_build_match_with_wildcard() {
        match parse_and_build_expr("(match x [Red 1 _ 0])").unwrap() {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 2);
                assert!(matches!(&arms[1].pattern, Pattern::Wildcard { .. }));
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.5.3 — variable pattern in match
    #[test]
    fn test_build_match_with_var_pattern() {
        match parse_and_build_expr("(match x [y y])").unwrap() {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 1);
                match &arms[0].pattern {
                    Pattern::Var { name, .. } => assert_eq!(name, "y"),
                    other => panic!("expected Var, got {other:?}"),
                }
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.7 — an odd match-arm count is rejected. Post-0591
    // (AP-3) the fixed even-count parity check is gone (an arm body may be a
    // two-token `:Type body` ascription, so `pattern body` is not always a
    // 2-token pair); the consume-based `build_match_arms` loop reports the
    // unpaired final pattern (`Green` here) as "match arm missing body".
    #[test]
    fn test_build_match_odd_arms_rejected() {
        let err = parse_and_build_expr("(match x [Red 1 Green])").unwrap_err();
        assert!(err.message().contains("missing body"));
    }

    // spec: 02-grammar §2.5.1 — constructor pattern with field bindings
    #[test]
    fn test_build_match_with_constructor_bindings() {
        match parse_and_build_expr("(match x [(Some v) v])").unwrap() {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 1);
                match &arms[0].pattern {
                    Pattern::Constructor { name, bindings, .. } => {
                        assert_eq!(name.name.as_ref(), "Some");
                        assert_eq!(bindings.len(), 1);
                        assert_eq!(bindings[0], "v");
                    }
                    other => panic!("expected Constructor, got {other:?}"),
                }
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.8 — `:Type form` annotation groups with the match
    // scrutinee (FIXME 0389): the simple colon-prefixed-symbol annotation
    // `:Bool` binds the following form `x`, yielding an annotated scrutinee +
    // intact arms.
    #[test]
    fn test_build_match_scrutinee_simple_annotation() {
        match parse_and_build_expr("(match :Bool x [True 1 False 0])").unwrap() {
            Expr::Match { scrutinee, arms, .. } => {
                assert!(
                    matches!(scrutinee.as_ref(), Expr::Annotate { annotation: TypeExpr::Named(_), .. }),
                    "scrutinee should be an annotated expr, got {scrutinee:?}"
                );
                assert_eq!(arms.len(), 2, "both arms survive the grouping");
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.8 — compound applied-type annotation `:(Option Int)`
    // groups with the match scrutinee (FIXME 0389): the bare-colon + following
    // list form `(Option Int)` binds the next form `None`, yielding an
    // annotated scrutinee whose annotation is the applied type + intact arms.
    #[test]
    fn test_build_match_scrutinee_compound_annotation() {
        match parse_and_build_expr("(match :(Option Int) None [None 0 (Some _) 1])").unwrap() {
            Expr::Match { scrutinee, arms, .. } => {
                match scrutinee.as_ref() {
                    Expr::Annotate { annotation, expr, .. } => {
                        match annotation {
                            TypeExpr::Applied(head, args) => {
                                assert_eq!(head.name.as_ref(), "Option");
                                assert_eq!(args.len(), 1, "(Option Int) has one type arg");
                            }
                            other => panic!("annotation should be an applied type, got {other:?}"),
                        }
                        // A bare uppercase `None` builds to `Expr::Var` at the
                        // frontend stage (constructor resolution is typecheck's).
                        assert!(
                            matches!(expr.as_ref(), Expr::Var { .. }),
                            "inner scrutinee is the bare `None` form, got {expr:?}"
                        );
                    }
                    other => panic!("scrutinee should be an annotated expr, got {other:?}"),
                }
                assert_eq!(arms.len(), 2, "both arms survive the grouping");
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // -- defn --

    // spec: 02-grammar §2.2.1 — defn single-signature form
    #[test]
    fn test_build_defn() {
        let prog = parse_and_build_program("(defn add [a b] (+ a b))").unwrap();
        assert_eq!(prog.len(), 1);
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.name, "add");
                assert_eq!(defn.params().len(), 2);
                assert_eq!(defn.visibility, Visibility::Public);
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.6 — defn- private function definition
    #[test]
    fn test_build_defn_private() {
        let prog = parse_and_build_program("(defn- helper [x] x)").unwrap();
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.name, "helper");
                assert_eq!(defn.visibility, Visibility::Private);
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.7 — defn with docstring
    #[test]
    fn test_build_defn_with_docstring() {
        let prog = parse_and_build_program("(defn add \"Adds two values\" [a b] (+ a b))").unwrap();
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.docstring.as_deref(), Some("Adds two values"));
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.1 — defn multi-signature form
    #[test]
    fn test_build_defn_multi() {
        let prog = parse_and_build_program("(defn f ([x] x) ([x y] (+ x y)))").unwrap();
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.name, "f");
                assert!(defn.is_multi_sig());
                assert_eq!(defn.variants.len(), 2);
                assert_eq!(defn.variants[0].params.len(), 1);
                assert_eq!(defn.variants[1].params.len(), 2);
            }
            other => panic!("expected Defn (multi-sig), got {other:?}"),
        }
    }

    // 0341 (FIXED): stacked trait-bound param annotations `[:Eq :Display a]`
    // attach BOTH bounds to the single binder `a`, yielding ONE param named `a`
    // (not two, with `:Display` mis-read as a second binder name). The run of
    // `:Trait` annotations preceding a binder all attach to it as a
    // `TypeExpr::Bounds([..])` carrier (FIXME 0341 frontend half / 0346 carrier).
    //
    // spec: spec/07-traits.md §7.8.2 — explicit constraint param annotations
    #[test]
    fn stacked_trait_bound_annotations_attach_to_single_param() {
        let prog = parse_and_build_program("(defn g [:Eq :Display a] a)").unwrap();
        assert_eq!(prog.len(), 1);
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.name, "g");
                // The stacked `:Eq :Display` bounds belong to `a`, so there is
                // exactly ONE parameter, named `a` — never a `:Display` binder.
                assert_eq!(
                    defn.params().len(),
                    1,
                    "stacked annotations must yield ONE param `a`; \
                     got {} params: {:?}",
                    defn.params().len(),
                    defn.params(),
                );
                assert_eq!(
                    defn.params()[0].0,
                    "a",
                    "the single param must be named `a`, not a mis-read \
                     `:Display` annotation"
                );
                // The accumulated run is carried as `Bounds([Eq, Display])` —
                // the shape typecheck's `resolve_bound_param` consumes.
                match &defn.params()[0].1 {
                    Some(TypeExpr::Bounds(bounds)) => {
                        let names: Vec<&str> =
                            bounds.iter().map(|t| t.name.as_ref()).collect();
                        assert_eq!(names, vec!["Eq", "Display"],
                            "the stacked bounds must be Bounds([Eq, Display])");
                        assert!(bounds.iter().all(|t| t.module.is_none()),
                            "unqualified bounds carry no module");
                    }
                    other => panic!(
                        "expected Some(Bounds([Eq, Display])), got {other:?}"
                    ),
                }
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // 0341 (FIXED): the `assert-eq`-shaped TWO-param stacked signature
    // `[:Eq :Display a :Eq :Display b]` must parse — each binder takes the run
    // of `:Eq :Display` bounds preceding it, NOT a `duplicate parameter name
    // ':Display'` error from `:Display` being mis-read as a second binder.
    //
    // spec: spec/07-traits.md §7.8.2 — explicit constraint param annotations
    #[test]
    fn stacked_trait_bounds_two_params_no_duplicate_error() {
        let prog =
            parse_and_build_program("(defn f [:Eq :Display a :Eq :Display b] a)")
                .expect("two stacked-bound params must parse, not duplicate-error");
        assert_eq!(prog.len(), 1);
        match &prog[0] {
            TopLevel::Defn(defn) => {
                let params = defn.params();
                assert_eq!(
                    params.len(),
                    2,
                    "exactly two binders `a` and `b`; got {:?}",
                    params,
                );
                assert_eq!(params[0].0, "a");
                assert_eq!(params[1].0, "b");
                for (i, name) in [(0usize, "a"), (1usize, "b")] {
                    match &params[i].1 {
                        Some(TypeExpr::Bounds(bounds)) => {
                            let ns: Vec<&str> =
                                bounds.iter().map(|t| t.name.as_ref()).collect();
                            assert_eq!(ns, vec!["Eq", "Display"],
                                "param {name} must carry Bounds([Eq, Display])");
                        }
                        other => panic!(
                            "param {name} expected Bounds([Eq, Display]), got {other:?}"
                        ),
                    }
                }
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // Regression: a SINGLE trait-bound `[:Eq a]` is the run-of-length-1 and is
    // left as the resolved `TypeExpr` (NOT wrapped in `Bounds`), so the existing
    // single-annotation path is unchanged.
    //
    // spec: spec/07-traits.md §7.8.2 — single explicit constraint param annotation
    #[test]
    fn single_trait_bound_annotation_unchanged() {
        let prog = parse_and_build_program("(defn g [:Eq a] a)").unwrap();
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.params().len(), 1);
                assert_eq!(defn.params()[0].0, "a");
                // Run-of-1: not promoted to Bounds — stays a Named annotation.
                assert!(
                    !matches!(defn.params()[0].1, Some(TypeExpr::Bounds(_))),
                    "single bound must NOT be wrapped in Bounds: {:?}",
                    defn.params()[0].1,
                );
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // Regression: a concrete-type annotation `[:Int x]` still emits
    // `Some(Named(Int))`, NOT `Bounds`.
    //
    // spec: spec/03-types.md §3.9.2 — concrete-type param annotation
    #[test]
    fn concrete_type_param_annotation_is_named() {
        let prog = parse_and_build_program("(defn g [:Int x] x)").unwrap();
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.params().len(), 1);
                match &defn.params()[0].1 {
                    Some(TypeExpr::Named(r)) => assert_eq!(r.name.as_ref(), "Int"),
                    other => panic!("expected Some(Named(Int)), got {other:?}"),
                }
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // Regression: a genuine duplicate binder `[x x]` still errors.
    //
    // spec: spec/07-traits.md §7.8.2 — distinct param names
    #[test]
    fn genuine_duplicate_binder_still_errors() {
        let err = parse_and_build_program("(defn g [x x] x)").unwrap_err();
        assert!(
            format!("{err:?}").contains("duplicate parameter name"),
            "genuine duplicate binder must still error: {err:?}",
        );
    }

    // Edge: a trailing annotation run with no terminating binder `[:Eq]` is the
    // structural "annotation missing expression" error.
    //
    // spec: spec/07-traits.md §7.8.2 — annotation must bind a parameter
    #[test]
    fn trailing_annotation_without_binder_errors() {
        let err = parse_and_build_program("(defn g [:Eq] 0)").unwrap_err();
        assert!(
            format!("{err:?}").contains("annotation missing expression"),
            "trailing annotation run must error: {err:?}",
        );
    }

    // -- deftype --

    // spec: 02-grammar §2.2.2 — deftype enum (all nullary constructors)
    #[test]
    fn test_build_deftype_enum() {
        let prog = parse_and_build_program("(deftype Color Red Green Blue)").unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name,
                constructors,
                ..
            } => {
                assert_eq!(name, "Color");
                assert_eq!(constructors.len(), 3);
                assert_eq!(constructors[0].name, "Red");
                assert_eq!(constructors[1].name, "Green");
                assert_eq!(constructors[2].name, "Blue");
                assert!(constructors[0].fields.is_empty());
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.2 — deftype product type with typed fields
    #[test]
    fn test_build_deftype_product() {
        let prog = parse_and_build_program("(deftype Point [:Int x :Int y])").unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name,
                constructors,
                ..
            } => {
                assert_eq!(name, "Point");
                assert_eq!(constructors.len(), 1);
                assert_eq!(constructors[0].fields.len(), 2);
                assert_eq!(constructors[0].fields[0].name, "x");
                assert_eq!(constructors[0].fields[1].name, "y");
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.2 — deftype polymorphic sum type
    #[test]
    fn test_build_deftype_sum() {
        let prog = parse_and_build_program("(deftype (Option a) None (Some [:a val]))").unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name,
                type_params,
                constructors,
                ..
            } => {
                assert_eq!(name, "Option");
                assert_eq!(type_params.len(), 1);
                assert_eq!(type_params[0], "a");
                assert_eq!(constructors.len(), 2);
                assert_eq!(constructors[0].name, "None");
                assert!(constructors[0].fields.is_empty());
                assert_eq!(constructors[1].name, "Some");
                assert_eq!(constructors[1].fields.len(), 1);
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.2 — deftype shortcut syntax (bare field names)
    #[test]
    fn test_build_deftype_shortcut_fields() {
        // (deftype Pair [first second]) — bare names get sequential type vars
        let prog = parse_and_build_program("(deftype Pair [first second])").unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name,
                type_params,
                constructors,
                ..
            } => {
                assert_eq!(name, "Pair");
                assert_eq!(type_params.len(), 2);
                assert_eq!(type_params[0], "a");
                assert_eq!(type_params[1], "b");
                assert_eq!(constructors[0].fields.len(), 2);
                // Fields should have sequential type vars (a, b, c, ...)
                match &constructors[0].fields[0].type_expr {
                    TypeExpr::TypeVar(v) => assert_eq!(*v, "a"),
                    other => panic!("expected TypeVar, got {other:?}"),
                }
                match &constructors[0].fields[1].type_expr {
                    TypeExpr::TypeVar(v) => assert_eq!(*v, "b"),
                    other => panic!("expected TypeVar, got {other:?}"),
                }
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // spec: 05-definitions §5.2 — a constructor with a bare type and no field
    // name (`(L :Int)` — missing the `[:Type name]` brackets) MUST be rejected,
    // not silently accepted as a nullary constructor. Regression guard for the
    // silent-enum collapse (S107 item 1).
    #[test]
    fn test_build_deftype_nameless_ctor_field_rejected() {
        let err = parse_and_build_program("(deftype Rotation (L :Int) (R :Int))").unwrap_err();
        let msg = format!("{err:?}");
        assert!(msg.contains("annotation missing expression"), "{msg}");
    }

    // spec: 05-definitions §5.2 — the rejection above must be NARROW: a
    // correctly-bracketed sum type still builds a unary constructor with one field.
    #[test]
    fn test_build_deftype_bracketed_ctor_field_still_ok() {
        let prog =
            parse_and_build_program("(deftype Rotation (L [:Int n]) (R [:Int m]))").unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name, constructors, ..
            } => {
                assert_eq!(name, "Rotation");
                assert_eq!(constructors.len(), 2);
                assert_eq!(constructors[0].name, "L");
                assert_eq!(constructors[0].fields.len(), 1);
                assert_eq!(constructors[1].name, "R");
                assert_eq!(constructors[1].fields.len(), 1);
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // spec: 05-definitions §5.2 — a constructor name must start uppercase so it
    // is matchable in patterns. The parenthesized (data) constructor arm now
    // enforces this the SAME as the bare-nullary arm: a lowercase parenthesized
    // ctor `(deftype Shape (circle [:Int r]))` was silently accepted (callable
    // but unmatchable) — 0660 cell (a). Reject is located at the ctor name and
    // names the fix; the uppercase twin builds.
    #[test]
    fn deftype_lowercase_parenthesized_ctor_rejected_uppercase_twin_accepts() {
        let src = "(deftype Shape (circle [:Int r]))";
        let err = parse_and_build_program(src)
            .expect_err("a lowercase parenthesized constructor must be rejected");
        assert!(
            err.message().contains("must start with uppercase")
                && err.message().contains("write `Circle`"),
            "the reject names the uppercase rule and the fix; got: {}",
            err.message()
        );
        assert_err_span_at(src, &err, "circle", 0);
        // Uppercase-parenthesized twin builds.
        let prog = parse_and_build_program("(deftype Shape (Circle [:Int r]))").unwrap();
        match &prog[0] {
            TopLevel::TypeDef { constructors, .. } => {
                assert_eq!(constructors[0].name, "Circle");
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // spec: 05-definitions §5.2 — the bare-nullary constructor arm is consistent:
    // a lowercase bare constructor `(deftype Shape circle)` is ALSO rejected (its
    // match guard `is_uppercase_start` fails → the constructor-definition reject),
    // while an uppercase bare constructor builds as nullary. Confirms both arms
    // enforce the uppercase rule (0660 cell (a), both-arm check).
    #[test]
    fn deftype_lowercase_bare_ctor_rejected_uppercase_bare_twin_accepts() {
        let err = parse_and_build_program("(deftype Shape circle)")
            .expect_err("a lowercase bare constructor must be rejected");
        // The bare arm rejects via guard-fallthrough (no uppercase symbol matched).
        assert!(
            err.to_string().to_lowercase().contains("constructor"),
            "the bare lowercase ctor is rejected as an invalid constructor; got: {err}"
        );
        // Uppercase bare (nullary) twin builds.
        let prog = parse_and_build_program("(deftype Shape Circle Square)").unwrap();
        match &prog[0] {
            TopLevel::TypeDef { constructors, .. } => {
                assert_eq!(constructors.len(), 2);
                assert_eq!(constructors[0].name, "Circle");
                assert_eq!(constructors[1].name, "Square");
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // spec: 05-definitions §5.2.2 (user ruling 2026-07-19) — a constructor name is
    // a BINDER (mints a module-level callable), so a qualified spelling rejects in
    // BOTH arms (bare-nullary + parenthesized-data), located at the ctor name.
    // Kills the degenerate-span silent accept of `(deftype Shape (fmt/Circle …))`.
    // 0660 cell (b).
    #[test]
    fn deftype_qualified_ctor_name_rejected_both_arms_bare_twins_accept() {
        // Bare-nullary arm: `is_uppercase_start` keys after the slash, so
        // `fmt/Circle` reaches the nullary arm; the qualified reject fires.
        let bare_src = "(deftype Shape fmt/Circle)";
        let bare_err = parse_and_build_program(bare_src)
            .expect_err("a qualified bare constructor name is rejected");
        assert!(
            bare_err.message().contains("qualified name") && bare_err.message().contains("binder"),
            "bare arm: qualified-binder message; got: {}", bare_err.message()
        );
        assert_err_span_at(bare_src, &bare_err, "fmt/Circle", 0);
        // Parenthesized-data arm.
        let list_src = "(deftype Shape (fmt/Circle [:Int r]))";
        let list_err = parse_and_build_program(list_src)
            .expect_err("a qualified parenthesized constructor name is rejected");
        assert!(
            list_err.message().contains("qualified name") && list_err.message().contains("binder"),
            "list arm: qualified-binder message; got: {}", list_err.message()
        );
        assert_err_span_at(list_src, &list_err, "fmt/Circle", 0);
        // Bare-name twins accept.
        assert!(parse_and_build_program("(deftype Shape Circle)").is_ok());
        assert!(parse_and_build_program("(deftype Shape (Circle [:Int r]))").is_ok());
    }

    // spec: 05-definitions §5.2.6 (user ruling 2026-07-19) — a field name is a
    // BINDER (mints a `Type.field` accessor), so a qualified field name rejects,
    // located at the field name. Covers both the annotated and bare field arms.
    #[test]
    fn deftype_qualified_field_name_rejected_bare_twin_accepts() {
        let ann_src = "(deftype T [:Int fmt/r])";
        let ann_err = parse_and_build_program(ann_src)
            .expect_err("a qualified annotated field name is rejected");
        assert!(
            ann_err.message().contains("qualified name") && ann_err.message().contains("binder"),
            "annotated field: qualified-binder message; got: {}", ann_err.message()
        );
        assert_err_span_at(ann_src, &ann_err, "fmt/r", 0);
        // Bare (shortcut) field arm.
        let bare_src = "(deftype T [fmt/r])";
        let bare_err = parse_and_build_program(bare_src)
            .expect_err("a qualified bare field name is rejected");
        assert!(
            bare_err.message().contains("qualified name"),
            "bare field: qualified-binder message; got: {}", bare_err.message()
        );
        assert_err_span_at(bare_src, &bare_err, "fmt/r", 0);
        // Bare-name twins accept.
        assert!(parse_and_build_program("(deftype T [:Int r])").is_ok());
        assert!(parse_and_build_program("(deftype T [r])").is_ok());
    }

    // spec: 05-definitions §5 binder-positions table — of the LOCAL binder
    // positions, only `defmacro` params are enforced at the frontend build layer
    // (they parse from raw pre-expansion source). The VALUE-level build-layer
    // binders (defn/fn params, let names, match patterns) are DEFERRED: their seam
    // runs after int's macro-expansion name-resolution, which itself qualifies a
    // colliding local binder (`name` → `primitives/name`), so a reject there would
    // break a VALID program — S113 item-3 finding, enforcement owed at the
    // reader/raw layer or the paired int fix. The bare twins parse here.
    #[test]
    fn defmacro_param_rejects_qualified_value_binders_still_accept() {
        // defmacro param — build via `build_form` (the adapter panics on Macro entries)
        let build_one = |src: &str| -> Result<(), CranelispError> {
            let sexps = crate::reader::parse(src)?;
            build_form(&sexps[0]).map(|_| ())
        };
        let err = build_one("(defmacro m [a/b] a/b)")
            .expect_err("a qualified defmacro param is rejected");
        assert!(
            err.message().contains("qualified name") && err.message().contains("binder"),
            "defmacro param reject names the rule; got: {}", err.message()
        );
        assert!(build_one("(defmacro m [ab] ab)").is_ok(), "defmacro param twin");
        // The deferred value-level binder positions still parse (no over-reach and,
        // pending the int fix, no false-positive on int-qualified names): bare
        // names bind normally.
        assert!(parse_and_build_program("(defn f [ab] ab)").is_ok(), "defn param");
        assert!(parse_and_build_expr("(fn [ab] ab)").is_ok(), "fn param");
        assert!(parse_and_build_expr("(let [ab 1] ab)").is_ok(), "let name");
        assert!(parse_and_build_expr("(match x [ab ab])").is_ok(), "match var");
        assert!(parse_and_build_expr("(match x [(Some ab) ab])").is_ok(), "match ctor binding");
    }

    // -- REPL input --

    // spec: 02-grammar §2.1 — REPL top-level expression
    #[test]
    fn test_repl_expression() {
        match parse_and_build_repl("42").unwrap() {
            TopLevel::Expr(Expr::IntLit { value, .. }) => assert_eq!(value, 42),
            other => panic!("expected Expr(IntLit), got {other:?}"),
        }
    }

    // spec: 02-grammar §2.1 — REPL defn definition
    #[test]
    fn test_repl_defn() {
        match parse_and_build_repl("(defn f [x] x)").unwrap() {
            TopLevel::Defn(defn) => assert_eq!(defn.name, "f"),
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.1 — REPL deftype definition
    #[test]
    fn test_repl_deftype() {
        match parse_and_build_repl("(deftype Color Red Green Blue)").unwrap() {
            TopLevel::TypeDef { name, .. } => assert_eq!(name, "Color"),
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // -- Rejected forms --

    // spec: spec/04-expressions.md §4.12 — trace produces Expr::Trace
    #[test]
    fn test_trace_produces_trace_node() {
        match parse_and_build_expr("(trace 42)").unwrap() {
            Expr::Trace { modules, body, .. } => {
                assert!(modules.is_empty());
                match *body {
                    Expr::IntLit { value, .. } => assert_eq!(value, 42),
                    other => panic!("expected IntLit body, got {other:?}"),
                }
            }
            other => panic!("expected Trace, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.4 — trace in head/reference position is the special
    // form and still builds Expr::Trace (it is NOT a binder, not rejected).
    #[test]
    fn test_trace_head_position_still_builds_trace_node() {
        match parse_and_build_expr("(trace (f 1))").unwrap() {
            Expr::Trace { body, .. } => {
                assert!(matches!(*body, Expr::Apply { .. }), "expected Apply body");
            }
            other => panic!("expected Trace, got {other:?}"),
        }
    }

    // -- test-discovery: `discover-tests` / `run-test` are NOT special forms --
    // design/arch/test-discovery.md §"Frontend — nothing (zero special-casing)"

    // spec: appendix-a-builtins §A.4 — `discover-tests` parses as an ordinary
    // application (no head-position dispatch), resolving through the symbol table.
    #[test]
    fn test_discover_tests_builds_as_apply() {
        match parse_and_build_expr("(discover-tests [\"user\"])").unwrap() {
            Expr::Apply { callee, args, .. } => {
                assert!(
                    matches!(&*callee, Expr::Var { name, .. } if name.as_ref() == "discover-tests"),
                    "expected Var(discover-tests) callee, got {callee:?}"
                );
                assert_eq!(args.len(), 1, "expected the vec-literal argument preserved");
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: appendix-a-builtins §A.4 — no-arg `(discover-tests)` is an ordinary
    // zero-arg application now (the no-arg sugar is a stdlib-macro concern, not a
    // frontend special form).
    #[test]
    fn test_discover_tests_no_arg_builds_as_apply() {
        match parse_and_build_expr("(discover-tests)").unwrap() {
            Expr::Apply { callee, args, .. } => {
                assert!(
                    matches!(&*callee, Expr::Var { name, .. } if name.as_ref() == "discover-tests"),
                    "expected Var(discover-tests) callee, got {callee:?}"
                );
                assert!(args.is_empty(), "expected no synthesised arguments");
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: appendix-a-builtins §A.4 — `run-test` is retired; it no longer parses
    // as a special form. It builds as an ordinary application (and will fail at
    // typecheck because no such symbol exists).
    #[test]
    fn test_run_test_builds_as_apply() {
        match parse_and_build_expr("(run-test foo)").unwrap() {
            Expr::Apply { callee, .. } => {
                assert!(
                    matches!(&*callee, Expr::Var { name, .. } if name.as_ref() == "run-test"),
                    "expected Var(run-test) callee, got {callee:?}"
                );
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: appendix-a-builtins §A.4 — `discover-tests` is NOT a reserved binder
    // (only `trace` is); defining it is allowed.
    #[test]
    fn test_defn_discover_tests_allowed() {
        let prog = parse_and_build_program("(defn discover-tests [x] x)").unwrap();
        assert!(!prog.is_empty(), "expected the defn to build");
    }

    // -- Reserved binder name: `trace` (spec/02-grammar.md §2.9) --

    fn assert_reserved_trace_error(err: CranelispError) {
        let msg = format!("{err}");
        assert!(
            msg.contains("'trace' is a reserved special-form name"),
            "expected reserved-name error, got: {msg}"
        );
    }

    // spec: 02-grammar §2.9 — `trace` rejected as a defn name
    #[test]
    fn test_reject_trace_defn_name() {
        let err = parse_and_build_program("(defn trace [x] x)").unwrap_err();
        assert_reserved_trace_error(err);
    }

    // spec: 02-grammar §2.9 — `trace` rejected as a let binder
    #[test]
    fn test_reject_trace_let_binder() {
        let err = parse_and_build_expr("(let [trace 1] trace)").unwrap_err();
        assert_reserved_trace_error(err);
    }

    // spec: 02-grammar §2.9 — `trace` rejected as a fn parameter
    #[test]
    fn test_reject_trace_fn_param() {
        let err = parse_and_build_expr("(fn [trace] trace)").unwrap_err();
        assert_reserved_trace_error(err);
    }

    // spec: 02-grammar §2.9 — `trace` rejected as a match pattern variable
    // binder (a bare lowercase pattern symbol is a binder).
    #[test]
    fn test_reject_trace_match_pattern_var() {
        let err = parse_and_build_expr("(match x [trace trace])").unwrap_err();
        assert_reserved_trace_error(err);
    }

    // spec: 02-grammar §2.9 — `trace` rejected as a constructor-pattern binding
    // (the bound variable is a binder; the constructor name is not).
    #[test]
    fn test_reject_trace_constructor_pattern_binding() {
        let err = parse_and_build_expr("(match x [(Some trace) trace])").unwrap_err();
        assert_reserved_trace_error(err);
    }

    // spec: 02-grammar §2.9 — `trace` rejected as a defmacro name (any
    // binder/definition position; spec §2.9 prose covers "any other position").
    #[test]
    fn test_reject_trace_defmacro_name() {
        let err = parse_and_build_program("(defmacro trace [x] x)").unwrap_err();
        assert_reserved_trace_error(err);
    }

    // spec: 02-grammar §2.9 — `trace` rejected as a defmacro parameter.
    #[test]
    fn test_reject_trace_defmacro_param() {
        let err = parse_and_build_program("(defmacro m [trace] trace)").unwrap_err();
        assert_reserved_trace_error(err);
    }

    // spec: 02-grammar §2.9 — a constructor NAME `Trace` is not a binder and is
    // unaffected (only the reserved lowercase keyword `trace` is rejected).
    #[test]
    fn test_constructor_name_unaffected() {
        // `traced` (a different name containing the substring) must bind fine.
        let expr = parse_and_build_expr("(let [traced 1] traced)").unwrap();
        assert!(matches!(expr, Expr::Let { .. }));
    }

    // spec: 02-grammar §2.3.9 — vec is now handled by the prelude vec macro
    // (no AST intercept). It parses as a regular function application.
    #[test]
    fn test_vec_parses_as_call() {
        // (vec 1 2 3) should parse as a regular Apply, not be rejected.
        let expr = parse_and_build_expr("(vec 1 2 3)").unwrap();
        assert!(matches!(expr, cranelisp_types::Expr::Apply { .. }));
    }

    // -- deftrait --

    // spec: 02-grammar §2.2.3 — simple deftrait with one method
    #[test]
    fn test_build_deftrait_simple() {
        let prog = parse_and_build_program(
            "(deftrait Display (show [self] String))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.name, "Display");
                assert!(decl.type_params.is_empty());
                assert_eq!(decl.methods.len(), 1);
                assert_eq!(decl.methods[0].name, "show");
                assert_eq!(decl.methods[0].params.len(), 1);
                assert!(matches!(&decl.methods[0].params[0].1, TypeExpr::SelfType));
                assert!(matches!(&decl.methods[0].tail, Sexp::Symbol(n, _) if n == "String"));
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.7 — deftrait with docstring
    #[test]
    fn test_build_deftrait_with_docstring() {
        let prog = parse_and_build_program(
            "(deftrait Display \"Convert to string\" (show [self] String))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.docstring.as_deref(), Some("Convert to string"));
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.3 — deftrait with multiple method signatures
    #[test]
    fn test_build_deftrait_multiple_methods() {
        // Per spec §5.3 EBNF (`param = ':' type_expr symbol | symbol`) required-method
        // params now carry names; bare params default to SelfType per spec §5.3.1.
        // S70 cascade row #9 — pre-cascade test input used `[self self]` (the bare
        // type-only no-default-branch reading) which is spec-non-compliant on the
        // post-S69-Sub-26 fused shape. Inputs rewritten to spec-conformant `[a b]`.
        let prog = parse_and_build_program(
            "(deftrait Num (+ [a b] self) (- [a b] self))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.name, "Num");
                assert_eq!(decl.methods.len(), 2);
                assert_eq!(decl.methods[0].name, "+");
                assert_eq!(decl.methods[1].name, "-");
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.3 — higher-kinded deftrait
    #[test]
    fn test_build_deftrait_hkt() {
        // S70 cascade row #9 — pre-cascade input used bare type expressions in the
        // bracket; spec §5.3 EBNF requires param names. The HKT param-index detect
        // logic walks `bracket_items` looking for a `(f ...)` shape, so the param
        // name must be annotated alongside an `(f a)` type. Use `:Type name` form.
        let prog = parse_and_build_program(
            "(deftrait (Functor f) (fmap [:(Fn [a] b) g :(f a) x] (f b)))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.name, "Functor");
                assert_eq!(decl.type_params.len(), 1);
                assert_eq!(decl.type_params[0], "f");
                assert_eq!(decl.methods[0].hkt_param_index, Some(1));
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.3 — deftrait with default method implementation
    #[test]
    fn test_build_deftrait_with_default() {
        // S70 cascade row #9 — `[self self]` pre-cascade input rewritten to spec
        // conformant `[a b]` (bare params default to SelfType per spec §5.3.1).
        let prog = parse_and_build_program(
            "(deftrait Ord (< [a b] Bool) (<= [x y] (if (< x y) true (= x y))))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.methods.len(), 2);
                // Names live with params now (S69 Sub 26) — verify the no-default
                // method has its two self-typed params.
                assert_eq!(decl.methods[0].params.len(), 2);
                assert!(matches!(decl.methods[1].tail, Sexp::List(..)));
                assert_eq!(decl.methods[1].params.len(), 2);
                assert_eq!(decl.methods[1].params[0].0, "x");
                assert_eq!(decl.methods[1].params[1].0, "y");
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
    }

    #[test]
    fn trait_method_preserves_exactly_one_unclassified_tail() {
        let prog = parse_and_build_program(
            "(deftrait T (required [x] Int) (default [x] (f x)) (pinned [x] :Int x))",
        )
        .unwrap();
        let TopLevel::TraitDecl(decl) = &prog[0] else {
            panic!()
        };
        assert!(matches!(decl.methods[0].tail, Sexp::Symbol(ref s, _) if s == "Int"));
        assert!(matches!(decl.methods[1].tail, Sexp::List(..)));
        assert!(matches!(decl.methods[2].tail, Sexp::Annotated { .. }));
        let err = parse_and_build_program("(deftrait T (old [x] Int x))").unwrap_err();
        assert!(err.message().contains("exactly one trailing"));
    }

    #[test]
    fn deftype_uniqueness_and_constructor_spellings_are_enforced() {
        assert!(parse_and_build_program("(deftype T A (B \"doc\") (C [:Int c]))").is_ok());
        assert!(parse_and_build_program("(deftype Cell (Cell [:Int value]))").is_ok());
        for src in [
            "(deftype T (A))",
            "(deftype T (A []))",
            "(deftype T T)",
            "(deftype T (T \"documented nullary\"))",
            "(deftype T A (A \"doc\"))",
            "(deftype T (A [:Int x]) (B [:Int x]))",
        ] {
            assert!(parse_and_build_program(src).is_err(), "must reject: {src}");
        }
    }

    #[test]
    fn deftype_product_rejects_a_trailing_form_at_that_form() {
        let src = "(deftype Point [:Int x] extra)";
        let err = parse_and_build_program(src).unwrap_err();
        assert!(err.message().contains("trailing"), "{}", err.message());
        assert_err_span_at(src, &err, "extra", 0);

        assert!(parse_and_build_program("(deftype Point [:Int x])").is_ok());
    }

    #[test]
    fn constructor_pattern_parentheses_require_a_subpattern() {
        let src = "(match x [(None) 0 None 1 (Some value) value])";
        let err = parse_and_build_program(src).unwrap_err();
        assert!(err.message().contains("at least one"), "{}", err.message());
        assert_err_span_at(src, &err, "(None)", 0);

        assert!(parse_and_build_program("(match x [None 0 (Some value) value])").is_ok());
    }

    #[test]
    fn deftype_duplicate_diagnostics_locate_the_second_binder() {
        let ctor_err = parse_and_build_program("(deftype T A (A \"again\"))").unwrap_err();
        assert_eq!(ctor_err.span(), Span::new(14, 15));

        let field_err =
            parse_and_build_program("(deftype T (A [:Int x]) (B [:Bool x]))").unwrap_err();
        assert_eq!(field_err.span(), Span::new(34, 35));

        // Uniqueness state is definition-local, not global.
        assert!(parse_and_build_program("(deftype A X) (deftype B X)").is_ok());
    }

    #[test]
    fn annotated_nodes_build_in_nested_and_operand_positions() {
        let direct = Sexp::Annotated {
            annotation: Box::new(Sexp::Symbol("Int".into(), Span::new(1, 4))),
            subject: Box::new(Sexp::Int(7, Span::new(5, 6))),
            span: Span::new(0, 6),
        };
        assert!(matches!(
            build_expr(&direct).unwrap(),
            Expr::Annotate { .. }
        ));
        assert!(matches!(
            parse_and_build_expr("(f :core.types/Int 1 [:Int 2])").unwrap(),
            Expr::Apply { .. }
        ));

        let malformed = Sexp::Annotated {
            annotation: Box::new(Sexp::Int(1, Span::new(1, 2))),
            subject: Box::new(Sexp::Int(2, Span::new(3, 4))),
            span: Span::new(0, 4),
        };
        assert!(build_expr(&malformed)
            .unwrap_err()
            .message()
            .contains("invalid type expression"));
    }

    #[test]
    fn nullary_constructor_pattern_is_bare_only() {
        assert!(parse_and_build_expr("(match x [None 0])").is_ok());
        assert!(parse_and_build_expr("(match x [(None) 0])").is_err());
    }

    // spec: 02-grammar §2.6 — deftrait- private trait declaration
    #[test]
    fn test_build_deftrait_private() {
        let prog = parse_and_build_program(
            "(deftrait- Internal (method [self] Int))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.visibility, Visibility::Private);
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.3 — HKT traits reject default method implementations
    #[test]
    fn test_build_deftrait_hkt_default_rejected() {
        // Frontend preserves one raw tail and does not classify it. The HKT
        // default-method restriction is enforced by typecheck after classification.
        let prog = parse_and_build_program("(deftrait (Functor f) (fmap [x] (f x)))").unwrap();
        let TopLevel::TraitDecl(decl) = &prog[0] else {
            panic!()
        };
        assert!(matches!(decl.methods[0].tail, Sexp::List(..)));
    }

    // -- impl --

    // spec: 02-grammar §2.2.4 — impl concrete type
    #[test]
    fn test_build_impl_concrete() {
        let prog = parse_and_build_program(
            "(impl Display Int (defn show [x] (int-to-string x)))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.trait_name.name.as_ref(), "Display");
                // Concrete target: TypeExpr::Named(Int)
                match &imp.target {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                    other => panic!("expected Named, got {other:?}"),
                }
                assert!(imp.type_constraints.is_empty());
                assert_eq!(imp.methods.len(), 1);
                assert_eq!(imp.methods[0].name, "show");
                assert_eq!(imp.methods[0].params().len(), 1);
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.4 — impl polymorphic type with trait constraint
    #[test]
    fn test_build_impl_polymorphic_with_constraint() {
        let prog = parse_and_build_program(
            "(impl Display (Option :Display a) (defn show [x] x))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.trait_name.name.as_ref(), "Display");
                // Polymorphic target: TypeExpr::Applied(Option, [TypeVar(a)])
                match &imp.target {
                    TypeExpr::Applied(head, args) => {
                        assert_eq!(head.name.as_ref(), "Option");
                        assert_eq!(args.len(), 1);
                        match &args[0] {
                            TypeExpr::TypeVar(v) => assert_eq!(v, "a"),
                            other => panic!("expected TypeVar(a), got {other:?}"),
                        }
                    }
                    other => panic!("expected Applied, got {other:?}"),
                }
                assert_eq!(imp.type_constraints.len(), 1);
                assert_eq!(imp.type_constraints[0].0, "a");
                assert_eq!(imp.type_constraints[0].1.name.as_ref(), "Display");
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.4 — impl higher-kinded trait
    #[test]
    fn test_build_impl_hkt() {
        let prog = parse_and_build_program(
            "(impl Functor Option (defn fmap [f opt] opt))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.trait_name.name.as_ref(), "Functor");
                // Concrete target (bare symbol form): TypeExpr::Named(Option)
                match &imp.target {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Option"),
                    other => panic!("expected Named, got {other:?}"),
                }
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.4 — impl in REPL context
    #[test]
    fn test_build_impl_repl() {
        match parse_and_build_repl(
            "(impl Eq Int (defn = [x y] (eq-i64 x y)))",
        ).unwrap() {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.trait_name.name.as_ref(), "Eq");
                match &imp.target {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                    other => panic!("expected Named, got {other:?}"),
                }
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.3 — deftrait in REPL context
    #[test]
    fn test_build_deftrait_repl() {
        match parse_and_build_repl(
            "(deftrait Showable (show [self] String))",
        ).unwrap() {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.name, "Showable");
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.4 — impl with multiple methods
    #[test]
    fn test_build_impl_multiple_methods() {
        let prog = parse_and_build_program(
            "(impl Num Int (defn + [x y] (add-i64 x y)) (defn - [x y] (sub-i64 x y)))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.methods.len(), 2);
                assert_eq!(imp.methods[0].name, "+");
                assert_eq!(imp.methods[1].name, "-");
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // -- Qualified impl-target / trait-name / method-sig type refs (D-qual, S91) --

    // spec: spec/08-modules.md §8.5 — a module-qualified concrete impl target
    // `primitives/Int` is canonical: it MUST lower to
    // `TypeRef { module: Some("primitives"), name: "Int" }`, NOT the un-split
    // `TypeRef { module: None, name: "primitives/Int" }` (which re-roots the impl
    // under the current module → phantom `user/primitives/Int`). Seam guard for
    // the D-qual-impl-target fix; the e2e
    // tests/spec_07_traits.rs::impl_qualified_primitive_type_target_resolves_to_canonical
    // is the end-to-end half.
    #[test]
    fn build_impl_qualified_primitive_target_splits_typeref() {
        let prog = parse_and_build_program(
            "(impl Num primitives/Int (defn + [x y] x))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => match &imp.target {
                TypeExpr::Named(n) => {
                    assert_eq!(n.module.as_deref(), Some("primitives"));
                    assert_eq!(n.name.as_ref(), "Int");
                }
                other => panic!("expected Named, got {other:?}"),
            },
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: spec/08-modules.md §8.5 — extent guard: the qualified-target split is
    // not primitives-specific. A `user/`-qualified target `user/Widget` lowers to
    // `TypeRef { module: Some("user"), name: "Widget" }`, NOT the double-rooted
    // `{ module: None, name: "user/Widget" }` → `user/user/Widget`. Companion to
    // tests/spec_07_traits.rs::impl_qualified_user_type_target_resolves_to_canonical.
    #[test]
    fn build_impl_qualified_user_target_splits_typeref() {
        let prog = parse_and_build_program(
            "(impl Tagger user/Widget (defn tagit [w] 99))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => match &imp.target {
                TypeExpr::Named(n) => {
                    assert_eq!(n.module.as_deref(), Some("user"));
                    assert_eq!(n.name.as_ref(), "Widget");
                }
                other => panic!("expected Named, got {other:?}"),
            },
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: spec/08-modules.md §8.5 — control: a BARE concrete impl target stays
    // `module: None`. Pins that the splitter only adds a module when a `/` is
    // present (no spurious re-rooting of bare targets).
    #[test]
    fn build_impl_bare_target_keeps_no_module() {
        let prog = parse_and_build_program(
            "(impl Num Int (defn + [x y] x))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => match &imp.target {
                TypeExpr::Named(n) => {
                    assert_eq!(n.module, None);
                    assert_eq!(n.name.as_ref(), "Int");
                }
                other => panic!("expected Named, got {other:?}"),
            },
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: spec/08-modules.md §8.5 — qualified type-ARG inside a parameterised
    // impl target (`(impl Display (Option primitives/Int))`) is the same
    // re-rooting class as the head: the uppercase arg `primitives/Int` MUST split
    // to `TypeRef { module: Some("primitives"), name: "Int" }`.
    #[test]
    fn build_impl_qualified_type_arg_splits_typeref() {
        let prog = parse_and_build_program(
            "(impl Display (Option primitives/Int) (defn show [x] x))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => match &imp.target {
                TypeExpr::Applied(head, args) => {
                    assert_eq!(head.name.as_ref(), "Option");
                    assert_eq!(args.len(), 1);
                    match &args[0] {
                        TypeExpr::Named(n) => {
                            assert_eq!(n.module.as_deref(), Some("primitives"));
                            assert_eq!(n.name.as_ref(), "Int");
                        }
                        other => panic!("expected Named arg, got {other:?}"),
                    }
                }
                other => panic!("expected Applied, got {other:?}"),
            },
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: spec/08-modules.md §8.5 + spec/07-traits.md:749 — the CONSTRAINT-trait
    // side of a parameterised impl target (`(impl Display (Option :fmt/Eq a) …)`)
    // is the same hand-rolled-no-split shape. A qualified constraint `:fmt/Eq`
    // MUST split to `TraitRef { module: Some("fmt"), name: "Eq" }`, not the
    // re-rooted `{ module: None, name: "fmt/Eq" }`. Completes the root-cause class.
    #[test]
    fn build_impl_qualified_constraint_splits_traitref() {
        let prog = parse_and_build_program(
            "(impl Display (Option :fmt/Eq a) (defn show [x] x))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.type_constraints.len(), 1);
                assert_eq!(imp.type_constraints[0].0, "a");
                let tr = &imp.type_constraints[0].1;
                assert_eq!(tr.module.as_deref(), Some("fmt"));
                assert_eq!(tr.name.as_ref(), "Eq");
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: spec/08-modules.md §8.5 — control: a BARE constraint trait stays
    // `module: None`. Pins that the constraint splitter only adds a module when a
    // `/` is present (no spurious re-rooting of bare constraints).
    #[test]
    fn build_impl_bare_constraint_keeps_no_module() {
        let prog = parse_and_build_program(
            "(impl Display (Option :Eq a) (defn show [x] x))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.type_constraints.len(), 1);
                let tr = &imp.type_constraints[0].1;
                assert_eq!(tr.module, None);
                assert_eq!(tr.name.as_ref(), "Eq");
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: spec/08-modules.md §8.5 — the TRAIT-name side of `impl` has the same
    // hand-rolled-no-split shape. A qualified trait `(impl primitives/Num Int …)`
    // MUST split to `TraitRef { module: Some("primitives"), name: "Num" }`, not
    // `{ module: None, name: "primitives/Num" }` (root-cause class, same fix).
    #[test]
    fn build_impl_qualified_trait_name_splits_traitref() {
        let prog = parse_and_build_program(
            "(impl primitives/Num Int (defn + [x y] x))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.trait_name.module.as_deref(), Some("primitives"));
                assert_eq!(imp.trait_name.name.as_ref(), "Num");
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // -- S112 b0: echo-the-head impl slot-1 (spec §7.2/§7.3) ----------------
    // Both slot-1 head shapes parse; the parser records ONLY the written shape
    // bit (`head_con_var`) and does NO kind classification or echo validation
    // against the trait declaration — that is typecheck's ONE §7.3.5 Case-3
    // seam. Slot 2 rides the unchanged `build_impl_target` `Applied` path. See
    // design/frontend/trait-impl-head-parse.md.

    // spec: spec/07-traits.md §7.3 — a BARE conventional impl head keeps
    // `head_con_var: None`, byte-identical to the pre-S112 path (additive-green
    // regression pin: every existing bare-head impl is unaffected).
    #[test]
    fn build_impl_bare_head_records_no_con_var() {
        let prog = parse_and_build_program(
            "(impl Display Int (defn show [x] x))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.head_con_var, None);
                assert_eq!(imp.trait_name.module, None);
                assert_eq!(imp.trait_name.name.as_ref(), "Display");
                match &imp.target {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                    other => panic!("expected Named(Int), got {other:?}"),
                }
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: spec/07-traits.md §7.3 — the higher-kinded echo-the-head form
    // `(Functor f)` records `head_con_var: Some("f")`; slot 2 `(Functor Option)`
    // STILL parses through the existing `build_impl_target` `Applied` machinery
    // (the parser assigns it no special meaning — kind-interpreted only at the
    // typecheck Case-3 seam).
    #[test]
    fn build_impl_hk_head_records_con_var_and_keeps_slot2_applied() {
        let prog = parse_and_build_program(
            "(impl (Functor f) (Functor Option) (defn fmap [g x] x))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                let cv = imp.head_con_var.as_ref().expect("expected head_con_var Some");
                assert_eq!(cv.as_ref(), "f");
                assert_eq!(imp.trait_name.module, None);
                assert_eq!(imp.trait_name.name.as_ref(), "Functor");
                match &imp.target {
                    TypeExpr::Applied(head, args) => {
                        assert_eq!(head.name.as_ref(), "Functor");
                        assert_eq!(args.len(), 1);
                        match &args[0] {
                            TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Option"),
                            other => panic!("expected Named(Option) arg, got {other:?}"),
                        }
                    }
                    other => panic!("expected Applied slot-2 target, got {other:?}"),
                }
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: spec/07-traits.md §7.3 — the con_var is recorded VERBATIM (the exact
    // spelling written), NOT normalised: `(Functor g)` records "g". Typecheck's
    // Case-3 echo check needs the written spelling, so the datum must survive.
    #[test]
    fn build_impl_hk_head_records_con_var_verbatim() {
        let prog = parse_and_build_program(
            "(impl (Functor g) (Functor Option) (defn fmap [h x] x))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                let cv = imp.head_con_var.as_ref().expect("expected head_con_var Some");
                assert_eq!(cv.as_ref(), "g");
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: spec/08-modules.md §8.5 + spec/07-traits.md §7.3 — a QUALIFIED echoed
    // head `(fmt/Functor f)` applies the D-qual splitter caller-side, exactly as
    // the bare-head trait-name position does: the head splits to
    // `TraitRef { module: Some("fmt"), name: "Functor" }` and the con_var is
    // still recorded (the split does not disturb the shape bit).
    #[test]
    fn build_impl_hk_qualified_head_splits_traitref_and_records_con_var() {
        let prog = parse_and_build_program(
            "(impl (fmt/Functor f) (Functor Option) (defn fmap [g x] x))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.trait_name.module.as_deref(), Some("fmt"));
                assert_eq!(imp.trait_name.name.as_ref(), "Functor");
                let cv = imp.head_con_var.as_ref().expect("expected head_con_var Some");
                assert_eq!(cv.as_ref(), "f");
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    /// Assert a parse error's located span points EXACTLY at `expected` (the
    /// offending head substring), located as the `nth` (0-based) occurrence of
    /// `expected` in `src`. Guards the design §4/§7 requirement — "every
    /// rejection is located at the head" — so a regression relocating a
    /// diagnostic to the whole-form `(impl …)` span fails here (the whole-form
    /// slice never equals the head substring).
    fn assert_err_span_at(src: &str, err: &CranelispError, expected: &str, nth: usize) {
        let byte_off = src
            .match_indices(expected)
            .nth(nth)
            .unwrap_or_else(|| panic!("`{expected}` occurrence {nth} not found in `{src}`"))
            .0;
        let want = Span::new(byte_off as u32, (byte_off + expected.len()) as u32);
        let got = err.location().span;
        assert_eq!(
            got, want,
            "span for `{src}`: expected to point at `{expected}` ({want}), got {got} \
             (source slice `{}`)",
            &src[got.start as usize..got.end as usize]
        );
    }

    // spec: spec/07-traits.md §7.2/§7.3 — malformed impl slot-1 head shapes are
    // rejected with a LOCATED, fix-naming diagnostic (design §4 table). Each row
    // dies in `parse_trait_head_shape`, the ONE head-shape grammar shared with
    // `deftrait` (Principle 7). Pre-fix they all died on a generic `expected
    // symbol`; each row now asserts its per-shape message names the fix AND that
    // the diagnostic is located at the offending head — the per-arm span:
    // whole slot-1 list (empty/1-elem/3+), inner head-element list (non-symbol
    // head), the head-name symbol (lowercase head), or the con_var element
    // (non-symbol con_var). See `parse_trait_head_shape` (`ast_builder.rs` ~855)
    // for which arm produces which span (design §4/§7 — "located at the head").
    #[test]
    fn build_impl_malformed_head_shapes_rejected_with_fix_naming_errors() {
        // (source, expected message substring, located head substring, occurrence)
        let cases: &[(&str, &str, &str, usize)] = &[
            // len==1 arm → whole slot-1 list span `(Functor)`.
            ("(impl (Functor) Int (defn m [x] x))", "missing its constructor variable", "(Functor)", 0),
            // 3+ arm → whole slot-1 list span `(Functor f g)`.
            ("(impl (Functor f g) Int (defn m [x] x))", "too many elements", "(Functor f g)", 0),
            // empty arm → whole slot-1 list span `()`.
            ("(impl () Int (defn m [x] x))", "empty trait head", "()", 0),
            // non-symbol head → `children[0].span()`, the inner list `(Functor f)`.
            ("(impl ((Functor f)) Int (defn m [x] x))", "trait name must be a bare symbol", "(Functor f)", 0),
            // lowercase head → `name_span`, the head-name symbol `functor`.
            ("(impl (functor f) Int (defn m [x] x))", "must start with uppercase", "functor", 0),
            // non-symbol con_var → `children[1].span()`, the con_var element `3`.
            ("(impl (Functor 3) Int (defn m [x] x))", "constructor variable must be a symbol", "3", 0),
        ];
        for (src, needle, span_snippet, nth) in cases {
            let err = parse_and_build_program(src)
                .expect_err(&format!("expected `{src}` to be rejected"));
            let msg = err.message();
            assert!(
                msg.contains(needle),
                "for `{src}` expected message containing `{needle}`, got: {msg}"
            );
            assert_err_span_at(src, &err, span_snippet, *nth);
        }
    }

    // spec: spec/07-traits.md §7.2 (`con_var = lowercase_symbol`) — an UPPERCASE
    // con_var is rejected at parse for BOTH the `impl` echoed head and the
    // `deftrait` head, via the ONE shared head-shape helper (/qa F2 ruling S112,
    // tests/plan/s112-0628-ic-wave.md §7.2 — one fix closes the two-parser drift
    // window). The diagnostic names the lowercase rule.
    #[test]
    fn trait_head_uppercase_con_var_rejected_in_both_impl_and_deftrait() {
        // The `var_span` arm of `parse_trait_head_shape` locates at the con_var
        // element itself (`F`), not the whole head or form (design §4/§7). In
        // both sources `F` first appears inside `Functor` (occurrence 0); the
        // standalone con_var is occurrence 1.
        let impl_src = "(impl (Functor F) (Functor Option) (defn fmap [g x] x))";
        let impl_err = parse_and_build_program(impl_src)
            .expect_err("uppercase con_var in an impl head is rejected");
        assert!(
            impl_err.message().contains("must start with lowercase"),
            "impl head lowercase-rule message; got: {}",
            impl_err.message()
        );
        assert_err_span_at(impl_src, &impl_err, "F", 1);
        let deftrait_src = "(deftrait (Functor F) (fmap [g] g))";
        let deftrait_err = parse_and_build_program(deftrait_src)
            .expect_err("uppercase con_var in a deftrait head is rejected");
        assert!(
            deftrait_err.message().contains("must start with lowercase"),
            "deftrait head lowercase-rule message; got: {}",
            deftrait_err.message()
        );
        assert_err_span_at(deftrait_src, &deftrait_err, "F", 1);
    }

    // spec: spec/07-traits.md §7.3 — grammar-parity pin (Principle 7): the slot-1
    // head grammar is SINGLE-SOURCED (`parse_trait_head_shape`), so a head shape
    // `deftrait` accepts, `impl` accepts identically — and one it rejects, the
    // other rejects. Directly guards that the two parsers cannot drift on what a
    // legal head looks like (design §3/§7).
    #[test]
    fn trait_head_grammar_parity_deftrait_and_impl_agree() {
        // Only the head shape varies; it is spliced into a well-formed deftrait
        // and a well-formed impl. Acceptance MUST agree row by row — these are
        // the SHAPE cases the shared `parse_trait_head_shape` grammar governs.
        //
        // The QUALIFIED head (`(fmt/Foo f)`) is deliberately EXCLUDED from this
        // parity set: it is the one case where the two callers' NAME policies
        // legitimately diverge — `deftrait`'s head is a BINDER (qualified →
        // rejected, S113), `impl` slot-1 is a trait REFERENCE (qualified →
        // accepted, D-qual splits it). The shared shape parser still accepts it
        // identically for both; the divergence lives entirely in the caller
        // policy (`build_trait_head` reject vs `trait_ref_from_name` split). That
        // divergence is pinned by
        // `qualified_trait_head_binder_reject_diverges_deftrait_from_impl` below.
        let heads: &[&str] = &[
            "Foo",           // bare uppercase        — accepted
            "(Foo f)",       // HK head               — accepted
            "(Foo)",         // missing con_var       — rejected
            "(Foo f g)",     // too many elements     — rejected
            "()",            // empty head            — rejected
            "((Foo f))",     // non-symbol head       — rejected
            "(foo f)",       // lowercase head        — rejected
            "(Foo 3)",       // non-symbol con_var    — rejected
            "(Foo F)",       // uppercase con_var     — rejected
        ];
        for head in heads {
            let deftrait_ok =
                parse_and_build_program(&format!("(deftrait {head} (m [self] self))")).is_ok();
            let impl_ok =
                parse_and_build_program(&format!("(impl {head} Int (defn m [self] self))")).is_ok();
            assert_eq!(
                deftrait_ok, impl_ok,
                "head `{head}`: deftrait accepted={deftrait_ok} but impl accepted={impl_ok} \
                 — the shared head grammar drifted"
            );
        }
    }

    // spec: spec/08-modules.md §8.5 — a qualified type reference in a `deftrait`
    // method signature (both param-annotation and return-type position) is
    // canonical: `:primitives/Int` MUST split to
    // `TypeRef { module: Some("primitives"), name: "Int" }` at both seams, not the
    // un-split `{ module: None, name: "primitives/Int" }`. Frontend half of the
    // Wave-0 sweep finding
    // (tests/spec_qualified_name_sweep.rs::deftrait_method_qualified_type_ref_equals_bare).
    #[test]
    fn build_deftrait_method_qualified_type_refs_split() {
        let decl = match parse_and_build_repl(
            "(deftrait Scaler (scale [:primitives/Int x] primitives/Int))",
        ).unwrap() {
            TopLevel::TraitDecl(decl) => decl,
            other => panic!("expected TraitDecl, got {other:?}"),
        };
        assert_eq!(decl.methods.len(), 1);
        let sig = &decl.methods[0];
        // Param annotation type ref split.
        assert_eq!(sig.params.len(), 1);
        match &sig.params[0].1 {
            TypeExpr::Named(n) => {
                assert_eq!(n.module.as_deref(), Some("primitives"));
                assert_eq!(n.name.as_ref(), "Int");
            }
            other => panic!("expected Named param type, got {other:?}"),
        }
        // Return type ref split.
        assert!(matches!(&sig.tail, Sexp::Symbol(n, _) if n == "primitives/Int"));
    }

    // -- S113 qualified binder-head rejection (reject_qualified_binder_head) --

    // spec: spec/05-definitions.md §5 — a declaration head is a BINDER, not a
    // reference: it binds a NEW name into the CURRENT module and MUST be a bare
    // (unqualified) symbol. The shared `reject_qualified_binder_head` helper gates
    // every binder head site identically (Principle 7). This exercises the helper
    // directly at the seam: a slash-bearing name rejects with a LOCATED,
    // fix-naming diagnostic; a bare name passes.
    #[test]
    fn reject_qualified_binder_head_rejects_slash_and_names_bare_fix() {
        let span = Span::new(3, 10);
        let err = reject_qualified_binder_head("fmt/foo", span)
            .expect_err("a qualified binder head is rejected");
        let msg = err.message();
        assert!(
            msg.contains("qualified name") && msg.contains("binder"),
            "message names the qualified-binder rule; got: {msg}"
        );
        // Fix-naming: the message names the bare after-last-slash segment.
        assert!(msg.contains("write 'foo'"), "message names the bare fix `foo`; got: {msg}");
        // Located at the exact span it was handed (not a degenerate 0..0).
        assert_eq!(err.location().span, span, "reject is located at the head span");
        // A deep-qualified name names the LAST segment as the fix.
        let deep = reject_qualified_binder_head("a.b/Bar", span).unwrap_err();
        assert!(deep.message().contains("write 'Bar'"), "got: {}", deep.message());
        // A bare name passes.
        assert!(reject_qualified_binder_head("foo", span).is_ok());
        assert!(reject_qualified_binder_head("Foo", span).is_ok());
        // The bare `/` division operator is a LEGITIMATE binder name (Principle
        // 16; `(deftrait Num (/ [a b] self) …)`, stdlib/num/num.cl) — it splits
        // to two EMPTY halves, so it is NOT qualified. A coarse `contains('/')`
        // would wrongly reject it. `foo/` and `/bar` (one empty half) pass too.
        assert!(reject_qualified_binder_head("/", span).is_ok(), "bare `/` operator must pass");
        assert!(reject_qualified_binder_head("foo/", span).is_ok());
        assert!(reject_qualified_binder_head("/bar", span).is_ok());
    }

    // spec: spec/07-traits.md §7.1 — a deftrait method NAMED `/` (the division
    // operator, `stdlib/num/num.cl` Num trait) is a bare binder and MUST parse:
    // the qualified-binder reject keys on a two-non-empty-half split, so the bare
    // `/` operator (which splits to empty halves) is not treated as qualified.
    // Regression pin for the prelude-load break the coarse predicate caused.
    #[test]
    fn deftrait_slash_operator_method_name_accepts() {
        assert!(
            parse_and_build_program("(deftrait Num (/ [a b] self))").is_ok(),
            "the `/` division-operator method name is a bare binder and must parse"
        );
        // And as a top-level defn head.
        assert!(
            parse_and_build_program("(defn / [a b] a)").is_ok(),
            "the `/` operator as a defn head is a bare binder and must parse"
        );
    }

    // spec: spec/05-definitions.md §5 — a DOTTED spelling in a binder position is
    // a located compile-time error on the same footing as a qualified one (user
    // ruling 2026-07-21, `[S115]`; 0702 Ruling 1). The predicate is the `/` arm's
    // twin: both-halves-non-empty at the LAST `.` (Principle 16), so a degenerate
    // lone/leading/trailing `.` is NOT a dotted spelling. The discriminating
    // control is the reference splitter: `split_qualified_name` stays `/`-only, so
    // a dotted REFERENCE is never split (the fences `Maybe.Some` / dotted module
    // paths rest on that).
    #[test]
    fn reject_qualified_binder_head_rejects_dotted_and_names_member_fix() {
        let span = Span::new(3, 10);
        let err = reject_qualified_binder_head("a.b", span)
            .expect_err("a dotted binder is rejected");
        let msg = err.message();
        assert!(
            msg.contains("dotted name") && msg.contains("binder"),
            "message names the dotted-binder rule; got: {msg}"
        );
        assert!(msg.contains("write 'b'"), "message names the bare fix `b`; got: {msg}");
        assert_eq!(err.location().span, span, "reject is located at the binder span");
        // Uppercase-dotted rejects on the DOTTED spelling, independent of the
        // per-site case gates (`A.b` passes an uppercase-start gate).
        assert!(reject_qualified_binder_head("A.b", span).is_err());
        assert!(reject_qualified_binder_head("A.B", span).is_err());
        // Deep-dotted names the LAST segment.
        let deep = reject_qualified_binder_head("a.b.c", span).unwrap_err();
        assert!(deep.message().contains("write 'c'"), "got: {}", deep.message());
        // Both-halves-non-empty controls: a degenerate `.` is NOT dotted.
        assert!(reject_qualified_binder_head(".", span).is_ok(), "lone `.` must pass");
        assert!(reject_qualified_binder_head("a.", span).is_ok());
        assert!(reject_qualified_binder_head(".b", span).is_ok());
        // The `/` arm is checked FIRST, so a name carrying both reports the
        // qualifier fault.
        let both = reject_qualified_binder_head("a.b/c", span).unwrap_err();
        assert!(both.message().contains("qualified name"), "got: {}", both.message());
        // CONTROL — the REFERENCE splitter is untouched by the widening: a dotted
        // name is not a qualified split, so dotted references keep working.
        assert_eq!(split_qualified_name("Maybe.Some"), None);
        assert_eq!(split_qualified_name("core.io/pure"), Some(("core.io", "pure")));
    }

    // spec: spec/05-definitions.md §5 — the ONE binder-reject message is shared by
    // declaration heads AND value-level locals (`let`/`match`/param), so it must
    // be position-neutral: saying "a definition head is a binder" at a `let`
    // binder describes something the user did not write (FIXME 0711).
    #[test]
    fn binder_reject_message_is_position_neutral() {
        let span = Span::new(0, 5);
        for name in ["fmt/foo", "a.b"] {
            let err = reject_qualified_binder_head(name, span).unwrap_err();
            let msg = err.message();
            assert!(
                msg.contains("a binder must be a bare (unqualified) name"),
                "message must state the position-neutral binder rule; got: {msg}"
            );
            assert!(
                !msg.contains("definition head"),
                "message must NOT say \"definition head\" (wrong at let/match/param \
                 positions, FIXME 0711); got: {msg}"
            );
        }
    }

    // spec: spec/05-definitions.md §5 — the `.` column of the binder matrix: every
    // native binder-head form rejects a DOTTED head and accepts its bare twin,
    // through the SAME one seam the `/` column uses (a cell that flipped
    // differently would have grown its own path). Located at the head substring.
    #[test]
    fn native_binder_heads_reject_dotted_and_accept_bare_twin() {
        let cases: &[(&str, &str, &str)] = &[
            ("(defn a.b [x] x)", "a.b", "(defn ab [x] x)"),
            ("(defn- a.b [x] x)", "a.b", "(defn- ab [x] x)"),
            ("(deftype A.B [:Int n])", "A.B", "(deftype AB [:Int n])"),
            ("(deftype- A.B [:Int n])", "A.B", "(deftype- AB [:Int n])"),
            ("(deftype (A.Pair a b) [:a x :b y])", "A.Pair", "(deftype (APair a b) [:a x :b y])"),
            // Variant-ctor name: UPPERCASE-dotted, so the reject must fire on the
            // dotted spelling INDEPENDENT of the pre-existing uppercase gate.
            ("(deftype Shape (A.b [:Int r]))", "A.b", "(deftype Shape (Ab [:Int r]))"),
            // Field name (mints a `Type.field` accessor — §5.2.6).
            ("(deftype P [:Int a.b])", "a.b", "(deftype P [:Int ab])"),
            ("(deftrait A.B (m [self] self))", "A.B", "(deftrait AB (m [self] self))"),
            ("(deftrait- A.B (m [self] self))", "A.B", "(deftrait- AB (m [self] self))"),
            ("(deftrait (Cat.X f) (fmap [g self] self))", "Cat.X", "(deftrait (CatX f) (fmap [g self] self))"),
            // con_var (§7.2 bare lowercase type-constructor variable).
            ("(deftrait (Functor a.b) (fmap [g self] self))", "a.b", "(deftrait (Functor ab) (fmap [g self] self))"),
            // Method-signature name (§5.3.3).
            ("(deftrait Foo (a.b [self] self))", "a.b", "(deftrait Foo (ab [self] self))"),
            ("(defmacro a.b [x] x)", "a.b", "(defmacro ab [x] x)"),
            ("(defmacro- a.b [x] x)", "a.b", "(defmacro- ab [x] x)"),
        ];
        let build_one = |src: &str| -> Result<(), CranelispError> {
            let sexps = crate::reader::parse(src)?;
            build_form(&sexps[0]).map(|_| ())
        };
        for (dotted, head, bare) in cases {
            let err = build_one(dotted)
                .expect_err(&format!("dotted head `{dotted}` must be rejected"));
            assert!(
                err.message().contains("dotted name") && err.message().contains("binder"),
                "for `{dotted}` expected the dotted-binder message, got: {}",
                err.message()
            );
            assert_err_span_at(dotted, &err, head, 0);
            assert!(build_one(bare).is_ok(), "bare-head twin `{bare}` must parse");
        }
    }

    // spec: spec/05-definitions.md §5 — the deftype TYPE PARAMETER is a binder
    // (`[S115]` binder table). It was the ONE binder site never routed onto the
    // shared helper: `is_uppercase_start` keys on the after-separator segment, so
    // `prim/a` passed the lowercase gate and died downstream as an incidental
    // `module 'prim' … not found` at a degenerate `0..0` span. The routing call
    // makes both separators a located reject at the PARAM span, with the lowercase
    // gate still the next check for a bare uppercase param.
    #[test]
    fn deftype_type_param_rejects_qualified_and_dotted_located_at_param() {
        let build_one = |src: &str| -> Result<(), CranelispError> {
            let sexps = crate::reader::parse(src)?;
            build_form(&sexps[0]).map(|_| ())
        };
        let err = build_one("(deftype (Duo prim/a b) [:b x])")
            .expect_err("a qualified type param is rejected");
        assert!(
            err.message().contains("qualified name") && err.message().contains("binder"),
            "got: {}", err.message()
        );
        assert!(
            !err.message().contains("not found"),
            "must be a located binder reject, NOT the incidental module-resolution \
             death; got: {}", err.message()
        );
        assert_err_span_at("(deftype (Duo prim/a b) [:b x])", &err, "prim/a", 0);
        // The `.` twin, same seam.
        let dotted = build_one("(deftype (Duo a.b c) [:c x])")
            .expect_err("a dotted type param is rejected");
        assert!(dotted.message().contains("dotted name"), "got: {}", dotted.message());
        assert_err_span_at("(deftype (Duo a.b c) [:c x])", &dotted, "a.b", 0);
        // Bare lowercase param still binds (the positive twin).
        assert!(build_one("(deftype (Duo a c) [:c x])").is_ok());
        // The lowercase gate is still the NEXT check for a bare uppercase param.
        let upper = build_one("(deftype (Duo A c) [:c x])")
            .expect_err("a bare uppercase type param still reports the case rule");
        assert!(
            upper.message().contains("lowercase"),
            "the case gate must still fire for a bare uppercase param; got: {}",
            upper.message()
        );
    }

    // spec: spec/05-definitions.md §5 — the native binder-head forms
    // (`defn`/`defn-`, `deftype`/`deftype-` bare and parenthesized, `deftrait`/
    // `deftrait-` bare and parenthesized, deftrait method-signature name,
    // `defmacro`/`defmacro-`) each reject a qualified head AND accept the bare
    // twin. One reject-plus-bare-twin per form (BD-M1). Every reject is LOCATED
    // at the offending head substring (span assertion via `assert_err_span_at`).
    #[test]
    fn native_binder_heads_reject_qualified_and_accept_bare_twin() {
        // (qualified source, located head substring; bare-twin source)
        let cases: &[(&str, &str, &str)] = &[
            // S1: defn / defn- (get_defn_name — also the impl-body method seam).
            ("(defn fmt/foo [x] x)", "fmt/foo", "(defn foo [x] x)"),
            ("(defn- fmt/foo [x] x)", "fmt/foo", "(defn- foo [x] x)"),
            // S2: deftype / deftype- — bare head arm.
            ("(deftype fmt/Foo [:Int n])", "fmt/Foo", "(deftype Foo [:Int n])"),
            ("(deftype- fmt/Foo [:Int n])", "fmt/Foo", "(deftype- Foo [:Int n])"),
            // S2: deftype — parenthesized `(Name params…)` head arm.
            ("(deftype (fmt/Pair a b) [:a x :b y])", "fmt/Pair", "(deftype (Pair a b) [:a x :b y])"),
            // S3: deftrait / deftrait- — bare head arm.
            ("(deftrait fmt/Foo (m [self] self))", "fmt/Foo", "(deftrait Foo (m [self] self))"),
            ("(deftrait- fmt/Foo (m [self] self))", "fmt/Foo", "(deftrait- Foo (m [self] self))"),
            // S3: deftrait — parenthesized `(Trait con_var)` head arm.
            ("(deftrait (fmt/Functor f) (fmap [g self] self))", "fmt/Functor", "(deftrait (Functor f) (fmap [g self] self))"),
            // S5: deftrait method-signature name.
            ("(deftrait Foo (fmt/show [self] self))", "fmt/show", "(deftrait Foo (show [self] self))"),
            // S4: defmacro / defmacro-.
            ("(defmacro fmt/m [x] x)", "fmt/m", "(defmacro m [x] x)"),
            ("(defmacro- fmt/m [x] x)", "fmt/m", "(defmacro- m [x] x)"),
        ];
        // Build a single form directly through `build_form` (the reject seam),
        // bypassing the TopLevel test adapter which panics on `defmacro`'s Macro
        // entries. The reject fires inside `build_form` either way.
        let build_one = |src: &str| -> Result<(), CranelispError> {
            let sexps = crate::reader::parse(src)?;
            build_form(&sexps[0]).map(|_| ())
        };
        for (qualified, head, bare) in cases {
            let err = build_one(qualified)
                .expect_err(&format!("qualified head `{qualified}` must be rejected"));
            assert!(
                err.message().contains("qualified name") && err.message().contains("binder"),
                "for `{qualified}` expected the qualified-binder message, got: {}",
                err.message()
            );
            assert_err_span_at(qualified, &err, head, 0);
            // The bare-head twin still parses.
            assert!(
                build_one(bare).is_ok(),
                "bare-head twin `{bare}` must parse"
            );
        }
    }

    // spec: spec/05-definitions.md §5 — the S1 single-source guard (Principle 7):
    // a qualified `defn` head rejects IDENTICALLY whether reached as a top-level
    // `defn` (via `parse_defn`) or as an impl-body method defn (via
    // `build_impl_method`), because both route through the ONE `get_defn_name`
    // seam. This is the instrument proving no impl-method copy grew.
    #[test]
    fn qualified_defn_head_rejects_identically_at_toplevel_and_impl_method() {
        let top = parse_and_build_program("(defn fmt/foo [x] x)")
            .expect_err("top-level qualified defn head rejected");
        let impl_method =
            parse_and_build_program("(impl Foo Int (defn fmt/foo [self] self))")
                .expect_err("impl-body qualified method-defn head rejected");
        assert_eq!(
            top.message(), impl_method.message(),
            "the two routes must produce the identical diagnostic (one seam, Principle 7)"
        );
        assert!(top.message().contains("write 'foo'"), "got: {}", top.message());
    }

    // spec: spec/05-definitions.md §5 + spec/07-traits.md §7.2 — the qualified
    // trait head diverges by caller policy: `deftrait`'s head is a binder
    // (rejected), `impl` slot-1 is a trait reference (accepted, D-qual splits).
    // The complement of `trait_head_grammar_parity_deftrait_and_impl_agree`,
    // which excludes this exact case.
    #[test]
    fn qualified_trait_head_binder_reject_diverges_deftrait_from_impl() {
        // deftrait: qualified head REJECTED as a binder.
        let deftrait_err =
            parse_and_build_program("(deftrait fmt/Foo (m [self] self))")
                .expect_err("qualified deftrait head is a binder — rejected");
        assert!(
            deftrait_err.message().contains("qualified name")
                && deftrait_err.message().contains("binder"),
            "got: {}", deftrait_err.message()
        );
        // impl slot-1: qualified echoed head ACCEPTED as a reference (splits).
        let prog = parse_and_build_program(
            "(impl fmt/Foo Int (defn m [self] self))",
        ).expect("qualified impl slot-1 is a reference — accepted and split");
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.trait_name.module.as_deref(), Some("fmt"));
                assert_eq!(imp.trait_name.name.as_ref(), "Foo");
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: spec/07-traits.md §7.2 (`con_var = lowercase_symbol`) — a
    // slash-bearing con_var is a qualified BINDER (BD-M4 / S112-F3 residual): it
    // slips past the uppercase gate (which keys on the after-slash segment) but
    // is rejected by `reject_qualified_binder_head` INSIDE the shared shape
    // parser, so it rejects for BOTH the `deftrait` head and the `impl` echoed
    // head, located at the con_var element.
    #[test]
    fn slash_bearing_con_var_rejected_in_both_deftrait_and_impl() {
        let deftrait_src = "(deftrait (Functor prim/x) (fmap [g self] self))";
        let deftrait_err = parse_and_build_program(deftrait_src)
            .expect_err("slash-bearing con_var in a deftrait head is rejected");
        assert!(
            deftrait_err.message().contains("qualified name"),
            "deftrait con_var qualified-binder message; got: {}",
            deftrait_err.message()
        );
        assert_err_span_at(deftrait_src, &deftrait_err, "prim/x", 0);

        let impl_src = "(impl (Functor prim/x) (Functor Option) (defn fmap [g self] self))";
        let impl_err = parse_and_build_program(impl_src)
            .expect_err("slash-bearing con_var in an impl echoed head is rejected");
        assert!(
            impl_err.message().contains("qualified name"),
            "impl con_var qualified-binder message; got: {}",
            impl_err.message()
        );
        assert_err_span_at(impl_src, &impl_err, "prim/x", 0);
    }

    // spec: spec/05-definitions.md §5.2 — a `deftype` type name must start
    // uppercase. The `(Name params…)` head arm must enforce this the SAME as the
    // bare `Symbol` arm's match guard; before S113 the list arm silently accepted
    // a lowercase head `(deftype (point a) …)` (audit S113 finding 2). Reject is
    // located at the head-name element; the uppercase-head twin still parses.
    #[test]
    fn deftype_parenthesized_head_lowercase_rejected_uppercase_twin_accepts() {
        let src = "(deftype (point a) [:a x])";
        let err = parse_and_build_program(src)
            .expect_err("a lowercase parenthesized deftype head must be rejected");
        assert!(
            err.message().contains("must start with uppercase"),
            "the reject names the uppercase-head rule; got: {}",
            err.message()
        );
        assert_err_span_at(src, &err, "point", 0);
        // The uppercase-head twin parses.
        assert!(
            parse_and_build_program("(deftype (Point a) [:a x])").is_ok(),
            "the uppercase parenthesized head `(Point a)` must parse"
        );
    }

    // spec: spec/08-modules.md §8.5 — `type_expr_to_trait_ref` no longer
    // re-splits (P7 / FIXME 0589): every name reaching it is already
    // module-split upstream. This guards the RETIREMENT of its third
    // `rsplit_once('/')` copy — a stacked qualified bound must still land the
    // module on the `TraitRef`. `:fmt/Eq :Display a` folds a run of two into
    // `Bounds`, and the qualified bound keeps `module = Some("fmt")`.
    #[test]
    fn type_expr_to_trait_ref_trusts_upstream_split_no_resplit() {
        // Direct: a qualified-uppercase annotation is split upstream by
        // `build_type_expr` (`Named`), and the reshape preserves the module.
        let tr = type_expr_to_trait_ref(build_name_type("fmt/Eq"));
        assert_eq!(tr.module.as_deref(), Some("fmt"));
        assert_eq!(tr.name.as_ref(), "Eq");
        // A bare bound stays module-less.
        let bare = type_expr_to_trait_ref(build_name_type("Display"));
        assert_eq!(bare.module, None);
        assert_eq!(bare.name.as_ref(), "Display");
        // Integration: a stacked run `:fmt/Eq :Display a` on a param folds into
        // `Bounds` with the qualified module preserved on the first bound.
        let prog =
            parse_and_build_program("(defn f [:fmt/Eq :Display a x] x)").unwrap();
        match &prog[0] {
            TopLevel::Defn(d) => match &d.variants[0].params[0].1 {
                Some(TypeExpr::Bounds(bounds)) => {
                    assert_eq!(bounds.len(), 2, "two stacked bounds");
                    assert_eq!(bounds[0].module.as_deref(), Some("fmt"));
                    assert_eq!(bounds[0].name.as_ref(), "Eq");
                    assert_eq!(bounds[1].module, None);
                    assert_eq!(bounds[1].name.as_ref(), "Display");
                }
                other => panic!("expected Bounds carrier, got {other:?}"),
            },
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // spec: spec/03-types.md §3.3 + FIXME 0589/0661 — `build_impl_target` is the
    // THIRD type-var decision point. A qualified-LOWERCASE type-arg in an impl
    // target (`(impl Show (Pair mod/x) …)`) is NOT a bare type var; it routes
    // through the §8.5 splitter to `Named`, never a slash-carrying `TypeVar`
    // (Principle 18). The bare-lowercase twin still mints a `TypeVar`.
    #[test]
    fn impl_target_qualified_lowercase_arg_routes_to_named_not_typevar() {
        let prog = parse_and_build_program(
            "(impl Show (Pair mod/x) (defn show [s] s))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => match &imp.target {
                TypeExpr::Applied(head, args) => {
                    assert_eq!(head.name.as_ref(), "Pair");
                    match &args[0] {
                        TypeExpr::Named(n) => {
                            assert_eq!(n.module.as_deref(), Some("mod"));
                            assert_eq!(n.name.as_ref(), "x");
                        }
                        other => panic!("expected Named (module split off), got {other:?}"),
                    }
                }
                other => panic!("expected Applied, got {other:?}"),
            },
            other => panic!("expected TraitImpl, got {other:?}"),
        }
        // Bare-lowercase twin: `a` stays a `TypeVar`.
        let bare = parse_and_build_program(
            "(impl Show (Pair a) (defn show [s] s))",
        ).unwrap();
        match &bare[0] {
            TopLevel::TraitImpl(imp) => match &imp.target {
                TypeExpr::Applied(_, args) => {
                    assert!(matches!(&args[0], TypeExpr::TypeVar(v) if v.as_ref() == "a"));
                }
                other => panic!("expected Applied, got {other:?}"),
            },
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: spec/07-traits.md §7.2 + FIXME 0661 — the CONSTRAINED type variable in
    // an impl target `(Type :Constraint var)` is a type-var BINDER; a qualified
    // spelling (`:Eq mod/a`) is a qualified binder and rejects (con_var §3.1
    // precedent), located at the var. The bare-var twin accepts and keys the
    // constraint on the bare var name.
    #[test]
    fn impl_target_qualified_constrained_var_rejected_bare_twin_accepts() {
        let src = "(impl Show (Pair :Eq mod/a) (defn show [s] s))";
        let err = parse_and_build_program(src)
            .expect_err("a qualified constrained type-var binder is rejected");
        assert!(
            err.message().contains("qualified name") && err.message().contains("binder"),
            "the reject names the qualified-binder rule; got: {}",
            err.message()
        );
        assert_err_span_at(src, &err, "mod/a", 0);
        // Bare-var twin: accepts, constraint keyed on the bare var `a`.
        let prog = parse_and_build_program(
            "(impl Show (Pair :Eq a) (defn show [s] s))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.type_constraints.len(), 1);
                assert_eq!(imp.type_constraints[0].0.as_ref(), "a");
                assert_eq!(imp.type_constraints[0].1.name.as_ref(), "Eq");
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // -- 0365 dotted-accessor transport invariance (frontend pass-through) --

    // spec: spec/08-modules.md §8.5.2 — the frontend transports a dotted member
    // name VERBATIM: `(Box.v b)` reads as a head `Sexp::Symbol("Box.v")` and
    // lowers to a head `Expr::Var { name: "Box.v" }`, un-split and un-rejected.
    // Field-accessor resolution is typecheck's; the frontend must never rewrite
    // the dotted form (the resolver in later waves depends on this transport).
    #[test]
    fn build_dotted_field_accessor_transports_verbatim() {
        // Reader: one symbol head with the dot retained.
        let sexps = crate::reader::parse("(Box.v b)").unwrap();
        match &sexps[0] {
            Sexp::List(children, _) => match &children[0] {
                Sexp::Symbol(s, _) => assert_eq!(s, "Box.v"),
                other => panic!("expected Symbol head, got {other:?}"),
            },
            other => panic!("expected List, got {other:?}"),
        }
        // Builder: head lowers to Expr::Var verbatim.
        match parse_and_build_expr("(Box.v b)").unwrap() {
            Expr::Apply { callee, .. } => match callee.as_ref() {
                Expr::Var { name, .. } => assert_eq!(name.as_ref(), "Box.v"),
                other => panic!("expected Var head, got {other:?}"),
            },
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: spec/08-modules.md §8.5.2 — companion: the constructor dotted case
    // (`Option.Some`) and the operator-member case (`Num.+`) ride the identical
    // member-agnostic transport, documenting that the lowercase field-accessor
    // member is not special-cased relative to existing dotted forms.
    #[test]
    fn build_dotted_constructor_and_operator_members_transport_verbatim() {
        match parse_and_build_expr("(Option.Some 1)").unwrap() {
            Expr::Apply { callee, .. } => match callee.as_ref() {
                Expr::Var { name, .. } => assert_eq!(name.as_ref(), "Option.Some"),
                other => panic!("expected Var head, got {other:?}"),
            },
            other => panic!("expected Apply, got {other:?}"),
        }
        match parse_and_build_expr("(Num.+ 1 2)").unwrap() {
            Expr::Apply { callee, .. } => match callee.as_ref() {
                Expr::Var { name, .. } => assert_eq!(name.as_ref(), "Num.+"),
                other => panic!("expected Var head, got {other:?}"),
            },
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // -- Type annotations --

    // spec: 02-grammar §2.8.2 — simple named type annotation on param
    #[test]
    fn test_type_annotation_simple() {
        // (fn [:Int x] x) — annotation on param
        match parse_and_build_expr("(fn [:Int x] x)").unwrap() {
            Expr::Lambda { params, .. } => {
                assert_eq!(params.len(), 1);
                match params[0].1.as_ref().unwrap() {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                    other => panic!("expected Named, got {other:?}"),
                }
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.4.2 — type variable annotation on param
    #[test]
    fn test_type_annotation_type_var() {
        match parse_and_build_expr("(fn [:a x] x)").unwrap() {
            Expr::Lambda { params, .. } => {
                assert_eq!(params.len(), 1);
                match params[0].1.as_ref().unwrap() {
                    TypeExpr::TypeVar(v) => assert_eq!(*v, "a"),
                    other => panic!("expected TypeVar, got {other:?}"),
                }
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.4.5 — function type annotation with bare colon
    #[test]
    fn test_type_annotation_fn_type() {
        // (fn [: (Fn [Int] Int) f] (f 42))
        match parse_and_build_expr("(fn [: (Fn [Int] Int) f] (f 42))").unwrap() {
            Expr::Lambda { params, .. } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].0, "f");
                match params[0].1.as_ref().unwrap() {
                    TypeExpr::FnType(fn_params, ret) => {
                        assert_eq!(fn_params.len(), 1);
                        match &fn_params[0] {
                            TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                            other => panic!("expected Named, got {other:?}"),
                        }
                        match ret.as_ref() {
                            TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                            other => panic!("expected Named, got {other:?}"),
                        }
                    }
                    other => panic!("expected FnType, got {other:?}"),
                }
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    // -- Empty application --

    // spec: 02-grammar §2.3.6 — empty application is an error
    #[test]
    fn test_empty_application_rejected() {
        let err = parse_and_build_expr("()").unwrap_err();
        assert!(err.message().contains("empty application"));
    }

    // -- Spans --

    // spec: 02-grammar §2.3.1 — expression span tracking
    #[test]
    fn test_expr_span() {
        let expr = parse_and_build_expr("42").unwrap();
        assert_eq!(expr.span(), Span::new(0, 2));
    }

    // spec: 02-grammar §2.3.3 — let expression span tracking
    #[test]
    fn test_let_span() {
        let expr = parse_and_build_expr("(let [x 1] x)").unwrap();
        assert_eq!(expr.span(), Span::new(0, 13));
    }

    // -- Nested expressions --

    // spec: 02-grammar §2.3.4 — nested let inside if branch
    #[test]
    fn test_nested_let_in_if() {
        let expr = parse_and_build_expr("(if true (let [x 1] x) 0)").unwrap();
        match expr {
            Expr::If { then_branch, .. } => {
                assert!(matches!(then_branch.as_ref(), Expr::Let { .. }));
            }
            other => panic!("expected If, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.5 — lambda in let binding value
    #[test]
    fn test_lambda_in_let() {
        let expr = parse_and_build_expr("(let [f (fn [x] x)] (f 42))").unwrap();
        match expr {
            Expr::Let { bindings, .. } => {
                assert!(matches!(&bindings[0].1, Expr::Lambda { .. }));
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    // -- Unexpected reader-macro forms (should be handled by expander) --

    // spec: 01-lexical §1.6 — quote form unexpected in AST builder (expander should handle)
    #[test]
    fn test_reject_quote() {
        let err = parse_and_build_expr("'foo").unwrap_err();
        assert!(err.message().contains("unexpected quote form"));
        assert!(err.message().contains("should have been expanded"));
    }

    // spec: 01-lexical §1.6 — quasiquote form unexpected in AST builder (expander should handle)
    #[test]
    fn test_reject_quasiquote() {
        let err = parse_and_build_expr("`foo").unwrap_err();
        assert!(err.message().contains("unexpected quasiquote form"));
        assert!(err.message().contains("should have been expanded"));
    }

    // spec: 01-lexical §1.6 — unquote form unexpected in AST builder (expander should handle)
    #[test]
    fn test_reject_unquote() {
        let err = parse_and_build_expr("~x").unwrap_err();
        assert!(err.message().contains("unexpected unquote form"));
        assert!(err.message().contains("should have been expanded"));
    }

    // spec: 01-lexical §1.6 — unquote-splicing form unexpected in AST builder (expander should handle)
    #[test]
    fn test_reject_unquote_splicing() {
        let err = parse_and_build_expr("~@xs").unwrap_err();
        assert!(err.message().contains("unexpected unquote-splicing form"));
        assert!(err.message().contains("should have been expanded"));
    }

    // spec: 01-lexical §1.6 — anonymous function form rejected; the NYI message
    // says what to write instead (no retired ring axis).
    #[test]
    fn test_reject_anon_fn() {
        let err = parse_and_build_expr("#(+ %1 %2)").unwrap_err();
        assert!(err.message().contains("anonymous-function"));
        assert!(err.message().contains("(fn"));
        assert!(!err.message().contains("Ring"));
    }

    // spec: 01-lexical §1.4.7 — percent param rejected in AST; the NYI message
    // names the explicit-`fn` alternative, no ring number.
    #[test]
    fn test_reject_percent_param() {
        let err = parse_and_build_expr("%1").unwrap_err();
        assert!(err.message().contains("percent parameters"));
        assert!(err.message().contains("(fn"));
        assert!(!err.message().contains("Ring"));
    }

    // spec: 01-lexical §1.4.6 — gensym dollar rejected in AST; message names the
    // `let`-bound-name alternative, no ring number.
    #[test]
    fn test_reject_gensym_dollar() {
        let err = parse_and_build_expr("$foo").unwrap_err();
        assert!(err.message().contains("gensym"));
        assert!(err.message().contains("let"));
        assert!(!err.message().contains("Ring"));
    }

    // spec: 01-lexical §1.4.8 — ampersand rejected in AST; no ring number.
    #[test]
    fn test_reject_ampersand() {
        let err = parse_and_build_expr("&rest").unwrap_err();
        assert!(err.message().contains("rest parameters"));
        assert!(!err.message().contains("Ring"));
    }

    // spec: 01-lexical §1.4.6 — gensym shorthand rejected in AST; no ring number.
    #[test]
    fn test_reject_gensym_shorthand() {
        let err = parse_and_build_expr("foo#").unwrap_err();
        assert!(err.message().contains("gensym"));
        assert!(!err.message().contains("Ring"));
    }

    // -- Ring 1: String literal --

    // spec: 02-grammar §2.3.1 — empty string literal in AST
    #[test]
    fn test_string_literal_empty() {
        match parse_and_build_expr("\"\"").unwrap() {
            Expr::StringLit { value, .. } => assert_eq!(value, ""),
            other => panic!("expected StringLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.1 — string literal with escape sequences in AST
    #[test]
    fn test_string_literal_with_escapes() {
        match parse_and_build_expr("\"line1\\nline2\"").unwrap() {
            Expr::StringLit { value, .. } => assert_eq!(value, "line1\nline2"),
            other => panic!("expected StringLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.1 — string literal span tracking in AST
    #[test]
    fn test_string_literal_span() {
        let expr = parse_and_build_expr("\"hello\"").unwrap();
        assert_eq!(expr.span(), Span::new(0, 7));
    }

    // spec: 02-grammar §2.3.3 — string literal in let binding value
    #[test]
    fn test_string_in_let_binding() {
        match parse_and_build_expr("(let [s \"hello\"] s)").unwrap() {
            Expr::Let { bindings, .. } => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "s");
                match &bindings[0].1 {
                    Expr::StringLit { value, .. } => assert_eq!(value, "hello"),
                    other => panic!("expected StringLit in binding, got {other:?}"),
                }
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.6 — string literal as function argument
    #[test]
    fn test_string_as_function_argument() {
        match parse_and_build_expr("(f \"world\")").unwrap() {
            Expr::Apply { args, .. } => {
                assert_eq!(args.len(), 1);
                match &args[0] {
                    Expr::StringLit { value, .. } => assert_eq!(value, "world"),
                    other => panic!("expected StringLit, got {other:?}"),
                }
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.4 — string literals in if branches
    #[test]
    fn test_string_in_if_branches() {
        match parse_and_build_expr("(if true \"yes\" \"no\")").unwrap() {
            Expr::If {
                then_branch,
                else_branch,
                ..
            } => {
                match then_branch.as_ref() {
                    Expr::StringLit { value, .. } => assert_eq!(value, "yes"),
                    other => panic!("expected StringLit in then, got {other:?}"),
                }
                match else_branch.as_ref() {
                    Expr::StringLit { value, .. } => assert_eq!(value, "no"),
                    other => panic!("expected StringLit in else, got {other:?}"),
                }
            }
            other => panic!("expected If, got {other:?}"),
        }
    }

    // -- Ring 1: Docstring interaction audit --

    // spec: 02-grammar §2.7 — docstring captured between name and params
    #[test]
    fn test_docstring_captured_in_defn() {
        let prog =
            parse_and_build_program("(defn greet \"docstring\" [x] x)").unwrap();
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.docstring.as_deref(), Some("docstring"));
                assert_eq!(defn.params().len(), 1);
                assert_eq!(defn.params()[0].0, "x");
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.7 — string in let binding is value, not docstring
    #[test]
    fn test_string_in_let_is_not_docstring() {
        // A string in a let binding position is a value, not a docstring.
        match parse_and_build_expr("(let [s \"hello\"] s)").unwrap() {
            Expr::Let { bindings, body, .. } => {
                match &bindings[0].1 {
                    Expr::StringLit { value, .. } => assert_eq!(value, "hello"),
                    other => panic!("expected StringLit, got {other:?}"),
                }
                match body.as_ref() {
                    Expr::Var { name, .. } => assert_eq!(name, "s"),
                    other => panic!("expected Var in body, got {other:?}"),
                }
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.7 — docstring is None when absent
    #[test]
    fn test_docstring_not_captured_when_absent() {
        let prog = parse_and_build_program("(defn f [x] x)").unwrap();
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert!(defn.docstring.is_none());
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.7 — deftype docstring between head and body
    #[test]
    fn test_docstring_in_deftype() {
        let prog =
            parse_and_build_program("(deftype Color \"Primary colors\" Red Green Blue)")
                .unwrap();
        match &prog[0] {
            TopLevel::TypeDef { docstring, .. } => {
                assert_eq!(docstring.as_deref(), Some("Primary colors"));
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // -- Ring 1: TypeExpr::Applied via annotation --

    // spec: 02-grammar §2.4.4 — applied type annotation :(Option Int)
    #[test]
    fn test_type_annotation_applied() {
        // :(Option Int) expr -> Annotate { Applied("Option", [Named("Int")]) }
        match parse_and_build_expr("(f :(Option Int) 42)").unwrap() {
            Expr::Apply { args, .. } => {
                assert_eq!(args.len(), 1);
                match &args[0] {
                    Expr::Annotate { annotation, .. } => match annotation {
                        TypeExpr::Applied(name, type_args) => {
                            assert_eq!(name.name.as_ref(), "Option");
                            assert_eq!(type_args.len(), 1);
                            match &type_args[0] {
                                TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                                other => panic!("expected Named(Int), got {other:?}"),
                            }
                        }
                        other => panic!("expected Applied, got {other:?}"),
                    },
                    other => panic!("expected Annotate, got {other:?}"),
                }
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.4.4 — applied type with multiple type args
    #[test]
    fn test_type_annotation_applied_multiple_args() {
        // :(Map String Int) expr
        match parse_and_build_expr("(f :(Map String Int) x)").unwrap() {
            Expr::Apply { args, .. } => {
                assert_eq!(args.len(), 1);
                match &args[0] {
                    Expr::Annotate { annotation, .. } => match annotation {
                        TypeExpr::Applied(name, type_args) => {
                            assert_eq!(name.name.as_ref(), "Map");
                            assert_eq!(type_args.len(), 2);
                        }
                        other => panic!("expected Applied, got {other:?}"),
                    },
                    other => panic!("expected Annotate, got {other:?}"),
                }
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // -- Ring 1: Constructor pattern with field bindings --

    // spec: 02-grammar §2.5.1 — constructor pattern with single field binding
    #[test]
    fn test_constructor_pattern_with_single_binding() {
        match parse_and_build_expr("(match x [(Some v) v])").unwrap() {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 1);
                match &arms[0].pattern {
                    Pattern::Constructor { name, bindings, .. } => {
                        assert_eq!(name.name.as_ref(), "Some");
                        assert_eq!(bindings.len(), 1);
                        assert_eq!(bindings[0], "v");
                    }
                    other => panic!("expected Constructor, got {other:?}"),
                }
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.5.1 — constructor pattern with multiple field bindings
    #[test]
    fn test_constructor_pattern_with_multiple_bindings() {
        match parse_and_build_expr("(match p [(Point x y) (+ x y)])").unwrap() {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 1);
                match &arms[0].pattern {
                    Pattern::Constructor { name, bindings, .. } => {
                        assert_eq!(name.name.as_ref(), "Point");
                        assert_eq!(bindings.len(), 2);
                        assert_eq!(bindings[0], "x");
                        assert_eq!(bindings[1], "y");
                    }
                    other => panic!("expected Constructor, got {other:?}"),
                }
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // -- Ring 1: Product type with fields --

    // spec: 02-grammar §2.2.2 — product type field type expressions
    #[test]
    fn test_product_type_field_types() {
        let prog = parse_and_build_program("(deftype Point [:Int x :Int y])").unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name,
                constructors,
                ..
            } => {
                assert_eq!(name, "Point");
                assert_eq!(constructors.len(), 1);
                let ctor = &constructors[0];
                assert_eq!(ctor.name, "Point");
                assert_eq!(ctor.fields.len(), 2);
                assert_eq!(ctor.fields[0].name, "x");
                match &ctor.fields[0].type_expr {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                    other => panic!("expected Named(Int), got {other:?}"),
                }
                assert_eq!(ctor.fields[1].name, "y");
                match &ctor.fields[1].type_expr {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                    other => panic!("expected Named(Int), got {other:?}"),
                }
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // -- Ring 1: Sum type with data constructors --

    // spec: 02-grammar §2.2.2 — sum type constructor details
    #[test]
    fn test_sum_type_constructor_details() {
        let prog = parse_and_build_program(
            "(deftype (Option a) None (Some [:a val]))",
        )
        .unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name,
                type_params,
                constructors,
                ..
            } => {
                assert_eq!(name, "Option");
                assert_eq!(type_params, &["a"]);
                assert_eq!(constructors.len(), 2);
                // None: nullary
                assert_eq!(constructors[0].name, "None");
                assert!(constructors[0].fields.is_empty());
                // Some: one field
                assert_eq!(constructors[1].name, "Some");
                assert_eq!(constructors[1].fields.len(), 1);
                assert_eq!(constructors[1].fields[0].name, "val");
                match &constructors[1].fields[0].type_expr {
                    TypeExpr::TypeVar(v) => assert_eq!(*v, "a"),
                    other => panic!("expected TypeVar(a), got {other:?}"),
                }
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // -- Ring 1: REPL string literal --

    // spec: 02-grammar §2.3.1 — REPL string literal expression
    #[test]
    fn test_repl_string_literal() {
        match parse_and_build_repl("\"hello\"").unwrap() {
            TopLevel::Expr(Expr::StringLit { value, .. }) => {
                assert_eq!(value, "hello");
            }
            other => panic!("expected Expr(StringLit), got {other:?}"),
        }
    }

    // -- Ring 1: Vec literals --

    // spec: 02-grammar §2.3.9 — Vec literal with integers
    #[test]
    fn test_vec_lit_integers() {
        match parse_and_build_expr("[1 2 3]").unwrap() {
            Expr::VecLit { elements, .. } => {
                assert_eq!(elements.len(), 3);
                match &elements[0] {
                    Expr::IntLit { value, .. } => assert_eq!(*value, 1),
                    other => panic!("expected IntLit, got {other:?}"),
                }
                match &elements[2] {
                    Expr::IntLit { value, .. } => assert_eq!(*value, 3),
                    other => panic!("expected IntLit, got {other:?}"),
                }
            }
            other => panic!("expected VecLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.9 — empty Vec literal
    #[test]
    fn test_vec_lit_empty() {
        match parse_and_build_expr("[]").unwrap() {
            Expr::VecLit { elements, .. } => {
                assert_eq!(elements.len(), 0);
            }
            other => panic!("expected VecLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.9 — nested Vec literals
    #[test]
    fn test_vec_lit_nested() {
        match parse_and_build_expr("[[1] [2]]").unwrap() {
            Expr::VecLit { elements, .. } => {
                assert_eq!(elements.len(), 2);
                match &elements[0] {
                    Expr::VecLit { elements: inner, .. } => {
                        assert_eq!(inner.len(), 1);
                        match &inner[0] {
                            Expr::IntLit { value, .. } => assert_eq!(*value, 1),
                            other => panic!("expected IntLit, got {other:?}"),
                        }
                    }
                    other => panic!("expected nested VecLit, got {other:?}"),
                }
            }
            other => panic!("expected VecLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.9 — Vec literal with mixed element types
    #[test]
    fn test_vec_lit_mixed_types() {
        match parse_and_build_expr("[true \"hello\" 42]").unwrap() {
            Expr::VecLit { elements, .. } => {
                assert_eq!(elements.len(), 3);
                assert!(matches!(&elements[0], Expr::BoolLit { value: true, .. }));
                assert!(matches!(&elements[1], Expr::StringLit { .. }));
                assert!(matches!(&elements[2], Expr::IntLit { value: 42, .. }));
            }
            other => panic!("expected VecLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.8.2 — brackets in defn are param list, not VecLit
    #[test]
    fn test_defn_params_still_work() {
        // Brackets in defn position are still parameter lists, not VecLit
        match parse_and_build_program("(defn foo [x] x)").unwrap().as_slice() {
            [TopLevel::Defn(defn)] => {
                assert_eq!(defn.name, "foo");
                assert_eq!(defn.params().len(), 1);
                assert_eq!(defn.params()[0].0, "x");
            }
            other => panic!("expected single Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.9 — Vec literal in let binding value
    #[test]
    fn test_vec_lit_in_let_binding() {
        // Vec literal in a let binding value position
        match parse_and_build_expr("(let [v [1 2 3]] v)").unwrap() {
            Expr::Let { bindings, .. } => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "v");
                match &bindings[0].1 {
                    Expr::VecLit { elements, .. } => assert_eq!(elements.len(), 3),
                    other => panic!("expected VecLit in binding, got {other:?}"),
                }
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.9 — Vec literal as function argument
    #[test]
    fn test_vec_lit_as_function_arg() {
        // Vec literal as argument to a function
        match parse_and_build_expr("(f [1 2])").unwrap() {
            Expr::Apply { args, .. } => {
                assert_eq!(args.len(), 1);
                match &args[0] {
                    Expr::VecLit { elements, .. } => assert_eq!(elements.len(), 2),
                    other => panic!("expected VecLit arg, got {other:?}"),
                }
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // -- Duplicate parameter names --

    // spec: 05-definitions §5 — duplicate param names rejected in defn (batch)
    #[test]
    fn test_duplicate_param_names_defn_batch() {
        let err = parse_and_build_program("(defn bad [x x] (add-i64 x x))").unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("duplicate parameter name 'x'"), "got: {msg}");
    }

    // spec: 05-definitions §5 — duplicate param names rejected in defn (REPL)
    #[test]
    fn test_duplicate_param_names_defn_repl() {
        let err = parse_and_build_repl("(defn bad [x x] (add-i64 x x))").unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("duplicate parameter name 'x'"), "got: {msg}");
    }

    // spec: 04-expressions §4 — duplicate param names rejected in lambda
    #[test]
    fn test_duplicate_param_names_lambda() {
        let err = parse_and_build_expr("(fn [a a] a)").unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("duplicate parameter name 'a'"), "got: {msg}");
    }

    // spec: 05-definitions §5 — distinct param names accepted
    #[test]
    fn test_distinct_param_names_ok() {
        assert!(parse_and_build_program("(defn good [x y] (add-i64 x y))").is_ok());
    }

    // ---------------------------------------------------------------------
    // build_form direct tests (Wave 3a-β — FIXME 0156)
    // ---------------------------------------------------------------------

    fn parse_one(input: &str) -> Sexp {
        let sexps = crate::reader::parse(input).unwrap();
        sexps.into_iter().next().unwrap()
    }

    // spec: 02-grammar §2.2.1 + facade frontend.md §"Free functions" — defn
    // yields exactly one ParsedEntry::Def.
    #[test]
    fn build_form_defn_yields_single_def() {
        let entries = build_form(&parse_one("(defn add [a b] (add-i64 a b))")).unwrap();
        assert_eq!(entries.len(), 1, "defn should yield 1 entry");
        match &entries[0] {
            ParsedEntry::Def { name, variants, visibility, .. } => {
                assert_eq!(name.as_ref(), "add");
                assert_eq!(variants.len(), 1);
                assert_eq!(variants[0].params.len(), 2);
                assert_eq!(*visibility, Visibility::Public);
            }
            other => panic!("expected ParsedEntry::Def, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.6 — defn- yields Private visibility.
    #[test]
    fn build_form_defn_private() {
        let entries = build_form(&parse_one("(defn- helper [x] x)")).unwrap();
        match &entries[0] {
            ParsedEntry::Def { visibility, .. } => {
                assert_eq!(*visibility, Visibility::Private);
            }
            other => panic!("expected ParsedEntry::Def, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.2 + facade — deftype with N constructors yields
    // 1 TypeDef + N Constructor entries (in source-declaration order).
    #[test]
    fn build_form_deftype_yields_typedef_plus_per_constructor() {
        // 3 variants → 4 entries.
        let entries = build_form(&parse_one("(deftype Color Red Green Blue)")).unwrap();
        assert_eq!(entries.len(), 4, "1 TypeDef + 3 Constructors expected");
        match &entries[0] {
            ParsedEntry::TypeDef { name, constructors, .. } => {
                assert_eq!(name.as_ref(), "Color");
                assert_eq!(constructors.len(), 3);
            }
            other => panic!("entries[0] should be TypeDef, got {other:?}"),
        }
        // Ordering: TypeDef, then Constructors in source order.
        for (i, expected_name) in ["Red", "Green", "Blue"].iter().enumerate() {
            match &entries[i + 1] {
                ParsedEntry::Constructor { name, of_type, .. } => {
                    assert_eq!(name.as_ref(), *expected_name);
                    assert_eq!(of_type.as_ref(), "Color");
                }
                other => panic!("entries[{}] should be Constructor, got {other:?}", i + 1),
            }
        }
    }

    // spec: 02-grammar §2.2.2 — product type (single bracketed-fields ctor)
    // yields 1 TypeDef + 1 Constructor.
    #[test]
    fn build_form_deftype_product_yields_two_entries() {
        let entries = build_form(&parse_one("(deftype Point [:Int x :Int y])")).unwrap();
        assert_eq!(entries.len(), 2);
        assert!(matches!(&entries[0], ParsedEntry::TypeDef { .. }));
        match &entries[1] {
            ParsedEntry::Constructor { name, of_type, fields, .. } => {
                assert_eq!(name.as_ref(), "Point");
                assert_eq!(of_type.as_ref(), "Point");
                assert_eq!(fields.len(), 2);
            }
            other => panic!("entries[1] should be Constructor, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.3 — deftrait yields exactly one TraitDecl.
    #[test]
    fn build_form_deftrait_yields_single_trait_decl() {
        let entries = build_form(&parse_one("(deftrait Display (show [self] String))")).unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            ParsedEntry::TraitDecl { decl } => {
                assert_eq!(decl.name.as_ref(), "Display");
                assert_eq!(decl.methods.len(), 1);
            }
            other => panic!("expected ParsedEntry::TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.4 — impl yields exactly one TraitImpl.
    #[test]
    fn build_form_impl_yields_single_trait_impl() {
        let entries = build_form(
            &parse_one("(impl Display Int (defn show [x] (int-to-string x)))"),
        )
        .unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            ParsedEntry::TraitImpl { impl_ } => {
                assert_eq!(impl_.trait_name.name.as_ref(), "Display");
                match &impl_.target {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                    other => panic!("expected Named(Int), got {other:?}"),
                }
            }
            other => panic!("expected ParsedEntry::TraitImpl, got {other:?}"),
        }
    }

    // spec: 09-macros.md + facade — defmacro yields one ParsedEntry::Macro
    // carrying ALL clauses in DefmacroInfo.clauses.
    #[test]
    fn build_form_defmacro_yields_single_macro_with_all_clauses() {
        let entries = build_form(
            &parse_one("(defmacro when ([cond body] (if cond body 0)))"),
        )
        .unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            ParsedEntry::Macro { info } => {
                assert_eq!(info.name.as_ref(), "when");
                assert_eq!(info.clauses.len(), 1);
                assert!(!info.is_private);
            }
            other => panic!("expected ParsedEntry::Macro, got {other:?}"),
        }
    }

    // spec: 09-macros.md — multi-clause defmacro packages every clause
    // inside one Macro entry (NOT per-clause Macro entries).
    #[test]
    fn build_form_multi_clause_defmacro_yields_single_macro() {
        let entries = build_form(
            &parse_one("(defmacro pick ([x] x) ([x y] x) ([x y z] x))"),
        )
        .unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            ParsedEntry::Macro { info } => {
                assert_eq!(info.clauses.len(), 3);
            }
            other => panic!("expected single Macro entry, got {other:?}"),
        }
    }

    // facade — `begin` must be flattened by the orchestrator; reaching
    // `build_form` is a caller bug.
    #[test]
    fn build_form_rejects_begin() {
        let err = build_form(&parse_one("(begin 1 2)")).unwrap_err();
        let msg = format!("{err}");
        assert!(
            msg.contains("begin") && msg.contains("flatten"),
            "got: {msg}"
        );
    }

    // facade — structural decls must be peeled by extract_module_declarations.
    #[test]
    fn build_form_rejects_import() {
        let err = build_form(&parse_one("(import [user [foo]])")).unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("structural"), "got: {msg}");
    }

    // facade — `build_form` rejects bare expressions (route to build_expr).
    #[test]
    fn build_form_rejects_bare_expression() {
        // A bare int isn't a top-level form vocabulary entry.
        let err = build_form(&parse_one("42")).unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("top-level form"), "got: {msg}");
    }

    // facade — unknown top-level head produces a clear error.
    #[test]
    fn build_form_rejects_unknown_head() {
        let err = build_form(&parse_one("(woot foo bar)")).unwrap_err();
        let msg = format!("{err}");
        assert!(
            msg.contains("unknown top-level form"),
            "got: {msg}"
        );
    }

    // facade — `build_expr` is a pure structural transform; no macro lookup.
    #[test]
    fn build_expr_pure_int_literal() {
        let expr = build_expr(&parse_one("42")).unwrap();
        assert!(matches!(expr, Expr::IntLit { value: 42, .. }));
    }

    // FIXME 0230 — `parse_type_expr` parses a bare named type.
    #[test]
    fn parse_type_expr_named() {
        let te = parse_type_expr("Int").unwrap();
        match te {
            TypeExpr::Named(r) => assert_eq!(r.name.as_ref(), "Int"),
            other => panic!("expected Named, got {other:?}"),
        }
    }

    // FIXME 0230 — `parse_type_expr` parses a type variable (lowercase).
    #[test]
    fn parse_type_expr_type_var() {
        let te = parse_type_expr("a").unwrap();
        assert!(matches!(te, TypeExpr::TypeVar(_)));
    }

    // FIXME 0589 (second decision point) — a qualified-LOWERCASE name in
    // type-expression position (`build_type_expr`, e.g. a `(Fn […])`/`(Option …)`
    // type-arg) is NOT a bare type var (spec §3.3); it routes to `Named` with the
    // module split off, never a `TypeVar` carrying the slash (Principle 18). The
    // sibling of `build_type_expr`'s routing — both type-var decision points
    // now enforce the invariant.
    #[test]
    fn parse_type_expr_qualified_lowercase_routes_to_named_not_typevar() {
        match parse_type_expr("mod/x").unwrap() {
            TypeExpr::Named(r) => {
                assert_eq!(r.module.as_deref(), Some("mod"));
                assert_eq!(r.name.as_ref(), "x");
            }
            other => panic!("expected Named (module split off), got {other:?}"),
        }
        // As a type-arg inside an applied form — the head splits, and the
        // qualified-lowercase arg is `Named`, not a slash-carrying `TypeVar`.
        match parse_type_expr("(Option mod/x)").unwrap() {
            TypeExpr::Applied(_, args) => match &args[0] {
                TypeExpr::Named(r) => {
                    assert_eq!(r.module.as_deref(), Some("mod"));
                    assert_eq!(r.name.as_ref(), "x");
                }
                other => panic!("expected Named type-arg, got {other:?}"),
            },
            other => panic!("expected Applied, got {other:?}"),
        }
        // Control: a BARE lowercase name still mints a `TypeVar`.
        assert!(matches!(parse_type_expr("a").unwrap(), TypeExpr::TypeVar(_)));
    }

    // FIXME 0230 — `parse_type_expr` parses a `(Fn [..] R)` form.
    #[test]
    fn parse_type_expr_fn() {
        let te = parse_type_expr("(Fn [Int] Bool)").unwrap();
        match te {
            TypeExpr::FnType(params, ret) => {
                assert_eq!(params.len(), 1);
                assert!(matches!(*ret, TypeExpr::Named(_)));
            }
            other => panic!("expected FnType, got {other:?}"),
        }
    }

    // FIXME 0230 — `parse_type_expr` parses an applied `(Name arg..)` form.
    #[test]
    fn parse_type_expr_applied() {
        let te = parse_type_expr("(Option Int)").unwrap();
        match te {
            TypeExpr::Applied(r, args) => {
                assert_eq!(r.name.as_ref(), "Option");
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected Applied, got {other:?}"),
        }
    }

    // FIXME 0230 — more than one form is rejected (string in / one out).
    #[test]
    fn parse_type_expr_rejects_multiple_forms() {
        let err = parse_type_expr("Int Bool").unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("single form"), "got: {msg}");
    }

    // FIXME 0230 — zero forms is rejected.
    #[test]
    fn parse_type_expr_rejects_empty() {
        let err = parse_type_expr("").unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("single form"), "got: {msg}");
    }

    // FIXME 0362 — a self-qualified type annotation `:t/Box` must split the
    // `module/Name` qualifier so it arrives downstream as
    // `TypeRef { module: Some("t"), name: "Box" }`, not the un-split
    // `TypeRef { module: None, name: "t/Box" }` (whose empty from-module is the
    // tell of the original `unknown type 't/Box' (from module '')` defect).
    #[test]
    fn annotation_name_splits_module_qualifier() {
        match build_name_type("t/Box") {
            TypeExpr::Named(r) => {
                assert_eq!(r.module.as_deref(), Some("t"));
                assert_eq!(r.name.as_ref(), "Box");
            }
            other => panic!("expected Named, got {other:?}"),
        }
    }

    // FIXME 0362 — a bare (unqualified) type name stays `module: None`.
    #[test]
    fn annotation_name_bare_stays_unqualified() {
        match build_name_type("Box") {
            TypeExpr::Named(r) => {
                assert_eq!(r.module, None);
                assert_eq!(r.name.as_ref(), "Box");
            }
            other => panic!("expected Named, got {other:?}"),
        }
    }

    // FIXME 0362 — a deep-qualified type name `a.b/Box` splits at the LAST `/`
    // (module = `a.b`, name = `Box`), matching the trait-ref precedent.
    #[test]
    fn annotation_name_deep_qualified_splits_at_last_slash() {
        match build_name_type("a.b/Box") {
            TypeExpr::Named(r) => {
                assert_eq!(r.module.as_deref(), Some("a.b"));
                assert_eq!(r.name.as_ref(), "Box");
            }
            other => panic!("expected Named, got {other:?}"),
        }
    }

    // FIXME 0589 — a qualified-LOWERCASE annotation (`user/int`) is NOT a bare
    // type var (spec §3.3 — a type var is a bare lowercase identifier). It must
    // route to `Named` (splitting the module off) so the downstream unknown-type
    // error names the module, NEVER to a `TypeVar` carrying the slash
    // (Principle 18 — a `TypeVar` must never carry a `/`).
    #[test]
    fn annotation_name_qualified_lowercase_routes_to_named_not_typevar() {
        match build_name_type("user/int") {
            TypeExpr::Named(r) => {
                assert_eq!(r.module.as_deref(), Some("user"));
                assert_eq!(r.name.as_ref(), "int");
            }
            other => panic!("expected Named (module split off), got {other:?}"),
        }
        // A deep-qualified lowercase name splits at the LAST slash too.
        match build_name_type("a.b/int") {
            TypeExpr::Named(r) => {
                assert_eq!(r.module.as_deref(), Some("a.b"));
                assert_eq!(r.name.as_ref(), "int");
            }
            other => panic!("expected Named, got {other:?}"),
        }
        // Control: a BARE lowercase name still mints a `TypeVar` (no slash).
        match build_name_type("a") {
            TypeExpr::TypeVar(v) => assert_eq!(v.as_ref(), "a"),
            other => panic!("expected TypeVar for a bare lowercase name, got {other:?}"),
        }
    }

    // FIXME 0362 — the qualifier split also applies in type-expression position
    // (`parse_type_expr` → `build_type_expr`), both for a bare qualified name
    // and for the applied `(t/Box arg)` head.
    #[test]
    fn parse_type_expr_splits_module_qualifier() {
        match parse_type_expr("t/Box").unwrap() {
            TypeExpr::Named(r) => {
                assert_eq!(r.module.as_deref(), Some("t"));
                assert_eq!(r.name.as_ref(), "Box");
            }
            other => panic!("expected Named, got {other:?}"),
        }
        match parse_type_expr("(t/Box Int)").unwrap() {
            TypeExpr::Applied(r, args) => {
                assert_eq!(r.module.as_deref(), Some("t"));
                assert_eq!(r.name.as_ref(), "Box");
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected Applied, got {other:?}"),
        }
    }

    // -------------------------------------------------------------------
    // Rendered-diagnostic tier (FIXME 0500)
    //
    // `ast_builder` emits ParseError diagnostics for malformed top-level
    // forms. This tier guards the P6 class (0485): the diagnostic MUST carry
    // a REAL source span (never a synthetic 1_000_000+ span), MUST name the
    // offending form, and MUST NOT leak a Debug-format struct dump.
    // Submodule × scenario-class per METHOD §2.2.
    // spec: repl/spec.md §"Self-documenting REPL" — no opaque errors.
    // -------------------------------------------------------------------
    mod rendered_diagnostics {
        use super::*;

        const SYNTHETIC_SPAN_BASE: u32 = 1_000_000;

        fn form_err(src: &str) -> cranelisp_types::CranelispError {
            let sexps = crate::reader::parse(src).expect("parse failed");
            build_form(&sexps[0]).expect_err("expected a build error")
        }

        fn assert_real_span(e: &cranelisp_types::CranelispError, src: &str) {
            let s = e.span();
            assert!(
                s.start < SYNTHETIC_SPAN_BASE && s.end < SYNTHETIC_SPAN_BASE,
                "build diagnostic carries a synthetic span {s}: {}",
                e.message(),
            );
            assert!(
                s.end as usize <= src.len(),
                "build span {s} exceeds source length {} for {src:?}",
                src.len(),
            );
        }

        fn assert_no_debug_artifacts(e: &cranelisp_types::CranelispError) {
            let m = e.message();
            assert!(!m.contains("Span {"), "message leaks a Debug span struct: {m}");
            assert!(!m.contains("Sexp::"), "message leaks a Debug Sexp variant: {m}");
            assert!(!m.contains("ErrorLocation"), "message leaks ErrorLocation: {m}");
        }

        // -- positive: message names what a defn is missing --

        // spec: 04-functions §4.1 — defn arity diagnostic.
        #[test]
        fn defn_missing_body_names_defn_with_real_span() {
            let e = form_err("(defn)");
            assert!(e.message().contains("defn"), "got: {}", e.message());
            assert_real_span(&e, "(defn)");
            assert_no_debug_artifacts(&e);
        }

        // -- edge: unknown top-level form echoes the offending head symbol --

        // spec: 02-grammar §2.9 — unknown top-level form.
        #[test]
        fn unknown_form_names_the_head_symbol() {
            let e = form_err("(frobnicate 1)");
            assert!(
                e.message().contains("frobnicate"),
                "message should name the unknown head symbol: {}",
                e.message(),
            );
            assert_real_span(&e, "(frobnicate 1)");
            assert_no_debug_artifacts(&e);
        }

        // -- edge: non-form input is diagnosed, not panicked --

        #[test]
        fn bare_atom_is_diagnosed_with_real_span() {
            let e = form_err("42");
            assert!(
                e.message().contains("form") || e.message().contains("list"),
                "got: {}",
                e.message(),
            );
            assert_real_span(&e, "42");
            assert_no_debug_artifacts(&e);
        }

        // -- negative: no internal artifacts leak across a spread of shapes --

        #[test]
        fn no_build_diagnostic_leaks_debug_or_synthetic_span() {
            for src in ["(defn)", "(frobnicate)", "42", "(deftype)", "(deftrait)"] {
                let e = form_err(src);
                assert_no_debug_artifacts(&e);
                assert_real_span(&e, src);
            }
        }
    }

    // -- Track D W-D1 seams: BD-A one-body-seam, deftype-ctor trailing, M2-TP1,
    //    RA-N5 bound-form-type, 0677 single splitter -------------------------
    mod track_d_wd1 {
        use super::*;

        // BD-A1: the four single-body operand positions accept a `:Type body`
        // ascription (spec §2.3.8), routed through the ONE `build_body_to_end`
        // seam. Each also has a bare-body positive twin.

        // spec: 03-types §2.3.8 — ascribed let body accepted (BD-A1, let position).
        #[test]
        fn let_body_ascription_builds() {
            let e = parse_and_build_expr("(let [x 41] :Int x)")
                .expect("an ascribed let body is valid (§2.3.8)");
            assert!(matches!(e, Expr::Let { .. }));
            assert!(parse_and_build_expr("(let [x 41] x)").is_ok());
        }

        // spec: 04-expressions §4.3 — a trailing form after the let body is a
        // located reject (BD-A2 sibling; `build_body_to_end` tail check).
        #[test]
        fn let_body_trailing_form_rejected() {
            let e = parse_and_build_expr("(let [x 1] x 9)")
                .expect_err("a trailing form after the let body is rejected");
            assert!(
                e.message().contains("trailing"),
                "the reject names the trailing form; got: {}",
                e.message(),
            );
        }

        // spec: 03-types §2.3.8 — ascribed `trace` operand accepted (BD-A1).
        #[test]
        fn trace_operand_ascription_builds() {
            assert!(parse_and_build_expr("(trace :Int 5)").is_ok());
            assert!(parse_and_build_expr("(trace 5)").is_ok());
        }

        // spec: 04-expressions §4.12 — a trailing form after the traced operand is
        // rejected (BD-A2 sibling; replaces the former blanket arity error).
        #[test]
        fn trace_trailing_form_rejected() {
            let e = parse_and_build_expr("(trace 5 9)")
                .expect_err("a trailing form after the trace operand is rejected");
            assert!(
                e.message().contains("trailing"),
                "the reject names the trailing form; got: {}",
                e.message(),
            );
        }

        // spec: 03-types §2.3.8 — ascribed impl-method body accepted (BD-A1); a
        // trailing form after it is rejected (BD-A2 — was a silent drop).
        #[test]
        fn impl_method_body_ascription_and_trailing() {
            assert!(parse_and_build_program(
                "(impl T Int (defn m [x] :Int x))"
            )
            .is_ok());
            let e = parse_and_build_program("(impl T Int (defn m [x] x 999))")
                .expect_err("a trailing form after an impl-method body is rejected");
            assert!(
                e.message().contains("trailing"),
                "the reject names the trailing form; got: {}",
                e.message(),
            );
        }

        // spec: 03-types §2.3.8 — ascribed trait default-method body accepted
        // (BD-A1); a trailing form after it is rejected (BD-A2).
        #[test]
        fn trait_default_body_ascription_and_trailing() {
            assert!(parse_and_build_program("(deftrait T (m [x] :Int x))").is_ok());
            let e = parse_and_build_program("(deftrait T (show [x] Int 999 888))")
                .expect_err("a trailing form after a method sig is rejected");
            assert!(
                e.message().contains("trailing"),
                "the reject names the trailing form; got: {}",
                e.message(),
            );
        }

        // spec: 05-definitions §5.2 — a form after a valid ctor field bracket is a
        // located reject, no longer silently dropped (deftype-ctor trailing; the
        // S107 pre-existing RED). Sibling of BD-A2.
        #[test]
        fn deftype_ctor_trailing_form_after_field_bracket_rejected() {
            let e = parse_and_build_program("(deftype Box (Box [:Int n] extra))")
                .expect_err("a form after the field bracket is rejected");
            assert!(
                e.message().contains("trailing"),
                "the reject names the trailing form; got: {}",
                e.message(),
            );
            // The well-formed one-field ctor still builds.
            assert!(parse_and_build_program("(deftype Box (Box [:Int n]))").is_ok());
        }

        // spec: 02-grammar §2.2.2 — an uppercase deftype type param is a located
        // reject (M2-TP1); a lowercase one is accepted (converges deftype onto
        // deftrait's existing case rule).
        #[test]
        fn deftype_uppercase_type_param_rejected() {
            let e = parse_and_build_program("(deftype (Box A) [:Int val])")
                .expect_err("an uppercase type param is rejected (§2.2.2)");
            assert!(
                e.message().contains("lowercase"),
                "the reject names the lowercase requirement; got: {}",
                e.message(),
            );
            assert!(parse_and_build_program("(deftype (Box a) [:Int val])").is_ok());
        }

        // spec: 03-types §2.3.8 — the form bound by a bare `:` MUST be a type
        // expression; a non-type bound form is a located reject (RA-N5), not a
        // swallow to `Expr::Var{ name: ":" }`.
        #[test]
        fn bare_colon_non_type_bound_form_rejected() {
            let e = parse_and_build_expr("(add-i64 :3 5)")
                .expect_err("`:3` binds a non-type form (§2.3.8)");
            assert!(
                e.message().contains("type expression"),
                "the reject names the type-expression requirement; got: {}",
                e.message(),
            );
            // A well-formed compound annotation `: (Fn [Int] Int) g` still builds.
            assert!(parse_and_build_expr("(let [g : (Fn [Int] Int) g] g)").is_ok());
        }

        // spec: 08-modules §8.5 — the ONE frontend splitter (0677). A qualified
        // name splits at the LAST `/` into two non-empty halves; a bare `/`,
        // `foo/`, `/bar` are NOT qualified (Principle 16).
        #[test]
        fn split_qualified_name_both_halves_nonempty() {
            assert_eq!(split_qualified_name("a/b"), Some(("a", "b")));
            assert_eq!(split_qualified_name("core.io/pure"), Some(("core.io", "pure")));
            assert_eq!(split_qualified_name("foo"), None);
            assert_eq!(split_qualified_name("/"), None);
            assert_eq!(split_qualified_name("foo/"), None);
            assert_eq!(split_qualified_name("/bar"), None);
        }

        // spec: 03-types §3.3 — a slash-bearing lowercase annotation routes to
        // `Named` (via the splitter), NEVER a slash-carrying `TypeVar` (0589 /
        // 0677 structural fence: such a `TypeVar` cannot reach
        // `type_expr_to_trait_ref`).
        #[test]
        fn qualified_lowercase_annotation_is_named_not_typevar() {
            assert!(matches!(build_name_type("user/int"), TypeExpr::Named(_)));
            assert!(matches!(build_name_type("int"), TypeExpr::TypeVar(_)));
            // A stacked-bounds run of qualified names reshapes without tripping
            // the `type_expr_to_trait_ref` splitter-dual debug_assert.
            assert!(parse_and_build_program("(defn f [:m/Foo :Bar a] a)").is_ok());
        }
    }

    // -- Audit R3 (0678): the ONE head classifier ---------------------------
    mod head_classifier {
        use super::*;

        // The head vocabulary is single-sourced in `classify_head`; the routing
        // predicate and the test adapter both consume it (cannot drift).
        #[test]
        fn classify_head_vocabulary() {
            use cranelisp_types::Visibility;
            assert_eq!(
                classify_head("defn"),
                HeadKind::Def { base: "defn", visibility: Visibility::Public }
            );
            assert_eq!(
                classify_head("deftype-"),
                HeadKind::Def { base: "deftype", visibility: Visibility::Private }
            );
            assert_eq!(classify_head("defmacro"), HeadKind::Defmacro);
            assert_eq!(classify_head("impl"), HeadKind::Impl);
            assert_eq!(classify_head("begin"), HeadKind::Begin);
            assert_eq!(
                classify_head("import"),
                HeadKind::StructuralDecl(StructuralKind::Import)
            );
            assert_eq!(
                classify_head("platform"),
                HeadKind::StructuralDecl(StructuralKind::Platform)
            );
            assert_eq!(
                classify_head("mod-"),
                HeadKind::StructuralDecl(StructuralKind::Mod(Visibility::Private))
            );
            assert_eq!(classify_head("add-i64"), HeadKind::Expr);
        }

        // FIXME 0703 (1)/(2): the public shape recognisers `is_defmacro`/`is_begin`
        // used to re-derive their arms (`head == "defmacro" || head == "defmacro-"`)
        // — a PUBLIC, int-consumed predicate, so drift there mis-routes real
        // dispatch. They now delegate to `classify_head`. Detection proof: this
        // test compares both predicates against the classifier across the whole
        // vocabulary, so a re-derived list that omits (say) `defmacro-` reds here.
        #[test]
        fn shape_recognisers_agree_with_classifier() {
            use crate::defmacro::{is_begin, is_defmacro};
            let vocab = [
                "defn", "defn-", "deftype", "deftype-", "deftrait", "deftrait-",
                "defmacro", "defmacro-", "impl", "begin", "mod", "mod-", "import",
                "export", "platform", "add-i64", "foo",
            ];
            for head in vocab {
                let form = crate::reader::parse(&format!("({head})")).unwrap();
                assert_eq!(
                    is_defmacro(&form[0]),
                    matches!(classify_head(head), HeadKind::Defmacro),
                    "`is_defmacro` must agree with the classifier for `{head}`"
                );
                assert_eq!(
                    is_begin(&form[0]),
                    matches!(classify_head(head), HeadKind::Begin),
                    "`is_begin` must agree with the classifier for `{head}`"
                );
            }
        }

        // `head_is_top_level_form` (the routing predicate) is defined over
        // `classify_head`, so `is_top_level_form_sexp` — used by BOTH prod and
        // the test adapter — cannot diverge from the vocabulary.
        #[test]
        fn routing_predicate_agrees_with_classifier() {
            for head in ["defn", "deftype", "deftrait-", "impl", "defmacro"] {
                assert!(head_is_top_level_form(head), "{head} routes to build_form");
            }
            for head in ["begin", "import", "mod", "platform", "add-i64", "let"] {
                assert!(!head_is_top_level_form(head), "{head} is NOT a build_form head");
            }
        }
    }

    // -- W-D2 (0670 wave 2): value-level qualified-binder reject re-landing ---
    //
    // A qualified spelling (`a/b`, both halves non-empty) in a value-level binder
    // slot — defn/fn param, let name, match var-pattern — is a located reject; the
    // BARE-binder twin stays legal. The reject fires on the WRITTEN spelling
    // (the seams see raw source, and 0670 keeps int from mangling colliding
    // binders into qualified names).
    mod value_level_qualified_binder {
        use super::*;

        // spec: 05-definitions §5.1.1 — a defn param binder must be bare.
        #[test]
        fn defn_param_qualified_rejects_bare_accepts() {
            assert!(parse_and_build_program("(defn f [a/b] a/b)").is_err());
            assert!(parse_and_build_program("(defn f [ab] ab)").is_ok());
        }

        // spec: 04-expressions §4.5 — an fn param binder must be bare.
        #[test]
        fn fn_param_qualified_rejects_bare_accepts() {
            assert!(parse_and_build_expr("(fn [a/b] a/b)").is_err());
            assert!(parse_and_build_expr("(fn [ab] ab)").is_ok());
        }

        // spec: 04-expressions §4.3 — a let binding name must be bare.
        #[test]
        fn let_name_qualified_rejects_bare_accepts() {
            assert!(parse_and_build_expr("(let [a/b 5] a/b)").is_err());
            assert!(parse_and_build_expr("(let [ab 5] ab)").is_ok());
        }

        // spec: 06-pattern-matching §6.2 — a match var-pattern binder must be
        // bare, but a qualified CONSTRUCTOR-pattern head is a reference (legal).
        #[test]
        fn match_var_pattern_qualified_rejects_ctor_head_ok() {
            assert!(parse_and_build_expr("(match v [a/b a/b])").is_err());
            assert!(parse_and_build_expr("(match v [x x])").is_ok());
            // A qualified ctor-pattern HEAD is a reference (spec §6.2.1) — legal;
            // only the bound variables inside must be bare.
            assert!(parse_and_build_expr("(match v [(option/Some x) x])").is_ok());
            // ...but a qualified binding VARIABLE inside a ctor pattern rejects.
            assert!(parse_and_build_expr("(match v [(Some a/b) a/b])").is_err());
        }

        // The reject uses the ONE `reject_qualified_binder_head` helper, so its
        // located message names the bare fix (self-documenting).
        #[test]
        fn qualified_binder_reject_names_the_bare_fix() {
            let e = parse_and_build_program("(defn f [a/b] a/b)").unwrap_err();
            assert!(
                e.message().contains("bare") && e.message().contains("a/b"),
                "the reject names the qualified spelling + the bare requirement; got: {}",
                e.message(),
            );
        }
    }
