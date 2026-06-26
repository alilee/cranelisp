    use super::*;

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

    /// Detect a top-level form head (defn/deftype/deftrait/impl/defmacro and
    /// their `-` variants) so the test adapter knows whether to route to
    /// `build_form` (and propagate its errors) or fall through to
    /// `build_expr`.
    fn is_top_level_form(sexp: &Sexp) -> bool {
        if let Sexp::List(children, _) = sexp
            && let Some(Sexp::Symbol(head, _)) = children.first()
        {
            return matches!(
                head.as_str(),
                "defn" | "defn-" | "deftype" | "deftype-" | "deftrait" | "deftrait-"
                    | "impl" | "defmacro" | "defmacro-"
            );
        }
        false
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
        let sexps = crate::reader::parse(":Int").unwrap();
        let err = build_forms(&sexps).unwrap_err();
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

    // spec: 02-grammar §2.3.7 — match arms must be even number of elements
    #[test]
    fn test_build_match_odd_arms_rejected() {
        let err = parse_and_build_expr("(match x [Red 1 Green])").unwrap_err();
        assert!(err.message().contains("even number"));
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
    // "annotation missing parameter name" error.
    //
    // spec: spec/07-traits.md §7.8.2 — annotation must bind a parameter
    #[test]
    fn trailing_annotation_without_binder_errors() {
        let err = parse_and_build_program("(defn g [:Eq] 0)").unwrap_err();
        assert!(
            format!("{err:?}").contains("annotation missing parameter name"),
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
                assert!(matches!(&decl.methods[0].ret_type, TypeExpr::Named(n) if n.name.as_ref() == "String"));
                assert!(decl.methods[0].default_body.is_none());
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
            "(deftrait Ord (< [a b] Bool) (<= [x y] Bool (if (< x y) true (= x y))))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.methods.len(), 2);
                assert!(decl.methods[0].default_body.is_none());
                // Names live with params now (S69 Sub 26) — verify the no-default
                // method has its two self-typed params.
                assert_eq!(decl.methods[0].params.len(), 2);
                assert!(decl.methods[1].default_body.is_some());
                assert_eq!(decl.methods[1].params.len(), 2);
                assert_eq!(decl.methods[1].params[0].0, "x");
                assert_eq!(decl.methods[1].params[1].0, "y");
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
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
        let err = parse_and_build_program(
            "(deftrait (Functor f) (fmap [x] (f Int) x))",
        ).unwrap_err();
        assert!(err.message().contains("default method implementations are not supported on higher-kinded traits"));
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
            "(deftrait Scaler (scale [:primitives/Int x] :primitives/Int))",
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
        match &sig.ret_type {
            TypeExpr::Named(n) => {
                assert_eq!(n.module.as_deref(), Some("primitives"));
                assert_eq!(n.name.as_ref(), "Int");
            }
            other => panic!("expected Named ret type, got {other:?}"),
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

    // spec: 01-lexical §1.6 — anonymous function form rejected (Ring 3)
    #[test]
    fn test_reject_anon_fn() {
        let err = parse_and_build_expr("#(+ %1 %2)").unwrap_err();
        assert!(err.message().contains("anonymous functions"));
        assert!(err.message().contains("Ring 3"));
    }

    // spec: 01-lexical §1.4.7 — percent param rejected in AST (Ring 3)
    #[test]
    fn test_reject_percent_param() {
        let err = parse_and_build_expr("%1").unwrap_err();
        assert!(err.message().contains("percent parameters not yet supported"));
        assert!(err.message().contains("Ring 3"));
    }

    // spec: 01-lexical §1.4.6 — gensym dollar rejected in AST (Ring 3)
    #[test]
    fn test_reject_gensym_dollar() {
        let err = parse_and_build_expr("$foo").unwrap_err();
        assert!(err.message().contains("gensym not yet supported"));
        assert!(err.message().contains("Ring 3"));
    }

    // spec: 01-lexical §1.4.8 — ampersand rejected in AST (Ring 3)
    #[test]
    fn test_reject_ampersand() {
        let err = parse_and_build_expr("&rest").unwrap_err();
        assert!(err.message().contains("rest parameters not yet supported"));
        assert!(err.message().contains("Ring 3"));
    }

    // spec: 01-lexical §1.4.6 — gensym shorthand rejected in AST (Ring 3)
    #[test]
    fn test_reject_gensym_shorthand() {
        let err = parse_and_build_expr("foo#").unwrap_err();
        assert!(err.message().contains("gensym shorthand not yet supported"));
        assert!(err.message().contains("Ring 3"));
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
    fn parse_annotation_name_splits_module_qualifier() {
        match parse_annotation_name("t/Box") {
            TypeExpr::Named(r) => {
                assert_eq!(r.module.as_deref(), Some("t"));
                assert_eq!(r.name.as_ref(), "Box");
            }
            other => panic!("expected Named, got {other:?}"),
        }
    }

    // FIXME 0362 — a bare (unqualified) type name stays `module: None`.
    #[test]
    fn parse_annotation_name_bare_stays_unqualified() {
        match parse_annotation_name("Box") {
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
    fn parse_annotation_name_deep_qualified_splits_at_last_slash() {
        match parse_annotation_name("a.b/Box") {
            TypeExpr::Named(r) => {
                assert_eq!(r.module.as_deref(), Some("a.b"));
                assert_eq!(r.name.as_ref(), "Box");
            }
            other => panic!("expected Named, got {other:?}"),
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
