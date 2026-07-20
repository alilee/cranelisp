    use super::*;

    fn parse_one(input: &str) -> Sexp {
        let sexps = parse(input).unwrap();
        assert_eq!(sexps.len(), 1, "expected exactly one sexp from: {input:?}");
        sexps.into_iter().next().unwrap()
    }

    fn assert_symbol(sexp: &Sexp, expected: &str) {
        match sexp {
            Sexp::Symbol(s, _) => assert_eq!(s, expected),
            other => panic!("expected Symbol({expected:?}), got {other:?}"),
        }
    }

    fn assert_int(sexp: &Sexp, expected: i64) {
        match sexp {
            Sexp::Int(v, _) => assert_eq!(*v, expected),
            other => panic!("expected Int({expected}), got {other:?}"),
        }
    }

    fn assert_float(sexp: &Sexp, expected: f64) {
        match sexp {
            Sexp::Float(v, _) => assert!((v - expected).abs() < 1e-10, "expected {expected}, got {v}"),
            other => panic!("expected Float({expected}), got {other:?}"),
        }
    }

    // -- Integer literals --

    // spec: 01-lexical §1.3.1 — integer literal (positive)
    #[test]
    fn test_parse_integer_literal() {
        assert_int(&parse_one("42"), 42);
    }

    // spec: 01-lexical §1.3.1 — negative integer literal
    #[test]
    fn test_parse_negative_integer() {
        assert_int(&parse_one("-7"), -7);
    }

    // spec: 01-lexical §1.3.1 — zero integer literal
    #[test]
    fn test_parse_zero() {
        assert_int(&parse_one("0"), 0);
    }

    // spec: 01-lexical §1.3.1 — explicit positive sign integer
    #[test]
    fn test_parse_positive_integer() {
        assert_int(&parse_one("+3"), 3);
    }

    // -- Float literals --

    // spec: 01-lexical §1.3.2 — float literal
    #[test]
    fn test_parse_float_literal() {
        assert_float(&parse_one("2.72"), 2.72);
    }

    // spec: 01-lexical §1.3.2 — negative float literal
    #[test]
    fn test_parse_negative_float() {
        assert_float(&parse_one("-0.5"), -0.5);
    }

    // spec: 01-lexical §1.3.2 — zero float literal
    #[test]
    fn test_parse_zero_float() {
        assert_float(&parse_one("0.0"), 0.0);
    }

    // -- Boolean literals --

    // spec: 01-lexical §1.3.3 — boolean literal true
    #[test]
    fn test_parse_true() {
        match parse_one("true") {
            Sexp::Bool(true, _) => {}
            other => panic!("expected Bool(true), got {other:?}"),
        }
    }

    // spec: 01-lexical §1.3.3 — boolean literal false
    #[test]
    fn test_parse_false() {
        match parse_one("false") {
            Sexp::Bool(false, _) => {}
            other => panic!("expected Bool(false), got {other:?}"),
        }
    }

    // spec: 01-lexical §1.3.3 — boolean must not be followed by symbol char
    #[test]
    fn test_true_prefix_is_symbol() {
        // `trueness` should parse as a symbol, not boolean + "ness"
        assert_symbol(&parse_one("trueness"), "trueness");
    }

    // spec: 01-lexical §1.3.3 — false prefix is a symbol, not boolean
    #[test]
    fn test_false_prefix_is_symbol() {
        assert_symbol(&parse_one("falsehood"), "falsehood");
    }

    // -- String literals --

    // spec: 01-lexical §1.3.4 — simple string literal
    #[test]
    fn test_parse_string() {
        match parse_one("\"hello\"") {
            Sexp::Str(s, _) => assert_eq!(s, "hello"),
            other => panic!("expected Str, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.3.4 — string escape sequences (newline)
    #[test]
    fn test_parse_string_escapes() {
        match parse_one("\"line1\\nline2\"") {
            Sexp::Str(s, _) => assert_eq!(s, "line1\nline2"),
            other => panic!("expected Str, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.3.4 — string escape sequences (escaped quote)
    #[test]
    fn test_parse_string_escaped_quote() {
        match parse_one("\"she said \\\"hi\\\"\"") {
            Sexp::Str(s, _) => assert_eq!(s, "she said \"hi\""),
            other => panic!("expected Str, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.3.4 — empty string literal
    #[test]
    fn test_parse_empty_string() {
        match parse_one("\"\"") {
            Sexp::Str(s, _) => assert_eq!(s, ""),
            other => panic!("expected Str, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.3.4 — unterminated string is an error
    #[test]
    fn test_unterminated_string() {
        assert!(parse("\"hello").is_err());
    }

    // -- Symbols --

    // spec: 01-lexical §1.4.1 — simple symbol
    #[test]
    fn test_parse_simple_symbol() {
        assert_symbol(&parse_one("foo"), "foo");
    }

    // spec: 01-lexical §1.4.1 — symbol with hyphens
    #[test]
    fn test_parse_symbol_with_hyphens() {
        assert_symbol(&parse_one("my-func"), "my-func");
    }

    // spec: 01-lexical §1.4.1 — symbol with question mark
    #[test]
    fn test_parse_symbol_with_question_mark() {
        assert_symbol(&parse_one("empty?"), "empty?");
    }

    // spec: 01-lexical §1.4.1 — symbol with exclamation mark
    #[test]
    fn test_parse_symbol_with_exclamation() {
        assert_symbol(&parse_one("do!"), "do!");
    }

    // spec: 01-lexical §1.4.1 — underscore-prefixed symbol
    #[test]
    fn test_parse_underscore_symbol() {
        assert_symbol(&parse_one("_private"), "_private");
    }

    // spec: 01-lexical §1.4.1 — uppercase symbol (type/constructor name)
    #[test]
    fn test_parse_uppercase_symbol() {
        assert_symbol(&parse_one("Point"), "Point");
    }

    // -- Operator symbols --

    // spec: 01-lexical §1.4.2 — operator symbol (+)
    #[test]
    fn test_parse_operator_plus() {
        assert_symbol(&parse_one("+"), "+");
    }

    // spec: 01-lexical §1.4.2 — operator symbol (-)
    #[test]
    fn test_parse_operator_minus() {
        assert_symbol(&parse_one("- "), "-");
    }

    // spec: 01-lexical §1.4.2 — multi-char operator symbol (<=)
    #[test]
    fn test_parse_operator_less_equal() {
        assert_symbol(&parse_one("<="), "<=");
    }

    // spec: 01-lexical §1.4.2 — arrow operator symbol (->)
    #[test]
    fn test_parse_operator_arrow() {
        assert_symbol(&parse_one("->"), "->");
    }

    // spec: 01-lexical §1.4.2 — thread-last operator symbol (->>)
    #[test]
    fn test_parse_operator_thread_last() {
        assert_symbol(&parse_one("->>"), "->>");
    }

    // spec: 01-lexical §1.4.2 — not-equal operator symbol (!=)
    #[test]
    fn test_parse_operator_not_equal() {
        assert_symbol(&parse_one("!="), "!=");
    }

    // -- Interior operator chars inside alphabetic symbols (D-name, S87) --
    //
    // spec: 01-lexical §1.4.1 — an alphabetic symbol may embed operator
    // characters interior to its body. `char->digit` is a SINGLE symbol; the
    // `->` does not split it nor trigger the threading reader path (which is a
    // standalone-`->` concern, not a substring concern). Regression guard for
    // the S87 D-name defect (`(defn char->digit ...)` mis-parsed because the
    // reader stopped the symbol at `>`).
    #[test]
    fn test_parse_symbol_with_interior_arrow() {
        assert_symbol(&parse_one("char->digit"), "char->digit");
    }

    // spec: 01-lexical §1.4.1 — minimal interior-arrow symbol `a->b`.
    #[test]
    fn test_parse_symbol_with_interior_arrow_minimal() {
        assert_symbol(&parse_one("a->b"), "a->b");
    }

    // spec: 01-lexical §1.4.1 — other interior operator chars (`<=`) inside an
    // alphabetic symbol are likewise absorbed, not split.
    #[test]
    fn test_parse_symbol_with_interior_le() {
        assert_symbol(&parse_one("clamp<=hi"), "clamp<=hi");
    }

    // spec: 01-lexical §1.4.2 — a TRAILING operator-char run is NOT absorbed
    // into a preceding symbol: `foo ->` reads the symbol `foo` then the
    // standalone arrow operator `->`. Pins that interior-absorption does not
    // swallow whitespace-separated standalone operators.
    #[test]
    fn test_symbol_then_standalone_arrow_not_merged() {
        let sexps = parse("foo ->").unwrap();
        assert_eq!(sexps.len(), 2, "expected `foo` and `->` as two sexps");
        assert_symbol(&sexps[0], "foo");
        assert_symbol(&sexps[1], "->");
    }

    // spec: 01-lexical §1.4.2 — the form `(-> x f g)` still reads as a
    // 4-element list headed by the standalone `->` operator symbol; the
    // interior-operator absorption must not perturb the standalone-`->`
    // (threading-macro) head.
    #[test]
    fn test_threading_arrow_head_still_standalone() {
        let sexp = parse_one("(-> x f g)");
        match sexp {
            Sexp::List(items, _) => {
                assert_eq!(items.len(), 4);
                assert_symbol(&items[0], "->");
                assert_symbol(&items[1], "x");
                assert_symbol(&items[2], "f");
                assert_symbol(&items[3], "g");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.4.2 — single-char operator symbol (!)
    #[test]
    fn test_parse_operator_bang_alone() {
        assert_symbol(&parse_one("!"), "!");
    }

    // -- Qualified symbols --

    // spec: 01-lexical §1.4.3 — qualified symbol (module/name)
    #[test]
    fn test_parse_qualified_symbol() {
        assert_symbol(&parse_one("math/sin"), "math/sin");
    }

    // spec: 01-lexical §1.4.3 — qualified symbol with dotted module path
    #[test]
    fn test_parse_qualified_dotted_module() {
        assert_symbol(&parse_one("core.io/pure"), "core.io/pure");
    }

    // spec: 01-lexical §1.4.3 — qualified operator symbol (module/+)
    #[test]
    fn test_parse_qualified_operator() {
        assert_symbol(&parse_one("math/+"), "math/+");
    }

    // -- Dotted symbols --

    // spec: 01-lexical §1.4.4 — dotted symbol (Type.member)
    #[test]
    fn test_parse_dotted_symbol() {
        assert_symbol(&parse_one("Option.Some"), "Option.Some");
    }

    // spec: 01-lexical §1.4.4 — dotted operator symbol (Trait.+)
    #[test]
    fn test_parse_dotted_operator() {
        assert_symbol(&parse_one("Num.+"), "Num.+");
    }

    // -- Colon-prefixed symbols --

    // spec: 01-lexical §1.4.5 — colon-prefixed type annotation
    #[test]
    fn test_parse_colon_prefix() {
        assert_symbol(&parse_one(":Int"), ":Int");
    }

    // spec: 01-lexical §1.4.5 — colon-prefixed type variable
    #[test]
    fn test_parse_colon_type_var() {
        assert_symbol(&parse_one(":a"), ":a");
    }

    // spec: 01-lexical §1.4.5 — bare colon (field separator)
    #[test]
    fn test_parse_bare_colon() {
        assert_symbol(&parse_one(": "), ":");
    }

    // spec: 03-types §3.1 — a colon-prefixed FQ type annotation reads as ONE
    // qualified token, not three (`:primitives`, `/`, `Int`). FIXME 0321
    // Root B-prim: an FQ type ref needs no import; `:primitives/Int` MUST be
    // valid in annotation position.
    #[test]
    fn test_parse_colon_prefix_qualified() {
        assert_symbol(&parse_one(":primitives/Int"), ":primitives/Int");
    }

    // spec: 03-types §3.1 — multi-dot module path in a colon annotation reads
    // as one qualified token (`:core.option/Option`).
    #[test]
    fn test_parse_colon_prefix_qualified_dotted_module() {
        assert_symbol(&parse_one(":core.option/Option"), ":core.option/Option");
    }

    // spec: 03-types §3.1 — the qualified colon annotation survives in field
    // position: the deftype field type is the single qualified leaf, not split.
    #[test]
    fn test_parse_deftype_fq_field_type_single_token() {
        // (deftype Box (ABox [:primitives/Int n]))
        let sexp = parse_one("(deftype Box (ABox [:primitives/Int n]))");
        let Sexp::List(top, _) = &sexp else {
            panic!("expected List, got {sexp:?}");
        };
        // top[2] is the ctor form `(ABox [:primitives/Int n])`.
        let Sexp::List(ctor, _) = &top[2] else {
            panic!("expected ctor List, got {:?}", top[2]);
        };
        // ctor[1] is the field bracket `[:primitives/Int n]`.
        let Sexp::Bracket(fields, _) = &ctor[1] else {
            panic!("expected field Bracket, got {:?}", ctor[1]);
        };
        // Exactly two items: the FQ type annotation and the field name — NOT
        // three (`:primitives`, `/`, `Int`) plus the name.
        assert_eq!(
            fields.len(),
            2,
            "FQ field type must read as one token; got {fields:?}"
        );
        assert_symbol(&fields[0], ":primitives/Int");
        assert_symbol(&fields[1], "n");
    }

    // -- Lists --

    // spec: 01-lexical §1.8 — parenthesized list form
    #[test]
    fn test_parse_list() {
        let sexp = parse_one("(+ 1 2)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_symbol(&children[0], "+");
                assert_int(&children[1], 1);
                assert_int(&children[2], 2);
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.8 — empty parenthesized list
    #[test]
    fn test_parse_empty_list() {
        match parse_one("()") {
            Sexp::List(children, _) => assert!(children.is_empty()),
            other => panic!("expected empty List, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.8 — nested list forms
    #[test]
    fn test_parse_nested_list() {
        let sexp = parse_one("(+ (* 2 3) 4)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert!(matches!(&children[1], Sexp::List(..)));
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // -- Brackets --

    // spec: 01-lexical §1.5 — bracket form
    #[test]
    fn test_parse_bracket() {
        let sexp = parse_one("[a b c]");
        match sexp {
            Sexp::Bracket(children, _) => {
                assert_eq!(children.len(), 3);
                assert_symbol(&children[0], "a");
                assert_symbol(&children[1], "b");
                assert_symbol(&children[2], "c");
            }
            other => panic!("expected Bracket, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.5 — bracket with colon-prefixed type annotations
    #[test]
    fn test_parse_bracket_with_types() {
        let sexp = parse_one("[:Int x :Int y]");
        match sexp {
            Sexp::Bracket(children, _) => {
                assert_eq!(children.len(), 4);
                assert_symbol(&children[0], ":Int");
                assert_symbol(&children[1], "x");
                assert_symbol(&children[2], ":Int");
                assert_symbol(&children[3], "y");
            }
            other => panic!("expected Bracket, got {other:?}"),
        }
    }

    // -- Comments --

    // spec: 01-lexical §1.2 — line comments
    #[test]
    fn test_parse_with_comment() {
        let sexps = parse("42 ; this is a comment\n43").unwrap();
        assert_eq!(sexps.len(), 2);
        assert_int(&sexps[0], 42);
        assert_int(&sexps[1], 43);
    }

    // spec: 01-lexical §1.2 — trailing comment at end of input
    #[test]
    fn test_parse_comment_at_end() {
        let sexps = parse("42 ; trailing comment").unwrap();
        assert_eq!(sexps.len(), 1);
        assert_int(&sexps[0], 42);
    }

    // -- Commas as whitespace --

    // spec: 01-lexical §1.2 — commas are whitespace
    #[test]
    fn test_commas_are_whitespace() {
        let sexp = parse_one("[1, 2, 3]");
        match sexp {
            Sexp::Bracket(children, _) => {
                assert_eq!(children.len(), 3);
                assert_int(&children[0], 1);
                assert_int(&children[1], 2);
                assert_int(&children[2], 3);
            }
            other => panic!("expected Bracket, got {other:?}"),
        }
    }

    // -- Multiple forms --

    // spec: 01-lexical §1.8 — program is sequence of forms
    #[test]
    fn test_parse_multiple_forms() {
        let sexps = parse("(defn f [x] x) (f 42)").unwrap();
        assert_eq!(sexps.len(), 2);
    }

    // -- Spans --

    // spec: 01-lexical §1.3.1 — integer literal span tracking
    #[test]
    fn test_span_integer() {
        let sexp = parse_one("42");
        assert_eq!(sexp.span(), Span::new(0, 2));
    }

    // spec: 01-lexical §1.8 — list form span tracking
    #[test]
    fn test_span_list() {
        let sexp = parse_one("(+ 1 2)");
        assert_eq!(sexp.span(), Span::new(0, 7));
    }

    // spec: 01-lexical §1.3.4 — string literal span tracking
    #[test]
    fn test_span_string() {
        let sexp = parse_one("\"hello\"");
        assert_eq!(sexp.span(), Span::new(0, 7));
    }

    // -- Error cases --

    // spec: 01-lexical §1.5 — unclosed parenthesis is an error
    #[test]
    fn test_unclosed_paren() {
        assert!(parse("(+ 1 2").is_err());
    }

    // spec: 01-lexical §1.5 — unclosed bracket is an error
    #[test]
    fn test_unclosed_bracket() {
        assert!(parse("[1 2").is_err());
    }

    // spec: 01-lexical §1.5 — unexpected close paren is an error
    #[test]
    fn test_unexpected_close_paren() {
        assert!(parse(")").is_err());
    }

    // -- Complex forms --

    // spec: 02-grammar §2.2.1 — defn form parsed as list
    #[test]
    fn test_parse_defn() {
        let sexp = parse_one("(defn add [a b] (+ a b))");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 4);
                assert_symbol(&children[0], "defn");
                assert_symbol(&children[1], "add");
                assert!(matches!(&children[2], Sexp::Bracket(..)));
                assert!(matches!(&children[3], Sexp::List(..)));
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.2 — deftype enum form parsed as list
    #[test]
    fn test_parse_deftype_enum() {
        let sexp = parse_one("(deftype Color Red Green Blue)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 5);
                assert_symbol(&children[0], "deftype");
                assert_symbol(&children[1], "Color");
                assert_symbol(&children[2], "Red");
                assert_symbol(&children[3], "Green");
                assert_symbol(&children[4], "Blue");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.4.5 — colon-prefixed symbol in list context
    #[test]
    fn test_parse_type_annotation() {
        let sexp = parse_one("(:Int)");
        // Wait, this is a list containing a colon-prefixed symbol — not valid as an expr
        // but the reader doesn't care.
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 1);
                assert_symbol(&children[0], ":Int");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.8.3 — compound type annotation with bare colon
    #[test]
    fn test_parse_compound_type_annotation() {
        // :(Fn [Int] Int) should produce : followed by (Fn [Int] Int)
        let sexps = parse(":(Fn [Int] Int) 42").unwrap();
        assert_eq!(sexps.len(), 3);
        assert_symbol(&sexps[0], ":");
        match &sexps[1] {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_symbol(&children[0], "Fn");
            }
            other => panic!("expected List, got {other:?}"),
        }
        assert_int(&sexps[2], 42);
    }

    // -- Whitespace edge cases --

    // spec: 01-lexical §1.8 — empty input produces no forms
    #[test]
    fn test_parse_empty_input() {
        let sexps = parse("").unwrap();
        assert!(sexps.is_empty());
    }

    // spec: 01-lexical §1.2 — whitespace-only input produces no forms
    #[test]
    fn test_parse_whitespace_only() {
        let sexps = parse("   \n\t  ").unwrap();
        assert!(sexps.is_empty());
    }

    // spec: 01-lexical §1.2 — comment-only input produces no forms
    #[test]
    fn test_parse_comment_only() {
        let sexps = parse("; just a comment").unwrap();
        assert!(sexps.is_empty());
    }

    // -- Minus as operator vs negative number --

    // spec: 01-lexical §1.7 — minus in list head is operator, not negative
    #[test]
    fn test_minus_in_list_is_operator() {
        let sexp = parse_one("(- 3 1)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_symbol(&children[0], "-");
                assert_int(&children[1], 3);
                assert_int(&children[2], 1);
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.7 — standalone -3 parses as negative integer
    #[test]
    fn test_negative_three_standalone() {
        assert_int(&parse_one("-3"), -3);
    }

    // -- Reader macros: quote, quasiquote, unquote --

    // spec: 01-lexical §1.6 — quote reader macro ('form -> (quote form))
    #[test]
    fn test_parse_quote() {
        let sexp = parse_one("'foo");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_symbol(&children[0], "quote");
                assert_symbol(&children[1], "foo");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.6 — quote reader macro on list form
    #[test]
    fn test_parse_quote_list() {
        let sexp = parse_one("'(1 2 3)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_symbol(&children[0], "quote");
                assert!(matches!(&children[1], Sexp::List(..)));
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.6 — quasiquote reader macro (`form -> (quasiquote form))
    #[test]
    fn test_parse_quasiquote() {
        let sexp = parse_one("`foo");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_symbol(&children[0], "quasiquote");
                assert_symbol(&children[1], "foo");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.6 — quasiquote reader macro on list form
    #[test]
    fn test_parse_quasiquote_list() {
        let sexp = parse_one("`(a b c)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_symbol(&children[0], "quasiquote");
                assert!(matches!(&children[1], Sexp::List(..)));
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.6 — unquote reader macro (~form -> (unquote form))
    #[test]
    fn test_parse_unquote() {
        let sexp = parse_one("~x");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_symbol(&children[0], "unquote");
                assert_symbol(&children[1], "x");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.6 — unquote-splicing reader macro (~@form)
    #[test]
    fn test_parse_unquote_splicing() {
        let sexp = parse_one("~@xs");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_symbol(&children[0], "unquote-splicing");
                assert_symbol(&children[1], "xs");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // -- Anonymous function --

    // spec: 01-lexical §1.6 — anonymous function reader macro #(...)
    #[test]
    fn test_parse_anon_fn() {
        let sexp = parse_one("#(+ %1 %2)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_symbol(&children[0], "anon-fn");
                match &children[1] {
                    Sexp::List(inner, _) => {
                        assert_eq!(inner.len(), 3);
                        assert_symbol(&inner[0], "+");
                        assert_symbol(&inner[1], "%1");
                        assert_symbol(&inner[2], "%2");
                    }
                    other => panic!("expected inner List, got {other:?}"),
                }
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.6 — # without ( is an error
    #[test]
    fn test_parse_hash_without_paren_fails() {
        assert!(parse("#foo").is_err());
    }

    // -- Percent params --

    // spec: 01-lexical §1.4.7 — bare % is shorthand for %1
    #[test]
    fn test_parse_percent_param_bare() {
        // Bare `%` is shorthand for `%1`
        assert_symbol(&parse_one("% "), "%1");
    }

    // spec: 01-lexical §1.4.7 — explicit %1 percent parameter
    #[test]
    fn test_parse_percent_param_1() {
        assert_symbol(&parse_one("%1"), "%1");
    }

    // spec: 01-lexical §1.4.7 — %2 percent parameter
    #[test]
    fn test_parse_percent_param_2() {
        assert_symbol(&parse_one("%2"), "%2");
    }

    // -- Gensym --

    // spec: 01-lexical §1.4.6 — gensym dollar-prefixed symbol
    #[test]
    fn test_parse_gensym_dollar() {
        assert_symbol(&parse_one("$foo"), "$foo");
    }

    // spec: 01-lexical §1.4.6 — bare $ without name is an error
    #[test]
    fn test_parse_gensym_dollar_needs_name() {
        assert!(parse("$ ").is_err());
    }

    // -- Ampersand --

    // spec: 01-lexical §1.4.8 — ampersand with rest parameter name (no space)
    #[test]
    fn test_parse_ampersand() {
        assert_symbol(&parse_one("&rest"), "&rest");
    }

    // spec: 01-lexical §1.4.8 — ampersand with rest parameter name (with space)
    #[test]
    fn test_parse_ampersand_with_space() {
        assert_symbol(&parse_one("& rest"), "&rest");
    }

    // spec: 01-lexical §1.4.8 — & rest in bracket context produces &rest symbol
    #[test]
    fn test_parse_ampersand_in_bracket() {
        let sexp = parse_one("[x & rest]");
        if let Sexp::Bracket(items, _) = &sexp {
            assert_eq!(items.len(), 2);
            assert_symbol(&items[0], "x");
            assert_symbol(&items[1], "&rest");
        } else {
            panic!("expected bracket, got: {sexp:?}");
        }
    }

    // spec: 01-lexical §1.4.8 — bare & without name is an error
    #[test]
    fn test_parse_ampersand_needs_name() {
        assert!(parse("& ").is_err());
    }

    // -- Gensym shorthand (name#) --

    // spec: 01-lexical §1.4.6 — gensym shorthand (name#)
    #[test]
    fn test_parse_gensym_shorthand() {
        assert_symbol(&parse_one("foo#"), "foo#");
    }

    // spec: 01-lexical §1.4.6 — gensym shorthand in list context
    #[test]
    fn test_parse_gensym_shorthand_in_list() {
        let sexp = parse_one("(let [x# 1] x#)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_symbol(&children[0], "let");
                match &children[1] {
                    Sexp::Bracket(items, _) => {
                        assert_symbol(&items[0], "x#");
                        assert_int(&items[1], 1);
                    }
                    other => panic!("expected Bracket, got {other:?}"),
                }
                assert_symbol(&children[2], "x#");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // -------------------------------------------------------------------
    // Rendered-diagnostic tier (FIXME 0500)
    //
    // The reader is one of frontend's own diagnostic-emitting submodules.
    // This tier institutionalizes the P6 diagnostic-quality class (0485):
    // a user-facing reader diagnostic MUST carry a REAL source span (never
    // a synthetic 1_000_000+ span), MUST NOT leak a Debug-format struct
    // dump into its text, and MUST name the offending construct.
    // Organized submodule × scenario-class per METHOD §2.2.
    // spec: repl/spec.md §"Self-documenting REPL" — no opaque errors.
    // -------------------------------------------------------------------
    mod rendered_diagnostics {
        use super::*;

        /// Synthetic-span floor — the quasiquote/defmacro allocator base
        /// (`quasiquote::SYNTHETIC_SPAN_COUNTER`). A reader diagnostic points
        /// at real source bytes, so it must never carry a span at/above this.
        const SYNTHETIC_SPAN_BASE: u32 = 1_000_000;

        fn err(src: &str) -> CranelispError {
            parse(src).expect_err("expected a reader error")
        }

        fn assert_real_span(e: &CranelispError, src: &str) {
            let s = e.span();
            assert!(
                s.start < SYNTHETIC_SPAN_BASE && s.end < SYNTHETIC_SPAN_BASE,
                "reader diagnostic carries a synthetic span {s}: {}",
                e.message(),
            );
            assert!(
                s.end as usize <= src.len(),
                "reader span {s} exceeds source length {} for {src:?}",
                src.len(),
            );
        }

        fn assert_no_debug_artifacts(e: &CranelispError) {
            let m = e.message();
            assert!(!m.contains("Span {"), "message leaks a Debug span struct: {m}");
            assert!(!m.contains("Sexp::"), "message leaks a Debug Sexp variant: {m}");
            assert!(!m.contains("ErrorLocation"), "message leaks ErrorLocation: {m}");
        }

        // -- positive: the message names the offending construct --

        // spec: 01-lexical §1.3.4 — unterminated string is a diagnosable error.
        #[test]
        fn unterminated_string_names_condition_with_real_span() {
            let e = err("\"hello");
            assert!(
                e.message().contains("unterminated string"),
                "got: {}",
                e.message(),
            );
            assert_real_span(&e, "\"hello");
            assert_no_debug_artifacts(&e);
        }

        // spec: 01-lexical §1.2 — a stray char is named in the diagnostic.
        #[test]
        fn unexpected_char_names_the_character() {
            let e = err(")");
            assert!(
                e.message().contains("unexpected character"),
                "got: {}",
                e.message(),
            );
            assert!(
                e.message().contains(')'),
                "message should name the offending char: {}",
                e.message(),
            );
            assert_no_debug_artifacts(&e);
        }

        // -- edge: escape + unclosed-delimiter boundaries --

        // spec: 01-lexical §1.3.4 — unknown escape names the escape char.
        #[test]
        fn unknown_escape_names_the_escape() {
            let e = err("\"\\q\"");
            assert!(
                e.message().contains("unknown escape sequence"),
                "got: {}",
                e.message(),
            );
            assert_real_span(&e, "\"\\q\"");
            assert_no_debug_artifacts(&e);
        }

        // spec: 01-lexical §1.8 — unclosed list names the delimiter, real span.
        #[test]
        fn unclosed_paren_names_the_delimiter_with_real_span() {
            let e = err("(a b");
            assert!(e.message().contains("unclosed"), "got: {}", e.message());
            assert!(
                e.message().contains('('),
                "message should name the delimiter: {}",
                e.message(),
            );
            assert_real_span(&e, "(a b");
            assert_no_debug_artifacts(&e);
        }

        // -- negative: no internal artifacts leak; every span is a real offset --

        #[test]
        fn no_reader_diagnostic_leaks_debug_or_synthetic_span() {
            for src in ["\"open", ")", "(unterminated", "\"\\z\"", "[a b"] {
                let e = err(src);
                assert_no_debug_artifacts(&e);
                assert_real_span(&e, src);
            }
        }
    }

    // -- RA (0682) — dangling-qualifier lexing (W-D1) ------------------------
    //
    // `:foo/`/`:a.b/` (empty local), `/bar` (empty module half) are located
    // reader errors; a bare `/` (division) and a valid qualified name stay
    // legal (RA-N4 fence, Principle 16). The value-path `foo/` already erred;
    // these pin the annotation-path parity + the new `/bar` guard.
    mod ra_dangling_qualifier {
        use super::*;

        fn read_err(src: &str) -> CranelispError {
            match parse(src) {
                Ok(sexps) => panic!("expected reader error from {src:?}, got {sexps:?}"),
                Err(e) => e,
            }
        }

        // spec: 01-lexical §1.4.5 — `:foo/` (empty local) is a located reader error.
        #[test]
        fn colon_foo_slash_empty_local_rejected() {
            let e = read_err(":foo/");
            assert!(
                e.message().contains("local name"),
                "`:foo/` must reject naming the missing local name, got: {}",
                e.message(),
            );
        }

        // spec: 01-lexical §1.4.5 — `:a.b/` (dotted module, empty local) rejects
        // through the SAME `consume_dotted_module_path` path (audit R7).
        #[test]
        fn colon_dotted_module_empty_local_rejected() {
            let e = read_err(":a.b/");
            assert!(
                e.message().contains("local name"),
                "`:a.b/` must reject (dotted-module swallow removed), got: {}",
                e.message(),
            );
        }

        // spec: 08-modules §8.5.1 — `/bar` (empty module half) is a located reader
        // error at the `/` token (the ONE genuinely-new lexical reject, RA-N6).
        #[test]
        fn slash_bar_empty_module_half_rejected() {
            let e = read_err("/bar");
            assert!(
                e.message().contains("module name"),
                "`/bar` must reject naming the empty module half, got: {}",
                e.message(),
            );
        }

        // spec: 08-modules §8.5.1 — a bare `/` (division) stays legal (RA-N4
        // fence; Principle 16). It reads as the operator symbol `/`.
        #[test]
        fn bare_slash_division_stays_a_symbol() {
            assert_symbol(&parse_one("/"), "/");
            // `/` separated from operands is division, not a dangling qualifier.
            let sexps = parse("(/ 6 2)").unwrap();
            assert_eq!(sexps.len(), 1);
            // `(map / xs)` — `/` as a first-class value, followed by whitespace.
            let sexps = parse("(map / xs)").unwrap();
            assert_eq!(sexps.len(), 1);
        }

        // spec: 08-modules §8.5.1 — a valid qualified name still reads as ONE leaf
        // (the un-swallow must not break the happy path).
        #[test]
        fn valid_qualified_names_still_read_as_one_leaf() {
            assert_symbol(&parse_one("foo/bar"), "foo/bar");
            assert_symbol(&parse_one(":primitives/Int"), ":primitives/Int");
            assert_symbol(&parse_one(":core.option/Option"), ":core.option/Option");
        }

        // spec: 01-lexical §1.7 — a bare dotted symbol/module path (no `/`) still
        // reads intact (the dotted-symbol reader is unchanged behaviourally).
        #[test]
        fn bare_dotted_names_unchanged() {
            assert_symbol(&parse_one("Option.Some"), "Option.Some");
            assert_symbol(&parse_one("main.shell.inner"), "main.shell.inner");
        }
    }
