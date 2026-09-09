use super::*;

/// Helper: parse a source string into a single Sexp.
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

// -- Integer literal expansion --

// spec: 09-macros.md section 9.4.2 -- integer literal in quasiquote
#[test]
fn expand_qq_integer() {
    let sexp = parse_one("`42");
    let result = expand_quasiquotes(&sexp).unwrap();
    assert!(is_list_headed_by(&result, "macros/SexpInt"));
    if let Sexp::List(ch, _) = &result {
        assert!(matches!(&ch[1], Sexp::Int(42, _)));
    }
}

// -- String literal expansion --

// spec: 09-macros.md section 9.4.2 -- string literal in quasiquote
#[test]
fn expand_qq_string() {
    let sexp = parse_one("`\"hello\"");
    let result = expand_quasiquotes(&sexp).unwrap();
    assert!(is_list_headed_by(&result, "macros/SexpStr"));
    if let Sexp::List(ch, _) = &result {
        assert!(matches!(&ch[1], Sexp::Str(s, _) if s == "hello"));
    }
}

// -- Symbol expansion --

// spec: 09-macros.md section 9.4.2 -- symbol in quasiquote
#[test]
fn expand_qq_symbol() {
    let sexp = parse_one("`foo");
    let result = expand_quasiquotes(&sexp).unwrap();
    assert!(is_list_headed_by(&result, "macros/SexpSym"));
    if let Sexp::List(ch, _) = &result {
        assert!(matches!(&ch[1], Sexp::Str(s, _) if s == "foo"));
    }
}

// -- Unquote pass-through --

// spec: 09-macros.md section 9.4.2 -- unquote evaluates expr
#[test]
fn expand_qq_unquote() {
    let sexp = parse_one("`~x");
    let result = expand_quasiquotes(&sexp).unwrap();
    // ~x should pass through as a bare symbol reference
    assert!(matches!(&result, Sexp::Symbol(s, _) if s == "x"));
}

// -- List expansion (nested SCons/SNil) --

// spec: 09-macros.md section 9.4.2 -- list in quasiquote
#[test]
fn expand_qq_list() {
    let sexp = parse_one("`(a b)");
    let result = expand_quasiquotes(&sexp).unwrap();
    // Should be (macros/SexpList (macros/SCons <a> (macros/SCons <b> macros/SNil)))
    assert!(is_list_headed_by(&result, "macros/SexpList"));
    assert!(contains_symbol(&result, "macros/SCons"));
    assert!(contains_symbol(&result, "macros/SNil"));
}

// -- Bracket expansion --

// spec: 09-macros.md section 9.4.2 -- bracket in quasiquote
#[test]
fn expand_qq_bracket() {
    let sexp = parse_one("`[a b]");
    let result = expand_quasiquotes(&sexp).unwrap();
    // Should be (macros/SexpBracket (macros/SCons <a> (macros/SCons <b> macros/SNil)))
    assert!(is_list_headed_by(&result, "macros/SexpBracket"));
    assert!(contains_symbol(&result, "macros/SCons"));
}

// -- Float and Bool expansion --

// spec: 09-macros.md section 9.4.2 -- float literal in quasiquote
#[test]
fn expand_qq_float() {
    let sexp = parse_one("`3.14");
    let result = expand_quasiquotes(&sexp).unwrap();
    assert!(is_list_headed_by(&result, "macros/SexpFloat"));
}

// spec: 09-macros.md section 9.4.2 -- boolean literal in quasiquote
#[test]
fn expand_qq_bool() {
    let sexp = parse_one("`true");
    let result = expand_quasiquotes(&sexp).unwrap();
    assert!(is_list_headed_by(&result, "macros/SexpBool"));
}

// -- Auto-gensym consistency within one expansion --

// spec: 09-macros.md section 9.8.1 -- auto-gensym consistency
#[test]
fn expand_qq_auto_gensym_consistent() {
    // `(let [x# 1] x#) should produce the same generated name for both x#
    let sexp = parse_one("`(let [x# 1] x#)");
    let result = expand_quasiquotes(&sexp).unwrap();
    // Find all SexpSym nodes with auto-generated names
    let mut auto_names = Vec::new();
    collect_auto_gensyms(&result, &mut auto_names);
    // Should have exactly 2 occurrences of the same auto name
    let x_autos: Vec<&str> = auto_names
        .iter()
        .filter(|n| n.starts_with("x__auto_"))
        .map(|s| s.as_str())
        .collect();
    assert_eq!(x_autos.len(), 2, "expected two x# auto-gensyms");
    assert_eq!(x_autos[0], x_autos[1], "both x# should produce same name");
}

// -- Auto-gensym uniqueness across expansions --

// spec: 09-macros.md section 9.8.1 -- auto-gensym uniqueness
#[test]
fn expand_qq_auto_gensym_unique_across() {
    let sexp1 = parse_one("`x#");
    let result1 = expand_quasiquotes(&sexp1).unwrap();
    let sexp2 = parse_one("`x#");
    let result2 = expand_quasiquotes(&sexp2).unwrap();
    // The two expansions should produce different names
    let name1 = extract_sexp_sym_value(&result1);
    let name2 = extract_sexp_sym_value(&result2);
    assert_ne!(
        name1, name2,
        "different expansions should produce different names"
    );
}

// -- Nested quasiquote (depth > 0) --

// spec: 09-macros.md section 9.4.2 -- nested quasiquote increments depth
#[test]
fn expand_qq_nested() {
    // ``~x should produce (SexpList (SCons (SexpSym "quasiquote") (SCons (SexpList ...) SNil)))
    // The inner quasiquote form is structurally quoted, not expanded
    let sexp = parse_one("``~x");
    let result = expand_quasiquotes(&sexp).unwrap();
    // The result should contain "quasiquote" as a quoted symbol
    assert!(contains_symbol(&result, "macros/SexpSym"));
    // And the inner ~x should NOT have been passed through
    // (it should be quoted as a list with "unquote" head)
}

// -- Quote expansion --

// spec: 09-macros.md section 9.4.2 -- quote is pure structural quotation
#[test]
fn expand_quote_basic() {
    let sexp = parse_one("'(a b)");
    let result = expand_quasiquotes(&sexp).unwrap();
    assert!(is_list_headed_by(&result, "macros/SexpList"));
    assert!(contains_symbol(&result, "macros/SCons"));
}

// spec: 09-macros.md §9.4.1–§9.4.2 — the shared closed quote-head
// classifier preserves the frontend fold's exact family boundary.
#[test]
fn shared_quote_head_classifier_preserves_all_frontend_branches() {
    let quote = expand_quasiquotes(&parse_one("'x")).unwrap();
    assert!(is_list_headed_by(&quote, "macros/SexpSym"));

    let quasiquote = expand_quasiquotes(&parse_one("`~x")).unwrap();
    assert!(matches!(quasiquote, Sexp::Symbol(ref name, _) if name == "x"));

    for source in ["~x", "~@xs"] {
        let input = parse_one(source);
        assert_eq!(
            expand_quasiquotes(&input).unwrap(),
            input,
            "standalone unquote forms must recurse unchanged to the AST backstop"
        );
    }

    for source in ["(macros/quote x)", "(quote x y)"] {
        let input = parse_one(source);
        assert_eq!(
            expand_quasiquotes(&input).unwrap(),
            input,
            "qualified and wrong-arity heads are ordinary lists: {source}"
        );
    }
}

// spec: 09-macros.md §9.4.2 — quote inside a quasiquote template is
// structural data, not a nested request for pure quote expansion.
#[test]
fn quote_inside_quasiquote_remains_structural() {
    let result = expand_quasiquotes(&parse_one("`(quote x)")).unwrap();
    assert!(is_list_headed_by(&result, "macros/SexpList"));
    assert!(contains_string(&result, "quote"));
    assert!(contains_string(&result, "x"));
}

// -- Unquote splicing --

// spec: 09-macros.md section 9.4.2 -- unquote-splicing in list
#[test]
fn expand_qq_splice_in_list() {
    let sexp = parse_one("`(a ~@xs b)");
    let result = expand_quasiquotes(&sexp).unwrap();
    // Should contain sconcat call for splicing
    assert!(contains_symbol(&result, "macros/sconcat"));
    assert!(is_list_headed_by(&result, "macros/SexpList"));
}

// -- Splicing at top level is an error --

// spec: 09-macros.md section 9.4.2 -- unquote-splicing at top level
#[test]
fn expand_qq_splice_top_level_error() {
    let sexp = parse_one("`~@xs");
    let result = expand_quasiquotes(&sexp);
    assert!(result.is_err(), "~@ at top level should be an error");
}

// -- Empty list --

// spec: 09-macros.md section 9.4.2 -- empty list in quasiquote
#[test]
fn expand_qq_empty_list() {
    let sexp = parse_one("`()");
    let result = expand_quasiquotes(&sexp).unwrap();
    assert!(is_list_headed_by(&result, "macros/SexpList"));
    assert!(contains_symbol(&result, "macros/SNil"));
}

// spec: 09-macros §9.4 — quote and quasiquote preserve annotated forms as
// `SexpAnnotated` with two recursively quoted halves.
#[test]
fn quote_and_quasiquote_preserve_annotated_node_shape() {
    for source in ["':Int 5", "`:Int 5"] {
        let result = expand_quasiquotes(&parse_one(source)).unwrap();
        assert!(
            contains_symbol(&result, "macros/SexpAnnotated"),
            "{source}: {result:?}"
        );
    }
}

// spec: 09-macros §9.4 — unquote-splicing cannot occupy the single
// annotation half of an annotated form.
#[test]
fn annotation_half_splice_is_rejected_in_quasiquote() {
    let err = expand_quasiquotes(&parse_one("`:~@xs value"))
        .expect_err("splice cannot stand as one annotation half");
    assert!(err.message().contains("unquote-splicing"));
}

// spec: 09-macros §9.4 — unquote-splicing cannot occupy the single
// subject half of an annotated form.
#[test]
fn annotation_subject_splice_is_rejected_in_quasiquote() {
    let err = expand_quasiquotes(&parse_one("`:Int ~@xs"))
        .expect_err("splice cannot stand as the annotated subject");
    assert!(err.message().contains("unquote-splicing"));
}

// spec: 09-macros §9.4 — unquote is permitted in either half of an
// annotated quasiquote form.
#[test]
fn unquote_is_processed_in_both_annotated_halves() {
    for source in ["`:~ty value", "`:Int ~value"] {
        let expanded = expand_quasiquotes(&parse_one(source)).unwrap();
        assert!(contains_symbol(&expanded, "macros/SexpAnnotated"));
    }
}

// -- Helpers for tests --

fn collect_auto_gensyms(sexp: &Sexp, out: &mut Vec<String>) {
    match sexp {
        Sexp::List(ch, _) => {
            // Check for (macros/SexpSym "x__auto_...")
            if ch.len() == 2
                && let Sexp::Symbol(head, _) = &ch[0]
                && head == "macros/SexpSym"
                && let Sexp::Str(name, _) = &ch[1]
                && name.contains("__auto_")
            {
                out.push(name.clone());
            }
            for c in ch {
                collect_auto_gensyms(c, out);
            }
        }
        Sexp::Bracket(ch, _) => {
            for c in ch {
                collect_auto_gensyms(c, out);
            }
        }
        _ => {}
    }
}

fn contains_string(sexp: &Sexp, expected: &str) -> bool {
    match sexp {
        Sexp::Str(value, _) => value == expected,
        Sexp::List(children, _) | Sexp::Bracket(children, _) => children
            .iter()
            .any(|child| contains_string(child, expected)),
        Sexp::Annotated {
            annotation,
            subject,
            ..
        } => contains_string(annotation, expected) || contains_string(subject, expected),
        _ => false,
    }
}

fn extract_sexp_sym_value(sexp: &Sexp) -> String {
    if let Sexp::List(ch, _) = sexp
        && ch.len() == 2
        && let Sexp::Symbol(head, _) = &ch[0]
        && head == "macros/SexpSym"
        && let Sexp::Str(name, _) = &ch[1]
    {
        return name.clone();
    }
    panic!("expected (macros/SexpSym \"...\"), got {:?}", sexp);
}
