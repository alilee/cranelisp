use super::*;
use crate::session_v4::{CompilerSession, RunMode, SessionSettings};
use cranelisp_types::{CodegenBehaviour, ModuleFullPath};

const PRELUDE: &str = "(import [primitives [Int String]])\n";

/// The checked table of module `m` declared by `source`. Each call is its own
/// session, so two tables never share type-variable ids.
fn checked_table(source: &str) -> SessionSymbolTable {
    let root = tempfile::tempdir().unwrap();
    let mut session = CompilerSession::new(
        SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 0,
            run_mode: RunMode::Run,
        },
        root.path().to_path_buf(),
        "m",
    )
    .unwrap();
    session.set_lib_dirs(Vec::new());
    let source = format!("{PRELUDE}{source}");
    session
        .register_module_with_source("m", &source, &root.path().join("m.cl"))
        .unwrap();
    let table = session
        .shared
        .symbol_tables
        .get(&ModuleFullPath::from("m"))
        .unwrap()
        .clone();
    session.shutdown();
    table
}

fn change(live: &str, staged: &str, name: &str) -> Option<StructuralTypeChange> {
    structural_type_change(
        &checked_table(live),
        &checked_table(staged),
        &Symbol::from(name),
    )
}

// spec: repl/spec/18-redefinition.md §18.5 — each structural facet refuses.
#[test]
fn structural_type_change_refuses_every_layout_facet() {
    let cases = [
        (
            "field type",
            "(deftype T [:Int v])",
            "(deftype T [:String v])",
            "T",
        ),
        (
            "field order",
            "(deftype T [:Int a :String b])",
            "(deftype T [:String b :Int a])",
            "T",
        ),
        (
            "field name",
            "(deftype T [:Int v])",
            "(deftype T [:Int w])",
            "T",
        ),
        (
            "field count",
            "(deftype T [:Int v])",
            "(deftype T [:Int v :Int w])",
            "T",
        ),
        (
            "sum constructor added",
            "(deftype S A B)",
            "(deftype S A B C)",
            "S",
        ),
        (
            "sum constructor removed",
            "(deftype S A B C)",
            "(deftype S A B)",
            "S",
        ),
        (
            "sum constructor reordered",
            "(deftype S A B)",
            "(deftype S B A)",
            "S",
        ),
        (
            "payload arity",
            "(deftype S (A [:Int x]) B)",
            "(deftype S (A [:Int x :Int y]) B)",
            "S",
        ),
        (
            "payload type",
            "(deftype S (A [:Int x]) B)",
            "(deftype S (A [:String x]) B)",
            "S",
        ),
        (
            "type parameters",
            "(deftype (P a) [:a v])",
            "(deftype (P a b) [:a v])",
            "P",
        ),
        (
            "product visibility",
            "(deftype T [:Int v])",
            "(deftype- T [:Int v])",
            "T",
        ),
        ("sum visibility", "(deftype S A B)", "(deftype- S A B)", "S"),
    ];
    for (facet, live, staged, name) in cases {
        let refusal = change(live, staged, name);
        assert_eq!(
            refusal.map(|r| r.type_name.to_string()),
            Some(format!("m/{name}")),
            "{facet}: {live} -> {staged}"
        );
    }
}

// spec: repl/spec/14-file-watching.md §14.8 — a structurally identical
// redeclaration is not refused.
#[test]
fn structural_type_change_admits_identical_structure() {
    let cases = [
        (
            "identical product",
            "(deftype T [:Int v])",
            "(deftype T [:Int v])",
            "T",
        ),
        (
            "identical sum",
            "(deftype S (A [:Int x]) B)",
            "(deftype S (A [:Int x]) B)",
            "S",
        ),
        (
            "docstring only",
            "(deftype T \"old\" [:Int v])",
            "(deftype T \"new\" [:Int v])",
            "T",
        ),
        (
            "payload label",
            "(deftype S (A [:Int x]) B)",
            "(deftype S (A [:Int y]) B)",
            "S",
        ),
        (
            "alpha-renamed parameters",
            "(deftype (P a) [:a v])",
            "(deftype (P b) [:b v])",
            "P",
        ),
    ];
    for (case, live, staged, name) in cases {
        assert_eq!(
            change(live, staged, name),
            None,
            "{case}: {live} -> {staged}"
        );
    }
}

// spec: repl/spec/14-file-watching.md §14.8 — the refusal names the type and
// the restart remedy, never a reload remedy.
#[test]
fn structural_type_change_error_names_type_and_restart_not_reload() {
    let refusal = change("(deftype S A B)", "(deftype- S A B)", "S").unwrap();
    let message = refusal.to_error().to_string();
    assert!(message.contains("m/S"), "{message}");
    assert!(message.contains("restart"), "{message}");
    assert!(!message.contains("reload"), "{message}");
}

// spec: design/int/session-transaction.md §2.6 — only a key declaring a type
// on both sides is compared; a callable or a new type is not this pass's.
#[test]
fn structural_type_change_ignores_non_type_and_new_keys() {
    assert_eq!(change("(defn f [] 1)", "(defn f [] \"s\")", "f"), None);
    assert_eq!(change("(defn f [] 1)", "(deftype T [:Int v])", "T"), None);
}
