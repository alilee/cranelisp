// Caller text is never qualified (`design/int/expansion-qualification-scope.md`
// §2.7, cells E1–E5). The home module `b` imports `add-i64`; the caller `user`
// does not, so a qualified `primitives/add-i64` in the expansion can only come
// from `b`'s scope.

use crate::session_v4::{CompilerSession, RunMode, SessionSettings};

const HOME: &str = "\
(import [primitives [add-i64]])
(defmacro pass [x] x)
(defmacro inc [x] `(add-i64 ~x 1))
(defmacro rebuild [x] (match x [(macros/SexpSym s) (macros/SexpSym s) _ x]))
(defmacro construct [x] `(~(macros/SexpSym \"add-i64\") ~x))
(defmacro inner [y] `(add-i64 ~y 1))
(defmacro outer [x] `(b/inner ~x))
";

/// The flat expansion of each form, through one session whose home module is
/// [`HOME`].
fn expansions(forms: &[&str]) -> Vec<String> {
    let dir = tempfile::tempdir().unwrap();
    let settings = SessionSettings {
        no_color: true,
        no_cache: true,
        codegen_behaviour: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
        priority_workers: 1,
        nice_workers: 0,
        run_mode: RunMode::Repl,
    };
    let mut session = CompilerSession::new(settings, dir.path().to_path_buf(), "user").unwrap();
    session.set_lib_dirs(Vec::new());
    session
        .register_module_with_source("b", HOME, &dir.path().join("b.cl"))
        .unwrap();
    let flat = forms
        .iter()
        .map(|form| session.expand_form_sexp(form).unwrap().format_flat())
        .collect();
    session.shutdown();
    flat
}

// spec: spec/08-modules.md §8.6.1; expansion-qualification-scope.md §2.7 E1 —
// an argument the macro returns stays bare, in the caller's scope.
#[test]
fn returned_argument_stays_bare() {
    assert_eq!(expansions(&["(b/pass (add-i64 1 2))"]), ["(add-i64 1 2)"]);
}

// spec: spec/09-macros.md §9.3.4; expansion-qualification-scope.md §2.7 E2 —
// the template's reference is qualified and the spliced argument spelled the
// same is not.
#[test]
fn template_reference_qualified_beside_bare_argument() {
    assert_eq!(
        expansions(&["(b/inc (add-i64 1 2))"]),
        ["(primitives/add-i64 (add-i64 1 2) 1)"]
    );
}

// spec: expansion-qualification-scope.md §2.7 E3 — a symbol rebuilt around the
// argument's own string is the caller's.
#[test]
fn symbol_rebuilt_around_argument_string_stays_bare() {
    assert_eq!(expansions(&["(b/rebuild add-i64)"]), ["add-i64"]);
}

// spec: expansion-qualification-scope.md §2.7 E4 — a symbol the macro
// constructs is the macro's, even when an argument has its spelling.
#[test]
fn constructed_symbol_spelled_like_argument_is_qualified() {
    assert_eq!(
        expansions(&["(b/construct add-i64)"]),
        ["(primitives/add-i64 add-i64)"]
    );
}

// spec: expansion-qualification-scope.md §2.7 E5 — caller text passed through
// an inner macro of the same home module stays bare; the inner template's
// reference is qualified.
#[test]
fn caller_text_stays_bare_through_nested_home_macro() {
    assert_eq!(
        expansions(&["(b/outer (add-i64 1 2))"]),
        ["(primitives/add-i64 (add-i64 1 2) 1)"]
    );
}
