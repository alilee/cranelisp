//! Session-level unit evidence for the persistence designs of
//! `design/int/s125-binary-clean.md` §4: the exhaustive section selector
//! (§4.1), authored order (§4.2), the cache never ahead of the file (§4.3) and
//! the refusal of a redefinition of a macro-generated definition (§4.4).

use super::*;
use std::path::Path;

/// A REPL session over `root` with one pool worker and no cache.
fn repl_session(root: &Path) -> CompilerSession {
    let mut s = CompilerSession::new(
        SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        },
        root.to_path_buf(),
        "user",
    )
    .expect("test session bootstrap");
    s.set_lib_dirs(Vec::new());
    s
}

/// Evaluate each turn in order, regenerating after each as the read loop does
/// for a defining turn, and return the backing file.
fn saved_after(turns: &[&str]) -> String {
    let root = tempfile::tempdir().unwrap();
    let mut s = repl_session(root.path());
    for turn in turns {
        s.eval(turn)
            .unwrap_or_else(|error| panic!("`{turn}` evaluates: {error}"));
        s.regenerate_backing_file();
    }
    s.shutdown();
    std::fs::read_to_string(root.path().join("user.cl")).unwrap_or_default()
}

/// Whether every needle occurs in `text`, each after the one before.
fn in_order(text: &str, needles: &[&str]) -> bool {
    let positions: Option<Vec<usize>> = needles.iter().map(|needle| text.find(needle)).collect();
    positions.is_some_and(|positions| positions.windows(2).all(|pair| pair[0] < pair[1]))
}

// ---------------------------------------------------------------------------
// §4.1 — one exhaustive selector (ACT-1068, ACT-1101)
// ---------------------------------------------------------------------------

// spec: repl/spec/15-session-persistence.md §15.4 rule 1 — a multi-signature
// function is persisted under its base name (ACT-1068).
#[test]
fn regeneration_writes_a_multi_signature_family() {
    let family = "(defn f ([:Int n] n) ([:String s] (str-len s)))";
    let saved = saved_after(&["(import [primitives [*]])", family]);
    assert!(saved.contains(family), "user.cl:\n{saved}");
}

// spec: repl/spec/15-session-persistence.md §15.1 — constructing a parametric
// product mints an instance that is not module content; the save still writes
// (ACT-1101). The seeded `Pair` is the second leg.
#[test]
fn regeneration_writes_after_a_product_instance_is_minted() {
    let saved = saved_after(&[
        "(deftype (P2 a b) [:a x :b y])",
        "(P2 1 2)",
        "(defn f [] 1)",
    ]);
    assert!(
        saved.contains("(deftype (P2 a b) [:a x :b y])") && saved.contains("(defn f [] 1)"),
        "user.cl:\n{saved}"
    );
    let saved = saved_after(&["(primitives/Pair 1 2)", "(defn g [] 2)"]);
    assert!(saved.contains("(defn g [] 2)"), "user.cl:\n{saved}");
}

// ---------------------------------------------------------------------------
// §4.2 — authored order (ACT-1005)
// ---------------------------------------------------------------------------

// spec: repl/spec/15-session-persistence.md §15.4 rule 2 — definitions are
// written in the order they were entered, whatever their kind and name.
#[test]
fn regeneration_keeps_entered_order_across_kinds_and_names() {
    let saved = saved_after(&[
        "(defn z [] 1)",
        "(deftype T K)",
        "(defn y [] 2)",
        "(defmacro m [] (quote 7))",
        "(defn x [] 3)",
    ]);
    assert!(
        in_order(
            &saved,
            &["(defn z", "(deftype T", "(defn y", "(defmacro m", "(defn x"]
        ),
        "user.cl:\n{saved}"
    );
}

// spec: repl/spec/15-session-persistence.md §15.4 rule 2 — a redefined symbol
// keeps its original position.
#[test]
fn a_redefinition_keeps_its_position() {
    let saved = saved_after(&[
        "(defn z [] 1)",
        "(defmacro m [] (quote 41))",
        "(defn z [] 2)",
    ]);
    assert!(
        in_order(&saved, &["(defn z [] 2)", "(defmacro m"]) && !saved.contains("(defn z [] 1)"),
        "user.cl:\n{saved}"
    );
}

// spec: repl/spec/15-session-persistence.md §15.4 rule 2 — the macro-before-use
// exception: a redefined function moves after a later macro it newly uses.
#[test]
fn a_redefinition_moves_after_a_later_macro_it_newly_uses() {
    let saved = saved_after(&[
        "(import [primitives [add-i64]])",
        "(defn f [] 1)",
        "(defmacro m [] (quote 41))",
        "(defn g [] 5)",
        "(defn f [] (add-i64 (m) 1))",
    ]);
    assert!(
        in_order(&saved, &["(defmacro m", "(defn f", "(defn g"]),
        "f moves just after m, before the later g:\n{saved}"
    );
}

// spec: repl/spec/15-session-persistence.md §15.4 rules 1–2 — a `begin`'s
// members are their own entries, so a redefinition of one replaces only that
// member, in its place.
#[test]
fn a_begin_split_by_redefinition_writes_each_survivor_alone() {
    let saved = saved_after(&[
        "(defn first [] 0)",
        "(begin (defn f [] 1) (defn g [] 10))",
        "(defn g [] 20)",
        "(defn last [] 9)",
    ]);
    assert!(
        in_order(
            &saved,
            &[
                "(defn first",
                "(defn f [] 1)",
                "(defn g [] 20)",
                "(defn last"
            ]
        ) && !saved.contains("(begin")
            && !saved.contains("(defn g [] 10)"),
        "user.cl:\n{saved}"
    );
}

// spec: repl/spec/15-session-persistence.md §15.4 rule 2;
// design/int/s125-binary-clean.md §4.2 row 1 — a REPL `begin` dissolves into its
// members: each is written once, in member order, and no `begin` is written.
#[test]
fn a_repl_begin_is_written_as_its_members() {
    let saved = saved_after(&["(begin (defn f [] 1) (defn g [] 10))"]);
    assert!(
        in_order(&saved, &["(defn f [] 1)", "(defn g [] 10)"])
            && saved.matches("(defn f [] 1)").count() == 1
            && saved.matches("(defn g [] 10)").count() == 1
            && !saved.contains("(begin"),
        "user.cl:\n{saved}"
    );
}

/// The authored position recorded for `user/name`.
fn position_of(s: &CompilerSession, name: &str) -> Option<AuthoredPosition> {
    s.shared
        .introspection
        .as_ref()?
        .get(&FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: cranelisp_types::Symbol::from(name),
        })?
        .position
}

// spec: spec/09-macros.md §9.6 (the SHOULD leniency);
// design/int/s125-binary-clean.md §4.2 row 2 — a legacy backing file's `begin`
// loads and dissolves: its members take distinct file positions in member
// order, and the next save writes the members with no `begin`.
#[test]
fn a_legacy_file_begin_dissolves_at_load() {
    let root = tempfile::tempdir().unwrap();
    let backing = "(defn first [] 0)\n(begin (defn f [] 1) (defn g [] 10))\n";
    std::fs::write(root.path().join("user.cl"), backing).unwrap();
    let mut s = repl_session(root.path());
    s.register_entry_module("user").expect("backing file loads");
    let (first, f, g) = (
        position_of(&s, "first"),
        position_of(&s, "f"),
        position_of(&s, "g"),
    );
    s.eval("(defn later [] 2)").unwrap();
    s.regenerate_backing_file();
    s.shutdown();
    let saved = std::fs::read_to_string(root.path().join("user.cl")).unwrap();
    assert!(
        first.is_some() && first < f && f < g,
        "members take distinct file positions in member order: {first:?} {f:?} {g:?}"
    );
    assert!(
        in_order(
            &saved,
            &[
                "(defn first",
                "(defn f [] 1)",
                "(defn g [] 10)",
                "(defn later"
            ]
        ) && !saved.contains("(begin"),
        "user.cl:\n{saved}"
    );
}

// spec: repl/spec/15-session-persistence.md §15.4 rules 1–2; spec/09-macros.md
// §9.6.1; design/int/s125-binary-clean.md §4.2 row 3 (R1) — a macro call that
// was a `begin` member is its own entry, written once as authored, and a
// redefinition of a sibling member replaces only that member.
#[test]
fn a_begin_macro_member_is_its_own_entry() {
    let saved = saved_after(&[MAKE, "(begin (make f) (defn a [] 1))", "(defn a [] 20)"]);
    assert!(
        saved.matches("(make f)").count() == 1
            && saved.matches("(defn a [] 20)").count() == 1
            && in_order(&saved, &["(make f)", "(defn a [] 20)"])
            && !saved.contains("(defn a [] 1)")
            && !saved.contains("(begin"),
        "user.cl:\n{saved}"
    );
}

// spec: repl/spec/15-session-persistence.md §15.4 rule 2;
// design/int/s125-binary-clean.md §4.2 row 4 (R3) — a redefined `begin` member
// keeps its own place among its siblings.
#[test]
fn a_redefined_begin_member_keeps_member_order() {
    let saved = saved_after(&[
        "(begin (defn z [] 1) (defn a [] 2) (defn m [] 3))",
        "(defn a [] 20)",
    ]);
    assert!(
        in_order(
            &saved,
            &["(defn z [] 1)", "(defn a [] 20)", "(defn m [] 3)"]
        ) && !saved.contains("(begin"),
        "user.cl:\n{saved}"
    );
}

const TWO: &str = "(defmacro two [] '(begin (defn p [] 1) (defn q [] 2)))";

// spec: spec/09-macros.md §9.6.1; design/int/s125-binary-clean.md §4.2 row 5 —
// a macro-call entry owns every key its expansion generated, and a re-entered
// call replaces the entry in place: a key the re-entry adds joins the entry's
// position, so the call is written once.
#[test]
fn a_re_entered_call_replaces_its_entry_in_place() {
    let root = tempfile::tempdir().unwrap();
    let mut s = repl_session(root.path());
    s.eval(TWO).unwrap();
    s.eval("(two)").unwrap();
    s.eval("(defn later [] 9)").unwrap();
    s.eval("(defmacro two [] '(begin (defn p [] 1) (defn q [] 2) (defn r [] 3)))")
        .unwrap();
    s.eval("(two)").unwrap();
    s.regenerate_backing_file();
    let (p, q, r) = (
        position_of(&s, "p"),
        position_of(&s, "q"),
        position_of(&s, "r"),
    );
    assert_eq!(s.eval("(r)").unwrap().unwrap().value(), 3);
    s.shutdown();
    let saved = std::fs::read_to_string(root.path().join("user.cl")).unwrap();
    assert!(p.is_some() && p == q && q == r, "{p:?} {q:?} {r:?}");
    assert!(
        saved.matches("(two)").count() == 1 && in_order(&saved, &["(two)", "(defn later"]),
        "user.cl:\n{saved}"
    );
}

// spec: spec/09-macros.md §9.6.1; design/int/s125-binary-clean.md §4.4 and §4.2
// row 6 — an identical re-entry whose expansion drops a key the entry owns is
// refused, naming the dropped key; nothing publishes, not even the expansion's
// macro checkpoint, and the live set and the saved file stand.
#[test]
fn a_shrinking_re_entry_is_refused_and_publishes_nothing() {
    let root = tempfile::tempdir().unwrap();
    let mut s = repl_session(root.path());
    s.eval(TWO).unwrap();
    s.eval("(two)").unwrap();
    s.regenerate_backing_file();
    let before = std::fs::read_to_string(root.path().join("user.cl")).unwrap();
    s.eval("(defmacro two [] '(begin (defmacro h [] 5) (defn p [] 1)))")
        .unwrap();
    let Err(error) = s.eval("(two)") else {
        panic!("the shrinking re-entry is refused");
    };
    let message = error.to_string();
    let h_published = s.eval("(h)").is_ok();
    let q = s.eval("(q)").unwrap().unwrap().value();
    let after = std::fs::read_to_string(root.path().join("user.cl")).unwrap();
    s.shutdown();
    assert!(
        message.contains("`q`") && message.contains("user/two"),
        "{message}"
    );
    assert!(!h_published, "the expansion's checkpoint did not publish");
    assert_eq!(q, 2, "the dropped key stays live");
    assert_eq!(before, after, "the saved file is unchanged");
}

// spec: spec/09-macros.md §9.6.1; design/int/s125-binary-clean.md §4.4 —
// control: re-entry with the macro unchanged is accepted.
#[test]
fn an_unchanged_re_entry_is_accepted() {
    let root = tempfile::tempdir().unwrap();
    let mut s = repl_session(root.path());
    s.eval(TWO).unwrap();
    s.eval("(two)").unwrap();
    s.eval("(two)")
        .expect("an identical re-entry of the same set passes");
    assert_eq!(s.eval("(q)").unwrap().unwrap().value(), 2);
    s.shutdown();
}

// ---------------------------------------------------------------------------
// §4.6 R2 — the checkpoint funnel applies the §9.6.1 refusal
// ---------------------------------------------------------------------------

const MAKER: &str = "(defmacro maker [] (quote (defmacro g [] (quote 10))))";

// spec: spec/09-macros.md §9.6.1; design/int/s125-binary-clean.md §4.6 R2 — a
// written `defmacro` over a live macro-generated macro is refused at the
// checkpoint, which publishes nothing; the generating call stays saved.
#[test]
fn a_written_defmacro_over_a_generated_macro_is_refused_at_the_checkpoint() {
    let root = tempfile::tempdir().unwrap();
    let mut s = repl_session(root.path());
    s.eval(MAKER).unwrap();
    s.eval("(maker)").unwrap();
    s.regenerate_backing_file();
    let Err(error) = s.eval("(defmacro g [] (quote 20))") else {
        panic!("the written defmacro is refused");
    };
    let g = s.eval("(g)").unwrap().unwrap().value();
    s.regenerate_backing_file();
    s.shutdown();
    let saved = std::fs::read_to_string(root.path().join("user.cl")).unwrap();
    assert!(error.to_string().contains("cannot redefine `g`"), "{error}");
    assert_eq!(g, 10, "the checkpoint published nothing");
    assert!(
        saved.matches("(maker)").count() == 1
            && !saved.lines().any(|line| line.starts_with("(defmacro g ")),
        "user.cl:\n{saved}"
    );
}

// spec: spec/09-macros.md §9.6.1; design/int/s125-binary-clean.md §4.6 R2 — the
// generating call re-entered passes the checkpoint; in a `begin`, an earlier
// macro checkpoint stays published when a later one is refused.
#[test]
fn the_generating_call_passes_the_checkpoint_and_earlier_checkpoints_stand() {
    let root = tempfile::tempdir().unwrap();
    let mut s = repl_session(root.path());
    s.eval(MAKER).unwrap();
    s.eval("(maker)").unwrap();
    s.eval("(maker)")
        .expect("the same call passes the checkpoint");
    let refused = s.eval("(begin (defmacro h [] (quote 1)) (defmacro g [] (quote 20)))");
    let h = s.eval("(h)").unwrap().unwrap().value();
    let g = s.eval("(g)").unwrap().unwrap().value();
    s.shutdown();
    assert!(refused.is_err(), "the later `g` checkpoint is refused");
    assert_eq!((h, g), (1, 10));
}

// spec: repl/spec/15-session-persistence.md §15.4 rule 2 — file-loaded forms
// keep source order, and REPL forms are appended after them.
#[test]
fn entered_forms_follow_the_file_in_entry_order() {
    let root = tempfile::tempdir().unwrap();
    let backing = "(defn zeta [] 1)\n(defn alpha [] 2)\n";
    std::fs::write(root.path().join("user.cl"), backing).unwrap();
    let mut s = repl_session(root.path());
    s.register_entry_module("user").expect("backing file loads");
    s.eval("(defn omega [] 3)").unwrap();
    s.regenerate_backing_file();
    s.eval("(defn beta [] 4)").unwrap();
    s.regenerate_backing_file();
    s.shutdown();
    let saved = std::fs::read_to_string(root.path().join("user.cl")).unwrap();
    assert!(
        in_order(
            &saved,
            &["(defn zeta", "(defn alpha", "(defn omega", "(defn beta"]
        ),
        "user.cl:\n{saved}"
    );
}

// ---------------------------------------------------------------------------
// §4.4 — a macro-generated definition is not redefined (S125-Q5)
// ---------------------------------------------------------------------------

const MAKE: &str = "(defmacro make [n] `(defn ~n [] 10))";

fn generated_session(root: &Path) -> CompilerSession {
    let mut s = repl_session(root);
    s.eval(MAKE).unwrap();
    s.eval("(make generated)").unwrap();
    s.regenerate_backing_file();
    s
}

// spec: spec/09-macros.md §9.6.1 — a written form redefining a live generated
// definition is refused at the redefining form; the definition stands.
#[test]
fn a_written_redefinition_of_a_generated_definition_is_refused() {
    let root = tempfile::tempdir().unwrap();
    let mut s = generated_session(root.path());
    let Err(error) = s.eval("(defn generated [] 20)") else {
        panic!("the written redefinition is refused");
    };
    let message = error.to_string();
    assert!(
        message.contains("cannot redefine `generated`") && message.contains("user/make"),
        "{message}"
    );
    assert_eq!(s.eval("(generated)").unwrap().unwrap().value(), 10);
    s.shutdown();
}

// spec: spec/09-macros.md §9.6.1 — another call of the same macro, or a call of
// another macro, generating a live name is refused.
#[test]
fn another_call_generating_a_live_name_is_refused() {
    let root = tempfile::tempdir().unwrap();
    let mut s = repl_session(root.path());
    s.eval("(defmacro make [x] `(defn generated [] ~x))")
        .unwrap();
    s.eval("(defmacro other [x] `(defn generated [] ~x))")
        .unwrap();
    s.eval("(make 10)").unwrap();
    assert!(s.eval("(make 20)").is_err(), "other arguments are refused");
    assert!(s.eval("(other 10)").is_err(), "another macro is refused");
    assert_eq!(s.eval("(generated)").unwrap().unwrap().value(), 10);
    s.shutdown();
}

// spec: spec/09-macros.md §9.6.1 — re-entering the same call replaces what it
// generates, and is written once at the call's position.
#[test]
fn re_entering_the_same_call_replaces_its_definitions() {
    let saved = saved_after(&[
        "(defmacro make [x] `(defn generated [] ~x))",
        "(make 10)",
        "(defn later [] 1)",
        "(defmacro make [x] `(defn generated [] (primitives/add-i64 ~x 1)))",
        "(make 10)",
    ]);
    assert_eq!(saved.matches("(make 10)").count(), 1, "user.cl:\n{saved}");
    assert!(in_order(&saved, &["(make 10)", "(defn later"]), "{saved}");
}

// spec: spec/09-macros.md §9.6.1 — control: a written definition is redefined
// as usual.
#[test]
fn a_written_definition_is_redefined_as_usual() {
    let root = tempfile::tempdir().unwrap();
    let mut s = repl_session(root.path());
    s.eval("(defn f [] 10)").unwrap();
    s.eval("(defn f [] 20)").unwrap();
    assert_eq!(s.eval("(f)").unwrap().unwrap().value(), 20);
    s.shutdown();
}

// ---------------------------------------------------------------------------
// §4.3 — the cache never ahead of the file (ACT-1102)
// ---------------------------------------------------------------------------

/// A cached REPL session over `root`, its entry loaded from `backing`.
fn cached_session_over(root: &Path, backing: &str) -> CompilerSession {
    std::fs::write(root.join("user.cl"), backing).unwrap();
    let mut s = CompilerSession::new(
        SessionSettings {
            no_color: true,
            no_cache: false,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        },
        root.to_path_buf(),
        "user",
    )
    .expect("test session bootstrap");
    s.set_lib_dirs(Vec::new());
    s.register_entry_module("user").expect("backing file loads");
    s
}

// spec: repl/spec/15-session-persistence.md §15.2; design/int/s125-binary-clean.md
// §4.3 — a definition turn whose regeneration did not write (here the
// inline-`mod` guard) leaves the table ahead of the file: the module diverges.
#[test]
fn a_regeneration_that_does_not_write_diverges_the_module() {
    let root = tempfile::tempdir().unwrap();
    let backing = "(defn old [] 1)\n(mod nested (defn child [] 1))\n";
    let mut s = cached_session_over(root.path(), backing);
    let user = ModuleFullPath::from("user");
    assert_eq!(
        s.shared.cache.agreement(&user),
        crate::session_setup::FileAgreement::Agrees,
        "a loaded module agrees with its file"
    );
    s.eval("(defn unsaved [] 42)").unwrap();
    s.regenerate_backing_file();
    let diverged = s.shared.cache.agreement(&user);
    s.shutdown();
    assert_eq!(
        std::fs::read_to_string(root.path().join("user.cl")).unwrap(),
        backing
    );
    assert_eq!(diverged, crate::session_setup::FileAgreement::Diverged);
}

// spec: design/int/s125-binary-clean.md §4.3 — control: a regeneration that
// writes leaves the module agreeing.
#[test]
fn a_regeneration_that_writes_agrees_with_the_file() {
    let root = tempfile::tempdir().unwrap();
    let mut s = cached_session_over(root.path(), "(defn old [] 1)\n");
    s.eval("(defn saved [] 42)").unwrap();
    s.regenerate_backing_file();
    let agreement = s.shared.cache.agreement(&ModuleFullPath::from("user"));
    s.shutdown();
    assert!(
        std::fs::read_to_string(root.path().join("user.cl"))
            .unwrap()
            .contains("(defn saved [] 42)")
    );
    assert_eq!(agreement, crate::session_setup::FileAgreement::Agrees);
}

// spec: spec/09-macros.md §9.6.1; repl/spec/15-session-persistence.md §15.4
// rules 1–2; tests/plan/s125-evidence-delta.md §19 (R5) — a macro call that
// generates a key a written entry owns becomes the one owning entry of every
// key it generates, at the call's own position, after the macro it uses; the
// written entry is retired and the call is written once.
#[test]
fn a_macro_call_over_a_written_definition_owns_it_at_the_calls_position() {
    let saved = saved_after(&["(defn p [] 0)", TWO, "(two)"]);
    assert!(
        saved.matches("(two)").count() == 1
            && !saved.contains("(defn p [] 0)")
            && in_order(&saved, &["(defmacro two", "(two)"]),
        "user.cl:\n{saved}"
    );
}
