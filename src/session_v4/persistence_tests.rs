use super::*;
use cranelisp_types::{
    Binding, CallableTarget, CodegenBehaviour, CranelispError, Life, Realization, Sexp, Symbol,
    Visibility,
};
use std::path::Path;

const BACKING: &str = "(defn kept [] 1)\n(defn gone [] 2)\n";

/// A REPL session whose `user` table holds `kept` with an authored record and,
/// when `with_orphan`, `orphan` with none; the backing file defines `kept` and
/// a non-live `gone`, but never `orphan`, so rehydration cannot supply it.
fn session_with_backing(with_orphan: bool) -> (CompilerSession, PathBuf) {
    let (s, root) = super::info_source_tests::isolated_session();
    let user = ModuleFullPath::from("user");
    let mut table = SessionSymbolTable::new_with_params(user.clone());
    let _ = crate::repl::test_support::install_userfn(&mut table, "kept", None, Visibility::Public);
    if with_orphan {
        let _ = crate::repl::test_support::install_userfn(
            &mut table,
            "orphan",
            None,
            Visibility::Public,
        );
    }
    s.shared.symbol_tables.insert(user.clone(), table);
    let kept = cranelisp_frontend::parse("(defn kept [] 1)")
        .expect("fixture parses")
        .remove(0);
    s.shared
        .introspection
        .as_ref()
        .expect("REPL session populates introspection")
        .entry(FQSymbol {
            module: user,
            symbol: Symbol::from("kept"),
        })
        .or_default()
        .sexp = Some(kept);
    std::fs::write(root.join("user.cl"), BACKING).expect("write backing file");
    (s, root)
}

// spec: design/int/session-persistence.md §2.4.3 — an entry with no authored
// form refuses the write: the backing file keeps its bytes, so the next start
// cannot lose the entry's source.
#[test]
fn regeneration_refusal_leaves_backing_file_bytes_unchanged() {
    let (mut s, root) = session_with_backing(true);
    s.regenerate_backing_file();
    let after = std::fs::read_to_string(root.join("user.cl")).expect("backing file present");
    let _ = std::fs::remove_dir_all(&root);
    assert_eq!(after, BACKING);
}

// spec: design/int/session-persistence.md §2.4.3 negative — a fully recorded
// module is written as usual.
#[test]
fn regeneration_writes_fully_recorded_module() {
    let (mut s, root) = session_with_backing(false);
    s.regenerate_backing_file();
    let after = std::fs::read_to_string(root.join("user.cl")).expect("backing file present");
    let _ = std::fs::remove_dir_all(&root);
    assert_eq!(after, "(defn kept [] 1)\n");
}

// ---------------------------------------------------------------------------
// Publication writer and `/mod` recompile
// (design/int/session-persistence.md §2.4.1, §2.4.5; repl-lifecycle.md §1.2)
// ---------------------------------------------------------------------------

/// A REPL session over `root` with one pool worker, so reloads and
/// dependency loads run.
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

fn record_of(s: &CompilerSession, module: &str, name: &str) -> Option<Introspection> {
    s.shared
        .introspection
        .as_ref()
        .expect("REPL session keeps introspection")
        .get(&FQSymbol {
            module: ModuleFullPath::from(module),
            symbol: Symbol::from(name),
        })
        .map(|record| record.clone())
}

/// The record's authored carriers, comparable across generations.
fn authored(record: &Introspection) -> (Option<String>, Option<String>, Option<String>, String) {
    (
        record.sexp.as_ref().map(Sexp::format_flat),
        record.expanded.as_ref().map(Sexp::format_flat),
        record.source.clone(),
        format!("{:?}", record.ast),
    )
}

fn flat(text: &str) -> String {
    cranelisp_frontend::parse(text)
        .expect("fixture parses")
        .remove(0)
        .format_flat()
}

/// `rejected` redefines `f` and fails; `f`'s record keeps its published
/// generation, and so does regeneration.
fn assert_rejected_redefinition_keeps_record(rejected: &str) {
    const F: &str = "(defn f [:Int x] (add-i64 x 1))";
    let root = tempfile::tempdir().unwrap();
    let mut s = repl_session(root.path());
    s.eval("(import [primitives [*]])").unwrap();
    s.eval(F).unwrap();
    s.eval("(defn k [:Int y] (f y))").unwrap();
    let published = authored(&record_of(&s, "user", "f").unwrap());
    assert_eq!(published.0, Some(flat(F)), "precondition: `f` is recorded");

    assert!(
        s.eval(rejected).is_err(),
        "precondition: `{rejected}` is rejected"
    );

    assert_eq!(authored(&record_of(&s, "user", "f").unwrap()), published);
    s.regenerate_backing_file();
    let saved = std::fs::read_to_string(root.path().join("user.cl")).unwrap();
    assert!(
        saved.contains(F) && !saved.contains(rejected),
        "user.cl:\n{saved}"
    );
    s.shutdown();
}

// spec: repl/spec/18-redefinition.md §18.8 — a redefinition rejected at
// typecheck changes no record (design/int/session-persistence.md §2.4.1).
#[test]
fn typecheck_rejected_redefinition_keeps_the_published_record() {
    assert_rejected_redefinition_keeps_record("(defn f [:Int x] (nope x))");
}

// spec: repl/spec/18-redefinition.md §18.8 — a redefinition the commit gate
// refuses (its type change breaks the dependent `k`) changes no record.
#[test]
fn commit_gate_rejected_redefinition_keeps_the_published_record() {
    assert_rejected_redefinition_keeps_record("(defn f [:String s] (str-len s))");
}

// spec: design/int/session-persistence.md §2.4.1 — an accepted replacement
// replaces form, AST and text, and clears an expansion the new generation
// lacks; the new generation's codegen facts are present.
#[test]
fn accepted_replacement_replaces_every_authored_carrier() {
    let root = tempfile::tempdir().unwrap();
    let mut s = repl_session(root.path());
    s.eval("(defmacro mkg [] `(defn g [] 1))").unwrap();
    s.eval("(mkg)").unwrap();
    let expanded = record_of(&s, "user", "g").unwrap();
    assert_eq!(
        expanded.sexp.as_ref().map(Sexp::format_flat),
        Some(flat("(mkg)"))
    );
    assert!(
        expanded.expanded.is_some(),
        "precondition: an expansion is recorded"
    );

    s.eval("(defn g [] 2)").unwrap();

    let replaced = record_of(&s, "user", "g").unwrap();
    assert_eq!(
        replaced.sexp.as_ref().map(Sexp::format_flat),
        Some(flat("(defn g [] 2)"))
    );
    assert!(
        replaced.expanded.is_none(),
        "the prior expansion is cleared"
    );
    assert_eq!(replaced.source.as_deref(), Some("(defn g [] 2)"));
    assert!(replaced.ast.is_some());
    assert_ne!(format!("{:?}", replaced.ast), format!("{:?}", expanded.ast));
    assert!(replaced.clif_ir.is_some() && replaced.code_size.is_some());
    s.shutdown();
}

// spec: design/int/session-persistence.md §2.4.1 — a definition whose
// dependency cannot be loaded fails and installs none of the record it staged
// before the gap; a definition whose dependency loads is recorded after the retry. The
// qualified references are type annotations, which expansion does not load, so
// the record is staged first. Both attempts of the retried definition stage the
// same record, so this does not observe when it was installed.
#[test]
fn unloadable_dependency_installs_no_record_and_loaded_retry_is_recorded() {
    const RETRIED: &str = "(defn h [:dep/T x] x)";
    let root = tempfile::tempdir().unwrap();
    std::fs::write(
        root.path().join("dep.cl"),
        "(deftype T [:primitives/Int v])\n",
    )
    .unwrap();
    let mut s = repl_session(root.path());

    assert!(s.eval("(defn lost [:absent/T x] x)").is_err());
    assert!(record_of(&s, "user", "lost").is_none());

    s.eval(RETRIED).unwrap();
    let record = record_of(&s, "user", "h").unwrap();
    assert_eq!(
        record.sexp.as_ref().map(Sexp::format_flat),
        Some(flat(RETRIED))
    );
    s.shutdown();
}

const DECLS_V1: &str = "(import [primitives [*]])\n(deftype T [:Int v])\n\
                        (deftrait Disp (dp [x] Int))\n(impl Disp T (defn dp [t] 42))\n";
const DECLS_V2: &str = "(import [primitives [*]])\n(deftype T \"edited\" [:Int v])\n\
                        (deftrait Disp (dp [x] Int))\n(impl Disp T (defn dp [t] 43))\n";
const DECLS_BROKEN: &str = "(import [primitives [*]])\n(deftype T \"edited\" [:Int v])\n\
                            (deftrait Disp (dp [x] Int))\n(impl Disp T (defn dp [t] (nope)))\n";

// spec: repl/spec/15-session-persistence.md §15.3 — an accepted reload
// replaces the records of the declarations it changed
// (design/int/session-persistence.md §2.4.1); a failed reload leaves the
// module cleared (repl/spec/14-file-watching.md §14.5 items 1–2), so none of
// its displaced records remains (design/int/session-transaction.md §7.3.1).
// The type edit is docstring-only: a structural one is refused (§14.8).
#[test]
fn reload_replaces_declaration_records_and_failed_reload_clears_them() {
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("user.cl");
    std::fs::write(&path, DECLS_V1).unwrap();
    let mut s = repl_session(root.path());
    s.register_module("user").unwrap();
    let user = ModuleFullPath::from("user");
    let type_v1 = record_of(&s, "user", "T").unwrap();
    assert_eq!(
        type_v1.sexp.as_ref().map(Sexp::format_flat),
        Some(flat("(deftype T [:Int v])"))
    );

    std::fs::write(&path, DECLS_V2).unwrap();
    attempt(s.reload_module(&user, &path, Default::default(), &Default::default())).unwrap();
    let type_v2 = record_of(&s, "user", "T").unwrap();
    let impl_v2 = record_of(&s, "user", "Disp.T").unwrap();
    assert_eq!(
        type_v2.sexp.as_ref().map(Sexp::format_flat),
        Some(flat("(deftype T \"edited\" [:Int v])"))
    );
    assert_eq!(
        type_v2.source.as_deref(),
        Some("(deftype T \"edited\" [:Int v])")
    );
    assert_eq!(
        impl_v2.sexp.as_ref().map(Sexp::format_flat),
        Some(flat("(impl Disp T (defn dp [t] 43))"))
    );

    std::fs::write(&path, DECLS_BROKEN).unwrap();
    assert!(
        attempt(s.reload_module(&user, &path, Default::default(), &Default::default())).is_err()
    );
    assert!(record_of(&s, "user", "T").is_none());
    assert!(record_of(&s, "user", "Disp.T").is_none());
    s.shutdown();
}

const MACRO_LIB: &str = "(defmacro mk [] `(begin (defn x-def [] 1) (defmacro x [] `(x-def))))\n\
                         (mk)\n(defn base [] 5)\n";

/// Make `lib` look cache-installed: flagged in the scheduler, with no records
/// and no recorded text, as a cache restore leaves it.
fn mark_cache_installed(s: &CompilerSession, module: &str) {
    let module = ModuleFullPath::from(module);
    s.shared.scheduler.cached_module_insert(module.clone());
    s.shared
        .introspection
        .as_ref()
        .unwrap()
        .retain(|key, _| key.module != module);
    if let Some(mut product) = s.shared.typecheck_products.get_mut(&module) {
        product.source_text = None;
    }
}

/// A session whose entry imports `lib`, compiled from `root/lib.cl`.
fn session_importing_lib(root: &Path) -> CompilerSession {
    std::fs::write(root.join("lib.cl"), MACRO_LIB).unwrap();
    let mut s = repl_session(root);
    s.eval("(import [lib [base]])").unwrap();
    s
}

// spec: design/int/session-persistence.md §2.4.5 — `/mod` into a
// cache-installed module recompiles it from its backing file, so the
// definitions its top-level macro call produced are recorded under that call.
#[test]
fn mod_into_cache_installed_module_recompiles_it_from_source() {
    let root = tempfile::tempdir().unwrap();
    let mut s = session_importing_lib(root.path());
    mark_cache_installed(&s, "lib");
    let lib = ModuleFullPath::from("lib");

    assert_eq!(s.handle_mod("lib"), None);

    assert!(!s.shared.scheduler.is_cached_module(&lib));
    assert_eq!(s.current_module_path(), lib);
    let x_def = record_of(&s, "lib", "x-def").expect("the macro call's product is recorded");
    assert_eq!(
        x_def.sexp.as_ref().map(Sexp::format_flat),
        Some(flat("(mk)"))
    );
    let product = s.shared.typecheck_products.get(&lib).unwrap();
    assert_eq!(
        product.file_path.as_deref(),
        Some(root.path().join("lib.cl").as_path())
    );
    assert_eq!(product.source_text.as_deref(), Some(MACRO_LIB));
    drop(product);
    s.shutdown();
}

// spec: design/int/session-persistence.md §2.4.5 negative — `/mod` into a
// module compiled from source this session or into the entry module switches
// without recompiling.
#[test]
fn mod_without_cache_installed_target_does_not_recompile() {
    let root = tempfile::tempdir().unwrap();
    let mut s = session_importing_lib(root.path());
    let lib = ModuleFullPath::from("lib");
    let user = ModuleFullPath::from("user");
    s.shared
        .introspection
        .as_ref()
        .unwrap()
        .retain(|key, _| key.module != lib);

    assert_eq!(s.handle_mod("lib"), None);
    assert!(
        record_of(&s, "lib", "base").is_none(),
        "a module compiled from source is not recompiled"
    );

    let entry_file = root.path().join("user.cl");
    std::fs::write(&entry_file, "(defn entry-only [] 1)\n").unwrap();
    crate::worker::ensure_typecheck_product(&s.shared.typecheck_products, &user);
    s.shared
        .typecheck_products
        .get_mut(&user)
        .unwrap()
        .file_path = Some(entry_file);
    s.shared.scheduler.cached_module_insert(user.clone());
    assert_eq!(s.handle_mod(""), None);
    assert!(
        record_of(&s, "user", "entry-only").is_none(),
        "the entry module is never recompiled by `/mod`"
    );
    s.shutdown();
}

// spec: design/int/repl-lifecycle.md §1.2 — a reload keeps the module's
// backing path and records its text, so regeneration of a library-directory
// module writes its own file and never `{project_root}/{module}.cl`.
#[test]
fn reload_keeps_backing_path_for_library_module_regeneration() {
    let root = tempfile::tempdir().unwrap();
    let libs = root.path().join("libs");
    std::fs::create_dir_all(&libs).unwrap();
    let lib_file = libs.join("libm.cl");
    std::fs::write(&lib_file, "(defn base [] 5)\n").unwrap();
    let mut s = repl_session(root.path());
    s.set_lib_dirs(vec![libs.clone()]);
    s.eval("(import [libm [base]])").unwrap();
    let libm = ModuleFullPath::from("libm");

    std::fs::write(&lib_file, "(defn base [] 6)\n").unwrap();
    attempt(s.reload_module(&libm, &lib_file, Default::default(), &Default::default())).unwrap();
    let product = s.shared.typecheck_products.get(&libm).unwrap();
    assert_eq!(product.file_path.as_deref(), Some(lib_file.as_path()));
    assert_eq!(product.source_text.as_deref(), Some("(defn base [] 6)\n"));
    drop(product);

    assert_eq!(s.handle_mod("libm"), None);
    s.eval("(defn later [] 2)").unwrap();
    s.regenerate_backing_file();

    let saved = std::fs::read_to_string(&lib_file).unwrap();
    assert!(
        saved.contains("(defn base [] 6)") && saved.contains("(defn later [] 2)"),
        "libs/libm.cl:\n{saved}"
    );
    assert!(!root.path().join("libm.cl").exists());
    s.shutdown();
}

// ---------------------------------------------------------------------------
// Failed modules: failed source and restart-required
// (repl/spec/14-file-watching.md §14.5 (session lock), §14.8;
// design/int/repl-lifecycle.md §1.3.1)
// ---------------------------------------------------------------------------

const TYPE_V1: &str = "(import [primitives [*]])\n(deftype T [:Int v])\n(defn g [] 1)\n";
const TYPE_STRUCTURAL: &str = "(import [primitives [*]])\n(deftype T [:String v])\n(defn g [] 1)\n";
const TYPE_BODY_ERROR: &str =
    "(import [primitives [*]])\n(deftype T [:Int v])\n(defn g [] (nope))\n";
const TYPE_PARSE_ERROR: &str = "(import [primitives [*]])\n(deftype T [:Int v])\n(defn g [] \n";

/// A REPL session whose `user` module was loaded from `root/user.cl` holding
/// `TYPE_V1`.
fn session_with_live_type(root: &Path) -> (CompilerSession, PathBuf) {
    let path = root.join("user.cl");
    std::fs::write(&path, TYPE_V1).unwrap();
    let mut s = repl_session(root);
    s.register_module("user").unwrap();
    (s, path)
}

/// Save `source` to `path` and rebuild its module and dependents as the
/// watcher does; whether the module's own rebuild succeeded.
fn save_and_reload(s: &mut CompilerSession, path: &Path, source: &str) -> bool {
    std::fs::write(path, source).unwrap();
    let module = ModuleFullPath::from(path.file_stem().unwrap().to_str().unwrap());
    s.run_reload_plan(vec![(module.clone(), path.to_path_buf())])
        .iter()
        .any(|outcome| outcome.module == module && outcome.status.is_rebuilt())
}

/// A module's own attempt as a result. The callers reload a module no failed
/// dependency refuses, so a wait fails the test.
fn attempt(reload: lifecycle::ReloadAttempt) -> Result<(), CranelispError> {
    match reload.attempt {
        lifecycle::Attempt::Settled(ReloadStatus::Rebuilt) => Ok(()),
        lifecycle::Attempt::Settled(ReloadStatus::Failed(error)) => Err(*error),
        lifecycle::Attempt::Settled(ReloadStatus::Waiting) => {
            panic!("the attempt waits on a failed dependency")
        }
        lifecycle::Attempt::Deferred(_) => panic!("the attempt is deferred"),
    }
}

fn restart_required_type(s: &CompilerSession, module: &str) -> Option<String> {
    match &s.failed_modules.get(&ModuleFullPath::from(module))?.cause {
        FailureCause::RestartRequired(type_name) => Some(type_name.to_string()),
        FailureCause::FailedSource => None,
    }
}

/// The cause `module` stands failed with, if it does.
fn lock_of(s: &CompilerSession, module: &str) -> Option<FailureCause> {
    s.failed_modules
        .get(&ModuleFullPath::from(module))
        .map(|failed| failed.cause.clone())
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock) — a reload that
// fails to parse, in an unlocked session, stands the module failed with failed
// source.
#[test]
fn reload_parse_failure_locks_the_module_with_failed_source() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = session_with_live_type(root.path());
    assert_eq!(lock_of(&s, "user"), None, "precondition");

    assert!(!save_and_reload(&mut s, &path, TYPE_PARSE_ERROR));
    assert_eq!(lock_of(&s, "user"), Some(FailureCause::FailedSource));
    assert!(s.is_locked());
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock), §14.8 — a type
// error stands the module failed with failed source; a later structural
// refusal replaces that cause with restart-required.
#[test]
fn reload_failure_locks_with_its_cause_and_a_structural_refusal_upgrades_it() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = session_with_live_type(root.path());
    let user = ModuleFullPath::from("user");

    assert!(!save_and_reload(&mut s, &path, TYPE_BODY_ERROR));
    assert_eq!(
        lock_of(&s, "user"),
        Some(FailureCause::FailedSource),
        "type error"
    );
    assert!(!save_and_reload(&mut s, &path, TYPE_PARSE_ERROR));
    assert_eq!(
        lock_of(&s, "user"),
        Some(FailureCause::FailedSource),
        "parse error"
    );

    assert!(!save_and_reload(&mut s, &path, TYPE_STRUCTURAL));
    assert_eq!(restart_required_type(&s, "user").as_deref(), Some("user/T"));
    assert!(s.failed_modules.contains_key(&user) && s.is_locked());
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock), §14.6 — a module
// standing failed with failed source stays failed through `/reset`, and a
// successful reload releases it and the session lock.
#[test]
fn failed_source_lock_stands_until_a_successful_reload() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = session_with_live_type(root.path());
    let user = ModuleFullPath::from("user");
    assert!(!save_and_reload(&mut s, &path, TYPE_BODY_ERROR));

    s.dispatch_command(crate::repl::ReplCommand::Reset, &mut Vec::new());
    assert_eq!(
        lock_of(&s, "user"),
        Some(FailureCause::FailedSource),
        "/reset"
    );
    assert!(s.is_locked(), "/reset keeps the session locked");

    assert!(save_and_reload(&mut s, &path, TYPE_V1));
    assert_eq!(lock_of(&s, "user"), None);
    assert!(!s.failed_modules.contains_key(&user) && !s.is_locked());
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock) — while the module
// stands failed with failed source, no regeneration writes the saved file, and
// a definition turn is refused naming the file with the save remedy, leaving
// the session unchanged; an expression is refused too.
#[test]
fn failed_source_module_keeps_saved_file_and_refuses_definition_turns() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = session_with_live_type(root.path());
    assert!(!save_and_reload(&mut s, &path, TYPE_BODY_ERROR));

    s.regenerate_backing_file();
    assert_eq!(std::fs::read_to_string(&path).unwrap(), TYPE_BODY_ERROR);

    let CommandResult::Final(refused) = s.process_commands("(defn h [] 2)", &mut Vec::new()) else {
        panic!("a definition turn in a locked session must be refused");
    };
    assert!(
        refused.contains("user.cl") && refused.contains("does not compile"),
        "{refused}"
    );
    assert!(!refused.contains("restart"), "{refused}");
    let user_table = s.shared.symbol_tables.get(&ModuleFullPath::from("user"));
    assert!(user_table.unwrap().get("h").is_none());
    let CommandResult::Final(expression) = s.process_commands("(g)", &mut Vec::new()) else {
        panic!("an expression is refused while locked");
    };
    assert!(expression.starts_with("Cannot evaluate"), "{expression}");
    s.shutdown();
}

// spec: design/int/session-transaction.md §2.6 — the type pass precedes the
// per-key guard, so a sum type's visibility change is refused with the restart
// remedy rather than the declaration-visibility refusal's reload remedy.
#[test]
fn sum_visibility_reload_is_refused_with_the_restart_remedy() {
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("user.cl");
    std::fs::write(&path, "(deftype S A B)\n").unwrap();
    let mut s = repl_session(root.path());
    s.register_module("user").unwrap();

    std::fs::write(&path, "(deftype- S A B)\n").unwrap();
    let error = attempt(s.reload_module(
        &ModuleFullPath::from("user"),
        &path,
        Default::default(),
        &Default::default(),
    ))
    .unwrap_err()
    .to_string();
    assert!(
        error.contains("user/S") && error.contains("restart"),
        "{error}"
    );
    assert!(!error.contains("reload"), "{error}");
    assert_eq!(restart_required_type(&s, "user").as_deref(), Some("user/S"));
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.8, §14.5 (session lock);
// design/int/repl-lifecycle.md §1.3.1 (Status is the last attempt) — the
// restart-required failure stands through `/reset`; a later failing save that
// is not structural records failed source, and a successful reload releases
// the module.
#[test]
fn restart_required_stands_until_a_successful_reload() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = session_with_live_type(root.path());
    let user = ModuleFullPath::from("user");
    assert!(!save_and_reload(&mut s, &path, TYPE_STRUCTURAL));

    s.dispatch_command(crate::repl::ReplCommand::Reset, &mut Vec::new());
    assert_eq!(
        restart_required_type(&s, "user").as_deref(),
        Some("user/T"),
        "/reset"
    );
    assert!(!save_and_reload(&mut s, &path, TYPE_BODY_ERROR));
    assert_eq!(
        lock_of(&s, "user"),
        Some(FailureCause::FailedSource),
        "later failure"
    );

    assert!(save_and_reload(&mut s, &path, TYPE_V1));
    assert_eq!(lock_of(&s, "user"), None);
    assert!(!s.failed_modules.contains_key(&user) && !s.is_locked());
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.8, §14.5 (session lock) — no
// regeneration writes the retained file, and a definition turn is refused
// naming the file, the type and the restart, leaving the session unchanged; an
// expression is refused too.
#[test]
fn restart_required_module_keeps_saved_file_and_refuses_definition_turns() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = session_with_live_type(root.path());
    assert!(!save_and_reload(&mut s, &path, TYPE_STRUCTURAL));

    s.regenerate_backing_file();
    assert_eq!(std::fs::read_to_string(&path).unwrap(), TYPE_STRUCTURAL);

    let CommandResult::Final(refused) = s.process_commands("(defn h [] 2)", &mut Vec::new()) else {
        panic!("a definition turn in a restart-required module must be refused");
    };
    assert!(
        refused.contains("user.cl") && refused.contains("user/T") && refused.contains("restart"),
        "{refused}"
    );
    let user_table = s.shared.symbol_tables.get(&ModuleFullPath::from("user"));
    assert!(user_table.unwrap().get("h").is_none());
    let CommandResult::Final(expression) = s.process_commands("(g)", &mut Vec::new()) else {
        panic!("an expression is refused while locked");
    };
    assert!(expression.starts_with("Cannot evaluate"), "{expression}");
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock), §14.8;
// design/int/repl-lifecycle.md §1.2 (Waiting), §1.3.1 — the lock is one
// session state: after a structural refusal of `shapes`, its dependent `user`
// waits rather than failing, a saved `user` still importing `shapes` waits
// too, and a definition in the unrelated module `other` is refused, leaving
// every file as saved.
#[test]
fn session_lock_holds_in_every_module_while_a_dependent_waits() {
    const SHAPES_V1: &str = "(import [primitives [*]])\n(deftype T [:Int v])\n";
    const SHAPES_STRUCTURAL: &str = "(import [primitives [*]])\n(deftype T [:String v])\n";
    const USER: &str = "(import [shapes [T]])\n(import [other [base]])\n(defn one [] 1)\n";
    const OTHER: &str = "(defn base [] 5)\n";
    let root = tempfile::tempdir().unwrap();
    let shapes = root.path().join("shapes.cl");
    std::fs::write(&shapes, SHAPES_V1).unwrap();
    let other_file = root.path().join("other.cl");
    std::fs::write(&other_file, OTHER).unwrap();
    let user_file = root.path().join("user.cl");
    std::fs::write(&user_file, USER).unwrap();
    let mut s = repl_session(root.path());
    s.register_module("user").unwrap();

    assert!(!save_and_reload(&mut s, &shapes, SHAPES_STRUCTURAL));
    assert_eq!(
        restart_required_type(&s, "shapes").as_deref(),
        Some("shapes/T")
    );
    assert_eq!(lock_of(&s, "user"), None, "the dependent waits");
    assert!(!save_and_reload(&mut s, &user_file, USER));
    assert_eq!(lock_of(&s, "user"), None, "the saved dependent waits");

    assert_eq!(s.handle_mod("other"), None);
    let refused = s.process_commands("(defn h [] 2)", &mut Vec::new());
    assert!(
        refusal_names(&refused, &["shapes.cl"]),
        "{}",
        shown(&refused)
    );
    s.regenerate_backing_file();
    assert_eq!(std::fs::read_to_string(&other_file).unwrap(), OTHER);
    assert_eq!(std::fs::read_to_string(&user_file).unwrap(), USER);
    assert_eq!(std::fs::read_to_string(&shapes).unwrap(), SHAPES_STRUCTURAL);
    s.shutdown();
}

// ---------------------------------------------------------------------------
// Startup recovery (repl/spec/15-session-persistence.md §15.2.3)
// ---------------------------------------------------------------------------

// spec: repl/spec/14-file-watching.md §14.6; repl/spec/15-session-persistence.md
// §15.1, §15.2.3 — an imported module that fails at startup stands failed and
// the entry waits. Recovery purges the dependency's never-compiled table, so
// `/mod` to it reloads it, reports its failure and stays put
// (design/int/int.md §8.5.1); the dependency still stands failed and no
// regeneration writes its file.
#[test]
fn startup_failed_dependency_stands_failed_through_a_mod_load_and_keeps_its_file() {
    const FAILING_LIB: &str = "(defn keep-me [] (nope))\n";
    let root = tempfile::tempdir().unwrap();
    let lib_path = root.path().join("lib.cl");
    write_files(
        root.path(),
        &[
            ("lib.cl", FAILING_LIB),
            ("user.cl", "(import [lib [keep-me]])\n(defn g [] 1)\n"),
        ],
    );
    let (mut s, report) = started_session(root.path());

    assert!(report.is_some(), "the startup failure is reported");
    assert_eq!(lock_of(&s, "lib"), Some(FailureCause::FailedSource));
    assert_eq!(lock_of(&s, "user"), None, "the entry waits");

    assert!(matches!(
        s.handle_mod("lib"),
        Some(crate::repl::commands::ModReport::Refused(_))
    ));
    assert_eq!(s.current_module_path(), ModuleFullPath::from("user"));
    assert_eq!(lock_of(&s, "lib"), Some(FailureCause::FailedSource));
    s.regenerate_backing_file();
    assert_eq!(std::fs::read_to_string(&lib_path).unwrap(), FAILING_LIB);
    s.shutdown();
}

const SIBLING_V1: &str = "(import [primitives [*]])\n(defn sib [] 1)\n";
const SIBLING_BODY_ERROR: &str = "(import [primitives [*]])\n(defn sib [] (nope))\n";

/// A REPL session whose entry imports `lib` (holding `TYPE_V1`) and `count`
/// modules unrelated to it; returns `lib`'s file and theirs.
fn session_with_siblings(root: &Path, count: usize) -> (CompilerSession, PathBuf, Vec<PathBuf>) {
    let lib = root.join("lib.cl");
    std::fs::write(&lib, TYPE_V1).unwrap();
    let mut entry = String::from("(import [lib [T]])\n");
    let mut siblings = Vec::new();
    for i in 0..count {
        let file = root.join(format!("sib{i}.cl"));
        std::fs::write(&file, SIBLING_V1).unwrap();
        entry.push_str(&format!("(import [sib{i} [sib]])\n"));
        siblings.push(file);
    }
    std::fs::write(root.join("user.cl"), entry).unwrap();
    let mut s = repl_session(root);
    s.register_module("user").unwrap();
    (s, lib, siblings)
}

/// Leave each sibling standing `Failed` through a reload with a body error.
fn fail_siblings(s: &mut CompilerSession, siblings: &[PathBuf]) {
    for file in siblings {
        assert!(!save_and_reload(s, file, SIBLING_BODY_ERROR));
    }
}

// spec: repl/spec/14-file-watching.md §14.8; design/int/repl-lifecycle.md §1.3
// Outcome — a structural reload beside a standing failure reports its own
// refusal and records its own marker. Fresh sessions reseed the scheduler's map
// order; the every-module wait was right only when `lib` came first among the
// failed modules.
#[test]
fn structural_reload_beside_a_failed_module_reports_its_own_refusal() {
    const SESSIONS: usize = 5;
    const SIBLINGS: usize = 3;
    let lib = ModuleFullPath::from("lib");
    for run in 0..SESSIONS {
        let root = tempfile::tempdir().unwrap();
        let (mut s, lib_file, siblings) = session_with_siblings(root.path(), SIBLINGS);
        fail_siblings(&mut s, &siblings);

        std::fs::write(&lib_file, TYPE_STRUCTURAL).unwrap();
        let error =
            attempt(s.reload_module(&lib, &lib_file, Default::default(), &Default::default()))
                .unwrap_err()
                .to_string();
        assert!(
            error.contains("lib/T") && error.contains("restart"),
            "run {run}: {error}"
        );
        assert_eq!(
            restart_required_type(&s, "lib").as_deref(),
            Some("lib/T"),
            "run {run}"
        );
        s.shutdown();
    }
}

// spec: repl/spec/14-file-watching.md §14.8; design/int/repl-lifecycle.md §1.3
// Outcome — a successful reload succeeds while another module stands `Failed`,
// and releases the module from the failed set with its restart marker.
#[test]
fn reload_beside_a_failed_module_succeeds_and_lifts_its_restart_marker() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, lib_file, siblings) = session_with_siblings(root.path(), 1);
    let lib = ModuleFullPath::from("lib");
    assert!(!save_and_reload(&mut s, &lib_file, TYPE_STRUCTURAL));
    assert_eq!(restart_required_type(&s, "lib").as_deref(), Some("lib/T"));
    fail_siblings(&mut s, &siblings);

    std::fs::write(&lib_file, TYPE_V1).unwrap();
    attempt(s.reload_module(&lib, &lib_file, Default::default(), &Default::default())).unwrap();
    assert_eq!(restart_required_type(&s, "lib"), None);
    assert!(!s.failed_modules.contains_key(&lib));
    assert!(s.shared.scheduler.is_failed(&ModuleFullPath::from("sib0")));
    s.shutdown();
}

// ---------------------------------------------------------------------------
// Whole-file rebuild (design/int/session-transaction.md §7.3.4) and the one
// reload executor (design/int/repl-lifecycle.md §1.2, §1.3.1)
// ---------------------------------------------------------------------------

const REBUILD_V1: &str = "(defn g [] 1)\n(defn h [] 2)\n";

/// A REPL session whose `user` module was loaded from `root/user.cl` holding
/// `source`.
fn rebuild_session(root: &Path, source: &str) -> (CompilerSession, PathBuf) {
    let path = root.join("user.cl");
    std::fs::write(&path, source).unwrap();
    let mut s = repl_session(root);
    s.register_module("user").unwrap();
    (s, path)
}

/// Save `source` to `path` and rebuild `user` alone from it.
fn rebuild_user(s: &mut CompilerSession, path: &Path, source: &str) -> Result<(), CranelispError> {
    std::fs::write(path, source).unwrap();
    reload_user(s, path)
}

fn table_of(s: &CompilerSession, module: &str) -> SessionSymbolTable {
    s.shared
        .symbol_tables
        .get(&ModuleFullPath::from(module))
        .expect("module has a table")
        .clone()
}

fn symbol_names(table: &SessionSymbolTable) -> Vec<String> {
    let mut names: Vec<String> = table
        .all_symbols()
        .map(|(name, _)| name.to_string())
        .collect();
    names.sort();
    names
}

/// Every compiled owner `table` holds, as `(owner symbol, slot)`.
fn compiled_owners(table: &SessionSymbolTable) -> Vec<(String, usize)> {
    table
        .codegen_targets()
        .filter_map(|(target, arm)| {
            let owner = match &target {
                CallableTarget::Binding(owner)
                | CallableTarget::OverloadArm { owner, .. }
                | CallableTarget::MacroClause { owner, .. } => owner,
                _ => return None,
            };
            match &arm.life {
                Life::Concrete {
                    slot,
                    realization: Realization::Body { code: Some(_), .. },
                    ..
                } => Some((owner.symbol.to_string(), slot.index())),
                _ => None,
            }
        })
        .collect()
}

fn pooled(s: &CompilerSession) -> Vec<(String, Option<usize>)> {
    s.shared
        .retained_code
        .lock()
        .unwrap()
        .iter()
        .map(|retained| (retained.fq.symbol.to_string(), retained.slot))
        .collect()
}

fn locked_with_failed_source(s: &CompilerSession, module: &str) -> bool {
    lock_of(s, module) == Some(FailureCause::FailedSource)
}

// spec: design/int/session-transaction.md §7.3.1 — a rebuild whose source
// omits `h` leaves it absent with no record, pools its compiled owner and
// tombstones nothing; the module keeps its GOT.
#[test]
fn rebuild_omitting_a_function_leaves_it_absent_with_its_owner_pooled() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = rebuild_session(root.path(), REBUILD_V1);
    let before = table_of(&s, "user");
    let h_slot = before
        .get("h")
        .and_then(Binding::callable_got_slot)
        .expect("precondition: `h` has a slot");
    assert!(record_of(&s, "user", "h").is_some(), "precondition");

    rebuild_user(&mut s, &path, "(defn g [] 1)\n").unwrap();

    let after = table_of(&s, "user");
    assert!(after.get("h").is_none(), "binding");
    assert!(record_of(&s, "user", "h").is_none(), "record");
    assert!(after.get("g").is_some(), "control: `g` is rebuilt");
    assert!(after.retired_slots().is_empty(), "no tombstone");
    assert!(Arc::ptr_eq(&after.got, &before.got), "the GOT is kept");
    assert!(
        pooled(&s).contains(&("h".to_string(), Some(h_slot))),
        "the displaced owner is pooled"
    );
    s.shutdown();
}

const PROLOGUE_LIB: &str = "(import [primitives [*]])\n(deftrait Sh (sh [x] Int))\n\
                            (defn id [x] x)\n";
const PROLOGUE_FULL: &str = ";; The user module.\n\n(import [primitives [*]])\n\
                             (import [lib [id Sh]])\n(import [(lib l) []])\n(mod child)\n\
                             (defn plain [] 1)\n(defn fam ([:Int x] x) ([:String s] (str-len s)))\n\
                             (defn tid [x] x)\n(defn uses-tid [] (tid 1))\n(deftype P [:Int a])\n\
                             (deftrait Tr (tr [x] Int))\n(impl Sh Int (defn sh [x] 1))\n\
                             (defmacro m [] `1)\n";

// spec: design/int/session-transaction.md §7.3.1, §7.3.4 (Prologue) — a
// rebuild keeping every kind of declaration records each once; a rebuild
// omitting them leaves every one absent, with the session state they
// established outside the table reset, no tombstone, the GOT kept and every
// displaced compiled owner pooled.
#[test]
fn rebuild_prologue_establishes_exactly_what_the_saved_source_keeps() {
    let root = tempfile::tempdir().unwrap();
    std::fs::write(root.path().join("lib.cl"), PROLOGUE_LIB).unwrap();
    std::fs::create_dir_all(root.path().join("user")).unwrap();
    std::fs::write(root.path().join("user").join("child.cl"), "(defn c [] 3)\n").unwrap();
    let (mut s, path) = rebuild_session(root.path(), PROLOGUE_FULL);
    let user = ModuleFullPath::from("user");
    let alias = |name: &str| cranelisp_types::module_alias_key(&user, name);
    let shell = cranelisp_types::trait_impl_key(
        &cranelisp_types::FQTypeName::new(
            ModuleFullPath::from("primitives"),
            cranelisp_types::TypeName::from("Int"),
        ),
        &cranelisp_types::FQTraitName::new(
            ModuleFullPath::from("lib"),
            cranelisp_types::TraitName::from("Sh"),
        ),
    );
    let declarations = ["P", "Tr", "fam", "m", "plain", "tid", "uses-tid"];

    rebuild_user(&mut s, &path, PROLOGUE_FULL).unwrap();
    let kept = table_of(&s, "user");
    assert_eq!(
        (
            kept.imports.len(),
            kept.submodules.len(),
            kept.written_trait_impls.len()
        ),
        (3, 1, 1),
        "each structural record once"
    );
    assert!(kept.module_preamble.is_some(), "preamble");
    for name in declarations {
        assert!(kept.get(name).is_some(), "`{name}` is kept");
    }
    let imported_id = s
        .explicit_import_sources(&user)
        .into_iter()
        .filter(|(name, _)| name == "id")
        .count();
    assert_eq!(imported_id, 1, "`id` is imported once");
    assert!(s.shared.module_aliases.get(&alias("l")).is_some());
    assert!(s.shared.module_aliases.get(&alias("child")).is_some());
    assert!(table_of(&s, "lib").get(shell.as_ref()).is_some());

    let owners = compiled_owners(&kept);
    assert!(!owners.is_empty(), "precondition: compiled owners");
    rebuild_user(&mut s, &path, "(defn z [] 0)\n").unwrap();

    let bare = table_of(&s, "user");
    assert_eq!(symbol_names(&bare), ["z"], "only what the source keeps");
    assert!(bare.imports.is_empty() && bare.submodules.is_empty());
    assert!(bare.written_trait_impls.is_empty());
    assert!(bare.module_preamble.is_none(), "preamble");
    assert!(bare.retired_slots().is_empty(), "no tombstone");
    assert!(Arc::ptr_eq(&bare.got, &kept.got), "the GOT is kept");
    assert!(
        s.explicit_import_sources(&user)
            .iter()
            .all(|(name, _)| name != "id")
    );
    assert!(s.eval("(id 5)").is_err(), "`id` is unresolved");
    assert!(s.shared.module_aliases.get(&alias("l")).is_none());
    assert!(s.shared.module_aliases.get(&alias("child")).is_none());
    assert!(
        table_of(&s, "lib").get(shell.as_ref()).is_none(),
        "the foreign trait home holds no shell"
    );
    let pool = pooled(&s);
    for (owner, slot) in owners {
        assert!(
            pool.contains(&(owner.clone(), Some(slot))),
            "`{owner}` at slot {slot} is pooled"
        );
    }
    s.shutdown();
}

// spec: design/int/session-transaction.md §7.3.4 (Prelude bit);
// spec/08-modules.md §8.8.1 — a rebuild that adds an explicit prelude import
// turns the fallback off; one that removes it turns the fallback on again.
#[test]
fn rebuild_recomputes_the_prelude_fallback_from_the_saved_source() {
    let root = tempfile::tempdir().unwrap();
    std::fs::write(root.path().join("prelude.cl"), "(defn pid [x] x)\n").unwrap();
    let (mut s, path) = rebuild_session(root.path(), "(defn g [] 1)\n");
    let user = ModuleFullPath::from("user");
    let fallback = |s: &CompilerSession| {
        s.shared
            .prelude_fallback
            .get(&user)
            .is_some_and(|enabled| *enabled)
    };
    assert!(fallback(&s), "precondition");

    rebuild_user(&mut s, &path, "(import [prelude [pid]])\n(defn g [] 1)\n").unwrap();
    assert!(!fallback(&s), "an explicit prelude import");
    rebuild_user(&mut s, &path, "(defn g [] 1)\n").unwrap();
    assert!(fallback(&s), "the import removed");
    s.shutdown();
}

// spec: design/int/session-transaction.md §7.3.4 (Unresolved omission);
// repl/spec/14-file-watching.md §14.2 steps 2–3, §14.5 (session lock) — a remaining
// definition naming an omitted function, in call or value position or from a
// template, fails as an unresolved name and leaves the module standing failed
// with failed source.
#[test]
fn rebuild_naming_an_omitted_function_fails_unresolved_and_locks() {
    for (v1, reloaded) in [
        (REBUILD_V1, "(defn g [] (h))\n"),
        (REBUILD_V1, "(defn g [] h)\n"),
        ("(defn h [] 2)\n(defn t [x] (h))\n", "(defn t [x] (h))\n"),
    ] {
        let root = tempfile::tempdir().unwrap();
        let (mut s, path) = rebuild_session(root.path(), v1);
        let error = rebuild_user(&mut s, &path, reloaded)
            .expect_err(reloaded)
            .to_string();
        assert!(error.contains('h'), "{reloaded}: {error}");
        assert!(table_of(&s, "user").get("h").is_none(), "{reloaded}");
        assert!(locked_with_failed_source(&s, "user"), "{reloaded}");
        s.shutdown();
    }
}

// spec: design/int/session-transaction.md §7.3.4 (Unresolved omission) — a
// body naming a function whose import the saved source omits fails as an
// unresolved name and stands the module failed.
#[test]
fn rebuild_naming_an_omitted_import_fails_unresolved_and_locks() {
    let root = tempfile::tempdir().unwrap();
    std::fs::write(root.path().join("lib.cl"), "(defn id [x] x)\n").unwrap();
    let (mut s, path) = rebuild_session(root.path(), "(import [lib [id]])\n(defn k [] (id 1))\n");

    let error = rebuild_user(&mut s, &path, "(defn k [] (id 1))\n")
        .expect_err("the import is omitted")
        .to_string();
    assert!(error.contains("id"), "{error}");
    assert!(locked_with_failed_source(&s, "user"));
    s.shutdown();
}

// spec: design/int/session-transaction.md §7.3.4 (Empty source) — a rebuild
// from a source with no checkable form succeeds with an empty table.
#[test]
fn rebuild_from_an_empty_source_leaves_an_empty_table() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = rebuild_session(root.path(), REBUILD_V1);
    rebuild_user(&mut s, &path, "").unwrap();
    assert!(symbol_names(&table_of(&s, "user")).is_empty());
    s.shutdown();
}

// spec: design/int/session-transaction.md §7.3.1 — a gap keeps the attempt's
// provenance: a rebuild whose body autoloads a module mid-check still leaves
// the definition it omits absent.
#[test]
fn rebuild_resumed_after_a_dependency_gap_still_omits_the_function() {
    let root = tempfile::tempdir().unwrap();
    std::fs::write(root.path().join("lib.cl"), "(defn a [] 1)\n").unwrap();
    let (mut s, path) = rebuild_session(root.path(), REBUILD_V1);
    let lib = ModuleFullPath::from("lib");
    assert!(
        s.shared.scheduler.module_pool(&lib).is_none(),
        "precondition"
    );

    rebuild_user(&mut s, &path, "(defn g [] (lib/a))\n").unwrap();

    assert!(
        s.shared.scheduler.module_pool(&lib).is_some(),
        "the rebuild took the dependency gap"
    );
    let table = table_of(&s, "user");
    assert!(table.get("g").is_some() && table.get("h").is_none());
    s.shutdown();
}

// spec: design/int/session-transaction.md §7.3.2, §7.3.4 (Reference);
// repl/spec/14-file-watching.md §14.8 — the first failing rebuild holds the
// established table, and later failing rebuilds keep it, so a structural type
// change refuses every time, also after a dependency gap. Success drops it,
// and a type a successful rebuild removed may return with another structure.
#[test]
fn established_reference_survives_failures_and_drops_on_success() {
    const GAPPED_STRUCTURAL: &str =
        "(import [primitives [*]])\n(deftype T [:String v])\n(defn g [] (dep/a))\n";
    const WITHOUT_T: &str = "(import [primitives [*]])\n(defn g [] 1)\n";
    let root = tempfile::tempdir().unwrap();
    std::fs::write(root.path().join("dep.cl"), "(defn a [] 1)\n").unwrap();
    let (mut s, path) = session_with_live_type(root.path());
    let user = ModuleFullPath::from("user");
    let established = table_of(&s, "user");

    let refusal = rebuild_user(&mut s, &path, TYPE_STRUCTURAL).unwrap_err();
    assert!(refusal.to_string().contains("restart"), "{refusal}");
    let held = Arc::clone(s.reload_references.get(&user).expect("reference held"));
    assert_eq!(
        symbol_names(&held),
        symbol_names(&established),
        "the established table"
    );

    for (attempt, source) in [TYPE_STRUCTURAL, GAPPED_STRUCTURAL].into_iter().enumerate() {
        let refusal = rebuild_user(&mut s, &path, source).unwrap_err();
        assert!(
            refusal.to_string().contains("restart"),
            "attempt {attempt}: {refusal}"
        );
        assert!(
            Arc::ptr_eq(&held, s.reload_references.get(&user).unwrap()),
            "attempt {attempt} keeps the first reference"
        );
    }
    assert!(
        s.shared
            .scheduler
            .module_pool(&ModuleFullPath::from("dep"))
            .is_some(),
        "the gapped attempt loaded its dependency"
    );

    rebuild_user(&mut s, &path, WITHOUT_T).unwrap();
    assert!(!s.reload_references.contains_key(&user), "success drops it");
    rebuild_user(&mut s, &path, TYPE_STRUCTURAL).expect("`T` returns with a new structure");
    s.shutdown();
}

// spec: design/int/session-transaction.md §7.3.3, §7.3.4 (GOT reuse), §7.5 —
// rebuilds reuse slot indices on the module's one GOT: more rebuilds of a
// module whose every callable changes type than the GOT has slots all succeed,
// retiring nothing. An increment's type-changing redefinition still retires
// its slot, and the next mint does not reissue it.
#[test]
fn repeated_rebuilds_reuse_got_slots_while_increments_retire_theirs() {
    const CALLABLES: usize = 128;
    const REBUILDS: usize = 9;
    assert!(CALLABLES * REBUILDS > cranelisp_types::GOT_TABLE_SIZE);
    let generation = |n: usize| -> String {
        (0..CALLABLES)
            .map(|i| {
                if n % 2 == 0 {
                    format!("(defn f{i} [] {i})\n")
                } else {
                    format!("(defn f{i} [] \"{i}\")\n")
                }
            })
            .collect()
    };
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = rebuild_session(root.path(), &generation(0));
    let got = Arc::clone(&table_of(&s, "user").got);

    for n in 1..=REBUILDS {
        rebuild_user(&mut s, &path, &generation(n)).unwrap_or_else(|e| panic!("rebuild {n}: {e}"));
        let table = table_of(&s, "user");
        assert!(Arc::ptr_eq(&table.got, &got), "rebuild {n} keeps the GOT");
        assert!(
            table.retired_slots().is_empty(),
            "rebuild {n} retires nothing"
        );
    }

    s.eval("(defn q [] 1)").unwrap();
    let q_slot = table_of(&s, "user")
        .get("q")
        .and_then(Binding::callable_got_slot)
        .unwrap();
    s.eval("(defn q [] \"one\")").unwrap();
    let table = table_of(&s, "user");
    assert!(
        table
            .retired_slots()
            .iter()
            .any(|retired| retired.slot.index() == q_slot),
        "the increment retires `q`'s slot"
    );
    s.eval("(defn r [] 2)").unwrap();
    assert_ne!(
        table_of(&s, "user")
            .get("r")
            .and_then(Binding::callable_got_slot),
        Some(q_slot),
        "no reissue"
    );
    s.shutdown();
}

// spec: design/int/repl-lifecycle.md §1.2 (Order check) — two modules change
// together and the earlier-sorting one's new source adds a qualified call into
// the other: the plan built it first, against the other's displaced
// generation, so the order check rebuilds it after the other and the call
// reaches the new definition rather than the slot it vacated.
#[test]
fn order_check_rebuilds_a_new_qualified_caller_after_its_callee() {
    let root = tempfile::tempdir().unwrap();
    let zlib = root.path().join("zlib.cl");
    let app = root.path().join("app.cl");
    std::fs::write(&zlib, "(defn b [] 1)\n(defn f [] 2)\n").unwrap();
    std::fs::write(&app, "(defn run [] 0)\n").unwrap();
    let mut s = repl_session(root.path());
    s.eval("(import [zlib [f]])").unwrap();
    s.eval("(import [app [run]])").unwrap();
    let run = |s: &mut CompilerSession| s.eval("(app/run)").unwrap().expect("a value").value();
    assert_eq!(run(&mut s), 0, "precondition");

    std::fs::write(&app, "(defn run [] (zlib/f))\n").unwrap();
    std::fs::write(&zlib, "(defn f [] 5)\n").unwrap();
    let outcomes = s.run_reload_plan(vec![
        (ModuleFullPath::from("app"), app),
        (ModuleFullPath::from("zlib"), zlib),
    ]);

    assert!(
        outcomes.iter().all(|outcome| outcome.status.is_rebuilt()),
        "{:?}",
        outcomes
            .iter()
            .filter_map(|o| o.notice())
            .collect::<Vec<_>>()
    );
    assert_eq!(outcomes.len(), 2, "one outcome per module");
    assert_eq!(run(&mut s), 5);
    s.shutdown();
}

// spec: design/int/repl-lifecycle.md §1.3.1 — a dependent that fails in a
// watcher plan rooted at its changed dependency stands failed, while the
// dependency that compiled does not.
#[test]
fn watcher_plan_locks_a_failed_dependent() {
    let root = tempfile::tempdir().unwrap();
    let lib = root.path().join("lib.cl");
    std::fs::write(&lib, "(defn f [] 1)\n").unwrap();
    let (mut s, _path) = rebuild_session(root.path(), "(import [lib [f]])\n(defn k [] (f))\n");

    assert!(save_and_reload(&mut s, &lib, "(defn f2 [] 1)\n"));

    assert_eq!(lock_of(&s, "lib"), None);
    assert!(locked_with_failed_source(&s, "user"));
    s.shutdown();
}

// spec: design/int/repl-lifecycle.md §1.3.1; design/int/session-persistence.md
// §2.4.5 — `/mod`'s recompile of a cache-installed module runs through the
// executor: its failure is reported and leaves the module standing failed.
#[test]
fn mod_recompile_failure_locks_the_module() {
    let root = tempfile::tempdir().unwrap();
    let mut s = session_importing_lib(root.path());
    mark_cache_installed(&s, "lib");
    std::fs::write(root.path().join("lib.cl"), "(defn base [] (nope))\n").unwrap();

    let Some(crate::repl::commands::ModReport::RecompileFailed(failure)) = s.handle_mod("lib")
    else {
        panic!("the failed recompile is reported");
    };

    assert!(failure.starts_with("[errors: lib.cl]"), "{failure}");
    assert!(locked_with_failed_source(&s, "lib"));
    s.shutdown();
}

// ---------------------------------------------------------------------------
// Reload next basket: failure dependencies and the startup reset
// (design/int/repl-lifecycle.md §1.2.1, §1.3.1), module cycles at publication
// (design/int/int.md §6.11) and the `/mod` target (int.md §8.5.1)
// ---------------------------------------------------------------------------

/// Start a REPL over `root` as `main.rs` does: load the entry `user`, and
/// recover from the failed start when that fails. Returns the startup
/// report.
fn started_session(root: &Path) -> (CompilerSession, Option<String>) {
    let mut s = repl_session(root);
    let started = s
        .register_module("user")
        .and_then(|_| s.wait_inmem_complete().map_err(CranelispError::from));
    let report = match started {
        Ok(()) => None,
        Err(error) => recover(&mut s, "user", &error),
    };
    s.mark_entry_eval_owned();
    (s, report)
}

/// Recover from `error`, the failed start of `entry`, as `main.rs` does;
/// returns the startup report.
fn recover(s: &mut CompilerSession, entry: &str, error: &CranelispError) -> Option<String> {
    s.recover_startup_failure(entry, error)
        .report()
        .map(str::to_string)
}

/// Start a REPL over `root` as `main.rs` does and return its restore notice.
fn restore_notice_after_start(root: &Path) -> Option<String> {
    let mut s = repl_session(root);
    let started = s
        .register_module("user")
        .and_then(|_| s.wait_inmem_complete().map_err(CranelispError::from));
    let recovery = started
        .err()
        .map(|error| s.recover_startup_failure("user", &error));
    let notice = s.startup_restore_notice(&ModuleFullPath::from("user"), recovery.as_ref());
    s.shutdown();
    notice
}

fn write_files(root: &Path, files: &[(&str, &str)]) {
    for (name, text) in files {
        let path = root.join(name);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(path, text).unwrap();
    }
}

fn has_table(s: &CompilerSession, module: &str) -> bool {
    s.shared
        .symbol_tables
        .contains_key(&ModuleFullPath::from(module))
}

fn maps_file(s: &CompilerSession, file: &Path) -> bool {
    let canonical = file.canonicalize().unwrap();
    s.shared
        .file_to_module
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .contains_key(&canonical)
}

fn failure_dependencies_of(s: &CompilerSession, module: &str) -> Vec<String> {
    s.failure_dependencies
        .get(&ModuleFullPath::from(module))
        .map(|dependencies| dependencies.iter().map(|m| m.to_string()).collect())
        .unwrap_or_default()
}

/// The import chain `user` → `lib` → `base` whose `base` fails at startup.
const CHAIN_FAILING_BASE: &[(&str, &str)] = &[
    ("base.cl", "(defn b [] (undefined-name 1))\n"),
    ("lib.cl", "(import [base [b]])\n(defn f [] (b))\n"),
    ("user.cl", "(import [lib [f]])\n(defn g [] 1)\n"),
];

// spec: design/int/repl-lifecycle.md §1.3.1 (A failed load's record,
// Startup), §1.2.1 — recovery leaves no table for a dependency that never
// compiled while keeping it mapped for the watcher: `base`, which failed in
// its own source, stands failed and `lib`, refused through it, waits. The
// entry keeps a table and waits, and each module's failure dependency is
// recorded.
#[test]
fn startup_reset_purges_never_compiled_dependencies_and_records_their_failure_dependencies() {
    let root = tempfile::tempdir().unwrap();
    write_files(root.path(), CHAIN_FAILING_BASE);
    let (mut s, report) = started_session(root.path());
    assert!(
        report.is_some(),
        "precondition: the startup failure is reported"
    );

    for dependency in ["lib", "base"] {
        assert!(!has_table(&s, dependency), "`{dependency}` keeps no table");
        assert!(maps_file(&s, &root.path().join(format!("{dependency}.cl"))));
    }
    assert_eq!(lock_of(&s, "base"), Some(FailureCause::FailedSource));
    assert_eq!(lock_of(&s, "lib"), None, "`lib` waits");
    assert!(has_table(&s, "user"), "the entry keeps a table");
    assert_eq!(lock_of(&s, "user"), None, "the entry waits");
    assert_eq!(failure_dependencies_of(&s, "lib"), vec!["base"]);
    assert_eq!(failure_dependencies_of(&s, "user"), vec!["lib"]);
    assert_eq!(
        failure_dependencies_of(&s, "base"),
        vec!["prelude"],
        "`base` failed in its own source, which names only its implicit prelude"
    );
    s.shutdown();
}

/// Start a REPL over `user` → `lib` → `base` in which `lib` fails in its own
/// source against `base`, and return the session.
fn own_source_failure_session(root: &Path, base: &str, lib: &str) -> CompilerSession {
    write_files(
        root,
        &[
            ("base.cl", base),
            ("lib.cl", lib),
            ("user.cl", "(import [lib [f]])\n(defn g [] 1)\n"),
        ],
    );
    let (s, report) = started_session(root);
    assert!(
        report.is_some(),
        "precondition: the startup failure is reported"
    );
    assert!(!has_table(&s, "lib"), "precondition: recovery purged `lib`");
    s
}

const BASE_B: &str = "(defn b [] 1)\n";

/// `(base source, lib source)` pairs in which `lib` fails in its own source
/// against `base` at each stage of its attempt.
const OWN_SOURCE_FAILURES: &[(&str, &str, &str)] = &[
    (
        "Pass 0 import of a name `base` lacks",
        BASE_B,
        "(import [base [c]])\n(defn f [] 1)\n",
    ),
    (
        "Pass 0 export of a name `base` lacks",
        BASE_B,
        "(export [base [c]])\n(defn f [] 1)\n",
    ),
    (
        "Pass 1 expansion of a macro imported from `base`",
        "(defmacro m [x] x)\n",
        "(import [base [m]])\n(defn f [] (m))\n",
    ),
    (
        "type pass through an import",
        BASE_B,
        "(import [base [b]])\n(defn f [] (b 1))\n",
    ),
    (
        "type pass through a qualified reference",
        BASE_B,
        "(defn f [] (base/b 1))\n",
    ),
    (
        "type pass through an import alias",
        BASE_B,
        "(import [(base bs) []])\n(defn f [] (bs/b 1))\n",
    ),
    (
        "type pass on a reference only a macro's expansion wrote",
        BASE_B,
        "(defmacro call-b [] `(base/b 1))\n(defn f [] (call-b))\n",
    ),
    (
        "macro checkpoint's type pass",
        BASE_B,
        "(defmacro bad [] (let [v (base/b 1)] `1))\n(defn f [] 1)\n",
    ),
];

// spec: design/int/repl-lifecycle.md §1.2.1 (The attempt failure exit) — a
// failure of `lib` in its own source against `base`, at every stage of its
// attempt, leaves `base` in `lib`'s failure dependencies, and startup
// recovery carries them past the purge of `lib`'s table.
#[test]
fn own_source_failure_at_every_stage_records_the_dependency_it_failed_against() {
    let mut missing = Vec::new();
    for (stage, base, lib) in OWN_SOURCE_FAILURES {
        let root = tempfile::tempdir().unwrap();
        let mut s = own_source_failure_session(root.path(), base, lib);
        let recorded = failure_dependencies_of(&s, "lib");
        if !recorded.contains(&"base".to_string()) {
            missing.push(format!("{stage}: {recorded:?}"));
        }
        s.shutdown();
    }
    assert!(missing.is_empty(), "`base` not recorded: {missing:#?}");
}

// spec: design/int/repl-lifecycle.md §1.2.1 — a qualified symbol inside
// reader-quoted data is data, not a dependency.
#[test]
fn own_source_failure_does_not_record_a_module_named_only_in_quoted_data() {
    let root = tempfile::tempdir().unwrap();
    let mut s = own_source_failure_session(
        root.path(),
        BASE_B,
        "(defn f [] (let [q (quote base/b)] (nope)))\n",
    );
    assert!(
        !failure_dependencies_of(&s, "lib").contains(&"base".to_string()),
        "{:?}",
        failure_dependencies_of(&s, "lib")
    );
    s.shutdown();
}

// spec: design/int/repl-lifecycle.md §1.2.1 — an increment's failure changes
// nothing and records nothing.
#[test]
fn a_failed_increment_records_no_failure_dependency() {
    let root = tempfile::tempdir().unwrap();
    write_files(root.path(), &[("base.cl", BASE_B)]);
    let mut s = repl_session(root.path());
    assert!(s.eval("(defn k [] (base/b 1))").is_err());
    assert!(
        s.shared
            .scheduler
            .failure_dependencies(&ModuleFullPath::from("user"))
            .is_empty()
    );
    s.shutdown();
}

// spec: design/int/repl-lifecycle.md §1.2 (Guards), §1.2.1 — after startup
// recovery of `user` → `lib` → `base` with `lib` failing in its own source
// against `base`, in Pass 0 or in its type pass, a save of `base` selects
// `lib` and then `user`, and both recompile.
#[test]
fn dependency_save_selects_a_module_failed_against_it_in_its_own_source() {
    for (stage, lib, fixed_base) in [
        (
            "Pass 0",
            "(import [base [c]])\n(defn f [] (c))\n",
            "(defn c [] 2)\n",
        ),
        (
            "type pass",
            "(import [base [b]])\n(defn f [] (b 1))\n",
            "(defn b [x] x)\n",
        ),
    ] {
        let root = tempfile::tempdir().unwrap();
        let mut s = own_source_failure_session(root.path(), BASE_B, lib);
        let base_file = root.path().join("base.cl");
        std::fs::write(&base_file, fixed_base).unwrap();

        let outcomes = s.run_reload_plan(vec![(ModuleFullPath::from("base"), base_file)]);

        let order: Vec<&str> = outcomes.iter().map(|o| o.module.as_ref()).collect();
        let notices: Vec<String> = outcomes.iter().filter_map(|o| o.notice()).collect();
        assert_eq!(order, ["base", "lib", "user"], "{stage}: {notices:?}");
        assert!(
            outcomes.iter().all(|outcome| outcome.status.is_rebuilt()),
            "{stage}: {notices:?}"
        );
        s.shutdown();
    }
}

/// `b` calls `a/f`; the session loads both.
fn qualified_pair_session(root: &Path, b_source: &str) -> CompilerSession {
    write_files(root, &[("a.cl", "(defn f [] 1)\n"), ("b.cl", b_source)]);
    let mut s = repl_session(root);
    s.eval("(b/g)").unwrap();
    s.eval("(a/f)").unwrap();
    s
}

fn defines(s: &CompilerSession, module: &str, name: &str) -> bool {
    symbol_names(&table_of(s, module))
        .iter()
        .any(|defined| defined == name)
}

// spec: design/int/int.md §6.11 — an increment in `a` whose staged callee
// reaches `b`, while `b`'s live table reaches `a`, is refused naming
// `a -> b -> a` and leaves `a`'s table without it; the same turn is accepted
// when `b` does not reach `a`.
#[test]
fn increment_closing_a_qualified_cycle_is_refused_with_the_table_unchanged() {
    let root = tempfile::tempdir().unwrap();
    let mut s = qualified_pair_session(root.path(), "(defn g [] (a/f))\n");
    assert_eq!(s.handle_mod("a"), None);
    let error = s
        .eval("(defn h [] (b/g))")
        .err()
        .expect("the cyclic turn is refused")
        .to_string();
    assert!(
        error.contains("circular dependency detected: a -> b -> a"),
        "{error}"
    );
    assert!(!defines(&s, "a", "h"));
    s.shutdown();

    let control = tempfile::tempdir().unwrap();
    let mut s = qualified_pair_session(control.path(), "(defn g [] 3)\n");
    assert_eq!(s.handle_mod("a"), None);
    s.eval("(defn h [] (b/g))").unwrap();
    assert!(defines(&s, "a", "h"));
    s.shutdown();
}

/// A `defmacro` in `a` whose clause calls `b/g`.
const MACRO_CALLING_B: &str = "(defmacro m [] (let [v (b/g)] `1))";

// spec: design/int/int.md §6.11 (Where) — a macro checkpoint in `a` whose
// clause calls `b/g`, while `b`'s live table reaches `a`, is refused naming
// `a -> b -> a` and publishes no macro; the same checkpoint is accepted when
// `b` does not reach `a`.
#[test]
fn macro_checkpoint_closing_a_qualified_cycle_is_refused_and_publishes_nothing() {
    let root = tempfile::tempdir().unwrap();
    let mut s = qualified_pair_session(root.path(), "(defn g [] (a/f))\n");
    assert_eq!(s.handle_mod("a"), None);
    let error = s
        .eval(MACRO_CALLING_B)
        .err()
        .expect("the cyclic checkpoint is refused")
        .to_string();
    assert!(
        error.contains("circular dependency detected: a -> b -> a"),
        "{error}"
    );
    assert!(!defines(&s, "a", "m"));
    s.shutdown();

    let control = tempfile::tempdir().unwrap();
    let mut s = qualified_pair_session(control.path(), "(defn g [] 3)\n");
    assert_eq!(s.handle_mod("a"), None);
    s.eval(MACRO_CALLING_B).unwrap();
    assert!(defines(&s, "a", "m"));
    s.shutdown();
}

// spec: design/int/int.md §6.11 (Unsettled members) — a rebuild of `a` whose
// macro checkpoint calls `b/g` is accepted while `b`, whose pre-plan table
// still reaches `a`, is among the members the pass rebuilds later.
#[test]
fn macro_checkpoint_in_a_rebuild_skips_members_rebuilt_later() {
    let root = tempfile::tempdir().unwrap();
    let mut s = qualified_pair_session(root.path(), "(defn g [] (a/f))\n");
    let (a_file, b_file) = (root.path().join("a.cl"), root.path().join("b.cl"));
    std::fs::write(&a_file, format!("(defn f [] 1)\n{MACRO_CALLING_B}\n")).unwrap();
    std::fs::write(&b_file, "(defn g [] 3)\n").unwrap();

    let outcomes = s.run_reload_plan(vec![
        (ModuleFullPath::from("a"), a_file),
        (ModuleFullPath::from("b"), b_file),
    ]);

    let notices: Vec<String> = outcomes.iter().filter_map(|o| o.notice()).collect();
    assert!(
        outcomes.iter().all(|outcome| outcome.status.is_rebuilt()),
        "{notices:?}"
    );
    assert!(defines(&s, "a", "m"));
    s.shutdown();
}

// spec: design/int/repl-lifecycle.md §1.2 (Cycles), §1.3.1 — a plan whose root
// closes a qualified cycle ends with the refused member failed, naming the
// cycle, and the member that depends on it waiting, so the session is
// locked; its acyclic twin rebuilds every member.
#[test]
fn reload_plan_closing_a_qualified_cycle_fails_one_member_and_the_other_waits() {
    for (h_body, cyclic) in [("(b/g)", true), ("2", false)] {
        let root = tempfile::tempdir().unwrap();
        let mut s = qualified_pair_session(root.path(), "(defn g [] (a/f))\n");
        let a_file = root.path().join("a.cl");
        std::fs::write(&a_file, format!("(defn h [] {h_body})\n(defn f [] 5)\n")).unwrap();

        let outcomes = s.run_reload_plan(vec![(ModuleFullPath::from("a"), a_file)]);

        let notices: Vec<String> = outcomes.iter().filter_map(|o| o.notice()).collect();
        let failed: Vec<&str> = ["a", "b"]
            .into_iter()
            .filter(|member| stands_failed(&s, member))
            .collect();
        if cyclic {
            assert_eq!(failed.len(), 1, "{notices:?}");
            let waiting = if failed == ["a"] { "b" } else { "a" };
            assert_eq!(notice_of(&outcomes, waiting), None, "{notices:?}");
            assert!(
                notice_of(&outcomes, failed[0])
                    .is_some_and(|notice| notice.contains("circular dependency detected")),
                "{notices:?}"
            );
        } else {
            assert!(failed.is_empty(), "{notices:?}");
            assert!(
                outcomes.iter().all(|outcome| outcome.status.is_rebuilt()),
                "{notices:?}"
            );
        }
        s.shutdown();
    }
}

// spec: design/int/repl-lifecycle.md §1.2 (Cycles); design/int/int.md §6.11
// (Unsettled members) — two roots change together: `b` drops its reference to
// `a` and `a` adds one to `b`. The plan rebuilds `a` first, while `b`'s live
// table still holds its pre-plan edge to `a`; that edge does not refuse `a`,
// and both succeed.
#[test]
fn reload_plan_swapping_a_reference_between_two_roots_rebuilds_both() {
    let root = tempfile::tempdir().unwrap();
    let mut s = qualified_pair_session(root.path(), "(defn g [] (a/f))\n");
    let (a_file, b_file) = (root.path().join("a.cl"), root.path().join("b.cl"));
    std::fs::write(&b_file, "(defn g [] 2)\n").unwrap();
    std::fs::write(&a_file, "(defn f [] (b/g))\n").unwrap();

    let outcomes = s.run_reload_plan(vec![
        (ModuleFullPath::from("a"), a_file),
        (ModuleFullPath::from("b"), b_file),
    ]);

    assert!(
        outcomes.iter().all(|outcome| outcome.status.is_rebuilt()),
        "{:?}",
        outcomes
            .iter()
            .filter_map(|outcome| outcome.notice())
            .collect::<Vec<_>>()
    );
    assert_eq!(s.eval("(a/f)").unwrap().expect("a value").value(), 2);
    s.shutdown();
}

fn tables_held(s: &CompilerSession) -> std::collections::BTreeSet<String> {
    s.shared
        .symbol_tables
        .iter()
        .map(|entry| entry.key().to_string())
        .collect()
}

// spec: design/int/int.md §8.5.1 — `/mod` on a name with no module reports an
// error naming it and leaves the current module and the set of tables
// unchanged.
#[test]
fn mod_unknown_name_is_refused_leaving_module_and_tables_unchanged() {
    let root = tempfile::tempdir().unwrap();
    let mut s = repl_session(root.path());
    let before = tables_held(&s);

    let report = s.handle_mod("nonexistent");

    let Some(crate::repl::commands::ModReport::Refused(refusal)) = report else {
        panic!("the unknown module is refused: {report:?}");
    };
    assert!(
        refusal.contains("'nonexistent'") && refusal.contains("not found"),
        "{refusal}"
    );
    assert_eq!(s.current_module_path(), ModuleFullPath::from("user"));
    assert_eq!(tables_held(&s), before);
    s.shutdown();
}

// spec: design/int/int.md §8.5.1 — `/mod` on a module not yet loaded loads its
// file and switches to it, and the module's definitions resolve there.
#[test]
fn mod_loads_an_unloaded_file_backed_module_and_switches_to_it() {
    let root = tempfile::tempdir().unwrap();
    write_files(root.path(), &[("lib.cl", "(defn keep-me [] 42)\n")]);
    let mut s = repl_session(root.path());

    assert_eq!(s.handle_mod("lib"), None);

    assert_eq!(s.current_module_path(), ModuleFullPath::from("lib"));
    assert_eq!(s.eval("(keep-me)").unwrap().expect("a value").value(), 42);
    s.shutdown();
}

// spec: design/int/int.md §8.5.1; spec/08-modules.md §8.11.2.1 — from a
// module declaring `(mod y)`, `/mod y` targets the submodule even though a
// root `y.cl` exists; without the declaration it targets the root.
#[test]
fn mod_resolves_a_declared_submodule_over_a_root_module() {
    for (user, target) in [
        ("(mod y)\n(defn g [] 0)\n", "user.y"),
        ("(defn g [] 0)\n", "y"),
    ] {
        let root = tempfile::tempdir().unwrap();
        write_files(
            root.path(),
            &[
                ("y.cl", "(defn which [] 2)\n"),
                ("user/y.cl", "(defn which [] 1)\n"),
                ("user.cl", user),
            ],
        );
        let (mut s, report) = started_session(root.path());
        assert_eq!(report, None, "precondition: the entry loads");

        assert_eq!(s.handle_mod("y"), None);

        assert_eq!(s.current_module_path(), ModuleFullPath::from(target));
        s.shutdown();
    }
}

// spec: design/int/int.md §8.5.1 — `/mod` on a file that fails to compile
// reports its error, stays in the current module and leaves no table.
#[test]
fn mod_on_a_failing_file_reports_its_error_and_stays_put() {
    let root = tempfile::tempdir().unwrap();
    write_files(root.path(), &[("lib.cl", "(defn keep-me [] (nope))\n")]);
    let mut s = repl_session(root.path());

    let report = s.handle_mod("lib");

    let Some(crate::repl::commands::ModReport::Refused(refusal)) = report else {
        panic!("the failed load is reported: {report:?}");
    };
    assert!(refusal.contains("nope"), "{refusal}");
    assert_eq!(s.current_module_path(), ModuleFullPath::from("user"));
    assert!(!has_table(&s, "lib"));
    s.shutdown();
}

/// `mymod.cl` for a prelude that imports it: opted out of the implicit prelude
/// with a null import (spec §8.3.7), or carrying the fallback bit.
fn mymod_source(opted_out: bool) -> &'static str {
    if opted_out {
        "(import [prelude []])\n(defn val [] 42)\n"
    } else {
        "(defn val [] 42)\n"
    }
}

/// A session over a prelude that imports `mymod` and defines `two`; the
/// entry's turn importing `two` loads the prelude.
fn prelude_dependency_session(
    root: &Path,
    opted_out: bool,
) -> (CompilerSession, Result<(), CranelispError>) {
    write_files(
        root,
        &[
            (
                "prelude.cl",
                "(export [primitives [*]])\n(import [mymod [val]])\n(defn two [] 2)\n",
            ),
            ("mymod.cl", mymod_source(opted_out)),
        ],
    );
    let mut s = repl_session(root);
    let loaded = s.eval("(import [prelude [two]])").map(|_| ());
    (s, loaded)
}

// spec: spec/08-modules.md §8.8.1, §8.10.2; design/int/int.md §6.12 — a
// prelude importing a module with the fallback bit on closes a cycle through
// that module's implicit prelude dependency, which is refused.
#[test]
fn prelude_importing_a_module_with_the_fallback_bit_is_refused_as_a_cycle() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, loaded) = prelude_dependency_session(root.path(), false);
    let error = loaded
        .expect_err("the cyclic prelude is refused")
        .to_string();
    assert!(
        error.contains("circular dependency detected: prelude -> mymod -> prelude"),
        "{error}"
    );
    s.shutdown();
}

// spec: spec/08-modules.md §8.3.7; design/int/int.md §6.12 (face C, probes
// N2–N4) — with `mymod` opted out, the prelude publishing a definition while
// importing it is accepted, an increment in `mymod` is accepted, a save of
// `mymod` rebuilds it before the prelude, and a save of the prelude succeeds.
#[test]
fn opted_out_prelude_dependency_loads_accepts_increments_and_reloads() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, loaded) = prelude_dependency_session(root.path(), true);
    loaded.expect("the prelude and its opted-out import load");
    assert!(defines(&s, "prelude", "two"));

    assert_eq!(s.handle_mod("mymod"), None);
    s.eval("(defn z [] 1)").unwrap();
    assert!(defines(&s, "mymod", "z"));

    let mymod_file = root.path().join("mymod.cl");
    std::fs::write(&mymod_file, "(import [prelude []])\n(defn val [] 99)\n").unwrap();
    let outcomes = s.run_reload_plan(vec![(ModuleFullPath::from("mymod"), mymod_file)]);
    let notices: Vec<String> = outcomes.iter().filter_map(|o| o.notice()).collect();
    assert!(
        outcomes.iter().all(|outcome| outcome.status.is_rebuilt()),
        "{notices:?}"
    );
    let position = |module: &str| outcomes.iter().position(|o| o.module.as_ref() == module);
    assert!(
        position("mymod") < position("prelude") && position("prelude").is_some(),
        "{notices:?}"
    );

    let prelude_file = root.path().join("prelude.cl");
    let outcomes = s.run_reload_plan(vec![(ModuleFullPath::from("prelude"), prelude_file)]);
    let notices: Vec<String> = outcomes.iter().filter_map(|o| o.notice()).collect();
    assert!(
        outcomes.iter().all(|outcome| outcome.status.is_rebuilt()),
        "{notices:?}"
    );
    s.shutdown();
}

/// Whether `x` and the prelude each compiled: a table on a module that does
/// not stand `Failed`.
fn helper_and_prelude_standing(s: &CompilerSession) -> [(&'static str, bool); 2] {
    ["x", "prelude"].map(|module| {
        let compiled =
            has_table(s, module) && !s.shared.scheduler.is_failed(&ModuleFullPath::from(module));
        (module, compiled)
    })
}

/// One direction of the helper-end cycle: the files a session loads, the
/// saved module, the save that closes the cycle and the save that opens it.
struct HelperCycleLeg {
    prelude: &'static str,
    x: &'static str,
    saved: &'static str,
    closing: &'static str,
    restoring: &'static str,
}

impl HelperCycleLeg {
    /// The leg's failures against ACT-1014's condition: the closing save names
    /// the cycle and no unresolved name, and ends as a fresh session on the
    /// saved files; the restoring save is accepted.
    fn failures(&self) -> Vec<String> {
        let label = format!("{} saving {:?}", self.saved, self.closing);
        let root = tempfile::tempdir().unwrap();
        write_files(
            root.path(),
            &[("prelude.cl", self.prelude), ("x.cl", self.x)],
        );
        let file = root.path().join(format!("{}.cl", self.saved));
        let load = |s: &mut CompilerSession| {
            let _ = s.eval("(import [prelude [two]])");
            let _ = s.eval("(import [x [one]])");
        };
        let save = |s: &mut CompilerSession, source: &str| -> Vec<String> {
            std::fs::write(&file, source).unwrap();
            s.run_reload_plan(vec![(ModuleFullPath::from(self.saved), file.clone())])
                .iter()
                .filter_map(|outcome| outcome.notice())
                .collect()
        };

        let mut s = repl_session(root.path());
        load(&mut s);
        assert_eq!(
            helper_and_prelude_standing(&s),
            [("x", true), ("prelude", true)],
            "precondition: {label} starts acyclic"
        );
        let closed = save(&mut s, self.closing);
        let session_standing = helper_and_prelude_standing(&s);
        let restored = save(&mut s, self.restoring);
        s.shutdown();

        std::fs::write(&file, self.closing).unwrap();
        let mut restart = repl_session(root.path());
        load(&mut restart);
        let restart_standing = helper_and_prelude_standing(&restart);
        restart.shutdown();

        let mut failures = Vec::new();
        if restart_standing != [("x", true), ("prelude", false)] {
            failures.push(format!(
                "precondition: a restart on {label} refuses only the prelude, got {restart_standing:?}"
            ));
        }
        let names_the_cycle = closed.iter().any(|notice| {
            notice.contains("circular dependency detected: x -> prelude -> x")
                || notice.contains("circular dependency detected: prelude -> x -> prelude")
        });
        if !names_the_cycle || closed.iter().any(|n| n.contains("not found in module")) {
            failures.push(format!("{label}: closing save {closed:#?}"));
        }
        if session_standing != restart_standing {
            failures.push(format!(
                "{label}: session {session_standing:?}, restart {restart_standing:?}"
            ));
        }
        if !restored
            .iter()
            .all(|notice| notice.starts_with("[updated:"))
        {
            failures.push(format!("{label}: restoring save {restored:#?}"));
        }
        failures
    }
}

// spec: spec/08-modules.md §8.8.1, §8.10.2; repl/spec/14-file-watching.md
// §14.6; design/int/int.md §6.11 (Pass-0 fail-fast), §6.12 (the helper end,
// restart parity) — the prelude reaches `x` by `export` or by `x/one`, which
// the static gate does not follow. A save that closes the cycle through `x`'s
// implicit prelude edge, by dropping `x`'s opt-out or, in the twin direction,
// by adding the prelude's reach, names the cycle, reports no unresolved name
// and ends as a restart on the saved files does: `x` compiled and the prelude
// refused. The save that opens the cycle again is accepted.
#[test]
fn helper_save_dropping_its_prelude_opt_out_is_refused_as_a_cycle() {
    const X_OPTED_OUT: &str = "(import [prelude []])\n(defn one [] 1)\n";
    const X_WITH_BIT: &str = "(defn one [] 1)\n";
    const PRELUDE_ALONE: &str = "(defn two [] 2)\n";
    let mut failures = Vec::new();
    for reaching_prelude in [
        "(export [x [one]])\n(defn two [] 2)\n",
        "(defn two [] (x/one))\n",
    ] {
        let helper_end = HelperCycleLeg {
            prelude: reaching_prelude,
            x: X_OPTED_OUT,
            saved: "x",
            closing: X_WITH_BIT,
            restoring: X_OPTED_OUT,
        };
        let twin = HelperCycleLeg {
            prelude: PRELUDE_ALONE,
            x: X_WITH_BIT,
            saved: "prelude",
            closing: reaching_prelude,
            restoring: PRELUDE_ALONE,
        };
        failures.extend(helper_end.failures());
        failures.extend(twin.failures());
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

// ---------------------------------------------------------------------------
// Session lock (repl/spec/14-file-watching.md §14.5 (session lock);
// design/int/repl-lifecycle.md §1.2 Waiting, §1.3.1, §1.3.2)
// ---------------------------------------------------------------------------

/// Whether `module` stands failed (`design/int/repl-lifecycle.md` §1.3.1).
fn stands_failed(s: &CompilerSession, module: &str) -> bool {
    s.failed_modules.contains_key(&ModuleFullPath::from(module))
}

/// Whether the session is locked: some module stands failed.
fn session_locked(s: &CompilerSession) -> bool {
    s.is_locked()
}

/// The cause `module` stands failed with: `failed source`, or `restart: <type>`.
fn cause_of(s: &CompilerSession, module: &str) -> Option<String> {
    match lock_of(s, module)? {
        FailureCause::RestartRequired(type_name) => Some(format!("restart: {type_name}")),
        FailureCause::FailedSource => Some("failed source".to_string()),
    }
}

/// Make `module` stand failed with failed source, its file `file`.
fn plant_failed(s: &mut CompilerSession, module: &str, file: &Path) {
    s.stand_failed(
        &ModuleFullPath::from(module),
        file,
        FailureCause::FailedSource,
    );
}

/// Reload `user` from `path` alone; the module's own attempt.
fn reload_user(s: &mut CompilerSession, path: &Path) -> Result<(), CranelispError> {
    attempt(s.reload_module(
        &ModuleFullPath::from("user"),
        path,
        Default::default(),
        &Default::default(),
    ))
}

/// The notification `module`'s outcome prints, if it has one.
fn notice_of(outcomes: &[lifecycle::ReloadOutcome], module: &str) -> Option<String> {
    outcomes
        .iter()
        .find(|outcome| outcome.module.as_ref() == module)
        .and_then(|outcome| outcome.notice())
}

/// The error the scheduler holds `module` `Failed` with.
fn scheduler_error(s: &CompilerSession, module: &str) -> Option<String> {
    let module = ModuleFullPath::from(module);
    if !s.shared.scheduler.is_failed(&module) {
        return None;
    }
    match s
        .shared
        .scheduler
        .wait_module_inmem_complete_blocking(&module)
    {
        Err(crate::scheduler::SchedulerError::ModuleFailed { message, .. }) => Some(message),
        _ => None,
    }
}

fn refusing_dependency_of(s: &CompilerSession, module: &str) -> Option<String> {
    s.shared
        .scheduler
        .refusing_dependency(&ModuleFullPath::from(module))
        .map(|dependency| dependency.to_string())
}

/// Save `files` and run one reload plan rooted at them.
fn save_all(
    s: &mut CompilerSession,
    root: &Path,
    files: &[(&str, &str)],
) -> Vec<lifecycle::ReloadOutcome> {
    write_files(root, files);
    let roots = files
        .iter()
        .map(|(name, _)| {
            let module = name.trim_end_matches(".cl");
            (ModuleFullPath::from(module), root.join(name))
        })
        .collect();
    s.run_reload_plan(roots)
}

/// The text a command result displays, for assertion messages.
fn shown(result: &CommandResult) -> &str {
    match result {
        CommandResult::Final(text) | CommandResult::Compile(text) => text,
        _ => "",
    }
}

/// A refusal of a code turn: names each of `files` and the save remedy.
fn refusal_names(result: &CommandResult, files: &[&str]) -> bool {
    let CommandResult::Final(text) = result else {
        return false;
    };
    files.iter().all(|file| text.contains(file)) && text.to_lowercase().contains("save")
}

// spec: repl/spec/14-file-watching.md §14.2 step 2, §14.5 items 1–2;
// design/int/repl-lifecycle.md §1.3.2 (Rebuild, parse failure; ACT-1044) — a
// reload from a file that does not parse, or that cannot be read, keeps no
// record of the module's previous definitions, holds it `Failed` in the
// scheduler with that error and leaves it standing failed with failed source.
// The type-failure leg of
// `reload_replaces_declaration_records_and_failed_reload_clears_them` is the
// control.
#[test]
fn reload_that_cannot_parse_or_read_keeps_nothing_of_the_module() {
    type BreakFile = fn(&Path);
    let legs: [(&str, BreakFile); 2] = [
        ("parse", |path| {
            std::fs::write(path, "(defn sq [x] x\n").unwrap()
        }),
        ("read", |path| std::fs::remove_file(path).unwrap()),
    ];
    for (leg, break_file) in legs {
        let root = tempfile::tempdir().unwrap();
        let (mut s, path) = rebuild_session(root.path(), "(defn sq [x] x)\n");
        assert!(
            table_of(&s, "user").get("sq").is_some() && record_of(&s, "user", "sq").is_some(),
            "{leg}: precondition"
        );

        break_file(&path);
        let error = reload_user(&mut s, &path).expect_err(leg).to_string();

        assert!(table_of(&s, "user").get("sq").is_none(), "{leg}: binding");
        assert!(record_of(&s, "user", "sq").is_none(), "{leg}: record");
        let held = scheduler_error(&s, "user");
        assert!(
            held.as_deref().is_some_and(|held| held.contains(&error)),
            "{leg}: the scheduler holds `user` Failed with {error:?}, got {held:?}"
        );
        assert_eq!(
            cause_of(&s, "user").as_deref(),
            Some("failed source"),
            "{leg}"
        );
        s.shutdown();
    }
}

/// `math` and its dependents: `mid` imports `sq`, `q` calls `math/sq` by a
/// qualified reference only, and the entry `user` imports both; `z` is
/// unrelated.
const WAIT_FILES: &[(&str, &str)] = &[
    ("math.cl", "(defn sq [x] x)\n"),
    ("mid.cl", "(import [math [sq]])\n(defn m [] (sq 3))\n"),
    ("q.cl", "(defn qq [] (math/sq 4))\n"),
    ("z.cl", "(defn zz [] 1)\n"),
    (
        "user.cl",
        "(import [mid [m]])\n(import [q [qq]])\n(import [z [zz]])\n(defn g [] 1)\n",
    ),
];
const MATH_BROKEN: &str = "(defn sq [x] (nope x))\n";

fn wait_session(root: &Path) -> CompilerSession {
    write_files(root, WAIT_FILES);
    let (s, report) = started_session(root);
    assert_eq!(report, None, "precondition: the session starts");
    s
}

// spec: repl/spec/14-file-watching.md §14.2 step 4, §14.5 (session lock);
// design/int/repl-lifecycle.md §1.2 (Waiting, before its attempt), §1.3.2 —
// after `math` fails, the plan members that reach it and are not roots, by
// import, by a qualified reference or transitively, are not attempted: each
// holds a fresh table, the scheduler holds it `Failed` with `math` as its
// refusing dependency, `math` is among its failure dependencies, it does not
// stand failed and it has no notification. An unrelated root of the same plan
// rebuilds. Once `math` compiles, the waiting modules rebuild after it in the
// same pass, each notifying `[updated:]`, and the session unlocks.
#[test]
fn dependents_of_a_failed_module_wait_unattempted_until_it_compiles() {
    let root = tempfile::tempdir().unwrap();
    let mut s = wait_session(root.path());

    let outcomes = save_all(
        &mut s,
        root.path(),
        &[("math.cl", MATH_BROKEN), ("z.cl", "(defn zz [] 2)\n")],
    );

    assert!(
        notice_of(&outcomes, "math").is_some_and(|n| n.starts_with("[errors: math.cl]")),
        "{:?}",
        notice_of(&outcomes, "math")
    );
    assert_eq!(
        notice_of(&outcomes, "z").as_deref(),
        Some("[updated: z.cl]")
    );
    for (module, defined) in [("mid", "m"), ("q", "qq"), ("user", "g")] {
        assert_eq!(
            notice_of(&outcomes, module),
            None,
            "`{module}` is not reported"
        );
        assert!(
            table_of(&s, module).get(defined).is_none(),
            "`{module}` holds a fresh table"
        );
        assert!(
            !stands_failed(&s, module),
            "`{module}` does not stand failed"
        );
        assert_eq!(
            refusing_dependency_of(&s, module).as_deref(),
            Some("math"),
            "`{module}`'s refusing dependency"
        );
        assert!(
            failure_dependencies_of(&s, module).contains(&"math".to_string()),
            "`{module}`'s failure dependencies"
        );
    }
    assert!(stands_failed(&s, "math") && session_locked(&s));

    let outcomes = save_all(
        &mut s,
        root.path(),
        &[("math.cl", "(defn sq [x] (primitives/add-i64 x x))\n")],
    );

    let order: Vec<&str> = outcomes.iter().map(|o| o.module.as_ref()).collect();
    let position = |module: &str| order.iter().position(|m| *m == module).unwrap();
    for module in ["mid", "q", "user"] {
        assert_eq!(
            notice_of(&outcomes, module),
            Some(format!("[updated: {module}.cl]")),
            "{order:?}"
        );
        assert!(position("math") < position(module), "{order:?}");
    }
    assert!(!session_locked(&s));
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock);
// design/int/repl-lifecycle.md §1.2 (Waiting, at its attempt), §1.3.2 — a saved
// root whose source still imports a module standing failed is attempted,
// waits and leaves the failed set it stood in; a saved root whose source drops
// that import rebuilds.
#[test]
fn saved_root_still_importing_a_failed_module_waits_and_dropping_the_import_rebuilds() {
    let root = tempfile::tempdir().unwrap();
    let mut s = wait_session(root.path());
    save_all(&mut s, root.path(), &[("math.cl", MATH_BROKEN)]);
    save_all(&mut s, root.path(), &[("mid.cl", "(defn m [] (nope))\n")]);
    assert!(
        stands_failed(&s, "mid"),
        "precondition: `mid` stands failed"
    );

    let outcomes = save_all(
        &mut s,
        root.path(),
        &[("mid.cl", "(import [math [sq]])\n(defn m [] (sq 3))\n")],
    );

    assert_eq!(
        notice_of(&outcomes, "mid"),
        None,
        "the waiting root is not reported"
    );
    assert!(!stands_failed(&s, "mid"), "it leaves the failed set");
    assert_eq!(refusing_dependency_of(&s, "mid").as_deref(), Some("math"));

    let outcomes = save_all(&mut s, root.path(), &[("mid.cl", "(defn m [] 3)\n")]);
    assert_eq!(
        notice_of(&outcomes, "mid").as_deref(),
        Some("[updated: mid.cl]")
    );
    assert!(
        stands_failed(&s, "math"),
        "control: `math` still stands failed"
    );
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock), §14.8;
// design/int/repl-lifecycle.md §1.3.1 (Status is the last attempt), §1.3.2 — a
// parse failure after a §14.8 refusal records failed source, the refusal
// returns with its type once the file parses again, and a successful reload
// removes the module's entry.
#[test]
fn each_attempt_sets_the_failure_cause_from_its_own_outcome() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = session_with_live_type(root.path());

    assert!(!save_and_reload(&mut s, &path, TYPE_STRUCTURAL));
    assert_eq!(cause_of(&s, "user").as_deref(), Some("restart: user/T"));
    assert!(!save_and_reload(&mut s, &path, TYPE_PARSE_ERROR));
    assert_eq!(cause_of(&s, "user").as_deref(), Some("failed source"));
    assert!(!save_and_reload(&mut s, &path, TYPE_STRUCTURAL));
    assert_eq!(cause_of(&s, "user").as_deref(), Some("restart: user/T"));
    assert!(save_and_reload(&mut s, &path, TYPE_V1));
    assert_eq!(cause_of(&s, "user"), None);
    assert!(!session_locked(&s));
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock), §14.6 — the lock
// holds until no module stands failed: with two siblings failed, a fix of one
// keeps the session locked and the refusal names only the other's file; the
// second fix releases it.
#[test]
fn session_lock_holds_until_every_failed_module_reloads() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, _lib, siblings) = session_with_siblings(root.path(), 2);
    fail_siblings(&mut s, &siblings);

    let refused = s.process_commands("(defn h [] 2)", &mut Vec::new());
    assert!(
        refusal_names(&refused, &["sib0.cl", "sib1.cl"]),
        "{}",
        shown(&refused)
    );

    assert!(save_and_reload(&mut s, &siblings[0], SIBLING_V1));
    let refused = s.process_commands("(defn h [] 2)", &mut Vec::new());
    assert!(refusal_names(&refused, &["sib1.cl"]), "{}", shown(&refused));
    assert!(
        matches!(&refused, CommandResult::Final(text) if !text.contains("sib0.cl")),
        "{}",
        shown(&refused)
    );

    assert!(save_and_reload(&mut s, &siblings[1], SIBLING_V1));
    assert!(!session_locked(&s));
    assert!(matches!(
        s.process_commands("(defn h [] 2)", &mut Vec::new()),
        CommandResult::Compile(_)
    ));
    s.shutdown();
}

// spec: repl/spec/15-session-persistence.md §15.1; repl/spec/14-file-watching.md
// §14.5 (session lock); design/int/repl-lifecycle.md §1.3.2 (Chokepoint) —
// while any module stands failed, regeneration writes nothing, for a current
// module that does not stand failed.
#[test]
fn regeneration_writes_nothing_while_another_module_stands_failed() {
    let (mut s, root) = session_with_backing(false);
    plant_failed(&mut s, "lib", &root.join("lib.cl"));
    assert!(!stands_failed(&s, "user"), "precondition");

    s.regenerate_backing_file();

    let after = std::fs::read_to_string(root.join("user.cl")).expect("backing file present");
    let _ = std::fs::remove_dir_all(&root);
    assert_eq!(after, BACKING);
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock),
// repl/spec/03-slash-commands.md §3.9; design/int/repl-lifecycle.md §1.3.1 (A
// failed load's record), §1.3.2 (Load reset) — a failed `/mod` load while
// `math` stands failed resets only the modules the load left `Failed`: `math`
// stays `Failed` in the scheduler and the failed target stands failed.
#[test]
fn failed_mod_load_resets_only_what_the_load_left_failed() {
    let root = tempfile::tempdir().unwrap();
    let mut s = wait_session(root.path());
    save_all(&mut s, root.path(), &[("math.cl", MATH_BROKEN)]);
    write_files(root.path(), &[("bad.cl", "(defn x [] (nope))\n")]);

    assert!(matches!(
        s.handle_mod("bad"),
        Some(crate::repl::commands::ModReport::Refused(_))
    ));

    assert!(s.shared.scheduler.is_failed(&ModuleFullPath::from("math")));
    assert!(
        s.shared.scheduler.is_failed(&ModuleFullPath::from("mid")),
        "a waiting module"
    );
    assert!(stands_failed(&s, "bad") && stands_failed(&s, "math"));
    s.shutdown();
}

// spec: repl/spec/03-slash-commands.md §3.9; repl/spec/14-file-watching.md
// §14.5 (session lock); design/int/repl-lifecycle.md §1.3.2 (`/mod` load) — a
// `/mod` target failing in its own source stands failed, leaves no table and
// leaves the active module unchanged; a target importing a module standing
// failed waits. A code turn importing a failing module while the session is
// unlocked records nothing.
#[test]
fn mod_load_failure_stands_failed_or_waits_and_a_code_turn_records_nothing() {
    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[
            ("bad.cl", "(defn x [] (nope))\n"),
            ("base.cl", "(defn b [] (nope))\n"),
            ("over.cl", "(import [base [b]])\n(defn o [] (b))\n"),
        ],
    );
    let mut s = repl_session(root.path());

    assert!(s.eval("(import [bad [x]])").is_err());
    assert!(!session_locked(&s), "a code turn locks nothing");
    assert!(!s.shared.scheduler.is_failed(&ModuleFullPath::from("bad")));
    assert!(failure_dependencies_of(&s, "user").is_empty());

    assert!(s.handle_mod("bad").is_some());
    assert!(stands_failed(&s, "bad"), "the target stands failed");
    assert!(!has_table(&s, "bad"));
    assert_eq!(s.current_module_path(), ModuleFullPath::from("user"));

    assert!(s.handle_mod("base").is_some());
    assert!(s.handle_mod("over").is_some());
    assert!(stands_failed(&s, "base"));
    assert!(!stands_failed(&s, "over"), "`over` waits on `base`");
    assert!(failure_dependencies_of(&s, "over").contains(&"base".to_string()));
    assert_eq!(s.current_module_path(), ModuleFullPath::from("user"));
    s.shutdown();
}

/// An entry `user` that imports `f` from `lib` and defines `good`.
const STARTUP_USER: &str = "(import [lib [f]])\n(defn good [] 10)\n(defn g [] (f))\n";

// spec: repl/spec/15-session-persistence.md §15.2.3; repl/spec/14-file-watching.md
// §14.5 (session lock); design/int/repl-lifecycle.md §1.3.1 (Startup), §1.3.2
// (a) — an entry that fails at startup in its own source stands failed with
// no definition, its green `good` included: there is no form-by-form repair.
// It is terminal and eval-owned, and the report holds `[errors: user.cl]` and
// the error. A cache-preloaded table cannot accompany this start, because the
// changed dependency invalidates the entry's cache entry; the displacement of
// a populated entry table is
// `worker::tests::startup_recovery_of_an_uncompiled_entry_keeps_its_got_and_no_definition`.
#[test]
fn startup_entry_type_failure_stands_failed_holding_no_definition() {
    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[("lib.cl", "(defn other [] 1)\n"), ("user.cl", STARTUP_USER)],
    );
    let (mut s, report) = started_session(root.path());

    assert!(stands_failed(&s, "user"));
    let table = table_of(&s, "user");
    assert!(
        table.get("good").is_none() && table.get("g").is_none(),
        "{:?}",
        symbol_names(&table)
    );
    assert_eq!(
        s.shared
            .scheduler
            .module_pool(&ModuleFullPath::from("user")),
        Some(crate::scheduler::ModulePool::TypecheckDone),
        "terminal and eval-owned"
    );
    let report = report.expect("the failure is reported");
    assert!(
        report.starts_with("[errors: user.cl]") && report.contains('f'),
        "{report}"
    );
    s.shutdown();
}

// spec: repl/spec/15-session-persistence.md §15.2.3; design/int/repl-lifecycle.md
// §1.3.2 Startup (b) — an entry file that does not parse stands failed with the
// parse error, and a refused definition leaves the file unchanged.
#[test]
fn startup_unparsable_entry_stands_failed_and_keeps_its_file() {
    let root = tempfile::tempdir().unwrap();
    write_files(root.path(), &[("user.cl", TYPE_PARSE_ERROR)]);
    let (mut s, report) = started_session(root.path());

    assert!(stands_failed(&s, "user"));
    let report = report.expect("the parse failure is reported");
    assert!(report.starts_with("[errors: user.cl]"), "{report}");
    let refused = s.process_commands("(defn h [] 2)", &mut Vec::new());
    assert!(refusal_names(&refused, &["user.cl"]), "{}", shown(&refused));
    s.regenerate_backing_file();
    assert_eq!(
        std::fs::read_to_string(root.path().join("user.cl")).unwrap(),
        TYPE_PARSE_ERROR
    );
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock: dependents of a
// module that failed at startup wait); design/int/repl-lifecycle.md §1.3.2
// Startup (c) — a dependency failing at startup stands failed, and the entry
// waits, holding it as a failure dependency; only the dependency is reported.
#[test]
fn startup_failing_dependency_stands_failed_and_the_entry_waits() {
    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[
            ("lib.cl", "(defn f [] (nope))\n"),
            ("user.cl", STARTUP_USER),
        ],
    );
    let (mut s, report) = started_session(root.path());

    assert!(stands_failed(&s, "lib"));
    assert!(!stands_failed(&s, "user"), "the entry waits");
    assert!(failure_dependencies_of(&s, "user").contains(&"lib".to_string()));
    let report = report.expect("the dependency's failure is reported");
    assert!(report.starts_with("[errors: lib.cl]"), "{report}");
    assert!(!report.contains("user.cl"), "{report}");
    let refused = s.process_commands("(defn h [] 2)", &mut Vec::new());
    assert!(refusal_names(&refused, &["lib.cl"]), "{}", shown(&refused));
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock);
// spec/08-modules.md §8.5.4 edge 6; design/int/repl-lifecycle.md §1.3.2
// Startup (d) — a startup qualified cycle leaves the refused member standing
// failed with the circular-dependency error, and the other member waits.
#[test]
fn startup_cycle_leaves_the_refused_member_failed_and_the_other_waiting() {
    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[
            ("a.cl", "(defn f [] (b/g))\n"),
            ("b.cl", "(defn g [] (a/f))\n"),
            (
                "user.cl",
                "(import [primitives [Pure]])\n(defn main [] (Pure (a/f)))\n",
            ),
        ],
    );
    let (mut s, report) = started_session(root.path());

    let report = report.expect("the failed start is reported");
    assert!(report.contains("circular dependency detected"), "{report}");
    let failed: Vec<&str> = ["a", "b"]
        .into_iter()
        .filter(|module| stands_failed(&s, module))
        .collect();
    assert_eq!(failed.len(), 1, "one refused member: {failed:?}\n{report}");
    let waiting = if failed == ["a"] { "b" } else { "a" };
    assert!(
        !failure_dependencies_of(&s, waiting).is_empty(),
        "`{waiting}` waits"
    );
    assert!(!stands_failed(&s, "user"), "the entry waits");
    assert!(!report.contains("in-memory codegen incomplete"), "{report}");
    s.shutdown();
}

// spec: repl/spec/15-session-persistence.md §15.2.2, §15.2.3;
// design/int/repl-lifecycle.md §1.3.1 (Startup, Restore notice), §1.3.2
// Startup (e) — there is no restore notice when the entry did not compile; an
// entry that compiles counts its file's definitions.
#[test]
fn startup_restore_notice_is_emitted_only_when_the_entry_compiled() {
    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[("user.cl", "(defn good [] 1)\n(defn broken [] (nope))\n")],
    );
    assert_eq!(restore_notice_after_start(root.path()), None);

    let control = tempfile::tempdir().unwrap();
    write_files(
        control.path(),
        &[("user.cl", "(defn good [] 1)\n(defn other [] 2)\n")],
    );
    assert_eq!(
        restore_notice_after_start(control.path()).as_deref(),
        Some("; resumed 2 definitions from user.cl")
    );
}

// ---------------------------------------------------------------------------
// Review rulings (design/int/repl-lifecycle.md §1.2 Waiting, Refused by a
// later member; §1.3.1 Set sites, A failed load's record; design/int/int.md
// §6.12 Refusal by a failed prelude)
// ---------------------------------------------------------------------------

/// A project prelude defining `inc1`, an entry and a library `lib2` that use
/// it through the fallback bit, and an explicit-import pair `ctl` → `base`.
const PRELUDE_FILES: &[(&str, &str)] = &[
    ("prelude.cl", "(defn inc1 [x] (primitives/add-i64 x 1))\n"),
    ("lib2.cl", "(defn k [] (inc1 2))\n"),
    ("base.cl", "(defn b [] 1)\n"),
    ("ctl.cl", "(import [base [b]])\n(defn c [] (b))\n"),
    (
        "user.cl",
        "(import [lib2 [k]])\n(import [ctl [c]])\n(defn g [] (inc1 1))\n",
    ),
];
const PRELUDE_FIXED: &str = "(defn inc1 [x] (primitives/add-i64 x 2))\n";

/// Every module the scheduler holds `Failed` stands failed or waits on a
/// refusing dependency: the failed set accounts for it.
fn scheduler_failures_accounted(s: &CompilerSession) -> bool {
    s.shared.scheduler.failed_modules().iter().all(|module| {
        s.failed_modules.contains_key(module)
            || s.shared.scheduler.refusing_dependency(module).is_some()
    })
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock), spec/08-modules.md
// §8.8.1; design/int/repl-lifecycle.md §1.2 (Waiting), §1.3.2 (Failing
// prelude) — a save of the project prelude that fails to parse, and
// separately to typecheck, leaves every module with the fallback bit on
// waiting: not reported, not standing failed, refused by the prelude; only
// the prelude stands failed. The prelude's compiling save rebuilds them. The
// control is the same shape through an explicit import: `base` failing leaves
// `ctl` waiting.
#[test]
fn failing_prelude_leaves_its_implicit_dependents_waiting() {
    for broken in [
        "(defn inc1 [x] (primitives/add-i64 x 1)\n",
        "(defn inc1 [x] (primitives/add-i64 x \"a\"))\n",
    ] {
        let root = tempfile::tempdir().unwrap();
        write_files(root.path(), PRELUDE_FILES);
        let (mut s, report) = started_session(root.path());
        assert_eq!(report, None, "precondition: the session starts");

        let outcomes = save_all(&mut s, root.path(), &[("prelude.cl", broken)]);

        let notices: Vec<String> = outcomes.iter().filter_map(|o| o.notice()).collect();
        assert_eq!(notices.len(), 1, "{broken}: {notices:?}");
        assert!(
            notices[0].starts_with("[errors: prelude.cl]"),
            "{notices:?}"
        );
        for module in ["lib2", "user"] {
            assert!(!stands_failed(&s, module), "{broken}: `{module}` waits");
            assert_eq!(
                refusing_dependency_of(&s, module).as_deref(),
                Some("prelude"),
                "{broken}: `{module}`"
            );
        }
        let refused = s.process_commands("(defn h [] 2)", &mut Vec::new());
        assert!(
            refusal_names(&refused, &["prelude.cl"]),
            "{}",
            shown(&refused)
        );
        assert!(!shown(&refused).contains("user.cl"), "{}", shown(&refused));
        assert!(scheduler_failures_accounted(&s));

        let outcomes = save_all(&mut s, root.path(), &[("prelude.cl", PRELUDE_FIXED)]);
        for module in ["prelude", "lib2", "user"] {
            assert_eq!(
                notice_of(&outcomes, module),
                Some(format!("[updated: {module}.cl]")),
                "{broken}"
            );
        }
        assert!(!session_locked(&s), "{broken}");
        s.shutdown();
    }

    let root = tempfile::tempdir().unwrap();
    write_files(root.path(), PRELUDE_FILES);
    let (mut s, _) = started_session(root.path());
    let outcomes = save_all(&mut s, root.path(), &[("base.cl", "(defn b [] 1\n")]);
    assert_eq!(notice_of(&outcomes, "ctl"), None, "control: `ctl` waits");
    assert_eq!(refusing_dependency_of(&s, "ctl").as_deref(), Some("base"));
    assert!(stands_failed(&s, "base") && !stands_failed(&s, "ctl"));
    s.shutdown();
}

// spec: spec/08-modules.md §8.8.1; design/int/int.md §6.12 (Refusal by a
// failed prelude); design/int/repl-lifecycle.md §1.3.2 (Injection refusal) — a
// module with the fallback bit on, attempted while the prelude stands
// `Failed`, is refused with the prelude as its refusing dependency: a saved
// root at a reload, and a fresh `/mod` load. A module that opts out with a null
// import is not refused.
#[test]
fn injection_refuses_a_module_with_the_bit_on_while_the_prelude_stands_failed() {
    let root = tempfile::tempdir().unwrap();
    write_files(root.path(), PRELUDE_FILES);
    write_files(
        root.path(),
        &[
            ("fresh.cl", "(defn fr [] (inc1 3))\n"),
            ("opt.cl", "(import [prelude []])\n(defn o [] 1)\n"),
        ],
    );
    let (mut s, _) = started_session(root.path());
    save_all(
        &mut s,
        root.path(),
        &[("prelude.cl", "(defn inc1 [x] (primitives/add-i64 x 1)\n")],
    );

    let outcomes = save_all(
        &mut s,
        root.path(),
        &[("lib2.cl", "(defn k [] (inc1 5))\n")],
    );
    assert_eq!(notice_of(&outcomes, "lib2"), None, "the saved root waits");
    assert_eq!(
        refusing_dependency_of(&s, "lib2").as_deref(),
        Some("prelude")
    );
    assert!(!stands_failed(&s, "lib2"));

    assert!(s.handle_mod("fresh").is_some(), "the fresh load is refused");
    assert!(!stands_failed(&s, "fresh"), "`fresh` waits");
    assert!(failure_dependencies_of(&s, "fresh").contains(&"prelude".to_string()));

    assert_eq!(s.handle_mod("opt"), None, "the null-importing module loads");
    assert_eq!(s.current_module_path(), ModuleFullPath::from("opt"));
    s.shutdown();
}

/// `a` and `b`, both imported by the entry.
const TWO_ROOT_FILES: &[(&str, &str)] = &[
    ("a.cl", "(defn ax [] 1)\n"),
    ("b.cl", "(defn bx [] 2)\n"),
    (
        "user.cl",
        "(import [a [ax]])\n(import [b [bx]])\n(defn g [] (primitives/add-i64 (ax) (bx)))\n",
    ),
];
const A_IMPORTING_B: &str = "(import [b [bx]])\n(defn ax [] (bx))\n";

// spec: repl/spec/14-file-watching.md §14.5 (session lock), §14.6;
// design/int/repl-lifecycle.md §1.2 (Refused by a later member), §1.3.2 — with
// `b` failed, one pass whose save repairs `b` while `a` newly imports it ends
// with both rebuilt and the session unlocked, as a restart on those files
// does. Twin: when `b` still fails, `a` waits and only `b` stands failed.
#[test]
fn a_member_refused_by_a_later_member_is_settled_by_that_member() {
    for (b_saved, repaired) in [("(defn bx [] 2)\n", true), ("(defn bx [] (nope))\n", false)] {
        let root = tempfile::tempdir().unwrap();
        write_files(root.path(), TWO_ROOT_FILES);
        let (mut s, _) = started_session(root.path());
        save_all(&mut s, root.path(), &[("b.cl", "(defn bx [] (nope))\n")]);
        assert!(stands_failed(&s, "b"), "precondition");

        let outcomes = save_all(
            &mut s,
            root.path(),
            &[("a.cl", A_IMPORTING_B), ("b.cl", b_saved)],
        );

        let notices: Vec<String> = outcomes.iter().filter_map(|o| o.notice()).collect();
        if repaired {
            for module in ["a", "b", "user"] {
                assert_eq!(
                    notice_of(&outcomes, module),
                    Some(format!("[updated: {module}.cl]")),
                    "{notices:?}"
                );
            }
            assert!(!session_locked(&s), "{notices:?}");
        } else {
            assert_eq!(notice_of(&outcomes, "a"), None, "{notices:?}");
            assert!(!stands_failed(&s, "a"), "`a` waits: {notices:?}");
            assert_eq!(
                s.failed_modules
                    .keys()
                    .map(|m| m.to_string())
                    .collect::<Vec<_>>(),
                ["b"],
                "{notices:?}"
            );
        }
        assert!(scheduler_failures_accounted(&s), "{notices:?}");
        s.shutdown();
    }
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock);
// design/int/repl-lifecycle.md §1.3.1 (Set sites, Invariants), §1.3.2 (Newly
// loaded failure) — a reload of `user` whose new import loads `n`, failing in
// its own source, leaves `n` standing failed with `n.cl`, reported as a failed
// module (§1.4), and `user` waiting. A
// later save of `user` dropping the import rebuilds `user` and leaves `n`
// standing failed, so the session stays locked naming `n.cl`; `n`'s compiling
// save releases it. The failed set accounts for every module the scheduler
// holds `Failed` at each step.
#[test]
fn a_newly_loaded_failing_module_stands_failed_and_its_importer_waits() {
    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[
            ("n.cl", "(defn nx [] (nope))\n"),
            ("user.cl", "(defn g [] 1)\n"),
        ],
    );
    let (mut s, _) = started_session(root.path());

    let outcomes = save_all(
        &mut s,
        root.path(),
        &[("user.cl", "(import [n [nx]])\n(defn g [] 1)\n")],
    );
    assert_eq!(notice_of(&outcomes, "user"), None, "`user` waits");
    assert!(
        notice_of(&outcomes, "n").is_some_and(|notice| notice.starts_with("[errors: n.cl]")),
        "the newly loaded module is reported: {:?}",
        notice_of(&outcomes, "n")
    );
    assert_eq!(cause_of(&s, "n").as_deref(), Some("failed source"));
    assert!(!stands_failed(&s, "user"));
    let refused = s.process_commands("(g)", &mut Vec::new());
    assert!(refusal_names(&refused, &["n.cl"]), "{}", shown(&refused));
    assert!(scheduler_failures_accounted(&s));

    let outcomes = save_all(&mut s, root.path(), &[("user.cl", "(defn g [] 1)\n")]);
    assert_eq!(
        notice_of(&outcomes, "user").as_deref(),
        Some("[updated: user.cl]")
    );
    assert!(stands_failed(&s, "n") && session_locked(&s));
    assert!(scheduler_failures_accounted(&s));

    let outcomes = save_all(&mut s, root.path(), &[("n.cl", "(defn nx [] 5)\n")]);
    assert_eq!(
        notice_of(&outcomes, "n").as_deref(),
        Some("[updated: n.cl]")
    );
    assert!(!session_locked(&s));
    assert!(scheduler_failures_accounted(&s));
    s.shutdown();
}

// spec: design/int/repl-lifecycle.md §1.3.1 (A failed load's record, step 3),
// §1.3.2 (Record order) — the record over the same reset modules in either
// order gives the same failed set when one module is refused through a module
// whose refusal chain is broken: both stand failed, since a broken chain
// grounds no wait.
#[test]
fn failed_load_record_does_not_depend_on_reset_order() {
    let reset = |module: &str, refusing: Option<&str>| crate::scheduler::ResetModule {
        module: ModuleFullPath::from(module),
        failure_dependencies: Default::default(),
        refusing_dependency: refusing.map(ModuleFullPath::from),
        error: Some(CranelispError::ModuleError {
            message: format!("{module} failed"),
            location: cranelisp_types::ErrorLocation::from_span(cranelisp_types::Span::SYNTHETIC),
        }),
    };
    let mut results = Vec::new();
    for order in [["z", "y"], ["y", "z"]] {
        let root = tempfile::tempdir().unwrap();
        let mut s = repl_session(root.path());
        let mut modules: Vec<_> = order
            .iter()
            .map(|module| match *module {
                "z" => reset("z", Some("gone")),
                _ => reset("y", Some("z")),
            })
            .collect();
        s.record_failed_load(&mut modules);
        results.push(
            s.failed_modules
                .keys()
                .map(|m| m.to_string())
                .collect::<Vec<_>>(),
        );
        s.shutdown();
    }
    assert_eq!(results[0], results[1]);
    assert_eq!(results[0], ["y", "z"]);
}

// ---------------------------------------------------------------------------
// A dependency that fails before it registers (PF-1), the report of a newly
// loaded failure (LQ-4) and an unreadable entry (ACT-1019)
// (design/int/repl-lifecycle.md §1.2 Three outcomes, §1.3.1; design/int/int.md
// §6.1.1)
// ---------------------------------------------------------------------------

/// Bytes that are not UTF-8, so the file cannot be read as source.
const NOT_UTF8: &[u8] = b"(defn g [] \xff\xfe)\n";

// spec: design/int/repl-lifecycle.md §1.3.1 (A dependency that fails before it
// registers), §1.3.2 (Pre-registration failure) — a dependency whose file does
// not parse, loaded through an `import`, a qualified reference, a declared
// `mod` child and the prelude injection, is held `Failed` with its parse error
// located in its own file, and the loader's attempt is refused with it as its
// refusing dependency. A read failure takes the same path; the type twin, which
// registers and fails in its own pass, is classified alike.
#[test]
fn a_dependency_failing_before_it_registers_is_failed_and_refuses_its_loader() {
    const UNPARSEABLE: &str = "(defn x [] 1\n";
    /// A leg's name, its files, the failing dependency and its file.
    type Leg<'a> = (&'a str, &'a [(&'a str, &'a str)], &'a str, &'a str);
    let legs: &[Leg] = &[
        (
            "import",
            &[
                ("n.cl", UNPARSEABLE),
                ("user.cl", "(import [n [x]])\n(defn g [] (x))\n"),
            ],
            "n",
            "n.cl",
        ),
        (
            "qualified",
            &[("n.cl", UNPARSEABLE), ("user.cl", "(defn g [] (n/x))\n")],
            "n",
            "n.cl",
        ),
        (
            "mod child",
            &[
                ("user/child.cl", UNPARSEABLE),
                ("user.cl", "(mod child)\n(defn g [] 1)\n"),
            ],
            "user.child",
            "user/child.cl",
        ),
        (
            "prelude",
            &[("prelude.cl", UNPARSEABLE), ("user.cl", "(defn g [] 1)\n")],
            "prelude",
            "prelude.cl",
        ),
        (
            "type twin",
            &[
                ("n.cl", "(defn x [] (nope))\n"),
                ("user.cl", "(import [n [x]])\n(defn g [] (x))\n"),
            ],
            "n",
            "",
        ),
    ];
    for (leg, files, dependency, file) in legs {
        let root = tempfile::tempdir().unwrap();
        write_files(root.path(), files);
        let mut s = repl_session(root.path());
        let started = s
            .register_module("user")
            .and_then(|_| s.wait_inmem_complete().map_err(CranelispError::from));
        assert!(started.is_err(), "{leg}: precondition");
        let _ = s
            .shared
            .scheduler
            .wait_module_inmem_complete_blocking(&ModuleFullPath::from("user"));

        let dep = ModuleFullPath::from(*dependency);
        assert!(
            s.shared.scheduler.is_failed(&dep),
            "{leg}: the dependency is `Failed`"
        );
        if !file.is_empty() {
            assert_eq!(
                s.shared.scheduler.failure_file(&dep),
                Some(root.path().join(file)),
                "{leg}: located in its own file"
            );
        }
        assert_eq!(
            refusing_dependency_of(&s, "user").as_deref(),
            Some(*dependency),
            "{leg}: the loader is refused by it"
        );
        s.shutdown();
    }

    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[("user.cl", "(import [n [x]])\n(defn g [] (x))\n")],
    );
    std::fs::write(root.path().join("n.cl"), NOT_UTF8).unwrap();
    let mut s = repl_session(root.path());
    assert!(s.register_module("user").is_err(), "read leg: precondition");
    let _ = s
        .shared
        .scheduler
        .wait_module_inmem_complete_blocking(&ModuleFullPath::from("user"));
    assert!(
        s.shared.scheduler.is_failed(&ModuleFullPath::from("n")),
        "read leg"
    );
    assert_eq!(
        refusing_dependency_of(&s, "user").as_deref(),
        Some("n"),
        "read leg"
    );
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock), §15.2.3;
// design/int/repl-lifecycle.md §1.3.2 (PF-1 classification) — at startup, a
// `prelude.cl` and, separately, an imported `lib.cl` that does not parse stands
// failed and is reported, and the entry waits unreported. A reload of `user`
// newly importing an unparseable `n` makes `n` stand failed and notify
// `[errors: n.cl]` after the plan's own outcomes, and `user` waits (LQ-4). `/mod
// m`, where `m` imports an unparseable `n`, makes `n` stand failed while `m`
// waits, and the active module is unchanged.
#[test]
fn a_dependency_failing_before_it_registers_stands_failed_and_its_loader_waits() {
    for (dependency, files) in [
        (
            "prelude",
            &[
                ("prelude.cl", "(defn p [] 1\n"),
                ("user.cl", "(defn g [] 1)\n"),
            ][..],
        ),
        (
            "lib",
            &[
                ("lib.cl", "(defn f [] 1\n"),
                ("user.cl", "(import [lib [f]])\n(defn g [] (f))\n"),
            ][..],
        ),
    ] {
        let root = tempfile::tempdir().unwrap();
        write_files(root.path(), files);
        let (mut s, report) = started_session(root.path());
        let report = report.expect("the failed start is reported");
        assert!(stands_failed(&s, dependency), "{dependency}: {report}");
        assert!(!stands_failed(&s, "user"), "{dependency}: the entry waits");
        assert!(
            report.starts_with(&format!("[errors: {dependency}.cl]"))
                && !report.contains("user.cl"),
            "{report}"
        );
        s.shutdown();
    }

    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[
            ("n.cl", "(defn nx [] 1\n"),
            ("z.cl", "(defn zz [] 1)\n"),
            ("user.cl", "(defn g [] 1)\n"),
        ],
    );
    let (mut s, _) = started_session(root.path());
    let outcomes = save_all(
        &mut s,
        root.path(),
        &[
            ("user.cl", "(import [n [nx]])\n(defn g [] 1)\n"),
            ("z.cl", "(defn zz [] 2)\n"),
        ],
    );
    let notices: Vec<String> = outcomes.iter().filter_map(|o| o.notice()).collect();
    assert_eq!(notice_of(&outcomes, "user"), None, "{notices:?}");
    assert!(
        stands_failed(&s, "n") && !stands_failed(&s, "user"),
        "{notices:?}"
    );
    assert!(
        notices
            .last()
            .is_some_and(|notice| notice.starts_with("[errors: n.cl]")),
        "the newly loaded failure is reported after the plan's outcomes: {notices:?}"
    );
    s.shutdown();

    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[
            ("n.cl", "(defn nx [] 1\n"),
            ("m.cl", "(import [n [nx]])\n(defn mm [] (nx))\n"),
        ],
    );
    let mut s = repl_session(root.path());
    assert!(s.handle_mod("m").is_some(), "the load fails");
    assert!(stands_failed(&s, "n"), "`n` stands failed");
    assert!(!stands_failed(&s, "m"), "`m` waits");
    assert_eq!(s.current_module_path(), ModuleFullPath::from("user"));
    s.shutdown();
}

// spec: repl/spec/15-session-persistence.md §15.2.3; design/int/int.md §6.1.1
// (Unreadable entry); design/int/repl-lifecycle.md §1.3.1 (Startup, step 1) —
// an entry file that is not valid UTF-8 stands failed after startup recovery,
// named in the report, and its bytes are unchanged after a refused definition.
#[test]
fn startup_unreadable_entry_stands_failed_and_keeps_its_bytes() {
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("user.cl");
    std::fs::write(&path, NOT_UTF8).unwrap();
    let (mut s, report) = started_session(root.path());

    assert!(stands_failed(&s, "user"));
    let report = report.expect("the unreadable entry is reported");
    assert!(report.starts_with("[errors: user.cl]"), "{report}");
    let refused = s.process_commands("(defn h [] 2)", &mut Vec::new());
    assert!(refusal_names(&refused, &["user.cl"]), "{}", shown(&refused));
    s.regenerate_backing_file();
    assert_eq!(std::fs::read(&path).unwrap(), NOT_UTF8);
    s.shutdown();
}

// ---------------------------------------------------------------------------
// Re-review rulings: the span rule (R2), an unreadable save (R3) and a type
// error located in its own file (design/int/repl-lifecycle.md §1.2 Content
// hash, §1.3.1 PF-1 Spans)
// ---------------------------------------------------------------------------

/// `lib.cl` whose third line opens a form it never closes, and its offset.
const LIB_UNCLOSED_LINE3: &str = "(defn a [] 1)\n\n(defn inc1 [x] (primitives/add-i64 x 1)\n";
const LIB_UNCLOSED_AT: u32 = 15;

/// How many times `text` wraps an error in a module error.
fn module_wrappers(text: &str) -> usize {
    text.matches("module error").count()
}

// spec: design/int/repl-lifecycle.md §1.3.1 (A dependency that fails before it
// registers, Spans), §1.3.2 (Span rule) — a dependency failing to parse at a
// non-zero offset is located at that offset in its own file, at a batch start,
// a code turn and a reload; a dependency failing to read is located in its own
// file at an empty span, not at the loader's import span; the loader's error
// is wrapped once.
#[test]
fn a_pre_registration_failure_keeps_its_own_span_in_its_own_file() {
    const USER: &str = ";; pad\n(import [lib [inc1]])\n(defn main [] (inc1 1))\n";
    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[("lib.cl", LIB_UNCLOSED_LINE3), ("user.cl", USER)],
    );
    let mut s = repl_session(root.path());
    let error = s
        .register_module("user")
        .and_then(|_| s.wait_inmem_complete().map_err(CranelispError::from))
        .expect_err("batch start: the start fails");
    let lib_file = root.path().join("lib.cl");
    assert_eq!(
        error.location().file.as_ref(),
        Some(&lib_file),
        "batch start: {error}"
    );
    assert_eq!(error.span().start, LIB_UNCLOSED_AT, "batch start: {error}");
    assert_eq!(
        module_wrappers(&error.to_string()),
        1,
        "batch start: {error}"
    );
    s.shutdown();

    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[
            ("lib.cl", LIB_UNCLOSED_LINE3),
            ("user.cl", "(defn g [] 1)\n"),
        ],
    );
    let mut s = repl_session(root.path());
    let error = s
        .eval("(defn k [] (lib/inc1 1))")
        .err()
        .expect("code turn: the turn fails");
    assert_eq!(
        error.location().file.as_ref(),
        Some(&root.path().join("lib.cl")),
        "code turn: {error}"
    );
    assert_eq!(error.span().start, LIB_UNCLOSED_AT, "code turn: {error}");
    assert_eq!(module_wrappers(&error.to_string()), 1, "code turn: {error}");
    s.shutdown();

    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[
            ("lib.cl", LIB_UNCLOSED_LINE3),
            ("user.cl", "(defn g [] 1)\n"),
        ],
    );
    let (mut s, _) = started_session(root.path());
    let outcomes = save_all(&mut s, root.path(), &[("user.cl", USER)]);
    let notice = notice_of(&outcomes, "lib").expect("reload: `lib` is reported");
    assert!(
        notice.contains(&format!("at {LIB_UNCLOSED_AT}..")) && module_wrappers(&notice) <= 1,
        "reload: {notice}"
    );
    s.shutdown();

    let root = tempfile::tempdir().unwrap();
    write_files(root.path(), &[("user.cl", USER)]);
    std::fs::write(root.path().join("lib.cl"), NOT_UTF8).unwrap();
    let mut s = repl_session(root.path());
    let error = s
        .register_module("user")
        .and_then(|_| s.wait_inmem_complete().map_err(CranelispError::from))
        .expect_err("read leg: the start fails");
    assert_eq!(
        error.location().file.as_ref(),
        Some(&root.path().join("lib.cl")),
        "read leg: {error}"
    );
    assert_eq!(
        error.span(),
        cranelisp_types::Span::new(0, 0),
        "read leg: {error}"
    );
    assert_eq!(module_wrappers(&error.to_string()), 1, "read leg: {error}");
    s.shutdown();
}

// spec: design/int/repl-lifecycle.md §1.3.1 (A dependency that fails before it
// registers, Batch) — a dependency that registers and fails to typecheck is
// reported at its own span in its own file at a batch start, not in the entry.
#[test]
fn a_dependency_type_error_is_located_in_its_own_file() {
    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[
            ("lib.cl", "(defn inc1 [x] (primitives/add-i64 x \"a\"))\n"),
            (
                "user.cl",
                "(import [lib [inc1]])\n(defn main [] (inc1 1))\n",
            ),
        ],
    );
    let mut s = repl_session(root.path());
    let error = s
        .register_module("user")
        .and_then(|_| s.wait_inmem_complete().map_err(CranelispError::from))
        .expect_err("the start fails");
    assert_eq!(
        error.location().file.as_ref(),
        Some(&root.path().join("lib.cl")),
        "{error}"
    );
    assert_eq!(error.span(), cranelisp_types::Span::new(15, 41), "{error}");
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.5 (session lock);
// design/int/repl-lifecycle.md §1.2 (Content hash), §1.3.2 (Unreadable save,
// R3) — a reload of a module whose saved file is not valid UTF-8 leaves it
// standing failed with a read error located in its file at an empty span, a
// refused definition leaves the bytes unchanged, and a readable compiling save
// releases it.
#[test]
fn an_unreadable_save_stands_failed_and_keeps_its_bytes() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = rebuild_session(root.path(), "(defn g [] 1)\n");
    std::fs::write(&path, NOT_UTF8).unwrap();

    let outcomes = s.run_reload_plan(vec![(ModuleFullPath::from("user"), path.clone())]);

    assert!(
        notice_of(&outcomes, "user").is_some_and(|n| n.starts_with("[errors: user.cl]")),
        "{:?}",
        notice_of(&outcomes, "user")
    );
    assert!(stands_failed(&s, "user"));
    let location = s
        .shared
        .scheduler
        .failure_location(&ModuleFullPath::from("user"))
        .expect("held `Failed`");
    assert_eq!(location.file.as_ref(), Some(&path));
    assert_eq!(location.span, cranelisp_types::Span::new(0, 0));
    let refused = s.process_commands("(defn h [] 2)", &mut Vec::new());
    assert!(refusal_names(&refused, &["user.cl"]), "{}", shown(&refused));
    s.regenerate_backing_file();
    assert_eq!(std::fs::read(&path).unwrap(), NOT_UTF8);

    assert!(save_and_reload(&mut s, &path, "(defn g [] 2)\n"));
    assert!(!session_locked(&s));
    s.shutdown();
}

// spec: design/int/repl-lifecycle.md §1.3.1 (A failed load's record, step 3),
// §1.3.2 (Newly failed report, A2) — a module newly loaded by a reload that
// fails to typecheck reports `[errors: n.cl]` with its own error at its own
// span, not rebuilt from a string at `0..0`.
#[test]
fn a_newly_failed_module_reports_its_own_error_at_its_own_span() {
    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[
            ("n.cl", "(defn nx [] (nope))\n"),
            ("user.cl", "(defn g [] 1)\n"),
        ],
    );
    let (mut s, _) = started_session(root.path());
    let outcomes = save_all(
        &mut s,
        root.path(),
        &[("user.cl", "(import [n [nx]])\n(defn g [] 1)\n")],
    );
    let notice = notice_of(&outcomes, "n").expect("`n` is reported");
    assert!(notice.starts_with("[errors: n.cl]"), "{notice}");
    assert!(notice.contains("at 13..17"), "its own span: {notice}");
    assert!(!notice.contains("0..0"), "{notice}");
    s.shutdown();
}

// ---------------------------------------------------------------------------
// A save while idle at the prompt (review N1, ACT-1045;
// design/int/repl-lifecycle.md §1.2 Poll points, §1.3.1 Write chokepoint)
// ---------------------------------------------------------------------------

// spec: repl/spec/15-session-persistence.md §15.1, repl/spec/14-file-watching.md
// §14.2; design/int/repl-lifecycle.md §1.3.1 (Write chokepoint, Unseen save),
// §1.3.2 (Unseen-save chokepoint) — with the backing file's content on disk
// differing from the recorded state, and separately with it unreadable,
// regeneration writes nothing and leaves the bytes unchanged; the next reload
// rebuilds from the save, or locks for the unreadable leg. A matching state
// writes, and a missing file is written. No OS watcher is running.
#[test]
fn regeneration_keeps_an_unseen_save() {
    for (leg, saved) in [
        ("readable", &b"(defn g [] 5)\n(defn k [] 9)\n"[..]),
        ("unreadable", NOT_UTF8),
    ] {
        let root = tempfile::tempdir().unwrap();
        let (mut s, path) = rebuild_session(root.path(), "(defn g [] 1)\n");
        assert!(s.watcher.is_none(), "{leg}: precondition: no OS watcher");
        std::fs::write(&path, saved).unwrap();

        s.eval("(defn h [] 2)").unwrap();
        s.regenerate_backing_file();

        assert_eq!(
            std::fs::read(&path).unwrap(),
            saved,
            "{leg}: the save is kept"
        );
        s.run_reload_plan(vec![(ModuleFullPath::from("user"), path.clone())]);
        if leg == "readable" {
            assert!(
                defines(&s, "user", "k"),
                "{leg}: the reload rebuilds from the save"
            );
        } else {
            assert!(stands_failed(&s, "user"), "{leg}: the reload locks");
        }
        s.shutdown();
    }

    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = rebuild_session(root.path(), "(defn g [] 1)\n");
    s.eval("(defn h [] 2)").unwrap();
    s.regenerate_backing_file();
    let written = std::fs::read_to_string(&path).unwrap();
    assert!(
        written.contains("(defn h [] 2)"),
        "control: a matching state writes: {written}"
    );

    std::fs::remove_file(&path).unwrap();
    s.eval("(defn m [] 3)").unwrap();
    s.regenerate_backing_file();
    let written = std::fs::read_to_string(&path).unwrap_or_default();
    assert!(
        written.contains("(defn m [] 3)"),
        "a missing file is written: {written}"
    );
    s.shutdown();
}

/// Poll the session's watcher, as the read loop does before each turn, until
/// the queued save's event has been reloaded.
fn poll_until_reloaded(s: &mut CompilerSession) -> Vec<String> {
    for _ in 0..200 {
        let notices = s.poll_watcher();
        if !notices.is_empty() {
            return notices;
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    Vec::new()
}

// spec: repl/spec/14-file-watching.md §14.2 ("a save between turns is reloaded
// before the next evaluation"), §14.5; design/int/repl-lifecycle.md §1.2 (Poll
// points), §1.3.2 (Pre-turn poll) — the poll the read loop runs before
// dispatching a turn reloads a save made while idle: a definition turn after a
// readable save keeps the saved definition in the file and the session, an
// expression and a slash command observe the rebuilt module, and after an
// unreadable save the definition is refused with the bytes unchanged. With no
// queued event the poll changes nothing. The read loop's dispatch order is
// `main.rs` and is evidenced end to end (IS-1, IS-2).
#[test]
fn the_pre_turn_poll_reloads_an_idle_save_before_the_turn() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = rebuild_session(root.path(), "(defn g [] 1)\n");
    s.init_watcher();
    if s.watcher.is_none() {
        s.shutdown();
        return; // the OS notification API is unavailable here
    }
    assert!(
        s.poll_watcher().is_empty(),
        "no queued event: nothing changes"
    );

    std::fs::write(&path, "(defn g [] 5)\n(defn k [] 9)\n").unwrap();
    let notices = poll_until_reloaded(&mut s);
    assert_eq!(notices, ["[updated: user.cl]"], "the save is reloaded");
    assert_eq!(s.eval("(k)").unwrap().expect("a value").value(), 9);
    let CommandResult::Final(sig) = s.process_commands("/sig g", &mut Vec::new()) else {
        panic!("`/sig` answers");
    };
    assert!(sig.contains("user/g"), "{sig}");
    s.eval("(defn h [] 2)").unwrap();
    s.regenerate_backing_file();
    let file = std::fs::read_to_string(&path).unwrap();
    assert!(
        file.contains("(defn k [] 9)")
            && file.contains("(defn h [] 2)")
            && !file.contains("(defn g [] 1)"),
        "{file}"
    );

    std::fs::write(&path, NOT_UTF8).unwrap();
    let notices = poll_until_reloaded(&mut s);
    assert!(
        notices
            .first()
            .is_some_and(|n| n.starts_with("[errors: user.cl]")),
        "{notices:?}"
    );
    let refused = s.process_commands("(defn h2 [] 3)", &mut Vec::new());
    assert!(refusal_names(&refused, &["user.cl"]), "{}", shown(&refused));
    assert_eq!(std::fs::read(&path).unwrap(), NOT_UTF8);
    s.shutdown();
}

// ---------------------------------------------------------------------------
// One record of what the session last saw (review N2, ACT-1046;
// design/int/repl-lifecycle.md §1.2 Content hash)
// ---------------------------------------------------------------------------

/// A save that lands after the session read `path` and before the watcher
/// first sees it: arm the watcher, poll until the save is reloaded, then
/// define `h` and regenerate. Returns the notices and the file afterwards;
/// `None` when the OS notification API is unavailable.
fn save_before_first_sight(
    s: &mut CompilerSession,
    path: &Path,
    saved: &str,
) -> Option<(Vec<String>, String)> {
    std::fs::write(path, saved).unwrap();
    s.init_watcher();
    s.watcher.as_ref()?;
    let notices = poll_until_reloaded(s);
    Some((notices, std::fs::read_to_string(path).unwrap_or_default()))
}

// spec: repl/spec/14-file-watching.md §14.2, repl/spec/15-session-persistence.md
// §15.1; design/int/repl-lifecycle.md §1.2 (Content hash), §1.3.2 (One record)
// — a save landing after entry registration's read and before the watcher's
// first sight is a change at the next poll: it is reloaded, and a later
// definition writes with no warning. The same holds for a dependency loaded by
// `register_dep`.
#[test]
fn a_save_before_the_watchers_first_sight_is_reloaded() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = rebuild_session(root.path(), "(defn g [] 1)\n");
    let Some((notices, _)) =
        save_before_first_sight(&mut s, &path, "(defn g [] 1)\n(defn k [] 9)\n")
    else {
        s.shutdown();
        return;
    };
    assert_eq!(
        notices,
        ["[updated: user.cl]"],
        "entry: the save is reloaded"
    );
    assert_eq!(s.eval("(k)").unwrap().expect("a value").value(), 9);
    s.eval("(defn h [] 2)").unwrap();
    s.regenerate_backing_file();
    let file = std::fs::read_to_string(&path).unwrap();
    assert!(
        file.contains("(defn k [] 9)") && file.contains("(defn h [] 2)"),
        "entry: the definition reaches the file: {file}"
    );
    s.shutdown();

    let root = tempfile::tempdir().unwrap();
    write_files(root.path(), &[("lib.cl", "(defn f [] 1)\n")]);
    let mut s = repl_session(root.path());
    s.eval("(import [lib [f]])").unwrap();
    let lib = root.path().join("lib.cl");
    let Some((notices, _)) = save_before_first_sight(&mut s, &lib, "(defn f [] 7)\n") else {
        s.shutdown();
        return;
    };
    assert_eq!(
        notices,
        ["[updated: lib.cl]"],
        "register_dep: the save is reloaded"
    );
    assert_eq!(s.eval("(f)").unwrap().expect("a value").value(), 7);
    s.shutdown();
}

// spec: design/int/repl-lifecycle.md §1.2 (Content hash, Writers), §1.3.2 (One
// record) — a module restored from the cache records the state it validated, so
// a save landing before the watcher's first sight is reloaded.
#[test]
fn a_cache_hit_restore_records_the_state_it_validated() {
    let root = tempfile::tempdir().unwrap();
    write_files(
        root.path(),
        &[
            ("lib.cl", "(defn f [] 1)\n"),
            ("user.cl", "(defn g [] 1)\n"),
        ],
    );
    let settings = || SessionSettings {
        no_color: true,
        no_cache: false,
        codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
        priority_workers: 1,
        nice_workers: 1,
        run_mode: RunMode::Repl,
    };
    let mut warm = CompilerSession::new(settings(), root.path().to_path_buf(), "user").unwrap();
    warm.set_lib_dirs(Vec::new());
    warm.eval("(import [lib [f]])").unwrap();
    warm.wait_object_complete().unwrap();
    warm.shutdown();

    let mut s = CompilerSession::new(settings(), root.path().to_path_buf(), "user").unwrap();
    s.set_lib_dirs(Vec::new());
    s.eval("(import [lib [f]])").unwrap();
    let lib_module = ModuleFullPath::from("lib");
    assert!(
        s.shared.scheduler.is_cached_module(&lib_module),
        "precondition: `lib` is restored from the cache"
    );
    let lib = root.path().join("lib.cl");
    assert!(
        s.shared.recorded_source(&lib).is_some(),
        "the restore records the state it validated"
    );
    let Some((notices, _)) = save_before_first_sight(&mut s, &lib, "(defn f [] 7)\n") else {
        s.shutdown();
        return;
    };
    assert_eq!(notices, ["[updated: lib.cl]"], "the save is reloaded");
    s.shutdown();
}

// spec: design/int/repl-lifecycle.md §1.2 (Content hash, The watcher compares,
// it does not record), §1.3.2 (One record) — a reload's read, not the poll,
// updates the record; an unreadable rebuild records unreadable, and a
// repeated unreadable event is no change.
#[test]
fn the_reload_read_updates_the_record_and_an_unreadable_rebuild_records_unreadable() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = rebuild_session(root.path(), "(defn g [] 1)\n");
    s.init_watcher();
    if s.watcher.is_none() {
        s.shutdown();
        return;
    }
    assert!(
        s.poll_watcher().is_empty(),
        "an unchanged file is not reloaded at first sight"
    );

    std::fs::write(&path, NOT_UTF8).unwrap();
    let notices = poll_until_reloaded(&mut s);
    assert!(
        notices
            .first()
            .is_some_and(|n| n.starts_with("[errors: user.cl]")),
        "{notices:?}"
    );
    assert_eq!(
        s.shared.recorded_source(&path),
        Some(crate::watch::FileState::Unreadable),
        "the rebuild's read records unreadable"
    );
    std::fs::write(&path, NOT_UTF8).unwrap();
    std::thread::sleep(std::time::Duration::from_millis(200));
    assert!(
        s.poll_watcher().is_empty(),
        "a repeated unreadable event is no change"
    );
    s.shutdown();
}
