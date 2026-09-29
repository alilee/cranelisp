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
    s.reload_module(&user, &path).unwrap();
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
    assert!(s.reload_module(&user, &path).is_err());
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
    s.reload_module(&libm, &lib_file).unwrap();
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
// Module lock: failed source and restart-required
// (repl/spec/14-file-watching.md §14.5 item 5, §14.8;
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
        .any(|outcome| outcome.module == module && outcome.result.is_ok())
}

fn restart_required_type(s: &CompilerSession, module: &str) -> Option<String> {
    match s.module_locks.get(&ModuleFullPath::from(module))? {
        ModuleLock::RestartRequired(type_name) => Some(type_name.to_string()),
        ModuleLock::FailedSource => None,
    }
}

fn lock_of(s: &CompilerSession, module: &str) -> Option<ModuleLock> {
    s.module_locks.get(&ModuleFullPath::from(module)).cloned()
}

// spec: repl/spec/14-file-watching.md §14.5 item 5 — a reload that fails to
// parse, from an unlocked module, locks it with failed source and blocks it.
#[test]
fn reload_parse_failure_locks_the_module_with_failed_source() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = session_with_live_type(root.path());
    assert_eq!(lock_of(&s, "user"), None, "precondition");

    assert!(!save_and_reload(&mut s, &path, TYPE_PARSE_ERROR));
    assert_eq!(lock_of(&s, "user"), Some(ModuleLock::FailedSource));
    assert!(s.error_modules.contains(&ModuleFullPath::from("user")));
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.5 item 5, §14.8 — a type error locks
// the module with failed source; a later structural refusal replaces that
// cause with restart-required.
#[test]
fn reload_failure_locks_with_its_cause_and_a_structural_refusal_upgrades_it() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = session_with_live_type(root.path());
    let user = ModuleFullPath::from("user");

    assert!(!save_and_reload(&mut s, &path, TYPE_BODY_ERROR));
    assert_eq!(
        lock_of(&s, "user"),
        Some(ModuleLock::FailedSource),
        "type error"
    );
    assert!(!save_and_reload(&mut s, &path, TYPE_PARSE_ERROR));
    assert_eq!(
        lock_of(&s, "user"),
        Some(ModuleLock::FailedSource),
        "parse error"
    );

    assert!(!save_and_reload(&mut s, &path, TYPE_STRUCTURAL));
    assert_eq!(restart_required_type(&s, "user").as_deref(), Some("user/T"));
    assert!(
        s.error_modules.contains(&user),
        "a lock implies the error set"
    );
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.5 item 5, §14.6 — a failed-source
// lock stands through `/reset` and ends at a successful reload, which also
// lifts the error block.
#[test]
fn failed_source_lock_stands_until_a_successful_reload() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = session_with_live_type(root.path());
    let user = ModuleFullPath::from("user");
    assert!(!save_and_reload(&mut s, &path, TYPE_BODY_ERROR));

    s.dispatch_command(crate::repl::ReplCommand::Reset, &mut Vec::new());
    assert_eq!(
        lock_of(&s, "user"),
        Some(ModuleLock::FailedSource),
        "/reset"
    );
    assert!(
        s.error_modules.contains(&user),
        "/reset keeps the error block"
    );

    assert!(save_and_reload(&mut s, &path, TYPE_V1));
    assert_eq!(lock_of(&s, "user"), None);
    assert!(!s.error_modules.contains(&user));
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.5 item 5 — while the module is locked
// with failed source, no regeneration writes the saved file, and a definition
// turn is refused with the save remedy and the session unchanged; expressions
// keep the §14.4 refusal.
#[test]
fn failed_source_module_keeps_saved_file_and_refuses_definition_turns() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = session_with_live_type(root.path());
    assert!(!save_and_reload(&mut s, &path, TYPE_BODY_ERROR));

    s.regenerate_backing_file();
    assert_eq!(std::fs::read_to_string(&path).unwrap(), TYPE_BODY_ERROR);

    let CommandResult::Final(refused) = s.process_commands("(defn h [] 2)", &mut Vec::new()) else {
        panic!("a definition turn in a locked module must be refused");
    };
    assert!(
        refused.contains("'user'") && refused.contains("does not compile"),
        "{refused}"
    );
    assert!(!refused.contains("Restart"), "{refused}");
    let user_table = s.shared.symbol_tables.get(&ModuleFullPath::from("user"));
    assert!(user_table.unwrap().get("h").is_none());
    let CommandResult::Final(expression) = s.process_commands("(g)", &mut Vec::new()) else {
        panic!("an expression stays error-blocked");
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
    let error = s
        .reload_module(&ModuleFullPath::from("user"), &path)
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

// spec: repl/spec/14-file-watching.md §14.8 — the failure stands through a
// later failing save and `/reset`, and ends at a successful reload.
#[test]
fn restart_required_stands_until_a_successful_reload() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = session_with_live_type(root.path());
    let user = ModuleFullPath::from("user");
    assert!(!save_and_reload(&mut s, &path, TYPE_STRUCTURAL));

    assert!(!save_and_reload(&mut s, &path, TYPE_BODY_ERROR));
    assert_eq!(
        restart_required_type(&s, "user").as_deref(),
        Some("user/T"),
        "later failure"
    );
    s.dispatch_command(crate::repl::ReplCommand::Reset, &mut Vec::new());
    assert_eq!(
        restart_required_type(&s, "user").as_deref(),
        Some("user/T"),
        "/reset"
    );
    assert!(
        s.error_modules.contains(&user),
        "/reset keeps the error block"
    );

    assert!(save_and_reload(&mut s, &path, TYPE_V1));
    assert_eq!(restart_required_type(&s, "user"), None);
    assert!(!s.error_modules.contains(&user));
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.8 — no regeneration writes the
// retained file, and a definition turn that would is refused with the session
// unchanged; expressions keep the §14.4 refusal.
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
        refused.contains("'user'") && refused.contains("user/T") && refused.contains("Restart"),
        "{refused}"
    );
    let user_table = s.shared.symbol_tables.get(&ModuleFullPath::from("user"));
    assert!(user_table.unwrap().get("h").is_none());
    let CommandResult::Final(expression) = s.process_commands("(g)", &mut Vec::new()) else {
        panic!("an expression stays error-blocked");
    };
    assert!(expression.starts_with("Cannot evaluate"), "{expression}");
    s.shutdown();
}

// spec: design/int/repl-lifecycle.md §1.3.1 — the lock is per module and
// carries its own cause: a dependent that fails because its import failed is
// locked with failed source, not restart-required, and a turn in a module that
// is not locked is admitted and regenerates its own file only.
#[test]
fn module_lock_is_keyed_by_the_failed_module_with_its_own_cause() {
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
    assert!(!save_and_reload(&mut s, &user_file, USER));
    assert_eq!(
        lock_of(&s, "user"),
        Some(ModuleLock::FailedSource),
        "a dependent failure locks the dependent with failed source"
    );
    assert!(matches!(
        s.process_commands("(defn h [] 2)", &mut Vec::new()),
        CommandResult::Final(_)
    ));

    assert_eq!(s.handle_mod("other"), None);
    assert_eq!(
        lock_of(&s, "other"),
        None,
        "precondition: `other` is unlocked"
    );
    assert!(matches!(
        s.process_commands("(defn h [] 2)", &mut Vec::new()),
        CommandResult::Compile(_)
    ));
    s.eval("(defn h [] 2)").unwrap();
    s.regenerate_backing_file();
    let other_saved = std::fs::read_to_string(&other_file).unwrap();
    assert!(
        other_saved.contains("(defn base [] 5)") && other_saved.contains("(defn h [] 2)"),
        "{other_saved}"
    );
    assert_eq!(std::fs::read_to_string(&user_file).unwrap(), USER);
    assert_eq!(std::fs::read_to_string(&shapes).unwrap(), SHAPES_STRUCTURAL);
    s.shutdown();
}

// ---------------------------------------------------------------------------
// Startup recovery (repl/spec/15-session-persistence.md §15.2.3)
// ---------------------------------------------------------------------------

/// A REPL session over `root` whose entry `user.cl` holds `source`, recovered
/// through the degraded startup load; returns the report.
fn recovered_session(root: &Path, source: &str) -> (CompilerSession, PathBuf, Option<String>) {
    let path = root.join("user.cl");
    std::fs::write(&path, source).unwrap();
    let mut s = repl_session(root);
    let report = s.recover_startup_failure("user");
    (s, path, report)
}

// spec: repl/spec/15-session-persistence.md §15.2.3 — an entry backing file
// that does not parse is reported and locks the module with failed source. It
// yields no failed form, so neither regeneration nor a definition turn writes
// the file.
#[test]
fn startup_unparsable_entry_locks_the_module_and_records_no_failed_form() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path, report) = recovered_session(root.path(), TYPE_PARSE_ERROR);
    let user = ModuleFullPath::from("user");
    let report = report.expect("an unparsable entry is reported");
    assert!(report.starts_with("[errors: user.cl]"), "{report}");
    assert_eq!(lock_of(&s, "user"), Some(ModuleLock::FailedSource));
    assert!(s.error_modules.contains(&user));
    assert!(!s.failed_forms.contains_key(&user));

    s.regenerate_backing_file();
    assert_eq!(std::fs::read_to_string(&path).unwrap(), TYPE_PARSE_ERROR);
    assert!(matches!(
        s.process_commands("(defn h [] 2)", &mut Vec::new()),
        CommandResult::Final(_)
    ));
    s.shutdown();
}

// spec: repl/spec/15-session-persistence.md §15.2.3 negative — an entry file
// that parses but has a failing form keeps the definition repair: its failed
// form is retained, the module is not locked and a definition is admitted.
#[test]
fn startup_parseable_entry_with_failed_form_is_not_locked() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, _path, report) = recovered_session(root.path(), TYPE_BODY_ERROR);
    let user = ModuleFullPath::from("user");
    assert!(report.is_some_and(|r| r.contains("g")));
    assert_eq!(lock_of(&s, "user"), None);
    assert!(s.error_modules.contains(&user));
    assert_eq!(s.failed_forms.get(&user).map(Vec::len), Some(1));
    assert!(matches!(
        s.process_commands("(defn h [] 2)", &mut Vec::new()),
        CommandResult::Compile(_)
    ));
    s.shutdown();
}

// spec: repl/spec/14-file-watching.md §14.6; repl/spec/15-session-persistence.md
// §15.1 — an imported module that fails at startup is locked with failed
// source, so no definition turn in it or regeneration writes its file, while
// the parseable entry keeps its §15.2.3 repair and is not locked.
#[test]
fn startup_failed_dependency_is_locked_and_the_entry_is_not() {
    const FAILING_LIB: &str = "(defn keep-me [] (nope))\n";
    let root = tempfile::tempdir().unwrap();
    let lib_path = root.path().join("lib.cl");
    std::fs::write(&lib_path, FAILING_LIB).unwrap();
    let entry = "(import [lib [keep-me]])\n(defn g [] 1)\n";
    std::fs::write(root.path().join("user.cl"), entry).unwrap();
    let mut s = repl_session(root.path());
    assert!(s.register_module("user").is_err(), "precondition");

    let report = s.recover_startup_failure("user");

    assert!(report.is_some(), "the startup failure is reported");
    assert_eq!(lock_of(&s, "lib"), Some(ModuleLock::FailedSource));
    assert!(s.error_modules.contains(&ModuleFullPath::from("lib")));
    assert_eq!(lock_of(&s, "user"), None, "the entry is not locked");

    s.handle_mod("lib");
    assert_eq!(s.current_module_path(), ModuleFullPath::from("lib"));
    assert!(matches!(
        s.process_commands("(defn z [] 1)", &mut Vec::new()),
        CommandResult::Final(_)
    ));
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
        let error = s.reload_module(&lib, &lib_file).unwrap_err().to_string();
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
// and lifts the module's error block and restart marker.
#[test]
fn reload_beside_a_failed_module_succeeds_and_lifts_its_restart_marker() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, lib_file, siblings) = session_with_siblings(root.path(), 1);
    let lib = ModuleFullPath::from("lib");
    assert!(!save_and_reload(&mut s, &lib_file, TYPE_STRUCTURAL));
    assert_eq!(restart_required_type(&s, "lib").as_deref(), Some("lib/T"));
    fail_siblings(&mut s, &siblings);

    std::fs::write(&lib_file, TYPE_V1).unwrap();
    s.reload_module(&lib, &lib_file).unwrap();
    assert_eq!(restart_required_type(&s, "lib"), None);
    assert!(!s.error_modules.contains(&lib));
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
    s.reload_module(&ModuleFullPath::from("user"), path)
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
    let module = ModuleFullPath::from(module);
    s.module_locks.get(&module) == Some(&ModuleLock::FailedSource)
        && s.error_modules.contains(&module)
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
// repl/spec/14-file-watching.md §14.2 steps 2–3, §14.5 item 5 — a remaining
// definition naming an omitted function, in call or value position or from a
// template, fails as an unresolved name and leaves the module locked and in
// the error set.
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
// unresolved name and locks the module.
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
        outcomes.iter().all(|outcome| outcome.result.is_ok()),
        "{:?}",
        outcomes.iter().map(|o| o.notice()).collect::<Vec<_>>()
    );
    assert_eq!(outcomes.len(), 2, "one outcome per module");
    assert_eq!(run(&mut s), 5);
    s.shutdown();
}

// spec: design/int/repl-lifecycle.md §1.3.1 — a dependent that fails in a
// watcher plan rooted at its changed dependency is locked and blocked, while
// the dependency that compiled is not.
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
// executor: its failure is reported and leaves the module locked and blocked.
#[test]
fn mod_recompile_failure_locks_the_module() {
    let root = tempfile::tempdir().unwrap();
    let mut s = session_importing_lib(root.path());
    mark_cache_installed(&s, "lib");
    std::fs::write(root.path().join("lib.cl"), "(defn base [] (nope))\n").unwrap();

    let failure = s
        .handle_mod("lib")
        .expect("the failed recompile is reported");

    assert!(failure.starts_with("[errors: lib.cl]"), "{failure}");
    assert!(locked_with_failed_source(&s, "lib"));
    s.shutdown();
}
