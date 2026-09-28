use super::*;
use cranelisp_types::{CodegenBehaviour, Sexp, Symbol, Visibility};
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
// replaces the records of the declarations it changed; a failed reload leaves
// them at the last published generation (design/int/session-persistence.md
// §2.4.1). The type edit is docstring-only: a structural one is refused
// (repl/spec/14-file-watching.md §14.8).
#[test]
fn reload_replaces_declaration_records_and_failed_reload_keeps_them() {
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
    assert_eq!(
        authored(&record_of(&s, "user", "T").unwrap()),
        authored(&type_v2)
    );
    assert_eq!(
        authored(&record_of(&s, "user", "Disp.T").unwrap()),
        authored(&impl_v2)
    );
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
// Restart-required failure (repl/spec/14-file-watching.md §14.8;
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

fn save_and_reload(s: &mut CompilerSession, path: &Path, source: &str) -> bool {
    std::fs::write(path, source).unwrap();
    let module = ModuleFullPath::from(path.file_stem().unwrap().to_str().unwrap());
    s.reload_module(&module, path).is_ok()
}

fn restart_required_type(s: &CompilerSession, module: &str) -> Option<String> {
    s.restart_required
        .get(&ModuleFullPath::from(module))
        .map(ToString::to_string)
}

// spec: repl/spec/14-file-watching.md §14.8 — only a structural refusal sets
// the retention; a reload failing on a body type error or a parse error does not.
#[test]
fn only_structural_reload_failure_marks_module_restart_required() {
    let root = tempfile::tempdir().unwrap();
    let (mut s, path) = session_with_live_type(root.path());
    let user = ModuleFullPath::from("user");

    assert!(!save_and_reload(&mut s, &path, TYPE_BODY_ERROR));
    assert_eq!(restart_required_type(&s, "user"), None, "type error");
    assert!(!save_and_reload(&mut s, &path, TYPE_PARSE_ERROR));
    assert_eq!(restart_required_type(&s, "user"), None, "parse error");

    assert!(!save_and_reload(&mut s, &path, TYPE_STRUCTURAL));
    assert_eq!(restart_required_type(&s, "user").as_deref(), Some("user/T"));
    assert!(
        s.error_modules.contains(&user),
        "restart-required implies the error set"
    );
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

// spec: design/int/repl-lifecycle.md §1.3.1 — the retention is per module: a
// dependent that fails because its import failed is not marked, and a turn in
// a module that is not restart-required is admitted and regenerates its file.
#[test]
fn restart_required_is_keyed_by_the_refused_module() {
    const SHAPES_V1: &str = "(import [primitives [*]])\n(deftype T [:Int v])\n";
    const SHAPES_STRUCTURAL: &str = "(import [primitives [*]])\n(deftype T [:String v])\n";
    const USER: &str = "(import [shapes [T]])\n(defn one [] 1)\n";
    let root = tempfile::tempdir().unwrap();
    let shapes = root.path().join("shapes.cl");
    std::fs::write(&shapes, SHAPES_V1).unwrap();
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
        restart_required_type(&s, "user"),
        None,
        "a dependent failure is not marked"
    );

    assert!(matches!(
        s.process_commands("(defn h [] 2)", &mut Vec::new()),
        CommandResult::Compile(_)
    ));
    s.eval("(defn h [] 2)").unwrap();
    s.regenerate_backing_file();
    assert!(
        std::fs::read_to_string(&user_file)
            .unwrap()
            .contains("(defn h [] 2)")
    );
    assert_eq!(std::fs::read_to_string(&shapes).unwrap(), SHAPES_STRUCTURAL);
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
