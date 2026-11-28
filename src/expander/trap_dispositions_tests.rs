// The binary's trap-disposition cells (`design/int/s125-binary-clean.md` §8.3).
// U1 reads every workspace member's source; U2 writes process dispositions, so
// its body runs in a re-executed child of this test binary.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

const TRAP_SIGNALS: [&str; 4] = ["SIGFPE", "SIGILL", "SIGBUS", "SIGSEGV"];

// --- U1: the workspace trap-disposition census -----------------------------

/// The disposition writers, in both the `libc` and the `nix` spelling: each is
/// matched as a call of the bare function name, whatever path precedes it.
const WRITERS: [&str; 2] = ["signal", "sigaction"];

/// Intrinsics' guard module, the one admitted writer of the four dispositions.
const GUARD_FILE: &str = "crates/cranelisp-intrinsics/src/io_guard.rs";
const GUARD_DIR: &str = "crates/cranelisp-intrinsics/src/io_guard/";

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Every workspace member, read from the root manifest.
fn workspace_members(root: &Path) -> Vec<PathBuf> {
    let manifest: toml::Table = std::fs::read_to_string(root.join("Cargo.toml"))
        .unwrap()
        .parse()
        .unwrap();
    manifest["workspace"]["members"]
        .as_array()
        .unwrap()
        .iter()
        .map(|member| {
            let member = member.as_str().unwrap();
            assert!(!member.contains('*'), "expand the member glob `{member}`");
            root.join(member)
        })
        .collect()
}

/// A file that compiles only under `cfg(test)`, by the workspace's naming.
fn is_test_only(path: &Path) -> bool {
    path.components().any(|c| c.as_os_str() == "tests")
        || path
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name == "tests.rs" || name.ends_with("_tests.rs"))
}

/// The production Rust source of every workspace member, keyed by its path
/// relative to the workspace root.
fn workspace_sources(root: &Path) -> BTreeMap<String, String> {
    fn visit(root: &Path, path: &Path, sources: &mut BTreeMap<String, String>) {
        for entry in std::fs::read_dir(path).unwrap() {
            let path = entry.unwrap().path();
            let relative = path.strip_prefix(root).unwrap();
            if is_test_only(relative) {
                continue;
            }
            if path.is_dir() {
                visit(root, &path, sources);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                let key = relative.to_str().unwrap().to_owned();
                sources.insert(key, std::fs::read_to_string(&path).unwrap());
            }
        }
    }

    let mut sources = BTreeMap::new();
    for member in workspace_members(root) {
        visit(root, &member.join("src"), &mut sources);
        let build = member.join("build.rs");
        if build.is_file() {
            let key = build.strip_prefix(root).unwrap().to_str().unwrap();
            sources.insert(key.to_owned(), std::fs::read_to_string(&build).unwrap());
        }
    }
    sources
}

/// One call of a disposition writer: its line and its first argument.
#[derive(Debug)]
struct WriterCall {
    line: usize,
    callee: &'static str,
    signal: String,
}

/// The spellings of a literal signal constant, in `libc` and in `nix`.
const LITERAL_PREFIXES: [&str; 3] = ["libc::", "nix::sys::signal::Signal::", "Signal::"];

impl WriterCall {
    /// A call that may write a trap disposition: its signal is not a qualified
    /// literal `SIG*` constant other than the four. An unqualified name, a
    /// local alias or a variable may name a trap signal.
    fn may_write_a_trap_disposition(&self) -> bool {
        let literal = LITERAL_PREFIXES
            .iter()
            .find_map(|prefix| self.signal.strip_prefix(prefix))
            .filter(|name| {
                name.strip_prefix("SIG").is_some_and(|rest| {
                    !rest.is_empty()
                        && rest
                            .chars()
                            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit())
                })
            });
        !literal.is_some_and(|name| !TRAP_SIGNALS.contains(&name))
    }
}

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// The writer calls in `source`, comments excluded. A call may span lines.
fn writer_calls(source: &str) -> Vec<WriterCall> {
    let text: String = source
        .lines()
        .map(|line| line.split_once("//").map_or(line, |(code, _)| code))
        .collect::<Vec<_>>()
        .join("\n");
    let mut calls = Vec::new();
    for callee in WRITERS {
        for (at, _) in text.match_indices(callee) {
            let before = &text[..at];
            let after = text[at + callee.len()..].trim_start();
            let preceded = before.chars().next_back();
            if preceded.is_some_and(|c| is_ident_char(c) || c == '.')
                || before.trim_end().ends_with("fn")
                || !after.starts_with('(')
            {
                continue;
            }
            let args = &after[1..];
            let end = args.find([',', ')']).unwrap_or(args.len());
            calls.push(WriterCall {
                line: before.matches('\n').count() + 1,
                callee,
                signal: args[..end].trim().to_owned(),
            });
        }
    }
    calls
}

/// Each trap-disposition write outside intrinsics' guard module, as
/// `path:line: callee(signal`.
fn census_violations(sources: &BTreeMap<String, String>) -> Vec<String> {
    sources
        .iter()
        .filter(|(path, _)| *path != GUARD_FILE && !path.starts_with(GUARD_DIR))
        .flat_map(|(path, source)| {
            writer_calls(source)
                .into_iter()
                .filter(WriterCall::may_write_a_trap_disposition)
                .map(move |call| format!("{path}:{}: {}({}", call.line, call.callee, call.signal))
        })
        .collect()
}

// spec: design/int/s125-binary-clean.md §8.3 U1 — outside intrinsics' guard
// module no workspace source writes the SIGFPE, SIGILL, SIGBUS or SIGSEGV
// disposition. The planted legs prove the census detects a writer; the
// `SIGUSR1` and guard legs prove it reads real calls and honours one admission.
#[test]
fn trap_dispositions_are_written_only_by_the_intrinsics_guard() {
    let root = workspace_root();
    let sources = workspace_sources(&root);

    let planted = |source: &str| {
        let sources = BTreeMap::from([("planted.rs".to_owned(), source.to_owned())]);
        census_violations(&sources)
    };
    assert_eq!(
        planted("fn f(h: usize) {\n    unsafe { libc::signal(libc::SIGILL, h) };\n}\n"),
        ["planted.rs:2: signal(libc::SIGILL"]
    );
    assert_eq!(
        planted("unsafe {\n    sigaction(sig, &action, &mut previous);\n}\n"),
        ["planted.rs:2: sigaction(sig"]
    );
    assert_eq!(
        planted("nix::sys::signal::sigaction(Signal::SIGSEGV, &sa);\n"),
        ["planted.rs:1: sigaction(Signal::SIGSEGV"]
    );
    assert_eq!(
        planted(
            "const SIGNAL: libc::c_int = libc::SIGSEGV;\nfn f(h: usize) {\n    \
             unsafe { libc::signal(SIGNAL, h) };\n}\n"
        ),
        ["planted.rs:3: signal(SIGNAL"]
    );
    assert_eq!(
        planted("const SIGUSR1: libc::c_int = libc::SIGBUS;\nlibc::signal(SIGUSR1, h);\n"),
        ["planted.rs:2: signal(SIGUSR1"]
    );

    assert_eq!(
        planted("fn f(h: usize) {\n    unsafe { libc::signal(libc::SIGABRT, h) };\n}\n"),
        Vec::<String>::new()
    );

    let sched_dump = writer_calls(&sources["src/sched_dump.rs"]);
    assert_eq!(sched_dump.len(), 1, "{sched_dump:?}");
    assert_eq!(sched_dump[0].signal, "libc::SIGUSR1");
    assert!(!sched_dump[0].may_write_a_trap_disposition());

    let guard = writer_calls(&sources[GUARD_FILE]);
    assert!(
        guard.iter().any(WriterCall::may_write_a_trap_disposition),
        "the guard admission is load-bearing: {guard:?}"
    );

    assert_eq!(census_violations(&sources), Vec::<String>::new());
}

// --- U2: a clause call leaves the dispositions unchanged -------------------

const CHILD_SELECTOR: &str = "CRANELISP_SRC_TEST_CHILD";
const CHILD: &str = "child_expands_a_macro_under_sentinel_actions";
const REPORT_MARKER: &str = "disposition ";

extern "C" fn sentinel_handler(_: libc::c_int, _: *mut libc::siginfo_t, _: *mut libc::c_void) {}

fn sentinel_flags() -> libc::c_int {
    libc::SA_SIGINFO | libc::SA_ONSTACK
}

fn signal_number(name: &str) -> libc::c_int {
    match name {
        "SIGFPE" => libc::SIGFPE,
        "SIGILL" => libc::SIGILL,
        "SIGBUS" => libc::SIGBUS,
        "SIGSEGV" => libc::SIGSEGV,
        _ => unreachable!("invariant: a trap signal name"),
    }
}

fn install_sentinel(sig: libc::c_int) {
    // SAFETY: a zeroed action with an empty mask and a valid `SA_SIGINFO`
    // handler; the child never raises the signal.
    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = sentinel_address();
        action.sa_flags = sentinel_flags();
        libc::sigemptyset(&mut action.sa_mask);
        assert_eq!(libc::sigaction(sig, &action, std::ptr::null_mut()), 0);
    }
}

fn sentinel_address() -> libc::sighandler_t {
    sentinel_handler as *const () as libc::sighandler_t
}

/// Whether two queried actions have the same handler and exactly the same
/// flags. Both are read back from the kernel, so a flag the system supplies
/// appears in both.
fn same_action(before: &libc::sigaction, after: &libc::sigaction) -> bool {
    before.sa_sigaction == after.sa_sigaction && before.sa_flags == after.sa_flags
}

fn installed_action(sig: libc::c_int) -> libc::sigaction {
    // SAFETY: a null new action makes `sigaction` a pure query.
    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        assert_eq!(libc::sigaction(sig, std::ptr::null(), &mut action), 0);
        action
    }
}

#[test]
fn child_expands_a_macro_under_sentinel_actions() {
    if std::env::var(CHILD_SELECTOR).as_deref() != Ok(CHILD) {
        return;
    }
    use crate::session_v4::{CompilerSession, RunMode, SessionSettings};
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
        .register_module_with_source("b", "(defmacro m [] `11)\n", &dir.path().join("b.cl"))
        .unwrap();

    let before = TRAP_SIGNALS.map(|name| {
        install_sentinel(signal_number(name));
        let action = installed_action(signal_number(name));
        assert_eq!(action.sa_sigaction, sentinel_address(), "{name}");
        assert_eq!(
            action.sa_flags & sentinel_flags(),
            sentinel_flags(),
            "{name}"
        );
        action
    });
    let expanded = session.expand_form_sexp("(b/m)").unwrap();
    assert!(
        matches!(expanded, cranelisp_types::Sexp::Int(11, _)),
        "{expanded:?}"
    );

    for (name, before) in TRAP_SIGNALS.iter().zip(&before) {
        let unchanged = same_action(before, &installed_action(signal_number(name)));
        println!("{REPORT_MARKER}{name}: unchanged {unchanged}");
    }
    session.shutdown();

    // Detection proof: an added flag is a change.
    let mut planted = before[0];
    planted.sa_flags |= libc::SA_NODEFER | libc::SA_RESETHAND;
    // SAFETY: the queried action with two more flags; the child never raises.
    unsafe {
        assert_eq!(
            libc::sigaction(libc::SIGFPE, &planted, std::ptr::null_mut()),
            0
        );
    }
    let unchanged = same_action(&before[0], &installed_action(libc::SIGFPE));
    println!("{REPORT_MARKER}planted SIGFPE: unchanged {unchanged}");
}

// spec: design/int/s125-binary-clean.md §8.3 U2 — expanding one macro leaves
// each trap signal's handler and flags as the first installer left them.
#[test]
fn macro_clause_call_leaves_trap_dispositions_unchanged() {
    let path = format!(
        "{}::{CHILD}",
        module_path!()
            .split_once("::")
            .map_or(module_path!(), |(_, rest)| rest)
    );
    let mut cmd = std::process::Command::new(std::env::current_exe().unwrap());
    cmd.env(CHILD_SELECTOR, CHILD).args([
        path.as_str(),
        "--exact",
        "--nocapture",
        "--test-threads=1",
    ]);
    let out = cmd.output().unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "{stdout}\n{}",
        String::from_utf8_lossy(&out.stderr)
    );

    let reported: Vec<&str> = stdout
        .lines()
        .filter_map(|line| line.find(REPORT_MARKER).map(|at| &line[at..]))
        .collect();
    let expected: Vec<String> = TRAP_SIGNALS
        .iter()
        .map(|name| format!("{REPORT_MARKER}{name}: unchanged true"))
        .chain([format!("{REPORT_MARKER}planted SIGFPE: unchanged false")])
        .collect();
    assert_eq!(reported, expected, "{stdout}");
}
