//! A missing or unreadable entry source file in each invocation mode
//! (`repl/spec/00-cli-invocation.md` §0.5.5 rules 2 and 4; ACT-1004, ACT-1019).
//!
//! The batch modes share one observation, `names_missing_entry`: exit 1 and the
//! missing file named in an error message on stderr. The `--test` cell applies
//! the same predicate and passes, so a RED `--run` or `--link` cell cannot be a
//! predicate that is unable to pass. The REPL cell pins the other side of rule
//! 2: a missing entry still starts an empty module.
//!
//! Rule 4 uses an entry file that exists but is not valid UTF-8. Its batch
//! cells reuse the message-body predicate; its REPL cell observes that the
//! session locks and the file keeps its bytes.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{CrOutput, Cranelisp};
use std::fs;

const MISSING: &str = "nope.cl";

/// The diagnostic text after a leading `<file>:<line>:<col>: ` location.
fn message_body(line: &str) -> &str {
    let Some((location, body)) = line.split_once(": ") else {
        return line;
    };
    let mut parts = location.rsplitn(3, ':');
    let numeric = |p: Option<&str>| p.is_some_and(|s| s.parse::<u32>().is_ok());
    if numeric(parts.next()) && numeric(parts.next()) && parts.next().is_some() {
        body
    } else {
        line
    }
}

/// Whether an error message, not merely its location prefix, names `file`.
/// Every diagnostic about the entry carries `<file>:1:1:`, so the prefix cannot
/// distinguish the required error from another one.
fn stderr_names_file(stderr: &str, file: &str) -> bool {
    stderr.lines().any(|l| message_body(l).contains(file))
}

/// Whether an error message names the missing entry file.
fn stderr_names_missing_file(stderr: &str) -> bool {
    stderr_names_file(stderr, MISSING)
}

/// §0.5.5 rule 2 for a batch mode: exit status 1 and an error on stderr
/// naming the missing file.
fn names_missing_entry(mode: &str, out: &CrOutput) {
    assert!(
        out.status.code() == Some(1) && stderr_names_missing_file(&out.stderr),
        "{mode} on a missing `{MISSING}` must exit 1 with stderr naming the \
         file (§0.5.5 rule 2)\n--- exit {:?}\n--- stdout:\n{}\n--- stderr:\n{}",
        out.status.code(),
        out.stdout,
        out.stderr
    );
}

// spec: repl/spec/00-cli-invocation.md §0.5.5 Error Handling [R4 S52] — the
// shared predicate accepts the file named in the message and rejects a
// location-only mention (both shapes observed on 2026-09-30).
#[test]
fn missing_entry_predicate_rejects_a_location_only_mention() {
    assert!(stderr_names_missing_file(
        "nope.cl:1:1: error: module error in /t/nope.cl: at 0..0: entry module \
         source file `/t/nope.cl` does not exist\n"
    ));
    assert!(!stderr_names_missing_file(
        "nope.cl:1:1: error: codegen error at 0..0: entry module has no 'main' function\n"
    ));
}

// spec: repl/spec/00-cli-invocation.md §0.5.5 Error Handling [R4 S52] — rule 2,
// `--run`: a missing entry source file is an error on stderr naming it, exit 1.
// defect: class=silent-accept locus=src/session_v4/lifecycle.rs::register_entry_module found=S122 owner=/dev
#[test]
fn run_missing_entry_file_is_named_on_stderr() {
    let out = Cranelisp::new().run(MISSING).output();
    names_missing_entry("--run", &out);
}

// spec: repl/spec/00-cli-invocation.md §0.5.5 Error Handling [R4 S52] — rule 2,
// `--link`: a missing entry source file is an error on stderr naming it, exit 1.
// defect: class=silent-accept locus=src/session_v4/lifecycle.rs::register_entry_module found=S122 owner=/dev
#[test]
fn link_missing_entry_file_is_named_on_stderr() {
    let out = Cranelisp::new().link(MISSING).output();
    names_missing_entry("--link", &out);
}

// spec: repl/spec/00-cli-invocation.md §0.5.5 Error Handling [R4 S52] — rule 2,
// `--test`: the control for the predicate the `--run` and `--link` cells share.
#[test]
fn test_mode_missing_entry_file_is_named_on_stderr() {
    let out = Cranelisp::new().test(MISSING).output();
    names_missing_entry("--test", &out);
}

// spec: repl/spec/00-cli-invocation.md §0.5.5 Error Handling [R4 S52] — rule 2,
// REPL mode: a missing entry starts an empty module that accepts definitions,
// rather than failing as the batch modes must.
#[test]
fn repl_missing_entry_starts_an_empty_module() {
    let out = Cranelisp::new()
        .repl()
        .cli_flag("fresh")
        .stdin("(defn answer [] 41)\n(answer)\n")
        .output();
    assert!(
        out.status.success()
            && out.stdout.contains("fresh>")
            && out.stdout.contains("fresh/answer")
            && out.stdout.contains("41"),
        "the REPL must start the missing entry `fresh` as an empty module and \
         evaluate in it\n--- exit {:?}\n--- stdout:\n{}\n--- stderr:\n{}",
        out.status.code(),
        out.stdout,
        out.stderr
    );
    assert!(
        out.tmp_exists("fresh.cl"),
        "the REPL session must leave `fresh.cl` as the entry's backing file"
    );
}

// =============================================================================
// Rule 4 — an entry file that exists but cannot be read
// =============================================================================

const UNREADABLE: &str = "garbled.cl";

/// An otherwise ordinary source file whose comment holds bytes that are not
/// valid UTF-8.
const NOT_UTF8: &[u8] = b"(defn g [] 1)\n;; \xff\xfe\n";

/// A builder whose project root holds `file` with the `NOT_UTF8` bytes.
fn with_non_utf8_file(file: &str) -> Cranelisp {
    let b = Cranelisp::new();
    let path = b.tmpdir_path().join(file);
    fs::write(&path, NOT_UTF8).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
    b
}

/// Whether `line` carries a `<file>:<line>:<col>: ` location prefix for `file`.
fn located_in(line: &str, file: &str) -> bool {
    let Some(rest) = line.strip_prefix(file).and_then(|r| r.strip_prefix(':')) else {
        return false;
    };
    let mut parts = rest.splitn(3, ':');
    let numeric = |p: Option<&str>| p.is_some_and(|s| s.parse::<u32>().is_ok());
    numeric(parts.next())
        && numeric(parts.next())
        && parts.next().is_some_and(|r| r.starts_with(' '))
}

/// §0.5.5 rule 4 for a batch mode: exit status 1 and a located error on
/// stderr whose message, not only its location prefix, names the unreadable
/// file.
fn names_unreadable_entry(mode: &str, out: &CrOutput) {
    let located_naming = out
        .stderr
        .lines()
        .any(|l| located_in(l, UNREADABLE) && message_body(l).contains(UNREADABLE));
    assert!(
        out.status.code() == Some(1) && located_naming,
        "{mode} on a non-UTF-8 `{UNREADABLE}` must exit 1 with a located error \
         naming the file (§0.5.5 rule 4)\n--- exit {:?}\n--- stdout:\n{}\n--- stderr:\n{}",
        out.status.code(),
        out.stdout,
        out.stderr
    );
}

// spec: repl/spec/00-cli-invocation.md §0.5.5 Error Handling [R4 S52] — the
// location predicate accepts a `<file>:<line>:<col>: ` prefix for the file and
// rejects another file's prefix and an unlocated line.
#[test]
fn located_in_predicate_reads_only_the_location_prefix() {
    assert!(located_in("garbled.cl:1:1: error: x", UNREADABLE));
    assert!(!located_in("user.cl:1:1: error: garbled.cl", UNREADABLE));
    assert!(!located_in("garbled.cl: error", UNREADABLE));
}

// spec: repl/spec/00-cli-invocation.md §0.5.5 Error Handling [R4 S52] — rule 4,
// `--run`: an entry file that is not valid UTF-8 is a located error naming the
// file, and the process exits 1. ACT-1019.
// Pre-fix (binary `5dddfaf4…`, this cell run by `test` on 2026-10-02): exit 1 with
// `garbled.cl:1:1: error: codegen error at 0..0: entry module has no 'main'
// function`, so the read failure was discarded as an empty source.
#[test]
fn run_unreadable_entry_file_is_a_located_error_naming_it() {
    let out = with_non_utf8_file(UNREADABLE).run(UNREADABLE).output();
    names_unreadable_entry("--run", &out);
}

// spec: repl/spec/00-cli-invocation.md §0.5.5 Error Handling [R4 S52] — rule 4,
// `--test`: an entry file that is not valid UTF-8 is a located error naming the
// file, and the process exits 1. ACT-1019.
// Pre-fix (binary `5dddfaf4…`, this cell run by `test` on 2026-10-02): `No tests found`
// and exit 0.
#[test]
fn test_mode_unreadable_entry_file_is_a_located_error_naming_it() {
    let out = with_non_utf8_file(UNREADABLE).test(UNREADABLE).output();
    names_unreadable_entry("--test", &out);
}

// spec: repl/spec/00-cli-invocation.md §0.5.5 Error Handling [R4 S52] — rule 4,
// `--link`: an entry file that is not valid UTF-8 is a located error naming the
// file, and the process exits 1. LK-1.
// No pre-fix `--link` run exists; the `--run` twin was observed RED on
// `5dddfaf4…` with the same predicate. Falsifier: a read of the entry on the
// `--link` path that is not `register_entry_module`'s.
#[test]
fn link_unreadable_entry_file_is_a_located_error_naming_it() {
    let out = with_non_utf8_file(UNREADABLE).link(UNREADABLE).output();
    names_unreadable_entry("--link", &out);
}

// spec: repl/spec/00-cli-invocation.md §0.5.5 Error Handling [R4 S52] — rule 4,
// REPL mode: a `user.cl` that is not valid UTF-8 is reported at startup as
// `[errors: user.cl]`, the entry stands failed and the session locks
// (repl/spec/14-file-watching.md §14.5): `(defn h [] 2)` and `(g)` are refused,
// naming `user.cl` and the save remedy, and the file keeps its bytes.
// ACT-1019. The release by a save is
// `repl_unreadable_entry_first_readable_save_releases_lock`.
// Pre-fix: `user.cl` registered as empty and the first definition overwrote
// it (SPRINT 2026-10-01, "Session lock implemented"; design/int/int.md §6.1.1);
// this cell, run by `test` on 2026-10-02 against binary `5dddfaf4…`, saw no
// startup report, `(defn h [] 2)` accepted and `user.cl` overwritten.
#[test]
fn repl_unreadable_entry_file_locks_session_and_keeps_its_bytes() {
    // Turns: 1 `(defn h [] 2)`, 2 `(g)`, 3 snapshot.
    let out = with_non_utf8_file("user.cl")
        .repl()
        .stdin("(defn h [] 2)\n(g)\n/sh cp user.cl after-refusals.bin\n/quit\n")
        .output();
    let t: Vec<&str> = out.stdout.split("user>").collect();
    let turn = |i: usize| t.get(i).copied().unwrap_or("");
    let refuses_naming_user_cl = |text: &str| {
        text.contains("user.cl")
            && !text.contains("[errors:")
            && text
                .split(|c: char| !c.is_alphabetic())
                .any(|w| w.eq_ignore_ascii_case("save"))
    };
    let after_refusals = fs::read(out.tmpdir.join("after-refusals.bin")).unwrap_or_default();
    let mut violated = Vec::new();
    let mut check = |holds: bool, leg: &str| {
        if !holds {
            violated.push(leg.to_string());
        }
    };
    let startup = format!("{}{}", turn(0), out.stderr);
    check(
        startup.contains("[errors: user.cl]"),
        "startup reports `[errors: user.cl]`",
    );
    check(!turn(1).contains("user/h"), "`(defn h [] 2)` is refused");
    check(
        refuses_naming_user_cl(turn(1)),
        "the definition refusal names `user.cl` and the save remedy",
    );
    check(!turn(2).contains(":primitives/Int"), "`(g)` is refused");
    check(
        refuses_naming_user_cl(turn(2)),
        "the expression refusal names `user.cl` and the save remedy",
    );
    check(
        after_refusals == NOT_UTF8,
        "user.cl keeps its bytes after the refused turns",
    );
    assert!(
        violated.is_empty(),
        "violated:\n- {}\n--- exit {:?}\n--- stdout:\n{}\n--- stderr:\n{}\n--- user.cl after the refused turns: {:?}",
        violated.join("\n- "),
        out.status.code(),
        out.stdout,
        out.stderr,
        String::from_utf8_lossy(&after_refusals)
    );
}

/// A REPL session whose `user.cl` fails at startup, then is saved once as the
/// readable, compiling `(defn g [] 5)`. Turns: 1 `(g)`, 2–4 the save, 5 `(g)`.
fn first_save_after_startup_failure(b: Cranelisp) -> CrOutput {
    b.repl()
        .stdin(
            "(g)\n/sh sleep 0.3\n/sh echo '(defn g [] 5)' > user.cl\n/sh sleep 0.5\n(g)\n/quit\n",
        )
        .output()
}

// spec: repl/spec/00-cli-invocation.md §0.5.5 Error Handling [R4 S52] — rule 4:
// an unreadable `user.cl` stands failed and locks the session as §14.5 states,
// and repl/spec/14-file-watching.md §14.5 releases the lock "when a save leaves
// no module standing failed": the first save of a readable, compiling
// `user.cl` makes `(g)` give 5. Twin control: a `user.cl` that reads but fails
// to typecheck at startup is released by the same first save.
// The defect (found by `test` on 2026-10-02 while authoring ACT-1019's cell,
// and observed RED then): the unreadable twin's first save printed no
// notification and `(g)` stayed refused; a second save was reloaded. The
// unreadable twin also failed against the pre-ACT-1019 binary `5dddfaf4…`, so
// the miss predated that correction. `watch_file` recorded no baseline for a
// file that did not read, so the per-turn `sync_watcher` took the saved
// content as the baseline before the poll compared it.
// defect: class=failure-collapse locus=src/watch.rs::FileWatcher::watch_file found=S122 owner=/dev
#[test]
fn repl_unreadable_entry_first_readable_save_releases_lock() {
    let unreadable = first_save_after_startup_failure(with_non_utf8_file("user.cl"));
    let ill_typed =
        first_save_after_startup_failure(Cranelisp::new().user("(defn g [] (undefined-name 1))\n"));
    let mut violated = Vec::new();
    for (twin, out) in [("unreadable", &unreadable), ("ill-typed", &ill_typed)] {
        let t: Vec<&str> = out.stdout.split("user>").collect();
        let turn = |i: usize| t.get(i).copied().unwrap_or("");
        if turn(1).contains(":primitives/Int") {
            violated.push(format!(
                "{twin}: precondition: `(g)` is refused before the save"
            ));
        }
        if !turn(5).contains(":primitives/Int 5") {
            violated.push(format!(
                "{twin}: the first compiling save releases the lock: `(g)` gives 5"
            ));
        }
    }
    assert!(
        violated.is_empty(),
        "violated:\n- {}\n--- unreadable twin stdout:\n{}\n--- ill-typed twin stdout:\n{}",
        violated.join("\n- "),
        unreadable.stdout,
        ill_typed.stdout
    );
}
