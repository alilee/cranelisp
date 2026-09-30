//! A missing entry source file in each invocation mode
//! (`repl/spec/00-cli-invocation.md` §0.5.5 rule 2; ACT-1004).
//!
//! The batch modes share one observation, `names_missing_entry`: exit 1 and the
//! missing file named in an error message on stderr. The `--test` cell applies
//! the same predicate and passes, so a RED `--run` or `--link` cell cannot be a
//! predicate that is unable to pass. The REPL cell pins the other side of rule
//! 2: a missing entry still starts an empty module.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{CrOutput, Cranelisp};

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

/// Whether an error message, not merely its location prefix, names the
/// missing file. Every diagnostic about the entry carries `nope.cl:1:1:`, so
/// the prefix cannot distinguish the required error from another one.
fn stderr_names_missing_file(stderr: &str) -> bool {
    stderr.lines().any(|l| message_body(l).contains(MISSING))
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
