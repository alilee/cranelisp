// agent/sink.rs — the ONE env-gated, best-effort, silent file-append mechanism
// shared by the two persistent agent sinks (`log.rs` JSONL index + `trace.rs`
// full-content trace). `design/int/agent.md §28.3` (Principle 7 — one mechanism,
// not two copies; Principle 6 — complexity budget).
//
// With the §28.1 stderr-sink removal, `log.rs::record` and `trace.rs`'s emitters
// perform the IDENTICAL operation: read an env var as a path (absence/empty =
// off), and best-effort-append text to it, all errors DISCARDED. That mechanism
// lives here exactly once. Each caller keeps its OWN env var const (`LOG_VAR` /
// `TRACE_VAR`) and its OWN content shape (JSONL line vs trace text block) — this
// helper owns ONLY the gate + open/append + swallow, which is genuinely common.

#![cfg(feature = "agent")]

use std::io::Write;

/// The configured path for an env-var path-gate, or `None` when off (unset or
/// empty after trimming). The single source for the §27 / §28 "set ⇒ a path;
/// unset/empty ⇒ off" gate shape — `log.rs` and `trace.rs` both read it.
pub(crate) fn env_path(var: &str) -> Option<String> {
    match std::env::var(var) {
        Ok(v) => {
            let v = v.trim();
            if v.is_empty() {
                None
            } else {
                Some(v.to_string())
            }
        }
        Err(_) => None,
    }
}

/// Append `content` to the file named by env var `var` IF that var is set to a
/// path (else no-op). Best-effort + GRACEFUL: the gate-check, open, and write are
/// ALL swallowed (`let _ = …`) — an unwritable path, a missing parent dir, or a
/// permission error degrades silently and NEVER crashes the session or spews into
/// the REPL. The ONLY side effect is the file write. Callers pre-format `content`
/// (a JSONL line, a trace block) including any trailing newline they want.
pub(crate) fn append_to_env_path(var: &str, content: &str) {
    let Some(path) = env_path(var) else {
        return; // off — no file created, no cost paid.
    };
    let _ = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
        .and_then(|mut f| f.write_all(content.as_bytes()));
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A guard that sets an arbitrary env var for the test body and restores the
    /// prior value on drop. Env mutation is process-global, so these tests run
    /// serially within this module's binary (one per nextest process).
    struct EnvGuard(&'static str, Option<String>);
    impl EnvGuard {
        fn set(var: &'static str, value: &str) -> Self {
            let prior = std::env::var(var).ok();
            // SAFETY: unit test, single-threaded within this process at this point.
            unsafe { std::env::set_var(var, value) };
            EnvGuard(var, prior)
        }
        fn unset(var: &'static str) -> Self {
            let prior = std::env::var(var).ok();
            unsafe { std::env::remove_var(var) };
            EnvGuard(var, prior)
        }
    }
    impl Drop for EnvGuard {
        fn drop(&mut self) {
            match &self.1 {
                Some(v) => unsafe { std::env::set_var(self.0, v) },
                None => unsafe { std::env::remove_var(self.0) },
            }
        }
    }

    const TEST_VAR: &str = "CRANELISP_AGENT_SINK_TEST";

    // §28.3 — gate OFF (unset / empty) ⇒ no path, append is a no-op (no file).
    #[test]
    fn env_path_off_for_unset_and_empty() {
        let _g = EnvGuard::unset(TEST_VAR);
        assert!(env_path(TEST_VAR).is_none(), "unset ⇒ off");
        // append is a silent no-op when off (no panic, no file).
        append_to_env_path(TEST_VAR, "ignored");

        let _g2 = EnvGuard::set(TEST_VAR, "   ");
        assert!(env_path(TEST_VAR).is_none(), "empty/whitespace ⇒ off");
    }

    // §28.3 — set ⇒ append the content verbatim; a second append APPENDS.
    #[test]
    fn append_writes_then_appends() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("sink.txt");
        let _g = EnvGuard::set(TEST_VAR, path.to_str().unwrap());
        append_to_env_path(TEST_VAR, "first\n");
        append_to_env_path(TEST_VAR, "second\n");
        let body = std::fs::read_to_string(&path).expect("the sink file must exist");
        assert_eq!(body, "first\nsecond\n", "appends in order, body={body:?}");
    }

    // §28.3 — GRACEFUL: an unwritable path (file under a nonexistent parent dir)
    // is swallowed — no panic, no file forced into being.
    #[test]
    fn unwritable_path_is_swallowed() {
        let dir = tempfile::tempdir().unwrap();
        let bad = dir.path().join("no-such-dir").join("sink.txt");
        let _g = EnvGuard::set(TEST_VAR, bad.to_str().unwrap());
        append_to_env_path(TEST_VAR, "data"); // must NOT panic
        assert!(!bad.exists(), "an unwritable path must not be created: {bad:?}");
    }
}
