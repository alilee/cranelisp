// agent/log.rs — the silent, persistent, greppable agent activity log (Pillar 4,
// S90; `design/int/agent.md §27`, `repl/spec.md §17.20`).
//
// A NEW feature-gated SIBLING sink to `trace.rs` (the `/arch` R5 ruling, §27.4) —
// NOT a `trace.rs` extension. The two are deliberately distinct:
//
//   - `trace.rs` (`CRANELISP_AGENT_TRACE`) is EPHEMERAL stderr wire-debug — the rig
//     message sequence, for watching one session live.
//   - `log.rs`  (`CRANELISP_AGENT_LOG`)   is PERSISTENT file-backed JSONL insight —
//     the struggle signal (where the agent repaired/gave up), for mining by hand
//     later with `grep`/`jq`.
//
// Different lifetime, sink, consumer (Principle 6 — two sinks, not one overloaded
// module). Both env-gated, both `#[cfg(feature="agent")]`, both silent-by-absence,
// both NG4 dev-session artifacts (never in a `--link`/`--release` artifact).
//
// Contract (`repl/spec.md §17.20`):
//   - SILENT: writing the log produces NOTHING extra in the REPL — no banner, no
//     per-event echo, no transcript change. The human's session is byte-identical
//     to the same session with logging off. The ONLY side effect is the file write.
//   - ENV-OPT-IN: `CRANELISP_AGENT_LOG=<path>` ⇒ append; unset/empty ⇒ OFF, no file
//     created, no cost paid (exactly like `trace::trace_enabled`, `trace.rs:38`).
//   - PERSISTENT JSONL: one JSON object per line, appended across turns + session.
//   - GREPPABLE STABLE KEYS: every record carries `event`; where applicable
//     `symbol`/`module`/`error_class`/`iteration`/`tool` — so a one-line grep/jq
//     extracts "every repair event and its triggering symbol/error".
//   - GRACEFUL: any IO/serialize failure is swallowed (`let _ = …`) — an unwritable
//     path NEVER crashes the session and NEVER spews an error into the REPL.

#![cfg(feature = "agent")]

use serde::Serialize;

/// The env var that turns the log on. A PATH (not a `=1` toggle) — set ⇒ append to
/// that file; unset/empty ⇒ off. Sibling to `trace.rs`'s `CRANELISP_AGENT_TRACE`.
const LOG_VAR: &str = "CRANELISP_AGENT_LOG";

/// The configured log path, or `None` when logging is off (unset/empty). Defers
/// to the shared `sink::env_path` gate (§28.3) — sibling to `trace::trace_path`.
fn log_path() -> Option<String> {
    crate::agent::sink::env_path(LOG_VAR)
}

/// A single agent-activity record (`repl/spec.md §17.20.3`). One per line of JSONL.
/// Int-private; `#[derive(Serialize)]`; zero `cranelisp-types`/public-API impact
/// (§27.3). The stable greppable keys: `event` is always present; the rest are
/// `Option` and omitted (`skip_serializing_if`) when absent — so a record carries
/// exactly the keys it has, and a `grep '"event":"repair"'` / `jq` over the file
/// extracts the struggle signal reliably.
#[derive(Serialize)]
pub(crate) struct LogEvent {
    /// The event type — `exchange` / `pull` / `repair` / `submit` / `give_up`.
    pub event: &'static str,
    /// The symbol involved (the defined/struggled-over name), when there is one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub symbol: Option<String>,
    /// The module the symbol lives in, when there is one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub module: Option<String>,
    /// A repair's triggering compiler-error class (e.g. `ParseError`/`TypeError`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error_class: Option<String>,
    /// A repair's 1-based iteration count.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub iteration: Option<usize>,
    /// The 1-based `agent_turn` loop-step index (§28.2) — the log↔trace
    /// correlation key. Its OWN field, NOT the overloaded `iteration` (a repair
    /// carries both: `turn` for correlation, `iteration` for its repair count).
    /// Joins each compact log record to the full-content trace block (`turn=N`)
    /// produced by the same loop iteration.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub turn: Option<usize>,
    /// A pull's tool/command name (e.g. `source`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tool: Option<String>,
    /// F1 (§17.20.3a) — the natural-language question a `pull` probe wanted to
    /// answer (the model-supplied `question` tool argument), stamped verbatim.
    /// Feeds the **unresolved-question list** metric (the primer-gap worklist).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub question: Option<String>,
    /// F3 (§17.20.3a) — a `give_up`'s terminal cause (`step_budget` /
    /// `model_declined`). The dominant `error_class` it was looping on rides the
    /// existing `error_class` field. Feeds the **give-up rate + cause histogram**.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cause: Option<String>,
    /// F4 (§17.20.3a) — the context-version stamp: a hash of the assembled primer.
    /// Feeds the **comparable-runs discipline** (a metric delta is valid only
    /// between runs whose stamps differ in the edited artifact alone).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub primer_hash: Option<String>,
    /// F4 (§17.20.3a) — the harvest character count (the session-context size).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub harvest_len: Option<usize>,
    /// F5 (§17.20.3a/b) — the `CRANELISP_AGENT_SCENARIO` tag, stamped on EVERY
    /// record (at the `record` chokepoint). Feeds **per-scenario slicing**.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub scenario: Option<String>,
    /// F6 (§17.20.3a) — the harness step counter at a `submit`. Feeds
    /// **probes-per-submit**.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub steps_at_submit: Option<usize>,
    /// F6 (§17.20.3a) — the harness step counter at a `give_up`. Feeds the
    /// step-count facet of the **give-up rate** analysis.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub steps_at_give_up: Option<usize>,
    /// A coarse wall-clock timestamp (unix seconds) — for ordering when mining.
    pub ts: u64,
}

impl LogEvent {
    /// Construct a bare event carrying only its type + timestamp. The optional
    /// fields are set fluently by the record sites (one-liners, §27.1).
    pub(crate) fn new(event: &'static str) -> Self {
        LogEvent {
            event,
            symbol: None,
            module: None,
            error_class: None,
            iteration: None,
            turn: None,
            tool: None,
            question: None,
            cause: None,
            primer_hash: None,
            harvest_len: None,
            scenario: None,
            steps_at_submit: None,
            steps_at_give_up: None,
            ts: now_unix_secs(),
        }
    }

    pub(crate) fn symbol(mut self, s: impl Into<String>) -> Self {
        self.symbol = Some(s.into());
        self
    }

    pub(crate) fn module(mut self, m: impl Into<String>) -> Self {
        self.module = Some(m.into());
        self
    }

    pub(crate) fn error_class(mut self, c: impl Into<String>) -> Self {
        self.error_class = Some(c.into());
        self
    }

    pub(crate) fn iteration(mut self, i: usize) -> Self {
        self.iteration = Some(i);
        self
    }

    /// Stamp the 1-based `agent_turn` loop-step index (§28.2) — the log↔trace
    /// correlation key. Mirrors `iteration` fluently; the two are distinct.
    pub(crate) fn turn(mut self, t: usize) -> Self {
        self.turn = Some(t);
        self
    }

    pub(crate) fn tool(mut self, t: impl Into<String>) -> Self {
        self.tool = Some(t.into());
        self
    }

    /// F1 — stamp the probe's natural-language `question` (§17.20.3a).
    pub(crate) fn question(mut self, q: impl Into<String>) -> Self {
        self.question = Some(q.into());
        self
    }

    /// F3 — stamp a `give_up`'s terminal `cause` (§17.20.3a).
    pub(crate) fn cause(mut self, c: impl Into<String>) -> Self {
        self.cause = Some(c.into());
        self
    }

    /// F4 — stamp the context-version stamp (`primer_hash` + `harvest_len`,
    /// §17.20.3a). Both together — the pair is the comparable-runs key.
    pub(crate) fn context_stamp(mut self, primer_hash: impl Into<String>, harvest_len: usize) -> Self {
        self.primer_hash = Some(primer_hash.into());
        self.harvest_len = Some(harvest_len);
        self
    }

    /// F6 — stamp the harness step counter at a `submit` (§17.20.3a).
    pub(crate) fn steps_at_submit(mut self, n: usize) -> Self {
        self.steps_at_submit = Some(n);
        self
    }

    /// F6 — stamp the harness step counter at a `give_up` (§17.20.3a).
    pub(crate) fn steps_at_give_up(mut self, n: usize) -> Self {
        self.steps_at_give_up = Some(n);
        self
    }
}

/// The scenario tag env (F5, §17.20.3b) — the sibling of `CRANELISP_AGENT_LOG`,
/// same silent/opt-in/graceful contract. Unset/empty ⇒ `None` (the field is
/// absent, never a spurious value). Read at the `record` chokepoint so EVERY
/// record carries it uniformly without threading it to every call site.
const SCENARIO_VAR: &str = "CRANELISP_AGENT_SCENARIO";

fn scenario_tag() -> Option<String> {
    crate::agent::sink::env_path(SCENARIO_VAR)
}

/// Append one event to the log file IF logging is enabled (`CRANELISP_AGENT_LOG`
/// set to a writable path). Best-effort + GRACEFUL (§27.2): the gate-check,
/// serialize, open, and write are ALL swallowed (`let _ = …`) — an unwritable path,
/// a serialize failure, or anything else degrades silently. NEVER writes to stdout
/// / the transcript (the SILENT contract, §27.1): the only side effect is the file.
pub(crate) fn record(mut event: LogEvent) {
    if log_path().is_none() {
        return; // off — no file created, no cost paid (early out before serialize).
    }
    // F5 (§17.20.3a/b) — stamp the scenario tag on EVERY record at the single
    // chokepoint (so no call site can forget it). Unset env ⇒ field stays absent.
    if event.scenario.is_none() {
        event.scenario = scenario_tag();
    }
    // Serialize to a single JSON line. A serialize failure (should never happen for
    // this flat struct) is swallowed — logging never disturbs the session.
    let Ok(mut line) = serde_json::to_string(&event) else {
        return;
    };
    line.push('\n');
    // The env-gate + best-effort append + swallow lives ONCE in `sink` (§28.3) —
    // shared with `trace.rs`. Any IO error (unwritable path, missing parent dir,
    // permission) is DISCARDED there.
    crate::agent::sink::append_to_env_path(LOG_VAR, &line);
}

/// Derive a stable, greppable `error_class` from a compiler-error string. The
/// validator feeds back `CranelispError::to_string()` (e.g. `"parse error at …"` /
/// `"type error at …"`), so the class is the leading error category. Stable enough
/// that `grep '"error_class":"ParseError"'` reliably buckets the struggle signal.
pub(crate) fn classify_error(error: &str) -> String {
    let e = error.trim_start();
    if e.starts_with("parse error") {
        "ParseError".to_string()
    } else if e.starts_with("type error") {
        "TypeError".to_string()
    } else if e.starts_with("codegen error") {
        "CodegenError".to_string()
    } else if e.starts_with("module error") {
        "ModuleError".to_string()
    } else if e.starts_with("macro error") {
        "MacroError".to_string()
    } else {
        "OtherError".to_string()
    }
}

/// Extract the defined symbol's name from a (possibly UNBALANCED — pre-repair)
/// definition form like `(defn helper [x] …)` / `(def x …)` / `(defmacro m …)` /
/// `(deftype T …)`. Tolerant of a broken form: it does NOT parse, it scans the
/// FIRST `(`, the head word, and the following name token. Returns `None` when the
/// shape is not a recognised defining form. Used so a `repair`/`submit` record
/// carries the struggled-over `symbol` even when the form does not yet compile.
pub(crate) fn defined_symbol(form: &str) -> Option<String> {
    let s = form.trim_start();
    let s = s.strip_prefix('(')?.trim_start();
    // The defining head words whose SECOND token is the defined name.
    let mut tokens = s.split_whitespace();
    let head = tokens.next()?;
    let defines = matches!(
        head,
        "defn" | "def" | "defmacro" | "deftype" | "deftrait" | "definstance"
    );
    if !defines {
        return None;
    }
    let name = tokens.next()?;
    // Strip any stray opening bracket fused to the name (defensive on broken forms).
    let name = name.trim_start_matches(['(', '[']);
    if name.is_empty() {
        None
    } else {
        Some(name.to_string())
    }
}

/// F4 (§17.20.3a) — a stable content hash of the assembled primer, for the
/// context-version stamp. Deterministic within a build (`DefaultHasher` uses
/// fixed keys), so two runs with the SAME primer produce the SAME stamp — the
/// comparable-runs discipline needs exactly that (a metric delta is valid only
/// between runs whose stamps differ in the edited artifact). Rendered as hex.
pub(crate) fn primer_hash(primer: &str) -> String {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    primer.hash(&mut h);
    format!("{:016x}", h.finish())
}

/// Unix-seconds timestamp, best-effort (`0` if the clock is before the epoch —
/// never panics).
fn now_unix_secs() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A guard that sets `CRANELISP_AGENT_LOG` for the test body and restores the
    /// prior value on drop. Env mutation is process-global, so these tests run
    /// serially within this module's binary (one at a time per nextest process).
    struct LogEnvGuard(Option<String>);
    impl LogEnvGuard {
        fn set(path: &str) -> Self {
            let prior = std::env::var(LOG_VAR).ok();
            // SAFETY: unit test, single-threaded within this process at this point.
            unsafe { std::env::set_var(LOG_VAR, path) };
            LogEnvGuard(prior)
        }
        fn unset() -> Self {
            let prior = std::env::var(LOG_VAR).ok();
            unsafe { std::env::remove_var(LOG_VAR) };
            LogEnvGuard(prior)
        }
    }
    impl Drop for LogEnvGuard {
        fn drop(&mut self) {
            match &self.0 {
                Some(v) => unsafe { std::env::set_var(LOG_VAR, v) },
                None => unsafe { std::env::remove_var(LOG_VAR) },
            }
        }
    }

    // §27.2 — env-gate OFF (unset) ⇒ `record` is a no-op: no file is created.
    #[test]
    fn env_unset_is_no_op() {
        let _g = LogEnvGuard::unset();
        assert!(log_path().is_none(), "unset ⇒ logging off");
        // Recording while off must not panic and must write nothing (no path to
        // check — the absence of a panic + the gate predicate is the assertion).
        record(LogEvent::new("repair").symbol("x"));
    }

    // §27.2 — an EMPTY env value is also OFF (mirrors `trace`'s empty-is-off rule).
    #[test]
    fn env_empty_is_off() {
        let _g = LogEnvGuard::set("");
        assert!(log_path().is_none(), "empty ⇒ logging off");
    }

    // §27.3 — with the env set to a writable path, `record` appends a well-formed
    // JSON LINE carrying the stable greppable keys (`event` always; the optional
    // keys when set), and a second `record` APPENDS (persistent JSONL, 2 lines).
    #[test]
    fn record_appends_jsonl_with_stable_keys() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("activity.jsonl");
        let _g = LogEnvGuard::set(path.to_str().unwrap());

        record(
            LogEvent::new("repair")
                .symbol("helper")
                .module("user")
                .error_class("ParseError")
                .iteration(1),
        );
        record(LogEvent::new("pull").tool("source").symbol("target"));

        let log = std::fs::read_to_string(&path).expect("the log file must exist");
        let lines: Vec<&str> = log.lines().filter(|l| !l.trim().is_empty()).collect();
        assert_eq!(lines.len(), 2, "each record appends one line (JSONL): {log:?}");

        // Every line is a JSON object carrying the `event` key.
        for line in &lines {
            let v: serde_json::Value = serde_json::from_str(line).expect("each line is JSON");
            assert!(v.get("event").is_some(), "every record carries `event`: {line}");
        }

        // The repair line carries the full struggle-signal key set.
        let repair: serde_json::Value = serde_json::from_str(lines[0]).unwrap();
        assert_eq!(repair["event"], "repair");
        assert_eq!(repair["symbol"], "helper");
        assert_eq!(repair["module"], "user");
        assert_eq!(repair["error_class"], "ParseError");
        assert_eq!(repair["iteration"], 1);
        // Absent optional keys are OMITTED (skip_serializing_if), not null.
        assert!(repair.get("tool").is_none(), "absent key omitted: {}", lines[0]);

        // The pull line carries `tool` + `symbol`, no repair keys.
        let pull: serde_json::Value = serde_json::from_str(lines[1]).unwrap();
        assert_eq!(pull["event"], "pull");
        assert_eq!(pull["tool"], "source");
        assert!(pull.get("error_class").is_none());
    }

    // §27.2 — GRACEFUL: an unwritable path (file under a NONEXISTENT parent dir)
    // is swallowed — `record` does not panic, and no file is forced into being.
    #[test]
    fn unwritable_path_is_swallowed() {
        let dir = tempfile::tempdir().unwrap();
        let bad = dir.path().join("no-such-dir").join("activity.jsonl");
        let _g = LogEnvGuard::set(bad.to_str().unwrap());
        // Must NOT panic — the IO error is discarded.
        record(LogEvent::new("repair").symbol("helper").error_class("ParseError"));
        assert!(!bad.exists(), "an unwritable path must not be created: {bad:?}");
    }

    // The error-class deriver buckets the validator's `to_string()` error prefixes.
    #[test]
    fn classify_error_buckets_by_prefix() {
        assert_eq!(classify_error("parse error at 1:2: unbalanced"), "ParseError");
        assert_eq!(classify_error("type error at 3:4: mismatch"), "TypeError");
        assert_eq!(classify_error("codegen error: boom"), "CodegenError");
        assert_eq!(classify_error("something weird"), "OtherError");
    }

    // The symbol extractor pulls the defined name out of (possibly UNBALANCED)
    // defining forms, and returns None for a non-defining form.
    #[test]
    fn defined_symbol_extracts_name_even_when_unbalanced() {
        // Balanced and unbalanced `(defn helper …)` both yield `helper`.
        assert_eq!(defined_symbol("(defn helper [x] (add-i64 x x))").as_deref(), Some("helper"));
        assert_eq!(defined_symbol("(defn helper [x] (add-i64 x x)").as_deref(), Some("helper"));
        assert_eq!(defined_symbol("  (def k 1)").as_deref(), Some("k"));
        assert_eq!(defined_symbol("(defmacro m [x] x)").as_deref(), Some("m"));
        // A non-defining form has no defined symbol.
        assert_eq!(defined_symbol("(add-i64 1 2)"), None);
        assert_eq!(defined_symbol("not a form"), None);
    }
}
