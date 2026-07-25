//! Origin-anchored CI tripwire for the "mode-gating cancer" class.
//!
//! A language-semantic decision — an error, a rejection, or a name/type
//! resolution — must NEVER be conditioned on REPL vs `--run`/`--link`. The
//! S102 /arch audit established that this class has a TINY, CLOSED set of
//! ORIGIN expressions in `src/` (the mode bit read at a branch), and that
//! naive detection fails because the bit is laundered through renamed bool
//! params (`reject_def_over_import`, …) far from the origin — which is how
//! 0514 evaded review. This guard greps the closed origin set and fails when a
//! NEW, un-allowlisted origin appears. It is a tripwire for the CLASS, not a
//! checker of existing code: the grep flags the origins; the reviewer applies
//! the acid test ("are we doing the same work on two paths because we branched
//! early?").
//!
//! Ship the origin grep FIRST (this file). A true interprocedural boolean-taint
//! lint is later hardening, deliberately NOT built here — the laundering
//! supplement below is only the cheap param-name grep, not taint tracking.
//!
// spec: (CI guard — no single spec §) — acid-test rationale is
//       feedback_investigate_suspected_dual_path (S98 0499 / S102 0484) and
//       FIXME 0517 (filed S102, resolved by this file). REPL/`--run`/`--link`
//       must be ONE shared path; divergence is a serious red flag.

use std::process::Command;

/// The closed mode-bit ORIGIN regex, re-enumerated S102 after 0514/0516
/// removed the `additive` flag (the set is smaller than the FIXME example).
/// `run_mode *==` currently matches nothing (the code reads via the
/// `.is_repl()` / `.populates_introspection()` helpers) but stays in the
/// pattern as a tripwire for future direct `RunMode` comparisons.
const ORIGIN_RE: &str = r"== *ModuleStrategy::(Additive|Replace)|\.is_repl\(\)|\.populates_introspection\(\)|run_mode *==";

/// Allowlist: `(file-suffix, code-token)` — every hit MUST match one entry.
/// Each origin was cleared by the S102 /arch mode-gating audit; a hit that
/// matches none is a NEW origin and fails the test.
const ALLOW_ORIGINS: &[(&str, &str)] = &[
    // platform layout-hash gate — user-ratified `platform-interface.md §5.5.4`:
    // REPL WarnAndLoad vs batch Refuse is a build-integrity gate (the REPL is
    // the only schema-regen path), NOT program-meaning. Do NOT unify to uniform.
    ("src/process_form/platform.rs", "run_mode.is_repl()"),
    // process_form Additive/Replace — a shared spine that late-narrows on a real
    // discriminant (post-0516 `ensure_prelude_bit` single-sourced); not a
    // per-mode meaning divergence. /arch cleared.
    ("src/process_form.rs", "strategy == ModuleStrategy::Replace"),
    // lifecycle policy gate — allocate the introspection map under REPL only
    // (batch never populates it); allocate-or-not, not program-meaning.
    (
        "src/session_v4/lifecycle.rs",
        ".populates_introspection()",
    ),
    // lifecycle policy gate — the shutdown-settle burn-down runs REPL-only;
    // allocate/settle-or-not, not program-meaning.
    ("src/session_v4/lifecycle.rs", "run_mode.is_repl() &&"),
];

/// Cheap flag-laundering supplement (0517): a mode bit renamed into a bool
/// fn-param crossing a `fn` boundary is exactly how 0514 hid. Each param shape
/// must trace to an allowlisted origin above. NOT the interprocedural taint
/// lint — just the param-name grep.
const PARAM_RE: &str = r"\b(reject_[a-z_]*|refuse_[a-z_]*|is_repl|interactive) *: *bool";

/// Allowlist for laundered bool params: `(file-suffix, code-token)`.
const ALLOW_PARAMS: &[(&str, &str)] = &[
    // layout_hash_gate's `is_repl` discriminator — traces to the
    // `platform-interface.md §5.5.4` origin allowlisted above.
    ("src/process_form/platform.rs", "is_repl: bool"),
];

/// grep `src/` and return `(file, code)` hits, dropping comment-only lines and
/// test files (test code is not shipped mode-gating behaviour).
fn grep_src(pattern: &str) -> Vec<(String, String)> {
    let root = env!("CARGO_MANIFEST_DIR");
    let out = Command::new("grep")
        .args(["-rnE", "--include=*.rs", pattern, "src/"])
        .current_dir(root)
        .output()
        .expect("grep must be available");
    let text = String::from_utf8_lossy(&out.stdout);
    let mut hits = Vec::new();
    for line in text.lines() {
        // grep -n output: `path:lineno:code` (code may contain `:` / `::`).
        let mut parts = line.splitn(3, ':');
        let file = parts.next().unwrap_or("").to_string();
        let _lineno = parts.next().unwrap_or("");
        let code = parts.next().unwrap_or("").to_string();
        if code.trim_start().starts_with("//") {
            continue; // doc/line comment — describes a bit, is not a branch
        }
        if file.ends_with("tests.rs") {
            continue; // #[cfg(test)] module file — not shipped behaviour
        }
        hits.push((file, code));
    }
    hits
}

fn check(pattern: &str, allow: &[(&str, &str)], what: &str) {
    let hits = grep_src(pattern);
    // (1) Every live hit is allowlisted — trips on a NEW origin.
    let offenders: Vec<String> = hits
        .iter()
        .filter(|(f, c)| {
            !allow
                .iter()
                .any(|(af, at)| f.ends_with(af) && c.contains(at))
        })
        .map(|(f, c)| format!("  {}: {}", f, c.trim()))
        .collect();
    assert!(
        offenders.is_empty(),
        "NEW un-allowlisted {what} detected. A language-semantic decision \
         conditioned on REPL vs --run/--link is the 'mode-gating cancer' class \
         (0514 evaded review this way). Apply the acid test — are two paths \
         doing the same work because of an early mode branch? — then either fix \
         the duplication or add an allowlist entry WITH a one-line rationale in \
         tests/mode_gating_guard.rs:\n{}",
        offenders.join("\n"),
    );
    // (2) Every allowlist entry still matches a live hit — trips on pattern rot
    // or a silently-removed origin (keep the allowlist honest).
    let stale: Vec<String> = allow
        .iter()
        .filter(|(af, at)| !hits.iter().any(|(f, c)| f.ends_with(af) && c.contains(at)))
        .map(|(af, at)| format!("  {af}  <<{at}>>"))
        .collect();
    assert!(
        stale.is_empty(),
        "Allowlisted {what} no longer matches any live hit — the origin moved/\
         was removed, or the grep pattern rotted. Re-enumerate and update the \
         allowlist in tests/mode_gating_guard.rs:\n{}",
        stale.join("\n"),
    );
}

#[test]
fn mode_gating_origins_are_allowlisted() {
    check(ORIGIN_RE, ALLOW_ORIGINS, "mode-bit origin(s)");
}

#[test]
fn laundered_mode_bit_params_trace_to_allowlisted_origin() {
    check(PARAM_RE, ALLOW_PARAMS, "laundered mode-bit bool param(s)");
}
