mod helpers;
use helpers::e2e::{CrOutput, Cranelisp};

const PROGRAM: &str = "(import [primitives [*]])\n(defn main [] (Pure (vec-len [10 20 30])))\n(defn test-ok [] None)\n";

fn base() -> Cranelisp {
    let c = base_without_xdg();
    let root = c.tmpdir_path();
    c.env("XDG_CONFIG_HOME", root.join("xdg").to_str().unwrap())
}

fn base_without_xdg() -> Cranelisp {
    let c = Cranelisp::new()
        .without_agent_provider()
        .env_remove("XDG_CONFIG_HOME")
        .env_remove("CRANELISP_NO_ENV")
        .env_remove("CRANELISP_ENV_FILE")
        .env_remove("CRANELISP_USER_ENV_FILE")
        .env_remove("CRANELISP_RC_STATS")
        .env_remove("CRANELISP_SPARK_STATS")
        .env_remove("CRANELISP_S123_PROBE")
        .env_remove("S123_FOREIGN")
        .env_remove("CRANELISP_AGENT_PROVIDER")
        .file("user.cl", PROGRAM)
        .file("stub.txt", "done: S123_STUB_REPLY\n");
    let root = c.tmpdir_path();
    c.env("HOME", root.join("home").to_str().unwrap()).env(
        "CRANELISP_AGENT_STUB_SCRIPT",
        root.join("stub.txt").to_str().unwrap(),
    )
}

fn stats(out: &CrOutput, expected: bool, clause: &str) {
    assert_eq!(
        out.linked_stderr
            .as_deref()
            .unwrap_or(&out.stderr)
            .contains("[RC_STATS]"),
        expected,
        "{clause}: [RC_STATS] presence; stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

fn probe(c: Cranelisp) -> CrOutput {
    c.stdin("/sh printf 'PROBE=<%s> FOREIGN=<%s> DISABLE=<%s> PROJECT=<%s> USER=<%s>\\n' \"$CRANELISP_S123_PROBE\" \"$S123_FOREIGN\" \"$CRANELISP_NO_ENV\" \"$CRANELISP_ENV_FILE\" \"$CRANELISP_USER_ENV_FILE\"\n")
        .output().assert_ok()
}

// spec: AGENTS.md §Assurance — E-0 declaration.
// spec: repl/spec/00-cli-invocation.md §0.8 — E-0 declaration.
#[test]
fn suite_declares_file_isolation_and_empty_provider() {
    assert_eq!(
        std::env::var("CRANELISP_NO_ENV").as_deref(),
        Ok("1"),
        "E-0 declaration: CRANELISP_NO_ENV must be 1"
    );
    assert_eq!(
        std::env::var("CRANELISP_AGENT_PROVIDER").as_deref(),
        Ok(""),
        "E-0 declaration: CRANELISP_AGENT_PROVIDER must be set and empty"
    );
}

// spec: repl/spec/00-cli-invocation.md §0.8 — E-0 inherited file leg.
#[test]
fn suite_inherited_environment_does_not_read_files() {
    let c = inherited_files();
    let out = c.run("user.cl").output().assert_exit(3);
    stats(&out, false, "E-0 isolation file leg");
}

fn inherited_files() -> Cranelisp {
    let c = Cranelisp::new()
        .without_agent_provider()
        .file("user.cl", PROGRAM)
        .file("stub.txt", "done: S123_STUB_REPLY\n");
    let root = c.tmpdir_path();
    let contents = format!(
        "CRANELISP_RC_STATS=1\nCRANELISP_AGENT_PROVIDER=stub\nCRANELISP_AGENT_STUB_SCRIPT={}\n",
        root.join("stub.txt").display()
    );
    c.file(".env", &contents)
        .file("xdg/cranelisp/env", &contents)
        .file("home/.config/cranelisp/env", &contents)
        .env("HOME", root.join("home").to_str().unwrap())
        .env("XDG_CONFIG_HOME", root.join("xdg").to_str().unwrap())
}

// spec: repl/spec/00-cli-invocation.md §0.6.1 and §0.8 — E-0 inherited banner leg.
#[test]
fn suite_inherited_environment_keeps_agent_dormant() {
    let out = inherited_files().output().assert_ok();
    assert!(
        out.stdout.lines().any(|l| l.contains("dormant")),
        "E-0 isolation banner leg: dormant state; stdout={}",
        out.stdout
    );
    assert!(
        !out.stdout.lines().any(|l| l.contains("active")),
        "E-0 isolation banner leg: no active state; stdout={}",
        out.stdout
    );
}

macro_rules! file_stats_case {
    ($name:ident, $mode:ident) => {
        // spec: repl/spec/00-cli-invocation.md §0.8 — E-1 file supply in each mode.
        #[test]
        fn $name() {
            let expected_exit = if stringify!($mode) == "run" { 3 } else { 0 };
            let control = base().$mode("user.cl").output().assert_exit(expected_exit);
            stats(&control, false, "E-1 no-file control");
            let out = base()
                .file(".env", "CRANELISP_RC_STATS=1\n")
                .$mode("user.cl")
                .output()
                .assert_exit(expected_exit);
            stats(&out, true, "E-1 project file supplies switch");
        }
    };
}
file_stats_case!(project_file_supplies_run_switch, run);
file_stats_case!(project_file_supplies_test_switch, test);
// spec: repl/spec/00-cli-invocation.md §0.8 — E-1 REPL face.
#[test]
fn project_file_supplies_repl_switch() {
    stats(
        &base().output().assert_ok(),
        false,
        "E-1 no-file REPL control",
    );
    stats(
        &base()
            .file(".env", "CRANELISP_RC_STATS=1\n")
            .output()
            .assert_ok(),
        true,
        "E-1 REPL supply",
    );
}

fn precedence() -> Cranelisp {
    base()
        .file(".env", "CRANELISP_AGENT_PROVIDER=bogus1\n")
        .file("xdg/cranelisp/env", "CRANELISP_AGENT_PROVIDER=bogus2\n")
}
fn banner(out: &CrOutput, state: &str, detail: &str, clause: &str) {
    assert!(
        out.stdout
            .split("user>")
            .next()
            .unwrap()
            .lines()
            .any(|l| l.contains(state) && l.contains(detail)),
        "{clause}: banner must contain {state:?} and {detail:?}; stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}
fn dormant_notice(out: &CrOutput, detail: &str, clause: &str) {
    banner(out, "dormant", "", clause);
    let notice = out.stdout.split_once("user>").expect("first REPL prompt").1;
    assert!(
        notice.contains(detail),
        "{clause}: /ask notice must contain {detail:?}; stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}
// spec: repl/spec/00-cli-invocation.md §0.8 — E-2 process beats both files.
#[test]
fn process_provider_precedes_both_files() {
    banner(
        &precedence()
            .env("CRANELISP_AGENT_PROVIDER", "stub")
            .output()
            .assert_ok(),
        "active",
        "stub",
        "E-2 process precedence",
    );
}
// spec: repl/spec/00-cli-invocation.md §0.8 — E-2 project beats user.
#[test]
fn project_provider_precedes_user_file() {
    dormant_notice(
        &precedence()
            .stdin("/ask explain this\n")
            .output()
            .assert_ok(),
        "bogus1",
        "E-2 project precedence",
    );
}
// spec: repl/spec/00-cli-invocation.md §0.8 — E-2 user fallback.
#[test]
fn user_provider_supplies_fallback() {
    dormant_notice(
        &base()
            .file("xdg/cranelisp/env", "CRANELISP_AGENT_PROVIDER=bogus2\n")
            .stdin("/ask explain this\n")
            .output()
            .assert_ok(),
        "bogus2",
        "E-2 user fallback",
    );
}
// spec: repl/spec/00-cli-invocation.md §0.8 — E-2 empty is a defined value.
#[test]
fn empty_process_provider_precedes_files() {
    dormant_notice(
        &precedence()
            .env("CRANELISP_AGENT_PROVIDER", "")
            .stdin("/ask explain this\n")
            .output()
            .assert_ok(),
        "CRANELISP_AGENT_PROVIDER",
        "E-2 empty precedence",
    );
}
// spec: repl/spec/00-cli-invocation.md §0.8 — E-3 location discriminator.
#[test]
fn xdg_file_precedes_home_file() {
    let out = probe(
        base()
            .file("xdg/cranelisp/env", "CRANELISP_S123_PROBE=xdg\n")
            .file("home/.config/cranelisp/env", "CRANELISP_S123_PROBE=home\n"),
    );
    assert!(
        out.stdout.contains("PROBE=<xdg>"),
        "E-3 XDG supplies probe and HOME is ignored: {}",
        out.stdout
    );
}
// spec: repl/spec/00-cli-invocation.md §0.8 — E-3 HOME fallback.
#[test]
fn home_file_supplies_without_xdg() {
    let out =
        probe(base_without_xdg().file("home/.config/cranelisp/env", "CRANELISP_S123_PROBE=home\n"));
    assert!(
        out.stdout.contains("PROBE=<home>"),
        "E-3 HOME fallback supplies probe: {}",
        out.stdout
    );
}
// spec: repl/spec/00-cli-invocation.md §0.8 — E-4 admission, observed by a child.
#[test]
fn admitted_probe_reaches_shell_but_foreign_key_does_not() {
    let inherited = probe(base().env("CRANELISP_S123_PROBE", "y"));
    assert!(
        inherited.stdout.contains("PROBE=<y> FOREIGN=<>"),
        "E-4 process-value shell control: {}",
        inherited.stdout
    );
    let control = probe(base());
    assert!(
        control.stdout.contains("PROBE=<> FOREIGN=<>"),
        "E-4 clean shell control: {}",
        control.stdout
    );
    let out = probe(base().file(".env", "S123_FOREIGN=x\nCRANELISP_S123_PROBE=y\n"));
    assert!(
        out.stdout.contains("FOREIGN=<>"),
        "E-4 foreign key excluded: {}",
        out.stdout
    );
    assert!(
        out.stdout.contains("PROBE=<y>"),
        "E-4 admitted key inherited: {}",
        out.stdout
    );
}
// spec: repl/spec/00-cli-invocation.md §0.8 — E-5 project redirect keeps user source.
#[test]
fn project_override_redirects_only_project_file() {
    let c = base()
        .file(".env", "CRANELISP_S123_PROBE=wrong\n")
        .file("alternate", "CRANELISP_S123_PROBE=project\n")
        .file("xdg/cranelisp/env", "CRANELISP_RC_STATS=1\n");
    let path = c.tmpdir_path().join("alternate");
    let out = probe(c.env("CRANELISP_ENV_FILE", path.to_str().unwrap()));
    assert!(
        out.stdout.contains("PROBE=<project>"),
        "E-5 project redirect: {}",
        out.stdout
    );
    stats(&out, true, "E-5 project redirect retains user file");
}
// spec: repl/spec/00-cli-invocation.md §0.8 — E-5 user redirect keeps project source.
#[test]
fn user_override_redirects_only_user_file() {
    let c = base()
        .file(".env", "CRANELISP_RC_STATS=1\n")
        .file("xdg/cranelisp/env", "CRANELISP_S123_PROBE=wrong\n")
        .file("alternate", "CRANELISP_S123_PROBE=user\n");
    let path = c.tmpdir_path().join("alternate");
    let out = probe(c.env("CRANELISP_USER_ENV_FILE", path.to_str().unwrap()));
    assert!(
        out.stdout.contains("PROBE=<user>"),
        "E-5 user redirect: {}",
        out.stdout
    );
    stats(&out, true, "E-5 user redirect retains project file");
}
// spec: repl/spec/00-cli-invocation.md §0.8 — E-5 disable both sources.
#[test]
fn disable_control_reads_neither_file() {
    let out = probe(
        base()
            .env("CRANELISP_NO_ENV", "1")
            .file(".env", "CRANELISP_S123_PROBE=project\n")
            .file("xdg/cranelisp/env", "CRANELISP_RC_STATS=1\n"),
    );
    assert!(
        out.stdout.contains("PROBE=<>"),
        "E-5 disabled project: {}",
        out.stdout
    );
    stats(&out, false, "E-5 disabled user");
}
// spec: repl/spec/00-cli-invocation.md §0.8 — E-5 files cannot choose controls.
#[test]
fn file_supplied_loader_controls_are_ignored() {
    let c = base();
    let contents = format!(
        "CRANELISP_NO_ENV=1\nCRANELISP_ENV_FILE={}\nCRANELISP_USER_ENV_FILE={}\nCRANELISP_S123_PROBE=project\n",
        c.tmpdir_path().join("alternate").display(),
        c.tmpdir_path().join("alternate").display()
    );
    let out = probe(
        c.file(".env", &contents)
            .file("alternate", "CRANELISP_S123_PROBE=wrong\n")
            .file("xdg/cranelisp/env", "CRANELISP_RC_STATS=1\n"),
    );
    assert!(
        out.stdout.contains("DISABLE=<> PROJECT=<> USER=<>"),
        "E-5 file-supplied controls must not enter child environment: {}",
        out.stdout
    );
    assert!(
        out.stdout.contains("PROBE=<project>"),
        "E-5 file cannot redirect/disable: {}",
        out.stdout
    );
    stats(&out, true, "E-5 file cannot suppress user supply");
}

fn refusal(repl: bool, directory: bool) {
    let c = base().file(
        ".env",
        if directory {
            ""
        } else {
            "ANTHROPIC_API_KEY=S123_SECRET_DO_NOT_PRINT\nFOREIGN=\"unterminated\n"
        },
    );
    let path = c.tmpdir_path().join(".env");
    if directory {
        std::fs::remove_file(&path).unwrap();
        std::fs::create_dir(&path).unwrap();
    }
    let out = if repl {
        c.output()
    } else {
        c.run("user.cl").output()
    };
    assert!(
        !format!("{}{}", out.stdout, out.stderr).contains("S123_SECRET_DO_NOT_PRINT"),
        "E-6 secret must not escape"
    );
    assert_eq!(
        out.status.code(),
        Some(1),
        "E-6 startup refusal exits 1: stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    assert!(
        out.stderr.contains(".env"),
        "E-6 refusal names file: {}",
        out.stderr
    );
    if !directory {
        assert!(
            regex::Regex::new(r"(?:\.env[:( ]+2(?:[:) ]|$)|\bline\s+2\b)")
                .unwrap()
                .is_match(&out.stderr),
            "E-6 malformed foreign line locates line 2: {}",
            out.stderr
        );
    }
}
macro_rules! refusal_case {
    ($name:ident, $repl:expr, $directory:expr) => {
        // spec: repl/spec/00-cli-invocation.md §0.8 — E-6 malformed/unreadable startup refusal.
        #[test]
        fn $name() {
            refusal($repl, $directory);
        }
    };
}
refusal_case!(malformed_foreign_key_refuses_run, false, false);
refusal_case!(malformed_foreign_key_refuses_repl, true, false);
refusal_case!(directory_env_refuses_run, false, true);
refusal_case!(directory_env_refuses_repl, true, true);

fn review_startup() -> Cranelisp {
    base()
        .env_remove("ANTHROPIC_API_KEY")
        .env_remove("CRANELISP_AGENT_MODEL")
        .env("CRANELISP_AGENT_PROVIDER", "stub")
        .file("home/.keep", "")
        .file("xdg/.keep", "")
        .cli_flag("--no-color")
        .stdin("/quit\n")
}

// spec: repl/spec/00-cli-invocation.md §0.8 — representable credential control.
#[test]
fn credential_without_nul_starts_normally() {
    review_startup()
        .cli_flag("--no-agent")
        .file(
            ".env",
            "# credential on line 2\nANTHROPIC_API_KEY=S123-REVIEW-SENTINELsuffix\n",
        )
        .output()
        .assert_ok();
}

// spec: repl/spec/00-cli-invocation.md §0.8 — located startup refusal.
// defect: class=silent-accept locus=src/env_files.rs found=S123 owner=/dev fixed=S123/efd09d29
// A NUL credential formerly reached the setter and panicked with the value.
#[test]
fn credential_with_nul_neg_refuses_without_disclosure_or_panic() {
    let out = review_startup()
        .expects_exit_without_reading_stdin()
        .cli_flag("--no-agent")
        .file(
            ".env",
            "# credential on line 2\nANTHROPIC_API_KEY=S123-REVIEW-SENTINEL\0suffix\n",
        )
        .output();
    let located_line = regex::Regex::new(r"(?:\.env[:( ]+2(?:[:) ]|$)|\bline\s+2\b)")
        .unwrap()
        .is_match(&out.stderr);
    // Evaluate every clause even when the first one fails.
    assert_eq!(
        (
            !out.stdout.contains("S123-REVIEW-SENTINEL"),
            !out.stderr.contains("S123-REVIEW-SENTINEL"),
            matches!(out.status.code(), Some(code) if code != 0 && code != 101),
            out.stderr.contains(".env"),
            located_line,
        ),
        (true, true, true, true, true),
        "R1: (sentinel absent stdout, sentinel absent stderr, nonzero non-101 nonsignal exit, file named, line 2 named); status={} stdout={:?} stderr={:?}",
        out.status,
        out.stdout,
        out.stderr
    );
}

fn model_startup(model: &str) -> CrOutput {
    review_startup()
        .file(".env", &format!("CRANELISP_AGENT_MODEL=\"{model}\"\n"))
        .output()
        .assert_ok()
}

fn one_physical_state_line(out: &CrOutput) {
    let (prologue, _) = out.stdout.split_once("user>").expect("first REPL prompt");
    // The timing prefix shares the prompt's physical line.
    let (complete_lines, _) = prologue.rsplit_once('\n').expect("lines before prompt");
    let lines: Vec<_> = complete_lines.lines().collect();
    let banner = lines
        .iter()
        .position(|line| line.contains("cranelisp REPL"))
        .expect("REPL banner");
    let state_lines: Vec<_> = lines[banner + 1..]
        .iter()
        .filter(|line| !line.trim().is_empty())
        .collect();
    assert_eq!(
        state_lines.len(),
        1,
        "R2: exactly one physical state line between banner and first prompt; stdout={:?}",
        out.stdout
    );
    assert!(
        state_lines[0].contains("active")
            && state_lines[0].contains("stub")
            && state_lines[0].contains("review-model"),
        "R2: active state names stub and model: {state_lines:?}"
    );
}

// spec: repl/spec/00-cli-invocation.md §0.6.1 — single-line model control.
#[test]
fn single_line_model_has_one_physical_state_line() {
    one_physical_state_line(&model_startup("review-model"));
}

// spec: repl/spec/00-cli-invocation.md §0.6.1 — one startup state line.
// R2: src/agent_activation.rs banner interpolates a physical newline; fix owner=/dev.
// QA handoff: assign a defect class for configuration text splitting presentation.
#[test]
fn multiline_model_neg_does_not_forge_second_physical_state_line() {
    one_physical_state_line(&model_startup("review-model\nagent: off"));
}

fn linked_switch(key: &str, at_link: bool, at_run: bool) -> CrOutput {
    let spark_program = "(import [primitives [*]])\n(defn ping [n d] (if (le-i64 n 0) (div-i64 10 d) (pong (sub-i64 n 1) d)))\n(defn pong [n d] (if (le-i64 n 0) (div-i64 10 d) (ping (sub-i64 n 1) d)))\n(defn compute [d] (let [a (ping 3 d) c (ping a 1)] c))\n(defn main [] (Pure (sub-i64 (compute 1) 7)))\n";
    let program = if key == "CRANELISP_SPARK_STATS" {
        spark_program
    } else {
        PROGRAM
    };
    let run_values = [(key, "1")];
    let c = base()
        .file("user.cl", program)
        .env("CRANELISP_NO_ENV", "1")
        .link_then_run("user.cl")
        .linked_environment(if at_run { &run_values } else { &[] });
    let c = if at_link {
        c.env(key, "1")
    } else {
        c.env_remove(key)
    };
    c.output().assert_exit(3)
}
// spec: repl/spec/00-cli-invocation.md §0.8 — B-1/B-2 spark-counter capability control.
#[test]
fn linked_spark_counter_fixture_reports_stats_when_armed() {
    let out = linked_switch("CRANELISP_SPARK_STATS", true, true);
    let stderr = out.linked_stderr.as_ref().unwrap();
    assert!(
        stderr.contains("[SPARK_STATS]"),
        "B spark positive control must report executable counters: {stderr}"
    );
}
macro_rules! baked_case {
    ($name:ident, $key:expr, $marker:expr, $link:expr, $run:expr) => {
        // spec: repl/spec/00-cli-invocation.md §0.8 — B-1/B-2 link-time source, never launch-time.
        #[test]
        fn $name() {
            let control = linked_switch($key, false, false);
            assert!(
                !control.linked_stderr.as_ref().unwrap().contains($marker),
                "B clean linked control: {}",
                control.stderr
            );
            let out = linked_switch($key, $link, $run);
            assert_eq!(
                out.linked_stderr.as_ref().unwrap().contains($marker),
                $link,
                "B baked switch {} link={} run={}: {}",
                $key,
                $link,
                $run,
                out.stderr
            );
        }
    };
}
baked_case!(
    link_time_rc_stats_survives_empty_launch,
    "CRANELISP_RC_STATS",
    "[RC_STATS]",
    true,
    false
);
baked_case!(
    launch_only_rc_stats_is_inert,
    "CRANELISP_RC_STATS",
    "[RC_STATS]",
    false,
    true
);
baked_case!(
    link_time_spark_stats_survives_empty_launch,
    "CRANELISP_SPARK_STATS",
    "[SPARK_STATS]",
    true,
    false
);
baked_case!(
    launch_only_spark_stats_is_inert,
    "CRANELISP_SPARK_STATS",
    "[SPARK_STATS]",
    false,
    true
);
// spec: repl/spec/00-cli-invocation.md §0.8 — B-3 file supply survives relocation and cleared launch.
#[test]
fn project_file_switch_bakes_for_relocated_run() {
    let out = base()
        .file(".env", "CRANELISP_RC_STATS=1\n")
        .link_then_run("user.cl")
        .linked_environment(&[])
        .linked_directory("elsewhere")
        .output()
        .assert_exit(3);
    stats(&out, true, "B-3 file-supplied baked switch");
}
// spec: repl/spec/00-cli-invocation.md §0.8 — B-4 keys excluded, runtime value positive control.
#[test]
fn linked_bytes_exclude_agent_secrets_and_include_runtime_value() {
    let out = base()
        .env("CRANELISP_NO_ENV", "1")
        .env("ANTHROPIC_API_KEY", "S123_ANTHROPIC_SECRET_67ae")
        .env("CRANELISP_AGENT_KEY", "S123_AGENT_SECRET_9bd1")
        .env("CRANELISP_QUARANTINE_MAX_BYTES", "7319042681")
        .link("user.cl")
        .output()
        .assert_ok();
    let bytes = std::fs::read(out.tmpdir.join("user")).unwrap();
    for secret in ["S123_ANTHROPIC_SECRET_67ae", "S123_AGENT_SECRET_9bd1"] {
        assert!(
            !bytes.windows(secret.len()).any(|w| w == secret.as_bytes()),
            "B-4 agent key must not be baked: {secret}"
        );
    }
    assert!(
        bytes.windows(10).any(|w| w == b"7319042681"),
        "B-4 positive control: runtime switch sentinel must be baked as plain text"
    );
}
