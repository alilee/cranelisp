//! Module evidence for the environment supply: `design/int/environment.md` §4
//! rows 1–5 (`tests/plan/s123-evidence-delta.md` §3.4, E-7).

use super::*;

fn env_of(pairs: &[(&str, &str)]) -> impl Fn(&str) -> Option<OsString> {
    let map: BTreeMap<String, OsString> = pairs
        .iter()
        .map(|(k, v)| (k.to_string(), OsString::from(v)))
        .collect();
    move |key| map.get(key).cloned()
}

fn entries(text: &str) -> Vec<Entry> {
    parse(text).expect("well-formed file")
}

fn pairs(entries: &[Entry]) -> Vec<(&str, &str)> {
    entries
        .iter()
        .map(|e| (e.key.as_str(), e.value.as_str()))
        .collect()
}

fn project_file(text: &str) -> EnvFile {
    EnvFile {
        path: PathBuf::from("/p/.env"),
        entries: entries(text),
    }
}

fn user_file(text: &str) -> EnvFile {
    EnvFile {
        path: PathBuf::from("/u/env"),
        entries: entries(text),
    }
}

fn values<'a>(chosen: &BTreeMap<&'a str, Chosen<'a>>) -> BTreeMap<&'a str, &'a str> {
    chosen
        .iter()
        .map(|(&key, c)| (key, c.entry.value.as_str()))
        .collect()
}

fn malformed_line(text: &str) -> Malformed {
    parse(text).expect_err("malformed file")
}

// ── Row 1: admission ────────────────────────────────────────────────────

// spec: repl/spec/00-cli-invocation.md §0.8 — admitted keys
#[test]
fn prefix_keys_and_the_three_named_keys_are_admitted() {
    for key in [
        "CRANELISP_RC_STATS",
        "CRANELISP_AGENT_PROVIDER",
        "CRANELISP_UNDOCUMENTED_SWITCH",
        "NO_COLOR",
        "ANTHROPIC_API_KEY",
        "OLLAMA_API_BASE_URL",
    ] {
        assert!(is_admitted(key), "{key} must be admitted");
    }
}

// spec: repl/spec/00-cli-invocation.md §0.8 — other keys and loader controls are ignored
#[test]
fn foreign_keys_and_loader_controls_are_not_admitted() {
    for key in [
        "PATH",
        "LD_LIBRARY_PATH",
        "HOME",
        "XDG_CONFIG_HOME",
        "CRANELISP",
        "cranelisp_rc_stats",
        "CRANELISP_NO_ENV",
        "CRANELISP_ENV_FILE",
        "CRANELISP_USER_ENV_FILE",
    ] {
        assert!(!is_admitted(key), "{key} must not be admitted");
    }
}

// spec: repl/spec/00-cli-invocation.md §0.8 — a file line cannot set a loader control
#[test]
fn resolve_drops_foreign_keys_and_controls_from_files() {
    let project = project_file("PATH=/evil\nCRANELISP_NO_ENV=1\nCRANELISP_X=1\n");
    let chosen = resolve(&env_of(&[]), &project, None);
    assert_eq!(
        values(&chosen).into_iter().collect::<Vec<_>>(),
        vec![("CRANELISP_X", "1")]
    );
}

// ── Row 2: precedence ───────────────────────────────────────────────────

// spec: repl/spec/00-cli-invocation.md §0.8 — process > project > user
#[test]
fn process_beats_project_beats_user() {
    let project = project_file("CRANELISP_A=project\nCRANELISP_B=project\n");
    let user = user_file("CRANELISP_A=user\nCRANELISP_B=user\nCRANELISP_C=user\n");
    let chosen = resolve(
        &env_of(&[("CRANELISP_A", "process")]),
        &project,
        Some(&user),
    );
    let chosen = values(&chosen);
    assert_eq!(chosen.get("CRANELISP_A"), None, "the process value is kept");
    assert_eq!(chosen.get("CRANELISP_B"), Some(&"project"));
    assert_eq!(chosen.get("CRANELISP_C"), Some(&"user"));
}

// spec: repl/spec/00-cli-invocation.md §0.8 — an empty process value is defined
#[test]
fn an_empty_process_value_still_wins() {
    let project = project_file("CRANELISP_AGENT_PROVIDER=stub\n");
    let user = user_file("CRANELISP_AGENT_PROVIDER=stub\n");
    let chosen = resolve(
        &env_of(&[("CRANELISP_AGENT_PROVIDER", "")]),
        &project,
        Some(&user),
    );
    assert!(
        chosen.is_empty(),
        "an empty process value is not unset: {chosen:?}"
    );
}

// spec: design/int/environment.md §2.2 step 4 — last occurrence within a file wins
#[test]
fn the_last_occurrence_within_a_file_wins() {
    let project = project_file("CRANELISP_A=first\nCRANELISP_A=second\n");
    let user = user_file("CRANELISP_B=first\nCRANELISP_B=second\n");
    let chosen = resolve(&env_of(&[]), &project, Some(&user));
    let chosen = values(&chosen);
    assert_eq!(chosen.get("CRANELISP_A"), Some(&"second"));
    assert_eq!(chosen.get("CRANELISP_B"), Some(&"second"));
}

// spec: design/int/environment.md §2.2 — the chosen value keeps its file and line
#[test]
fn the_chosen_assignment_keeps_its_file_and_line() {
    let project = project_file("# c\nCRANELISP_A=p\n");
    let user = user_file("CRANELISP_A=u\n\nCRANELISP_B=\"two\nlines\"\nCRANELISP_C=after\n");
    let chosen = resolve(&env_of(&[]), &project, Some(&user));
    let at = |key: &str| {
        let c = &chosen[key];
        (c.path.to_str().unwrap(), c.entry.line)
    };
    assert_eq!(at("CRANELISP_A"), ("/p/.env", 2));
    assert_eq!(
        at("CRANELISP_B"),
        ("/u/env", 3),
        "a quoted value is located at its first line"
    );
    assert_eq!(at("CRANELISP_C"), ("/u/env", 5));
}

// ── Row 3: syntax ───────────────────────────────────────────────────────

// spec: repl/spec/00-cli-invocation.md §0.8 — blank lines, comments, export, whitespace
#[test]
fn comments_blank_lines_export_and_whitespace() {
    let text = "\n# a comment\n   # indented comment\nexport A=1\n  B  =  two words  \n\texport\tC=3\nexport=4\n";
    assert_eq!(
        pairs(&entries(text)),
        vec![("A", "1"), ("B", "two words"), ("C", "3"), ("export", "4")]
    );
}

// spec: repl/spec/00-cli-invocation.md §0.8 — ` #` begins an inline comment
#[test]
fn inline_comments_end_unquoted_values() {
    let text = "A=value # comment\nB=no#comment\nC= # only comment\nD=#leading\n";
    assert_eq!(
        pairs(&entries(text)),
        vec![
            ("A", "value"),
            ("B", "no#comment"),
            ("C", ""),
            ("D", "#leading")
        ]
    );
}

// spec: repl/spec/00-cli-invocation.md §0.8 — single quotes are literal
#[test]
fn single_quoted_values_are_literal() {
    let text = "A='a \\n \"b\" # c ${D}' # comment\nB=''\n";
    assert_eq!(
        pairs(&entries(text)),
        vec![("A", "a \\n \"b\" # c ${D}"), ("B", "")]
    );
}

// spec: repl/spec/00-cli-invocation.md §0.8 — double quotes span lines and know three escapes
#[test]
fn double_quoted_values_span_lines_with_escapes() {
    let text = "A=\"one\ntwo \\\"q\\\" \\\\ \\n # kept\" # comment\nB=after\n";
    assert_eq!(
        pairs(&entries(text)),
        vec![("A", "one\ntwo \"q\" \\ \n # kept"), ("B", "after")]
    );
}

// spec: repl/spec/00-cli-invocation.md §0.8 — no interpolation
#[test]
fn interpolation_syntax_stays_literal() {
    let text = "A=${HOME}/x\nB=\"$HOME ${B}\"\n";
    assert_eq!(
        pairs(&entries(text)),
        vec![("A", "${HOME}/x"), ("B", "$HOME ${B}")]
    );
}

// spec: repl/spec/00-cli-invocation.md §0.8 — CRLF line endings read as LF
#[test]
fn crlf_line_endings_are_accepted() {
    assert_eq!(
        pairs(&entries("A=1\r\nB=2\r\n")),
        vec![("A", "1"), ("B", "2")]
    );
}

// ── Row 4: malformed and unreadable ─────────────────────────────────────

const SECRET: &str = "S123_UNIT_SECRET";

fn assert_located_without_value(text: &str, line: usize, reason: MalformedReason) {
    let m = malformed_line(text);
    assert_eq!(m, Malformed { line, reason });
    let message = SupplyError {
        path: PathBuf::from("/p/.env"),
        kind: SupplyErrorKind::Malformed(m),
    }
    .to_string();
    assert!(message.contains(&format!("/p/.env:{line}:")), "{message}");
    assert!(
        !message.contains(SECRET),
        "the message leaks a value: {message}"
    );
}

// spec: repl/spec/00-cli-invocation.md §0.8 — an unterminated quote is malformed, any key
#[test]
fn unterminated_quotes_are_located_errors() {
    for key in ["FOREIGN", "ANTHROPIC_API_KEY"] {
        assert_located_without_value(
            &format!("CRANELISP_A=1\n{key}=\"{SECRET}\nmore\n"),
            2,
            MalformedReason::UnterminatedQuote,
        );
        assert_located_without_value(
            &format!("{key}='{SECRET}\n"),
            1,
            MalformedReason::UnterminatedQuote,
        );
    }
}

// spec: repl/spec/00-cli-invocation.md §0.8 — an invalid key is malformed, any key
#[test]
fn invalid_keys_are_located_errors() {
    for text in [
        format!("1ANTHROPIC_API_KEY={SECRET}\n"),
        format!("FOR-EIGN={SECRET}\n"),
        format!("=\"{SECRET}\"\n"),
        format!("CRANELISP X={SECRET}\n"),
    ] {
        assert_located_without_value(&text, 1, MalformedReason::InvalidKey);
    }
}

// spec: repl/spec/00-cli-invocation.md §0.8 — a non-assignment line is malformed
#[test]
fn non_assignment_lines_are_located_errors() {
    assert_located_without_value(
        &format!("CRANELISP_A=1\n\n{SECRET}\n"),
        3,
        MalformedReason::NotAnAssignment,
    );
    assert_located_without_value(
        &format!("ANTHROPIC_API_KEY='{SECRET}' trailing\n"),
        1,
        MalformedReason::TextAfterQuote,
    );
}

// spec: design/int/environment.md §2.7 — a value the environment cannot hold is a located,
// value-free startup error, decided before any value is set (review R1)
#[test]
fn a_chosen_nul_value_refuses_the_whole_plan_without_its_value() {
    let project = project_file(&format!(
        "CRANELISP_A=fine\n# c\nANTHROPIC_API_KEY={SECRET}\0suffix\nCRANELISP_Z=fine\n"
    ));
    let chosen = resolve(&env_of(&[]), &project, None);
    let error = settable(&chosen).expect_err("a NUL value cannot be set");
    assert_eq!(
        error,
        SupplyError {
            path: PathBuf::from("/p/.env"),
            kind: SupplyErrorKind::Unrepresentable {
                line: 3,
                key: "ANTHROPIC_API_KEY".to_string(),
            },
        }
    );
    let message = error.to_string();
    assert!(message.contains("/p/.env:3:"), "{message}");
    assert!(
        !message.contains(SECRET),
        "the message leaks a value: {message}"
    );
    assert!(
        !message.contains("suffix"),
        "the message leaks a value: {message}"
    );
}

// spec: design/int/environment.md §2.7 — only a value that would be set is refused (review R1)
#[test]
fn a_nul_value_that_is_never_set_is_not_refused() {
    let project = project_file(&format!(
        "FOREIGN=a\0b\nCRANELISP_A=x\0y\nCRANELISP_A=later\nCRANELISP_B=p\0q\n"
    ));
    let chosen = resolve(&env_of(&[("CRANELISP_B", "process")]), &project, None);
    assert_eq!(settable(&chosen), Ok(vec![("CRANELISP_A", "later")]));
}

// spec: repl/spec/00-cli-invocation.md §0.8 — an unreadable file is a startup error naming it
#[test]
fn a_directory_or_non_utf8_file_is_unreadable() {
    let dir = tempfile::tempdir().unwrap();
    let directory = dir.path().join(".env");
    std::fs::create_dir(&directory).unwrap();
    let binary = dir.path().join("env");
    std::fs::write(&binary, b"ANTHROPIC_API_KEY=\xff\xfe\n").unwrap();
    for path in [&directory, &binary] {
        let error = load(path).expect_err("unreadable");
        assert!(
            matches!(error.kind, SupplyErrorKind::Unreadable(_)),
            "{error:?}"
        );
        let message = error.to_string();
        assert!(message.contains(&path.display().to_string()), "{message}");
    }
}

// spec: repl/spec/00-cli-invocation.md §0.8 — a missing optional file is silent
#[test]
fn a_missing_file_is_silent() {
    let dir = tempfile::tempdir().unwrap();
    let absent = dir.path().join("absent");
    assert_eq!(load(&absent).map(|f| f.entries), Ok(Vec::new()));
    let through_a_file = dir.path().join("file");
    std::fs::write(&through_a_file, "").unwrap();
    assert_eq!(
        load(&through_a_file.join("env")).map(|f| f.entries),
        Ok(Vec::new())
    );
}

// ── Row 5: location ─────────────────────────────────────────────────────

fn root() -> PathBuf {
    PathBuf::from("/project")
}

// spec: repl/spec/00-cli-invocation.md §0.8 — XDG_CONFIG_HOME over HOME
#[test]
fn xdg_config_home_relocates_the_user_file() {
    let both = locate(
        &env_of(&[("XDG_CONFIG_HOME", "/xdg"), ("HOME", "/home/u")]),
        &root(),
    );
    assert_eq!(
        both,
        Some(Locations {
            project: PathBuf::from("/project/.env"),
            user: Some(PathBuf::from("/xdg/cranelisp/env")),
        })
    );
    for env in [
        vec![("HOME", "/home/u")],
        vec![("XDG_CONFIG_HOME", ""), ("HOME", "/home/u")],
    ] {
        assert_eq!(
            locate(&env_of(&env), &root()).and_then(|l| l.user),
            Some(PathBuf::from("/home/u/.config/cranelisp/env")),
            "{env:?}"
        );
    }
    assert_eq!(locate(&env_of(&[]), &root()).and_then(|l| l.user), None);
}

// spec: repl/spec/00-cli-invocation.md §0.8 — each override replaces only its own file
#[test]
fn overrides_replace_only_their_own_file() {
    let base = [("XDG_CONFIG_HOME", "/xdg")];
    let project = locate(
        &env_of(&[base[0], ("CRANELISP_ENV_FILE", "/alt/p")]),
        &root(),
    );
    assert_eq!(
        project,
        Some(Locations {
            project: PathBuf::from("/alt/p"),
            user: Some(PathBuf::from("/xdg/cranelisp/env")),
        })
    );
    let user = locate(
        &env_of(&[base[0], ("CRANELISP_USER_ENV_FILE", "/alt/u")]),
        &root(),
    );
    assert_eq!(
        user,
        Some(Locations {
            project: PathBuf::from("/project/.env"),
            user: Some(PathBuf::from("/alt/u")),
        })
    );
}

// spec: repl/spec/00-cli-invocation.md §0.8 — CRANELISP_NO_ENV=1 reads neither file
#[test]
fn no_env_disables_both_files() {
    assert_eq!(
        locate(
            &env_of(&[("CRANELISP_NO_ENV", "1"), ("HOME", "/h")]),
            &root()
        ),
        None
    );
    assert!(
        locate(&env_of(&[("CRANELISP_NO_ENV", "0")]), &root()).is_some(),
        "only the value 1 disables"
    );
}

// spec: repl/spec/00-cli-invocation.md §0.8 — only exactly `1` disables the files
#[test]
fn no_env_values_other_than_exactly_one_leave_loading_enabled() {
    for value in ["true", "", " 1", "1 ", "01", "0"] {
        assert_eq!(
            locate(
                &env_of(&[("CRANELISP_NO_ENV", value), ("HOME", "/h")]),
                &root()
            ),
            Some(Locations {
                project: PathBuf::from("/project/.env"),
                user: Some(PathBuf::from("/h/.config/cranelisp/env")),
            }),
            "CRANELISP_NO_ENV={value:?} must not disable"
        );
    }
}

// spec: repl/spec/00-cli-invocation.md §0.8 — no whitespace is required before a `#`
// after a closing quote
#[test]
fn a_comment_may_follow_a_closing_quote_without_whitespace() {
    let text = "A='v'#c\nB=\"v\"#c\nC='w'\t# c\n";
    assert_eq!(
        pairs(&entries(text)),
        vec![("A", "v"), ("B", "v"), ("C", "w")]
    );
}

// spec: repl/spec/00-cli-invocation.md §0.8 — text after a closing quote is malformed,
// for both quote kinds
#[test]
fn text_after_a_closing_quote_is_a_located_error() {
    for key in ["FOREIGN", "ANTHROPIC_API_KEY"] {
        assert_located_without_value(
            &format!("CRANELISP_A=1\n{key}=\"{SECRET}\" trailing\n"),
            2,
            MalformedReason::TextAfterQuote,
        );
        assert_located_without_value(
            &format!("{key}=\"two\n{SECRET}\"x\n"),
            1,
            MalformedReason::TextAfterQuote,
        );
        assert_located_without_value(
            &format!("{key}='{SECRET}'x\n"),
            1,
            MalformedReason::TextAfterQuote,
        );
    }
}

// spec: repl/spec/00-cli-invocation.md §0.8 — the NUL refusal names the key, never the value
#[test]
fn the_nul_refusal_message_names_the_key_without_its_value() {
    let project = project_file(&format!("ANTHROPIC_API_KEY={SECRET}\0suffix\n"));
    let chosen = resolve(&env_of(&[]), &project, None);
    let message = settable(&chosen)
        .expect_err("a NUL value cannot be set")
        .to_string();
    assert!(message.contains("/p/.env:1:"), "{message}");
    assert!(message.contains("ANTHROPIC_API_KEY"), "{message}");
    for fragment in [SECRET, "suffix", "\0"] {
        assert!(
            !message.contains(fragment),
            "the message leaks a value: {message:?}"
        );
    }
}
