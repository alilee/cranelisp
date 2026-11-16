use super::*;
use crate::test_child;

/// Values sharing one switch value, chosen to stress the encoding: empty,
/// separators, non-ASCII and a long value.
const AWKWARD_VALUES: [&str; 5] = ["", "1", "a=b;c\0d\ne", "zwölf ✓", "x\u{2028}"];

fn values_with(entries: &[(Switch, &str)]) -> Values {
    let mut values = Values::unset();
    for (switch, value) in entries {
        values.set(*switch, value);
    }
    values
}

/// A hand-built capture, so refusals can be planted without the encoder.
fn capture_bytes(format: u8, entries: &[(&[u8], &[u8])]) -> Vec<u8> {
    let mut bytes = vec![format];
    for (name, value) in entries {
        bytes.extend_from_slice(&(name.len() as u32).to_le_bytes());
        bytes.extend_from_slice(name);
        bytes.extend_from_slice(&(value.len() as u32).to_le_bytes());
        bytes.extend_from_slice(value);
    }
    bytes
}

// spec: design/intrinsics/process-lifecycle.md §2.2 — every member's value
// survives capture and install unchanged, alone and with the others unset.
#[test]
fn each_member_round_trips_alone() {
    for switch in Switch::ALL {
        for value in AWKWARD_VALUES {
            let values = values_with(&[(switch, value)]);
            let decoded = decode(&encode(&values)).expect("own capture decodes");
            assert_eq!(decoded, values, "{} = {value:?}", switch.name());
            for other in Switch::ALL.iter().filter(|&&o| o != switch) {
                assert_eq!(decoded.get(*other), None, "{} leaked", other.name());
            }
        }
    }
}

// spec: design/intrinsics/process-lifecycle.md §2.2 — a capture of every member
// and a capture of none both round trip.
#[test]
fn all_set_and_none_set_round_trip() {
    let all: Vec<(Switch, String)> = Switch::ALL
        .iter()
        .map(|s| (*s, format!("v-{}", s.name())))
        .collect();
    let refs: Vec<(Switch, &str)> = all.iter().map(|(s, v)| (*s, v.as_str())).collect();
    let values = values_with(&refs);
    assert_eq!(decode(&encode(&values)), Ok(values));
    assert_eq!(decode(&encode(&Values::unset())), Ok(Values::unset()));
}

// spec: design/intrinsics/process-lifecycle.md §2.4 — a baked value is stored
// verbatim, so it is observable in the executable's bytes.
#[test]
fn a_captured_value_is_stored_verbatim() {
    let bytes = encode(&values_with(&[(
        Switch::QuarantineMaxBytes,
        "sentinel-4096",
    )]));
    assert_eq!(bytes[0], FORMAT);
    assert!(
        bytes
            .windows(b"sentinel-4096".len())
            .any(|w| w == b"sentinel-4096")
    );
}

// spec: design/intrinsics/process-lifecycle.md §2.2 — the decoder refuses an
// unknown format and an unknown name rather than skipping them.
#[test]
fn unknown_format_and_unknown_name_are_refused() {
    assert_eq!(
        decode(&capture_bytes(FORMAT + 1, &[])),
        Err(DecodeError::UnknownFormat(FORMAT + 1))
    );
    // An agent key is not a member, so it cannot arrive as one.
    assert_eq!(
        decode(&capture_bytes(FORMAT, &[(b"CRANELISP_AGENT_KEY", b"k")])),
        Err(DecodeError::UnknownName("CRANELISP_AGENT_KEY".into()))
    );
    // Control: the same frame with a member name is accepted.
    assert_eq!(
        decode(&capture_bytes(FORMAT, &[(b"CRANELISP_DEGREE", b"k")])),
        Ok(values_with(&[(Switch::Degree, "k")]))
    );
}

// spec: design/intrinsics/process-lifecycle.md §2.2 — a malformed capture is
// refused, never partly applied.
#[test]
fn malformed_captures_are_refused() {
    assert_eq!(decode(&[]), Err(DecodeError::Empty));
    let whole = capture_bytes(FORMAT, &[(b"CRANELISP_DEGREE", b"3")]);
    for cut in 2..whole.len() {
        assert_eq!(
            decode(&whole[..cut]),
            Err(DecodeError::Truncated),
            "cut {cut}"
        );
    }
    assert_eq!(
        decode(&capture_bytes(FORMAT, &[(b"CRANELISP_DEGREE", b"\xff")])),
        Err(DecodeError::NotUtf8)
    );
    assert_eq!(
        decode(&capture_bytes(
            FORMAT,
            &[(b"CRANELISP_DEGREE", b"1"), (b"CRANELISP_DEGREE", b"2")]
        )),
        Err(DecodeError::Repeated(Switch::Degree))
    );
}

// spec: design/intrinsics/process-lifecycle.md §2.1 — member names are distinct,
// so a name identifies exactly one member.
#[test]
fn member_names_are_distinct() {
    let mut names: Vec<&str> = Switch::ALL.iter().map(|s| s.name()).collect();
    names.sort_unstable();
    names.dedup();
    assert_eq!(names.len(), MEMBER_COUNT);
}

// --- Child-process cells: the snapshot is process-wide, and a refusal exits.

fn run_child(name: &str, env: &[(&str, &str)]) -> test_child::Ending {
    test_child::run(&test_child::child_path(module_path!(), name), env)
}

#[track_caller]
fn assert_succeeded(ending: &test_child::Ending) {
    assert_eq!(ending.code, Some(0), "{}", ending.stderr);
}

#[track_caller]
fn assert_refused_with(ending: &test_child::Ending, detail: &str) {
    assert_eq!(ending.code, Some(1), "{}", ending.stderr);
    let expected = format!("error: runtime configuration: {INSTALL_SITE}: {detail}");
    assert!(
        ending.stderr.lines().any(|l| l == expected),
        "want {expected:?} in:\n{}",
        ending.stderr
    );
}

fn install_values(entries: &[(Switch, &str)]) {
    let bytes = encode(&values_with(entries));
    cranelisp_install_runtime_switches(bytes.as_ptr(), bytes.len());
}

#[test]
fn child_reads_the_environment_without_an_install() {
    if !test_child::selected("child_reads_the_environment_without_an_install") {
        return;
    }
    assert_eq!(value(Switch::Degree), Some("7"));
    assert!(!is_set(Switch::DriveMode));
}

// spec: design/intrinsics/process-lifecycle.md §2.1 — without an install, the
// switches come from the process environment.
#[test]
fn without_an_install_the_process_environment_answers() {
    assert_succeeded(&run_child(
        "child_reads_the_environment_without_an_install",
        &[("CRANELISP_DEGREE", "7")],
    ));
}

#[test]
fn child_installs_then_reads_only_the_capture() {
    if !test_child::selected("child_installs_then_reads_only_the_capture") {
        return;
    }
    install_values(&[(Switch::Degree, "3")]);
    assert_eq!(value(Switch::Degree), Some("3"));
    assert!(!is_set(Switch::DriveMode), "launch environment leaked");
    // A capture after the install re-exports the installed set.
    assert_eq!(
        decode(&capture_runtime_switches()),
        Ok(values_with(&[(Switch::Degree, "3")]))
    );
}

// spec: design/intrinsics/process-lifecycle.md §2.1 — once installed, the
// capture is the only source: the launch environment is not read.
#[test]
fn an_installed_capture_replaces_the_launch_environment() {
    assert_succeeded(&run_child(
        "child_installs_then_reads_only_the_capture",
        &[
            ("CRANELISP_DEGREE", "7"),
            ("CRANELISP_DRIVE_MODE", "server"),
        ],
    ));
}

#[test]
fn child_reads_then_installs() {
    if !test_child::selected("child_reads_then_installs") {
        return;
    }
    let _ = value(Switch::Degree);
    install_values(&[]);
    unreachable!("an install after a read must end the process");
}

// spec: design/intrinsics/process-lifecycle.md §2.1 — an install after any read
// ends the process with a located configuration fault.
#[test]
fn an_install_after_a_read_is_refused() {
    assert_refused_with(
        &run_child("child_reads_then_installs", &[]),
        "a runtime switch was read before the install",
    );
}

#[test]
fn child_installs_a_malformed_capture() {
    if !test_child::selected("child_installs_a_malformed_capture") {
        return;
    }
    let bytes = capture_bytes(FORMAT, &[(b"CRANELISP_AGENT_KEY", b"k")]);
    cranelisp_install_runtime_switches(bytes.as_ptr(), bytes.len());
    unreachable!("a malformed install must end the process");
}

// spec: design/intrinsics/process-lifecycle.md §2.2 — a malformed capture ends
// the process at install.
#[test]
fn a_malformed_install_is_refused() {
    assert_refused_with(
        &run_child("child_installs_a_malformed_capture", &[]),
        "malformed capture: unknown switch `CRANELISP_AGENT_KEY`",
    );
}

fn core_count() -> usize {
    std::thread::available_parallelism().map_or(1, |n| n.get())
}

/// A worker count the core count can never equal.
fn decoy_worker_count() -> String {
    (core_count() + 3).to_string()
}

#[test]
fn child_installs_then_counts_workers() {
    if !test_child::selected("child_installs_then_counts_workers") {
        return;
    }
    install_values(&[]);
    assert_eq!(rayon::current_num_threads(), core_count());
}

#[test]
fn child_counts_workers_without_an_install() {
    if !test_child::selected("child_counts_workers_without_an_install") {
        return;
    }
    assert_eq!(rayon::current_num_threads(), core_count() + 3);
}

// spec: design/intrinsics/process-lifecycle.md §2.3 — the install builds the
// pool with the core count, so `RAYON_NUM_THREADS` is not read. The control
// shows the decoy would otherwise take effect.
#[test]
fn the_installed_pool_uses_the_core_count() {
    let decoy = decoy_worker_count();
    assert_succeeded(&run_child(
        "child_installs_then_counts_workers",
        &[("RAYON_NUM_THREADS", &decoy)],
    ));
    assert_succeeded(&run_child(
        "child_counts_workers_without_an_install",
        &[("RAYON_NUM_THREADS", &decoy)],
    ));
}

// --- The source census: no environment read outside this module.

/// Sources that are compiled only for tests and may read the environment.
const TEST_ONLY_SOURCES: [&str; 2] = ["test_child.rs", "drop/rc_balance.rs"];

/// The lines of `source` that read the process environment, ignoring
/// comments. Exempt files yield nothing.
fn environment_reads(relative_path: &str, source: &str) -> Vec<String> {
    let exempt = relative_path == "runtime_switches.rs"
        || relative_path.ends_with("tests.rs")
        || TEST_ONLY_SOURCES.contains(&relative_path);
    if exempt {
        return Vec::new();
    }
    source
        .lines()
        .enumerate()
        .filter_map(|(i, line)| {
            let code = line.split("//").next().unwrap_or("");
            let reads = ["env::var", "env::{", "getenv"]
                .iter()
                .any(|p| code.contains(p));
            reads.then(|| format!("{relative_path}:{}: {}", i + 1, line.trim()))
        })
        .collect()
}

fn crate_sources() -> Vec<(String, String)> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut pending = vec![root.clone()];
    let mut sources = Vec::new();
    while let Some(dir) = pending.pop() {
        for entry in std::fs::read_dir(&dir).expect("read src dir") {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().is_some_and(|e| e == "rs") {
                let relative = path.strip_prefix(&root).unwrap().to_string_lossy();
                let text = std::fs::read_to_string(&path).expect("read source");
                sources.push((relative.replace('\\', "/"), text));
            }
        }
    }
    sources
}

// spec: design/intrinsics/process-lifecycle.md §2.1 — no code in the crate
// reads the process environment except this module.
#[test]
fn no_environment_read_outside_the_switch_module() {
    let sources = crate_sources();
    assert!(
        sources.iter().any(|(p, _)| p == "alloc.rs"),
        "scan found the crate"
    );
    let reads: Vec<String> = sources
        .iter()
        .flat_map(|(path, text)| environment_reads(path, text))
        .collect();
    assert!(reads.is_empty(), "environment reads:\n{}", reads.join("\n"));
}

// spec: design/intrinsics/process-lifecycle.md §2.5 — detection proof: a planted
// read in each spelling is found; a comment, this module and a test file are not.
#[test]
fn the_census_detects_a_planted_read() {
    for planted in [
        "    let on = std::env::var_os(\"CRANELISP_X\").is_some();",
        "    let v = env::var(\"CRANELISP_X\");",
        "use std::env::{self};",
        "    let p = unsafe { libc::getenv(c\"X\".as_ptr()) };",
    ] {
        let source = format!("fn f() {{\n{planted}\n}}\n");
        assert_eq!(
            environment_reads("alloc.rs", &source),
            [format!("alloc.rs:2: {}", planted.trim())],
            "{planted}"
        );
        assert!(environment_reads("runtime_switches.rs", &source).is_empty());
        assert!(environment_reads("alloc/tests.rs", &source).is_empty());
    }
    let commented = "/// reads `std::env::var(\"X\")`\n// std::env::var_os\nfn f() {}\n";
    assert!(environment_reads("alloc.rs", commented).is_empty());
}
