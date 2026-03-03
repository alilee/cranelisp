use std::path::Path;

/// Strip timing prefixes (e.g. "0+1ms; ") from REPL prompts so e2e tests
/// are not sensitive to non-deterministic timing values.
fn strip_timing(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for line in s.lines() {
        if !result.is_empty() {
            result.push('\n');
        }
        // Match pattern: digits "+" digits "ms; " at start of line
        let trimmed = line.trim_start();
        if let Some(rest) = strip_timing_prefix(trimmed) {
            let leading = &line[..line.len() - trimmed.len()];
            result.push_str(leading);
            result.push_str(rest);
        } else {
            result.push_str(line);
        }
    }
    result
}

fn strip_timing_prefix(s: &str) -> Option<&str> {
    let bytes = s.as_bytes();
    let mut i = 0;
    // digits before '+'
    if i >= bytes.len() || !bytes[i].is_ascii_digit() {
        return None;
    }
    while i < bytes.len() && bytes[i].is_ascii_digit() {
        i += 1;
    }
    // '+'
    if i >= bytes.len() || bytes[i] != b'+' {
        return None;
    }
    i += 1;
    // digits after '+'
    if i >= bytes.len() || !bytes[i].is_ascii_digit() {
        return None;
    }
    while i < bytes.len() && bytes[i].is_ascii_digit() {
        i += 1;
    }
    // "ms; "
    if s[i..].starts_with("ms; ") {
        Some(&s[i + 4..])
    } else {
        None
    }
}

/// Run a single e2e test: pipe .cl file as stdin to the REPL, compare stdout to .out file.
fn run_e2e_test(cl_file: &Path) {
    let out_file = cl_file.with_extension("out");
    assert!(
        out_file.exists(),
        "Missing .out file for {:?}",
        cl_file.file_name().unwrap()
    );

    let input = std::fs::read_to_string(cl_file).unwrap();
    let expected = std::fs::read_to_string(&out_file).unwrap();

    // Set up a temp directory with symlinks to lib/ and target/debug/ so the REPL
    // can find the prelude and platform DLLs.
    let dir = tempfile::tempdir().unwrap();
    let lib_src = Path::new(env!("CARGO_MANIFEST_DIR")).join("lib");
    std::os::unix::fs::symlink(&lib_src, dir.path().join("lib")).unwrap();
    let target_debug = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/debug");
    if target_debug.exists() {
        std::fs::create_dir_all(dir.path().join("target")).unwrap();
        std::os::unix::fs::symlink(&target_debug, dir.path().join("target/debug")).unwrap();
    }

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_cranelisp"))
        .current_dir(dir.path())
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            use std::io::Write;
            child.stdin.take().unwrap().write_all(input.as_bytes())?;
            child.wait_with_output()
        })
        .unwrap();

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(
        strip_timing(stdout.trim()),
        strip_timing(expected.trim()),
        "\n=== E2E test failed: {:?} ===\n--- expected ---\n{}\n--- actual ---\n{}\n--- stderr ---\n{}",
        cl_file.file_name().unwrap(),
        expected.trim(),
        stdout.trim(),
        stderr.trim(),
    );
}

/// Discover and run all .cl/.out pairs in tests/e2e/.
#[test]
fn e2e_tests() {
    let e2e_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/e2e");
    if !e2e_dir.exists() {
        return;
    }

    let mut entries: Vec<_> = std::fs::read_dir(&e2e_dir)
        .unwrap()
        .filter_map(|e| {
            let path = e.ok()?.path();
            if path.extension().map(|e| e == "cl").unwrap_or(false) {
                Some(path)
            } else {
                None
            }
        })
        .collect();
    entries.sort();

    if entries.is_empty() {
        return;
    }

    let mut failures = Vec::new();
    for path in &entries {
        if let Err(e) = std::panic::catch_unwind(|| run_e2e_test(path)) {
            failures.push((path.clone(), e));
        }
    }

    if !failures.is_empty() {
        for (path, _) in &failures {
            eprintln!("FAILED: {:?}", path.file_name().unwrap());
        }
        panic!("{} e2e test(s) failed", failures.len());
    }
}
