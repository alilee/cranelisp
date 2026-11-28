use std::{fs, path::Path, process::Command};

const ALLOWED_SITES: [(&str, &str, &str); 1] = [(
    "crates/cranelisp-types/src/mono_expr.rs",
    "fn lenient_from_expr() { let x = t.unwrap_or(ConcreteType::Int); }",
    "fn lenient_from_expr() {}",
)];

fn allowed_sites(root: &Path) {
    for (relative, source, _) in ALLOWED_SITES {
        let path = root.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, source).unwrap();
    }
}

fn census(root: &Path) -> (bool, String) {
    // read-only on project_root: checker input and executable, no production writes.
    let checker =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/scripts/concrete_boundary_check.py");
    let out = Command::new("python3")
        .arg(checker)
        .arg("--root")
        .arg(root)
        .output()
        .unwrap();
    (
        out.status.success(),
        format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        ),
    )
}

// spec: AGENTS.md — Assurance: R18 concreteness cannot be fabricated or its witness discarded.
#[test]
fn s125_nc2_production_concrete_boundary_census() {
    // read-only on project_root: production source census.
    let (ok, report) = census(Path::new(env!("CARGO_MANIFEST_DIR")));
    assert!(ok, "{report}");
}

// spec: AGENTS.md — Assurance: an allowance must expire when its fabrication site is removed.
#[test]
fn s125_nc2_stale_allow_list_detection_proof() {
    let root = tempfile::tempdir().unwrap();
    allowed_sites(root.path());
    assert!(census(root.path()).0, "all allowances match actual sites");
    for (relative, source, without_fallback) in ALLOWED_SITES {
        let path = root.path().join(relative);
        for replacement in [Some(without_fallback), None] {
            match replacement {
                Some(text) => fs::write(&path, text).unwrap(),
                None => fs::remove_file(&path).unwrap(),
            }
            let (ok, report) = census(root.path());
            assert!(
                !ok && report.contains(&format!("{relative}: stale-allow-list"))
                    && report.lines().count() == 1,
                "removed fallback or file must expire only its allowance: {report}"
            );
            fs::write(&path, source).unwrap();
            let (ok, report) = census(root.path());
            assert!(ok, "restoring the allowed site clears the gate: {report}");
        }
    }
}

// spec: AGENTS.md — Assurance: each instrument must detect a planted fault and accept its absence.
#[test]
fn s125_nc2_detection_proof() {
    let root = tempfile::tempdir().unwrap();
    allowed_sites(root.path());
    let src = root.path().join("src");
    fs::create_dir(&src).unwrap();
    let path = src.join("main.rs");
    let sound = r#"
        fn check(t: &Type) { let witness = ConcreteType::from_type(t)?; }
        fn predicate(t: &Type) { if ConcreteType::from_type(t).is_ok() {} }
        // let _ = ConcreteType::from_type(t); Type::default();
        const TEXT: &str = r"Type::default()";
        #[cfg(test)] mod tests { fn fabricated() { Type::default(); } }
        #[cfg(test)] mod external;
    "#;
    fs::write(&path, sound).unwrap();
    fs::write(src.join("external.rs"), "fn unit() { Type::default(); }").unwrap();
    assert!(
        census(root.path()).0,
        "clean code, comments, literals and test modules excluded"
    );
    for (fault, reason) in [
        ("ConcreteType::from_type(t);", "unchecked-call"),
        ("ConcreteType::from_type(t).ok();", "unchecked-call"),
        ("let _ = ConcreteType::from_type(t);", "discarded-witness"),
        (
            "let x = ConcreteType::from_type(t).unwrap_or_default();",
            "erased-witness-error",
        ),
        ("let x = Type::default();", "type-default"),
        ("let x = ConcreteType::default();", "type-default"),
        ("let x = maybe.unwrap_or(Type::Int);", "fallback-type"),
        (
            "let x = maybe.unwrap_or_else(|| ConcreteType::Int);",
            "fallback-type",
        ),
        ("let x: Type = Default::default();", "typed-default"),
        (
            "let x: ConcreteType = maybe.unwrap_or_default();",
            "typed-default",
        ),
    ] {
        fs::write(&path, format!("{sound}\nfn fault() {{ {fault} }}")).unwrap();
        let (ok, report) = census(root.path());
        assert!(
            !ok && report.contains(reason),
            "plant {fault} must fail for {reason}: {report}"
        );
        fs::write(&path, sound).unwrap();
        assert!(census(root.path()).0, "negative leg after removing {fault}");
    }
    for (relative, source, _) in ALLOWED_SITES {
        let path = root.path().join(relative);
        fs::write(
            &path,
            format!("{source}\nfn elsewhere() {{ let x = t.unwrap_or(ConcreteType::Int); }}"),
        )
        .unwrap();
        let (ok, report) = census(root.path());
        assert!(
            !ok && report.contains("fallback-type") && !report.contains("stale-allow-list"),
            "allow-list cannot cover a neighboring site in {relative}: {report}"
        );
        fs::write(&path, source).unwrap();
        assert!(
            census(root.path()).0,
            "removing the neighboring plant clears the gate"
        );
    }
}
