//! M-3 documentation maintenance check. Metadata and limits: tests/AGENTS.md.
use std::path::Path;
use std::process::{Command, Output};

fn check(docs: &Path) -> Output {
    Command::new("python3")
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/scripts/user_samples.py"))
        .arg("--docs")
        .arg(docs)
        .arg("--binary")
        .arg(env!("CARGO_BIN_EXE_cranelisp"))
        .output()
        .expect("python3 must run the documentation sample checker")
}

fn diagnostic(output: &Output) -> String {
    format!(
        "status: {}\n{}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

// spec: AGENTS.md §Design Principles — the user/ sample harness stdlib exception
#[test]
fn user_documentation_samples_match_the_compiler() {
    // read-only on project_root; all compiler writes go to checker-owned tmpdirs.
    let output = check(&Path::new(env!("CARGO_MANIFEST_DIR")).join("user"));
    assert!(output.status.success(), "{}", diagnostic(&output));
}

const SOUND: &str = r#"<!-- sample: {"kind":"definition","group":"double"} -->
```clojure
(defn double "An error: in a docstring is not a diagnostic" [x]
  (* x 2))
```
<!-- sample: {"kind":"repl","group":"double"} -->
```text
> (double 21)
:primitives/Int 42
> missing
Error: type error at 0..7: undefined variable: missing
```
<!-- sample: {"kind":"repl","group":"fixture","files":{"math.cl":"(defn value [] 17)\n"}} -->
```
> (import [math [value]])
> (value)
:primitives/Int 17
> /sh printf '%s\n' '(defn value [] 29)' > math.cl
[updated: math.cl]
[updated: user.cl]
> (value)
:primitives/Int 29
```
<!-- sample: {"kind":"repl"} -->
```
cranelisp REPL — type /help for help
agent: dormant (/ask shows what to set)
> double
Error: type error at 0..6: undefined variable: double
> 9
:primitives/Int 9
```
<!-- sample: {"kind":"illustrative","reason":"Abbreviated diagnostic, not exact output"} -->
```
Error: ...
```
"#;

// spec: AGENTS.md §Assurance — a maintenance instrument must detect its planted faults
#[test]
fn sample_checker_detects_wrong_output_and_unclassified_fences_then_clears() {
    let corpus = tempfile::tempdir().unwrap();
    let guide = corpus.path().join("guide.md");
    std::fs::write(&guide, SOUND).unwrap();
    let sound = check(corpus.path());
    assert!(sound.status.success(), "{}", diagnostic(&sound));
    assert!(String::from_utf8_lossy(&sound.stdout).contains("Executed 3 fresh groups"));
    println!("SOUND\n{}", diagnostic(&sound));

    std::fs::write(
        &guide,
        SOUND.replace(":primitives/Int 42", ":primitives/Int 43"),
    )
    .unwrap();
    let wrong = check(corpus.path());
    assert!(!wrong.status.success(), "{}", diagnostic(&wrong));
    assert!(String::from_utf8_lossy(&wrong.stderr).contains("expected output mismatch"));
    println!("PLANTED WRONG EXPECTED LINE\n{}", diagnostic(&wrong));

    std::fs::write(&guide, format!("{SOUND}\n```clojure\n(+ 1 2)\n```\n")).unwrap();
    let unclassified = check(corpus.path());
    assert!(
        !unclassified.status.success(),
        "{}",
        diagnostic(&unclassified)
    );
    assert!(String::from_utf8_lossy(&unclassified.stderr).contains("unclassified fence"));
    println!("PLANTED UNCLASSIFIED BLOCK\n{}", diagnostic(&unclassified));

    std::fs::write(&guide, SOUND).unwrap();
    let restored = check(corpus.path());
    assert!(restored.status.success(), "{}", diagnostic(&restored));
    println!("RESTORED\n{}", diagnostic(&restored));
}
