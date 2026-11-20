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

macro_rules! document_samples {
    ($($name:ident => $path:literal),+ $(,)?) => {
        const DOCUMENTS: &[&str] = &[$($path),+];
        $(
            // spec: AGENTS.md §Design Principles — the user/ sample harness stdlib exception
            #[test]
            fn $name() {
                // read-only on project_root; compiler writes go to checker-owned tmpdirs.
                let output = check(&Path::new(env!("CARGO_MANIFEST_DIR")).join("user").join($path));
                assert!(output.status.success(), "{}", diagnostic(&output));
                println!("{}", diagnostic(&output));
            }
        )+
    };
}

document_samples! {
    samples_entry_guidance => "AGENTS.md",
    samples_cli_reference => "cli-reference.md",
    samples_getting_started => "getting-started.md",
    samples_trait_impl_diagnostics => "errors/trait-impl-diagnostics.md",
    samples_bitwise => "guide/bitwise.md",
    samples_concurrency => "guide/concurrency.md",
    samples_constructors => "guide/constructors.md",
    samples_field_accessors => "guide/field-accessors.md",
    samples_functions => "guide/functions.md",
    samples_live_development => "guide/live-development.md",
    samples_macros => "guide/macros.md",
    samples_modules => "guide/modules.md",
    samples_parallel_collections => "guide/parallel-collections.md",
    samples_syntax_command => "guide/syntax-command.md",
    samples_testing => "guide/testing.md",
    samples_tracing => "guide/tracing.md",
    samples_traits => "guide/traits.md",
    samples_using_platforms => "guide/using-platforms.md",
    samples_writing_platforms => "guide/writing-platforms.md",
}

fn markdown_documents(root: &Path) -> std::collections::BTreeSet<String> {
    fn visit(root: &Path, dir: &Path, found: &mut std::collections::BTreeSet<String>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                visit(root, &path, found);
            } else if path.extension().is_some_and(|ext| ext == "md") {
                found.insert(
                    path.strip_prefix(root)
                        .unwrap()
                        .to_str()
                        .unwrap()
                        .to_owned(),
                );
            }
        }
    }
    let mut found = std::collections::BTreeSet::new();
    visit(root, root, &mut found);
    found
}

// spec: AGENTS.md §Assurance — every document must keep an executing sample cell
#[test]
fn document_sample_cells_cover_every_markdown_document() {
    let selected = DOCUMENTS.iter().map(|path| (*path).to_owned()).collect();
    // read-only on project_root.
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("user");
    assert_eq!(
        markdown_documents(&root),
        selected,
        "update document_samples! when adding or removing a guide"
    );
}

// spec: AGENTS.md §Assurance — the selection guard must detect an omitted document
#[test]
fn document_selection_detects_an_unallocated_guide_then_clears() {
    let corpus = tempfile::tempdir().unwrap();
    std::fs::write(corpus.path().join("guide.md"), "guide").unwrap();
    let selected = ["guide.md".to_owned()].into_iter().collect();
    assert_eq!(markdown_documents(corpus.path()), selected);
    let added = corpus.path().join("nested");
    std::fs::create_dir(&added).unwrap();
    std::fs::write(added.join("new.md"), "new guide").unwrap();
    assert_ne!(markdown_documents(corpus.path()), selected);
    std::fs::remove_file(added.join("new.md")).unwrap();
    assert_eq!(markdown_documents(corpus.path()), selected);
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

    let sibling = corpus.path().join("sibling.md");
    std::fs::write(&sibling, SOUND).unwrap();
    let selected = check(&sibling);
    assert!(selected.status.success(), "{}", diagnostic(&selected));
    assert!(String::from_utf8_lossy(&selected.stdout).contains("Census: 1 documents"));
    assert!(String::from_utf8_lossy(&selected.stdout).contains("Executed 3 fresh groups"));
    let selected_wrong = check(&guide);
    assert!(
        !selected_wrong.status.success(),
        "{}",
        diagnostic(&selected_wrong)
    );
    assert!(String::from_utf8_lossy(&selected_wrong.stderr).contains("expected output mismatch"));
    std::fs::remove_file(sibling).unwrap();

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
