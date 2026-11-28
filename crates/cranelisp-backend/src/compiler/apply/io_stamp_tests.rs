//! The `Pure` node's glue-word layout and its closed set of writers
//! (`design/backend/non-concrete-release-contract.md` §5.3;
//! `design/backend/io-trampoline.md` §2.1).

use super::PURE_GLUE_ABS_OFFSET;
use cranelisp_intrinsics::alloc::HeapAdt;
use std::collections::BTreeMap;
use std::path::Path;

// spec: design/backend/non-concrete-release-contract.md §5.1/§5.3 — field 0 remains the
// language payload and the hidden witness is field 1 at absolute offset 32.
#[test]
fn pure_hidden_field_extends_the_payload_without_moving_field_zero() {
    assert_eq!(HeapAdt::field_offset(0), 24);
    assert_eq!(PURE_GLUE_ABS_OFFSET, HeapAdt::field_offset(1) as i64);
    assert_eq!(PURE_GLUE_ABS_OFFSET, 32);
    assert_eq!(HeapAdt::payload_size(2), 24);
}

/// The two tokens that name a `Pure` node write.
const PURE_TOKENS: [&str; 2] = ["IO_TAG_PURE", "PURE_GLUE_ABS_OFFSET"];

/// Every non-test source file of this crate, relative path to its full text.
/// Test files are skipped by name; inline test modules are left for
/// [`pure_write_sites`] to exclude, so a plant in the text passes through the
/// same exclusion as the file on disk.
fn production_sources() -> BTreeMap<String, String> {
    fn walk(root: &Path, dir: &Path, out: &mut BTreeMap<String, String>) {
        for entry in std::fs::read_dir(dir).expect("read source dir") {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                walk(root, &path, out);
                continue;
            }
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if !name.ends_with(".rs")
                || name.ends_with("tests.rs")
                || name == "test_support.rs"
                || name == "test_child.rs"
            {
                continue;
            }
            let text = std::fs::read_to_string(&path).expect("read source");
            let rel = path.strip_prefix(root).expect("under src").display();
            out.insert(rel.to_string(), text);
        }
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut out = BTreeMap::new();
    walk(&root, &root, &mut out);
    out
}

/// `text` without the bodies of its inline `#[cfg(test)] mod … {` blocks.
/// A block ends at its first column-0 `}` line, which rustfmt places only at
/// the module's close. `#[cfg(test)] mod name;` declarations are kept.
fn strip_inline_test_module(text: &str) -> String {
    let mut kept = String::with_capacity(text.len());
    let mut lines = text.split_inclusive('\n').peekable();
    while let Some(line) = lines.next() {
        let opens_inline_module = line.trim_end() == "#[cfg(test)]"
            && lines
                .peek()
                .is_some_and(|next| next.starts_with("mod ") && next.trim_end().ends_with('{'));
        if !opens_inline_module {
            kept.push_str(line);
            continue;
        }
        lines.next();
        for body in lines.by_ref() {
            if body.trim_end() == "}" {
                break;
            }
        }
    }
    kept
}

/// `(token, file) -> occurrences` for each [`PURE_TOKENS`] token outside
/// inline test modules.
fn pure_write_sites(sources: &BTreeMap<String, String>) -> BTreeMap<(String, String), usize> {
    let mut sites = BTreeMap::new();
    for (file, text) in sources {
        let text = strip_inline_test_module(text);
        for token in PURE_TOKENS {
            let count = text.matches(token).count();
            if count > 0 {
                sites.insert((token.to_string(), file.clone()), count);
            }
        }
    }
    sites
}

/// The admitted sites. `io_nodes.rs`: `emit_pure_node`, the one node
/// builder. `apply.rs`: `IO_TAG_PURE` once, as `stamp_platform_return`'s tag
/// comparison; `PURE_GLUE_ABS_OFFSET` at its definition, its pin and the
/// stamp's store.
fn admitted_sites() -> BTreeMap<(String, String), usize> {
    [
        (("IO_TAG_PURE", "compiler/io_nodes.rs"), 1),
        (("IO_TAG_PURE", "compiler/apply.rs"), 1),
        (("PURE_GLUE_ABS_OFFSET", "compiler/apply.rs"), 3),
    ]
    .into_iter()
    .map(|((token, file), n)| ((token.to_string(), file.to_string()), n))
    .collect()
}

// spec: design/backend/non-concrete-release-contract.md §5.3; io-trampoline.md
// §2.1 — the `Pure` tag is stored as a node tag only by the one emitter, and
// the glue word at `PURE_GLUE_ABS_OFFSET` is written only by the
// platform-return adoption stamp.
#[test]
fn pure_node_writes_have_exactly_the_emitter_and_the_adoption_stamp() {
    assert_eq!(pure_write_sites(&production_sources()), admitted_sites());
}

// spec: design/backend/non-concrete-release-contract.md §5.3 — detection
// proof: a planted second node-tag store, or a second glue-word store, fails
// the census, including one after an inline test module; one planted inside a
// test module does not.
#[test]
fn pure_write_census_detects_a_planted_second_store() {
    let clean = production_sources();
    assert_eq!(pure_write_sites(&clean), admitted_sites(), "negative leg");

    let mut second_tag = clean.clone();
    second_tag
        .get_mut("compiler/control_flow/fn_as_value.rs")
        .expect("fn_as_value.rs is production")
        .push_str("\nfn planted() { emit(cranelisp_platform::IO_TAG_PURE as usize); }\n");
    assert_ne!(pure_write_sites(&second_tag), admitted_sites());

    let mut second_glue = clean.clone();
    second_glue
        .get_mut("compiler/apply.rs")
        .expect("apply.rs is production")
        .push_str("\nfn planted() { store(v, node, PURE_GLUE_ABS_OFFSET as i32); }\n");
    assert_ne!(pure_write_sites(&second_glue), admitted_sites());

    // `io_nodes.rs` ends in an inline test module; production code after it
    // still counts.
    let after_test_module = |plant: &str| {
        let mut sources = clean.clone();
        let io_nodes = sources
            .get_mut("compiler/io_nodes.rs")
            .expect("io_nodes.rs is production");
        assert!(io_nodes.contains("#[cfg(test)]\nmod tests {"));
        io_nodes.push_str(plant);
        pure_write_sites(&sources)
    };
    assert_ne!(
        after_test_module("\nfn planted() { emit(IO_TAG_PURE as usize); }\n"),
        admitted_sites(),
        "tag store after an inline test module"
    );
    assert_ne!(
        after_test_module("\nfn planted() { store(v, node, PURE_GLUE_ABS_OFFSET as i32); }\n"),
        admitted_sites(),
        "glue store after an inline test module"
    );

    let in_test_module = "fn f() {}\n#[cfg(test)]\nmod tests {\n    IO_TAG_PURE\n}\n";
    assert_eq!(strip_inline_test_module(in_test_module), "fn f() {}\n");
    let declared = "#[cfg(test)]\nmod t;\nfn g() { IO_TAG_PURE }\n";
    assert_eq!(strip_inline_test_module(declared), declared);
    let after = "#[cfg(test)]\nmod tests {\n    fn t() {\n    }\n}\nfn h() { IO_TAG_PURE }\n";
    assert_eq!(strip_inline_test_module(after), "fn h() { IO_TAG_PURE }\n");
}
