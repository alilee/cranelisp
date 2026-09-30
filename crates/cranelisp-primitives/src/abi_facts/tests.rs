use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

fn production_sources() -> BTreeMap<PathBuf, String> {
    fn visit(root: &Path, path: &Path, sources: &mut BTreeMap<PathBuf, String>) {
        for entry in std::fs::read_dir(path).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                if path
                    .file_name()
                    .is_some_and(|name| name == "tests" || name == "ui")
                {
                    continue;
                }
                visit(root, &path, sources);
            } else if path.extension().is_some_and(|extension| extension == "rs")
                && path.file_name().is_some_and(|name| name != "tests.rs")
            {
                sources.insert(
                    path.strip_prefix(root).unwrap().to_path_buf(),
                    std::fs::read_to_string(path).unwrap(),
                );
            }
        }
    }

    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut sources = BTreeMap::new();
    visit(&root, &root, &mut sources);
    sources
}

fn function_name(line: &str) -> Option<&str> {
    let rest = line.split_once("fn ")?.1;
    let end = rest
        .find(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
        .unwrap_or(rest.len());
    (end != 0).then_some(&rest[..end])
}

fn token_sites(sources: &BTreeMap<PathBuf, String>, token: &str) -> BTreeMap<String, usize> {
    let mut sites = BTreeMap::new();
    for (path, source) in sources {
        let mut current_function = "<module>";
        for line in source.lines() {
            if let Some(name) = function_name(line) {
                current_function = name;
            }
            let trimmed = line.trim_start();
            if !line.contains(token)
                || trimmed.starts_with("use ")
                || trimmed.contains(&format!("fn {token}"))
            {
                continue;
            }
            let key = format!("{}::{current_function}", path.display());
            *sites.entry(key).or_insert(0) += line.matches(token).count();
        }
    }
    sites
}

fn abi_handle_conversion_sites(
    sources: &BTreeMap<PathBuf, String>,
    method: &str,
) -> BTreeMap<String, usize> {
    let tokens = [
        format!("AbiHandle::{method}("),
        format!("AbiHandle>::{method}("),
        format!(".{method}("),
    ];
    let mut sites = BTreeMap::new();
    for (path, source) in sources {
        let mut current_function = "<module>";
        for line in source.lines() {
            if let Some(name) = function_name(line) {
                current_function = name;
            }
            let count = tokens
                .iter()
                .map(|token| line.matches(token).count())
                .sum::<usize>();
            if count != 0 {
                let key = format!("{}::{current_function}", path.display());
                *sites.entry(key).or_insert(0) += count;
            }
        }
    }
    sites
}

fn expected(entries: &[(&str, usize)]) -> BTreeMap<String, usize> {
    entries
        .iter()
        .map(|(site, count)| ((*site).to_owned(), *count))
        .collect()
}

// spec: design/primitives/primitives.md §2.4 — every raw
// adoption, retained-child projection and storage exit belongs to an exact
// approved function/site. The census is recursive and excludes test sources.
#[test]
fn typed_consume_trusted_base_matches_exact_production_callers() {
    let sources = production_sources();

    let unexpected_abi_handle_files = sources
        .iter()
        .filter_map(|(path, source)| {
            (source.contains("AbiHandle")
                && path != Path::new("abi_facts.rs")
                && path != Path::new("declaration_macro.rs"))
            .then(|| path.clone())
        })
        .collect::<Vec<_>>();
    assert_eq!(unexpected_abi_handle_files, Vec::<PathBuf>::new());
    // A shim boundary kind exists only through this implementing set, so a
    // borrowed (or any third) kind cannot be adopted by a wrapper.
    let abi_handle_kinds = sources[Path::new("abi_facts.rs")]
        .lines()
        .filter_map(|line| line.strip_prefix("impl AbiHandle for "))
        .map(|header| header.trim_end_matches(" {"))
        .collect::<Vec<_>>();
    assert_eq!(abi_handle_kinds, ["i64", "Owned"]);
    assert_eq!(
        abi_handle_conversion_sites(&sources, "from_abi"),
        expected(&[
            ("abi_facts.rs::test_owned", 1),
            ("declaration_macro.rs::<module>", 2),
        ])
    );
    assert_eq!(
        abi_handle_conversion_sites(&sources, "into_abi"),
        expected(&[("declaration_macro.rs::<module>", 2)])
    );

    assert_eq!(
        token_sites(&sources, "Owned::from_abi("),
        expected(&[
            ("abi_facts.rs::from_abi", 1),
            ("abi_facts.rs::adopt_produced_value", 1),
        ])
    );
    assert_eq!(
        token_sites(&sources, "Borrowed::from_abi("),
        expected(&[
            ("abi_facts.rs::test_borrowed", 1),
            ("marshal.rs::borrowed_field", 1),
        ])
    );
    assert_eq!(
        token_sites(&sources, "borrowed_field("),
        expected(&[
            ("marshal.rs::quote_sexp_build", 4),
            ("marshal.rs::read_slist", 2),
        ])
    );
    assert_eq!(
        token_sites(&sources, "adopt_produced_value("),
        expected(&[
            ("bool.rs::bool_to_string", 1),
            ("float.rs::float_to_string", 1),
            ("int.rs::int_to_string", 1),
            ("int.rs::parse_int", 2),
            ("marshal.rs::alloc_adt_2", 1),
            ("marshal.rs::alloc_adt_3", 1),
            ("marshal.rs::alloc_runtime_string", 1),
            ("marshal.rs::build_runtime_list", 1),
            ("marshal.rs::quote_sexp_build", 1),
            ("string.rs::str_char_at", 1),
            ("string.rs::str_concat", 1),
            ("string.rs::str_join", 1),
            ("string.rs::str_replace", 1),
            ("string.rs::str_split", 1),
            ("string.rs::str_substring", 1),
            ("string.rs::str_to_lower", 1),
            ("string.rs::str_to_upper", 1),
            ("string.rs::str_trim", 1),
            ("string.rs::vec_strings_from_owned_handles", 1),
        ])
    );
    assert_eq!(
        token_sites(&sources, ".into_raw()"),
        expected(&[
            ("abi_facts.rs::into_abi", 1),
            ("marshal.rs::alloc_adt_2", 1),
            ("marshal.rs::alloc_adt_3", 2),
            ("string.rs::vec_strings_from_owned_handles", 1),
        ])
    );
    assert_eq!(
        token_sites(&sources, ".to_owned()"),
        expected(&[
            ("marshal.rs::quote_sexp_build", 2),
            ("marshal.rs::shallow_rc_inc", 1),
        ])
    );

    let wrappers = &sources[Path::new("declaration_macro.rs")];
    assert_eq!(
        wrappers
            .matches("pub(crate) extern \"C\" fn $shim($($arg: i64),*) -> i64")
            .count(),
        1
    );
    assert_eq!(
        wrappers
            .matches("pub(crate) extern \"C\" fn $hshim($($harg: i64),*) -> i64")
            .count(),
        1
    );
}
