//! Source-census helpers for the crate's structural guards: a test reads the
//! crate's own production sources and asserts where a token may appear.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// Files that compile only under `cfg(test)`: test modules and the crate's
/// test-support modules.
const TEST_ONLY_FILES: [&str; 3] = ["tests.rs", "source_census.rs", "test_child.rs"];

/// Every production source file of this crate, by path relative to `src/`.
/// Test-only files and `tests/` directories are excluded.
pub(crate) fn production_sources() -> BTreeMap<PathBuf, String> {
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
                && path
                    .file_name()
                    .is_some_and(|name| !TEST_ONLY_FILES.iter().any(|test| name == *test))
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

fn declaration_name(line: &str, prefix: &str) -> Option<String> {
    let rest = line.split_once(prefix)?.1;
    let end = rest
        .find(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
        .unwrap_or(rest.len());
    (end != 0).then(|| rest[..end].to_owned())
}

fn impl_owner(line: &str) -> Option<String> {
    let trimmed = line.trim_start();
    let rest = trimmed.strip_prefix("impl")?.trim_start();
    let target = rest.split_once(" for ").map_or(rest, |(_, target)| target);
    let target = target.trim_start();
    let target = if target.starts_with('<') {
        target.split_once('>')?.1.trim_start()
    } else {
        target
    };
    let end = target
        .find(|character: char| {
            !(character.is_ascii_alphanumeric() || character == '_' || character == ':')
        })
        .unwrap_or(target.len());
    (end != 0).then(|| target[..end].to_owned())
}

/// The occurrences of `token` in `sources`, keyed `file::[Owner::]function`.
pub(crate) fn token_sites(
    sources: &BTreeMap<PathBuf, String>,
    token: &str,
) -> BTreeMap<String, usize> {
    let mut sites = BTreeMap::new();
    for (path, source) in sources {
        let mut owner = None;
        let mut function = None;
        for line in source.lines() {
            let trimmed = line.trim_start();
            if line.len() == trimmed.len() {
                if let Some(next_owner) = impl_owner(line) {
                    owner = Some(next_owner);
                    function = None;
                } else if trimmed == "}" {
                    owner = None;
                    function = None;
                }
            }
            if let Some(name) = declaration_name(line, "fn ") {
                function = Some(name);
            }
            if !line.contains(token)
                || trimmed.starts_with("use ")
                || trimmed.contains(&format!("fn {token}"))
            {
                continue;
            }
            let function = function.as_deref().unwrap_or("<module>");
            let key = match &owner {
                Some(owner) => format!("{}::{owner}::{function}", path.display()),
                None => format!("{}::{function}", path.display()),
            };
            *sites.entry(key).or_insert(0) += line.matches(token).count();
        }
    }
    sites
}

/// An expected [`token_sites`] result.
pub(crate) fn expected(entries: &[(&str, usize)]) -> BTreeMap<String, usize> {
    entries
        .iter()
        .map(|(site, count)| ((*site).to_owned(), *count))
        .collect()
}
