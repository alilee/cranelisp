use super::*;
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

fn token_sites(sources: &BTreeMap<PathBuf, String>, token: &str) -> BTreeMap<String, usize> {
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

fn expected(entries: &[(&str, usize)]) -> BTreeMap<String, usize> {
    entries
        .iter()
        .map(|(site, count)| ((*site).to_owned(), *count))
        .collect()
}

// spec: design/runtime/s119-typed-consume-funnel.md §5 — dropping an armed
// owner without discharging it is a located debug failure.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "LEAKED Owned heap handle")]
fn leaked_owner_trips_the_debug_drop_bomb() {
    let raw = crate::heap_string::alloc_string(b"leaked") as i64;
    let _owner = unsafe { Owned::from_abi(raw) };
}

// spec: design/runtime/s119-typed-consume-funnel.md §5 — consuming the same
// fixture disarms the owner and balances its allocation without a false alarm.
#[cfg(debug_assertions)]
#[test]
fn consumed_owner_is_silent_and_balanced() {
    let allocs_before = crate::alloc::alloc_count();
    let deallocs_before = crate::alloc::dealloc_count();
    let raw = crate::heap_string::alloc_string(b"consumed") as i64;
    let owner = unsafe { Owned::from_abi(raw) };

    crate::rc::consume_shallow(owner);

    assert_eq!(
        crate::alloc::alloc_count() - allocs_before,
        crate::alloc::dealloc_count() - deallocs_before,
        "the consumed handle fixture must balance"
    );
}

// spec: design/runtime/s119-typed-consume-funnel.md §5 — an unrelated unwind
// remains survivable while an owner is in scope.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "unrelated handle test panic")]
fn owner_drop_during_unrelated_unwind_does_not_double_panic() {
    let raw = crate::heap_string::alloc_string(b"unwind") as i64;
    let _owner = unsafe { Owned::from_abi(raw) };
    panic!("unrelated handle test panic");
}

// spec: design/runtime/s119-typed-consume-funnel.md §3 — the unsafe adoption
// and disarm vocabulary remains confined to the approved intrinsics seams.
#[test]
fn typed_handle_trusted_base_matches_the_approved_intrinsics_allow_list() {
    let sources = production_sources();

    assert_eq!(
        token_sites(&sources, "Owned::from_abi"),
        expected(&[
            ("drop.rs::consume_vec_with", 1),
            ("drop.rs::owned_field", 1),
            ("handle.rs::Borrowed::to_owned", 1),
            ("handle.rs::test_owned", 1),
            ("io.rs::ProducedValue::drop", 1),
            ("io.rs::TrampolineFrame::drop", 2),
            ("io.rs::call_continuation", 1),
            ("io.rs::cranelisp_run_io", 1),
            ("io.rs::feed_continuation", 2),
            ("io.rs::read_bind_transition", 1),
            ("panic.rs::catch_runtime_error", 1),
            ("panic.rs::cranelisp_run_program", 1),
            ("reactor.rs::StateClosure::consume", 1),
            ("reactor.rs::supervised", 1),
            ("trace.rs::consume_slist_of_string", 2),
            ("trace.rs::consume_slist_of_trace", 2),
            ("trace.rs::consume_trace_call", 4),
            ("trace.rs::cranelisp_trace_children", 1),
            ("trace.rs::cranelisp_trace_first_child_nanos", 1),
            ("trace.rs::cranelisp_trace_name", 1),
            ("trace.rs::cranelisp_trace_nanos", 1),
            ("trace.rs::cranelisp_trace_params", 1),
            ("trace.rs::cranelisp_trace_result", 1),
            ("vec_runtime.rs::UnpublishedVecStrings::drop", 1),
        ])
    );
    assert_eq!(
        token_sites(&sources, "Borrowed::from_abi"),
        expected(&[("io.rs::borrowed_io_field", 1)])
    );
    assert_eq!(
        token_sites(&sources, "borrowed_io_field("),
        expected(&[("io.rs::read_bind_transition", 2)])
    );
    assert_eq!(
        token_sites(&sources, ".to_owned()"),
        expected(&[("io.rs::read_bind_transition", 2)])
    );

    assert_eq!(
        token_sites(&sources, "mem::forget"),
        expected(&[
            ("handle.rs::Owned::into_raw", 1),
            ("reactor.rs::OwnedCWaker::wake", 1),
        ])
    );

    let handle = &sources[Path::new("handle.rs")];
    let owned_decl = handle.find("pub struct Owned").unwrap();
    let owned_attributes = &handle[owned_decl.saturating_sub(300)..owned_decl];
    assert!(!owned_attributes.contains("derive(Clone"));
    assert!(!owned_attributes.contains("derive(Copy"));
    assert!(!handle.contains("impl Clone for Owned"));
    assert!(!handle.contains("impl Copy for Owned"));
    assert!(!sources[Path::new("drop.rs")].contains("pub type ElemConsumeFn"));
}
