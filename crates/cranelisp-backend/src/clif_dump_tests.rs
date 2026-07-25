//! Unit tests for Sprint 60 Workstream B (CLIF dump observability).
//!
//! These exercise the env-var filter grammar and the output formatter
//! in isolation from codegen — the integration test (exercising the
//! wired-up env var end-to-end via a subprocess) lives with `/qa` in
//! `tests/sprint60_observability.rs`.
use super::{clif_dump_matches, write_clif_dump};

#[test]
fn filter_unset_or_empty_never_matches() {
    assert!(!clif_dump_matches(None, "user", "foo"));
    assert!(!clif_dump_matches(Some(""), "user", "foo"));
}

#[test]
fn filter_wildcard_matches_every_function() {
    assert!(clif_dump_matches(Some("*"), "user", "foo"));
    assert!(clif_dump_matches(
        Some("*"),
        "exemplar.solver",
        "cell-at$grid.Cell"
    ));
    assert!(clif_dump_matches(Some("*"), "", ""));
}

#[test]
fn filter_module_only_matches_any_symbol_in_that_module() {
    assert!(clif_dump_matches(Some("user"), "user", "foo"));
    assert!(clif_dump_matches(Some("user"), "user", "bar"));
    assert!(!clif_dump_matches(Some("user"), "main", "foo"));
    // Dotted module paths are matched literally, not as prefixes.
    assert!(clif_dump_matches(
        Some("exemplar.solver"),
        "exemplar.solver",
        "go"
    ));
    assert!(!clif_dump_matches(
        Some("exemplar"),
        "exemplar.solver",
        "go"
    ));
}

#[test]
fn filter_module_colon_symbol_matches_that_exact_function() {
    let filter = Some("grid::cell-at$grid.Cell");
    assert!(clif_dump_matches(filter, "grid", "cell-at$grid.Cell"));
    // Wrong module — reject.
    assert!(!clif_dump_matches(filter, "html", "cell-at$grid.Cell"));
    // Wrong symbol — reject.
    assert!(!clif_dump_matches(filter, "grid", "cell-at"));
}

#[test]
fn write_clif_dump_frames_header_and_trailer() {
    let mut buf = Vec::<u8>::new();
    write_clif_dump(&mut buf, "user", "foo", "function %foo() -> i64 {\n}\n").unwrap();
    let out = String::from_utf8(buf).unwrap();
    assert!(
        out.starts_with("; === CLIF user::foo ===\n"),
        "output: {out}"
    );
    assert!(
        out.contains("function %foo() -> i64 {"),
        "body missing: {out}"
    );
    assert!(
        out.trim_end().ends_with("; === end CLIF user::foo ==="),
        "trailer missing: {out}"
    );
}

#[test]
fn write_clif_dump_adds_trailing_newline_when_body_lacks_one() {
    // Body without trailing newline — formatter should insert one so the
    // "end" trailer appears on its own line.
    let mut buf = Vec::<u8>::new();
    write_clif_dump(&mut buf, "m", "s", "noeol").unwrap();
    let out = String::from_utf8(buf).unwrap();
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines[0], "; === CLIF m::s ===");
    assert_eq!(lines[1], "noeol");
    assert_eq!(lines[2], "; === end CLIF m::s ===");
}
