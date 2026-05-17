// facade_compliance.rs — Sprint 67 Wave 0 (/qa primary deliverable).
//
// **Failing-not-ignored by design.** Per `memory/feedback_failing_not_ignored.md`
// and `sprints/SPRINT.md §"Enforcement mechanism"`, this test is the
// mechanical drift detector between as-built (each crate's
// `public-api.txt` baseline) and as-designed (each crate's `facades/{crate}.md`).
// At S67 Wave 0 open, ~45 PFR/PIF rows have been dispositioned by /arch
// (sprint table 116–162); orphan items in the pub-api baseline are the
// expected failure surface. The test should FAIL TODAY and flip GREEN
// as /design (Wave 1) + /dev (Waves 2–4) reconcile each crate's drift.
//
// **Mechanism (Option A — text grep).** For each (crate baseline, facade
// document) pair, extract the leaf "name" from every `pub …` line in the
// baseline, then assert that name appears as a substring of the facade
// document. Hits = covered; misses = orphan items.
//
// **Why grep and not a structural parser.** Facade documents are prose
// + Rust code blocks, not structured pub-api dumps. Names appear in
// `### \`MyType\``, in `pub fn foo(…)` declarations inside fenced code
// blocks, in cross-references (`see \`FooBar\``), in non-goals
// (`Backend MUST NOT carry name-keyed special cases…`). A substring
// match is the lowest-overhead way to assert facade awareness without
// requiring the facade to be a typed manifest. False positives are
// possible (a name mentioned only in a cross-reference would pass);
// the cost is recoverable — /review reads both the facade diff and the
// pub-api diff side-by-side at PR time (see `design/arch/CLAUDE.md
// §"Baseline-diff discipline"`).
//
// **Item filtering.** We filter out trait-impl boilerplate that adds
// massive noise without signal:
//   - `impl core::*` / `impl std::*` / `impl alloc::*` lines (auto-derived)
//   - `pub fn …::clone(…)` / `::fmt(…)` / `::eq(…)` and other derive-impl
//     method lines
//   - `impl` lines without a primary type name visible at the boundary
// The remaining "named items" are structs, enums, free fns, modules,
// type aliases, constants, and trait declarations — the surface that
// the facade SHOULD enumerate.
//
// **Per-crate facade pairs** (per SPRINT.md "Cover the 8 facade↔baseline pairs"):
//   types       → facades/types.md
//   frontend    → facades/frontend.md
//   typecheck   → facades/typecheck.md
//   backend     → facades/backend.md + facades/backend-cache.md (sub-facade)
//   primitives  → facades/primitives.md
//   intrinsics  → facades/intrinsics.md
//   platform    → facades/platform.md
// `int` (binary crate) has no `public-api.txt` and is skipped here;
// `int` surface is covered by separate integration tests below
// (`int_facade_*` files in this directory).
//
// spec: design/arch/CLAUDE.md §"Baseline-diff discipline" — every
// edge change must update both the pub-api baseline and the facade in
// the same change-set; this test enforces the second half.
// FIXME(/dev — every crate's PFR/PIF resolution in S67 Waves 1–4 must
// either name the item in the facade or mark it internal-but-exposed
// with rationale).

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::PathBuf;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// (crate-name, pub-api filename, [facade markdown files that together cover it])
fn facade_pairs() -> Vec<(&'static str, &'static str, Vec<&'static str>)> {
    vec![
        ("cranelisp-types", "cranelisp-types", vec!["types.md"]),
        ("cranelisp-frontend", "cranelisp-frontend", vec!["frontend.md"]),
        ("cranelisp-typecheck", "cranelisp-typecheck", vec!["typecheck.md"]),
        // backend split across two facade files (cache sub-facade per REV-1):
        (
            "cranelisp-backend",
            "cranelisp-backend",
            vec!["backend.md", "backend-cache.md"],
        ),
        ("cranelisp-primitives", "cranelisp-primitives", vec!["primitives.md"]),
        ("cranelisp-intrinsics", "cranelisp-intrinsics", vec!["intrinsics.md"]),
        ("cranelisp-platform", "cranelisp-platform", vec!["platform.md"]),
    ]
}

/// Extract candidate item names from one `public-api.txt` line. Returns
/// the empty set for lines we deliberately ignore (auto-derived
/// trait-impl boilerplate, blanket marker impls). Returns one-or-more
/// names for lines that introduce something the facade should describe.
fn extract_names(line: &str) -> HashSet<String> {
    let l = line.trim();
    let mut out: HashSet<String> = HashSet::new();
    if l.is_empty() {
        return out;
    }
    // Skip auto-derived / blanket impls — these are noise:
    //   impl core::clone::Clone for cranelisp_types::ast::Expr
    //   impl core::marker::Send for cranelisp_types::ast::Expr
    //   impl core::panic::unwind_safe::RefUnwindSafe for …
    //   impl core::cmp::Eq for …
    //   impl core::fmt::Debug for …
    //   impl core::fmt::Display for …
    //   impl core::default::Default for …
    //   impl serde::ser::Serialize for …
    //   impl serde::de::Deserialize for …
    //   impl core::ops::deref::Deref for …
    //   impl core::ops::deref::DerefMut for …
    //   impl core::error::Error for …
    //   impl core::hash::Hash for …
    //   impl core::cmp::PartialEq for …
    //   impl core::cmp::PartialOrd for …
    //   impl core::cmp::Ord for …
    //   impl core::marker::Copy / StructuralPartialEq / Freeze / Unpin / etc.
    if l.starts_with("impl core::")
        || l.starts_with("impl std::")
        || l.starts_with("impl alloc::")
        || l.starts_with("impl serde::")
        || l.starts_with("impl <")
        || l.starts_with("impl !")
        || (l.starts_with("impl<") && l.contains(" for ") && (
            l.contains("core::marker::")
            || l.contains("core::clone::")
            || l.contains("core::cmp::")
            || l.contains("core::fmt::")
            || l.contains("core::hash::")
            || l.contains("core::panic::")
            || l.contains("core::default::")
            || l.contains("core::ops::deref::")
            || l.contains("core::error::Error")
            || l.contains("serde::")
        ))
    {
        return out;
    }
    // Skip derive-impl method lines: `pub fn …::clone(&self) -> …`,
    // `::fmt(&self, …)`, `::eq(&self, …)`. These belong to skipped
    // trait-impl blocks above.
    if l.starts_with("pub fn ") && (
        l.contains("::clone(")
        || l.contains("::fmt(")
        || l.contains("::eq(")
        || l.contains("::hash<")
        || l.contains("::hash(")
        || l.contains("::partial_cmp(")
        || l.contains("::cmp(")
        || l.contains("::deref(")
        || l.contains("::deref_mut(")
        || l.contains("::default(")
        || l.contains("::serialize<")
        || l.contains("::serialize(")
        || l.contains("::deserialize<")
        || l.contains("::deserialize(")
        || l.contains("::source(")
    ) {
        return out;
    }
    // For `pub type X::Target = …`, also skip — it's the Deref Target alias.
    if l.starts_with("pub type ") && l.contains("::Target = ") {
        return out;
    }
    // For each remaining `pub …` line, pull out:
    //   - The leaf identifier after the final `::` in the first
    //     identifier-like path (struct, enum, fn, mod, const).
    //   - For `pub use X::Y`, the leaf Y (re-exports are facade-worth-
    //     mentioning).
    //   - For `pub enum Foo::Variant`, the variant name Foo::Variant
    //     produces both `Foo` and `Variant` (variants usually appear
    //     inside the enum's facade description).
    //   - For `pub struct Foo`, just `Foo`.
    //   - For `#[export_name = "…"] pub c fn …::name`, the leaf name AND
    //     the export name (kebab-case symbol that's the user-visible
    //     binding).
    // Extract export_name = "…" first if present.
    if let Some(start) = l.find("#[export_name = \"") {
        let s = &l[start + "#[export_name = \"".len()..];
        if let Some(end) = s.find('"') {
            out.insert(s[..end].to_string());
        }
    }
    // Pull leaf identifier. The leaf is the last "path component" that
    // starts with `cranelisp_<crate>::…` or is a plain Rust identifier.
    // Strategy: collect every `::` token that follows a `cranelisp_*::`
    // prefix.
    for tok in l.split_whitespace() {
        if let Some(after) = tok.split_once("cranelisp_") {
            // after = ("", "types::ast::Expr") or similar
            let rest = after.1;
            // Trim trailing punctuation (commas, parens, angles, etc.).
            let trimmed = rest.trim_end_matches(|c: char| {
                !c.is_alphanumeric() && c != '_' && c != ':'
            });
            // Split on `::`, take the leaf.
            if let Some(leaf) = trimmed.rsplit("::").next() {
                let leaf = leaf.trim_end_matches(|c: char| {
                    !c.is_alphanumeric() && c != '_'
                });
                if !leaf.is_empty()
                    && leaf
                        .chars()
                        .all(|c| c.is_alphanumeric() || c == '_')
                    && !leaf.starts_with(char::is_numeric)
                {
                    out.insert(leaf.to_string());
                }
            }
        }
    }
    out
}

/// Names from the pub-api line that are effectively "auto-generated"
/// and should not be required to appear in the facade. These leak
/// through `extract_names` because the line itself wasn't filtered
/// (e.g., the line introduces a struct AND has an auto method).
fn name_blacklist() -> &'static [&'static str] {
    &[
        // Rust auto-derived method names
        "clone",
        "fmt",
        "eq",
        "ne",
        "hash",
        "default",
        "deref",
        "deref_mut",
        "partial_cmp",
        "cmp",
        "source",
        "serialize",
        "deserialize",
        // common single-word identifiers that are too generic to
        // require facade mention (and that appear inside struct fields):
        "new",
        "as_str",
        "as_ref",
        "from",
        "into",
        "to_string",
        "len",
        "is_empty",
    ]
}

#[test]
fn facade_compliance_orphans_match_expected_sprint_67_baseline() {
    let root = workspace_root();
    let blacklist: HashSet<&str> = name_blacklist().iter().copied().collect();

    // Collected orphans across all crates: items appear in pub-api but
    // do NOT appear as a substring in any of the crate's facade docs.
    let mut orphans_per_crate: Vec<(String, Vec<String>)> = Vec::new();
    let mut total_orphans: usize = 0;

    for (display_name, crate_dir, facade_files) in facade_pairs() {
        let pub_api_path = root
            .join("crates")
            .join(crate_dir)
            .join("public-api.txt");
        let pub_api = std::fs::read_to_string(&pub_api_path)
            .unwrap_or_else(|e| {
                panic!("read {}: {e}", pub_api_path.display())
            });
        // Concatenate every facade file's content into one corpus.
        let mut facade_corpus = String::new();
        for f in &facade_files {
            let p = root.join("design").join("arch").join("facades").join(f);
            let s = std::fs::read_to_string(&p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            facade_corpus.push_str(&s);
            facade_corpus.push('\n');
        }

        let mut crate_orphans: Vec<String> = Vec::new();
        let mut seen: HashSet<String> = HashSet::new();
        for line in pub_api.lines() {
            let names = extract_names(line);
            for name in names {
                if blacklist.contains(name.as_str()) {
                    continue;
                }
                if !seen.insert(name.clone()) {
                    continue;
                }
                if !facade_corpus.contains(&name) {
                    crate_orphans.push(name);
                }
            }
        }
        crate_orphans.sort();
        total_orphans += crate_orphans.len();
        orphans_per_crate.push((display_name.to_string(), crate_orphans));
    }

    // Build the panic message — fail with the orphan list so /design
    // and /dev can attack them by crate.
    let mut msg = format!(
        "Facade compliance: {} pub-api items NOT named in their facade.\n\
         Sprint 67 Wave 0 baseline — expected to fail; /design (Wave 1) \
         and /dev (Waves 2–4) close the gap.\n\n",
        total_orphans
    );
    for (crate_name, orphans) in &orphans_per_crate {
        msg.push_str(&format!(
            "  {} — {} orphans:\n",
            crate_name,
            orphans.len()
        ));
        for o in orphans.iter().take(50) {
            msg.push_str(&format!("    - {o}\n"));
        }
        if orphans.len() > 50 {
            msg.push_str(&format!(
                "    … ({} more)\n",
                orphans.len() - 50
            ));
        }
    }

    // Failing-not-ignored. Total orphan count is the sprint progress
    // metric. Test passes when total_orphans == 0 (Wave 6 close gate).
    assert_eq!(total_orphans, 0, "{msg}");
}
