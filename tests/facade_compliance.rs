// facade_compliance.rs — Sprint 67 Wave 0 (/qa primary deliverable);
// re-anchored Sprint 74 Wave 4 (/qa), then SIMPLIFIED later in W4 (/qa).
//
// **One check, one contract.** This file holds the mechanical drift
// detector between as-built (each crate's `public-api.txt` baseline) and
// as-designed, FOR CRATES THAT STILL HAVE A BINDING FACADE `.md`. That is
// its entire job: for each such crate, assert every public-api baseline
// item is named somewhere in the facade (an orphan check).
//
// **Facade-compliance applies only to crates with a binding facade.** As of
// Sprint 74, SIX of the original eight facades have been RETIRED and their
// `.md` files deleted:
//
//   types.md      retired S69 (FIXME 0218)
//   frontend.md   retired S70 W4
//   platform.md   retired S71 W4
//   typecheck.md  retired S72
//   intrinsics.md retired S74 W3
//   primitives.md retired S74 W3
//
// For those six crates there is **nothing for a facade-compliance test to
// check**. Once a facade is retired the crate's public surface is DEFINED by
// its source: the `public-api.txt` baseline (the `cargo public-api` record)
// plus the compiler ARE the definition and the guard. There is no longer a
// facade `.md` to comply WITH, so asserting "the crate documents itself"
// would just be restating the code — not a contract check. Source rustdoc on
// those crates carries rationale (why the code is shaped as it is), not a
// restatement of the surface; it is intentionally NOT asserted here. The
// cross-type design narrative for the retired crates lives in
// `design/arch/bounded-contexts.md` (§7 types, §1 frontend, §5 platform,
// §4a primitives, §4b intrinsics).
//
// Therefore the six retired crates are **intentionally absent from this
// test entirely** — they are not moved to a different check; they drop out.
//
// Only the still-binding facades remain in scope here:
//
//   backend.md + backend-cache.md (sub-facade per REV-1)
//   int.md  — covered by the separate `int_facade_*` tests in this dir
//             (e.g. `tests/facade_pif_rows.rs`); `int` is a binary crate with
//             no `public-api.txt`, so it is not part of THIS file's
//             pub-api↔facade grep check.
//
// So the only crate exercised by this file's grep check is `cranelisp-backend`.
//
// **Why this file was latently broken before S74.** The S67 `facade_pairs()`
// listed all eight crates and read each facade `.md` with panic-on-missing.
// As each facade retired (S69–S74), its slice began panicking on the now-
// deleted file. This stayed masked because `tests/` integration targets
// link the root `cranelisp` binary, and that binary has been RED (backend
// cascade) across these sprints — so the test never compiled/ran to expose
// the panic. The S74 W4 re-anchor removed the dependency on the six deleted
// `.md` files; this file is pure `std::fs` and references no retired facade.
//
// =============================================================================
// Facade text compliance (binding facades only)
// =============================================================================
//
// **Failing-not-ignored by design.** Per `memory/feedback_failing_not_ignored.md`
// and `sprints/SPRINT.md §"Enforcement mechanism"`, this is the drift
// detector between each binding facade and its crate's `public-api.txt`.
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
// spec: design/arch/CLAUDE.md §"Baseline-diff discipline" — every
// edge change must update both the pub-api baseline and the facade in
// the same change-set; this test enforces the second half.

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::PathBuf;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// (crate-name, pub-api filename, [facade markdown files that together cover it])
/// — only the still-binding facades. The six retired crates
/// (types/frontend/platform/typecheck/intrinsics/primitives) are intentionally
/// absent: their facade `.md` is gone, so source IS their canonical surface,
/// guarded by `public-api.txt` + the compiler, with rustdoc carrying rationale.
/// There is nothing for a facade-compliance test to check on a retired-facade
/// crate, so they drop out of this test entirely (they are not moved to a
/// different check).
fn facade_pairs() -> Vec<(&'static str, &'static str, Vec<&'static str>)> {
    vec![
        // backend split across two facade files (cache sub-facade per REV-1):
        (
            "cranelisp-backend",
            "cranelisp-backend",
            vec!["backend.md", "backend-cache.md"],
        ),
        // `int` (binary crate) has no `public-api.txt`, so it is not part of
        // the pub-api↔facade grep check; `int.md` remains binding and is
        // covered by separate `int_facade_*` integration tests in this dir
        // (e.g. `tests/facade_pif_rows.rs`).
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

// =============================================================================
// Facade text compliance for the still-binding facades.
// =============================================================================

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
         Binding facades checked here: backend.md + backend-cache.md. The six \
         retired-facade crates (types/frontend/platform/typecheck/intrinsics/\
         primitives) are intentionally absent — source is their canonical \
         surface, so there is nothing for a facade-compliance test to check.\n\n",
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

    // Failing-not-ignored. Total orphan count is the drift metric for the
    // still-binding facades. Test passes when total_orphans == 0.
    assert_eq!(total_orphans, 0, "{msg}");
}
