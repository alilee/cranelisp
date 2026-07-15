// stdlib_conformance.rs — S110 §E SG-1: the stdlib-compile smoke gate.
//
// The CLASS this gate cures: a compiler regression that breaks a stdlib module's
// compilation must NOT be able to ship invisibly (the 0604 blast radius —
// `num.bits` and other deep submodules are unreachable from the 13 top-level
// `.cl` files, so a top-level-only probe would miss them).
//
// Design (design/int/index-worker-isolation.md context + PLAN.md §S110 E,
// /qa-confirmed with two refinements):
//   1. Enumeration is RECURSIVE — every `stdlib/**/*.cl`, skipping `prelude.cl`
//      and every subtree declared private by its parent (`(mod- name)`, which
//      covers ALL `.test` submodules per the S109 P5-S2 conversion). No
//      hand-list anywhere — the walk + a light per-parent scan derives the set.
//   2. Shape: ONE enumerating test fn, a per-module `--run` subprocess loop
//      (each module compiles in its own subprocess + tmpdir), an AGGREGATED
//      failure report naming every failing module + its first error line (so one
//      run reports the full breakage set, not just the first).
//   3. Determinism: the gate runs `--run` (batch) — the background index feed is
//      REPL-only (R17), so the gate is deterministic by construction and is NOT
//      a race guard (the 0604 race is guarded by the §F ≥25× sweep). Its job is
//      the CLASS, not the race.
//
// Behind the ONE sanctioned `use_workspace_stdlib_for_stdlib_conformance_only()`
// gate (root CLAUDE.md §"Design Principles" — Stdlib separation; tests/CLAUDE.md
// §"Test isolation"). Plan: tests/plan/PLAN.md §S110 E / SG-1.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

/// The workspace `stdlib/` directory. Read-only on project_root — the gate only
/// reads the module tree to enumerate it; every compile runs in a per-module
/// tmpdir via the harness. `CARGO_MANIFEST_DIR` is the crate (workspace) root.
fn stdlib_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("stdlib")
}

/// Recursively collect every `*.cl` file under `dir`.
fn collect_cl_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_cl_files(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("cl") {
            out.push(path);
        }
    }
}

/// The dotted module path for a stdlib file: relative to `stdlib/`, `.cl`
/// stripped, `/` → `.`. `stdlib/collections/vec.cl` → `collections.vec`.
fn module_path(file: &Path, stdlib: &Path) -> String {
    let rel = file.strip_prefix(stdlib).expect("file under stdlib");
    let no_ext = rel.with_extension("");
    no_ext
        .components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join(".")
}

/// Does `parent_file` declare `child` as a PRIVATE submodule via `(mod- child)`?
/// A declaration line's trimmed head is `(mod- ` (comment lines start `;;`, so a
/// prose mention of `(mod- test)` in a `;;` comment is not matched).
fn declares_private_child(parent_file: &Path, child: &str) -> bool {
    let Ok(text) = fs::read_to_string(parent_file) else {
        return false;
    };
    for line in text.lines() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("(mod- ") {
            let name: String = rest
                .chars()
                .take_while(|c| !c.is_whitespace() && *c != ')')
                .collect();
            if name == child {
                return true;
            }
        }
    }
    false
}

/// A module is private (skip) if ANY of its path prefixes is declared private by
/// the parent `.cl` that owns that component — which also covers everything
/// UNDER a private module (the ancestor's `(mod- child)` catches the whole
/// subtree). `collections.vec.test` is private because `collections/vec.cl`
/// declares `(mod- test)`.
fn is_private_module(components: &[&str], stdlib: &Path) -> bool {
    for k in 1..components.len() {
        // Parent module = components[0..k]; its file is stdlib/<that>.cl.
        let parent_file = stdlib.join(components[0..k].join("/")).with_extension("cl");
        let child = components[k];
        if declares_private_child(&parent_file, child) {
            return true;
        }
    }
    false
}

// spec: spec/11-stdlib.md §11 + spec/08-modules.md §8.2 — every PUBLIC stdlib
// module MUST compile and run cleanly: a `--run` program that imports each
// public module's full surface (`[*]`) and returns `0` from `main` exits 0. The
// gate enumerates the module set RECURSIVELY (skipping `prelude.cl` and every
// `(mod- …)` private subtree) and reports EVERY failing module in one run.
//
// NOTE (per PLAN §S110 SG-1): this should be GREEN once 0604 lands; if any
// module is RED on HEAD today, that is SIGNAL (a real stdlib-compile break), not
// noise — the aggregated report names the module(s), for triage.
#[test]
fn stdlib_all_public_modules_compile_and_run() {
    let stdlib = stdlib_dir();
    let mut files = Vec::new();
    collect_cl_files(&stdlib, &mut files);
    files.sort();

    let mut public_modules: Vec<String> = Vec::new();
    for f in &files {
        let name = module_path(f, &stdlib);
        if name == "prelude" {
            continue;
        }
        let comps: Vec<&str> = name.split('.').collect();
        if is_private_module(&comps, &stdlib) {
            continue;
        }
        public_modules.push(name);
    }
    public_modules.sort();
    public_modules.dedup();

    assert!(
        !public_modules.is_empty(),
        "enumeration found zero public stdlib modules — the walk/skip logic is \
         broken (found {} .cl files under {})",
        files.len(),
        stdlib.display()
    );

    // Per-module subprocess loop: each module compiles in its own tmpdir; a
    // trivial `main` returning 0 makes exit 0 the pass condition. Cache ON within
    // the test's own tmpdir (transitive deps compile once per module).
    let mut failures: Vec<(String, String)> = Vec::new();
    for m in &public_modules {
        // `main` must return `IO _` under the workspace prelude (batch main
        // shape); `Pure` wraps the trivial `0` exit code. `Pure` is imported
        // explicitly from `primitives` because a module with an explicit
        // `(import …)` does not receive the implicit prelude glob, so a bare
        // `Pure` would be `undefined variable` — an artefact of the probe, not a
        // module defect.
        let probe = format!(
            "(import [{m} [*]])\n(import [primitives [Pure]])\n(defn main [] (Pure 0))\n"
        );
        let out = Cranelisp::new()
            .use_workspace_stdlib_for_stdlib_conformance_only()
            .file("main.cl", &probe)
            .run("main.cl")
            .timeout(Duration::from_secs(90))
            .output();
        if !out.status.success() {
            let combined = format!("{}\n{}", out.stdout, out.stderr);
            let first_err = combined
                .lines()
                .find(|l| {
                    let l = l.trim();
                    !l.is_empty() && !l.starts_with(":primitives/")
                })
                .unwrap_or("<no error line captured>")
                .trim()
                .to_string();
            failures.push((m.clone(), first_err));
        }
    }

    if !failures.is_empty() {
        let report = failures
            .iter()
            .map(|(m, e)| format!("  {m:32} → {e}"))
            .collect::<Vec<_>>()
            .join("\n");
        panic!(
            "SG-1: {} of {} public stdlib modules FAILED to compile/run under \
             `--run` (aggregated report — the full breakage set):\n{}",
            failures.len(),
            public_modules.len(),
            report
        );
    }
}
