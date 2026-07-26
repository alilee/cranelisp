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
// defect: class=wrong-reject locus=crates/cranelisp-backend/src/drop_glue.rs::ctor_shapes found=S118 owner=/dev
//   — RED at S118 close on `core.io/when-io` (taking `core` and `core.io` down
//   with it): FIXME 0907 hard-refuses the concrete-`IO T` release with
//   `constructor 'Bind' disagrees on declared parameter identity for
//   'primitives/IO'`. A spec-conforming module, rejected. The aggregated
//   report names every failing module, so any module OUTSIDE that trio is a
//   new finding, not this defect. Census: tests/plan/s118-test-plan.md §11.1;
//   minimal repro: spec_10_io::pure_pattern_accepted.
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
        let probe =
            format!("(import [{m} [*]])\n(import [primitives [Pure]])\n(defn main [] (Pure 0))\n");
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

// =============================================================================
// BD-M3 — the STDLIB-ROUTE conformance row (binder matrix, sanctioned stdlib
// exception). `def`/`const` are stdlib macros (`stdlib/defs.cl`) that expand to
// native `defn`/`defmacro`, so the §5 binder rule reaches them AFTER expansion
// (spec §5 intro: "a qualified head such as `(def fmt/x 1)` … is rejected on the
// same principle"). This is the real user-facing route (the forms users actually
// write), exercised behind the ONE sanctioned workspace-stdlib gate. Reject cell
// is RED today (silent-accept) → flips at W3; the located-span provenance shares
// the BD-M2 int re-anchoring seam (W4, FIXME 0650). Bare-head positive is GREEN.
// =============================================================================

// A REPL session with the workspace stdlib (its prelude auto-loads, so `def`/
// `const` are in scope without an explicit import — an explicit `(import …)` would
// suppress the implicit prelude glob and lose the macros). REPL mode also sidesteps
// the batch-`main` shape (`Pure` is not in the prelude glob).
fn stdlib_repl(stdin: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .repl()
        .stdin(stdin)
        .timeout(Duration::from_secs(90))
        .output()
}

// BD-M3 (reject cell) — `(def fmt/x 1)` via the stdlib `def` macro: a qualified
// head reaches the binder reject after expansion. RED today (silent-accept /
// incidental); flips at W3. The located span provenance shares the BD-M2 int
// re-anchoring seam (W4, FIXME 0650).
// spec: spec/05-definitions.md §5 + §5.7 — `def` expands to a native binder; a
// qualified head is rejected on the binder principle.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs (post-expansion binder reject, def macro route) found=S113 owner=/dev
#[test]
fn stdlib_def_qualified_head_rejected_binder_neg() {
    let out = stdlib_repl("(def fmt/x 1)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the stdlib `def` route with a qualified head `fmt/x` MUST be a compile-\
         time error (§5 binder principle reaches macro expansion); got:\n{c}"
    );
    assert!(
        !c.contains("undefined function") && !out.stdout.contains("user/fmt/x"),
        "the reject MUST NOT surface as an `undefined function` codegen leak nor \
         silently bind `user/fmt/x`; got:\n{c}"
    );
}

// BD-M3 (bare-head positive TWIN) — `(def x 1)` via the stdlib `def` macro binds
// normally; `x` reads back `:primitives/Int 1`. GREEN.
// spec: spec/05-definitions.md §5.7 — a bare `def` head binds normally.
#[test]
fn stdlib_def_bare_head_accepts_twin() {
    let out = stdlib_repl("(def x 1)\nx\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains(":primitives/Int 1"),
        "a bare `def x 1` head MUST bind and `x` read back `:primitives/Int 1`; \
         got:\n{c}"
    );
}

// BD-M3 (const reject cell) — the `const` macro route, same principle.
// spec: spec/05-definitions.md §5 + §5.6 — `const` expands to a native binder.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs (post-expansion binder reject, const macro route) found=S113 owner=/dev
#[test]
fn stdlib_const_qualified_head_rejected_binder_neg() {
    let out = stdlib_repl("(const fmt/PI 3)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the stdlib `const` route with a qualified head `fmt/PI` MUST be a compile-\
         time error (§5 binder principle); got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/fmt/PI"),
        "the qualified `const` head MUST NOT silently bind; got:\n{}",
        out.stdout
    );
}
