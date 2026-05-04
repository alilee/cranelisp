---
number: 0138
target: /frontend
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/modules.rs
status: open
---

# Harvest tests/legacy/modules.rs into cranelisp-frontend unit tests

## Issue

The Sprint 64 Wave 5 test-port quarantined `tests/legacy/modules.rs`
(530 LOC, 39 tests). The file exercises module discovery and graph
construction:

- `discover_module_graph` direct API (since removed from public
  pipeline.rs but still used as Rust-internal observation).
- `compile_module_graph` — module compilation order.
- Cross-module imports without `(mod ...)` declaration.
- Re-export chains.
- Multi-dot import paths.
- Module cycle detection.

The language-observable subset has been carried forward into
`tests/spec_08_modules.rs` (mode-specific exception: `--run` mode
because module discovery is most cleanly tested through the batch
driver's project-root resolution): import specific names, glob, qualified
names, visibility (defn- private), prelude, synthetic primitives module,
non-existent name errors, super-import-at-top-level rejection, cycle
detection.

The legacy file's remaining content is direct
`cranelisp_frontend::module_extract::*` API observation (re-export
glob inference, module-path canonicalisation), which is unit-tier work.

## Proposed resolution

Translate into `crates/cranelisp-frontend/src/module_extract.rs` (or
adjacent) as `#[cfg(test)]` modules. Many tests already exist there;
this harvest extends rather than replaces.

- **discover_module_graph tests** — translate the temp-fixture pattern
  into a `tempfile::TempDir` + direct API invocation.
- **Re-export inference tests** — assert the names threaded through
  `(import [util [*]]) (export [util-thing])` chains.
- **Multi-dot path tests** — `main.mid.leaf` resolution.

The current `crates/cranelisp-frontend/src/module_extract.rs` already
has tests for `test_module_path_preserved`, `test_export_specific`,
`test_export_glob` per spec citations — the harvest extends this
existing pattern.

## Operational implication / Context

Co-owner: `/int` if the harvest also wants to test the binary-level
project-root resolution path (currently in `src/session_v4.rs`); that
work is deferred until FIXME 0109 lands the decomposition.

When complete, delete `tests/legacy/modules.rs` and remove its row from
`tests/legacy/README.md`.
