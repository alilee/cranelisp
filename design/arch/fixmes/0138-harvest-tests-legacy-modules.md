---
number: 0138
target: /qa
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
sprint_retargeted: 81
retargeted_by: /dev (cranelisp-frontend)
refers_to: tests/legacy/modules.rs, tests/spec_08_modules.rs
status: open
---

# Harvest tests/legacy/modules.rs into cranelisp-frontend unit tests

## S81 W-B verification (/dev narrow on cranelisp-frontend, 2026-06-13)

Verified the harvest disposition against current source. Conclusion:
**no frontend-internal harvest is owed** — the one genuinely
frontend-internal property (the `super` → parent rewrite) is ALREADY
unit-covered in `module_extract.rs`; everything else in the legacy file is
e2e behaviour already carried forward into `tests/spec_08_modules.rs`. The
residual is purely the legacy-file deletion (/qa). Re-targeted
/frontend → /qa.

**Coverage audit:**

- 28 of the 29 active legacy tests are e2e-shaped (`batch_run_file` → run a
  project fixture, assert the returned value or that it errors). These are
  int/e2e concerns, not frontend-internal — and ALL are carried forward in
  `tests/spec_08_modules.rs` with explicit `(carry: legacy/modules.rs::...)`
  annotations: specific/glob import, qualified ref, private-not-importable,
  prelude/synthetic primitives, non-existent-name error, cycle detection,
  super-at-top-level reject, multi-dot path, nested chain,
  project-root-shadows-stdlib, stdlib-module, prelude-like reexport,
  export_specific/glob/transitive/multiple, export-private-not-reexported,
  imported-fn-as-HOF-arg.
- The ONE frontend-internal test —
  `super_import_rewrites_to_parent_end_to_end` — additionally reached into
  `session.symbol_tables()` to assert the `super`→parent rewrite produced
  no lingering `"super"` literal in `ModuleEntry::Import` and named the
  parent path absolutely. The FRONTEND HALF of that property (the rewrite in
  `parse_import_entries`, Decision 30) is ALREADY fully unit-covered in
  `crates/cranelisp-frontend/src/module_extract.rs` `#[cfg(test)]`:
    - `test_import_super_rewrites_to_parent` (`math.test` → `math`, glob)
    - `test_import_super_rewrites_nested_parent` (`app.handler.test` → `app.handler`)
    - `test_import_super_at_root_errors` (root → ModuleError naming super / root / no-parent)
  No frontend unit-test gap remains. (The end-to-end *execution* half of the
  legacy test — that `super`-rewritten imports run correctly — is the e2e
  concern covered by `spec_08_modules.rs::super_import_at_top_level_neg` for
  the negative; the positive execution path is not separately re-witnessed
  e2e but is exercised transitively through the reexport/nested-chain tests.
  If /qa wants the positive `super`-rewrite execution as an explicit e2e it
  may add one, but it is NOT a frontend-internal harvest.)
- The FIXME's named candidates — re-export glob inference, module-path
  canonicalisation, multi-dot path parsing — are extraction-level and
  ALREADY unit-covered in `module_extract.rs`: `test_export_glob`,
  `test_export_specific`, `test_export_multiple`, `test_module_path_preserved`,
  `test_import_multiple_modules`, `test_import_member_glob`. No gap.

`discover_module_graph` / `compile_module_graph` (cited in the original
issue) were removed from `pipeline.rs` — the legacy tests that used them are
already DISABLED (commented out) in the file, so there is nothing live to
port for those APIs.

## Residual work owed (target: /qa)

Delete `tests/legacy/modules.rs` and remove its row from
`tests/legacy/README.md` — coverage fully subsumed (28 behavioural tests in
`spec_08_modules.rs`; the super-rewrite frontend-internal property in
`module_extract.rs` units). Optionally (not required) add an explicit
positive `super`-rewrite *execution* e2e to `spec_08_modules.rs` if a
durable end-to-end witness is wanted — but that is /qa discretion, not a
blocker for deletion. The /int co-owner note (binary-level project-root
resolution, FIXME 0109) is unchanged.

Once the deletion lands, /qa deletes this FIXME.

## (Original issue, retained for provenance)

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
