---
number: 0235
target: /qa
filed_by: /dev (platform)
filed_at: 2026-05-28
sprint_filed: 71
refers_to: design/platform/sprint71-redesign.md §12 (Next skills), tests/plan/sprint71-platform.md §4, FIXME 0229, FIXME 0233
status: open
---

# Round-trip integration tests once host-side wiring lands

## Issue

Sprint 71's Wave 2 tests are intra-crate (`crates/cranelisp-platform/tests/*.rs`):
they exercise the marker-type pattern, schema parser, and worked
extern functions against synthetic in-test heap fixtures.

True end-to-end coverage — a real DLL exporting CLAdt-typed functions,
loaded by the host, called from cranelisp source code, with values
crossing the FFI boundary — is deferred until:
- `HostCallbacks::alloc_with_tag` is wired (FIXME 0229).
- Platform-as-module is in place (FIXME 0233) so the cranelisp source
  can reference the platform-declared ADTs by name.

Tests/plan/sprint71-platform.md §4 explicitly defers these to the
host-wiring sprint and tracks them via this FIXME.

## Proposed resolution

In the host-wiring sprint (or the sprint immediately after):

1. **A new test-platform DLL** — `platforms/test-adt/`:
   - `declare_platform!` with a non-trivial schema (Rectangle +
     OptionInt + ListInt; deliberately exercise all three shape
     families).
   - Three extern functions that consume CLAdt parameters and return
     CLInt: `rectangle-area`, `option-or-default`, `list-sum`.

2. **A new test file** — `tests/spec_platforms_adt.rs`:
   - Loads the test-adt platform DLL.
   - Executes cranelisp source that constructs the corresponding
     ADTs via cranelisp-side `deftype` + constructor calls, then
     passes them to the platform fns.
   - Asserts the round-trip values match the expected outputs
     (rectangle of {w=3, h=4} → 12, etc.).

3. **Cache-restore round-trip** — re-load the same project from cache
   and verify ADTs cross correctly post-cache-hit (validates the
   `.meta.json` schema_literal field of FIXME 0232).

4. **Mismatch coverage** — a test that intentionally ships a
   schema-typo'd DLL and verifies the host's `validate_schema`
   callback rejects it at load with a clear error.

## Operational implication / Context

These tests are workspace-integration (under `tests/`) per the
two-tier discipline in `tests/CLAUDE.md`. The intra-crate tests
landed Sprint 71 Wave 2 are the unit/crate-integration tier; this
FIXME closes the e2e tier for the same surface.

Coordinating with the host-wiring sprint: as `/int` implements
FIXMEs 0229–0233, `/qa` files this FIXME's failing-first test plan;
Wave 2 of that sprint lands these round-trip tests as the acceptance
criterion.
