---
number: 0140
target: /int
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/spec_08_modules.rs::import_below_use_still_available_before_definitions, spec/08-modules.md §8.3.9, tests/legacy/sprint59_neg.rs
status: open
---

# `--run` mode rejects program where `import` follows `(defn main ...)`

## Issue

Per `spec/08-modules.md §8.3.9` ("Imports may appear anywhere at the top level; they are extracted en bloc before compilation"), this program shape is valid:

```cranelisp
(defn main [] (helper))
(import [util [helper]])
```

(with sibling file `util.cl` defining `helper`).

The integration-tier helper `helpers::batch_run_file` accepts this program (the legacy test `tests/legacy/sprint59_neg.rs::import_below_use_still_available_before_definitions` passes). The binary `--run` orchestration in `src/main.rs` / `src/session_v4.rs` rejects it with:

```
error: module error at 0..0: entry module has no `main` function —
       batch mode requires (defn main [] ...)
```

The binary's parse/extract path appears to fail before reaching the `defn main` form when an `import` follows it — either the import-extraction pass aborts early, or the entry-module `main` check runs before the import en-bloc extraction completes. Spec §8.3.9 mandates the en-bloc extraction precedes compilation.

## Proposed resolution

`/int` reviews the order of operations in the `--run` driver against `spec §8.3.9`. The integration-tier helper proves the underlying compilation pipeline handles this correctly; the divergence is in the binary entry point's pre-compilation phase ordering.

Specifically: ensure import extraction runs to completion across all top-level forms (in declaration order is fine; en-bloc extraction need not reorder) before the `main`-presence check runs.

The failing test `tests/spec_08_modules.rs::import_below_use_still_available_before_definitions` is the durable repro + regression guard. Per `memory/feedback_repros_join_suite.md`, it stays in the suite forever — even after fix.

## Operational implication / Context

Surfaced during Sprint 64 Wave 5.5 dedupe-verification audit. Was a sprint59_neg.rs `[Tested+Neg]` carry-forward; passed integration-tier, fails e2e — exactly the integration-vs-CLI divergence the two-tier strategy is designed to surface (cf. FIXME 0121, FIXME 0122).

This is the THIRD `--run`-mode-vs-spec divergence Sprint 64's port has surfaced (after FIXME 0121 `(mod ...)` discovery and FIXME 0122 `--link` GOT alignment). Per the architectural principle of pipeline-v4 convergence (Decisions 22/25/41 + Principles 11–13), these divergences indicate the convergence is not yet complete in the binary's entry-point orchestration, even when the underlying compilation pipeline is correct.

Wave 5.5 spotted this only because the dedupe audit re-traced the spec annotation `[Tested+Neg]` for §8.3.9 and noticed the integration-tier carry-forward had no e2e equivalent.
