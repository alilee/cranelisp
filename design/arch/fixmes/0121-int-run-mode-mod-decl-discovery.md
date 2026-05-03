---
number: 0121
target: /int
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/cache.rs::cache_multi_module_transitive_imports
status: open
---

# `--run` mode does not discover `(mod ...)` declarations in the entry module

## Issue

Defect surfaced during Sprint 64 Wave 2 Batch 1 audit (`tests/cache.rs`
test-port from integration-tier to e2e).

The legacy integration-tier test (using the in-process
`compile_module_graph_cached` via `helpers::batch_run_file_cached`)
PASSED. The e2e form via `--run main.cl` FAILS with:

```
error: module error at 0..0: entry module has no `main` function — batch mode requires (defn main [] ...)
```

Reproducer (committed at `tests/cache.rs::cache_multi_module_transitive_imports`):

```
main.cl       — (mod mid)
                (import [main.mid [relay]])
                (defn main [] (relay))
main/mid.cl   — (mod leaf)
                (import [main.mid.leaf [base-val]])
                (defn relay [] (base-val))
main/mid/leaf.cl — (defn base-val [] 77)
```

`/Users/.../cranelisp --run main.cl` exits 1 with the message above.

The integration helper goes through `register_module("main")` which
appears to walk `(mod ...)` declarations before expecting `main` to be
defined; the `--run` driver in `src/` does not. This is a binary
surface gap, not a language-semantics issue: the same tree compiles
fine through the integration helper.

## Proposed resolution

Either:

1. Make `--run` mirror the integration helper's module-discovery flow:
   parse the entry, follow `(mod ...)` declarations to discover
   submodules in dependency order, then resolve `main` in the (now
   fully-typed) entry module.
2. Document `(mod ...)` in the entry module of `--run` projects as
   unsupported, and update the test + spec accordingly. (Less
   preferred — the integration helper accepts it, so users may
   reasonably expect `--run` to as well.)

`/int` decides which path; this FIXME tracks the decision plus the
implementation.

## Operational implication / Context

This is a parity-rule landing per `tests/plan/PLAN.md §"Defect rule"`
and `memory/feedback_repros_join_suite.md`: the failing test is
committed un-ignored as the durable repro + regression guard. Until
`/int` resolves it, the test ledgers under
`tests/plan/ledger.md` as `out-of-scope (owner=/int)` with target
sprint TBD.

The legacy integration-tier coverage is preserved in
`tests/legacy/cache.rs::cache_multi_module_transitive_imports` (with
the `helpers::batch_run_file_cached` path that passes). Per the parity
rule the legacy file is NOT compiled — but the source is preserved as
audit trail.
