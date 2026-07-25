---
number: 0869
target: /dev
filed_by: /testing
filed_at: 2026-07-25
sprint_filed: 117
refers_to: spec/07-traits.md §7.3; spec/08-modules.md §8.5;
  design/backend/module-caching.md §8;
  tests/cache.rs::cache_restores_sibling_written_trait_impls_for_dispatch
status: open
---

# Cache restoration loses sibling-written trait implementations

## Issue

A fresh build succeeds when one child module declares a trait, a sibling
declares the target type and its implementation, and the entry module
dispatches the imported method. The unchanged second `--run` restores the
modules from cache but rejects the same call with `no impl of trait ... for
type ...`.

Qualification is not causal. The reduced guard contains matched variants:
the sibling writes `(impl main.lib/Show W ...)` without importing the trait,
or imports `Show` and writes `(impl Show W ...)`. Both variants exit `7`
fresh and both lose the impl on the warm run.

The split storage model explains the loss. `ModuleEntry::TraitImpl`, the
dispatch-discovery shell, is stored only in the trait's home table. The
mangled method `Def`s are stored in the impl writer's table. In the observed
fresh schedule, the trait-home cache snapshot is written before the sibling
impl later mutates that live table, while the writer's cache snapshot contains
the method bodies but no typed record from which cache restoration can
re-enrol the discovery shell. Restoring each per-module snapshot therefore
reconstructs the two writer-owned method `Def`s but not the cross-module
trait-home discovery entry.

## Proposed resolution

Persist an explicit, typed list of implementations **written by each module**
as part of that module's cache metadata. Each record must carry the canonical
`FQTraitName`, canonical `FQTypeName`, writer module, method names, and
visibility needed to reconstruct the exact `ModuleEntry::TraitImpl`; it must
not parse mangled method spellings or scan unrelated tables.

During cache restoration, after the writer table and its dependencies are
installed, enrol those records through one idempotent helper into their trait
home tables. The helper should use the same canonical conflict/coherence
checks as fresh registration, preserve the discovery-shell/storage-module
split, and reject inconsistent cached metadata rather than silently choosing
one row. Cache schema/version handling must invalidate old sidecars that lack
the carrier.

The repair must retain:

- qualified and imported-bare impl-head equivalence;
- fresh/warm `Run` dispatch equivalence;
- one canonical discovery shell in the trait home;
- writer-owned mangled methods and GOT slots;
- idempotence when multiple dependency paths restore the writer;
- deterministic duplicate/conflict handling without string reconstruction.

The permanent failing-not-ignored discriminator is
`tests/cache.rs::cache_restores_sibling_written_trait_impls_for_dispatch`.
Owner unit tests should pin writer-side metadata projection, restore-time
enrollment, idempotent replay, and rejection of malformed or conflicting
records.

## Plan handoff

This Phase 6b defect needs a `/qa` PLAN row and sprint disposition.
