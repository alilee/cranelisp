---
number: 0179
target: /design
filed_by: /dev
filed_at: 2026-05-14
sprint_filed: 66
refers_to: design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md §"`ClusterContext` (Approach B is canonical)", design/arch/facades/typecheck.md §"check_forms — cluster check", crates/cranelisp-typecheck/src/checker.rs §"current_symbol_table"
status: open
---

# Cluster-mode reads — union staging-first-then-live (Wave 3b-2c.1 follow-up)

## Issue

Wave 3b-2c.1 (sprint 66 — this change) plumbed `ClusterContext::Cluster`
**write** redirection through `TypeCheckEnv`: writes targeting the cluster's
`current_module` route to the orchestrator-handed staging table via the new
`current_symbol_table_mut → SymbolTableMut::Staging(...)` accessor path. The
acceptance test `check_forms_cluster_mode_writes_go_to_staging` pins this
guarantee — live is byte-identical to its pre-call state across cluster
processing, and staging carries the registrations.

**Reads** in cluster mode currently still hit live directly via
`TypeCheckEnv::current_symbol_table(state)` → DashMap `Ref` over the
per-module live table. The facade and Decision 44 specify that cluster-mode
reads should return `View::union(staging, live)` (staging-first, then live)
so that intra-cluster forward references work: Pass 1 stages a signature
shell to staging; Pass 2 body-checks a sibling defn whose body references
the staged signature; the body check must read staging-first to see the
sibling.

The current `check_forms_forward_reference_works` test exercises this in
**live** mode (writes hit live, so the second pass sees the first defn). In
**cluster** mode this would break — Pass 2 reads from live and misses the
staged signature.

## Proposed resolution

Reshape `TypeCheckEnv::current_symbol_table` to return a wrapper that, in
cluster mode, dispatches reads through `View::union(staging, live)` per the
facade. The 51 read sites in `program.rs` / `traits.rs` / `builtins.rs` /
`infer.rs` / `adt.rs` / `checker.rs` either:
- Migrate to a `View`-shaped API (`.lookup(&Symbol)`, `.iter()`,
  `.iter_filter_by(...)`) — preferable, matches `View<'a, C, L>` in
  `cranelisp-types`, but is a non-trivial 51-site rewrite.
- Or use a wrapper enum that deref-coerces to `&SymbolTable` for the
  Live-mode path and a hand-rolled "union shadow" view for the Cluster path,
  preserving existing `.symbols.get`, `.all_symbols()`, `.get` access
  shapes. Simpler in mechanics; less idiomatic.

The first option (`View`-shaped API at the typecheck call sites) aligns with
Principle 17 (Module locality in typecheck) and `View<'a, C, L>`'s placement
in `cranelisp-types`. It is the same surgery as the Wave 3a-α locality
refactor and may want to land in that context.

## Operational implication / Context

Without this follow-up, `int::process_cluster` (Wave 3b-2c.2) cannot rely on
cluster-mode `check_forms` for any cluster larger than one independent form.
The `(begin form₁ form₂ form₃)` REPL cluster — the explicit multi-form
cluster boundary per Decision 44 — depends on intra-cluster forward refs to
work. Until read-side union lands, int must either:
- Continue using `ClusterContext::Live { … }` (current behaviour — writes
  leak to live; cluster atomicity not delivered), or
- Restrict cluster mode to single-form clusters where intra-cluster reads
  never trigger.

The single-form-cluster case still benefits from this change (atomic
commit-or-discard on `Err`), so 3b-2c.2 can begin lifting `Cluster` mode
with that restriction; the `(begin)` multi-form path waits on read-side
union.

The acceptance test added in this change
(`check_forms_cluster_mode_writes_go_to_staging`) intentionally uses a
single defn with a unit body to avoid the read-union dependency.
`check_forms_forward_reference_works` continues to exercise live mode only.

## Related

- Decision 0044 amendment (2026-05-13 third amendment) — `View<'a, C, L>`
  is the read surface that `ClusterContext::current_symbol_table()`
  constructs.
- Principle 17 (Module locality in typecheck) — the four principled access
  patterns at the 51 read sites; this follow-up is the structural seam
  where `View`-shaped access lands.
- FIXME 0168 / Decision 0046 — Wave 3a-α locality refactor; this read-side
  union plumbing is a natural fit for that wave's scope.
