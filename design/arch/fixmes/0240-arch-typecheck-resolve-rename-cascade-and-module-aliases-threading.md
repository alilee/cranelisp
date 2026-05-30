---
number: 0240
target: /arch
filed_by: /dev (typecheck)
filed_at: 2026-05-30
sprint_filed: 72
refers_to: design/arch/facades/typecheck.md §"Per-kind lookup helpers", §"check_forms — cluster check scaffolding", §"Module-lifecycle free functions", §"TypeCheckEnv target shape — narrowing target", §"SymbolTableRead / SymbolTableMut single-pair invariant", design/typecheck/phase-b-plan.md (Sprint 72 Wave 3a — Phase B design plan)
status: open
---

# Phase C facade cascade — resolve_* rename + module_aliases threading + env accessor exposure

## Issue

Sprint 72 Wave 3b Phase B landed the typecheck-side rename family per the
plan (`fqtn_for_bare_type_name` → `resolve_type`, `trait_home_for` →
`resolve_trait`, plus a new `resolve_constructor` helper), the
`ResolveError` enum + `From<ResolveError> for CheckError` projection,
Tier 2 universe-walk deletion, and the `IntrinsicType` activation for
the four intrinsic scalars. The facade text in
`design/arch/facades/typecheck.md` still names the retired identifiers
in the §"Per-kind lookup helpers" section and surrounding rustdoc
references.

Three further Phase B audit findings (A1, A4, A7) need facade-side
attention; A7 (env accessor exposure to `pub`) landed source-side in
Wave 3b; A1 and A4 (module_aliases threading) were deferred from Wave 3b
because the source change is breaking for cross-crate consumers
(`src/worker.rs`, `src/session.rs`) and the dev/typecheck narrow may not
edit other crates.

## Proposed resolution

1. **Rename cascade** — `design/arch/facades/typecheck.md` §"Per-kind lookup
   helpers" (or equivalent) is rewritten to name the new `resolve_*`
   family:
   - `resolve_trait(state, name, span) -> Result<ModuleFullPath, ResolveError>`
   - `resolve_type(state, name, span) -> Result<FQTypeName, ResolveError>`
   - `resolve_constructor(state, name, span) -> Result<TypeName, ResolveError>`

   Plus the new `pub enum ResolveError` with five variants
   (`TraitNotFound` / `TypeNotFound` / `ConstructorNotFound` /
   `QualifiedModuleUnknown` / `PrivateInaccessible`) and the
   `From<ResolveError> for CheckError` projection — both per the plan
   §5.2 / §5.3.

2. **TypeCheckEnv accessors** — A7 source-side already landed
   (`current_symbol_table` / `current_symbol_table_mut` promoted from
   `pub(crate)` to `pub` on `TypeCheckEnv`). Facade text in
   §"SymbolTableRead / SymbolTableMut single-pair invariant" should
   confirm both pairs (`ClusterContext::current_symbol_table[_mut]` AND
   `TypeCheckEnv::current_symbol_table[_mut]`) return the same wrappers.

3. **module_aliases threading (A1 / A4)** — deferred from Wave 3b
   because the signature change for `check_forms` /
   `register_imports` / `register_exports` to take `&ModuleAliases`
   breaks downstream callers in `src/worker.rs` (~6 sites),
   `src/session.rs` (~1 site). Per
   `feedback_facade_first_migration.md` the discipline is: push
   typecheck to the target signature first, accept broken downstream
   build, fix consumers wave-by-wave. /arch coordinates the
   cross-crate cascade — either:

   (a) /arch + /dev (int) land the module_aliases threading
       coherently in a coordinated wave, OR

   (b) the facade text relaxes A1/A4 to permit the per-call
       `CheckState`-local `module_aliases` HashMap until a later
       FIXME drives the session-level migration.

   The plan §A1/A4 recommends (a) (~1-2 day combined source-moves
   change). The Wave 3b deferral is mechanical, not a Decision change.

4. **public-api.txt regeneration** — Wave 3b regenerated
   `crates/cranelisp-typecheck/public-api.txt` with the new
   `ResolveError` + `resolve_*` surface, dropped the `module_aliases`
   parameter rows (still absent), and added the public env accessors.
   Phase C facade text needs to reflect the regenerated baseline.

## Operational implication / Context

- Phase B's release gate is green at this fire (346/346 typecheck tests
  pass; clippy clean; no new warnings); the deferred A1/A4 work does
  not block Phase B closure.
- The rename cascade is editorial (no behavioural change); A1/A4 is
  substantive (session-level module aliases table).
- `feedback_decision_cascade_discipline.md` warns against
  un-cascaded Decisions causing drift. This FIXME is the cascade record
  for the Phase B Decision-class moves (rename family + IntrinsicType
  activation).
- The plan document itself (`design/typecheck/phase-b-plan.md`) is
  authoritative for the rename rationale + the §"Cross-cutting: Parts
  2 + 2b + 5 compose" sub-order. Phase C should match.
