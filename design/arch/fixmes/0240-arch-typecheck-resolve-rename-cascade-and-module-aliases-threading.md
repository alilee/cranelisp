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
   confirm both pairs (`SymbolTableAccess::current_symbol_table[_mut]` AND
   `TypeCheckEnv::current_symbol_table[_mut]`) return the same wrappers.
   (Note: the boundary type was renamed `ClusterContext` →
   `SymbolTableAccess` in the facade-coherence pass — see
   `facades/typecheck.md` §"Cluster check scaffolding" naming rationale.)

3. **module_aliases threading (A1 / A4)** — **alias provenance is now
   settled (facade-coherence pass): `module_aliases` arrives threaded
   READ-ONLY into `check_forms`, and typecheck follows aliases during
   §8.6.6 FQ resolution but does NOT self-populate an alias table.** The
   `register_imports` / `register_exports` typecheck free functions
   (FIXME 0192 hack-back) are **struck from the typecheck surface** — see
   `facades/typecheck.md` §"Import/export registration is not a typecheck
   concern". So the original threading premise here — "the signature
   change for `check_forms` / `register_imports` / `register_exports` to
   take `&ModuleAliases`" — is subsumed: there is no longer any
   `register_imports` / `register_exports` on the typecheck surface to
   thread `&ModuleAliases` through, and the alias writer is the int-side /
   frontend-StructuralDecl parse-time installer, not typecheck. What
   remains live: threading the read-only `module_aliases` parameter into
   `check_forms` (the `check_forms` signature in the facade already names
   it). This is a mechanical cross-crate cascade (push typecheck to the
   target read-only signature first, fix `src/worker.rs` / `src/session.rs`
   consumers wave-by-wave per `feedback_facade_first_migration.md`) — NOT
   a Decision change, and option (b)'s `CheckState`-local
   self-populated HashMap is **rejected** (typecheck does not populate
   aliases). /arch + /dev (int) land the read-only threading coherently.

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
