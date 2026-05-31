---
number: 0187
target: /dev (int)
filed_by: /dev (typecheck)
filed_at: 2026-05-15
sprint_filed: 67
refers_to: design/arch/facades/typecheck.md §"Cluster check scaffolding" §"TypeCheckEnv target shape", crates/cranelisp-typecheck/src/checker.rs, src/session_v4.rs, src/worker.rs, src/platform.rs, src/session.rs
status: open
---

# `int` consumers of `TypeCheckEnv` helper methods need migration to facade-targeted surface

## Issue

Sprint 67 Wave 3 /dev (typecheck) narrowed `TypeCheckEnv`'s public surface
toward the facade target (2 methods: `new` + `next_type_id`). Per the per-method
audit, ~15 methods still hold `pub` because `int` (`src/session_v4.rs`,
`src/worker.rs`, `src/platform.rs`, `src/session.rs`) consumes them cross-crate.

The full narrowing-to-facade-target cannot land until the consumers migrate to
either:

1. Reading the underlying `ModuleEntry` directly via `SymbolTable::get` and
   following the per-symbol chain-follow primitives that `cranelisp-typecheck`
   exposes implicitly through `cranelisp-types::ModuleEntry::Import { source, .. }`
   (the standard chain-follow pattern from Principle 17).
2. Or accepting that some methods stay `pub` permanently as escape-hatch
   "internal-but-exposed" helpers for REPL introspection (in which case the
   facade should be amended to list them).

The methods still publicly exposed by `TypeCheckEnv` after Wave 3 narrowing:

| Method | External consumer site(s) | Suggested migration |
|---|---|---|
| `ensure_module_exists(&ModuleFullPath)` | session_v4.rs:1049, 1692, 1947, 2587, 2905; worker.rs:414, 3831; platform.rs:245 | Wrap behind an `int`-side helper (`Sess::ensure_module_exists`) or keep `pub` as bootstrap-time invariant guard |
| `resolve_module_by_name(&CheckState, &str)` | session_v4.rs:1082, 2780 | Migrate to `SymbolTable::lookup` for `ModuleEntry::Submodule` per Principle 17 |
| `snapshot(&CheckState)` / `restore(&mut CheckState, ReplSnapshot)` | session_v4.rs:1091, 1100 | REPL eval rollback — facade prescribes this as `ReplSnapshot` primitive; could move to a standalone `ReplSnapshot::capture(&CheckState, &TypeCheckEnv) -> Self` + `apply(&self, &mut CheckState, &TypeCheckEnv)` free-function pair |
| `lookup_type_def(&TypeName)` | session_v4.rs:3584 | REPL `/info <type>` — migrate to direct `SymbolTable::get` for `ModuleEntry::TypeDef` |
| `get_type_constructors(&TypeName)` | session_v4.rs:3672 | REPL `/info` — migrate as above |
| `get_impls_for_type(&TypeName)` | session_v4.rs:3677, 3714 | REPL `/info`/`/list` — migrate to chain-follow + per-trait module probe |
| `defining_module_for(&CheckState, &str)` | session_v4.rs:3693 | REPL trait-display formatting — migrate to direct chain-follow on `Import` source field |
| `get_trait_methods(&TraitName)` | session_v4.rs:3697 | REPL — migrate to read `ModuleEntry::TraitDecl.methods` directly |
| `get_implementing_types(&TraitName)` | session_v4.rs:3702 | REPL — migrate to scan the trait's defining module for `TraitImpl` entries |
| `module_table(&ModuleFullPath)` | session_v4.rs:2757, 2785, 3215, 3343 | Migrate to `Sess.shared.symbol_tables.get(&path)` directly (the `DashMap` is already in `int`'s reach) |
| `restore_cached_module(SymbolTable)` / `restore_cached_impls(&[String])` | worker.rs:1904, 1909 | Cache-hit reconstruction — migrate to direct `DashMap::insert` (and the no-op `restore_cached_impls` deletes outright) |
| `register_imports` / `register_exports` | worker.rs:1618, 1644, 2119, 2176, 2721, 2765; session.rs:335 | **Struck from the typecheck surface (facade-coherence pass) — NOT kept `pub`.** Import/export registration is frontend's StructuralDecl concern; `ParsedEntry` has no `Import`/`Export` variant, so typecheck never receives imports/exports (see `facades/typecheck.md` §"Import/export registration is not a typecheck concern"). These callers migrate off typecheck: the alias writer is the int-side / frontend-StructuralDecl parse-time installer; the cross-module concern typecheck does have surfaces as `CheckError::Gap` (orchestrator loads + retries). The dead-code warnings on removal are the expected signal. |

## Proposed resolution

Two phases for /dev (int):

**Phase A — non-invasive migrations.** Migrate the REPL introspection
consumers (`session_v4.rs` lines 3584, 3672, 3677, 3693, 3697, 3702, 3714) to
read `SymbolTable::get` directly with chain-follow per Principle 17. ~7 call
sites; each is a small replacement. After this phase, `lookup_type_def`,
`get_type_constructors`, `get_impls_for_type`, `defining_module_for`,
`get_trait_methods`, `get_implementing_types` can narrow to `pub(crate)`.

**Phase B — bootstrap + cache reconstruction.** Migrate `ensure_module_exists`
and `restore_cached_*` to direct `DashMap` operations on `Sess.shared.symbol_tables`
(no `TypeCheckEnv` construction required for these paths). After this phase,
the 8 remaining helper-method exposures collapse to 2 or 3 facade-listed
escape hatches. `register_imports`/`register_exports` are **struck from
the typecheck surface** (facade-coherence pass — see row above and
`facades/typecheck.md` §"Import/export registration is not a typecheck
concern"); their callers migrate off typecheck rather than the facade
listing them as kept entry points.

The facade `design/arch/facades/typecheck.md` should be amended at the end
of Phase B to either (a) list the residual `pub` exposures with rationale, or
(b) confirm the 2-method target is met.

## Operational implication / Context

- **No behavioural defect today.** The current `pub` methods produce correct
  results; this FIXME captures the narrowing residue, not a bug.
- **Test impact: none.** The facade compliance test (`row_21_*`) tolerates
  ≤4 method count today; once Phase A lands, the count drops further toward 2.
- **Cross-skill dependencies:** Phase A depends on `cranelisp-types::ModuleEntry`
  remaining stable (`Import { source, .. }`, `TypeDef { .. }`,
  `TraitDecl { decl, .. }` field accessibility). All three are stable per
  S66/S67 facade lock.

## Why a FIXME and not inline TODO

The /dev (typecheck) narrowing is local to `cranelisp-typecheck`; the
consumer-side rework is `/dev (int)` work. Per `sprints/METHOD.md` §3.3,
cross-skill change requests live in `design/arch/fixmes/`.
