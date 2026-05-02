---
number: 0100
target: /dev
filed_by: /arch
filed_at: 2026-05-02
sprint_filed: 64
refers_to: design/arch/principles/15-facade-types-live-with-behavior.md, design/arch/facades/typecheck.md, design/arch/facades/backend.md, design/arch/facades/runtime.md, crates/cranelisp-types/src/, crates/cranelisp-typecheck/src/lib.rs, crates/cranelisp-backend/src/lib.rs, src/
status: open
---

# Relocate single-consumer facade types from `cranelisp-types` to their originating crates

## Issue

Per Principle 15 (S64) — facade types live with their behavior. A type appears in `cranelisp-types` IFF it is referenced by two or more implementation-crate facades (excluding `int`). Several types currently in `cranelisp-types` violate this heuristic: they are originated by exactly one implementation crate and consumed only by `int` downstream of that crate.

The relocation rationalises the dep graph (each crate's facade exposes its own types directly), eliminates re-export ceremony in implementation-crate `lib.rs` files (which Principle 15 also forbids), and aligns with the per-facade `cargo-public-api` change-control regime (M4-pending) by ensuring each crate's `api.txt` is the audit-of-record for its own types.

## Proposed resolution

Sequenced per affected implementation crate. Phases are independent and can land in any order.

**Phase 1 — `cranelisp-typecheck`** (`/dev` narrow to typecheck):

Move from `crates/cranelisp-types/src/` to `crates/cranelisp-typecheck/src/`:
- `CheckResult`, `CheckError`, `ResolutionGap`
- `FormCheckResult`, `CheckPass`
- `CheckState`, `TypeCheckEnv`, `ModuleCheckAccumulator`
- `ReplSnapshot`

Update `crates/cranelisp-typecheck/src/lib.rs`:
- Remove the existing `pub use cranelisp_types::{CheckResult, CranelispError, ReplSnapshot, TopLevel};` block.
- Add `pub use` for the relocated types from internal modules.

Update `int` callsites: rewrite `use cranelisp_types::{CheckResult, CheckError, ResolutionGap, …}` → `use cranelisp_typecheck::{…}`. Likewise for `ReplSnapshot`. `CranelispError` and `TopLevel` stay in `cranelisp-types` and remain imported from there.

**Phase 2 — `cranelisp-backend`** (`/dev` narrow to backend):

Move from `crates/cranelisp-types/src/` to `crates/cranelisp-backend/src/`:
- `CompilationError` (the variant set per `facades/backend.md` §"Errors")
- `GotEvent`, `GotEventTag`, `GotProvenance`, `GotObserver` (already speced in `facades/backend.md` as backend-originated; FIXME 0099 tracks the implementation work)

`Code` already lives in `cranelisp-backend` per Decision 41 — no relocation needed for it.

Update `int` callsites: rewrite imports of `CompilationError` and the GOT observer types from `cranelisp_types` → `cranelisp_backend`. Coordinate with FIXME 0099 to avoid two simultaneous moves of the same observer types.

**Phase 3 — verification sweep**:

After Phases 1 and 2, run `cargo public-api` (or equivalent) on `cranelisp-typecheck`, `cranelisp-backend`, and `cranelisp-types` to confirm:
- The relocated types appear in their new homes' public surface.
- `cranelisp-types`' public surface no longer carries the relocated types.
- No accidental wildcard re-export pulls them back through.

## Sequencing notes

- Independent of FIXME 0098 (multi-crate `ResolutionGap`/`CheckError`/`ExpansionError` migration). Phase 1 here covers the typecheck-side moves of `CheckError` and `ResolutionGap`; FIXME 0098's typecheck phase becomes simpler if this lands first.
- Coordinates with FIXME 0099 (GotObserver implementation): if 0099 lands first, the GOT observer types are already in backend by construction; this FIXME's Phase 2 just confirms they didn't accidentally land in `cranelisp-types`. If this FIXME lands first, the types are in backend before 0099's wiring work begins.
- Phase 1 and Phase 2 are parallelisable.

## Operational implication / Context

Closes the architecture-side resolution of FIXME 0002 (S63 — convenience re-exports) and operationalises Principle 15. The reduction in `cranelisp-types`' surface area also tightens Principle 13 (`interfaces.md` is auditable) — the shared crate's `api.txt` becomes a more honest indicator of what genuinely crosses multiple boundaries.

The runtime facade's IO observation types (`IoEvent`, `IoObserver`, `IoTraceFlushGuard`, `SchedulerTraceFlushGuard`) are already in `cranelisp-runtime` per `facades/runtime.md` — no Phase needed for runtime. The frontend facade's `ExtractedDeclarations` / `StructuralDecls` are likewise already in `cranelisp-frontend`.
