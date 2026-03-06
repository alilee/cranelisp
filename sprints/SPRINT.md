# Sprint 6: Ring 2B — Modules & Multi-Sig Dispatch

**Status**: DRAFT
**Ring**: 2 (Abstraction) — third increment
**Goal**: Deliver file-based modules (import/export/visibility/qualified names), multi-signature dispatch, and Display trait registration.

## Scope

Ring 2A is complete (traits, constrained poly, default methods, user trait impls — 1177 tests, gate PASS). This sprint delivers Ring 2B: the module system and remaining Ring 2 features.

### What this sprint delivers

1. **File-based modules**: `(mod name)`, file discovery, compilation ordering
2. **Imports/exports**: `(import [module [names]])`, `(export [names])`, wildcard imports
3. **Visibility**: `pub`/private enforcement across module boundaries
4. **Qualified names**: `module/name` resolution
5. **Multi-signature dispatch**: `(defn show ([Int x] ...) ([Bool x] ...))` (if feasible within sprint)
6. **Display trait registration**: Register `Display` at startup alongside `Num`/`Eq`/`Ord` (FIXME U2.1)
7. **I1, I2, I4, I6 tech debt** from Sprint 4 review

### What this sprint does NOT deliver (Sprint 7+)

- Auto-curry: `(map (+ 1) [1 2 3])`
- Stdlib files in `lib/` (requires modules working first)
- Platform DLL loading
- Macros, derive (Ring 3)

## FIXME Debt

{To be filled during Phase 1 scan}

## Architecture Review

{To be filled by /arch during Phase 2}

## Skill Plans

{To be filled by each skill during Phase 3}

## Waves

{To be filled during Phase 4}

## Notes

## Outcome

{Filled in when sprint closes}

### Delivered

### Deferred

### Findings
