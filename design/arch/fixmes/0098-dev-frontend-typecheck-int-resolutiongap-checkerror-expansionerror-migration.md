---
number: 0098
target: /dev
filed_by: /arch
filed_at: 2026-05-02
sprint_filed: 64
refers_to: crates/cranelisp-types/src/error.rs rustdoc (ResolutionGap, CheckError; facades/types.md retired S69 Sub 42), crates/cranelisp-frontend/src/lib.rs //! preamble + per-item rustdoc on expand/ExpansionError/parse/extract_module_declarations + bounded-contexts.md §1 (facades/frontend.md retired S70 B3-C), design/arch/facades/typecheck.md §"check_form", design/arch/facades/int.md §"process_form", crates/cranelisp-frontend/, crates/cranelisp-typecheck/, crates/cranelisp-types/, src/expander.rs, src/worker.rs
status: open (Phase 3 typecheck CLOSED — Phases 2 frontend / 4 int remain)
---

# S72 W3b status — Phase 3 (typecheck) verified closed

`check_forms` is the free function returning `Result<(), CheckError>` per
`crates/cranelisp-typecheck/public-api.txt` (post-Wave 3b regen). `CheckError`
carries `Gap(ResolutionGap)` + `TypeError { message, location }` per facade.
`ResolveError` was added in Sprint 72 Wave 3b Part 5 as a typecheck-local
projection target — projecting to `CheckError::TypeError` via
`impl From<ResolveError> for CheckError`.

Phase 2 (frontend `ExpansionError`) and Phase 4 (int gap-orchestration
retry loop) remain. Refile or close when those land.

---

# Multi-crate migration: ResolutionGap + CheckError + ExpansionError + expand to facade-spec homes

## Issue

Resolves the implementation work surfaced by FIXMEs 0092 (frontend) and 0093 (typecheck), now that `/arch` has confirmed placement and added the boundary types to `cranelisp-types`. The contract is fully designed; the source has not yet caught up. This FIXME tracks the multi-crate `/dev` migration that closes the gap.

The work spans three crates and is best executed as a single coordinated triad cycle (frontend + types + int) — not three independent waves — because the boundary types and the call-site refactors are tightly coupled. Splitting risks intermediate states where one side typechecks but the other doesn't.

## Proposed resolution

**Phase 1 — `cranelisp-types`** (`/dev` narrow to types is `/arch`-direct work; coordinate with `/arch`):

1. Land `ResolutionGap` enum per `facades/types.md` §"Errors and warnings". Variants: `SymbolTypechecked(FQSymbol)`, `MacroInMem(FQSymbol)`, `Type(FQTypeName)`. `#[non_exhaustive]`.
2. Land `CheckError` enum per same. Variants: `Gap(ResolutionGap)`, `TypeError { message, location: ErrorLocation }`. `#[non_exhaustive]`.
3. Verify `Sexp`, `Defn`, `Expr`, `StructuralDecls`, `ImportSpec`, `ExportSpec`, `ModDecl`, `PlatformSpec`, `FQSymbol`, `FQTypeName`, `ModuleFullPath`, `Span`, `ErrorLocation`, `CodeStore`, `LinkerStore` all exist (most do per Decision 32 + Decision 39).

**Phase 2 — `cranelisp-frontend`** (`/dev` narrow to frontend):

1. Land `ExpansionError` enum in the frontend crate per the lib.rs //! preamble + per-item rustdoc on `pub enum ExpansionError` (`crates/cranelisp-frontend/src/expand.rs`; post-S70 B3-C the canonical home — `facades/frontend.md` retired). Variants: `Gap(ResolutionGap)`, `Malformed { message, span }`, `MacroAborted { fq, message, span }`. Re-export `ResolutionGap` from `cranelisp-types` for ergonomics.
2. Migrate `expand_sexp_recursive` from `src/expander.rs` (integration layer) to `crates/cranelisp-frontend/src/expand.rs`. Rename to `expand` per the facade. Drop the `MacroResolver` trait (Decision 8 retracted; replaced by direct `&SymbolTables<C, L>` lookup pattern).
3. Update the `expand` signature to match facade — generic over `<C: CodeStore, L: LinkerStore>`, takes `&SymbolTables<C, L>`. The depth-limit reconciliation (frontend design §5.2) is a separate question; keep current behaviour pending `/arch`'s call.
4. Update `extract_module_declarations` signature to match facade — accept `containing_module: &ModuleFullPath` parameter (this matches what the implementation already does internally; the facade now reflects it). Demote `parse_import_sexp` and the other per-form sub-parsers to `pub(crate)`.

**Phase 3 — `cranelisp-typecheck`** (`/dev` narrow to typecheck):

1. Migrate `check_form` from `TypeCheckEnv` method form to free-function form per `facades/typecheck.md` §"check_form". Return type changes from `Result<FormCheckResult, CranelispError>` to `Result<CheckResult, CheckError>`.
2. Replace ad-hoc unresolved-FQ-symbol-or-type detection points (in `infer.rs`'s deferred trait-call resolver and `program.rs`'s post-pass dependency analysis) with typed `Err(CheckError::Gap(ResolutionGap::*))` returns.
3. Re-export `CheckError` and `ResolutionGap` from `cranelisp-types` per facade §"Re-exports" (subject to FIXME 0002's policy on convenience re-exports — coordinate).
4. Pairs with FIXME 0008's mutability migration (free-function shape + per-symbol mutability discipline land together).

**Phase 4 — `src/` (int, integration layer)** (`/dev` narrow to int):

1. Replace ad-hoc dependency detection in `src/worker.rs` and `src/session_v4.rs` with typed pattern-matching on `ExpansionError::Gap(ResolutionGap)` (from frontend `expand`) and `CheckError::Gap(ResolutionGap)` (from typecheck `check_form`).
2. Wire the gap-orchestration retry loop per `facades/int.md` §"process_form — the gap-orchestration retry loop": catch Gap, dispatch via `handle_gap` (register + wait_for_typecheck_symbol + (priority_boost + wait_for_inmem) + wait_for_typecheck_type as needed), retry until both `expand` and `check_form` succeed.
3. Delete the `MacroResolver` trait and any integration-layer-internal expander scaffolding now superseded by the frontend-side free function.

## Sequencing notes

- Phase 1 (types) is prerequisite for Phases 2–4. Land first; downstream crates build against the new types.
- Phases 2 + 3 can proceed in parallel after Phase 1 (different crates, independent triads) but their facade-conformance lands together at Phase 4 wiring.
- Phase 4 closes the loop — the integration-layer pattern-match completes the gap-orchestration contract `facades/int.md` §"process_form" already specifies.
- FIXME 0008 (typecheck per-symbol mutability) bundles naturally with Phase 3.
- FIXME 0002 (re-exports policy) is upstream-of Phases 2+3's re-exports — coordinate.
- This is `/sprint`-scoped multi-wave work; not deliverable in a single per-crate triad cycle.

## Operational implication / Context

This was the largest contract-vs-source gap surfaced by the Sprint 64 Step 2 design refreshes (frontend + typecheck both flagged it). The contract itself is internally consistent and implementable; the work is migration, not redesign. After this FIXME closes:

- `cargo public-api` conformance becomes feasible for frontend and typecheck (M4).
- Decision 8's retraction lands in source (the `MacroResolver` trait disappears).
- `int::process_form` becomes a clean typed pattern-match instead of ad-hoc detection.
- FIXMEs 0008 and 0002 unblock for completion.
