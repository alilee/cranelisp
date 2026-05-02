---
number: 0092
target: /arch
filed_by: /design
filed_at: 2026-05-01
sprint_filed: 63
refers_to: design/arch/facades/frontend.md §"expand", design/arch/facades/int.md §"process_form — the gap-orchestration retry loop", crates/cranelisp-types/src/, src/expander.rs
status: open
---

# `ResolutionGap`, `ExpansionError`, and `expand` are not yet in their facade-specified homes

## Issue

The frontend facade and the int facade together specify a contract that does not yet exist in code:

1. `cranelisp_frontend::expand(sexp, &symbol_tables) -> Result<Sexp, ExpansionError>` — does not exist. Today's expander lives in `src/expander.rs` (integration layer) as `expander::expand_sexp_recursive(sexp, &mut dyn MacroResolver, depth)`.
2. `ExpansionError` (with `Gap(ResolutionGap)`, `Malformed`, `MacroAborted` variants) — does not exist. Today's expander returns `CranelispError`.
3. `ResolutionGap` enum (`SymbolTypechecked(FQSymbol)`, `MacroInMem(FQSymbol)`, `Type(FQTypeName)`) — does not exist anywhere in `cranelisp-types`.
4. `MacroResolver` trait — exists in `src/expander.rs` and is invoked by `worker.rs` and `session_v4.rs`. Decision 8 retracted the `MacroExpander` trait from `cranelisp-types`; the current `MacroResolver` is an integration-layer trait, not a public boundary contract.
5. `StructuralDecls` — does not exist; today's `ExtractedDeclarations` (in `crates/cranelisp-frontend/src/module_extract.rs`) is the closest analogue and carries `path` plus four spec vectors.

The frontend per-crate design doc (`design/frontend/frontend.md`) cannot describe HOW the crate fulfills the facade without this scaffolding existing somewhere. The design intent is committable today (the contract is internally consistent and implementable), but the boundary types must land in `cranelisp-types` before `/dev` can build to the facade.

## Proposed resolution

Confirm placement and ordering:

(a) `ResolutionGap` lands in `cranelisp-types` as a public enum alongside `FQSymbol` and `FQTypeName`. Both `ExpansionError::Gap` and the (planned) `CheckError::Gap` carry it.

(b) `ExpansionError` lands in `cranelisp-frontend` as the public error type for `expand`. Per facade §"Re-exports", frontend re-exports `ResolutionGap` for ergonomics.

(c) The expander code currently in `src/expander.rs` migrates to `cranelisp-frontend/src/expand.rs` (or similar). The migration deletes the integration-layer `MacroResolver` trait (Decision 8 already retracted the trait shape) and replaces it with the direct `&symbol_tables` lookup pattern the facade specifies.

(d) The integration layer (`int::process_form`) becomes the orchestrator that catches `ExpansionError::Gap` and dispatches via the scheduler — exactly as `design/arch/facades/int.md` already specifies.

If `/arch` accepts (a)-(d), this is a substantial migration spanning frontend + types + int. Sprint planning consideration: this is the single largest contract-vs-source gap in the frontend BC and should be tracked as a bounded migration task before any facade-conformance test (M4 cargo-public-api) can run against the frontend.

## Context

Decision 8 ("MacroExpander trait deleted") retracted the trait-based dependency-inversion shape that an earlier design proposed. The replacement is the free-function form (`expand`) consuming a symbol-tables map directly. This is settled at the architectural-decision level; what's missing is the implementation move and the supporting types in `cranelisp-types`.

The two facades (frontend + int) are mutually consistent on this contract — `int::process_form` already references `cranelisp_frontend::expand` and pattern-matches on `ExpansionError::Gap(ResolutionGap)`. The boundary is fully designed. This FIXME is about making the source match the as-designed shape.

A single multi-wave sprint (or a coordinated triad cycle on frontend + types + int) is the natural execution unit. No facade text changes; only confirmation that the placement above is the canonical resolution and that types should land before frontend `expand` can.
