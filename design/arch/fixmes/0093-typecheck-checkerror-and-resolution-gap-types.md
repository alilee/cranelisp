---
number: 0093
target: /arch
filed_by: /design
filed_at: 2026-05-01
sprint_filed: 63
refers_to: design/arch/facades/typecheck.md §"Public surface (as-designed)" + §"Re-exports from cranelisp-types", design/arch/facades/int.md §"process_form — the gap-orchestration retry loop", crates/cranelisp-types/src/, crates/cranelisp-typecheck/src/lib.rs, design/arch/fixmes/0008-typecheck-symboltable-per-symbol-mutability.md, design/arch/fixmes/0092-frontend-expand-and-resolution-gap-types-not-yet-in-types.md
status: open
---

# `CheckError`, `ResolutionGap` not yet in `cranelisp-types`; `check_form` cannot conform to its facade signature without these boundary types

## Issue

The typecheck facade specifies:

```rust
pub fn check_form(
    node: Ast,
    table: &SymbolTable<Code, ()>,
    symbol_tables: &SymbolTables,
) -> Result<CheckResult, CheckError>;
```

with re-exports including `CheckError` and `ResolutionGap` from `cranelisp-types`. The int facade's `process_form` (`facades/int.md` §"process_form — the gap-orchestration retry loop") catches `CheckError::Gap(ResolutionGap)` and dispatches via the scheduler — exactly mirroring the frontend-side `ExpansionError::Gap(ResolutionGap)` flow.

Today's source has none of this:

1. `CheckError` does not exist in `cranelisp-types`.
2. `ResolutionGap` does not exist in `cranelisp-types`.
3. The current implementation returns `CranelispError` (not a typecheck-specific error type) and has no gap-return mechanism — the per-form scheduler at `int` detects unresolved-symbol cases through ad-hoc dependency detection, not through a typed Gap path from typecheck.
4. `cranelisp-typecheck/src/lib.rs` re-exports a small subset (`CheckResult`, `CranelispError`, `ReplSnapshot`, `TopLevel`) — the full facade re-export set (incl. `CheckError`, `ResolutionGap`, `ConstructorInfo`, `DisplayInfo`, `FieldInfo`, `MethodResolutions`, `MonoDefn`, `ResolvedCall`, `TypeDefInfo`, `Scheme`, `Subst`, `Type`, `TypeId`) is target-state, not as-built. (The re-exports policy is itself FIXME 0002's question — but the *types being missing* is upstream of the re-exports question.)

The typecheck per-crate design doc (`design/typecheck/typecheck.md`) cannot describe HOW the crate fulfils the facade without this scaffolding existing somewhere. The design intent is committable today (the contract is internally consistent and implementable, and FIXME 0008 already pins the mutability discipline that flanks it), but the boundary types must land in `cranelisp-types` before `/dev` can build the free-function `check_form` to the facade.

This is the typecheck-side mirror of FIXME 0092 (frontend-side `ExpansionError`/`ResolutionGap`).

## Proposed resolution

Confirm placement and ordering — coordinated with FIXME 0092 since the two share `ResolutionGap`:

(a) `ResolutionGap` lands in `cranelisp-types` as a public enum alongside `FQSymbol` and `FQTypeName`. Carries `SymbolTypechecked(FQSymbol)`, `Type(FQTypeName)`, and `MacroInMem(FQSymbol)` per the facade. Both `ExpansionError::Gap` and `CheckError::Gap` carry it. (FIXME 0092 already proposes this for the frontend side; this FIXME confirms the typecheck side needs the same type. Land once.)

(b) `CheckError` lands in `cranelisp-types` (alongside `CheckResult`) as the public error type for `check_form`. Variants per facade §"Returns": `Gap(ResolutionGap)`, `TypeError { … }` carrying `ErrorLocation` per Decision 39. Per facade §"Re-exports", typecheck re-exports `CheckError` and `ResolutionGap` for ergonomics (subject to FIXME 0002's policy on convenience re-exports of types-crate items).

(c) Once (a) and (b) land, `check_form`'s migration to the free-function shape (FIXME 0008's main pivot) becomes mechanical — the function's return type changes from `Result<FormCheckResult, CranelispError>` to `Result<CheckResult, CheckError>`, and the gap path exists to be raised from the unresolved-FQ-symbol-or-type detection points already present in `infer.rs`'s deferred trait-call resolver and `program.rs`'s post-pass dependency analysis.

(d) The integration layer (`int::process_form`) becomes the typed orchestrator that catches `CheckError::Gap(ResolutionGap)` and dispatches via the scheduler — exactly as `design/arch/facades/int.md` already specifies. The current ad-hoc detection at `int` is replaced by typed pattern-matching on the variant.

## Sequencing

This depends on FIXME 0092 (`ResolutionGap` placement in `cranelisp-types`). Suggest landing them together as a single types-crate addition that unblocks both frontend's `expand` and typecheck's `check_form` migrations.

Independently of FIXME 0008's mutability work — which can land first — but together with the free-function migration which FIXME 0008 names as the target shape. Practically: a sprint that adds (a) + (b), then a follow-on sprint that drives the source migrations on both sides.

## Operational implication

- Until this lands, the typecheck per-crate design doc carries a "Drift between facade and current source" register (`design/typecheck/typecheck.md` §2.1) naming this gap explicitly. The register is not silent debt — it is the migration backlog.
- Until this lands, `/qa` cannot author the proposed narrow unit tests for the gap-return contract from typecheck's side (one per `ResolutionGap` variant) — the variants don't exist to test against.
- Until this lands, the int → typecheck call site (`facades/int.md` line 564) is documentation, not real code — the actual `process_form` calls a different path through `TypeCheckEnv`. The drift between `facades/int.md` and `int`'s current source is a separate matter (covered by FIXME 0009), but this FIXME removes one prerequisite to closing it.

## Context

Surfaced during the S63 `/design` refresh of `design/typecheck/typecheck.md`. The refresh confirmed the contract (BC + facade + Decisions 38/39) is internally consistent and implementable, and named six prioritised audit remediations as the immediate `/dev` work — but identified that the boundary-type addition (this FIXME) is upstream of the free-function `check_form` migration that FIXME 0008 specifies.

The contract is settled at the architectural-decision level via Decisions 14, 19, 22, 38, 39 plus the gap-return pattern documented in both facades. What's missing is the implementation move and the supporting types in `cranelisp-types`. No facade text changes; only confirmation that the placement above is the canonical resolution and that types should land before `check_form` can take its facade shape.
