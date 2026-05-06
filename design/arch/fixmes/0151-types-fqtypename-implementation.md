---
number: 0151
target: /dev
filed_by: /arch
filed_at: 2026-05-06
sprint_filed: 65
refers_to: design/arch/facades/types.md §"Resolved type system" + §"FQTypeName", design/arch/legacy/fqtypename.md, design/arch/facades/frontend.md, design/arch/facades/typecheck.md, design/arch/facades/backend.md, design/arch/facades/platform.md, design/arch/facades/intrinsics.md, design/arch/facades/int.md, design/arch/principles/15-facade-types-live-with-behavior.md (receiver-pinned exception), memory/project_fqtypename_priority.md
status: open
---

# Implement `FQTypeName` threading: lift binding facade commitment into source

## Issue

`facades/types.md` (post-Sprint-65 W2) commits to **`FQTypeName` as binding** for resolved-stage type identifiers:

> Every API past frontend's resolution stage that names a type uses `FQTypeName`; bare `TypeName` is reserved for syntactic-stage uses inside the frontend (parser output, AST surface, `TypeExpr` shape).

Pre-S65 the commitment was aspirational — facades cited `FQTypeName` in some positions while source still passed bare `TypeName` across resolved-stage boundaries. S65 W2 lifted the facade language from aspirational to binding (commit `2a6b4e7`) and ran a deliberate grep-and-classify pass over every facade. S65 W2.5 added the explicit receiver-pinned exception. The facade is now binding; **source has not yet been migrated**.

This FIXME tracks the implementation work to bring source in line with the binding facade. Per `memory/project_fqtypename_priority.md`, the user flagged FQTypeName migration as next-up after test stabilisation; this is the durable record.

## Proposed resolution

Multi-crate migration. The work bundles naturally with crate vertical sprints (S67+) and is NOT blocked on anything in S66.

### Scope — what migrates

Every API at a **resolved-stage boundary** that today takes a bare `TypeName` converts to `FQTypeName { module: ModuleFullPath, name: TypeName }`. Specifically:

- `Type::ADT` already takes `FQTypeName` per facades/types.md §"Resolved type system" — confirm the source matches.
- `TypeDefInfo.name: FQTypeName` — confirm.
- `MethodResolutions.impl_type: FQTypeName` — confirm.
- `ResolutionGap::Type(FQTypeName)` — confirm.
- `int::wait_for_typecheck_type(fqt: &FQTypeName)` — confirm.
- Any other API surfaces in `cranelisp-typecheck`, `cranelisp-backend`, `cranelisp-platform`, `cranelisp-intrinsics`, or `int` that today pass `&TypeName` across a *resolved-stage* boundary — convert.

### Scope EXCEPTIONS (explicit — do NOT migrate)

Per facades/types.md §"Resolved type system" and principles/15 §"Receiver-pinned exception":

1. **Frontend syntactic-stage uses.** `TypeExpr::Named(TypeName)`, `TypeExpr::Applied`, `TraitImpl.target_type`, `TraitDecl.type_params`, `parse_type_sig` output positions inside frontend AST nodes. Bare `TypeName` is correct here — module context is not yet known at the syntactic stage. The `TypeName → FQTypeName` lift happens inside `check_form` when a `TypeExpr::Named(name)` is resolved against the current scope plus imported modules.

2. **Reverse-lookup helpers on `Type`** (narrow exception #1 in facades/types.md §"Resolved type system"). `Type::from_name(&TypeName) -> Option<Type>` and `Type::type_name(&Type) -> Option<TypeName>` operate on the small set of built-in non-ADT types where the unqualified name IS unique (`Int`, `Bool`, `String`, `Float`, `Unit`). Keep bare `TypeName`.

3. **Receiver-pinned lookups** (narrow exception #2 in facades/types.md §"Resolved type system" + principles/15 §"Receiver-pinned exception"). `SymbolTable::get_type(&TypeName)` is keyed by bare `TypeName` because the `&self` receiver IS the module — wrapping the local-to-this-table key in `FQTypeName` would re-encode information already pinned by the receiver. The fully-qualified identity is reconstructible by the caller as `FQTypeName::new(module_of(&self), name.clone())` if needed downstream.

The exception list is structural, not aspirational. New APIs that fit either pattern (frontend syntactic stage, receiver-pinned single-module lookup) MAY take bare `TypeName`; otherwise `FQTypeName` is required.

### Implementation phasing

**Phase 1 — `/dev` (types crate)**: Confirm `cranelisp-types` exports a complete `FQTypeName` API surface — struct definition, constructors, `Display`/`Serialize`/`Deserialize` impls, helpers (`new`, `from_parts`, etc. as needed). The struct already exists per `facades/types.md` §"Fully-qualified references"; this phase is a confirmation + any helper-API gap fills surfaced by Phase 2's call sites.

**Phase 2 — `/dev` (typecheck crate)**: Migrate typecheck's API surface. The lift point — where `TypeName` becomes `FQTypeName` — lives inside `check_form` per facades/types.md §"Resolved type system". Touch points:
- `TypeDefInfo.name`: convert from `TypeName` to `FQTypeName` if not already.
- `MethodResolutions.impl_type`: convert if not already.
- `ResolvedCall::TraitMethod` etc.: ensure resolved type identifiers are `FQTypeName`.
- `CheckResult.type_defs`: confirm element type carries `FQTypeName`.
- Internal helpers in `cranelisp-typecheck/src/` that consume `&TypeName` at resolved-stage boundaries — convert.

**Phase 3 — `/dev` (backend crate)**: Migrate backend's consumed-type surface. Touch points:
- `Type::ADT(FQTypeName, ...)`: confirm pattern matches use `FQTypeName` fields.
- Drop-glue keying, layout-derivation maps, mangled-name generation: convert any internal `TypeName` keys to `FQTypeName` where the key crosses a resolved-stage boundary.
- The name-keyed primitive-substitution table at `cranelisp-backend/src/primitives_inline.rs` is keyed on `Symbol`, not `TypeName` — out of scope.

**Phase 4 — `/dev` (intrinsics + platform)**: Audit each crate for any resolved-stage `TypeName` that escaped the per-facade grep classification. Per facades/types.md, both crates already consume only `FQTypeName` — Phase 4 is verification.

**Phase 5 — `/dev` (int crate)**: Migrate consumer surface. Touch points:
- `wait_for_typecheck_type(fqt: &FQTypeName)`: confirm.
- `process_form` / `handle_gap`: confirm `ResolutionGap::Type(FQTypeName)` propagates correctly.
- Slash-command output (`/info`, `/sig`, etc.): the `Display` impl on `FQTypeName` should produce `:module/Name` per `repl/spec.md` §3 conventions.
- REPL display surface (`src/display.rs` per FIXME 0108): confirm `format_type_qualified` uses the `FQTypeName` from `Type::ADT` rather than constructing module prefixes ad-hoc.

**Phase 6 — `/qa`**: Per-phase test surface impact. The migration should be observable as: error messages now show `:module/Name` consistently rather than bare `Name`; `(/info Foo)` for an ambiguous bare name surfaces a "did-you-mean" with module-qualified candidates. `/qa` writes targeted tests for these visibility cases.

### Sequencing

- **Bundles with crate vertical sprints.** The natural shape is one phase per crate, in the order types → typecheck → backend → intrinsics → platform → int. Each phase is a small in-crate refactor + signature audit; not a sprint-sized increment on its own. Bundles into the relevant crate's vertical sprint at S67+.
- **Not blocked on anything in S66.** S66 facade-adoption work runs against the binding facade; if a Phase 1 helper is needed earlier, S66 may pull it in by filing an `/arch` follow-up FIXME for the narrow types-crate API addition.
- **Coordinates with FIXME 0098** (ResolutionGap/CheckError/ExpansionError migration). Both FIXMEs touch the same producer-side error variants. If FIXME 0098 lands first, this FIXME's Phase 2/5 grep against `ResolutionGap::Type` is straightforward. If this FIXME lands first, FIXME 0098's relocation does not have to renegotiate type-name shapes.

## Operational implication / Context

- **Aspirational-to-binding lift IS the architectural commitment of S65 W2.** The facade is binding from this sprint forward. Implementation deferral is intentional (multi-crate scope; bundles into crate verticals). The facade does not wait for implementation; source migrates against a stable target.

- **Receiver-pinned exception is structural, not transitional.** `SymbolTable::get_type(&TypeName)` stays bare per the user-decided W2.5 exception. The exception is documented inline at `facades/types.md` line 230 and `principles/15-facade-types-live-with-behavior.md` §"Receiver-pinned exception". Implementation MUST preserve this — converting `get_type` to take `FQTypeName` would re-encode information already pinned by the receiver and is explicitly out of scope.

- **Test impact: error message stability.** Some test assertions match against type-name display strings; the migration shifts unambiguous type displays from `Name` to `module/Name`. `/qa` audits assertions for tolerance (regex match where module prefix may vary, or full-string match where the prefix is explicit). Pre-S67 sprints should not introduce new tests that match against bare unqualified type names — they will need updating during the migration phase.

- **NOT a blocker for any open Decision.** Decisions 0010 / 0011 / 0027 / 0030 / 0031 / 0035 / 0040 / 0041 / 0042 / 0043 do not depend on this FIXME. The migration is orthogonal to all of them.

- **Memory flag origin.** `memory/project_fqtypename_priority.md` flagged FQTypeName as "next-up after test stabilisation". Filing this FIXME satisfies the visibility commitment and gives `/sprint` a single tracked locus for the migration work.

## Cross-references

- `design/arch/facades/types.md` §"Resolved type system" — the binding commitment + the two narrow exceptions
- `design/arch/legacy/fqtypename.md` — the original Sprint-51 design sketch (informs Phase 1's helper-API surface)
- `design/arch/principles/15-facade-types-live-with-behavior.md` §"Receiver-pinned exception" — the exception's principle-level statement
- `design/arch/sprint-65-reshape-phase-2-review.md` §4.1 — the FQTypeName threading second-order analysis that grounds the binding lift
- `design/arch/fixmes/0098-dev-frontend-typecheck-int-resolutiongap-checkerror-expansionerror-migration.md` — coordinating FIXME (touches the same producer-side error variants)
- `memory/project_fqtypename_priority.md` — user memory flag (origin)
