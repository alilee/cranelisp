---
number: 15
title: Facade types live with their behavior
---

# Principle 15 — Facade types live with their behavior

**Statement.** Each crate's facade owns the types it originates. `cranelisp-types` holds *only* types referenced in two or more implementation-crate facades — the workspace's shared multi-consumer vocabulary. Types consumed only by `int` (the integration layer) live with their producer. There is no umbrella crate; consumers import directly from the originating crate.

**The placement heuristic.** A type lives in `cranelisp-types` IFF it is referenced in two or more implementation-crate facades. `int` is excluded from the count: it integrates everything by construction, so counting it would force every facade-output type into the shared crate by definition. Any type used by exactly one implementation crate plus int lives in that implementation crate.

**Rationale.** A network of crates that exchange definitions among themselves does not benefit from the consolidation pattern that umbrella crates (`tokio::prelude`, `bevy::prelude`) provide for end-user APIs — there is no "external user fragmentation" to hide. Hoisting all facade types into `cranelisp-types` (the "single source of definition" position) imposes orphan-rule ceremony on behavior-bearing types and decouples definitions from the inference / codegen / IO logic that produces them. Adding an umbrella above the network adds a re-export layer with no payoff for the existing consumers (`int` and the implementation crates themselves), all of whom already depend on the underlying crates by name. Letting types live where their behavior lives keeps each crate's definition-and-behavior pair local; the facade spec documents what crosses out; `cargo-public-api` per crate makes drift visible and gateable.

**Consequence.**

- **No re-exports of `cranelisp-types` items from implementation-crate `lib.rs` files.** Consumers import directly: `use cranelisp_types::Symbol`, `use cranelisp_typecheck::CheckResult`, `use cranelisp_backend::CompilationError`. The dep graph reads honestly.
- **`cargo-public-api` per crate is the change-control mechanism.** Per Principle 13 (`interfaces.md` is auditable), every facade is auditable; the per-crate `api.txt` is the audit-of-record. Drift surfaces at PR gate; arch approval required.
- **Naming follows location.** `cranelisp_typecheck::CheckResult` reads naturally — the crate prefix supplies the "Typecheck" context. No global-perspective rename is forced (in contrast to the umbrella + "single types crate" alternative).
- **External-audience exception (narrow).** A facade whose external audience does not (and should not need to) depend on `cranelisp-types` MAY re-export the items its public API uses. The criterion is concrete: an external consumer for whom `cranelisp-types` is not otherwise a natural dependency. Today this applies to `cranelisp-platform` (DLL authors writing out-of-tree crates that depend only on `cranelisp-platform`). Each invocation of the exception is justified inline in the facade spec; it is not a general license.

**Heuristic application — current sorting (Sprint 64 baseline).**

Stays in `cranelisp-types` (multi-implementation-crate consumers): the newtypes (`Symbol`, `FQSymbol`, `ModuleFullPath`, …); `Span`, `ErrorLocation`, `CranelispError`; `Sexp`, `Expr`, `TopLevel`, `Defn`, `Pattern`, `MatchArm`, `TypeExpr`, `Ast`; `SymbolTable`, `ModuleEntry`, `DefKind`, `Visibility`, `ImportSpec`, `ExportSpec`; `Type`, `Scheme`, `Subst`, `TypeId`; `ResolvedCall`, `MethodResolutions`, `ConstructorInfo`, `FieldInfo`, `TypeDefInfo`, `DisplayInfo`, `MonoDefn`; `SchedulingClass`; `PrimitiveDef`; `MacroClauseInfo`, `MacroParam`, `MacroClause`; `CallGraph`, `CallEdge`, `CallInfo`; `HeapHeader`, `HeapCategory`.

Moves out (single-implementation-crate origin): `CheckResult`, `CheckError`, `ResolutionGap`, `FormCheckResult`, `CheckPass`, `CheckState`, `TypeCheckEnv`, `ModuleCheckAccumulator`, `ReplSnapshot` → `cranelisp-typecheck`. `CompilationError`, `GotEvent`, `GotEventTag`, `GotProvenance`, `GotObserver` → `cranelisp-backend`. `IoEvent`, `IoObserver`, `IoTraceFlushGuard`, `SchedulerTraceFlushGuard` → `cranelisp-runtime` (already there per facade). `ExtractedDeclarations`, `StructuralDecls` → `cranelisp-frontend` (already there per facade). The relocation is tracked by a `/dev` FIXME spanning the affected crates; `int` import sites are rewritten as part of the same FIXME.

*(Sprint origin: Sprint 64 — FIXME 0002 resolution.)*
