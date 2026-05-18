---
number: 18
title: Enforce architectural invariants structurally where possible
---

# Principle 18 — Enforce architectural invariants structurally where possible

**Statement.** When the workspace DAG, the type system, or the public-surface contract can *prevent* the violation of an architectural invariant by construction, prefer that mechanism over runtime checks, lints, code-review discipline, or behavioral tests. Structural enforcement makes the invariant a property of the artefact, not a property of the test suite that probes it.

**Rationale.** Behavioral tests (CLIF-shape inspection, AST walks, "the emitted code never contains pattern X") verify the invariant in a single compilation path. Structural mechanisms — workspace dep-bans, sealed traits, `pub(crate)` visibility, type-parameter constraints, single-source-of-truth fields — foreclose the violation across *every* compilation path (debug, release, future codegen modes, `#[cfg(test)]` shims, hypothetical extensions). The structural form is strictly stronger. It is also typically cheaper to test (parse the artefact; assert presence/absence of a name) and immune to "the test ran but the wrong path was exercised" failure modes.

The principle does not claim every invariant admits a structural form. It claims that *when both options exist*, the structural option is the right choice.

**Worked example — primitives dispatch (Decision 0048 §"Structural invariant — backend dep-ban", S68 Phase 3, 2026-05-17).** The architectural invariant "backend reaches primitives via the GOT, never via direct extern" was originally proposed as a CLIF-inspection test: "scan backend's emitted CLIF for direct calls to primitive symbols; assert none exist." User-arbitrated revision converted it to a workspace dep-ban: `cranelisp-backend` MUST NOT depend on `cranelisp-primitives`. With no Rust-path visibility into primitives' fns, backend physically cannot emit a direct-call instruction targeting one — the only available dispatch is the type-erased SymbolTable + GOT mechanism in `cranelisp-types`. The test reduces to a one-line Cargo.toml parse. The invariant is now a property of the workspace, not a property of the test that probed it.

**When to reach for the structural mechanism.**

- **Workspace dep-bans** — when crate A must not name crate B's items, but A and B both exist in the workspace. Removing the dep edge (and keeping the workspace acyclic) makes the constraint structural. Cost: zero (no test infrastructure); enforced at every `cargo build`.
- **Sealed traits** — when a trait must be implemented only inside the crate that defines it. The private-supertrait pattern makes external impls impossible. Cost: one extra trait declaration; enforced at compile time.
- **`pub(crate)` defaulting** — when an item is internal but is `pub` by oversight. Demoting to `pub(crate)` removes the item from the public surface; `cargo-public-api` baselines + `/review`'s per-PR audit make further drift visible. Cost: one keyword change per item; enforced at compile time.
- **Type-parameter constraints** — when a type must carry a specific kind of payload (e.g., `SymbolTable<Code, ()>` parametrised by lifecycle owner). The type system rejects mismatches at every call site. Cost: one type parameter; enforced at compile time.
- **Single-source-of-truth fields** — when a value must have exactly one canonical home (Decision 35 — GOT is the single source of truth for callable addresses; no per-entry pointer field). Multi-home shapes drift; single-home shapes cannot. Cost: discipline around field placement; enforced by code review + the test suite for whichever single home exists.

**When the behavioral form is the right answer.**

Some invariants do not admit a structural form. Examples: "the typed AST after monomorphisation has no remaining type variables" (a property of an algorithm's output, not of a type signature), "the cache .meta.json byte-for-byte reproduces from the same source" (a property of serialisation that the type system cannot constrain). These are caught by tests, not by construction. Principle 18 is about preferring the structural option *when both exist*, not about retrofitting structure where it does not naturally fit.

**Consequence.**

- When proposing a new invariant, `/arch` evaluates the structural option first. Only when no structural form is available (or available structural forms are disproportionately expensive) does the behavioral test become the primary enforcement.
- When auditing an existing invariant enforced behaviorally, `/arch` asks whether a structural form is reachable in a reasonable migration. If yes, the migration to the structural form is itself a refactor candidate.
- `/qa` does not write behavioral tests for invariants that have a structural form. The structural mechanism IS the test; one Cargo.toml assertion (or one `cargo-public-api` baseline diff) is the standing check.
- `/dev` resists adding "convenience" dep edges that would weaken an existing structural invariant. The dep edge is the test surface; loosening it loses the property.

**Cross-references.**

- Principle 05 — Testability is structural (the antecedent; this Principle extends from "tests are easier when boundaries are right" to "the right boundary often replaces the test entirely").
- Principle 07 — Single source of truth (single-home placement is one form of structural enforcement).
- Principle 13 — `interfaces.md` is auditable (`cargo-public-api` is the audit-of-record for structural public-surface invariants).
- Decision 0048 — the worked example: backend dep-ban as structural enforcement of the GOT-dispatch invariant for primitives.
