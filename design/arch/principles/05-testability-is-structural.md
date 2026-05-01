---
number: 05
title: Testability is structural
---

# Principle 05 — Testability is structural

**Statement.** If a component can't be unit-tested without constructing the entire pipeline, the boundaries are wrong. Each crate must be testable with stubs at its boundaries.

**Rationale.** The prototype had 6192 lines of codegen with zero unit tests — not because of laziness, but because the code was structurally untestable (everything depended on everything). Untestable code is a structural defect, not a discipline failure.

**Consequence.** Cross-crate types cannot smuggle "open the world" handles (raw pointers to session state, references to pipeline orchestration) past the boundary. Cache schema versioning (Decision 34) is an example: an explicit `schema_version: u32` makes shape-mismatch failures testable and recoverable, where an implicit hash would not.
