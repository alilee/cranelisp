---
number: 01
title: Decoupling over convenience
---

# Principle 01 — Decoupling over convenience

**Statement.** Each crate should be independently compilable, testable, and replaceable. If adding a feature requires modifying three crates, the boundaries are wrong.

**Rationale.** The prototype's `CompiledModule` was convenient (everything in one place) and catastrophic (133 references across 18 files, untestable in isolation). Boundaries that admit shared mutable structure end up dragging the whole codebase along on every change.

**Consequence.** Boundary types live in `cranelisp-types` and carry only the information the consuming crate needs (Principle 2). Crates do not share runtime state across the boundary other than through that types crate. A change scoped to one crate's bounded context must compile, test, and ship without touching other crates.
