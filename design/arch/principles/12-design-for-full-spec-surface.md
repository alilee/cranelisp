---
number: 12
title: Design for the full spec surface
---

# Principle 12 — Design for the full spec surface

**Statement.** Pipeline stage interfaces are designed against all language features the spec defines, not against the current sprint's needs. Every variant of a boundary type that the spec requires should exist from the start, with `todo!()` bodies if not yet implemented.

**Rationale.** Accretive growth — each sprint adding variants and match arms to whichever function is closest — eventually produces parallel paths nobody designed. A `todo!()` is visible and compiler-enforced; a missing arm in a parallel function is silent.

**Consequence.** New `Expr` variants for spec-required forms are added when the spec adds them, not when the implementation reaches them. `interfaces.md` (the narrative companion to `cranelisp-types`) documents the full surface, and the types crate carries the complete shape even if some arms are stubs. *(Sprint origin: Sprint 26 — the ring model's accretive delivery pattern caused the dual-pipeline defect.)*
