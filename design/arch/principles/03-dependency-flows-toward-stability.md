---
number: 03
title: Dependency flows toward stability
---

# Principle 03 — Dependency flows toward stability

**Statement.** `cranelisp-types` is the most stable crate (data definitions, no logic). Everything depends on it; it depends on nothing. When deciding where a type lives, put it in the most stable crate that makes sense. The dependency graph must be acyclic — Cargo enforces this at build time.

**Rationale.** Cycles between crates collapse the boundary. Pulling Cranelift IR types into `cranelisp-types` would invert the DAG; pulling typecheck-internal state into the frontend would invert it the other way. The DAG shape is what makes the boundaries enforceable.

**Consequence.** `cranelisp-types` MUST stay ignorant of `cranelift_jit::JITModule` and the linker. The `Code` enum lives in the integration layer (`src/code.rs`), not in `cranelisp-types` — see Decision 35 and the `super` arbitration in `super-import-arbitration.md` for canonical applications. When deciding placement: choose the most stable crate that has the information needed.
