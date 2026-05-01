---
number: 09
title: Rings are accretive
---

# Principle 09 — Rings are accretive

**Statement.** Each ring adds code, tests, and capabilities — it should not replace or delete work from earlier rings. Earlier-ring tests remain as-is; later rings add new tests for the new mechanism.

**Rationale.** Accretive rings provide diagnostic isolation: if `(+ 1 2)` (trait dispatch, Ring 2) fails but `(add-i64 1 2)` (primitive, Ring 0) passes, the bug is in dispatch, not codegen. Primitives survive as the foundation that higher-level mechanisms dispatch to.

**Consequence.** Ring 0–1 `BuiltinFn` resolution and Ring 2 `TraitMethod` resolution coexist (Decision 15). When a higher-ring mechanism subsumes a lower-ring one, the lower-ring path is not deleted — it remains as a regression net and as the implementation backbone the higher-ring mechanism delegates to.
