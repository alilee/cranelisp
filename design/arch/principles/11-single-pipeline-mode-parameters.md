---
number: 11
title: Single pipeline, mode parameters
---

# Principle 11 — Single pipeline, mode parameters

**Statement.** There is one compilation pipeline. Batch, REPL, and module-loading all flow through the same stages with the same types. Where modes genuinely differ (direct vs GOT-indirect calls), the difference is a parameter on a shared function, not a separate function or a separate type.

**Rationale.** Duplicate types at a pipeline boundary (e.g., `TopLevel` / `ReplInput`) and adapter functions between them (e.g., `build_check_for_backend`) are architectural violations: each duplicate is a divergence point that ages independently. The Sprint-26 dual-pipeline defect (`/arch`, `/qa`, three integrators all maintaining separate code paths for the same operation) is the canonical anti-pattern this principle prevents.

**Consequence.** `compile_to_module<M: Module>` has no mode discriminator (Decision 23); object vs JIT differs only in how the passed-in `Module` resolves the `__cranelisp_got_{module}` data symbol at finalize time. Cache-hit and fresh-build branch within ONE `register_module` flow, not in parallel codepaths (Decision 37). Type-checking does NOT differ by mode — the multi-pass pipeline (register all signatures, then check all bodies) works identically on any input size. *(Sprint origin: Sprint 26, dual-pipeline defect — see `archive/pipeline-convergence-review.md`.)*
