---
number: 0374
target: /typecheck
filed_by: /arch
filed_at: 2026-06-16
sprint_filed: 83
refers_to: design/arch/bounded-contexts.md §2 (monomorphisation-from-roots note), design/arch/bounded-contexts.md §3 invariant 9, crates/cranelisp-typecheck/src/program.rs + crates/cranelisp-typecheck/src/traits.rs (collect_local_parametric_calls, monomorphise_inner_parametric_hops), commits 5634dd3 + 9e57330 + the 0355 machinery
status: open
---

# Typecheck: Tier 2 — systematic full monomorphisation from the roots (no Type::Var reaches codegen)

## Issue

The 0373 investigation settled full monomorphisation-from-roots as the architectural target (rank-1 HM ⇒ complete; keeps representation backend-internal; the only sound fix over the rejected runtime-RC-witness / tagged-value alternatives). The architecture is recorded at `bounded-contexts.md` §2 (typecheck) + §3 invariant 9 (backend RC soundness).

**S83 delivered Tier 1 + Tier 1.5** (`5634dd3`, `9e57330`): polymorphic-**result-hop** monomorphisation, same-module and cross-module, routed through the 0355 machinery (`collect_local_parametric_calls`, `monomorphise_inner_parametric_hops`). This closed the SIGSEGV that motivated the investigation but covers only a subset — the result-hop / 0355-constrained / cross-module cases.

**Tier 2 is the systematic remainder:** generalise the per-`(Def, type-args)` instance model so that **every reachable fn instance** has fully concrete parameter and result types, under any reachable instantiation — so NO `Type::Var` reaches the codegen boundary. This is the prerequisite for backend RC soundness: while a `Type::Var` can flow to codegen, `HeapCategory::classify(Type::Var)` falls back to `Mixed` and emits the unsound `<1024` RC guard (negative/`≥1024` `Int` misread as a heap pointer → use-after-free on the dec path; BC §3 invariant 9 has the full statement).

## Proposed resolution

Generalise the Tier-1/1.5 polymorphic-result-hop machinery into a full monomorphisation-from-roots pass: enumerate reachable instances from the program roots, instantiate each `(Def, concrete-type-args)` pair, and ensure no instance leaves a residual `Type::Var` at any codegen-visible position. Build on `5634dd3`/`9e57330` and the 0355 machinery rather than a parallel pass. Connects to the deferred concurrency/mono work (cross-reference at scheduling time). Unconstrained top-level type vars that no instantiation pins are out of scope for codegen by construction — they are an ambiguity error owned by /spec (FIXME 0373 part (ii)).

The fix lands with unit tests at the typecheck seam per the per-fix discipline; assess the e2e need (the original defect was a `--run` SIGSEGV, so an end-to-end repro across modes is warranted — coordinate with /qa).

## Operational implication / Context

**Gates two downstream FIXMEs:**
- **0373 part (iii)** (/spec) — relaxing §12.1 to backend-internal representation is gated on Tier 2 concreteness.
- **0375** (/backend) — making `classify(Type::Var)` an assert/panic and retiring the `<1024` guard from the `Type::Var` path is gated on Tier 2 guaranteeing concrete types at codegen.

Companion: FIXME 0373 part (i)/(ii) (/spec — state rank-1 HM; ambiguity rule). Likely a dedicated sprint (the investigation framed Tier 2 as the systematic remainder warranting its own increment). Architecture conclusion: `bounded-contexts.md` §2 + §3 invariant 9.
