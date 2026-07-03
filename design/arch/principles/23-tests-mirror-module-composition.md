---
number: 23
title: Unit tests mirror module composition — submodule × scenario class
---

# Principle 23 — Unit tests mirror module composition (submodule × scenario class)

> Authored S102 Phase 2 (2026-07-03), resolving FIXME 0494 — the **architecture half** of the S101 user ruling whose methodology half is binding in `sprints/METHOD.md` §2.2 "Implementation-strategy unit scenarios". Formal ratification at the S102 Phase-7 close review per the sprint-close-only convention in `principles.md`.

**Statement.** Two coupled halves:

1. **Composition makes strategy seams visible.** A crate's internal module composition is an architectural surface: every strategy-bearing seam — a staging/commit split, a retention pool, a cache layer, a wrapper-emission path, a batch-derivation pass, a generation counter — is a *named submodule*, not an unnamed region inside a larger file. The bounded contexts (crate boundaries) are settled and are NOT governed here; this principle governs composition and accounting *inside* each crate.
2. **Test placement mirrors composition.** Each strategy-bearing submodule carries its own test module (`foo/tests.rs` or a `#[cfg(test)] mod tests` sibling to `foo.rs`), organized by scenario class **{complexity, edge — every cell of any implied matrix, negative}**, with scenarios expressed through the crate facade wherever the seam is facade-reachable (internal-invariant tests permitted; the facade is the default, so the tier survives refactors and reads as a contract). Coverage is thereby attributable and auditable **per submodule** — a coverage audit is mechanical, not archaeological.

**Why this is architectural, not only methodological.** The scenario space of an implementation strategy exists *below* the spec by construction — spec-derived testing (including `/qa`'s) structurally cannot see it; only the implementer knows it exists. The architecture's defense is representational (Principles 5/18/20 family): make the seam a submodule so it has a name, and make the test module its sibling so absence of coverage is *visible in the tree* rather than discoverable only by reverse-engineering a monolith.

**Named anti-pattern.** The monolithic crate-root `tests.rs`. S101 exhibit: backend's flat 5.9k-line `tests.rs` over 32.5k LOC of well-composed submodules — submodule-level coverage unattributable (FIXME 0495 is its drain; 0496–0498/0500–0502 are the sibling drains this principle governs).

**Role bindings.** `/design` names the strategy's scenario space in the per-crate design doc (the matrices, the boundaries — a design that does not name its matrix has not laid the strategy bare); `/dev` derives and lands the scenarios per METHOD §2.2 (the binding methodology text — maintained there, not duplicated here); `/review` treats a strategy-bearing seam carrying only happy-path pins as an **Important** finding; `/qa` audits unit tiers at submodule granularity (seam inventory = submodule inventory).

**Motivating register (S101).** 0479 — displacement matrix: only the design-named cell was pinned; the complementary cell was a live UAF caught by review. 0483/0488 — instantiation matrices: single cells pinned; SIGBUS one step out. /port's D1/D2 — regeneration/adoption strategies with zero unit scenarios.

**Cross-references.**

- Principle 5 — Testability is structural (this principle is its unit-tier/interior instance).
- Principle 22 — companion-tripwire rule (same pattern: the guard lands in the same change-set that creates the hazard).
- `sprints/METHOD.md` §2.2 "Implementation-strategy unit scenarios" — the methodology half, binding on `/dev`.
- `memory/feedback_dev_strategy_derived_unit_scenarios.md` — the originating user ruling.
