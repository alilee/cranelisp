---
number: 0494
target: /arch
filed_by: /sprint
filed_at: 2026-07-03
sprint_filed: 101
refers_to: design/arch/ facade conventions, .claude/commands/{arch,design,dev,review}.md import blocks, sprints/METHOD.md §2.2 "Implementation-strategy unit scenarios"
status: open
---

# Facade test-organization convention — codify implementation-strategy unit scenarios at the architecture level

## Issue

User ruling (S101 Phase 6b): `/dev` unit tiers systematically under-cover scenarios that arise from the **implementation strategy** rather than the spec — complexity paths, edge cells of strategy-implied matrices, and negative cases. S101 evidence: 0479 (displacement matrix — only the design-named cell pinned; the complementary cell was a live UAF found by review), 0483/0488 (instantiation matrix — single cells pinned; SIGBUS one step out), /port's D1/D2 (regeneration/adoption strategies, zero unit scenarios). These are invisible to spec-derived testing by construction — only the implementer knows the strategy's scenario space exists.

The methodology half is now binding in `sprints/METHOD.md` §2.2 ("Implementation-strategy unit scenarios"). The architecture half is missing: the facade conventions say nothing about test organization, and the per-crate skill definitions don't instruct the discipline.

## Proposed resolution

1. Extend the facade conventions (wherever facade convention items live in `design/arch/`) with a **test-organization** item: unit tiers organized by **submodule × scenario class {complexity, edge, negative}** — each strategy-bearing submodule carries its own test module (`foo/tests.rs` or a `#[cfg(test)] mod tests` sibling), scenarios expressed through the crate facade wherever reachable (internal-invariant tests permitted, facade default), so coverage is attributable and auditable per submodule.

   **User refinement (S101, post-filing):** the bounded contexts (crate boundaries) are settled and are NOT in question — the convention governs **internal module composition inside each crate** and per-submodule test accounting. The named anti-pattern is the monolithic crate-root `tests.rs` (exhibit: backend's flat 5.9k-line `tests.rs` over 32.5k LOC of well-composed submodules — submodule-level coverage is unattributable). `/arch` may fold this into the facade conventions as a companion *module-composition* convention: submodule structure should make strategy-bearing seams visible, and test placement should mirror it.
2. Propagate to the four import blocks (`arch`/`design`/`dev`/`review` command defs) per the Principle-22 precedent: `/design` names the strategy's scenario space in the design doc (the matrix, the boundaries); `/dev` derives and lands the scenarios; `/review` treats a strategy-bearing seam with only happy-path pins as an Important finding.
3. Consider whether this is a numbered architectural principle (it pairs naturally with Principle 22's tripwire-companion rule) or a facade-convention item — /arch's call.

## Operational implication / Context

`/qa`'s S101 risk review + coverage audit (in flight) gains a per-crate unit-tier axis assessed **at submodule granularity** (seam inventory = submodule inventory; map existing tests to submodules; flag zero-coverage and happy-path-only submodules); its findings will land as FIXMEs against `/dev`(crate) for S102 D/D/R drains. This convention is what makes those audits mechanical rather than archaeological. Backend (~10 tests/kLOC, monolithic root `tests.rs`) and the pre-S101 src/ session seams are the known-thin surfaces.
