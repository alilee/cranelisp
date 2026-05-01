---
number: 06
title: Complexity has a budget
---

# Principle 06 — Complexity has a budget

**Statement.** Every abstraction, indirection, or generalization must justify the complexity it introduces against the coupling it removes. A premature abstraction that serves no current ring is debt, not architecture.

**Rationale.** The ring model exists so that Ring 0 code carries zero heap complexity. `compile_to_module`'s mode parameter exists so that batch and REPL share one pipeline instead of two. But abstractions that anticipate features the spec does not yet require accrue cost without payoff and tend to be wrong by the time the feature lands.

**Consequence.** Mutual-import deadlock under the form-by-form scheduler (Decision 30) is an instance of this principle in action — the workaround is clear and ergonomic via `discover-tests`, so the constraint is accepted rather than papered over with a half-fix. A real fix requires a major scheduler redesign and is flagged as future research, not roadmap work.
