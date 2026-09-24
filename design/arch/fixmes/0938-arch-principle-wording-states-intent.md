---
number: 0938
target: /arch
filed_by: /sprint
filed_at: 2026-08-29
sprint_filed: 119
refers_to: design/arch/principles/CLAUDE.md;
  design/arch/principles/24-resolve-once.md
status: open
---

# Principle-authoring convention: the wording states intent, never verified against the implementation

## The user ruling to place (S110, Principle 24 ratification)

1. A Principle's wording states what the architecture should guarantee. It is
   not checked against the current implementation first.
2. An implementation deviation is an instance of the defect class the
   Principle names, never counter-evidence against the wording. The
   compliance sweep is a follow-up consequence, not an input.
3. At a ratification gate, strengthen a proposed Principle by asking "can we
   name one valid instance of the thing we are calling suspect?" Worked
   example: Principle 24 widened from a backend-scoped "keyed read versus
   search" to a compiler-wide rule because no search of compile-necessary
   identity survived that question; the import chain is a bounded sequence
   of keyed lookups, not a search.

## Current state (verified 2026-09-24)

`design/arch/principles/CLAUDE.md` governs principle authoring and
membership. It and the shared `maintain-documents` support skill require
current intent over history, but neither states the three rules above.
Principle 24's text already carries the resulting acid test and carve-outs;
the derivation method is not recorded as repeatable.

## Remaining obligation

`arch` places the three rules in one carrier at the Phase 7 principle review —
`design/arch/principles/CLAUDE.md` is the default, or a shared-package
contribution if the rule proves project-neutral. The user's local memory entry
"Principle wording states intent" retires when this lands.

## Closure

The rules are in their chosen carrier; this filing and the memory retire.
