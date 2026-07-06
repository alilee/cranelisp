---
number: 0531
target: /repl
filed_by: /sprint
filed_at: 2026-07-06
sprint_filed: 103
refers_to: repl/spec.md §18.1.1, design/int/session-transaction.md §10, spec/ (§18 cross-ref)
status: open
---

# repl/spec.md §18.1.1 normative text now contradicted by the shipped T1 full cure

## Issue
S103 Wave 4 landed the T1 full cure: an unannotated-fn redefinition that in S102
downgraded to a silent split-world (mitigated by a printed `; stale:` section) now
**recompiles the stale callers** at end-of-turn so they see the new definition, and the
`stale:` section renders **empty**.

`repl/spec.md §18.1.1` still carries the pre-cure normative text: "The report is
informational only. It recompiles, breaks, and traps nothing," plus a worked example
showing `(g 1) → 2` (the OLD chain) and a printed `; stale:` section. Shipped code now
contradicts both: the caller recompiles (observes the new def), and the section is omitted.

The Wave-4 /review flagged this (Finding 2). The Phase-3 /design(src/) plan anticipated
routing the corrective wording to a separate `/repl` CS-2 increment; that increment was NOT
in the Wave-4 change-set, so the spec is stale-until-updated.

## Proposed resolution
`/repl` updates §18.1.1 (with `/spec` cross-check on §18) to the cured semantics:
- The stale downgrade now triggers an end-of-turn module reload; the previously-stale
  caller **recompiles** and picks up the new definition (the §18.1.1 negative-MUST is
  now satisfied by construction, not by a warning).
- The `stale:` section renders empty on a successful cure; it prints only on the CS-3
  edge paths (regen-suppressed module keeps the interim print; reload-failure →
  §14.4 error-blocked).
- Refresh the worked example to the cured values (the acceptance test
  `t1_full_cure_recompiles_stale_callers_stale_section_empty` pins them).
- Update the `[Tested+Neg]` annotation to reference the acceptance pair.

## Operational implication / Context
Testless spec-text update — the failing/flipped tests already pin the behaviour; this is
the normative-record catch-up. Until it lands, §18.1.1's prose describes retired behaviour.
Pairs with [[0507]] (the T1 design holes, now largely resolved) and the S102 §18.1.1 print
mitigation that the cure supersedes.
