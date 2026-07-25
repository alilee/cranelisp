---
number: 0889
target: /design
filed_by: /sprint
filed_at: 2026-07-26
sprint_filed: 118
refers_to: src/marshal.rs (header: "their RC is never decremented");
  src/expander.rs §invoke_clause (result tree dropped unconsumed);
  design/arch/fixmes/0835-slist-sexp-construction-corrupts-the-heap-at-small-sizes.md §Branch-F falsification pointer;
  tests/plan/s118-test-plan.md §2.5 (Branch-F execution record);
  sprints/archive/sprint-118.md §Notes 2026-07-26 (user decision)
status: open
---

# Recover the macro-turn marshal leak (the ambient 1143 prelude residue)

Surface: Binary/int (`src/marshal.rs` + `src/expander.rs`). `/design`(int)
rules the ownership protocol BEFORE any `/dev` dispatch.

**USER DECISION (2026-07-26, S118 Branch-F closure):** S118 makes the
exit-balance *instrument* truthful (marginal/twin-control accounting in the
affected cells) and explicitly accepts the leak for now; this FIXME is the
user-required record that the leak itself must be recovered in a future
sprint — accounting around it is not closure.

## The defect

Every macro expansion leaks, by documented design, at the int-side macro-turn
marshal boundary:

- marshalled argument trees are never RC-decremented (`src/marshal.rs` header
  states this as intent; each cell further pinned by the FIXME-0638
  `protect_marshalled_cell` +1);
- the expansion-result tree is never consumed after `runtime_to_sexp` copies
  it (`src/expander.rs` `invoke_clause` drops the `i64`).

Closed-form residual, exact on every S118 probe point: **|marshalled arg
cells + args spine| + |non-aliased result-tree cells|, per expansion.** Full
stdlib prelude: 1,143 allocations per session. Compile-time bounded; does not
grow with runtime execution (P1/P2 probes = 0).

## Resolution requirements

- True balance at the macro-turn boundary: post-turn deep-release of the
  marshalled argument trees + consume of the expansion result, with
  result↔argument **aliasing** handled (P3c's result aliases its arg — a
  naive release double-frees; the FIXME-0638 interior-alias double-free
  history shows this has burned once already), OR an arena/epoch expansion
  allocator that reclaims the whole turn wholesale (see
  `design/arch/` S119 structural option paper, marginal-balance/arena
  options).
- The S118 exact-value probe pins (P3 +2, no-quote +1 class) flip from
  documented-residual to zero in the fixing change-set.
- The S118 marginal-accounting instrument remains valid afterwards (it
  measures runtime behavior either way).

Scheduled: S119, under the structural option paper's disposition.
