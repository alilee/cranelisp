---
id: ACT-1082
title: A qualified reference written through a module alias is reported, and in one REPL order resolved, against the alias as if it were a module
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - spec/08-modules.md
  - design/arch/interfaces.md
  - design/int/int.md
  - tests/spec_08_modules.rs
---

## Observation

`qa`'s full run on the debug build of `a205a29f`, 2026-11-18. Four cells
of `tests/spec_08_modules.rs` fail, written by `test` at `da90a23d`,
`7c8e1d65` and `a76e42e4`.

- **An absent member.** `zz.cl` defines `zf`. A module declares
  `(import [(zz z) [zf]])` and calls `(z/nope)`. Spec §8.5.4 edge 4
  requires `module 'zz' has no member 'nope'`. Under `--run`, `--link` and
  the REPL the diagnostic names `z`, which is not a module.
  `s124_missing_member_alias_neg_{run,link,repl}` fail on it; the control
  that writes `(zz/nope)` passes in every mode.
- **A graph loaded through an alias.** In ACT-1081's module tree,
  `P/c.cl` declares `(import [(z zz) []])` and calls `(zz/zf)`. A cold
  REPL whose first turn is `(z/zf)` reports
  `module 'zz' referenced by 'zz/...' not found`. The other REPL order
  and the three batch entries give 11.
  `s124_declared_child_alias_graph_repl_orders_agree` fails on
  `[false, true, true, true, true]`; the same tree without the alias
  agrees on every route.

## Classification

- **A defect:** spec §8.6.6 substitutes an alias before a qualified name
  is resolved, and §8.5.4 edge 4 words the absent-member error by the
  module.
- **Class:** `wrong-scope-lookup` for the diagnostic; the REPL face is a
  refusal of a legal program in one order of two.

## Attribution: provisional

- **Design's reading** ([interfaces, *Resolution gaps*](../../design/arch/interfaces.md#resolution-gaps);
  [int §6.3.1](../../design/int/int.md#631-locating-a-gap-at-its-reference-site)):
  typecheck's `resolve_qualified` puts the written qualifier in a
  member-absent `ResolutionGap`, and the binary reads that as a module to
  load and to name. `qa` did not observe the gap value at its seam.
- **Refuted if** a build whose member-absent gap carries the substituted
  module still fails any of the four cells.
- **Owner:** typecheck for the producer, once `arch`'s proposed rule (every
  gap names the module after one alias substitution) has the user's
  approval. It changes what a public value means between crates, so it is
  held at the user's gate and is not in source.

## Evidence

The four committed cells and their controls are the allocation. `arch`'s
row adds a typecheck module test at `resolve_qualified`.

## Completion evidence

The four cells pass with their controls unchanged; the module test is in
source; `qa` judges adequacy and deletes this action.
