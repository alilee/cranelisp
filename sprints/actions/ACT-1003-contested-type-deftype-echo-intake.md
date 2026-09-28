---
id: ACT-1003
title: Classify the missing constructor listing for a type whose name another type's constructor shares
status: open
priority: advisory
from: qa
to: qa
sprint: 122
filed_at: 2026-09-28
refers_to:
  - src/repl/format_type.rs
  - crates/cranelisp-types/src/module.rs
  - repl/spec/04-self-documentation.md
  - repl/spec/01-display-format.md
---

## Request

`qa` classifies this lead. It needs one discriminating probe, directed to
`test`, before it becomes a defect or is dismissed. It is neither a blocker
nor a reopening of
[ACT-1002](ACT-1002-contested-type-name-constructor-pattern-intake.md).

## Observation (unreduced, pre-ACT-1002-fix binary)

- **Requirement.** REPL spec §4.1 and §1 show `:user/Color ; deftype` followed
  by `; match:` and the constructor list. The listing is omitted only when
  empty.
- **World.** `(deftype Qtok (Qa [:Int n]) Qb)` then
  `(deftype Qwrap (Qtok [:Int x]))`, entered at the REPL.
- **Observed.** The warm (cache-restored) leg echoes `:user/Qtok ; deftype`
  with no `; match:` section. The fresh leg lists `Qa Qb`. `Qwrap` keeps its
  listing in both legs.
- **Control.** With `Qwrap2 (Qother …)` in place of `Qwrap`, both legs list
  `Qa Qb`.
- **Evidence.** `.local/s122-act1002-test/probe-repl-text.log`: lines 31–38
  are the fresh leg and 44–49 the warm leg. The omission was seen in two
  runs. The cell has been removed; nothing is committed.

## Mechanism (source-predicted, not observed at its seam)

- The deftype formatter in `src/repl/format_type.rs` reads the constructor
  list through `cranelisp_types::lookup_type_def_chain(…, module, &tn)`.
  That read is by the bare spelling, rooted at the home module.
- In the warm leg, `Qwrap.Qtok` is already registered when `Qtok` is echoed.
  The spelling is then contested and the read is predicted to return `None`,
  which omits the section silently. This is the same collapse ACT-1002
  confirmed for pattern readers.
- If the prediction holds, this is a contested-spelling defect in a REPL
  display reader. It is not a cache-persistence defect: the cache only
  changes the timing.
- **Falsifier.** A fresh session that defines `Qwrap` before `Qtok`, or
  enters bare `Qtok` after both, still lists `Qa Qb`. The cause would then be
  cache restoration, and attribution moves to the persistence layer.

## Next step

`test` runs one fresh-only probe, with no cache: define both types, then
enter bare `Qtok`. Include the reversed-order declaration. `qa` then does one
of the following:

- attributes the defect and directs a failing, unignored cell, owned by
  `/dev` on `src/`. Its `// defect:` class comes from the `tests/CLAUDE.md`
  vocabulary. No current class names a display reader that collapses a
  contested spelling, so `qa` may need to add one;
- or dismisses the lead with the probe as evidence.

The ACT-1002 correction did not touch this reader, so the fixed binary is
expected to show the same observation.

## Completion evidence

- The probe result is recorded here.
- Either a committed failing cell with its owner named, or a dismissal with
  its evidence.
