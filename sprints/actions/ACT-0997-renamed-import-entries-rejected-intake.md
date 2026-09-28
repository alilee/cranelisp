---
id: ACT-0997
title: Route the rejection of renamed import and export entries
status: open
priority: normal
from: qa
to: qa
sprint: 122
filed_at: 2026-09-27
refers_to:
  - spec/08-modules.md
  - crates/cranelisp-frontend/src/module_extract.rs
  - crates/cranelisp-types/src/module.rs
  - src/save.rs
---

## Observed defect

Spec §8.3.5 admits a renamed entry `(source-name local-name)` in an import
names list, and §8.4 admits it in an export. The compiler rejects every such
entry at parse. For example, `(import [lib [(Box B)]])` reports
`module error …: expected symbol for import name, got (Box B)`. The
self-rename `[(Some Some)]`, which §8.3.5 says MUST NOT be rejected, takes the
same path.

- **Observed:** a REPL turn on the pre- and post-S122-persistence binaries
  (`ce266062…`, `e6076b17…`), for a renamed type and a renamed trait. The
  unrenamed control `(import [lib [Box]])` installs, and its impl persists.
  Log: `.local/s122-persistence-review-qa/basket-coordinator.log`.
  This is diagnostic evidence, not a committed repro.
- **Coverage:** §8.3.5 carries no coverage annotation, and no e2e cell writes
  a renamed entry.
- **Class:** `wrong-reject`.
- **Locus (from source):** `crates/cranelisp-frontend/src/module_extract.rs`,
  where the names list calls `expect_symbol(item, "import name")`. The
  cross-crate `ImportNames::Specific(Vec<Symbol>)` has no representation for
  a rename, so a correction changes a public type and needs `arch` and the
  inter-crate public-API user gate.
- **Misleading carriers:** `src/syntax/cheatsheet.txt` advertises
  `(import [m [(src local)]])`. `design/arch/backend-keyed-consumer.md`
  describes renamed imports as part of the rename surface.

## Obligations a correction inherits

These are latent now only because no rename reaches the compiler:

- **Impl identity in persistence (S122 review F1).** Save labels an impl from
  settled names (`src/save.rs::impl_label`). The live turn and rehydration use
  the written head name (`definition_result_symbol`). Under a rename these
  keys differ. Every later regeneration of the module would then be refused,
  and later definitions lost at exit. The correction's evidence must include
  an impl written through a renamed type import and one written through a
  renamed trait import, each persisted once with a later definition, plus a
  cold restart.
- **Trait identity in typecheck.** `design/typecheck/typecheck.md` §11
  records a renamed-trait lead in the type-or-trait routes and the stacked
  bound.

## Next

1. `test` commits the minimal failing-not-ignored repro, the renamed import
   of a type, with the unrenamed sibling as control.
2. `arch` frames the `ImportNames` change for the user gate.
3. Scheduling is the user's decision.
