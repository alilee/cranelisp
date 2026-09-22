---
id: ACT-0972
title: Design a structural reader form for rest-parameter markers
status: open
priority: advisory
from: sprint
to: arch
filed_at: 2026-09-21
refers_to:
  - spec/01-lexical.md
  - spec/09-macros.md
  - crates/cranelisp-types/src/sexp.rs
  - crates/cranelisp-frontend/src/reader.rs
  - crates/cranelisp-frontend/src/defmacro.rs
---

## User decision and future scope

The user approved both `&rest` and `& rest`, with ampersand reserved and
excluded from ordinary source identifiers. They then approved retaining
`SexpSym("&rest")` for now and requested this action for a future structural
representation, analogous to the reader's structural annotation form.

Current behavior remains authoritative: either spelling produces one rest-marker
form encoded as `SexpSym("&rest")`, including quoted and macro-argument data.
This encoding does not make ampersand legal inside ordinary identifiers.
No reader, public API or data-model change is authorised by this action.

## Next increment

Assess a dedicated rest-marker reader node carrying the parameter name.
Decide its exact language-visible S-expression representation with the user;
do not assume a constructor name or payload schema. Account for reader
output, quote/quasiquote and splicing, macro argument transport and matching,
macro parameter parsing, rendering and persistence, and existing macros that
inspect the current symbol encoding. Preserve the two source spellings.

Present the cross-crate/public-API and language-visible delta before
implementation, with compatibility and migration consequences. QA allocates
discriminating evidence for the approved representation and its consumers.
Until then, retain the current encoding; do not treat it as a defect.
