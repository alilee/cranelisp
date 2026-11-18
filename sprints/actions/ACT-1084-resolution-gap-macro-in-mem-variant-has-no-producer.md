---
id: ACT-1084
title: The public variant `ResolutionGap::MacroInMem` has no producer in any crate
status: open
priority: low
from: sprint
to: arch
sprint: 124
filed_at: 2026-11-18
refers_to:
  - crates/cranelisp-types/src/error.rs
  - design/arch/interfaces.md
---

## Observation

`arch`, reading source at `0086d210` (S124, Phase 5): no crate constructs
`ResolutionGap::MacroInMem`. Frontend raises no gap (its `ExpansionError` was
deleted at S76); an alias-spelled macro head is resolved in the binary by
`SymbolTableMacroResolver::recognize` without a gap value. The variant is
constructed only by a module test in `src/process_form/tests.rs` and matched
in `src/process_form/dependency.rs`. Two comments still name a frontend
producer (`crates/cranelisp-frontend/src/lib.rs`,
`tests/process_form_dispatch.rs`).

## Requested outcome

Remove the variant, or state the producer it is kept for. Removal is an
inter-crate public-API change (`cranelisp-types` −1 line) and needs the
user's approval before it is built. Not scheduled in S124.
