---
id: ACT-0985
title: Assess declaration forward-reference and higher-kinded dispatch leads
status: open
priority: required
from: design
to: qa
sprint: 122
filed_at: 2026-09-22
refers_to:
  - design/typecheck/typecheck.md
  - design/typecheck/hkt.md
---

## Request

Classify three source-read leads from the typecheck design reconciliation before
changing behavior or treating existing tests as authority:

- Declaration forward references: the master design's open items contrast
  spec/05-definitions.md section 5.13.1 and spec/08-modules.md section 8.10.4
  with `tests/spec_09_macros.rs::macro_expanded_begin_impl_neg_before_deftype_is_rejected`.
  That test requires rejection when expansion places an impl before its type.
  Reconcile the governing scope with spec; seek a user ruling only if required
  meaning remains unsettled.
- Result-only constructor variables: the HKT design's open questions record
  `find_hkt_param_index` defaulting to parameter zero when no parameter applies
  the constructor variable. Assess the admissibility and dispatch of a method
  such as `(pure [:a x] (f a))` against spec/03-types.md section 3.7.6.
- Primitive identity: the HKT design records Case 2 rejection comparing the
  written spelling against Int/Bool/String/Float. Assess equivalent qualified
  or renamed references against the same kind requirement.

## Completion evidence

These are unexecuted leads, not confirmed or closed defects. QA determines the
minimal discriminating reproductions and controls, routes requirement ambiguity
to spec, and attributes confirmed failures before implementation. Preserve any
confirmed defect as an unignored spec-traced test; record each lead's disposition.

Provenance: design session `511c3863-4a8b-4ac4-8288-7c24e9d964ac` inspected
`traits/registry.rs`, `traits/impl_check.rs` and the macro test above. Sprint
reopened those source loci before filing; no runtime reproduction was run.
