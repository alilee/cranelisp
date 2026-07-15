---
number: 0618
target: /arch
filed_by: /review
filed_at: 2026-07-15
sprint_filed: 110
refers_to: design/arch/interfaces.md (0583 carrier + impl_module narrative)
status: open
---

# interfaces.md narrative owed for the 0583 carrier fields (W0 + W0.1b)

## Severity
Important (documentation cascade named in the pinned change-set; not W1-gating)

## Issue

`design/arch/interfaces.md` carries NO narrative for any of the S110 0583
carrier surface landed in `cranelisp-types`:

- W0 (`41fab350`): `MethodResolutions.resolved_targets`,
  `MonoExpr::{Var,Apply}.resolved_target`, the REQUIRED `from_expr` third
  param, the relocated `lenient_from_expr`.
- W0.1b (`144828d1`): `ModuleEntry::TraitImpl.impl_module`,
  `ResolvedCall::TraitMethod.impl_module`.

`backend-keyed-consumer.md` §1.1.1's pinned W0.1b diff says "Baseline regen +
`interfaces.md` + rustdoc ride that change-set"; the baseline and rustdoc rode,
`interfaces.md` did not — `/dev` correctly flagged instead of editing
(`/arch`-owned; see the `/dev (W0.1b)` SPRINT note). Grep confirms zero hits
for `resolved_targets` / `impl_module` in `interfaces.md`.

## Proposed resolution

One narrative block (or two short section additions: `ResolvedCall` and
`ModuleEntry`) in `interfaces.md` covering the carrier contract (§1.1
semantics, "whichever storage key HIT") and the two `impl_module` fields (the
amended-D45 discovery→storage pointer). Land before S110 close; W3's archive
trigger expects the contract folded into rustdoc + BC + `interfaces.md`.

## Context

Found by `/review` (producer W0.1+W0.1b gate review). Baseline-diff discipline
(root `design/arch/CLAUDE.md` §Baseline-diff) requires the surface record to
catch up in the same change-set; the source rustdoc half is complete and good.
