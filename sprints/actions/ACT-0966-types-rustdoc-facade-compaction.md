---
id: ACT-0966
title: Dispose the types audit's rustdoc history-compaction and citation-refresh recommendations
status: open
priority: advisory
from: audit
to: arch
sprint: 122
filed_at: 2026-09-21
refers_to:
  - crates/cranelisp-types/src/module.rs
  - crates/cranelisp-types/src/error.rs
  - crates/cranelisp-types/CLAUDE.md
---

## Request

Provenance: the S118 `cranelisp-types` whole-context assessment
([historical assessment](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-types-s118.md), §3 R4 and R5). Its
disposition trail was never written. R1, R2 and R3 are delivered in source —
the dead exports and `StructuralDeclEntry`/`append_structural_decl` deleted
(S119, FIXME 0918), the concurrency target formally retracted in
`module.rs` rustdoc, `PlatformSpec.name` carrying a standing decision with a
trigger (0919), and `got_data_symbol_name` escaping `_` injectively (FIXME
0748 deleted by its owner at `3d37028b`). The platform carve-out inside that
mint is carried separately by the S122 plan's "Platform naming carve-out" row.
Two recommendations remain, **undisposed — not approved work**:

1. **R4 — history compaction of the rustdoc facade.** The audit judged
   `module.rs` to be roughly two-thirds comment mass, with retired shapes
   (the `Macro` retirement, Decision-45 placement) narrated in several places
   and sprint/submission labels used as anchors. The file is now 5,427 lines.
   The recommended bar is reader-facing, not a line target: each item's
   rustdoc states the current contract plus at most a one-line provenance
   pointer, without thinning the load-bearing notes (serde discipline,
   accessor read-throughs, exception classes). Doc-only; `public-api.txt`
   unchanged. Question for `arch` and the user: accept as a bounded pass,
   decline, or fold into the next change-set that opens the file.
2. **R5 residue — citations.** `crates/cranelisp-types/CLAUDE.md` is now
   mostly symbol-anchored; three `file.rs:NNN` citations remain. Two types
   source comments still cite retired facade documents
   (`crates/cranelisp-types/src/error.rs` → `facades/backend.md`;
   `crates/cranelisp-types/src/module.rs` → `facades/frontend-audit-s70.md`).

## Completion evidence

- Item 1: a recorded accept/decline; if accepted, no retired-shape narrative
  longer than a line in the public rustdoc and an unchanged baseline.
- Item 2: every citation in the crate memory and crate source resolves;
  symbol names preferred over line numbers.

## Additional source-verified leads from the boundary-guide cleanup

The S122 architecture read found stale scaffold status in `concrete.rs` and
`mono_expr.rs`, retired decision-index citations in `module.rs`, an obsolete
exact-diff reference in `ownership.rs`, and a completed raw-slot wording task
in `lib.rs`. Recheck those comments when this rustdoc pass is dispositioned;
these leads do not approve the separate API contraction in ACT-0971.

The concreteness review also found `Life::HostPromised` rustdoc in
`lifecycle.rs` calling the host symbol concrete although the pinned four-member
roster has polymorphic schemes. Reconcile this claim against the current
I-EMIT status in `design/arch/total-concreteness.md` §3.3.
