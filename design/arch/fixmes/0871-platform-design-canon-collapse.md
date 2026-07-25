---
number: 0871
target: /design
filed_by: /sprint
filed_at: 2026-07-25
sprint_filed: 118
refers_to: audits/cranelisp-platform-s117.md §R2;
  design/platform/platform.md;
  design/platform/poll-support.md
status: open
---

# Collapse the platform design canon to current design (audit R2)

Crate in scope: `cranelisp-platform` (design surface only).

User-accepted S117 platform-audit recommendation R2 (2026-07-25, S118 Phase 1),
**target sprint S119** — S118 editing capacity belongs to the safety frontier.
Quoting the assessment:

> `design/platform/` has a concise current `platform.md`, a right-sized
> DLL-authoring/interior design, and a right-sized poll-support design.
> Superseded per-sprint implementation plans move under
> `design/platform/archive/` with a short index. The current docs contain no
> retired Decision-0031 callback commitment and no volatile LOC/public-item
> census. Historical rationale remains discoverable in archive or the decision
> record without being interleaved with current instructions.

Evidence: five live records totalling ~3,900 lines; `poll-support.md` alone is
1,414 lines including implementation handoff material; live historical files
`sprint71-redesign.md`, `host-wiring-s76.md`, `implementation-slice-s66.md`;
stale manual census at `platform.md:97-107`.

Cost: medium.
