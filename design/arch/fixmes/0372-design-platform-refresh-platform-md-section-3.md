---
number: 0372
target: /design
filed_by: /sprint
filed_at: 2026-06-16
sprint_filed: 83
refers_to: audits/platform-2026-06-14.md (MED-1, MED-2, MED-4, LOW), design/platform/platform.md §3, crates/cranelisp-platform/src/lib.rs (null_alloc_with_tag R1 gate)
status: open
---

# platform: refresh design/platform/platform.md §3 (two reworks stale) + R1 residue + macro extract

## Issue (0101 audit — platform, 2026-06-14)

From `audits/platform-2026-06-14.md` (the biggest contributor-confusion source, zero source risk):
- **MED-1 — `design/platform/platform.md §3` is two reworks out of date:** claims single-file ~940 lines, ABI v1, live `derive_jit_name`/`platform_fn_ptr`/`JITBuilder::symbol` dispatch; as-built is 3 files / ~3,816 LOC / ABI v5 / GOT-indirect / ADT-marshaling. The doc even contradicts its own §13. Refresh §3 to the as-built shape.
- **MED-2 — R1 gate residue (`/dev`):** `null_alloc_with_tag`'s "wired-or-panic" gate + rustdoc + the `t25` test still say `alloc_with_tag` is "not yet wired … removed in the host-wiring sprint (FIXME 0229)", but 0229 is resolved and the callback was wired in S76 (another rustdoc block in the same file correctly says so). Reframe the R1 gate as a permanent fallback + fix `t25`.
- **MED-4 — `declare_platform!` extract (`/dev`):** the macro is large; extract to a sibling module.
- **LOW:** "owns no runtime state" wording; two guarded `schema.rs` unwraps; CLAdtType marker ergonomics.

## Proposed resolution
`/design` narrow-deployed on platform: refresh `platform.md §3` to as-built (3 files, ABI v5, GOT-indirect, ADT-marshaling; reconcile with §13). The `/dev` items (R1 gate reframe + `t25` fix; `declare_platform!` extract) can be split to a `/dev` sub-FIXME or actioned alongside when platform is next touched — they're recorded in the audit doc.

## Context
0101 audit pass. Doc-accuracy + migration-residue, no behavior change. Paired with FIXME 0371 (the schema-grammar correctness pin). Forward-flow; not S83-blocking.
