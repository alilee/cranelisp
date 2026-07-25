---
number: 0870
target: /dev
filed_by: /sprint
filed_at: 2026-07-25
sprint_filed: 118
refers_to: audits/cranelisp-platform-s117.md §R1;
  crates/cranelisp-platform/src/concurrency.rs;
  crates/cranelisp-platform/src/poll_support.rs;
  crates/cranelisp-platform/src/declare.rs;
  crates/cranelisp-platform/src/lib.rs;
  crates/cranelisp-platform/CLAUDE.md
status: open
---

# Platform source facade describes retired architectures (audit R1)

Crate in scope: `cranelisp-platform`.

User-accepted S117 platform-audit recommendation R1 (2026-07-25, S118 Phase 1).
Quoting the assessment:

> All crate-root and module rustdoc describes ABI v9, core/ungated poll
> support, layout-hash validation, and the permanently two-field
> `HostCallbacks`. The retired closure-callback promise is absent. The local
> memory no longer needs a "known stale phrasing" warning. Add a narrow
> source-text/doc guard only if the owner judges version drift likely to
> recur; do not add another manually maintained surface inventory.

Evidence rows in the audit cite `concurrency.rs:4,21`, `poll_support.rs:1`,
`declare.rs:132-135`, `lib.rs:16-19,585-595,893-898`, and `CLAUDE.md:142-145`,
each contradicted by `lib.rs:298` and `bounded-contexts.md:567-568,597-599`.

Cost: small. Scheduled: S118 platform slice (with 0873/0874). Documentation
repair only — no semantic API delta is authorized.
