---
number: 0873
target: /design
filed_by: /sprint
filed_at: 2026-07-25
sprint_filed: 118
refers_to: audits/cranelisp-platform-s117.md §R4;
  crates/cranelisp-platform/src/adt.rs;
  platforms/shapes/src/lib.rs;
  platforms/shapes-badabi/src/lib.rs;
  exemplar/platforms/web/src/lib.rs
status: open
---

# Decide marker-binding ergonomics — deferral trigger has fired (audit R4)

Crate in scope: `cranelisp-platform` (design decision; `/arch` review required
if the chosen mechanism changes public API).

User-accepted S117 platform-audit recommendation R4, **explicitly pulled into
S118 by the user** (2026-07-25, S118 Phase 1). Quoting the assessment:

> A focused design compares keeping explicit marker impls, a derive, and a
> macro/generated binding. It chooses the smallest shape that either makes
> schema-name agreement structural or explicitly accepts runtime failure with
> a production-path negative witness and clear diagnostics. If explicit impls
> remain, the rationale and trigger for reconsideration are recorded; merely
> adding another positive test does not cure the mismatch risk.

Context: platform ADT bindings hand-write `CLAdtType::TYPE_NAME` as a string
that must agree with the generated schema; nothing checks it before runtime.
The S87 assessment deferred a mechanism until a real multi-ADT platform
existed; the web platform now hand-writes four marker types
(`exemplar/platforms/web/src/lib.rs:89-115`).

Cost: medium (design only this sprint; any implementation is a follow-on).
Scheduled: S118 platform slice (with 0870/0874).
