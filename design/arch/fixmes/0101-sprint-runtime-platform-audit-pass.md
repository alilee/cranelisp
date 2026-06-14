---
number: 0101
target: /sprint
filed_by: /design (runtime)
filed_at: 2026-05-02
sprint_filed: 64
refers_to: design/runtime/runtime.md §10, crates/cranelisp-runtime/src/, crates/cranelisp-platform/src/, audits/
status: deferred
deferred_at: 2026-06-14
deferred_reason: S82 re-scope — `cranelisp-runtime` no longer exists (D43 split into primitives+intrinsics); audit targets are now cranelisp-primitives + cranelisp-intrinsics + cranelisp-platform. Per this FIXME's own framing ("schedule ... in a future sprint"), the three audit passes are SCHEDULED to a dedicated audit sprint, not executed in the S82 decks-clearing sprint.
target_sprint: dedicated-audit-sprint (post-S82)
---

# Schedule runtime + platform audit passes

## Issue

The 2026-04-23 audit pass produced HIGH/MEDIUM/LOW finding reports for four crates: frontend, typecheck, backend, int. Runtime and platform were not covered. There is no `audits/runtime-*.md` or `audits/platform-*.md` document; no current-state structural diagram; no per-file LOC + responsibility map produced under audit discipline; no remediation plan.

`design/runtime/runtime.md` (this Sprint 64 refresh) carries a per-file summary derived from source-reading, but source-reading is not an audit. The audit discipline catches what desk-review does not — architectural drift, hidden coupling, monoliths, duplication across files, and divergence between as-designed and as-built that has not yet surfaced as a Decision or FIXME.

LOC distribution in the runtime crate at audit time would be:
- `io.rs` 966
- `drop.rs` 864
- `string.rs` 717
- `vec.rs` 666
- `marshal.rs` 389
- `ivar.rs` 314
- `alloc.rs` 304
- `rc.rs` 199
- `panic.rs` 95

(Per Decision 40, `io_trace.rs` 952 and `trace.rs` 740 relocate out — auditing them in the runtime crate would audit a transient shape; better to audit post-relocation.)

## Proposed resolution

Schedule two audit passes in a future sprint, sequenced after Decision 40 / FIXME 0098 relocation lands so the runtime audit looks at the post-relocation shape:

1. **Runtime audit pass** — produce `audits/runtime-2026-NN-NN.md` following the established 4-crate audit format: per-file responsibility map, hidden coupling check, monolith candidates (`io.rs` and `drop.rs` are the obvious starting points), HIGH/MEDIUM/LOW finding list with proposed remediations, current-state + target-state diagrams.

2. **Platform audit pass** — same shape for `cranelisp-platform`.

Following the audit, `design/runtime/runtime.md` §3 cross-checks against the audit's per-file map; §10 may gain concrete findings; new FIXMEs may be filed targeting `/dev` for remediation work.

## Operational implication / Context

Without an audit, `runtime.md` §3 is the only structured per-file analysis of the crate, and it is `/design`-authored rather than audit-discipline-authored. The two are complements, not substitutes — design docs argue intent; audits surface drift. Closing the audit gap brings runtime + platform to parity with the rest of the workspace.

Sequence is the load-bearing constraint: auditing runtime today would audit the in-flight transition state (with `trace.rs` and `io_trace.rs` still present per as-built but slated for relocation per Decision 40). Audit post-relocation to avoid producing a snapshot of a transient.
