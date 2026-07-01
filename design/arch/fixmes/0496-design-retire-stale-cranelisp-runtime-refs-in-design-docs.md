---
number: 0496
target: /design
filed_by: /dev
filed_at: 2026-07-01
sprint_filed: 98
refers_to: design/int/int.md §"observability sinks", design/backend/backend.md, design/platform/platform.md, design/int/observability.md, design/runtime/runtime.md
status: open
---

# Retire residual stale `cranelisp-runtime` references in `/design`-owned per-crate design docs

## Issue

FIXME 0493 (S98, `/dev` repo-wide comment/doc sweep) retired stale `cranelisp-runtime`
crate-name references across governance CLAUDE.md tables, live source rustdoc/comments,
audits (LOW-1), and `tests/plan/*` reactor.md citations. It deliberately left the
per-crate **design docs** to their owners, per the `/dev` boundary
("Never edit `design/{crate}/{crate}.md` — file FIXME `target: /design`").

The following live `/design`-owned design docs still carry stale `cranelisp-runtime`
current-tense references that misdirect a newcomer to a crate that no longer exists
(D43 split → `cranelisp-primitives` + `cranelisp-intrinsics`; several subsystems
relocated: `io_trace` → `src/io_trace.rs`, the IO trampoline / `IoObserver` →
`cranelisp-intrinsics`, RC → `cranelisp-intrinsics`):

- **`design/platform/platform.md:32-33`** — "IO trampoline — owned by `cranelisp-runtime`",
  "`IoObserver` callback contract — owned by `cranelisp-runtime`". Both are now
  owned by `cranelisp-intrinsics` (backend-emitted runtime library).
- **`design/int/int.md:631`** — `cranelisp_runtime::register_io_observer(...)` API ref
  (now `cranelisp-intrinsics`). (int.md:627/682 are already correctly past-tensed —
  "relocated from `cranelisp-runtime/src/io_trace.rs`" — leave.)
- **`design/backend/backend.md:278`** — `cranelisp_runtime::heap_alloc` example string
  + "a real `cranelisp-runtime` linkage" (now the two successor crates). (backend.md:433
  is already corrected — "the runtime crate was dissolved by D43" — leave.)
- **`design/int/observability.md`** (lines ~28, 86-87, 101, 233, 243, 245, 330) — multiple
  `crates/cranelisp-runtime/src/{rc,io_trace,io}.rs` path refs and `cranelisp_runtime::…`
  API examples. `io_trace` is now `src/io_trace.rs`; `rc.rs`/`io.rs` are now in
  `cranelisp-intrinsics`.
- **`design/runtime/runtime.md`** — the entire doc is the design-of-record for the
  **retired** `crates/cranelisp-runtime/` crate (dissolved S66 W4a). Not a stale-ref
  fix but a whole-doc disposition question: archive it, or re-home its still-live intent
  under `design/primitives/` + `design/intrinsics/`? `/design` (or `/arch`) call.

## Proposed resolution

Mechanical current-tense sweep of the four live docs (platform.md, int.md, backend.md,
observability.md): replace `cranelisp-runtime` → the correct successor
(`cranelisp-intrinsics` for runtime internals / trampoline / observer / RC / io_trace-now-int;
`cranelisp-primitives` for the user-callable conversion surface), past-tensing any migration
narrative (the `crates/cranelisp-primitives/src/marshal.rs:25` "lifted from the pre-D43
runtime crate" one-liner is the model). Separately decide the disposition of the
retired-crate design doc `design/runtime/runtime.md` (archive vs re-home).

## Operational implication / Context

Doc-only, no baseline churn. Not urgent (a reader who knows the D43 history is not blocked),
but each stale ref sends a newcomer looking for a non-existent crate. Sibling to the
retired FIXME 0493 (source/governance/audit half, done S98) — this is the `/design`-owned
per-crate-design-doc half that ownership discipline routes here rather than sweeping
inline. Also note (for `/arch`/`/sprint`): the legacy skill-def files
`.claude/commands/arch.md` (§crate-surface table line ~122 lists `cranelisp-runtime/` as a
live crate) and `.claude/commands/platform.md` (pre-D43 "create `cranelisp-runtime/`"
instructions) carry the same staleness — skill-def ownership, outside `/dev` scope.
