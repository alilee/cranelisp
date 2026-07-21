---
number: 0740
target: /design (int)
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/int/prelude-table-write-isolation.md §2.1/§2.4 census table
  (the closure-claim acceptance instrument) vs src/bootstrap.rs:446/:807 +
  src/platform.rs:407 — live-table PUBLIC-write seams neither routed through
  check_terminal_closure nor carried as named legal-skips.
status: open
---

# 0604 census closure-claim is materially incomplete — two live-table PUBLIC-write seams undispositioned

## Severity
Important (census is the acceptance instrument; benign in effect — see below)

## Issue

The §2.1/§2.4 census exists to prove a **closed** set: "no *other* foreground
seam can insert a public table entry" (§2.1), enforced by the greppable
structural guard (§2.4, Principle 18): "a public-insert seam that bypasses
`check_terminal_closure` is a `/review` finding." The S114 lesson the re-based
plan itself cites is that the census **missed the suspected writer**
(`commit_staging_to_live`). This change-set correctly routes that row, but a
`/review` grep of live-table `.insert` sites surfaces **two more public-write
seams neither routed nor legal-skipped in the census**:

1. **`src/bootstrap.rs:446`** — seeds `Int/Bool/Float/String → primitives/<name>`
   as **`Visibility::Public` `ModuleEntry::Import` edges into the live `macros`
   module table**. This is **cross-module** (`source.module == primitives`,
   dest == `macros`) — the **exact phantom shape** the gate exists to reject
   (a public re-export whose source ≠ destination). `bootstrap.rs:807`
   (`Bind → IO.Bind`) is the intra-module sibling. Neither routes through the
   gate.
2. **`src/platform.rs:407`** — writes a `Visibility::Public`
   `DefKind::PlatformEffect` (own-def, non-`Import`) into the live
   `platform.<name>` table via `get_mut` + `insert`, at DLL-load orchestration.

## Why benign (why Important, not Blocker)

Neither seam can produce the live defect: bootstrap runs single-threaded at
session init writing correct seeds (and `D(macros)` is never recorded there, so
even if routed the unknown-`D` arm would permit); platform-load writes only
own-module `PlatformEffect` Defs (own-def arm passes by construction). The
gate's soundness for the `bit-and` phantom is intact. But the census's
**closure claim** — the load-bearing acceptance instrument for 0604 — is
technically false while these seams are undispositioned, and a future reader
running the §2.4 structural grep will hit them with no recorded disposition.
That is precisely the failure mode the census discipline exists to prevent.

## Proposed resolution

In `design/int/prelude-table-write-isolation.md` §2.1, either:
- (a) state the census scope boundary explicitly ("session-init bootstrap seeds
  and platform-DLL load orchestration are OUTSIDE the foreground
  concurrent-compile path"), naming `bootstrap.rs` and `platform.rs` as
  scope-excluded with the single-threaded-at-init / load-orchestration
  rationale; **and/or**
- (b) add census rows for both as **named legal-skips** (bootstrap: correct
  seeds at init, pre-worker-spawn, `D` unrecorded → unknown-permit; platform:
  own-module `PlatformEffect` Defs only, own-def arm) so the §2.4 grep resolves.

The `src/imports.rs` census-comment mirror should track whichever wording lands
(a `/dev` follow-up, since that comment is code). No behavioural change is
required — this is a completeness/disposition fix so the closure claim is true
as stated.

## Context

`/review`(src) S115 W2, change-set `d9f2caea`. The routed `commit_staging_to_live`
row and the corrected predicate are correct; this finding is only that the census
closure claim omits two seams the design's own structural guard would flag.
