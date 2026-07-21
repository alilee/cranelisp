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

---

## /dev(src) S115 W6 — the CODE half is LANDED; two factual corrections to this finding

`/dev`(src, narrow int) actioned the code half (this file targets `/design`(int),
so the §2.1/§2.4 census-table wording is still owed — see "What /design(int) still
owes" below). Change-set: `src/platform.rs`, `src/bootstrap.rs`, `src/imports.rs`.

### Correction 1 — `src/bootstrap.rs:446` is `Visibility::PRIVATE`, not Public

Verified at HEAD `26ecdc54` and at the reviewed change-set `d9f2caea`
(`git show d9f2caea:src/bootstrap.rs`): the four `Int/Bool/Float/String →
primitives/<name>` edges seeded into the live `macros` table carry
`visibility: Visibility::Private` (`bootstrap.rs:451`). They are therefore **not
public writes at all** — `check_terminal_closure`'s first clause (`!entry.is_public()`)
would return `Ok` before any arm is consulted. The finding's framing of this seam
as "the exact phantom shape" (a cross-module PUBLIC re-export) does not hold, and
`/qa`'s S115 retirement ruling in FIXME 0604 repeats the same characterisation —
both should be corrected when the census wording lands.

### Correction 2 — bootstrap's one PUBLIC `Import` is intra-module

The public-`Import` seam bootstrap actually has is `bootstrap.rs:812`
(`Bind → <io_fqtn.module>/IO.Bind`, step 5). `io_fqtn` is
`primitives_fqtn("IO")`, so `source.module == "primitives" ==` the destination
module: it takes the **intra-module self-alias** arm — Ok, no `D` read. Every
other bootstrap public write is a non-`Import` own definition (special forms,
intrinsic types, `TypeDef`s, synthetic ADT ctors/Defs) → own-def arm.

### Dispositions landed

1. **`src/platform.rs::register_platform_in_tc` — ROUTED.** The public
   `PlatformEffect` write now calls `imports::check_terminal_closure(&module_path,
   name, &entry, Span::SYNTHETIC, None)` before `table.insert`. Safe under the
   held `get_mut` guard by construction (own-def arm does no map read — the
   deadlock hazard 0604 names); `declared_exports = None` because a synthetic
   `platform.<name>` module records no `(export …)` surface. **No behavioural
   change is reachable**: the entry is never an `Import`, so the own-def arm
   always admits it. (Confirmed by the full suite: platform e2e lanes unchanged.)
2. **`src/bootstrap.rs::mount_synthetic_modules` — NAMED LEGAL-SKIP, ASSERTED.**
   Rationale in the fn's rustdoc + the `src/imports.rs` census block: it runs once
   at session init, single-threaded, **before any worker is spawned** (outside the
   foreground concurrent-compile path), and seeds only own definitions plus the one
   intra-module self-alias above. Making the whole init path fallible to route an
   unreachable rejection buys no soundness (Principle 6/8). Instead the skip carries
   a **detection proof**:
   `bootstrap::tests::bootstrap_seeds_pass_the_terminal_closure_gate` sweeps EVERY
   seeded entry through `check_terminal_closure` under the strictest closure
   `D(M) = {}` (so the unknown-D permit arm cannot mask anything). Detection
   demonstrated: flipping the `macros` seed edges to `Visibility::Public` turns the
   test RED with the out-of-closure diagnosis; reverting turns it GREEN.
3. **`src/imports.rs` census-comment mirror updated** with both rows
   (bootstrap = legal-skip-asserted, platform = routed) and the rationale.

### What /design(int) still owes

`design/int/prelude-table-write-isolation.md` §2.1/§2.4 needs, in its own words:

- a **census row for `platform.rs::register_platform_in_tc` = ROUTE** (it is no
  longer an undispositioned seam — it goes through the chokepoint);
- a **census row (or scope-boundary statement) for
  `bootstrap.rs::mount_synthetic_modules` = named legal-skip**, with the
  pre-worker-spawn / own-def + intra-module-self-alias rationale AND a pointer to
  the asserting sweep test (the §2.4 structural grep must resolve to a recorded
  disposition, not to an argument);
- the two factual corrections above (Private ≠ Public at `:446`; the real public
  `Import` is the intra-module `Bind` at `:812`), so the doc does not carry
  forward the "exact phantom shape" characterisation.

The `src/imports.rs` mirror already tracks this wording and will be re-synced by
`/dev` if `/design`(int) words it differently.
