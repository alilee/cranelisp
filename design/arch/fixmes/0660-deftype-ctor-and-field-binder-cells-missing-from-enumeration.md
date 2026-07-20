---
number: 0660
target: /design
filed_by: /review
filed_at: 2026-07-19
sprint_filed: 113
refers_to: design/frontend/binder-head-reject.md §3/§8 — the site enumeration and spec-diff table omit deftype variant-constructor names (and field names, and the platform-decl name) entirely
status: open
---

# deftype variant-ctor names are binders missing from the §8 enumeration on all three sides

## Severity

Important

## Issue

`binder-head-reject.md` §8's spec-diff table covers every spec §5 head plus two
justified exclusions (type-params, `mod`). But a **deftype variant constructor
name is a binder** — each variant "introduces a distinct variant" (spec §5.2.2)
and mints a module-level callable — the exact analogue of the S5
method-signature argument (§5.3.3 "introduces method names into scope") that the
design DID include. The ctor-name row is absent from **all three sides**: spec
§5's native-binder enumeration, this design's site list (§3), and /qa's BD-M1
matrix (`tests/plan/s113-test-plan.md` §1.2). Neither covered nor
justified-excluded — an enumeration miss, not a /dev miss (W3 implements the
design faithfully).

Live faces, probed on the W3 tree (`--run`, no module `fmt` present):

- `(deftype Shape (fmt/Circle [:primitives/Int r]))` — **accepted at parse**;
  fails later with the incidental degenerate-span
  `module error at 0..0: module 'fmt' … not found` — the same dual silent-accept
  face the design's §1 table pins for deftrait heads. `build_constructor_def`
  (`ast_builder.rs:685`) has no `reject_qualified_binder_head` in either arm
  (bare-symbol arm's `is_uppercase_start` keys on the after-slash segment, so
  `fmt/Circle` passes it).
- **Mirror of the list-arm case defect this very change-set fixed** (audit S113
  finding 2, `build_type_head`): the ctor **list arm has no uppercase check** —
  `(deftype Shape2 (circle [:primitives/Int r]))` parses, typechecks, and binds
  a callable lowercase ctor `circle` (probed to full acceptance), while the bare
  nullary arm's match guard rejects lowercase. A lowercase ctor is additionally
  **unmatchable**: `build_pattern` treats a lowercase pattern symbol as a var
  binder, never a ctor.
- Field names (`[:primitives/Int fmt/r]`) are the secondary-binder sibling of
  the §3.2 type-param cell: silently accepted, dies at the synthesized accessor
  with the same degenerate `0..0` module-not-found face (probed). Needs the
  same deliberate include-or-exclude treatment §3.2 gave type-params.
- `(platform name)` (`module_extract.rs:435` `parse_platform`) enforces
  nothing beyond symbol-ness; spec §5 says only "bare symbol (not a string
  literal)" — no §5.8-style "not qualified, not dotted" clause — yet the name
  composes the synthetic module path `platform.<name>` and the DLL search path,
  so a qualified/dotted spelling mints a bogus module path. Same family as the
  `mod`-head cell W3 closed; spec wording gap.

## /design(frontend) disposition (2026-07-19) — dispositioned in binder-head-reject.md §3.3 + §8; STAYS OPEN

Actioned into `design/frontend/binder-head-reject.md` **§3.3** (new subsection,
per-cell) + **§8** diff table (four rows added) + §8 Result prose. Per-cell:

- **(a) ctor-name uppercase gate (list arm, `build_constructor_def:637`)** —
  clear **defect-class mirror** of the `build_type_head` list-arm case defect
  this same W3 change-set fixed (audit S113 finding 2); a lowercase data ctor is
  callable-but-unmatchable. **Recommend in-sprint fix** (frontend touch, W4
  window rider): add `is_uppercase_start` to the list arm, located, naming the
  uppercase-ctor rule. **Fix half RE-TARGETED to `/dev`(frontend)** — settled
  defect-class mirror, no user ruling needed. /sprint schedules the W4 rider.

- **(b) ctor-name qualified reject** (`(deftype Shape (fmt/Circle …))` accepts,
  degenerate-span dual face) — an **EXTENSION of the binder principle to ctor
  names**, NOT a settled ruling (spec §5 enumerates def-form heads + impl-body
  method defns + (now §5-scribed) method-sig names, not variant-ctor names).
  Marked **USER-QUEUE, veto-visible** per the TB-27/S112 precedent: **/sprint
  carries it to the user gate**; `/dev` does NOT land the ctor-name qualified
  reject until the user ratifies or it stands un-vetoed. Do NOT treat as settled.
  The spec-enumeration amendment (§5 → add variant-ctor names) is tracked here
  and routed to /spec by /sprint once ruled.

- **(c) field names + `platform` name** — field names: `/qa` matrix candidate,
  **justified exclusion** as a secondary field binder (like the §3.2 type-param
  cell), not a reject site. `platform` name: **module-phase family** (like the
  `mod`-head cell W3 closed) — recommend adopting the `mod`-model guard (reject
  `/` AND `.` at `parse_platform`, module-phase style, NOT
  `reject_qualified_binder_head`) as a small in-sprint frontend rider,
  `/dev`-actionable; the spec §5.10 wording gap ("bare symbol" lacks a "not
  qualified, not dotted" clause) is tracked here, routed to /spec by /sprint.

**Status: STAYS OPEN.** The FIXME remains the tracking home until: (a) lands the
W4-rider fix, (b) the user rules the ctor-name reject, (c) the platform guard
lands + /qa dispositions field names. Cell (a)'s fix half is /dev-owned; the
matrix rows (BD ctor cells) route to /qa; the spec amendments (ctor-name
enumeration if ruled, platform §5.10 clause) are tracked here and routed to
/spec by /sprint (FIXME 0651, the method-name enumeration gap, was actioned by
/spec and deleted).

## Proposed resolution (original /review text)

/design(frontend) extends §3 with the ctor-name site (both arms of
`build_constructor_def`, uppercase gate on the list arm included) + a §3.2-style
disposition for field names, adds the §8 rows, and routes: the spec-enumeration
gap to /spec (rider on FIXME 0651's §5 enumeration amendment — ctor names +
platform simple-symbol clause), the matrix rows to /qa (BD-M1 ctor cells ×
{qualified-reject, lowercase-list-arm-reject, bare-uppercase-twin}). Repros
above are one-liners; /testing reduction already effectively done.

## Context

Filed from the S113 W3 change-set review (frontend). The W3 code is faithful to
the design as written; this is the "coverage by definition variants" class
(tests/CLAUDE.md) — the deftype family {head, type-params, ctor names, field
names} had only the first two dispositioned.

## /spec update (2026-07-19) — cell (b) RULED + SCRIBED; spec-enumeration gaps closed

USER RULING 2026-07-19: **variant-constructor names are binders** (user principle:
"you can't define a name in another module, only reference"). Cell (b) is no
longer USER-QUEUE/veto-visible — it is **settled**. Scribed into `spec/`:

- **§5 native-binder enumeration** — added variant-constructor names AND field
  names (each mints a module-level callable/accessor). `[S113]`
- **§5 new "Binder positions" table** — enumerates EVERY name-introducing
  position (module-level, type-var, local, alias) with its bare-symbol rule and
  the reference-position contrast (impl slots, ctor-pattern heads). Answers the
  user's "where do we tighten the spec for this?" `[S113]`
- **§5.2.2** — ctor-name binder bullet (both arms, bare uppercase, span at ctor;
  lowercase-ctor ill-formed cross-ref) + field-name binder bullet. `[S113]`
- **§5.10 platform** — closed the wording gap (cell (c)): platform name is now
  "simple symbol — not qualified, not dotted" (mod-model), noting it composes
  `platform.<name>`. `[S113]`
- Local-binder sites also tightened (§4.3 let, §4.5.2 fn params + defn/defmacro
  params, §6.2.4 match var, §8.3.4 import/export aliases). `[S113]`

**Re-targeting**: the spec-enumeration half is DONE. What STAYS OPEN under this
FIXME is the **implementation half**, now /dev-owned: (a) ctor-name uppercase
gate on the list arm (W4-rider defect-mirror), (b) ctor-name **qualified reject**
(now settled — implement `reject_qualified_binder_head` at
`build_constructor_def` both arms), and the **platform-name guard** (`/`+`.`
reject at `parse_platform`, mod-model). Field-name disposition + BD ctor matrix
rows route to /qa. /sprint handles the code dispatch. This FIXME remains the
tracking home until the /dev + /qa halves land.
