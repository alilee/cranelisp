---
number: 0515
target: /arch
filed_by: /spec
filed_at: 2026-07-04
sprint_filed: 102
refers_to: design/int/s78-entry-module.md §2 (esp. lines 26, 93, 100, 180, 295–297, 447), spec/08-modules.md §8.6.1/§8.6.4/§8.8.1
status: open
---

# s78-entry-module.md §2 still presents "explicit/local SILENTLY shadows the prelude" as settled — reverse it to the no-exception ruling

## Issue

The user (sole language arbiter, 2026-07-04) reversed the prelude carve-out:
**the prelude is just an implicit `(import [prelude [*]])`; its provided names
are in scope exactly like any imported name, and redefining/shadowing a
prelude-provided name is the SAME compile-time error as shadowing an explicit
import. There are NO exceptions.**

`/spec` has already enacted this in `spec/08-modules.md` (this sprint):
- §8.6.4 "Definition over a name in scope" now reads over `import` **∪** `export`
  **∪** the implicit prelude; the "Contrast — prelude-provided names remain
  shadowable" paragraph is replaced with "The prelude carries no exemption — a
  loaded prelude name is NOT shadowable."
- §8.6.1 layer 2 and §8.8.1 now state the outer/inner scope layering is an
  **implementation detail of resolution, not an exemption**; prelude names are
  subject to the §8.6.4 conflict rules and §8.6.5 ambiguity identically to
  explicit imports (same-terminal dedup, distinct-terminal poison, def-over
  = error).
- §8.8.3 pins the distinct, still-legal escape hatch: *not loading* a prelude
  name (empty/suppressed prelude) ≠ *shadowing* a loaded one.

`design/int/s78-entry-module.md §2` — the /arch-authored "prelude-as-outer-scope"
target design — still encodes the **superseded** conclusion that explicit imports
and local definitions *silently shadow* the prelude with no error. Concretely
stale statements:

- L93 / L100: "Explicit imports shadow the implicit prelude … The shadow is a
  lookup ordering, not a same-table override" presented as the settled semantic
  outcome (silent, no collision).
- L180: "teaching the shadowing model the spec describes."
- L295–297: the "3 import-shadow REDs" fix + "12 greens" preservation are argued
  on the premise that an explicit import of a prelude-provided name silently
  wins and a local def silently shadows — both now **errors** (tier-a explicit
  distinct-terminal collision; tier-b def-over-prelude).
- L447: the /spec editorial-alignment note frames the change as making
  outer-scope framing normative *while keeping the silent shadow* — the change
  is now a **semantic reversal**, not editorial.

The **outer-scope RESOLUTION MECHANISM itself is not reversed** — the user ruled
the outer/inner layering is an impl detail. What is reversed is the doc's
*conclusion* that this layering licenses a silent shadow. Under the ruling the
same two-scope resolver must instead REJECT a definition (and poison a
distinct-terminal import) that collides with a prelude-provided name.

## Proposed resolution

Re-anchor §2's shadow-semantics prose to the no-exception ruling, keeping the
outer-scope resolution mechanism as the (unchanged) impl substrate:

1. Replace "explicit/local silently shadows the prelude" wording with: the
   prelude outer scope participates in the §8.6.4/§8.6.5 collision rules exactly
   as an explicit import — same-terminal dedup, distinct-terminal poison,
   **def-over-prelude = compile-time error**. No silent shadow; no carve-out.
2. Rework the §2.7.x "3 import-shadow REDs / 12 greens" reasoning (L295–297) to
   the post-ruling outcome: an explicit import that shares a bare name with a
   prelude-provided one dedups only if their **terminals are equal**, else it is
   an ambiguity error; a local def over any in-scope prelude name is rejected.
   The still-green cases are the *not-loading* ones (refusal / selective /
   null import → no outer scope for that name → free to define).
3. Update the §"Dependency on /spec" (L26) and §5 editorial-alignment note
   (L447): the /spec change is now **enacted** and is a **semantic reversal**,
   not editorial. Point at the landed §8.6.1/§8.6.4/§8.8.1 text.
4. Cross-reference **FIXME 0514** — the shared-seam re-impl (move the
   def-over-(import|export|prelude) rejection to the typecheck `check_forms`
   Pass-1 two-scope chokepoint) already carries the "NO prelude exception"
   RULING UPDATE and the 0475 re-anchor; §2's design narrative should defer to
   0514 for the implementation seam rather than re-deriving the silent-shadow
   installer story.

## Operational implication / Context

- This is a **doc-coherence** re-anchor, not new impl work — 0514 owns the impl
  and 0475 re-anchor; the spec is already corrected. The risk of leaving §2
  stale is a future reader treating "silent shadow" as settled and re-encoding
  the reversed carve-out.
- Owner note: the doc header names Owner `/arch` though it lives in `design/int/`.
  Filed to `/arch` accordingly; if `/arch` deems the §2 prose an `/int`-owned
  edit, re-target at pickup.
- Do **not** reverse the outer-scope resolution mechanism itself — only the
  shadow *conclusion*. The user explicitly ruled the outer/inner layering an
  implementation detail.
