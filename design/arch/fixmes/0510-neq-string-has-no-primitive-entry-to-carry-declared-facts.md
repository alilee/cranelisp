---
number: 0510
target: /design (cranelisp-backend)
filed_by: /dev (cranelisp-primitives)
filed_at: 2026-07-04
sprint_filed: 102
refers_to: design/typecheck/ownership-inference.md §13.4 (the neq-string bullet + the coverage verdict), design/backend/ring2-rc.md §3.3 (the neq-string audit row, FIXME 0504)
status: open
---

# `neq-string` has no `DefKind::Primitive` entry — CS-B cannot attach its declared facts

## Issue

§13.4 lists `neq-string` as a covered leaf: FIXME 0504 added its `ring2-rc.md`
§3.3 audit row (two heap args, body verified consuming, the `Eq.!=` counterpart
of `str-eq`) precisely "before CS-B transcribes … or both silently skip the
leaf." The §13.4 verdict then claims coverage is complete for every heap-arg
extern-shimmed `DefKind::Primitive`.

But as-built, **`neq-string` has no `ModuleEntry` in `cranelisp-primitives`**. It
is shim-only: `extern_shims()` harvests its fn ptr for GOT population, and it is
reached exclusively through the `Eq.!=` trait-dispatch path
(`cranelisp-typecheck/src/traits/dispatch.rs:177` maps `("Eq","!=","String") →
"neq-string"`). It is registered in **neither** `ring0/ring1/ring3_primitives()`
**nor** the vec-query family — the only entry sources `insert_primitive_entry` /
`insert_vec_query_entries` build. The existing `extern_shims_harvest_covers_full_inventory`
test documents this explicitly: `neq-string` (with `neq-i64/f64/bool` and
`sconcat`) has "no `PRIMITIVES_TABLE` entry."

Consequently CS-B has **no leaf to populate** for `neq-string`: there is no
`DefKind::Primitive { mode_summary }` entry for pass5 to read via
`ModuleEntry::mode_summary()`. pass5's `Apply` classification of `(!= s1 s2)`
(String) chain-follows to a missing entry ⇒ the Decision-24 conservative default
(`Owned`), so `s1`/`s2` widen to `Owned`. This is exactly the "silently skip the
leaf" outcome 0504 tried to prevent — and it is **asymmetric** with `str-eq`
(`==`), which IS a registered `ring1` entry and DOES get the declared `Borrowed`
facts, so `(== s1 s2)` keeps its args borrowed while `(!= s1 s2)` does not.

This is a precision loss only (monotone-sound); it is not a correctness defect.

## What CS-B did

- Populated every entry that exists (`ring0/1/3` + vec-query) with declared
  facts per §13.4.
- **Transcribed the `neq-string` audit row into the classifier anyway**:
  `ownership_facts::declared_mode_summary` lists `neq-string` in the only-read
  `Borrowed` set, so IF an entry is ever registered it gets the correct facts by
  construction (unit-tested: `neq_string_transcribes_the_0504_borrowed_row`).
  With no entry today, the classifier is simply never consulted for it.
- Did **not** register a new `neq-string` `PrimitiveDef` entry — that is a table
  change (it would make `neq-string` name-resolvable, perturb the golden
  corpus / the harvest test's invariant, and is out of CS-B's "populate existing
  entries" scope).

## Proposed resolution

`/design` (backend) to decide between:

- **(a)** Register `neq-string` as a `ring1` `PrimitiveDef` entry (symmetric with
  `str-eq`), so it becomes a real `DefKind::Primitive` leaf carrying the declared
  `Borrowed`/`Consumed`/`Fresh` facts — restoring the §13.4 coverage claim and
  the `==`/`!=` precision symmetry. (Note: this may change name-resolution and
  the golden corpus; assess against Q1/`extern_shims` invariants.)
- **(b)** Accept conservative-default (`Owned`) for the entry-less `neq-*`
  family — matching `neq-i64/f64/bool`, which are also shim-only trait-dispatch
  targets with no entries — and amend the §13.4 verdict to name `neq-string` as
  a trait-dispatch leaf outside the declared-fact table (like `sconcat`'s
  `PrimitiveExtern` scope cut), not a covered `DefKind::Primitive`.

## Operational implication / Context

Non-blocking for CS-B, CS-1..4, or the L-D3e per-row guards on the entries that
DO exist. It bounds only the achievable precision on `(!= <string> <string>)`
until resolved. The classifier already encodes the correct facts, so option (a)
is a pure table-registration change with no `ownership_facts` edit; option (b) is
a doc amendment with no code change.
