---
number: 0932
target: /design
filed_by: /arch
filed_at: 2026-07-28
sprint_filed: 119
refers_to: design/arch/total-concreteness.md §3.2/§3.3;
  crates/cranelisp-primitives/src/declarations.rs:660-671 (vec-len — the ONE
  slotted polymorphic primitive), :672-704 (vec-get/set/push — Inline,
  slot-less, the model);
  crates/cranelisp-primitives/src/tests.rs:75-99 (the inline slot-less pin);
  src/bootstrap.rs:876, :925-943, :1129-1160 (the by-name polymorphic import
  roster: bind, race, select, catch-runtime-error)
status: open
---

# S120: `vec-len` de-slots; the polymorphic ABI-import roster is pinned with declared representation dependencies

**Target: `/design`(backend + runtime pair). S120 scope.**

Per `design/arch/total-concreteness.md` §3.2, `vec-len` is the single slotted
polymorphic primitive in the system and the last `Primitive`-kind exception to
the universal `slot ⇒ is_concrete()` invariant. Choose and design one of the
two legal spellings:

- **(a) Reclassify `PrimitiveBody::Inline`** — a length-word load, same
  emission family as `vec-get` minus the element op; concrete-per-use by
  construction, layout-robust by construction. Preferred if the emission is
  genuinely element-independent under the current Vec header contract.
- **(b) Reclassify `DefKind::PrimitiveExtern`** — slot-less by-name (the
  `bind` precedent), joining the I-ABI roster with the declared dependency
  "Vec `LEN` at a fixed offset for every element type".

Either retires the slot. Value-position use rides the existing `__inlwrap`
per-concrete-sig wrapper family.

**Second deliverable — the I-ABI roster pin** (`total-concreteness.md` §3.3):
a unit cell enumerating the slot-less polymorphic by-name callables exactly
(`bind`, `race`, `select`, `catch-runtime-error`, plus `vec-len` if spelling
(b) is chosen), each with its declared representation dependencies recorded
(uniform value word; IO node tag discipline; closure `DROP_GLUE_PTR`; `Result`
Ok/Err tag order; Vec header). A new polymorphic import REDs the cell until
declared. This roster is the closed re-visit list when `--release` layout
specialisation lands — the point of the user's ruling.

Note for the layout work (record in the design, no action now): `vec-get`/
`vec-set`/`vec-push` need NO change — inline emission at concrete sites is
exactly the shape that survives per-element-type layouts; `vec-len`'s shared
body is the one family member a common-length-word layout contract can keep.

Delete this file when the S120 design lands.
