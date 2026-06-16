---
number: 0365
target: /spec
filed_by: /spec
filed_at: 2026-06-16
sprint_filed: 83
refers_to: spec/05-definitions.md §5.2.6, spec/08-modules.md §8.5.2
status: open
---

# Extend `Type.member` dotted syntax to resolve field accessors

## Issue

Same-module duplicate field names poison the bare accessor (§5.2.6, ruled S83 W2):
two type definitions that share a field name — e.g. `(deftype Box [:Int v])` and
`(deftype Cup [:Int v])` — both generate an accessor named `v`, making bare `v`
ambiguous under §8.6.5 (compile-time error listing alternatives; no silent overload,
no silent winner).

Today the only escapes for a poisoned field's value are `match` (§6) and, cross-module,
module-qualified names (`m/v`, §8.5.1). The user directed (S83 W2 ruling) that there
SHOULD also be a per-type qualification escape hatch usable within the same module:
"you should be able to qualify to overcome the ambiguity."

The natural mechanism is the existing `Type.member` dotted syntax (§8.5.2), which
currently resolves only **constructors** (`Option.Some`) and **trait methods**
(`Display.show`). It does not yet resolve field accessors.

§5.2.6 already names this enhancement as the planned escape and cites this FIXME by
number; this FIXME tracks the actual work.

## Proposed resolution

Extend the `Type.member` dotted-name form (§8.5.2) so that, when `member` is the name
of a field accessor of type `Type`, `Type.member` resolves directly to that accessor
function — e.g. `Box.v` → the `v` accessor of `Box`, `Cup.v` → the `v` accessor of
`Cup` — bypassing bare-name lookup exactly as dotted constructor/trait-method access
does. This disambiguates same-module duplicate field-name accessors directly, without
needing `match` or a module qualifier.

Spec changes:
- §8.5.2 — add field accessors to the set of members reachable via `Type.member`
  (alongside constructors and trait methods); add an example (`Box.v`).
- §5.2.6 — once landed, update the "planned extension" wording from future-tense to
  the realized escape hatch (and add coverage annotation).

## Operational implication / Context

This is a FUTURE enhancement, NOT implemented in S83. It requires a downstream cascade:
- **/frontend** — grammar/reader: `Type.member` already parses as a dotted name, but
  resolution must learn the accessor case;
- **/typecheck** — name resolution must resolve `Type.member` to a field accessor and
  type it as `(Fn [Type] FieldType)`;
- **/qa** — a guard exercising `Box.v` / `Cup.v` disambiguating a poisoned field.

Scheduled for a future sprint. The S83 W2 ruling (the basis for §5.2.6) deliberately
deferred this so the immediate work (ambiguity-by-default, rejecting the arg-type
overload fold) lands first; the qualification escape follows.
