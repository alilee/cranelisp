---
number: 0912
target: /spec
filed_by: /arch
filed_at: 2026-07-26
sprint_filed: 118
refers_to: spec/03-types.md (deftype declaration rules);
  design/arch/concrete-boundary-type.md §3.1.1 point 2 (S118 amendment);
  design/backend/transitive-drop-glue.md §4.1; FIXME 0903
status: open
---

# Open normative question: should an undeclared `deftype` field be rejected at declaration time?

## The question (for the user to arbitrate — /spec frames, never rules)

Today `(deftype B (Mk [v]))` — a field with no type annotation on a type with no
type parameters — is **accepted**: typecheck leaves `v` a free type variable,
and because `B` is monomorphic no instantiation ever pins it. Nothing in the
current spec rejects this shape at declaration, and §3.11.1's full-concreteness
verdict does not reach it (that check covers codegen-reaching *value*
positions, not declarations).

Should the spec instead require every `deftype` field to have a determinable
type at declaration — i.e. reject `(deftype B (Mk [v]))` with a located error
("field `v` has no declared type and `B` declares no type parameters")?

## Why it surfaced (S118, FIXMEs 0902/0903)

The undeclared-field shape is one of two legal declaration shapes that give a
constructor/accessor *template* (compiled once per declaration,
signature-typed) a non-concrete field type — the other being an ordinary
declared type parameter (`(deftype (Box a) [:a v])`). The compiler handles both
by classifying the residual type `Mixed` (uniform i64) for RC purposes
(`concrete-boundary-type.md` §3.1.1 point 2 as amended S118), and the
release-side handling of the wider class is under re-ruling at FIXME 0903.

## Consequences either way (neutrally stated)

- **Reject at declaration**: removes the undeclared-field shape from the
  template class (the generic-parameter shape remains regardless, so the
  compiler's `Mixed` classification rule stands either way). Existing corpus
  impact: `(deftype Pair [first second])`-style product shortcuts — the
  field-name-only product form — would need a spec decision on whether the
  *shortcut* form infers/defaults differently from an explicit ctor arm
  (`tests/spec_05_definitions.rs::deftype_product_shortcut_field_names`
  exercises the shortcut today; FIXME 0903's measurement lists the affected
  programs).
- **Keep accepting**: the field stays polymorphic-in-effect but unusable at
  any concrete type without annotation at use sites; the template carries a
  free var forever, which is exactly the shape feeding one of the 0903 leak
  families until 0903's release-side ruling lands.

## Handoff

`/spec` frames this for the user alongside the 0903 window (S119), since a
"reject" ruling narrows 0903's class. Neither `/arch` nor `/design` has ruled
or will rule the semantics; the compiler-side classification is settled
independently of the answer.
