---
number: 0847
target: /qa
filed_by: /testing
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/deftype_duplicate_constructor.rs (4 cells);
  tests/deftype_constructor_form_rulings_s116.rs (11 cells);
  tests/plan/PLAN.md; spec/05-definitions.md §5.2
status: open
---

# `PLAN.md` rows + spec annotations for the 15 new `deftype` constructor-form cells

## What landed

Two files, 15 cells, authored in S115 Phase 7 (7 intended REDs, 8 green):

**`tests/deftype_duplicate_constructor.rs`** — live defect, duplicate
constructor names within one `deftype` accepted silently (FIXME 0845 carries
the spec gap; the tests are the defect record and trigger, owner `/dev`):

| Cell | Disposition |
|---|---|
| `deftype_duplicate_nullary_constructor_rejected_neg` | RED |
| `deftype_duplicate_enum_constructor_rejected_neg` | RED |
| `deftype_duplicate_fielded_constructor_rejected_neg` | RED |
| `deftype_distinct_fielded_constructors_control_green` | green control |

**`tests/deftype_constructor_form_rulings_s116.rs`** — the two settled S115
constructor-form rulings, unimplemented at HEAD, flip trigger = the **S116
implementation wave**:

| Cell | Disposition |
|---|---|
| `deftype_content_free_paren_constructor_rejected_neg` | RED (ruling 1) |
| `deftype_content_free_paren_among_bare_nullaries_rejected_neg` | RED (ruling 1) |
| `deftype_content_free_paren_in_polymorphic_type_rejected_neg` | RED (ruling 1) |
| `deftype_nullary_constructor_sharing_type_name_rejected_neg` | RED (ruling 2) |
| `deftype_unit_zero_field_product_control_green` | green control |
| `deftype_product_constructor_sharing_type_name_control_green` | green control |
| `deftype_documented_nullary_control_green` | green control |
| `deftype_documented_nullary_sharing_type_name_control_green` | green control, disposition open (FIXME 0846) |
| `deftype_mixed_bare_nullary_and_fielded_control_green` | green control |
| `deftype_plain_enum_control_green` | green control |
| `deftype_empty_parens_constructor_rejected_neg_anchor` | green (pre-existing reject anchor) |

## What is asked of `/qa`

1. **`PLAN.md` rows** for all 15 cells (every authored test traces to a row;
   drift in either direction is a defect to resolve before phase exit).
2. **Spec annotation band** on `spec/05-definitions.md` §5.2.1/§5.2.2/§5.2.3/
   §5.2.5 once the rulings are scribed and implemented — these cells are the
   first negative coverage the constructor-FORM column has had; §5.2.2's current
   `[Tested …]` is positive-only.
3. **Coverage-by-definition-variants note**: this is a constructor-arm-spelling
   × {accept, reject} matrix (bare nullary / documented nullary / content-free
   paren / fielded / product field list / zero-field product), and it was
   assembled from the ruling text, not from an existing register. The
   `tests/CLAUDE.md` §"Coverage by definition variants" lens would have named
   the gap; consider adding the constructor-arm spelling family to the rolling
   sweep list.
