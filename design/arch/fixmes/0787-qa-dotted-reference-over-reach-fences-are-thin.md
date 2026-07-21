---
number: 0787
target: /qa
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/dotted_binder_reject_0702.rs (the 13 "_green" fences) + design/frontend/binder-head-reject.md §2.2 constraint 1
status: open
---

# The S115 dotted-binder over-reach control set is thinner than it reads: 10 of 13 "fences" carry no dot

## Severity
Important (coverage gap — the risk direction of the S115 widening is over-reach, and the standing control set does not cover the design's own named hazard)

## Issue

S115 W5b (`d3f0a223`) widened `reject_qualified_binder_head` to the `.` axis.
`/dev` reports "18 flips, 13 fences held" and states the 13 GREEN fences ARE the
discriminating control, "since they could only stay green if the fix landed at
the binder/reference line rather than on `contains a dot`".

That claim holds for **3** of the 13, not 13. The green set in
`tests/dotted_binder_reject_0702.rs` is:

- **10 × `*_bare_*_accepts_twin_green`** — `(defn ab …)`, `(let [ab 5] …)`,
  `(deftype (Duo a c) …)`, etc. These names contain **no `.`**, so a coarse
  `name.contains('.')` over-reach would leave every one of them GREEN. They
  discriminate a different (also valuable) thing: that the reject did not eat
  legal *bare* binders.
- **3 × genuine dotted-REFERENCE fences** — `dotted_ctor_pattern_head_…`,
  `dotted_ctor_value_construction_…`, `dotted_module_path_in_import_…`.

Only those 3 are over-reach controls for the `.` axis, and none of them covers
the hazard the design **explicitly names** as the reason
`split_qualified_name` must stay `/`-only
(`design/frontend/binder-head-reject.md` §2.2, constraint 1):

> Widening *it* to `.` would corrupt legitimate dotted references (`Maybe.Some`,
> **`core.io/pure`**).

`Maybe.Some` is fenced. **`core.io/pure` — a qualified reference whose MODULE
half is dotted — is not**, in either tier. Nothing in the suite would red if
`split_qualified_name` were widened to split at `.`, corrupting
`platform.stdio/print` into module `platform` / name `stdio/print`.

Unfenced dotted-REFERENCE positions (all verified BY PROBE to hold correctly at
`d3f0a223` — the finding is the missing standing guard, not a live defect):

| Reference position | Probe result at HEAD | Standing guard |
|---|---|---|
| `:platform.stdio/Nope` annotation (dotted module half of a qualified ref) | splits correctly → `unknown type Nope (from module platform.stdio)` | **none e2e**; unit only at `ast_builder/tests.rs::…parse_annotation_name("a.b/Box")` |
| `(import [(platform.stdio io) [*]])` — dotted module path in the ALIAS form | accepted | none (only the reject twin `io.x` is pinned) |
| `(export [platform.stdio [print]])` — dotted path in `export` | accepted | none (import path is fenced, export is not) |
| `Type.field` accessor `(Point.x p)` | accepted | `tests/spec_field_accessor.rs` (indirect) |
| dotted symbols inside quoted data / quasiquote templates | accepted | none |
| degenerate `.` / `a.` / `.b` NOT dotted (the Principle-16 twin of bare `/`) | accepted | unit only (`reject_qualified_binder_head_rejects_dotted_and_names_member_fix`) |

## Proposed resolution

Add the missing **reference-column** cells to the S115 matrix
(`tests/plan/s115-test-plan.md` §4) so the over-reach direction has a standing
control, prioritising the design's named hazard:

1. `core.io/pure`-shaped: a qualified reference with a **dotted module half**
   resolves with the module intact (e2e; `(platform stdio)` +
   `:platform.stdio/T` or a call `platform.stdio/print`).
2. dotted module path in `export` (twin of the fenced `import` cell).
3. the `(dotted.module alias)` positive alias form.
4. an e2e degenerate-`.` cell (or an explicit note that the unit pin is the
   agreed tier for it).

This is the standing *coverage-by-definition-variants* category (the `{/, .} ×
{binder, reference} × position` matrix): the binder column is now dense on both
separators; the reference column is dense on `/` and sparse on `.`.

## Context

Found during `/review` of `d3f0a223` (S115 W5b, cranelisp-frontend). All of the
unfenced positions above were probed live at HEAD and behave correctly, so this
blocks nothing — it is a guard gap against a future re-widening, exactly the
mistake the design wrote a constraint to prevent.
