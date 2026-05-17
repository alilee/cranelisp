---
number: 0189
target: /design (primitives)
filed_by: /dev (primitives)
filed_at: 2026-05-15
sprint_filed: 67
refers_to: design/arch/facades/primitives.md §"String + vec primitives", tests/facade_compliance.rs::facade_compliance_orphans_match_expected_sprint_67_baseline, crates/cranelisp-primitives/public-api.txt
status: open
---

# `cranelisp-primitives` facade missing the spec's predicate-suffix export names

## Issue

Sprint 67 Wave 3 physically relocated the 15 user-callable string fns + `vec_len`
from `cranelisp-intrinsics` into `cranelisp-primitives`. After the relocation,
`tests/facade_compliance::facade_compliance_orphans_match_expected_sprint_67_baseline`
flags 3 orphan names on the primitives baseline:

- `contains?`
- `starts-with?`
- `ends-with?`

These are the `#[export_name = "..."]` symbol-table names on the
`str_contains` / `str_starts_with` / `str_ends_with` Rust fns. The
predicate-suffix `?` is the spec-mandated form per
`spec/appendix-a-builtins.md §A.3`. The facade text in
`design/arch/facades/primitives.md` §"String + vec primitives" lists these
with the dash-naming convention (`str-contains`, `str-starts-with`,
`str-ends-with`) rather than the actual symbol-table form
(`contains?`, `starts-with?`, `ends-with?`).

Pre-Wave-3 these orphans were absorbed by `cranelisp-intrinsics`'s facade
which carried both name forms (Rust name + kebab JIT name); post-Wave-3
the primitives facade is the authoritative naming home and must list the
true JIT-name form.

## Proposed resolution

Update `design/arch/facades/primitives.md` §"String + vec primitives" so
the as-listed names match the actual `#[export_name = …]` values for these
three predicates (and verify the other 12 — none of `str_contains`'s
siblings carry the `?` suffix, only the boolean-predicates). Suggested
phrasing: list the JIT name beside each Rust identifier rather than
choosing one convention. The facade compliance test's name-extraction
treats `#[export_name = "…"]`'s string literal as a leaf name and looks
for it as a substring of the facade corpus, so simply mentioning
`contains?`, `starts-with?`, `ends-with?` (in code-fence or inline) is
sufficient.

## Operational implication / Context

- Wave 3 `/dev (primitives)` cannot edit `design/arch/facades/primitives.md`
  (file-ownership boundary). The relocation is otherwise complete; rows 26 +
  27 PIF tests pass.
- `facade_compliance_orphans_match_expected_sprint_67_baseline` currently
  reports 5 orphans total (3 here + 2 from intrinsics — see FIXME 0190 for
  the intrinsics counterpart). Resolving this FIXME drops the total to 2.
- No source change is needed; this is a facade-text update.
