---
number: 0686
target: /spec
filed_by: /sprint
filed_at: 2026-07-20
sprint_filed: 114
refers_to: spec/08-modules.md §8.5.1 [S114] dangling-qualifier bullet (currently enumerates empty-LOCAL-half spellings: foo/, a.b/); design/arch/principles/16-punctuation-symbols-are-not-special.md (amended bullet already states the symmetric reading)
status: open
---

# Enumerate `/bar` (empty module half) explicitly in §8.5.1's dangling-qualifier error

**User confirmation (2026-07-20, S114 Phase 3): "the symmetric reading stands —
`/bar` errors too."** The both-halves-non-empty classifier already implies it, and
the amended Principle 16 states it, but §8.5.1's [S114] bullet enumerates only the
empty-local-half spellings (`foo/`, `a.b/`). Add `/bar` to the enumeration so the
error set is explicit rather than inferred (bare `/` division fence unchanged).
One-line edit; ride any Phase 5 spec touch.
