---
number: 0788
target: /design
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/frontend/enforcement-matrices.md §3.2 (table row `foo/` (value) + design item 3); design/frontend/binder-head-reject.md §3.5
status: open
---

# `enforcement-matrices.md` §3.2 still presents the retired `"expected local name after '/'"` message as current behaviour

## Severity
Suggestion (design-doc staleness against shipped code; the §3.2 S115 rider itself is correct)

## Issue

S115 W5b (`d3f0a223`) landed FIXME 0710: `read_local_name`'s message changed from

```
expected local name after '/'
```

to the empty-MODULE-half sibling's shape

```
`/` here has no local name after it — a qualified name needs a non-empty local
(`mod/name`); drop the trailing `/` to write a bare name
```

`design/frontend/enforcement-matrices.md` §3.2 still carries the retired string
in two places that read as **present-tense current behaviour**:

- the "Today" table row — ``| `foo/` (value) | … `Err("expected local name after
  '/'")` (`:788`, propagated by `?`) | **already errors** |``
- design item **3** — "`read_local_name`'s existing `Err` (`:788`, `"expected
  local name after '/'"`) **is retained**".

The **S115 message-parity rider** immediately below item 3 designs the new
message correctly, so the doc is internally coherent but self-contradicting on a
skim: item 3 says the old string is retained, the rider says raise it. A reader
grepping the codebase for the quoted string now finds only comments.

`design/frontend/binder-head-reject.md` §3.5 has the same present-tense quote
("being terse vs the rich `/bar` message"), which is a *description of the
problem 0710 solved* and is defensible as history — flagged only for the same
pass.

## Proposed resolution

One editing pass on `enforcement-matrices.md` §3.2: restate the table row and
item 3 in the past tense (or quote the landed message), and mark the S115 rider
**LANDED** with the pin
(`crates/cranelisp-frontend/src/reader/tests.rs::empty_local_half_message_names_shape_and_remedy`).
Optionally the same for `binder-head-reject.md` §3.5's 0710 bullet.

Note this is the **third** copy of these two message strings found outside the
source: the `/docs` catalogue quotes (routed as FIXME 0786) and these design
docs. A message that is quoted verbatim in three owner-separated documents is
the recurring "one requirement written twice" class `/spec` named at S115 W5a;
the durable fix is quoting *the remedy* rather than the exact string, which the
catalogue already says it does and the design docs do not.

## Context

Found during `/review` of `d3f0a223` (S115 W5b, cranelisp-frontend). No test
asserts either retired string (grep-verified), so nothing is RED.
