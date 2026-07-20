---
number: 0710
target: /dev
filed_by: /docs
filed_at: 2026-07-20
sprint_filed: 114
refers_to: crates/cranelisp-frontend (qualified-tail reader — the empty-local-half dangling-qualifier reject)
status: open
---

# Dangling-qualifier empty-LOCAL-half message is terse and unremedied, unlike the rich empty-MODULE-half (`/bar`) message

## Severity
Minor (usability finding — message quality)

## Issue

S114 made dangling qualifiers located errors in every position. Probing the two
halves at HEAD (`3cdd285c`, prebuilt `target/debug/cranelisp`) shows an
**asymmetry in message quality** between the empty-module and empty-local cases:

- Empty **module** half (`/bar`, in-form e.g. `(+ /bar 1)`) — rich, remedy-named:

  ```
  Error: parse error at 3..4: `/` here has no module name before it — a qualified name needs a non-empty module (`mod/name`); a bare `/` division must be separated (`(/ a b)`)
  ```

- Empty **local** half (`foo/`, `:foo/`) — terse, no remedy:

  ```
  user> :foo/ 3
  Error: parse error at 5..5: expected local name after '/'
  user> foo/
  Error: parse error at 4..4: expected local name after '/'
  ```

Both are correctly *located* and *rejected* (spec §8.5.1 both-halves-non-empty).
The functional contract holds. The finding is purely that the empty-local message
does not name the malformed shape ("dangling qualifier") or the remedy the way its
sibling does, so a newcomer who typed `map/` gets less help than one who typed
`/bar`.

## Why this reaches /docs

The errors catalogue (`user/errors/trait-impl-diagnostics.md`) is gaining a
dangling-qualifier entry in S114 Phase 6b. The catalogue can supply the remedy
prose itself (it already notes "exact wording can shift; the remedy is the stable
part"), so documentation closes the user-facing gap regardless. This FIXME asks
only that the empty-local reject be brought to **parity** with the empty-module
message so the catalogue can quote a message that already carries its own remedy.

## Suggested resolution

At the qualified-tail reader seam that raises `expected local name after '/'`,
emit a message shaped like the empty-module sibling — name the dangling-qualifier
shape and the fix (write `mod/name` with a non-empty local, or drop the trailing
`/`). No semantic change; message text only. Coordinate wording with /spec §8.5.1
if the two rejects should share one phrasing.

## Priority
Low. Does not block the Phase 6b catalogue entry (the catalogue supplies the
remedy). File-and-forget polish for whenever the frontend touches this reader.
