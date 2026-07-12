---
number: 0561
target: /repl
filed_by: /sprint
filed_at: 2026-07-12
sprint_filed: 108
refers_to: repl/spec.md §10.3 (style table, ~L1456-1470 + ~13 downstream refs + the `<dim>` examples ~L1485-1508, 2336/2521/2525/2555/2739); src/style.rs (Style::Italic="3" comments, Style::Dim="2" prompt/banner); src/main.rs L408 comment
status: open
---

# `repl/spec.md` §10.3 says classification-comments render **dim**; the impl renders them **italic** — a repo-wide spec/impl divergence needing user ratification

## Issue

Surfaced during S108 Increment 2 M-1 finalize (the `/search` lifecycle messages
use the classification-comment role, which forced a dim-vs-italic decision). The
divergence is NOT local to §17.19:

- **Spec §10.3** (the canonical style table, `repl/spec.md` ~L1456-1470) states the
  **classification-comment / related-symbol-comment / metadata** role renders
  **dim** (`\033[2m`), with an explicit documented rationale, and ~13 downstream
  references + the `<dim>` render examples (~L1485-1508, 2336/2521/2525/2555/2739)
  follow suit.
- **The impl** (`src/style.rs`): `Style::Italic => "3"` is "Italic (SGR 3) —
  comments"; `Style::Dim => "2"` is "Dim (SGR 2) — prompt, banner." So comments
  render **italic** and **dim** is reserved for prompt/banner.

The two `/search` §17.19 edits landed in S108 Inc2 now cite §10.3 for "italic"
while §10.3 itself still says "dim" — an internal spec contradiction. `src/main.rs`
L408 also carries a code comment "Dim classification-comment role" that is a
misnomer (the impl uses Italic) — a 1-word fix folded into this reconciliation.

## Proposed resolution

`/repl` runs a §10.3 reconciliation pass. Because §10.3's dim choice was
DELIBERATE (documented rationale), this is a genuine REPL-experience decision, not
a silent alignment: **the split as-built is dim = prompt/banner, italic =
classification-comments/metadata.** Bring the canonical choice to the USER (via
`/sprint`) as a one-line ratification:
- **Ratify the impl** (comments = italic; dim = prompt/banner) → update §10.3's
  table + rationale + all ~13 downstream refs + the `<dim>` examples to italic, and
  fix the `main.rs` L408 comment word. (Least churn; the impl is coherent.)
- OR **restore the spec** (comments = dim) → then `/dev` changes `src/style.rs` +
  the S108 §17.19 completion/note styling back to dim. (More churn; reverts a
  working, reviewed impl for a documented-but-old rationale.)

Recommend ratifying the impl unless the user prefers the original dim rationale.
Whichever wins, the §17.19 edits + §10.3 + `main.rs` L408 comment all align to it.

## Operational implication / Context

- Pre-existing (predates S108); NOT an Increment-2 defect — surfaced by it. Not a
  blocker for S108 Inc2 close (the impl renders correctly; only the spec text +
  one code comment are inconsistent).
- Delete when §10.3 + downstream refs + the `main.rs` L408 comment are reconciled
  to the ratified canonical style.
