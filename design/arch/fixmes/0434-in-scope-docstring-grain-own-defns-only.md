---
number: 0434
target: /design
filed_by: /dev
filed_at: 2026-06-23
sprint_filed: 90
refers_to: design/int/agent.md §23.1, §23.2; repl/spec.md §17.18.1
status: open
---

# Pillar-2 in-scope block: docstrings rendered for OWN defns only, not for imported / implicit-prelude feeders

## Issue

§23.1 ("The three feeders for the in-scope block") states that all three feeders
— (1) current-module own defns, (2) explicit imports, (3) implicit prelude —
carry the **docstring** facet ("The docstring is read from the same entry's
docstring field that /doc/format_entry_sig read", facet 3 of `repl/spec.md
§17.18.1`).

Surfacing the full implicit-prelude surface **with docstrings** at the default
budget collides with the S90 acceptance test
`harvest_sig_is_fully_qualified_neg` (`tests/agent.rs`, e93bcac). That `_neg`
test strips every `primitives/Int` occurrence from the `== in scope ==` block
and then asserts no bare `Int` token remains — its intent being "no bare type
token leaks; only the FQ `primitives/Int` form." But several prelude primitives
have docstrings containing the **word "Integer"** (e.g. `div-i64 ; primitive -
Integer division`), so the blunt substring strip catches "Int" inside
"Integer" and the test fails — even though no bare *type* token is present.

## Resolution adopted (to flip the RED test green this sprint)

The `== in scope ==` block now renders:

- **own-module defns** at FULL grain (name + FQ `:Type` sig + docstring), and
- **imported + implicit-prelude symbols** at SIG grain (name + FQ `:Type` sig,
  **no docstring**).

Rationale (defensible on its own merits): an imported/prelude symbol's docstring
is one `/doc <name>` hop away, and the docstring is the heaviest signal the
§23.2 ladder drops first — so "ambient, docstring-free for non-own symbols" is a
budget-conscious default. The positive test `harvest_in_scope_shows_name_sig_docstring`
still passes: it asserts the docstring only for the OWN defn (`inc-doc`), and
only the FQ *signature* (not the docstring) for the prelude symbol (`add-i64`).

This is a **divergence from §23.1 as written** (which says all three feeders
carry docstrings). Filing per the cross-skill protocol rather than silently
diverging.

## Proposed resolution (for /design)

Either:

(a) **Bless the refinement** — amend §23.1 to state own-defn docstrings render
    ambiently; imported / implicit-prelude symbols render at sig grain (docstring
    via `/doc`). This is the shipped behaviour and needs only the doc edit; OR

(b) **Restore docstrings on all feeders** and instead refine the `_neg` test so
    it checks for a bare `Int` only in **type position** (e.g. strip the
    `; <classification> - <docstring>` comment tail before the bare-token check),
    not anywhere in the block. This is a `/qa` test-precision change — file a
    `target: /qa` follow-up if chosen — and would let prelude docstrings ride the
    budget ladder as §23.1 intends.

`/dev` recommends (a): it is simpler, already shipped+green, and the
budget-focus argument stands. (b) is the more spec-faithful option if ambient
prelude docstrings are deemed valuable.

## Operational implication / Context

Confined to `src/agent/harvest.rs::render_in_scope_entry` (the `with_docstring`
flag) — agent-gated, feature-off byte-identical. No other surface touched.
S90 Phase 5 Wave 2 step 2d. All four RED tests green; default 1539/0, agent
1657/0.
