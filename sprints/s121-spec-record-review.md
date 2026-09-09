# S121 Phase 6b — exact REPL spec record-only review

## Scope and authority

**Approved 2026-09-09** (user: “approved”, after the three corrections were
presented). Applied and snapshot-diff verified. The before/after hunks below retain
the exact authorized scope; no build or test is required for these prose edits.

Each hunk below records existing approved and delivered behavior only:

- the 2026-09-03 `/search` ruling excludes macro declarations from every feed,
  forbids macro execution while indexing unloaded source, and leaves complete
  semantic indexing to ACT-0952; and
- the 2026-09-04 redefinition/trait rulings retain whole-pair `impl` behavior.

No requirement, test annotation, API, implementation, or deferred scope is
changed by this proposal.

## 1. `repl/spec/17a-agent-language-awareness.md` §17.19 status

**Before**

```md
### 17.19 Importable-Symbol Search — `/search` — Pillar 3 (DESIGN-PINNED, IMPLEMENTED LATER) [S90 re-pin]

> **Status: RE-PINNED, DESIGN-ONLY THIS SPRINT, IMPLEMENTED LATER.** Pillar 3 was
> redesigned mid-plan (user, 2026-06-23); the authoritative architecture is
> `repl-embedded-agent.md §11.1–§11.9` (commit `c699045`). The command was **renamed
> `/lib-search` → `/search`** (R12), is now a **non-agent-gated default-build session
> facility** (R9), searches public non-macro symbols reachable on the **lib search path ∪ the project root**
> (R10), matches by **name, scheme, OR docstring** (exact-or-partial on the name/scheme axes,
> case-insensitive substring on the docstring axis — the docstring axis added S106, FIXME
> 0540) (R6), and is served by
> an **eager** background index built by the nice workers (R4/R9b). Per the
> `/arch` Phase-2 ruling (R1; `repl-embedded-agent.md §11.5`), Pillar 3 still ships as
> **design only** in S90 — implementation is gated on the FIXME-0432 typecheck root fix
> **plus** the nice-worker indexer `catch_unwind` floor (CF.2, §11.3). This subsection pins
> the **experience contract** — the command shape, the result row, the dual human/agent use,
> the partial-result UX, and the safety floor — so the implementation, whenever it lands, has
> a fixed target. It carries the `[S90 re-pin]` tag and is **not yet a conformance MUST** for
> a shipping build. [S90 re-pin]
```

**After**

```md
### 17.19 Importable-Symbol Search — `/search` — Pillar 3 [S90 re-pin]

> **Status: current contract.** `/search` is a normal default-build session
> facility for public non-macro symbols. Source indexing does not execute macro
> expansion. Complete semantic indexing remains deferred in ACT-0952.
```

**Effect:** removes the obsolete implementation-gate claim. It neither admits
macro rows nor macro execution, and it does not alter result shape, indexing,
or any §17.19 MUST.

## 2. `repl/spec/03-slash-commands.md` §3.1 `/search` inventory row

**Before**

```md
| `/search <query>` | — | **Design-pinned S90 (re-pin), implemented later** — search public non-macro **importable-but-unimported** symbols (reachable on the lib search path ∪ the project root) by **name OR scheme, exact OR partial** (see §17.19); a **normal default-build session facility** (not agent-gated); also reached by the agent via the ordinary pull | 4 | [Tested+Neg tests/search::search_by_name_exact_returns_four_facets, tests/search::search_by_scheme_partial_contains, tests/search::search_neg_no_match_self_documenting_note] |
```

**After**

```md
| `/search <query>` | — | Search public non-macro symbols reachable on the lib search path ∪ the project root by name, scheme, or docstring (see §17.19). An exact in-scope name match remains visible as `already in scope — no import needed`; source indexing does not execute macro expansion. A **normal default-build session facility** (not agent-gated), also reached by the agent via the ordinary pull | 4 | [Tested+Neg tests/search::search_by_name_exact_returns_four_facets, tests/search::search_by_scheme_partial_contains, tests/search::search_neg_no_match_self_documenting_note] |
```

**Effect:** makes the inventory agree with the already-detailed §17.19
exception for exact in-scope names and its existing non-macro boundary. It
adds no behavior: §17.19 already owns the complete rule, including the deferred
semantic-index limit.

## 3. `repl/spec/18-redefinition.md` §18.7 stale FIXME-0832 status

**Before**

```md
**Known implementation defect — FIXME 0832.** The failing-not-ignored test
`tests/trait_method_tail_s116.rs::reimpl_default_body_calls_replaced_sibling`
currently fails after a re-`impl` when a materialized default body calls a
replaced sibling method (expected `1050`, observed a type mismatch: expected
`Box`, got `Int`). This is a defect against the normative whole-pair
replacement and current-default requirements above, not an exception to them.
```

**After**

No replacement text. The applied hunk deletes the six-line stale failure
paragraph; the existing `### 18.8 Persistence and Reload [Uncovered S121]`
heading follows the preceding `impl` enumeration requirement directly.

**Effect:** the final accepted gate records
`trait_method_tail_s116::reimpl_default_body_calls_replaced_sibling` as PASS.
Deletion corrects only a disproven current-status assertion. The preceding
whole-pair validation, publication atomicity, and current-default requirements
remain byte-for-byte unchanged; QA separately owns the coverage/status repair.

## Approved decision

The user approved exactly the three after-states above as **record-only**
corrections, with no normative behavior change. Apply only these prose hunks;
do not change coverage annotations or add a semantic-index/macro expansion
promise in the same edit.
